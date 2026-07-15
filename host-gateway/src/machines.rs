//! The fly.io-compatible machines surface — records, the store, and the handler the
//! [`crate::route`] classifier dispatches into.
//!
//! A create maps a fly machine request onto a durable workload record and admits it.
//! The **fulfillment** — running the workload on a real dregg execution-lease — is the
//! injected [`MachineLauncher`] seam: an in-process [`NullLauncher`] admits the record
//! without launching (the dev / single-box default), a [`crate::launcher::SandboxLauncher`]
//! drives a real local lease lifecycle, and a production launcher drives the lease over
//! the resident `hosted-lease` plane.
//!
//! ## Every mutation is owner-enforced (the closed cross-tenant hole)
//!
//! Every read and mutation carries the **verified subject** and is checked against the
//! record's [`Machine::owner`]. A caller may only see / stop / start / delete a machine
//! it owns; a request for another tenant's machine — even with the exact `{app}` and
//! `{id}` — is a `404` (indistinguishable from non-existence, so ownership is not an
//! oracle). Ids are unguessable 128-bit tokens ([`crate::util::mint_token`]), so
//! enumeration is not a fallback attack either. A request with no verified subject is
//! refused (`401`).

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};

use http_serve::{HttpMethod, WebResponse};
use serde::{Deserialize, Serialize};

use crate::page::Page;
use crate::persist::{MachinePersistence, NullMachines};
use crate::route::{self, Route};
use crate::util::{lock, mint_token};

/// The lifecycle state of a machine (a subset of fly's states, on the dregg workload
/// lifecycle).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MachineState {
    /// Created + admitted, workload running.
    Started,
    /// Reaped (stopped) — the record survives, the workload is not running.
    Stopped,
    /// Destroyed — retained only transiently for the destroy response.
    Destroyed,
}

impl MachineState {
    /// The fly-compatible state string.
    pub fn as_str(self) -> &'static str {
        match self {
            MachineState::Started => "started",
            MachineState::Stopped => "stopped",
            MachineState::Destroyed => "destroyed",
        }
    }
}

/// The requested guest shape (a fly `guest` block, graded onto the dregg cap-lattice by
/// a launcher). Only the size-shaping fields the gateway records.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct GuestConfig {
    /// Requested vCPUs.
    #[serde(default)]
    pub cpus: u32,
    /// Requested memory (MiB).
    #[serde(default)]
    pub memory_mb: u32,
    /// The workload image reference (an owned-sandbox workload reference, not an OCI
    /// pull — noted honestly as a divergence from fly).
    #[serde(default)]
    pub image: String,
}

/// The config block of a create request / a machine record (`fly` shape, trimmed).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct MachineConfig {
    /// The guest shape.
    #[serde(default)]
    pub guest: GuestConfig,
    /// The requested region.
    #[serde(default)]
    pub region: String,
}

/// A create-machine request body (`POST /v1/apps/{app}/machines`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct CreateMachineRequest {
    /// The machine name (fly `name`).
    #[serde(default)]
    pub name: String,
    /// The machine config.
    #[serde(default)]
    pub config: MachineConfig,
}

/// A machine record (the fly `Machine` shape the surface returns).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Machine {
    /// The machine id.
    pub id: String,
    /// The machine name.
    pub name: String,
    /// The owning app (fly `{app}`).
    pub app: String,
    /// The owner subject (the cap-scope key; every read + mutation is checked against
    /// it). Set from the verified subject at create, immutable thereafter.
    pub owner: String,
    /// The lifecycle state.
    pub state: MachineState,
    /// The region.
    pub region: String,
    /// The config the machine was created with.
    pub config: MachineConfig,
}

/// The compute backend a create is fulfilled onto — the injected launch seam.
///
/// A create records the [`Machine`], then calls [`MachineLauncher::launch`]; a
/// production launcher drives the workload onto a funded dregg execution-lease and
/// returns the started state. The [`NullLauncher`] admits without launching (dev).
pub trait MachineLauncher: Send + Sync {
    /// Launch (or admit) `machine`; return the state it settled into (or an error
    /// string that becomes a `502`). The default in-process launcher returns
    /// `Started`.
    fn launch(&self, machine: &Machine) -> Result<MachineState, String>;

    /// Reap `machine` (stop the workload). Default: no-op success.
    fn reap(&self, _machine: &Machine) -> Result<(), String> {
        Ok(())
    }
}

/// The in-process launcher: admits a create as `Started` without a real compute
/// backend (the dev / single-box default). The named seam a production launcher fills.
pub struct NullLauncher;

impl MachineLauncher for NullLauncher {
    fn launch(&self, _machine: &Machine) -> Result<MachineState, String> {
        Ok(MachineState::Started)
    }
}

/// The machine store — the fly surface's record plane, owner-scoped and owner-indexed.
///
/// Records live in a primary `id -> Machine` map; a secondary `owner -> {id}` index
/// makes a scoped read O(owned) rather than O(all). Every mutation writes through the
/// injected [`MachinePersistence`] so the store survives a restart.
pub struct MachineStore {
    machines: Mutex<BTreeMap<String, Machine>>,
    by_owner: Mutex<BTreeMap<String, BTreeSet<String>>>,
    persistence: Arc<dyn MachinePersistence>,
}

impl Default for MachineStore {
    fn default() -> MachineStore {
        MachineStore::new()
    }
}

impl MachineStore {
    /// A fresh, empty store with no durability (in-RAM only).
    pub fn new() -> MachineStore {
        MachineStore::with_persistence(Arc::new(NullMachines))
    }

    /// A store seeded from — and writing through to — `persistence`. Prior records are
    /// reloaded and indexed at construction.
    pub fn with_persistence(persistence: Arc<dyn MachinePersistence>) -> MachineStore {
        let store = MachineStore {
            machines: Mutex::new(BTreeMap::new()),
            by_owner: Mutex::new(BTreeMap::new()),
            persistence,
        };
        for machine in store.persistence.load() {
            store.index_insert(&machine);
            lock(&store.machines).insert(machine.id.clone(), machine);
        }
        store
    }

    fn index_insert(&self, machine: &Machine) {
        lock(&self.by_owner)
            .entry(machine.owner.clone())
            .or_default()
            .insert(machine.id.clone());
    }

    fn index_remove(&self, owner: &str, id: &str) {
        let mut idx = lock(&self.by_owner);
        if let Some(ids) = idx.get_mut(owner) {
            ids.remove(id);
            if ids.is_empty() {
                idx.remove(owner);
            }
        }
    }

    fn mint_id(&self) -> String {
        mint_token("mch_")
    }

    /// Create + fulfill a machine for `app`, owned by `owner`, through `launcher`. The
    /// record is indexed and persisted before return.
    pub fn create(
        &self,
        app: &str,
        owner: &str,
        req: &CreateMachineRequest,
        launcher: &dyn MachineLauncher,
    ) -> Result<Machine, String> {
        let id = self.mint_id();
        let mut machine = Machine {
            id: id.clone(),
            name: if req.name.trim().is_empty() {
                id.clone()
            } else {
                req.name.clone()
            },
            app: app.to_string(),
            owner: owner.to_string(),
            state: MachineState::Stopped,
            region: req.config.region.clone(),
            config: req.config.clone(),
        };
        machine.state = launcher.launch(&machine)?;
        self.index_insert(&machine);
        lock(&self.machines).insert(id, machine.clone());
        self.persistence.upsert(&machine);
        Ok(machine)
    }

    /// One machine by id, **only if** it is in `app` AND owned by `owner`. A wrong owner
    /// or wrong app yields `None` — the same result as a non-existent id, so ownership
    /// is not an oracle.
    pub fn get_owned(&self, app: &str, id: &str, owner: &str) -> Option<Machine> {
        lock(&self.machines)
            .get(id)
            .filter(|m| m.app == app && m.owner == owner)
            .cloned()
    }

    /// Set an owned machine's state (stop / start). `None` (no write) unless the record
    /// exists in `app` and is owned by `owner`.
    pub fn set_state_owned(
        &self,
        app: &str,
        id: &str,
        owner: &str,
        state: MachineState,
    ) -> Option<Machine> {
        let updated = {
            let mut guard = lock(&self.machines);
            let m = guard
                .get_mut(id)
                .filter(|m| m.app == app && m.owner == owner)?;
            m.state = state;
            m.clone()
        };
        self.persistence.upsert(&updated);
        Some(updated)
    }

    /// Destroy an owned machine record. `None` unless it exists in `app` and is owned by
    /// `owner`.
    pub fn delete_owned(&self, app: &str, id: &str, owner: &str) -> Option<Machine> {
        let removed = {
            let mut guard = lock(&self.machines);
            if guard
                .get(id)
                .map(|m| m.app == app && m.owner == owner)
                .unwrap_or(false)
            {
                guard.remove(id)
            } else {
                None
            }
        }?;
        self.index_remove(&removed.owner, &removed.id);
        self.persistence.remove(&removed.id);
        Some(removed)
    }

    /// Every machine owned by `owner`, across apps, ordered by id — O(owned) via the
    /// owner index, never a full-store scan.
    pub fn list_for_owner(&self, owner: &str) -> Vec<Machine> {
        let ids: Vec<String> = lock(&self.by_owner)
            .get(owner)
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default();
        let guard = lock(&self.machines);
        ids.into_iter()
            .filter_map(|id| guard.get(&id).cloned())
            .collect()
    }

    /// The machines owned by `owner` within `app`, ordered by id.
    pub fn list_owned_in_app(&self, app: &str, owner: &str) -> Vec<Machine> {
        self.list_for_owner(owner)
            .into_iter()
            .filter(|m| m.app == app)
            .collect()
    }

    /// Total machine count across all owners (for the gateway status surface only).
    pub fn count(&self) -> usize {
        lock(&self.machines).len()
    }
}

/// The fly-machines API handler: classifies with [`crate::route`] and drives the
/// [`MachineStore`] through the injected [`MachineLauncher`], **owner-enforced on every
/// route**. Every machine route requires a verified `subject`; a machine is only ever
/// exposed / mutated for its owner.
///
/// The store is shared (`Arc`) so the assembled gateway reads the same records through
/// the cap-scoped `/api/machines` surface.
pub struct MachinesHandler {
    store: Arc<MachineStore>,
    launcher: Arc<dyn MachineLauncher>,
}

impl MachinesHandler {
    /// A handler over a fresh store with the in-process [`NullLauncher`].
    pub fn new() -> MachinesHandler {
        MachinesHandler {
            store: Arc::new(MachineStore::new()),
            launcher: Arc::new(NullLauncher),
        }
    }

    /// A handler over `store` with a specific launcher (the production compute backend).
    pub fn over(store: Arc<MachineStore>, launcher: Arc<dyn MachineLauncher>) -> MachinesHandler {
        MachinesHandler { store, launcher }
    }

    /// A handler with a specific launcher over a fresh store.
    pub fn with_launcher(launcher: Arc<dyn MachineLauncher>) -> MachinesHandler {
        MachinesHandler {
            store: Arc::new(MachineStore::new()),
            launcher,
        }
    }

    /// The backing store (the source `/api/machines` reads) — shareable.
    pub fn store(&self) -> &Arc<MachineStore> {
        &self.store
    }

    /// Dispatch a classified request. `subject` is the verified caller; **every** machine
    /// route requires it (`401` when absent) and is enforced against the record owner
    /// (`404` on a mismatch, indistinguishable from non-existence).
    pub fn respond(
        &self,
        method: HttpMethod,
        target: &str,
        body: &[u8],
        subject: Option<&str>,
    ) -> WebResponse {
        let owner = subject.map(str::trim).filter(|s| !s.is_empty());
        match route::parse(method, target) {
            Route::CreateMachine { app } => {
                let Some(owner) = owner else {
                    return unauthorized();
                };
                let req: CreateMachineRequest = match serde_json::from_slice(body) {
                    Ok(r) => r,
                    Err(_) if body.is_empty() => CreateMachineRequest::default(),
                    Err(e) => return WebResponse::error(400, format!("bad create body: {e}")),
                };
                match self.store.create(app, owner, &req, self.launcher.as_ref()) {
                    Ok(m) => machine_json(201, &m),
                    Err(e) => WebResponse::error(502, format!("launch failed: {e}")),
                }
            }
            Route::ListMachines { app } => {
                let Some(owner) = owner else {
                    return unauthorized();
                };
                let page = Page::from_target(target);
                json_ok(&page.apply(self.store.list_owned_in_app(app, owner)))
            }
            Route::GetMachine { app, id } => {
                let Some(owner) = owner else {
                    return unauthorized();
                };
                match self.store.get_owned(app, id, owner) {
                    Some(m) => machine_json(200, &m),
                    None => not_found(),
                }
            }
            Route::StopMachine { app, id } => {
                let Some(owner) = owner else {
                    return unauthorized();
                };
                match self.store.get_owned(app, id, owner) {
                    Some(m) => {
                        let _ = self.launcher.reap(&m);
                        let updated = self
                            .store
                            .set_state_owned(app, id, owner, MachineState::Stopped)
                            .unwrap_or(m);
                        machine_json(200, &updated)
                    }
                    None => not_found(),
                }
            }
            Route::StartMachine { app, id } => {
                let Some(owner) = owner else {
                    return unauthorized();
                };
                match self.store.get_owned(app, id, owner) {
                    Some(m) => match self.launcher.launch(&m) {
                        Ok(state) => {
                            let updated = self
                                .store
                                .set_state_owned(app, id, owner, state)
                                .unwrap_or(m);
                            machine_json(200, &updated)
                        }
                        Err(e) => WebResponse::error(502, format!("start failed: {e}")),
                    },
                    None => not_found(),
                }
            }
            Route::DeleteMachine { app, id } => {
                let Some(owner) = owner else {
                    return unauthorized();
                };
                match self.store.delete_owned(app, id, owner) {
                    Some(mut m) => {
                        m.state = MachineState::Destroyed;
                        machine_json(200, &m)
                    }
                    None => not_found(),
                }
            }
            _ => WebResponse::error(404, "unknown machines surface"),
        }
    }
}

impl Default for MachinesHandler {
    fn default() -> MachinesHandler {
        MachinesHandler::new()
    }
}

fn unauthorized() -> WebResponse {
    WebResponse::error(
        401,
        "the machines API is cap-scoped; present a verified subject",
    )
}

fn not_found() -> WebResponse {
    WebResponse::error(404, "no such machine")
}

fn machine_json(status: u16, machine: &Machine) -> WebResponse {
    let body = serde_json::to_vec(machine).unwrap_or_default();
    WebResponse {
        status,
        content_type: "application/json".to_string(),
        body,
    }
}

fn json_ok<T: Serialize>(value: &T) -> WebResponse {
    WebResponse::json(serde_json::to_vec(value).unwrap_or_default())
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: &str = "dregg:alice";
    const BOB: &str = "dregg:bob";

    fn create_body() -> Vec<u8> {
        serde_json::to_vec(&CreateMachineRequest {
            name: "web".into(),
            config: MachineConfig {
                guest: GuestConfig {
                    cpus: 1,
                    memory_mb: 256,
                    image: "workload:agent".into(),
                },
                region: "iad".into(),
            },
        })
        .unwrap()
    }

    fn create(h: &MachinesHandler, app: &str, subject: &str) -> Machine {
        let resp = h.respond(
            HttpMethod::Post,
            &format!("/v1/apps/{app}/machines"),
            &create_body(),
            Some(subject),
        );
        assert_eq!(resp.status, 201, "{}", resp.body_str());
        serde_json::from_slice(&resp.body).unwrap()
    }

    #[test]
    fn create_list_get_stop_start_delete_owner_scoped() {
        let h = MachinesHandler::new();
        let m = create(&h, "app1", ALICE);
        assert_eq!(m.owner, ALICE);
        assert_eq!(m.state, MachineState::Started);
        // Unguessable id, not a sequential counter.
        assert!(m.id.starts_with("mch_"));
        assert_eq!(m.id.len(), "mch_".len() + 32);

        // List (owner-scoped).
        let listed = h.respond(HttpMethod::Get, "/v1/apps/app1/machines", &[], Some(ALICE));
        let all: Vec<Machine> = serde_json::from_slice(&listed.body).unwrap();
        assert_eq!(all.len(), 1);

        // Get / stop / start (owner-scoped).
        let got = h.respond(
            HttpMethod::Get,
            &format!("/v1/apps/app1/machines/{}", m.id),
            &[],
            Some(ALICE),
        );
        assert_eq!(got.status, 200);

        let stopped = h.respond(
            HttpMethod::Post,
            &format!("/v1/apps/app1/machines/{}/stop", m.id),
            &[],
            Some(ALICE),
        );
        let sm: Machine = serde_json::from_slice(&stopped.body).unwrap();
        assert_eq!(sm.state, MachineState::Stopped);

        let started = h.respond(
            HttpMethod::Post,
            &format!("/v1/apps/app1/machines/{}/start", m.id),
            &[],
            Some(ALICE),
        );
        let stm: Machine = serde_json::from_slice(&started.body).unwrap();
        assert_eq!(stm.state, MachineState::Started);

        // Delete -> destroyed, then gone.
        let del = h.respond(
            HttpMethod::Delete,
            &format!("/v1/apps/app1/machines/{}", m.id),
            &[],
            Some(ALICE),
        );
        let dm: Machine = serde_json::from_slice(&del.body).unwrap();
        assert_eq!(dm.state, MachineState::Destroyed);
        assert_eq!(
            h.respond(
                HttpMethod::Get,
                &format!("/v1/apps/app1/machines/{}", m.id),
                &[],
                Some(ALICE)
            )
            .status,
            404
        );
    }

    // THE CLOSED CROSS-TENANT HOLE: Bob cannot read / stop / start / delete Alice's
    // machine even knowing the exact app + id. Every attempt is a 404 (not a 403 — the
    // record's existence is never confirmed to a non-owner), and the record is untouched.
    #[test]
    fn a_stranger_cannot_touch_anothers_machine_even_knowing_app_and_id() {
        let h = MachinesHandler::new();
        let m = create(&h, "app1", ALICE);
        let base = format!("/v1/apps/app1/machines/{}", m.id);

        for (method, path) in [
            (HttpMethod::Get, base.clone()),
            (HttpMethod::Post, format!("{base}/stop")),
            (HttpMethod::Post, format!("{base}/start")),
            (HttpMethod::Delete, base.clone()),
        ] {
            let resp = h.respond(method, &path, &[], Some(BOB));
            assert_eq!(
                resp.status, 404,
                "{method} {path} by a stranger must be 404, got {}",
                resp.status
            );
        }

        // Alice's machine is untouched: still Started, still present, still hers.
        let got = h.respond(HttpMethod::Get, &base, &[], Some(ALICE));
        assert_eq!(got.status, 200);
        let after: Machine = serde_json::from_slice(&got.body).unwrap();
        assert_eq!(after.state, MachineState::Started, "no stranger stopped it");
        assert_eq!(after.owner, ALICE);

        // Bob's own list never shows Alice's machine.
        let bob_list = h.respond(HttpMethod::Get, "/v1/apps/app1/machines", &[], Some(BOB));
        let bob_machines: Vec<Machine> = serde_json::from_slice(&bob_list.body).unwrap();
        assert!(bob_machines.is_empty(), "a stranger's list is empty");
    }

    #[test]
    fn every_route_requires_a_subject() {
        let h = MachinesHandler::new();
        let m = create(&h, "app1", ALICE);
        let base = format!("/v1/apps/app1/machines/{}", m.id);
        for (method, path) in [
            (HttpMethod::Post, "/v1/apps/app1/machines".to_string()),
            (HttpMethod::Get, "/v1/apps/app1/machines".to_string()),
            (HttpMethod::Get, base.clone()),
            (HttpMethod::Post, format!("{base}/stop")),
            (HttpMethod::Post, format!("{base}/start")),
            (HttpMethod::Delete, base.clone()),
        ] {
            assert_eq!(
                h.respond(method, &path, &[], None).status,
                401,
                "{method} {path} without a subject must be 401"
            );
            assert_eq!(
                h.respond(method, &path, &[], Some("   ")).status,
                401,
                "{method} {path} with an empty subject must be 401"
            );
        }
        // The refused create left no record.
        assert_eq!(h.store().count(), 1, "only Alice's create landed");
    }

    #[test]
    fn a_launcher_failure_is_a_502() {
        struct FailLauncher;
        impl MachineLauncher for FailLauncher {
            fn launch(&self, _m: &Machine) -> Result<MachineState, String> {
                Err("no compute".into())
            }
        }
        let h = MachinesHandler::with_launcher(Arc::new(FailLauncher));
        let resp = h.respond(
            HttpMethod::Post,
            "/v1/apps/app1/machines",
            &create_body(),
            Some(ALICE),
        );
        assert_eq!(resp.status, 502);
    }

    #[test]
    fn list_is_paginated() {
        let h = MachinesHandler::new();
        for _ in 0..5 {
            create(&h, "app1", ALICE);
        }
        let resp = h.respond(
            HttpMethod::Get,
            "/v1/apps/app1/machines?limit=2&offset=1",
            &[],
            Some(ALICE),
        );
        let page: Vec<Machine> = serde_json::from_slice(&resp.body).unwrap();
        assert_eq!(page.len(), 2, "the window is honoured");
    }

    #[test]
    fn owner_index_scopes_reads_without_cross_talk() {
        let store = MachineStore::new();
        store
            .create(
                "app-a",
                ALICE,
                &CreateMachineRequest::default(),
                &NullLauncher,
            )
            .unwrap();
        store
            .create(
                "app-b",
                BOB,
                &CreateMachineRequest::default(),
                &NullLauncher,
            )
            .unwrap();
        assert_eq!(store.list_for_owner(ALICE).len(), 1);
        assert_eq!(store.list_for_owner(BOB).len(), 1);
        assert!(store.list_for_owner("dregg:nobody").is_empty());
        // Deleting Alice's machine drops it from her index.
        let mine = store.list_for_owner(ALICE);
        store
            .delete_owned("app-a", &mine[0].id, ALICE)
            .expect("owner deletes");
        assert!(store.list_for_owner(ALICE).is_empty());
    }
}

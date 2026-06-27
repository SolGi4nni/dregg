//! The **Service Directory** — the deos-interior face of SERVICE DISCOVERY +
//! ANNOUNCEMENT.
//!
//! Where [`crate::service_explorer`] is the *per-cell* Postman (one focused
//! cell's published interface, pick a method, invoke), the service directory is
//! its *whole-image* sibling: it BROWSES the live image for every cell that
//! publishes a service interface, and lets the operator ANNOUNCE a service as a
//! real verified turn so the announcement leaves a witnessed receipt.
//!
//! # What "the directory" IS here (grounded)
//!
//! The canonical `dregg-directory` crate (`Directory::{register, lookup, revoke,
//! discover}`, `DirectoryEntry`, `EntryKind`) is the *userspace name→handle*
//! primitive (a versioned `BTreeMap`, the lifted `rbg::directory::DirectoryCell`
//! pattern). It is NOT wired into the cockpit's embedded [`World`] as an on-ledger
//! cell. The genuine "directory of services" present in a live image is therefore
//! the set of LEDGER CELLS THAT PUBLISH AN INTERFACE: a cell that does
//! method-dispatch auto-derives its [`InterfaceDescriptor`]
//! ([`InterfaceDescriptor::derive_replayable`]) — exactly the
//! cells-as-service-objects model. This module reads that, with NO new dependency
//! and NO ledger wiring: a `discover()` scans `World::ledger()`, derives each
//! cell's interface, and presents the cells that expose ≥1 method as discovered
//! services. (Per `cell/src/lib.rs:40` the interface is a non-committed USERSPACE
//! object — derived, not a committed cell field — so the read is over the program,
//! not a commitment.)
//!
//! # ANNOUNCE — a real verified turn
//!
//! The `dregg-directory` crate's stated stance (see its `lib.rs`) is that a
//! directory "emits standard `Effect::SetField` + `Effect::EmitEvent` actions
//! rather than introducing a new effect variant." So an announcement here is a
//! real verified turn carrying an [`Effect::EmitEvent`] whose `topic` is the
//! canonical announce symbol and whose `data` carries the service's
//! `interface_id` and method count. It commits through the embedded executor
//! ([`World::commit_turn`]) and leaves a real [`TurnReceipt`] in the receipt
//! nervous system. `discover()` then reads those announcement events back out of
//! the recorded history, so a discovered service is marked `announced` exactly
//! when a genuine announce turn for its interface has committed — the loop closes
//! over the real ledger, not a transient in-memory flag.
//!
//! gpui-free and `cargo test`-able, exactly like [`crate::service_explorer`].

use dregg_cell::interface::InterfaceDescriptor;
use dregg_cell::CellId;
use dregg_turn::action::{
    symbol as method_symbol, Action, Authorization, CommitmentMode, DelegationMode, Effect, Event,
};
use dregg_turn::turn::TurnReceipt;

use crate::reflect;
use crate::replay::RecordedStep;
use crate::world::{CommitOutcome, World};

/// The canonical announce topic — the symbol an announcement [`Effect::EmitEvent`]
/// carries. Anyone scanning the receipt history for service announcements matches
/// this topic.
pub fn announce_topic() -> [u8; 32] {
    method_symbol("dregg.directory.announce")
}

/// What kind of resource a discovered entry points at — a local mirror of
/// [`dregg_directory::EntryKind`] (kept local so this view-model carries no new
/// crate dependency; the canonical `dregg-directory` integration is the named
/// next build). A cell that publishes methods is a [`ServiceKind::Service`]; a
/// cell with no published interface is an opaque [`ServiceKind::Capability`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServiceKind {
    /// An invocable service — a cell with a non-empty published interface.
    Service,
    /// An opaque capability the directory does not introspect (no published
    /// interface).
    Capability,
}

impl ServiceKind {
    pub fn label(self) -> &'static str {
        match self {
            ServiceKind::Service => "service",
            ServiceKind::Capability => "capability",
        }
    }
}

/// One **discovered service** — a ledger cell as it appears in the directory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiscoveredService {
    /// The backing cell on the live ledger.
    pub cell: CellId,
    /// The legible handle (short-hex of the cell id) the UI shows.
    pub label: String,
    /// The content-address of the cell's published interface (its `interface_id`),
    /// the stable handle an announcement names + a verifier could witness
    /// route-membership against.
    pub interface_id: [u8; 32],
    /// How many methods the cell's interface publishes.
    pub method_count: usize,
    /// What kind of resource this entry points at.
    pub kind: ServiceKind,
    /// Whether a genuine announce turn for this interface has committed (read back
    /// from the receipt history, not a transient flag).
    pub announced: bool,
}

/// A filter over the directory listing — the local mirror of
/// [`dregg_directory::DiscoveryFilter`], scoped to what the first slice needs.
#[derive(Clone, Debug, Default)]
pub struct ServiceFilter {
    /// Match entries whose short-hex label starts with this prefix.
    pub label_prefix: Option<String>,
    /// Restrict to a single kind.
    pub kind: Option<ServiceKind>,
    /// Only entries that have been announced.
    pub only_announced: bool,
    /// Include cells that publish NO interface (otherwise the listing is just the
    /// service-publishing cells — the default, the "services" view).
    pub include_non_services: bool,
}

/// The outcome of ANNOUNCING a service — the publish half of the loop.
#[derive(Debug)]
pub enum AnnounceOutcome {
    /// The announcement COMMITTED a real verified turn. Carries the executor's own
    /// [`TurnReceipt`] and the `interface_id` it announced.
    Announced {
        receipt: Box<TurnReceipt>,
        interface_id: [u8; 32],
        method_count: usize,
    },
    /// The announcement was REFUSED, surfaced IN-BAND. `by_executor` distinguishes
    /// the userspace front-door refusal (the cell is absent / publishes no
    /// interface — nothing to announce) from the real executor rejecting the
    /// announce turn (a permissions gate fired).
    Refused { reason: String, by_executor: bool },
}

impl AnnounceOutcome {
    pub fn is_announced(&self) -> bool {
        matches!(self, AnnounceOutcome::Announced { .. })
    }
}

/// **THE SERVICE DIRECTORY VIEW** — every service-publishing cell in the live
/// image, built fresh off [`World`].
#[derive(Clone, Debug)]
pub struct ServiceDirectory {
    /// The discovered services (filtered).
    pub services: Vec<DiscoveredService>,
    /// How many distinct services have been announced (across the whole image).
    pub announced_count: usize,
}

impl ServiceDirectory {
    /// **BROWSE** — scan the live ledger for service-publishing cells, deriving
    /// each cell's interface, and present them as discovered services. Announce
    /// events are read back from the recorded history so each entry's `announced`
    /// bit reflects the real ledger.
    pub fn discover(world: &World, filter: &ServiceFilter) -> Self {
        let announced = announced_interface_ids(world);

        let mut services: Vec<DiscoveredService> = world
            .ledger()
            .iter()
            .map(|(id, cell)| {
                let descriptor = InterfaceDescriptor::derive_replayable(&cell.program);
                let method_count = descriptor.methods.len();
                let kind = if method_count > 0 {
                    ServiceKind::Service
                } else {
                    ServiceKind::Capability
                };
                DiscoveredService {
                    cell: *id,
                    label: reflect::short_hex(id.as_bytes()),
                    interface_id: descriptor.interface_id,
                    method_count,
                    kind,
                    announced: announced.contains(&descriptor.interface_id),
                }
            })
            .filter(|s| {
                if !filter.include_non_services && s.kind == ServiceKind::Capability {
                    return false;
                }
                if filter.only_announced && !s.announced {
                    return false;
                }
                if let Some(k) = filter.kind {
                    if s.kind != k {
                        return false;
                    }
                }
                if let Some(p) = &filter.label_prefix {
                    if !s.label.starts_with(p) {
                        return false;
                    }
                }
                true
            })
            .collect();

        // Deterministic order (the rail order survives across commits): by label.
        services.sort_by(|a, b| a.label.cmp(&b.label));

        let announced_count = services.iter().filter(|s| s.announced).count();
        ServiceDirectory {
            services,
            announced_count,
        }
    }

    /// Look up a discovered service by its short-hex label.
    pub fn service(&self, label: &str) -> Option<&DiscoveredService> {
        self.services.iter().find(|s| s.label == label)
    }

    /// **ANNOUNCE a service — the publish half, a real verified turn.**
    ///
    /// An announcement is the ANNOUNCER'S turn that PUBLISHES a `service` cell's
    /// interface to the directory — NOT a method-call on the service cell itself.
    /// (A service cell with a strict `Cases` program default-denies any undeclared
    /// method — the Cav-Codex Block 4 operation-discrimination rule, `cell/src/
    /// program/eval.rs:87` — so impersonating the service's program would be
    /// refused. The announcer is the operator's own principal, whose turn
    /// references the service.)
    ///
    /// Derives `service`'s interface off its live program; refuses in-band if the
    /// service is absent or publishes no interface (nothing to announce).
    /// Otherwise builds an [`Effect::EmitEvent`] emitted by `announcer`, carrying
    /// [`announce_topic`] + the service `interface_id`, the service cell id, and
    /// the method count, wraps it as the announcer's turn (via
    /// [`World::wrap_action_turn`]), and commits through the real executor. A
    /// committed announcement is visible to the next [`Self::discover`] as
    /// `announced = true` (read back from the receipt history). The executor still
    /// gates the announcer's own program + permissions — an announcer that may not
    /// emit is refused with `by_executor = true`.
    pub fn announce(world: &mut World, announcer: CellId, service: CellId) -> AnnounceOutcome {
        let descriptor = match world.ledger().get(&service) {
            Some(c) => InterfaceDescriptor::derive_replayable(&c.program),
            None => {
                return AnnounceOutcome::Refused {
                    reason: format!(
                        "cell {} is absent from the ledger — nothing to announce",
                        reflect::short_hex(service.as_bytes())
                    ),
                    by_executor: false,
                };
            }
        };

        if descriptor.methods.is_empty() {
            return AnnounceOutcome::Refused {
                reason: format!(
                    "cell {} publishes no interface (it dispatches on no method) — there is no \
                     service to announce",
                    reflect::short_hex(service.as_bytes())
                ),
                by_executor: false,
            };
        }

        let interface_id = descriptor.interface_id;
        let method_count = descriptor.methods.len();

        // The announcement payload: the interface_id (felt 0), the announced
        // service cell id (felt 1), the method count (felt 2). The directory
        // crate's "emit a standard EmitEvent" stance — no new effect variant.
        let mut count_felt = [0u8; 32];
        count_felt[..8].copy_from_slice(&(method_count as u64).to_le_bytes());
        let event = Event {
            topic: announce_topic(),
            data: vec![interface_id, *service.as_bytes(), count_felt],
        };

        let action = Action {
            target: announcer,
            method: announce_topic(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::EmitEvent {
                cell: announcer,
                event,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let turn = world.wrap_action_turn(announcer, action);

        match world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => AnnounceOutcome::Announced {
                receipt,
                interface_id,
                method_count,
            },
            CommitOutcome::Rejected { reason, .. } => AnnounceOutcome::Refused {
                reason,
                by_executor: true,
            },
            CommitOutcome::Queued { .. } => AnnounceOutcome::Refused {
                reason: "the world is suspended; the announcement was staged in the pending queue"
                    .to_string(),
                by_executor: false,
            },
        }
    }

    /// Every line of text the directory renders, flattened — so a test (and a
    /// headless bake) can assert the surface speaks real text about the real
    /// services.
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!(
            "service-directory · {} service(s) · {} announced",
            self.services.len(),
            self.announced_count
        ));
        for s in &self.services {
            out.push(format!(
                "· {} [{}] · interface {} · {} method(s){}",
                s.label,
                s.kind.label(),
                reflect::short_hex(&s.interface_id),
                s.method_count,
                if s.announced { " · ANNOUNCED" } else { "" }
            ));
        }
        out
    }
}

/// Walk the recorded turn history and collect the `interface_id`s that a genuine
/// announce turn has emitted (an [`Effect::EmitEvent`] whose topic is
/// [`announce_topic`], whose first data felt is the announced `interface_id`).
fn announced_interface_ids(world: &World) -> std::collections::HashSet<[u8; 32]> {
    let topic = announce_topic();
    let mut out = std::collections::HashSet::new();
    for step in world.recorded_turns().steps() {
        let RecordedStep::Committed { turn, .. } = step else {
            continue;
        };
        for root in &turn.call_forest.roots {
            for effect in &root.action.effects {
                if let Effect::EmitEvent { event, .. } = effect {
                    if event.topic == topic {
                        if let Some(id) = event.data.first() {
                            out.insert(*id);
                        }
                    }
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard};
    use dregg_cell::AuthRequired;

    /// Install a `Cases` program so the cell's derived interface publishes the
    /// given methods (plus an `Always` catch-all so non-method writes commit), and
    /// open its permissions so a turn can run. Returns the cell id.
    fn cell_publishing(world: &mut World, seed: u8, methods: &[&str]) -> CellId {
        let id = world.genesis_cell(seed, 1_000);
        let mut cases: Vec<TransitionCase> = methods
            .iter()
            .map(|name| TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: method_symbol(name),
                },
                constraints: vec![],
            })
            .collect();
        cases.push(TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![],
        });
        assert!(world.set_cell_program(&id, CellProgram::Cases(cases)));
        world.genesis_open_permissions(&id);
        id
    }

    #[test]
    fn discover_lists_service_publishing_cells_from_the_real_ledger() {
        let mut w = World::new();
        let svc = cell_publishing(&mut w, 0x10, &["send", "dequeue"]);
        // A plain cell with no method-dispatch program publishes no interface.
        let _plain = w.genesis_cell(0x11, 500);

        let dir = ServiceDirectory::discover(&w, &ServiceFilter::default());

        // The default ("services" view) lists the publishing cell, not the plain one.
        assert_eq!(dir.services.len(), 1);
        let entry = &dir.services[0];
        assert_eq!(entry.cell, svc);
        assert_eq!(entry.kind, ServiceKind::Service);
        assert_eq!(entry.method_count, 2);
        assert!(!entry.announced, "nothing announced yet");
        assert!(dir
            .all_text()
            .iter()
            .any(|l| l.contains("1 service(s) · 0 announced")));
    }

    /// A plain principal (no method-dispatch program) with open permissions — the
    /// operator that announces a service. Its turn is admitted by the executor.
    fn announcer_principal(world: &mut World, seed: u8) -> CellId {
        let id = world.genesis_cell(seed, 1_000);
        world.genesis_open_permissions(&id);
        id
    }

    #[test]
    fn announce_commits_a_real_turn_and_discover_reads_it_back() {
        let mut w = World::new();
        let svc = cell_publishing(&mut w, 0x20, &["write"]);
        let op = announcer_principal(&mut w, 0x21);
        let iface = InterfaceDescriptor::derive_replayable(&w.ledger().get(&svc).unwrap().program);

        let outcome = ServiceDirectory::announce(&mut w, op, svc);
        let (receipt, announced_id) = match outcome {
            AnnounceOutcome::Announced {
                receipt,
                interface_id,
                ..
            } => (receipt, interface_id),
            AnnounceOutcome::Refused { reason, .. } => {
                panic!("an open-permission announcer should announce: {reason}")
            }
        };
        assert_eq!(announced_id, iface.interface_id);
        assert_eq!(
            receipt.agent, op,
            "the announcement is the announcer's turn"
        );
        assert_eq!(w.receipts().len(), 1, "the announce committed a real turn");

        // THE LOOP CLOSES: a fresh discover reads the announcement back off the
        // recorded history and marks the service announced.
        let dir = ServiceDirectory::discover(&w, &ServiceFilter::default());
        let entry = dir.service(&reflect::short_hex(svc.as_bytes())).unwrap();
        assert!(entry.announced, "the committed announcement is read back");
        assert_eq!(dir.announced_count, 1);

        // The only-announced filter now admits it.
        let only = ServiceDirectory::discover(
            &w,
            &ServiceFilter {
                only_announced: true,
                ..Default::default()
            },
        );
        assert_eq!(only.services.len(), 1);
    }

    #[test]
    fn announcing_a_non_service_cell_is_refused_in_band() {
        let mut w = World::new();
        let plain = w.genesis_cell(0x30, 500);
        let op = announcer_principal(&mut w, 0x31);

        let outcome = ServiceDirectory::announce(&mut w, op, plain);
        match outcome {
            AnnounceOutcome::Refused {
                reason,
                by_executor,
            } => {
                assert!(!by_executor, "a no-interface cell is a front-door refusal");
                assert!(reason.contains("publishes no interface"));
            }
            AnnounceOutcome::Announced { .. } => panic!("a non-service cannot announce"),
        }
        assert_eq!(w.receipts().len(), 0, "no turn ran");
    }

    #[test]
    fn announcing_an_absent_cell_is_refused_in_band() {
        let mut w = World::new();
        // A cell id that was never seeded onto the ledger.
        let ghost = cell_publishing(&mut w, 0x40, &["x"]);
        let mut w2 = World::new();
        let op = announcer_principal(&mut w2, 0x41);
        let outcome = ServiceDirectory::announce(&mut w2, op, ghost);
        assert!(matches!(
            outcome,
            AnnounceOutcome::Refused {
                by_executor: false,
                ..
            }
        ));
    }

    #[test]
    fn filter_by_label_prefix_and_kind() {
        let mut w = World::new();
        let svc = cell_publishing(&mut w, 0x50, &["m"]);
        let prefix = reflect::short_hex(svc.as_bytes())[..2].to_string();

        let hit = ServiceDirectory::discover(
            &w,
            &ServiceFilter {
                label_prefix: Some(prefix),
                kind: Some(ServiceKind::Service),
                ..Default::default()
            },
        );
        assert_eq!(hit.services.len(), 1);

        let miss = ServiceDirectory::discover(
            &w,
            &ServiceFilter {
                label_prefix: Some("zzzz".into()),
                ..Default::default()
            },
        );
        assert!(miss.services.is_empty());
    }

    #[test]
    fn include_non_services_widens_the_listing() {
        let mut w = World::new();
        let _svc = cell_publishing(&mut w, 0x60, &["m"]);
        let _plain = w.genesis_cell(0x61, 100);

        let services_only = ServiceDirectory::discover(&w, &ServiceFilter::default());
        let widened = ServiceDirectory::discover(
            &w,
            &ServiceFilter {
                include_non_services: true,
                ..Default::default()
            },
        );
        assert!(widened.services.len() > services_only.services.len());
        // The widened view carries the opaque capability cell too.
        assert!(widened
            .services
            .iter()
            .any(|s| s.kind == ServiceKind::Capability));
    }

    // The auth lattice the announce path will gate on once cap-gating lands (the
    // named next build): a viewer must hold authority over the cell to announce
    // its service. Documented here so the refinement has a home.
    #[test]
    fn announce_topic_is_stable() {
        assert_eq!(announce_topic(), method_symbol("dregg.directory.announce"));
        let _ = AuthRequired::None; // the lattice the cap-gate will consult
    }
}

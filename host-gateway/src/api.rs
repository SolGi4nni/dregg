//! The cap-scoped registry **read** surfaces a customer console populates from.
//!
//! Each surface returns exactly the records owned by the **authenticated subject**.
//! The subject is established by [`crate::auth::SubjectAuth`] — by default the gateway
//! verifies a presented `dga1_` credential itself and derives the subject from it (it
//! trusts no upstream header). The cap-scoping is the tooth: another subject's request
//! sees none of the caller's cells.
//!
//! ```text
//!   GET /api/sites              owned microsites            (name, owner, content_root, bytes)
//!   GET /api/domains            owned custom-domain bindings (owner == subject)
//!   GET /api/machines           owned fly-machines           (owner == subject)
//!   GET /api/servers            owned persistent servers     (lessee == subject)   [source]
//!   GET /api/agents             owned deployed agents         (owner == subject)    [source]
//!   GET /api/billing/spend      owned spend lines             (owner == subject)    [source]
//!   GET /api/billing/balances   { subject: balance }          (the caller's balance) [source]
//! ```
//!
//! ## What is LIVE vs a source seam
//!
//! The **sites** ([`crate::microsite::SiteRegistry`]), **domains**
//! ([`starbridge_domains::DomainRegistry`]), and **machines**
//! ([`crate::machines::MachineStore`]) surfaces read the gateway's own resident
//! registries directly — live. The server fleet, deployed-agent set, and $DREGG ledger
//! are pluggable [`ServerSource`] / [`AgentSource`] / [`BillingSource`] seams, wired
//! when the control / billing planes expose them and **empty until then** — never
//! fabricated (the honesty law).
//!
//! ## Fail closed
//!
//! A request with no resolved subject fails **closed** (`401`) — the gateway never
//! returns the unscoped, cloud-wide set.

use std::collections::BTreeMap;
use std::sync::Arc;

use http_serve::{HttpMethod, WebResponse};
use serde::{Deserialize, Serialize};

use starbridge_domains::DomainRegistry;

use crate::machines::MachineStore;
use crate::microsite::SiteRegistry;
use crate::page::Page;

/// The path prefix the console read surfaces are served under.
pub const API_PREFIX: &str = "/api";

/// A persistent-server record in the shape the console reads (`lessee` is the owner).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ServerView {
    /// The server id.
    pub id: String,
    /// The display name.
    pub name: String,
    /// The lessee renting the server — the OWNER the scope filters on.
    pub lessee: String,
    /// Lifecycle state (running/stopped/…).
    pub state: String,
    /// The region.
    pub region: String,
    /// The machine size label.
    pub size: String,
    /// The lease's funded budget (units).
    pub budget_units: i64,
    /// Per-period metered cost (units).
    pub per_period_units: i64,
    /// Periods metered so far.
    pub periods_metered: i64,
}

/// One spend ledger line in the shape the console reads (`owner` is the payer).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpendLine {
    /// The cap-account subject the charge is billed to — the OWNER scoped on.
    pub owner: String,
    /// What kind of resource the charge is for (server/site/bucket/…).
    pub resource_kind: String,
    /// The specific resource id.
    pub resource_id: String,
    /// The billing period label.
    pub period: String,
    /// The units charged.
    pub units: i64,
}

/// A deployed agent as the `/api/agents` surface renders it. `report` is passed through
/// verbatim as opaque JSON, so the gateway carries no dependency on the exec runtime.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AgentView {
    /// The owner subject — the field the scope filters on.
    pub owner: String,
    /// The agent id.
    pub id: String,
    /// The capabilities the agent was deployed with.
    pub caps: Vec<String>,
    /// The last run report, verbatim.
    pub report: serde_json::Value,
    /// The committed root the agent deployed from.
    pub deployed_root: String,
}

/// The persistent-server fleet the `/api/servers` surface reads (across all lessees;
/// the gateway scopes by subject). Absent ⇒ the surface is empty (the honesty law).
pub trait ServerSource: Send + Sync {
    /// Every server record across all lessees.
    fn servers(&self) -> Vec<ServerView>;
}

/// The deployed-agent set the `/api/agents` surface reads. Absent ⇒ empty.
pub trait AgentSource: Send + Sync {
    /// Every deployed agent across all owners.
    fn agents(&self) -> Vec<AgentView>;
}

/// The ledger the `/api/billing/*` surfaces read. Absent ⇒ empty.
pub trait BillingSource: Send + Sync {
    /// Every spend line across all owners.
    fn spend(&self) -> Vec<SpendLine>;
    /// Per-subject balances.
    fn balances(&self) -> BTreeMap<String, i64>;
}

/// The gateway HTTP handler that serves the cap-scoped console read surfaces.
///
/// A pure handler: [`respond`](ApiHandler::respond) takes an already-resolved subject.
/// The assembled [`crate::gateway::Gateway`] establishes that subject with a
/// [`crate::auth::SubjectAuth`] (verifying the presented credential) and dispatches
/// here.
pub struct ApiHandler {
    sites: Arc<SiteRegistry>,
    domains: Arc<DomainRegistry>,
    machines: Arc<MachineStore>,
    servers: Option<Arc<dyn ServerSource>>,
    billing: Option<Arc<dyn BillingSource>>,
    agents: Option<Arc<dyn AgentSource>>,
}

impl ApiHandler {
    /// Serve the resident site / domain / machine registries the gateway holds, with no
    /// server-fleet / agent / billing source (those surfaces are empty until wired).
    pub fn new(
        sites: Arc<SiteRegistry>,
        domains: Arc<DomainRegistry>,
        machines: Arc<MachineStore>,
    ) -> ApiHandler {
        ApiHandler {
            sites,
            domains,
            machines,
            servers: None,
            billing: None,
            agents: None,
        }
    }

    /// Attach the persistent-server fleet source (`/api/servers`).
    pub fn with_servers(mut self, servers: Arc<dyn ServerSource>) -> ApiHandler {
        self.servers = Some(servers);
        self
    }

    /// Attach the ledger source (`/api/billing/*`).
    pub fn with_billing(mut self, billing: Arc<dyn BillingSource>) -> ApiHandler {
        self.billing = Some(billing);
        self
    }

    /// Attach the deployed-agent source (`/api/agents`).
    pub fn with_agents(mut self, agents: Arc<dyn AgentSource>) -> ApiHandler {
        self.agents = Some(agents);
        self
    }

    /// Whether this handler serves `path`: anything beneath `/api/`.
    pub fn serves_path(path: &str) -> bool {
        let p = path.split('?').next().unwrap_or(path);
        p == API_PREFIX || p.starts_with("/api/")
    }

    /// Route + serve one read, scoped to `subject`. A missing/empty subject fails closed
    /// (`401`). The pure core — testable with an explicit subject.
    pub fn respond(&self, method: HttpMethod, target: &str, subject: Option<&str>) -> WebResponse {
        if method != HttpMethod::Get {
            return WebResponse::error(405, "the console read surfaces are GET-only");
        }
        let path = target.split('?').next().unwrap_or(target);
        let Some(subject) = subject.map(str::trim).filter(|s| !s.is_empty()) else {
            return WebResponse::error(
                401,
                "no verified subject; the console reads are cap-scoped",
            );
        };
        // Every array surface is bounded + windowed by the request's ?limit/?offset.
        let page = Page::from_target(target);
        match path {
            "/api/sites" => json_array(page.apply(self.sites_for(subject))),
            "/api/domains" => json_array(page.apply(self.domains_for(subject))),
            "/api/machines" => json_array(page.apply(self.machines_for(subject))),
            "/api/servers" => json_array(page.apply(self.servers_for(subject))),
            "/api/agents" => json_array(page.apply(self.agents_for(subject))),
            "/api/billing/spend" => json_array(page.apply(self.spend_for(subject))),
            "/api/billing/balances" => json_value(self.balances_for(subject)),
            _ => WebResponse::error(404, "unknown console read surface"),
        }
    }

    /// The subject's published microsites — compact metadata (no asset bodies). O(owned)
    /// via the registry's owner index.
    fn sites_for(&self, subject: &str) -> Vec<serde_json::Value> {
        self.sites
            .list_for_owner(subject)
            .into_iter()
            .map(|s| {
                serde_json::json!({
                    "name": s.name,
                    "owner": s.owner,
                    "content_root": s.content_root().to_string_cid(),
                    "assets": s.assets.len(),
                    "bytes": s.bytes(),
                    "status": "published",
                })
            })
            .collect()
    }

    /// The subject's bound custom domains (scoped by owner).
    fn domains_for(&self, subject: &str) -> Vec<serde_json::Value> {
        self.domains
            .list()
            .into_iter()
            .filter(|b| b.owner == subject)
            .filter_map(|b| serde_json::to_value(b).ok())
            .collect()
    }

    /// The subject's fly-machines (scoped by owner). O(owned) via the store's owner
    /// index — never a full-store scan.
    fn machines_for(&self, subject: &str) -> Vec<serde_json::Value> {
        self.machines
            .list_for_owner(subject)
            .into_iter()
            .filter_map(|m| serde_json::to_value(m).ok())
            .collect()
    }

    /// The subject's persistent servers (scoped by `lessee`).
    fn servers_for(&self, subject: &str) -> Vec<serde_json::Value> {
        let Some(src) = &self.servers else {
            return Vec::new();
        };
        src.servers()
            .into_iter()
            .filter(|s| s.lessee == subject)
            .filter_map(|s| serde_json::to_value(s).ok())
            .collect()
    }

    fn agents_for(&self, subject: &str) -> Vec<serde_json::Value> {
        let Some(src) = &self.agents else {
            return Vec::new();
        };
        src.agents()
            .into_iter()
            .filter(|a| a.owner == subject)
            .filter_map(|a| serde_json::to_value(a).ok())
            .collect()
    }

    /// The subject's spend lines (scoped by `owner`).
    fn spend_for(&self, subject: &str) -> Vec<serde_json::Value> {
        let Some(src) = &self.billing else {
            return Vec::new();
        };
        src.spend()
            .into_iter()
            .filter(|e| e.owner == subject)
            .filter_map(|e| serde_json::to_value(e).ok())
            .collect()
    }

    /// The subject's balance, as a `{ subject: balance }` object. Only the caller's own
    /// balance is exposed.
    fn balances_for(&self, subject: &str) -> serde_json::Value {
        let balance = self
            .billing
            .as_ref()
            .and_then(|src| src.balances().get(subject).copied())
            .unwrap_or(0);
        serde_json::json!({ subject: balance })
    }
}

/// A JSON-array response over the scoped records.
fn json_array(records: Vec<serde_json::Value>) -> WebResponse {
    json_value(serde_json::Value::Array(records))
}

/// A JSON response over an arbitrary value.
fn json_value(value: serde_json::Value) -> WebResponse {
    WebResponse {
        status: 200,
        content_type: "application/json".to_string(),
        body: value.to_string().into_bytes(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machines::{CreateMachineRequest, NullLauncher};
    use crate::microsite::Microsite;
    use starbridge_domains::{ChallengeMethod, DomainBinding};

    const ALICE: &str = "dregg:aaaa0000aaaa0000";
    const BOB: &str = "dregg:bbbb1111bbbb1111";

    struct Fleet(Vec<ServerView>);
    impl ServerSource for Fleet {
        fn servers(&self) -> Vec<ServerView> {
            self.0.clone()
        }
    }

    struct Roster(Vec<AgentView>);
    impl AgentSource for Roster {
        fn agents(&self) -> Vec<AgentView> {
            self.0.clone()
        }
    }

    struct Ledger {
        spend: Vec<SpendLine>,
        balances: BTreeMap<String, i64>,
    }
    impl BillingSource for Ledger {
        fn spend(&self) -> Vec<SpendLine> {
            self.spend.clone()
        }
        fn balances(&self) -> BTreeMap<String, i64> {
            self.balances.clone()
        }
    }

    fn agent(id: &str, owner: &str) -> AgentView {
        AgentView {
            owner: owner.into(),
            id: id.into(),
            caps: vec!["deploy".into()],
            report: serde_json::json!({ "receipts": 2 }),
            deployed_root: format!("root_{id}"),
        }
    }

    fn srv(id: &str, lessee: &str) -> ServerView {
        ServerView {
            id: id.into(),
            name: format!("{id}-api"),
            lessee: lessee.into(),
            state: "running".into(),
            region: "iad".into(),
            size: "small".into(),
            budget_units: 1000,
            per_period_units: 10,
            periods_metered: 3,
        }
    }

    /// A handler whose LIVE registries + source seams each hold records for TWO subjects,
    /// so the cap-scope is exercised non-vacuously.
    fn two_owner_handler() -> ApiHandler {
        let sites = Arc::new(SiteRegistry::new("dregg.net"));
        sites
            .publish(Microsite::new("alice-site", ALICE).with("/index.html", "alice"))
            .unwrap();
        sites
            .publish(Microsite::new("bob-secret", BOB).with("/index.html", "bob"))
            .unwrap();

        // Live domains: two verified bindings, adopted (no cap needed for the read side).
        let domains = Arc::new(DomainRegistry::new());
        domains.adopt(DomainBinding::verified(
            "alice.example.com",
            "alice-site",
            ALICE,
            ChallengeMethod::Txt,
            "nonce-a",
            1,
        ));
        domains.adopt(DomainBinding::verified(
            "bob.example.com",
            "bob-secret",
            BOB,
            ChallengeMethod::Txt,
            "nonce-b",
            2,
        ));

        // Live machines: one per owner.
        let machines = Arc::new(MachineStore::new());
        machines
            .create(
                "app-a",
                ALICE,
                &CreateMachineRequest::default(),
                &NullLauncher,
            )
            .unwrap();
        machines
            .create(
                "app-b",
                BOB,
                &CreateMachineRequest::default(),
                &NullLauncher,
            )
            .unwrap();

        let mut balances = BTreeMap::new();
        balances.insert(ALICE.to_string(), 500);
        balances.insert(BOB.to_string(), 12_000);
        let ledger = Ledger {
            spend: vec![
                SpendLine {
                    owner: ALICE.into(),
                    resource_kind: "server".into(),
                    resource_id: "srv_a".into(),
                    period: "p1".into(),
                    units: 1,
                },
                SpendLine {
                    owner: BOB.into(),
                    resource_kind: "server".into(),
                    resource_id: "srv_b".into(),
                    period: "p2".into(),
                    units: 450,
                },
            ],
            balances,
        };

        ApiHandler::new(sites, domains, machines)
            .with_servers(Arc::new(Fleet(vec![
                srv("srv_a", ALICE),
                srv("srv_b", BOB),
            ])))
            .with_billing(Arc::new(ledger))
            .with_agents(Arc::new(Roster(vec![
                agent("agt_a", ALICE),
                agent("agt_b", BOB),
            ])))
    }

    fn get(h: &ApiHandler, path: &str, subject: Option<&str>) -> serde_json::Value {
        let resp = h.respond(HttpMethod::Get, path, subject);
        assert_eq!(resp.status, 200, "{path}: {}", resp.body_str());
        serde_json::from_slice(&resp.body).unwrap()
    }

    #[test]
    fn each_surface_returns_only_the_callers_records() {
        let h = two_owner_handler();

        let sites = get(&h, "/api/sites", Some(ALICE));
        let arr = sites.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["name"], "alice-site");
        assert_eq!(arr[0]["owner"], ALICE);
        assert!(arr[0]["bytes"].as_u64().unwrap() > 0);
        // The site record carries a content-addressed root (a CIDv1 string).
        assert!(arr[0]["content_root"].as_str().unwrap().starts_with('b'));

        let domains = get(&h, "/api/domains", Some(ALICE));
        let arr = domains.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["domain"], "alice.example.com");
        assert_eq!(arr[0]["owner"], ALICE);

        let machines = get(&h, "/api/machines", Some(ALICE));
        let arr = machines.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["owner"], ALICE);
        assert_eq!(arr[0]["app"], "app-a");

        let servers = get(&h, "/api/servers", Some(ALICE));
        assert_eq!(servers.as_array().unwrap()[0]["id"], "srv_a");

        let agents = get(&h, "/api/agents", Some(ALICE));
        let arr = agents.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["id"], "agt_a");
        assert_eq!(arr[0]["report"]["receipts"], 2);

        let spend = get(&h, "/api/billing/spend", Some(ALICE));
        assert_eq!(spend.as_array().unwrap()[0]["resource_id"], "srv_a");
        let bal = get(&h, "/api/billing/balances", Some(ALICE));
        assert_eq!(bal[ALICE].as_i64().unwrap(), 500);
        assert!(
            bal.get(BOB).is_none(),
            "another subject's balance never leaks"
        );
    }

    #[test]
    fn a_different_subject_sees_none_of_anothers_records() {
        let h = two_owner_handler();

        let bob_sites = get(&h, "/api/sites", Some(BOB));
        let arr = bob_sites.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["name"], "bob-secret");
        assert!(!arr.iter().any(|s| s["name"] == "alice-site"));

        assert!(
            !get(&h, "/api/domains", Some(BOB))
                .as_array()
                .unwrap()
                .iter()
                .any(|d| d["domain"] == "alice.example.com")
        );

        assert!(
            !get(&h, "/api/machines", Some(BOB))
                .as_array()
                .unwrap()
                .iter()
                .any(|m| m["app"] == "app-a")
        );

        let stranger = "dregg:0000000000000000";
        assert!(
            get(&h, "/api/sites", Some(stranger))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            get(&h, "/api/domains", Some(stranger))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            get(&h, "/api/machines", Some(stranger))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            get(&h, "/api/billing/balances", Some(stranger))[stranger]
                .as_i64()
                .unwrap(),
            0
        );
    }

    #[test]
    fn no_subject_fails_closed() {
        let h = two_owner_handler();
        for path in [
            "/api/sites",
            "/api/domains",
            "/api/machines",
            "/api/servers",
            "/api/agents",
            "/api/billing/spend",
            "/api/billing/balances",
        ] {
            assert_eq!(
                h.respond(HttpMethod::Get, path, None).status,
                401,
                "{path} must fail closed without a subject"
            );
            assert_eq!(
                h.respond(HttpMethod::Get, path, Some("   ")).status,
                401,
                "{path} must reject an empty subject"
            );
        }
    }

    #[test]
    fn unset_sources_contribute_empty_not_fabricated() {
        let sites = Arc::new(SiteRegistry::new("dregg.net"));
        sites
            .publish(Microsite::new("s", ALICE).with("/index.html", "hi"))
            .unwrap();
        let h = ApiHandler::new(
            sites,
            Arc::new(DomainRegistry::new()),
            Arc::new(MachineStore::new()),
        );
        assert_eq!(
            get(&h, "/api/sites", Some(ALICE)).as_array().unwrap().len(),
            1
        );
        assert!(
            get(&h, "/api/servers", Some(ALICE))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            get(&h, "/api/agents", Some(ALICE))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            get(&h, "/api/billing/spend", Some(ALICE))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            get(&h, "/api/billing/balances", Some(ALICE))[ALICE]
                .as_i64()
                .unwrap(),
            0
        );
    }

    #[test]
    fn routing_predicate() {
        assert!(ApiHandler::serves_path("/api/sites"));
        assert!(ApiHandler::serves_path("/api/billing/balances"));
        assert!(!ApiHandler::serves_path("/apidocs"));
        assert!(!ApiHandler::serves_path("/v1/apps/x/machines"));
    }
}

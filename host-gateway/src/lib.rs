//! # host-gateway — a fly-compat Machines-API host gateway + cap-scoped reads.
//!
//! One serving block ([`Gateway`]) is the public control + hosting surface for agents
//! and their launches — a verified hosting edge. It classifies every inbound request:
//!
//! ```text
//!   fly client ─HTTP─▶  Gateway::handle
//!                         │  Host <name>.<apex> / verified custom domain ─▶ microsite  (static, content-addressed)
//!                         │  /ask?domain=<host>                          ─▶ on-demand-TLS ask (starbridge_domains::is_verified)
//!                         │  /api/{sites,domains,machines,servers,…}     ─▶ cap-scoped reads (subject VERIFIED by the gateway)
//!                         │  /v1/apps/{app}/machines...                  ─▶ fly machines API (create owner-scoped)
//!                         │  / , /status , /healthz                      ─▶ friendly surfaces
//! ```
//!
//! ## Assembled on the resident substrate (no forks)
//!
//! * [`http_serve`] — the hardened HTTP/1.1 serve loop the gateway serves on.
//! * [`starbridge_domains`] — the verified custom-domain resolver + the
//!   `is_verified` read the on-demand-TLS `ask` consults.
//! * [`webauth_core`] — the gateway VERIFIES a presented `dga1_` credential itself and
//!   derives the cap-scope subject from it (it trusts no upstream header; see
//!   [`auth::SubjectAuth`]).
//! * [`dregg_ipfs`] — a dregg content commitment IS an IPFS CID, so a launch's landing
//!   page, token metadata, and image are content-addressed ([`content`], [`launchpad`]).
//!
//! ## The launch composition (the offering)
//!
//! The gateway is not just a router: [`launchpad::Launchpad`] composes a [`launchpad::Launch`]
//! into a **live landing microsite** whose metadata + image are content-addressed — so
//! the instant a launch lands it is served at `<slug>.<apex>` and re-witnessable by CID.
//!
//! ## Parameterized apex, no product branding
//!
//! The hosting apex is configuration ([`SiteRegistry::new`] / [`starbridge_domains`]'s
//! `apex_from_env`), never a hardcoded host. The crate is substrate-general.
//!
//! ## Assembling + serving
//!
//! The wired default is the **verifying** posture: the gateway verifies a presented
//! `dga1_` credential itself and derives the cap-scope subject from it (it trusts no
//! upstream header). Durable state, a real (non-Null) launcher, and structured logging
//! are attached builder-style.
//!
//! ```no_run
//! use std::sync::Arc;
//! use host_gateway::{
//!     Gateway, SiteRegistry, MachineStore, MachinesHandler, SandboxLauncher, SubjectAuth,
//!     JsonlMachines, JsonlSites, StderrObserver,
//! };
//! use starbridge_domains::DomainRegistry;
//! use webauth_core::config::WebAuthConfig;
//!
//! // Durable registries — sites + machines survive a restart (append-only logs).
//! let sites = Arc::new(SiteRegistry::with_persistence(
//!     "dregg.net",
//!     Arc::new(JsonlSites::open("/var/lib/dregg/sites.jsonl").unwrap()),
//! ));
//! let store = Arc::new(MachineStore::with_persistence(
//!     Arc::new(JsonlMachines::open("/var/lib/dregg/machines.jsonl").unwrap()),
//! ));
//! // A real launcher (local sandbox lease plane), not the Null admit-only default.
//! let machines = MachinesHandler::over(store, Arc::new(SandboxLauncher::new()));
//! let domains = Arc::new(DomainRegistry::new());
//! // Verify-don't-trust: the gateway verifies the credential itself.
//! let auth = SubjectAuth::verified(WebAuthConfig::default(), "console-read");
//! let gateway = Gateway::new(sites, domains, machines, auth)
//!     .with_observer(Arc::new(StderrObserver));
//! http_serve::serve_http("127.0.0.1:8080", gateway.into_service()).unwrap();
//! ```

pub mod api;
pub mod auth;
pub mod content;
pub mod gateway;
pub mod launcher;
pub mod launchpad;
pub mod machines;
pub mod microsite;
pub mod observe;
pub mod page;
pub mod persist;
pub mod route;
pub mod util;
pub mod write;

pub use api::{
    AgentSource, AgentView, ApiHandler, BillingSource, ServerSource, ServerView, SpendLine,
};
pub use auth::SubjectAuth;
pub use content::{ContentStore, address};
pub use gateway::Gateway;
pub use launcher::{LeaseInfo, SandboxLauncher};
pub use launchpad::{Launch, LaunchError, LaunchReceipt, Launchpad, compose_unpinned};
pub use machines::{
    CreateMachineRequest, GuestConfig, Machine, MachineConfig, MachineLauncher, MachineState,
    MachineStore, MachinesHandler, NullLauncher,
};
pub use microsite::{Asset, Microsite, SiteError, SiteRegistry};
pub use observe::{NullObserver, Observer, RequestEvent, StderrObserver};
pub use page::Page;
pub use persist::{
    JsonlMachines, JsonlSites, MachinePersistence, NullMachines, NullSites, SitePersistence,
};
pub use route::Route;
pub use write::{AssetSpec, LaunchRequest, PublishSiteRequest, WriteHandler};

// Re-export the resident custom-domain control plane the gateway aggregates, so a
// caller wires bindings without a second dependency line.
pub use starbridge_domains::{DomainBinding, DomainRegistry};

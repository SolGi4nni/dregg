//! # `dregg-deploy` — DreggDL, a CapDL-inspired checkable deployment spec.
//!
//! Write a dregg capability layout **once**, declaratively (TOML/JSON), and
//! lower it to the exact `dregg_turn::CallForest` the SDKs instantiate and
//! `dregg-userspace-verify` checks. This is CapDL's "audit the whole authority
//! structure off one file" property, made executable for dregg:
//!
//! > **DreggDL + dregg-userspace-verify = a checkable deployment spec.**
//!
//! ## The pipeline
//!
//! ```text
//!   dregg.deploy.toml  ──parse──▶  Deployment  ──lower──▶  CallForest
//!                                                              │
//!                                              dregg-userspace-verify::analyze
//!                                                              ▼
//!                                                          Assurance
//!     (conservation B · non-amplification A · well-formedness · ring)
//!     over the WHOLE declared authority layout — before any gas.
//! ```
//!
//! - [`parse_toml`] / [`parse_json`] — the surface text → the [`Deployment`]
//!   serde struct (names, not raw ids).
//! - [`Lowered::from_deployment`] — name resolution + lowering to the ordered
//!   effect forest (deploy → birth → fund → grant), the exact artifact the
//!   checker consumes. Reuses `FactoryDescriptor`, `FactoryCreationParams`,
//!   `Effect`, `CapabilityRef`, `FederationId` verbatim — no new on-chain
//!   types.
//! - [`check`] — the synthesis: parse → lower → run the four static checks →
//!   report the [`DeployVerdict`] (the assurance over the cap graph + the
//!   resolved ids), naming the precise locus on failure.
//! - [`plan_apply`] — the `apply` flow: parse → lower → **gate on the static
//!   check** → emit the ordered, receipt-chained per-root [`apply::AppliedPlan`]
//!   (one `Turn` per effect-group, births → funds → grants, each chained to the
//!   previous via `previous_receipt_hash`). An amplifying/non-conserving spec is
//!   [`apply::ApplyError::Refused`] **before any turn is produced** — the check
//!   is the gate, not an afterthought.
//!
//! ## How each SDK consumes the lowered effects (the thin binding)
//!
//! The parser + lowering live **once**, here, in verified-adjacent Rust. Each
//! SDK is a thin binding that drives [`Lowered::from_deployment`] and feeds the
//! resulting [`dregg_turn::Effect`]s to verbs it already has. The lowering
//! emits one root per effect-group in dependency order (births → funds →
//! grants, grants nested by delegation), so an SDK walks `lowered.forest.roots`
//! and dispatches per effect:
//!
//! | lowered effect | Rust SDK | TS SDK | Python SDK |
//! |---|---|---|---|
//! | `CreateCellFromFactory` | `runtime.execute(create_effects)` (`sdk/src/runtime.rs`) | `runtime.turn().createCellFromFactory(vk, params)` | `turn.create_cell_from_factory(...)` |
//! | `Transfer` (fund) | `Effect::Transfer` via `runtime.execute` | `runtime.turn().transfer(to, amt)` | `turn.transfer(to, amt)` |
//! | `GrantCapability` | `Effect::GrantCapability` via `runtime.execute_on` | `runtime.turn().grant(to, target, perms)` | `turn.grant(to, target, perms)` |
//! | bind topology (`federation_id`) | `set_local_federation_id` | `new NodeClient(url, {federationId})` | `Identity.turn(url, federation_id=…)` |
//!
//! - **Rust** calls this crate directly: `Lowered::from_deployment(&dep)?` then
//!   submits `lowered.forest` (or its per-root effect groups) through the
//!   runtime, binding `lowered.federation_id` at signing time.
//! - **TS / Python** get the lowering **for free over the existing FFI seams**:
//!   the lowering is a pure function (DreggDL text → JSON `CallForest`), so the
//!   PyO3 (`sdk-py/src/lib.rs`) and wasm (`sdk-ts/src/wasm.ts`) bindings call
//!   `dregg-deploy lower` (or a `#[no_mangle]` wrapper) and replay the decoded
//!   effects through their own turn builders. The *parser lives once*; the
//!   language bindings are thin. (The TS/Py binding glue + a node `POST /deploy`
//!   ingress are tracked in HORIZONLOG — the wire shape is already settled
//!   because `CallForest`/`Assurance` are serde types.)
//!
//! Because all three SDKs emit the identical postcard `SignedTurn` envelope
//! over the same federation-bound message, a DreggDL deployed from Python and
//! the same DreggDL deployed from Rust produce **byte-identical on-chain
//! effects** (modulo the signing key) — the reproducibility half of the CapDL
//! property.
//!
//! ## The honest boundary
//!
//! The static audit certifies the *artifact-decidable* layout: per-asset
//! conservation of the funding transfers, non-amplification of the `[[grant]]`
//! edges *as a graph*, structural well-formedness. It does NOT replace the
//! executor: whether the signer HELD the cap it grants (the live c-list), the
//! balances, credential/signature validity, freshness, and the state
//! commitment all need the live executor / receipt. See
//! `dregg_userspace_verify::boundary`. DreggDL is a convenience + an audit
//! artifact — never a trust boundary; a malformed DreggDL produces turns the
//! executor rejects, it cannot produce an unsafe deployment the executor would
//! accept.

pub mod apply;
pub mod diagnose;
pub mod facet;
pub mod lower;
pub mod refine;
pub mod schema;

pub use apply::{
    AppliedPlan, ApplyError, DeferredField, PlannedTurn, ProjectedReceipt, plan_apply,
    plan_apply_toml,
};
pub use diagnose::{DeployDiagnostics, explain_assurance, explain_finding};
pub use facet::{describe_allowed_effects, describe_facet, facet_to_allowed_effects, parse_facet};
pub use lower::{LowerError, Lowered};
pub use refine::{
    FlowSpec, IntentEffect, Proc, RefineFinding, RefineVerdict, decide_refines,
    describe_diverging_effect, describe_effect, flow_of_forest, flow_of_plan, refines_intent,
    refines_upgrade,
};
pub use schema::*;

use dregg_userspace_verify::Assurance;

/// Errors from the top-level [`check`] / [`plan_apply_toml`] / parse entry
/// points.
#[derive(Debug, thiserror::Error)]
pub enum DeployError {
    #[error("TOML parse error: {0}")]
    Toml(#[from] toml::de::Error),
    #[error("JSON parse error: {0}")]
    Json(#[from] serde_json::Error),
    #[error(transparent)]
    Lower(#[from] LowerError),
    /// The `apply` flow refused or could not lower the deployment (the gate
    /// rejected a non-conserving / amplifying spec, see [`apply::ApplyError`]).
    #[error(transparent)]
    Apply(#[from] ApplyError),
}

/// Parse DreggDL TOML text into a [`Deployment`].
pub fn parse_toml(text: &str) -> Result<Deployment, DeployError> {
    Ok(toml::from_str(text)?)
}

/// Parse DreggDL JSON text into a [`Deployment`] (the JSON/YAML equivalent of
/// the TOML surface; the canonical form is the serde struct).
pub fn parse_json(text: &str) -> Result<Deployment, DeployError> {
    Ok(serde_json::from_str(text)?)
}

/// Re-serialize a [`Deployment`] back to canonical TOML (the round-trip
/// surface). `parse_toml(serialize_toml(d)) == d` for any well-formed `d`.
pub fn serialize_toml(dep: &Deployment) -> Result<String, toml::ser::Error> {
    toml::to_string_pretty(dep)
}

/// The verdict of a deployment check: the static assurance over the lowered
/// authority layout, plus the resolved content-addresses / cell ids so a
/// caller can submit or audit by name.
#[derive(Clone, Debug)]
pub struct DeployVerdict {
    /// The four static assurance checks over the lowered forest.
    pub assurance: Assurance,
    /// `ref` -> resolved `factory_vk` (descriptor content-address), hex.
    pub factories: Vec<(String, String)>,
    /// `name` -> resolved `CellId`, hex.
    pub cells: Vec<(String, String)>,
    /// Number of root effect-groups in the lowered forest.
    pub turn_count: usize,
}

impl DeployVerdict {
    /// `true` iff every static check passed.
    pub fn pass(&self) -> bool {
        self.assurance.pass()
    }
}

/// THE SYNTHESIS: parse DreggDL text → lower to the forest → run
/// `dregg-userspace-verify::analyze` over the whole declared authority layout →
/// return the assurance verdict with the resolved ids.
///
/// This is what `dregg-deploy check <file.dregg.toml>` runs. On failure the
/// `assurance` findings name the precise locus (which node, which effect, which
/// asset) within the lowered forest.
///
/// `as_ring`: also run the ring-balance check (for a deployment that declares a
/// settlement ring as bare funding transfers).
pub fn check(text: &str, as_ring: bool) -> Result<DeployVerdict, DeployError> {
    let dep = parse_toml(text)?;
    check_deployment(&dep, as_ring)
}

/// [`check`] from an already-parsed [`Deployment`].
pub fn check_deployment(dep: &Deployment, as_ring: bool) -> Result<DeployVerdict, DeployError> {
    let lowered = Lowered::from_deployment(dep)?;
    let assurance = dregg_userspace_verify::analyze(&lowered.forest, as_ring);

    let factories = lowered
        .factory_vks
        .iter()
        .map(|(k, v)| (k.clone(), hex32(v)))
        .collect();
    let cells = lowered
        .cell_ids
        .iter()
        .map(|(k, v)| (k.clone(), hex32(&v.0)))
        .collect();

    Ok(DeployVerdict {
        assurance,
        factories,
        cells,
        turn_count: lowered.forest.roots.len(),
    })
}

fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for byte in b {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

#[cfg(test)]
mod tests;

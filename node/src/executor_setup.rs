//! Blocklace-aware [`TurnExecutor`] configuration shared across node entry points.
//!
//! Keeps federation id, wall-clock timestamp, and attested block height aligned with
//! the same rules as [`crate::blocklace_sync::execute_finalized_turn`].

use std::sync::Arc;
use std::sync::OnceLock;

use dregg_circuit::dsl::circuit::CellProgram;
use dregg_circuit::dsl::dfa_routing::dfa_routing_descriptor;
use dregg_dsl_runtime::ProgramRegistry;
use dregg_turn::TurnExecutor;
use dregg_turn::executor::DslCircuitDfaVerifier;

use crate::state::NodeStateInner;

/// The deployed name of the node's routing circuit — the `dregg-dfa-routing-v1`
/// route-commitment-binding AIR (`dregg_circuit::dsl::dfa_routing`, faithful to
/// the Lean model `Dregg2.Crypto.DfaAcceptanceAir`).
pub const ROUTE_CIRCUIT_NAME: &str = "dregg-dfa-routing-v1";

/// The node's canonical 4-state message router, flattened to `(state, symbol, next)`.
///
/// States: `IDLE=0`, `LOCAL=1`, `REMOTE=2`, `REJECT=3`.
/// Symbols: `internal=0`, `external=1`, `privileged=2`, `unknown=3`.
///
/// This is the SAME table the `dregg-dfa-routing-v1` AIR was authored and proven
/// against (`circuit/src/dsl/dfa_routing.rs` `tests::router_transitions`, and the
/// `live_routing*` teeth in `turn/src/executor/membership_verifier.rs`). The table
/// is the routing POLICY: its `compute_table_commitment` seeds every route
/// commitment, and it flows into the descriptor — so changing it changes
/// [`route_circuit_vk`], which is a deliberate, visible re-deployment.
pub fn canonical_router_transitions() -> Vec<(u32, u32, u32)> {
    // TRANSITIONS = [[1,2,1,3],[1,2,1,3],[1,2,3,3],[3,3,3,3]]
    let table = [[1, 2, 1, 3], [1, 2, 1, 3], [1, 2, 3, 3], [3, 3, 3, 3]];
    let mut out = Vec::new();
    for (state, row) in table.iter().enumerate() {
        for (symbol, &next) in row.iter().enumerate() {
            out.push((state as u32, symbol as u32, next));
        }
    }
    out
}

/// The node's deployed routing program.
///
/// No ceremony, no epoch decision: a DSL program's `vk_hash` is CONTENT-DERIVED
/// (`CellProgram::compute_vk_hash` = blake3 over the postcard-serialized
/// descriptor), so this program's identity follows from the descriptor + the
/// canonical table alone — every node that runs this code mints the same vk.
pub fn route_circuit_program() -> &'static CellProgram {
    static PROGRAM: OnceLock<CellProgram> = OnceLock::new();
    PROGRAM.get_or_init(|| {
        CellProgram::new(
            dfa_routing_descriptor(ROUTE_CIRCUIT_NAME, &canonical_router_transitions()),
            1,
        )
    })
}

/// The routing circuit's verification-key hash — the commitment a relay's
/// `Witnessed { Dfa }` caveat carries (the relay's `route_table_root`).
///
/// [`DslCircuitDfaVerifier`] resolves a Dfa caveat's commitment against the
/// deployed [`ProgramRegistry`]; a `vk_hash` absent from it fails closed. This is
/// the vk under which [`configure_turn_executor`] deploys the routing program, so
/// a Dfa caveat carrying it now DISCHARGES through the real STARK verifier
/// instead of being rejected as `KindNotRegistered`.
pub fn route_circuit_vk() -> [u8; 32] {
    route_circuit_program().vk_hash
}

/// The registry the node's `Dfa` verifier resolves against: the node's deployed
/// programs PLUS the routing circuit at [`route_circuit_vk`].
///
/// Deployment is idempotent (`ProgramRegistry::deploy` keys by vk_hash), so a
/// registry that already carries the routing program is unchanged.
pub fn program_registry_with_route_circuit(_s: &NodeStateInner) -> ProgramRegistry {
    // A FRESH registry holding EXACTLY the canonical route circuit — deliberately
    // NOT `s.program_registry`.
    //
    // `DslCircuitDfaVerifier` resolves ANY `vk_hash` present in the registry it is
    // handed, lowers that program, and verifies its STARK against PROVER-SUPPLIED
    // public inputs; nothing else pins the program to the routing circuit. The
    // node's `s.program_registry` is CALLER-FILLABLE: `POST /programs/deploy`
    // (`api.rs::post_deploy_program`) accepts an arbitrary postcard
    // `CircuitDescriptor` and `descriptor.validate()` has no minimum-constraint
    // check, so a trivially-satisfiable program sails through. (That route sits
    // behind `require_auth`, so this is "any AUTHORIZED deployer", not "anyone" —
    // but that is exactly the point: the Dfa verifier must not trust a circuit
    // merely because some authorized caller deployed it. Defence in depth.)
    // Handing that registry to the verifier would let such a deployer and
    // discharge a `Dfa` caveat against their OWN program's vk — turning a
    // fail-closed (safe-but-dead) relay into a live forgery surface. Pinning the
    // registry to the one content-derived route vk is what makes wiring the
    // verifier an improvement rather than a regression.
    let mut programs = ProgramRegistry::new();
    // `deploy` only fails on a descriptor that does not validate or a vk_hash that
    // does not match its descriptor — neither is possible for a `CellProgram::new`
    // over the pinned descriptor (`descriptor_is_deployable` pins the validation).
    programs
        .deploy(route_circuit_program().clone())
        .expect("the canonical dregg-dfa-routing-v1 program must deploy");
    programs
}

/// How to derive the executor's block height from node state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockHeightMode {
    /// Use the latest attested root height (read-only / verify paths).
    Current,
    /// Use `latest + 1` — the height assigned to the turn about to execute.
    Next,
}

/// Resolve the blocklace-attested height from persistent store + solo fallback.
pub fn attested_block_height(s: &NodeStateInner) -> u64 {
    let store_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let solo_height = s
        .solo_consensus
        .as_ref()
        .map(|solo| solo.height)
        .unwrap_or(0);
    store_height.max(solo_height)
}

/// Federation id for turn signing — matches blocklace finalized-turn path.
pub fn federation_id_for_executor(s: &NodeStateInner) -> [u8; 32] {
    if s.federation_configured {
        s.federation_id
    } else {
        *blake3::hash(s.cclerk.public_key().as_bytes()).as_bytes()
    }
}

fn wall_clock_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// Configure `executor` with federation id, timestamp, and blocklace height.
pub fn configure_turn_executor(
    executor: &mut TurnExecutor,
    s: &NodeStateInner,
    height_mode: BlockHeightMode,
) {
    executor.set_local_federation_id(federation_id_for_executor(s));
    executor.set_timestamp(wall_clock_secs());
    // Sign committed receipts with the node's key (same key the MCP entry
    // points use). Without this, every HTTP/blocklace-path receipt carried
    // `executor_signature: None` (`executor_signed:false` in /api/receipts) and
    // conditional-turn verification of our receipts was impossible.
    executor.set_executor_signing_key(s.cclerk.gossip_signing_key().to_bytes());

    // ORGANS §5 (adjudication): install the court's `validEquivocation`
    // predicate atom into the executor's witnessed-predicate registry, so
    // turn admission / cell programs can gate on a verified fork exhibit
    // (CONSENSUS-FLEX §7 item 2, live on every node executor).
    if let Some(registry) = executor.witnessed_registry.as_mut() {
        dregg_federation::court::register_equivocation_court(registry);

        // DFA ROUTE-COMMITMENT (the relay's caveat): install the real
        // `DslCircuitDfaVerifier` over the node's deployed programs + the
        // canonical routing circuit. The executor default
        // (`registry_with_real_verifiers`) leaves `Dfa` FAIL-CLOSED because the
        // kind needs a host-trusted `ProgramRegistry`; this supplies it, so a
        // relay's `Witnessed { Dfa }` caveat carrying `route_circuit_vk()` now
        // discharges through the real route-commitment-binding STARK ("a router
        // cannot claim a delivery it did not make") instead of being rejected
        // before its verify logic runs. This upgrades ONLY `Dfa` — every other
        // kind stays exactly as `registry_with_real_verifiers` set it. A caveat
        // whose commitment is NOT a deployed vk_hash still fails closed.
        registry.register_builtin(Arc::new(DslCircuitDfaVerifier::new(Arc::new(
            program_registry_with_route_circuit(s),
        ))));
    }

    // THE EPOCH §5 (signed wells): wire the genesis-declared wells so fees
    // are MOVES to the fee well and Burn is a MOVE to the asset's issuer
    // well — every committed turn conserves exactly
    // (`reachable_total_zero`'s hypotheses hold on the deployed chain).
    if let Some(fee_well) = s.fee_well {
        executor.set_fee_well_cell(fee_well);
    }
    for (token_id, well) in &s.issuer_wells {
        executor.register_issuer_well(*token_id, *well);
    }

    let base = attested_block_height(s);
    let height = match height_mode {
        BlockHeightMode::Current => base,
        BlockHeightMode::Next => base.saturating_add(1),
    };
    executor.set_block_height(height);
}

/// The node's OWN agent cell — `derive_raw(cipherclerk pubkey, blake3("default"))`. This is the
/// agent whose receipt chain the cipherclerk maintains authoritatively (the source of the
/// host-fed `stored_head` for the boundary-P1 admission shadow). Mirrors the derivation in
/// `api.rs` (the submit path), centralised so the blocklace-finalized path agrees.
pub fn local_agent_cell(s: &NodeStateInner) -> dregg_cell::CellId {
    let default_token_id = *blake3::hash(b"default").as_bytes();
    dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &default_token_id)
}

/// THE one executor gate (#171): execute `turn` through the producer-aware path
/// shared by EVERY ingress — the thin-HTTP `/turn/submit`, the signed-envelope
/// `/turns/submit` (remote agents), and blocklace-finalized turns all call this,
/// so a remote-submitted turn runs on exactly the same authoritative state
/// producer as a local one (no parallel entry).
///
/// THE SWAP — producer mode (authority inversion), the DEFAULT. When
/// `lean_producer_enabled` is set (default ON unless `DREGG_LEAN_PRODUCER=0`),
/// the VERIFIED Lean executor is the authoritative state PRODUCER for the
/// swap-safe COVERED set: `produce_via_lean` reconstitutes the committed ledger
/// from the Lean FFI's post-state and demotes the Rust `TurnExecutor` to a
/// parallel differential cross-check, returning the Rust `TurnResult` (so the
/// receipt / proving / attestation machinery is unchanged) together with a
/// differential outcome. A turn that is unmappable or touches a characterized
/// root-gap effect falls back to the Rust producer for that turn (logged, never
/// silent). A covered-set divergence keeps the Rust state and is surfaced as a
/// real soundness finding. When the flag is OFF, this is exactly the legacy
/// Rust-producer path.
pub fn execute_via_producer(
    executor: &TurnExecutor,
    turn: &dregg_turn::Turn,
    ledger: &mut dregg_cell::Ledger,
    lean_producer_enabled: bool,
) -> dregg_turn::TurnResult {
    use tracing::{error, info, warn};

    if !lean_producer_enabled {
        return executor.execute(turn, ledger);
    }

    let agent = turn.agent;
    let (result, outcome) = dregg_exec_lean::produce_via_lean(executor, turn, ledger);
    match &outcome {
        dregg_exec_lean::ProducerOutcome::LeanAuthoritative {
            committed,
            rust_agreed,
            lean_root,
            rust_root,
            rust_committed,
        } => {
            if *rust_agreed {
                info!(
                    target: "dregg::lean_shadow::producer",
                    agent = ?agent,
                    committed = *committed,
                    "THE SWAP producer mode: verified Lean executor is AUTHORITATIVE for this \
                     covered turn (its post-state is committed); Rust reference AGREES"
                );
            } else {
                // THE AUTHORITY INVERSION's tooth: on a covered turn a Lean↔Rust disagreement is,
                // by definition, the Rust path being WRONG (Rust is the artifact dregg2 replaces
                // because it is buggy). The verified Lean verdict was committed; this surfaces the
                // Rust bug as a finding — it is NOT a fallback to Rust.
                error!(
                    target: "dregg::lean_shadow::producer",
                    agent = ?agent,
                    lean_committed = *committed,
                    rust_committed = *rust_committed,
                    lean_root = %dregg_types::hex_encode(lean_root),
                    rust_root = %dregg_types::hex_encode(rust_root),
                    "THE SWAP authority inversion: verified Lean executor (AUTHORITATIVE) and the \
                     demoted Rust reference DISAGREE on a covered turn — the Rust path is BUGGY \
                     (REAL finding). The verified Lean verdict was committed; Rust was NOT \
                     allowed to override it"
                );
            }
        }
        dregg_exec_lean::ProducerOutcome::Fallback { reason } => {
            warn!(
                target: "dregg::lean_shadow::producer",
                agent = ?agent,
                reason = %reason,
                "THE SWAP producer mode: turn outside the swap-safe covered set — FENCED onto the \
                 legacy Rust path for this turn (explicit, surfaced; the named burning-down \
                 partition, not a silent Rust-authoritative default)"
            );
        }
    }
    result
}

/// COMMIT ARBITRARY EFFECTS AS `agent` — the factored core of the signed-turn
/// commit path, callable WITHOUT an HTTP envelope.
///
/// The signed-turn ingress (`api.rs::post_submit_signed_turn`) verifies a caller
/// signature, derives the agent, then runs exactly this core: build a `Turn`
/// carrying `effects` under `agent`'s current nonce + chain head, execute it
/// through the ONE producer gate (`execute_via_producer`), and append the
/// committed `TurnReceipt` to the cipherclerk chain. This helper is that core,
/// without the signature/HTTP/gossip/proving shell — so an IN-PROCESS host (the
/// `deos-host` server program, which owns the agent cell and decides its effects
/// directly) commits a real verified turn on the node's ledger by the same path.
///
/// Returns the committed receipt hash, or a rejection reason. The receipt lands
/// on `s.cclerk`'s chain and the ledger is mutated in place — identical to the
/// HTTP path's committed-turn semantics, minus the wire shell.
// In-process committed-turn entry mirroring the HTTP path; reached via tests / the deos-host program.
pub fn commit_effects_as(
    s: &mut crate::state::NodeStateInner,
    agent: dregg_cell::CellId,
    method: &str,
    effects: Vec<dregg_turn::action::Effect>,
) -> Result<[u8; 32], String> {
    use dregg_turn::{CallForest, Turn};

    let exec_federation_id = federation_id_for_executor(s);
    let nonce = s.ledger.get(&agent).map(|c| c.state.nonce()).unwrap_or(0);
    let prev = s.cclerk.receipt_chain().last().map(|r| r.receipt_hash());

    let action = s
        .cclerk
        .make_action(agent, method, effects, &exec_federation_id);
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);

    let mut turn = Turn {
        agent,
        nonce,
        fee: 0,
        memo: Some(format!("deos_host:{method}")),
        valid_until: Some(i64::MAX / 2),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash: prev,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let executor = new_submit_executor(s);
    // Size the fee to the estimated computron cost so the executor budget gate passes.
    turn.fee = executor.estimate_cost(&turn);

    crate::api::seed_executor_receipt_head(&executor, agent, prev);
    let lean_producer_enabled = s.lean_producer_enabled;
    match execute_via_producer(&executor, &turn, &mut s.ledger, lean_producer_enabled) {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let rh = receipt.receipt_hash();
            s.cclerk
                .append_receipt(receipt)
                .map_err(|e| format!("append_receipt: {e}"))?;
            Ok(rh)
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => Err(format!("rejected: {reason}")),
        other => Err(format!("turn did not commit: {other:?}")),
    }
}

/// Build a fresh executor configured for turn submission (height = attested + 1).
///
/// The verified-Lean shadow/gate observer (`dregg_exec_lean::LeanShadowObserver`) is injected
/// UNCONDITIONALLY on the native node — the differential cross-check and the strict-veto rejection
/// authority are live on every executor the node builds. (Only a wasm / no-FFI build, which does
/// not depend on `dregg-exec-lean`, gets the no-op default.)
pub fn new_submit_executor(s: &NodeStateInner) -> TurnExecutor {
    let mut executor = TurnExecutor::new(dregg_turn::ComputronCosts::default())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc());
    configure_turn_executor(&mut executor, s, BlockHeightMode::Next);
    require_pq_admission(&executor);
    executor
}

/// HYBRID PERIMETER — DEPLOYED POSTURE (require_pq = ON) at the ADMISSION
/// boundary. Called on the executors the node uses to ADMIT a turn for commit:
/// the thin-HTTP + signed-envelope submit path (`new_submit_executor`, reached by
/// `commit_effects_as` and the queue drainers too) and the blocklace
/// finalized-turn path (`blocklace_sync::execute_finalized_turn`). Requiring the
/// post-quantum half rejects a classical-only `Authorization::Signature` and an
/// outer envelope lacking a PQ signature (`api.rs::post_submit_signed_turn` reads
/// `require_pq()`); a present hybrid `HybridSignature` (ed25519 + ML-DSA-65) is
/// accepted. The Rust default signer and both SDKs (sdk-ts ML-DSA-65, sdk-py
/// hybrid) already emit the hybrid shape, so this closes the staged rollout for
/// the node's admission surface. NOT applied to `new_verify_executor`: read/proof
/// re-execution replays turns already admitted (possibly pre-flip classical
/// history), so gating it on PQ presence would wrongly reject a legitimate read.
/// A present-but-invalid PQ half is fail-closed in EITHER mode regardless.
///
/// DEPLOYED DEFAULT is ON. The staged-rollout ops override `DREGG_REQUIRE_PQ=0`
/// forces it OFF for a migration window (mirrors the consensus HybridPq knob) —
/// the default with the var unset, or set to anything but `0`/`false`, is ON.
pub fn require_pq_admission(executor: &TurnExecutor) {
    let disabled = std::env::var("DREGG_REQUIRE_PQ")
        .map(|v| v == "0" || v.eq_ignore_ascii_case("false"))
        .unwrap_or(false);
    executor.set_require_pq(!disabled);
}

/// Build a fresh executor at the current attested height (verify / read paths). Injects the
/// verified-Lean shadow/gate observer like [`new_submit_executor`].
pub fn new_verify_executor(s: &NodeStateInner) -> TurnExecutor {
    let mut executor = TurnExecutor::new(dregg_turn::ComputronCosts::default())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc());
    configure_turn_executor(&mut executor, s, BlockHeightMode::Current);
    executor
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn height_mode_next_increments() {
        let base = 41u64;
        let next = match BlockHeightMode::Next {
            BlockHeightMode::Next => base.saturating_add(1),
            BlockHeightMode::Current => base,
        };
        assert_eq!(next, 42);
    }
}

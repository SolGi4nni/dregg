//! Blocklace-aware [`TurnExecutor`] configuration shared across node entry points.
//!
//! Keeps federation id, wall-clock timestamp, and attested block height aligned with
//! the same rules as [`crate::blocklace_sync::execute_finalized_turn`].

use dregg_turn::TurnExecutor;

use crate::state::NodeStateInner;

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
    executor
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

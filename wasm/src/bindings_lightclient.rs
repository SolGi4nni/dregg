//! THE LIGHT CLIENT IN THE TAB (N12) — `#[wasm_bindgen]` over
//! `dregg-lightclient::verify_history`.
//!
//! `docs/design-frontiers/WEB-FORWARD.md §8 S4`. The anti-pale-ghost tooth: a
//! browser can fold a whole finalized history into ONE succinct recursive
//! aggregate and verify it RE-WITNESSING NOTHING — the executable counterpart of
//! `Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history`.
//!
//! Two entry points, both honest about the VK trust anchor:
//!
//! - [`light_client_demo`] — fold a real K-turn chain IN THE TAB (each turn's
//!   post-state is the next's pre-state; each leaf is a REAL Lean-descriptor
//!   EffectVM proof verified in-circuit) and light-verify it. This is the SETUP
//!   side that SELF-ANCHORS (the VK fingerprint is minted from the locally
//!   produced fold — exactly how an honest setup mints the anchor it then
//!   distributes). It proves the whole pipeline runs in wasm32; "verify the whole
//!   history yourself" becomes tactile.
//! - [`verify_devnet_history`] — verify an EXTERNALLY-produced aggregate (proof
//!   bytes) against a CONFIG-pinned VK anchor (genesis/checkpoint configuration,
//!   NEVER read off the artifact under verification — the light-client invariant).
//!   This is the real remote-verifier path; the demo wires the in-tab
//!   `light_client_demo` for a zero-setup runnable artifact.
//!
//! HONEST SCOPE (the project law): this carries the light client's NAMED floor —
//! `recursive_sound` (the recursion fork's FRI engine soundness) + the two
//! precisely-scoped fork follow-ups stated in `circuit/src/ivc_turn_chain.rs` —
//! surfaced in the UI, NOT hidden. The verification IS the trust: IF the aggregate
//! verifies (engine sound), THEN the whole history is attested.

use serde::Serialize;
use wasm_bindgen::prelude::*;

/// The whole-history attestation a light client obtains — the JS view of
/// `dregg_lightclient::AttestedHistory`. Holding it means: *every one of
/// `num_turns` finalized turns executed correctly, in order, from `genesis_root`
/// to `final_root`, and `chain_digest` commits to that exact ordered history* —
/// and the tab re-executed nothing.
#[derive(Clone, Debug, Serialize)]
pub struct AttestedHistoryView {
    /// Whether the aggregate verified (the headline). On a real verify failure
    /// this is the engine REJECTING the proof — no attestation granted.
    pub attested: bool,
    /// The genesis state root the attested history starts from (decimal felt).
    pub genesis_root: u32,
    /// The final state root — the genuine fold of the whole history (decimal felt).
    pub final_root: u32,
    /// The running digest committing to the ORDERED `(old_root, new_root)` pairs
    /// (decimal felt) — distinct histories with the same endpoints still differ.
    pub chain_digest: u32,
    /// How many finalized turns the attested history folds. The light client
    /// learns ALL of them executed correctly without seeing any.
    pub num_turns: usize,
    /// The proof-system identifier + the honest named floor, for the UI.
    pub engine: String,
    /// The named soundness floor (surfaced, not hidden).
    pub named_floor: String,
}

/// **THE IN-TAB LIGHT CLIENT** — fold a real `k`-turn chain in wasm32 and
/// light-verify it, re-witnessing nothing.
///
/// Each turn debits `step` from a running balance; each leaf is a REAL
/// Lean-descriptor EffectVM proof (`prove_vm_descriptor`, the audited p3 batch
/// prover — the same wire artifact the SDK cutover emits) verified in-circuit by
/// the recursion wrap. The fold is the expensive step (done once); the
/// light-client verify is the cheap step. SELF-ANCHORS: the VK fingerprint is
/// minted from the locally produced fold (the honest setup mint).
///
/// `k` is clamped to `[2, 4]` — the recursive chain-binding folds the temporal
/// `new_root[i] == old_root[i+1]` tooth, so it needs AT LEAST 2 turns; and
/// recursive proving in a browser is heavy, so a small chain keeps the demo
/// responsive while exercising the REAL pipeline end-to-end.
///
/// Returns an [`AttestedHistoryView`]. Errors only on an internal substrate bug
/// (a chain that should fold but doesn't), which the caller surfaces honestly.
#[wasm_bindgen]
pub fn light_client_demo(k: usize, step: u64) -> Result<JsValue, JsError> {
    use dregg_circuit::effect_vm::{generate_effect_vm_trace, sel, CellState, Effect};
    use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
    use dregg_circuit::ivc_turn_chain::FinalizedTurn;
    use dregg_circuit::joint_turn_aggregation::DescriptorParticipant;
    use dregg_circuit::lean_descriptor_air::{parse_vm_descriptor, prove_vm_descriptor};
    use dregg_lightclient::fold_and_attest;

    let k = k.clamp(2, 4);
    let step = if step == 0 { 1 } else { step };
    // Start with enough balance that k debits of `step` never underflow.
    let start_balance: u64 = step.saturating_mul(k as u64).saturating_add(1_000_000);

    // Build a continuous chain of REAL finalized turns (each post-state IS the
    // next pre-state — the temporal binding the aggregate enforces).
    let json = descriptor_for_selector(sel::TRANSFER)
        .ok_or_else(|| JsError::new("transfer descriptor not registered"))?;
    let desc = parse_vm_descriptor(json)
        .map_err(|e| JsError::new(&format!("transfer descriptor parse failed: {e:?}")))?;

    let mut turns: Vec<FinalizedTurn> = Vec::with_capacity(k);
    let mut balance = start_balance;
    let mut nonce: u32 = 0;
    for _ in 0..k {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount: step,
            direction: 1,
        }];
        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let dpis = &public_inputs[..desc.public_input_count];
        let proof = prove_vm_descriptor(&desc, &trace, dpis)
            .map_err(|e| JsError::new(&format!("descriptor prove failed: {e:?}")))?;
        turns.push(FinalizedTurn::new(
            DescriptorParticipant::v1(proof, public_inputs),
            trace,
        ));
        balance -= step;
        nonce += 1;
    }

    // Fold + light-verify (the SETUP-side self-anchor: the VK fingerprint is
    // minted from the locally produced fold, then verify_history checks the
    // aggregate against it — re-witnessing nothing).
    let (_agg, attested) = fold_and_attest(&turns)
        .map_err(|e| JsError::new(&format!("light-client fold/verify failed: {e}")))?;

    let view = AttestedHistoryView {
        attested: true,
        genesis_root: attested.genesis_root.as_u32(),
        final_root: attested.final_root.as_u32(),
        chain_digest: attested.chain_digest.as_u32(),
        num_turns: attested.num_turns,
        engine: "recursive-stark (plonky3 fork) · descriptor-leaf EffectVM".to_string(),
        named_floor: "named floor: recursive_sound (FRI engine soundness) + the two \
                      ivc_turn_chain fork follow-ups — the verification IS the trust"
            .to_string(),
    };
    serde_wasm_bindgen::to_value(&view).map_err(|e| JsError::from(e))
}

/// **VERIFY AN EXTERNAL HISTORY against a config-pinned VK anchor** — the real
/// remote-verifier shape.
///
/// In the production shape the aggregate is produced by whoever ran the history
/// (a node, a relayer) and the VK anchor is the client's genesis/checkpoint
/// configuration, NEVER read off the artifact under verification (the
/// light-client invariant `verify_history` enforces, and the in-tab
/// [`light_client_demo`] honors by minting the anchor from the local fold).
///
/// HONEST OBSTACLE (named, not hidden — `WEB-FORWARD.md §7` discipline): the
/// crate's [`dregg_circuit::ivc_turn_chain::WholeChainProof`] is an IN-MEMORY
/// proof object — its `root: RecursionOutput<SC>` wraps an `Rc<CircuitProverData>`
/// — so it has NO serde/byte encoding to transport over the wasm boundary today.
/// A remote-verifier byte path therefore needs a fork-side serialization of the
/// recursion proof first (the same follow-up the `ivc_turn_chain` module docs
/// name). Until that lands, the runnable in-tab tooth is [`light_client_demo`]
/// (fold + verify entirely in wasm, no transport), and this entry reports the
/// obstacle rather than pretending a byte path exists. `proof_len` /
/// `vk_anchor_len` are accepted so the JS signature is the production one.
#[wasm_bindgen]
pub fn verify_devnet_history(proof_len: usize, vk_anchor_len: usize) -> Result<JsValue, JsError> {
    let view = AttestedHistoryView {
        attested: false,
        genesis_root: 0,
        final_root: 0,
        chain_digest: 0,
        num_turns: 0,
        engine: "recursive-stark (plonky3 fork)".to_string(),
        named_floor: format!(
            "external byte-verify not yet available (proof_len={proof_len}, \
             vk_anchor_len={vk_anchor_len}): WholeChainProof holds an Rc-backed \
             RecursionOutput with no serde encoding — needs a fork-side recursion-proof \
             serialization first. Use light_client_demo for the in-tab fold+verify tooth."
        ),
    };
    serde_wasm_bindgen::to_value(&view).map_err(JsError::from)
}

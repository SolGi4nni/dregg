//! `dregg-verifier`: the standalone verify floor.
//!
//! # Design intent
//!
//! This crate imports `dregg-circuit` (the batch-STARK VERIFY surface
//! `descriptor_ir2::verify_vm_descriptor2`) + `dregg-types`, plus `dregg-turn` +
//! `dregg-federation` + `dregg-captp` so the `verify-cross-fed-bundle`
//! subcommand can deserialize and verify a
//! [`dregg_federation::CrossFedReceiptBundle`] end-to-end. It MUST NOT import
//! from `dregg-node`, `dregg-wire`, or any crate that carries ledger / executor /
//! program-registry state.
//!
//! The invariant: a verifier process can run in a completely separate OS process
//! with no shared memory, no shared mutable state, and no callbacks into a
//! prover. It reads bytes from disk, runs cryptographic verification, and exits.
//!
//! ⚠ **"Prover-free" is about CONTROL FLOW here, not about linkage, and the docblock
//! used to blur them.** Measured 2026-08-05 (`cargo tree -p dregg-verifier -e normal`):
//! `dregg-turn-prover` is an unconditional dependency — the `aggregated-bundle`
//! subcommand's `AggregatedBundle` type and its verifier live there — and it pulls
//! `dregg-circuit-prove` at depth 2. The recursion prover IS linked into this binary.
//! No verify path calls into it, and deleting this crate's own `dregg-circuit-prove`
//! edge (with the recursive-replay entries, below) removed a knob rather than the
//! tower. Making the linkage claim TRUE means moving `AggregatedBundle` +
//! `verify_aggregated_bundle` into a verify-only crate; that is real work and is not
//! done here, so the claim is not made. `dregg-federation` is depended on with
//! `default-features = false` so no tokio runtime is pulled — the verifier
//! stays single-threaded and synchronous. This is the "Charlie" role
//! described in `06-the-real-demo.md`.
//!
//! # ⚑ FLAG DAY 2026-08-05 — the v1 hand-AIR surface is DELETED, not retired
//!
//! Until this commit the crate shipped four entry points that had been "retired"
//! into unconditional rejections and then left in place:
//!
//! * `verify_effect_vm_proof` — returned `exit_code::ERROR` on every input;
//! * `replay_chain` / `replay_one_with_prev` — rejected every entry, because step 1
//!   was the above;
//! * `verify_recursive_replay{,_from_bundle}` / `replay_chain_recursive` — same,
//!   and `verify_recursive_replay` had ZERO callers (the repo's own
//!   `baseline/production-callers.tsv` marked it `UNCALLED`);
//! * the VK registry (`EFFECT_VM_AIR_NAME`, `EFFECT_VM_VK_HASH_HEX`,
//!   `resolve_vk_hash`, `AUTO_DETECT_VK_HASH`) that only those entries consulted.
//!   `EFFECT_VM_VK_HASH_HEX` documented itself as `SHA-256(b"dregg-effect-vm-v1")`
//!   and carried `8b80e1cf7b0a…`; the real digest is `0942b5f2a4ec…`. The
//!   derivation was invented, and `main.rs` printed the value as a copy-pasteable
//!   CLI example.
//!
//! A surface that cannot return "verified" is not a fail-closed verifier, it is an
//! advertisement for a check that does not exist. They are DELETED. What replaced
//! each one already existed and is tested:
//!
//! | deleted | replacement |
//! |---|---|
//! | `verify_effect_vm_proof` (single v1 proof) | [`rotated_replay::verify_rotated_leg`] |
//! | `replay_chain` (v1 chain) | [`rotated_replay::verify_rotated_replay_chain`] |
//! | `replay_chain_recursive` / `verify_recursive_replay*` | same — the rotated leg IS the recursion-era unit |
//!
//! **What re-emits / breaks:** the `dregg-verifier` binary no longer accepts
//! `--proof/--pi/--vk-hash`, a JSON request on stdin, `replay-chain`, or
//! `scope-recursive`; each now prints usage and exits `ERROR` rather than pretending
//! to check something. `demo/two-ai-handoff/charlie.py` and
//! `demo/cross-app-e2e/verify_real.py` invoked `replay-chain` / `scope-recursive`
//! and were already getting a rejection on every run; they must be re-pointed at
//! `rotated-replay-chain`. Nothing persists a v1 proof; nothing needs migrating.

use serde::{Deserialize, Serialize};

pub mod aggregated_bundle;
pub mod bilateral_pair;
pub mod cross_fed;
/// Rotated replay-chain verify — the LIVE replay-chain verify. Verifies a chain of
/// `"effect-vm-rotated"` IR-v2 legs via the audited `verify_vm_descriptor2`.
///
/// UNCONDITIONAL as of 2026-08-05. It used to sit behind `#[cfg(feature = "verifier")]`,
/// a feature declared as `verifier = []` — it forwarded nothing to any dependency, so
/// the gate never selected anything; it only decided whether the crate's one real proof
/// verifier compiled. This is the verify floor (its code path calls no prover) and it
/// belongs on every build, including the seL4 verifier-PD's.
pub mod rotated_replay;
pub use aggregated_bundle::{
    AggregatedBundleVerdict, verify_aggregated_bundle_json, verify_aggregated_bundle_struct,
};
pub use bilateral_pair::{
    BilateralBundle, BilateralEntry, BilateralPiAgreement, check_bilateral_pi_agreement,
    fabricate_pi_only_witnessed_receipt,
};
pub use cross_fed::{
    CommitteeDescriptor, CrossFedVerdict, ValidatorDescriptor, verify_cross_fed_bundle,
};
pub use rotated_replay::{
    RotatedChainOutput, RotatedReplayLeg, RotatedReplayVerdict, verify_rotated_leg,
    verify_rotated_replay_chain,
};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// The result of a verification attempt, serialized to stdout.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifierOutput {
    pub verified: bool,
    pub reason: String,
}

impl VerifierOutput {
    pub fn accept(reason: impl Into<String>) -> Self {
        Self {
            verified: true,
            reason: reason.into(),
        }
    }

    pub fn reject(reason: impl Into<String>) -> Self {
        Self {
            verified: false,
            reason: reason.into(),
        }
    }
}

/// Exit codes used by the binary.
pub mod exit_code {
    pub const VERIFIED: i32 = 0;
    pub const REJECTED: i32 = 1;
    pub const ERROR: i32 = 2;
}

// ---------------------------------------------------------------------------
// Receipt <-> PI cross-binding (used by the rotated replay chain)
// ---------------------------------------------------------------------------

/// The shortest PI vector [`check_receipt_pi_binding`] can decide, DERIVED from the
/// highest offset the body reads rather than written down. Every offset it touches
/// lives in the v1 PI prefix a rotated leg publishes in full
/// (`trace_rotated::V1_PI_COUNT` = 42), so the deployed leg always satisfies it.
///
/// The previous precondition was `pi::ACTIVE_BASE_COUNT` (213), which did not make
/// the check strict — it made it **unreachable on every leg that ships**. Measured
/// 2026-07-27 against a real wide rotated proof from
/// `dregg_turn_prover::mint_transfer_proven_receipt`: the leg carries **68** felts, and
/// the binding answered `PI too short for receipt binding: have 68 elements, need at
/// least 213` on the only proof it was supposed to bind. Same shape as the
/// balance-limb bug in `circuit/src/effect_vm/verify.rs`; same fix — the
/// precondition is computed from the reads so it cannot drift away from them again.
pub const RECEIPT_PI_BINDING_MIN_LEN: usize =
    dregg_circuit::effect_vm::pi::TURN_HASH_BASE + dregg_circuit::effect_vm::pi::TURN_HASH_LEN;

/// Cross-bind a rotated leg's claimed public inputs against the receipt it attests
/// (and the prior receipt's hash, for the chain-walk invariant).
///
/// Returns `Some(reason)` on rejection, `None` on pass. This is the
/// EXECUTOR-HONESTY-AUDIT cross-cutting #3 enforcement: PI is not merely
/// deserialized, it is *checked against an expected value*.
///
/// Two teeth, both of which RUN on a real `"effect-vm-rotated"` leg:
///
/// - **T11 (stale-proof replay against a different receipt).**
///   `PI[TURN_HASH_BASE..+4]` must equal `canonical_32_to_felts_4(receipt.turn_hash)`.
///   `TURN_HASH_BASE` is 33 and the rotated leg publishes the v1 prefix `[0, 42)`, so
///   this is inside the window a real proof carries. The slot is not pinned to a
///   trace column by the AIR — the honest producer fills it
///   (`turn_prover::proven_receipt`) and it rides the Fiat–Shamir transcript — so
///   what this comparison forbids is RELABELLING: a genuine proof of turn A
///   presented alongside a receipt naming turn B.
/// - **T8 (forged chain link).** When `prev_receipt_hash` is `Some`, the receipt's own
///   `previous_receipt_hash` must equal it (`receipt[N].previous_receipt_hash ==
///   receipt[N-1].receipt_hash()`); when it is `None` the receipt is the chain head
///   and must not claim a predecessor. Verifying a suffix requires the caller to
///   supply the expected prior hash.
///
/// ⚠ **The honest producer must FILL the slot for this to bind anything.**
/// `dregg_turn_prover::proven_receipt` and the rotated-replay test minter both write
/// `canonical_32_to_felts_4(turn_hash)` into `PI[TURN_HASH_BASE..+4]`.
/// `dregg_sdk::prove_full_turn` does NOT (measured 2026-08-05: `TURN_HASH_BASE`
/// appears nowhere in `sdk/src/full_turn_proof.rs`, and `verify_full_turn_bound`
/// never reads `FullTurnProof::turn_hash`), so a leg minted by that path carries the
/// zero sentinel and this comparison would refuse a receipt naming a real turn. That
/// is a producer-side hole in the SDK, not a reason to weaken the comparison.
///
/// # What is NOT compared, and why that is not a hole
///
/// `PI[PREVIOUS_RECEIPT_HASH_BASE..+4]` and `PI[IS_AGENT_CELL]` used to be compared
/// here. Both comparisons are GONE, because neither offset exists on a leg that
/// ships and keeping them would have been worse than useless:
///
/// * `PREVIOUS_RECEIPT_HASH_BASE` is **42**, and the rotated producer slices the v1
///   PI vector at exactly `V1_PI_COUNT` = **42** before appending its four rotated
///   pins (`trace_rotated`: OLD commit / NEW commit / committed height / caveat
///   commit). So indices 42..46 of a real leg are those pins — measured
///   `[0, 0, 0, 531325421]` on a live proof whose receipt's
///   `canonical_32_to_felts_4(previous_receipt_hash)` was
///   `[740780208; 4]`. Comparing them would reject every honest proof.
/// * `IS_AGENT_CELL` is **81**, past the end of a 68-felt leg entirely.
///
/// The chain link is still bound to the proof, TRANSITIVELY and for real:
/// `Turn::hash()` absorbs `previous_receipt_hash` (`turn/src/turn.rs`, "Include
/// previous_receipt_hash to bind to causal ordering"), and `PI[TURN_HASH]` is
/// `canonical_32_to_felts_4` of that hash. A receipt re-minted for a different chain
/// position therefore names a different `turn_hash`, and the T11 comparison above
/// refuses it. That is the same argument the pre-existing note below makes for
/// `EFFECTS_HASH_GLOBAL` and `ACTOR_NONCE` — it simply also covers the chain link.
///
/// Does NOT cross-check EFFECTS_HASH_GLOBAL or ACTOR_NONCE: those derive
/// from the Turn (call_forest, nonce), not the Receipt. The receipt's
/// `turn_hash` field commits to both via the canonical Turn::hash, and
/// the TURN_HASH PI binding above transitively guards them — a divergent
/// EFFECTS_HASH_GLOBAL or ACTOR_NONCE in the proof's PI would imply a
/// different Turn::hash, which the TURN_HASH check catches.
pub fn check_receipt_pi_binding(
    receipt: &dregg_turn::TurnReceipt,
    public_inputs: &[u32],
    prev_receipt_hash: Option<[u8; 32]>,
) -> Option<String> {
    use dregg_circuit::effect_vm::pi;
    use dregg_commit::typed::canonical_32_to_felts_4;

    // Chain-walk invariant (T8): receipt[N].previous_receipt_hash must
    // match receipt[N-1].receipt_hash().
    match (prev_receipt_hash, receipt.previous_receipt_hash) {
        (Some(expected), Some(claimed)) if expected != claimed => {
            return Some(format!(
                "chain-walk break: receipt.previous_receipt_hash {} != prior receipt_hash {}",
                hex::encode(claimed),
                hex::encode(expected)
            ));
        }
        (Some(expected), None) => {
            return Some(format!(
                "chain-walk break: receipt.previous_receipt_hash is None, expected {}",
                hex::encode(expected)
            ));
        }
        (None, Some(claimed)) => {
            return Some(format!(
                "chain-walk break: chain head has receipt.previous_receipt_hash {}, expected None",
                hex::encode(claimed)
            ));
        }
        _ => {}
    }

    // PI length sanity, derived from the reads (see `RECEIPT_PI_BINDING_MIN_LEN`).
    let pi_len = public_inputs.len();
    if pi_len < RECEIPT_PI_BINDING_MIN_LEN {
        return Some(format!(
            "PI too short for receipt binding: have {} elements, need at least {} \
             (the v1 prefix through TURN_HASH)",
            pi_len, RECEIPT_PI_BINDING_MIN_LEN
        ));
    }

    // TURN_HASH binding (T11).
    let expected_turn_hash = canonical_32_to_felts_4(&receipt.turn_hash);
    for i in 0..pi::TURN_HASH_LEN {
        let claimed = public_inputs[pi::TURN_HASH_BASE + i];
        let expected = expected_turn_hash[i].as_u32();
        if claimed != expected {
            return Some(format!(
                "PI[TURN_HASH_BASE+{}] = {} but canonical_32_to_felts_4(receipt.turn_hash)[{}] = {}",
                i, claimed, i, expected
            ));
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_receipt() -> dregg_turn::TurnReceipt {
        dregg_turn::TurnReceipt {
            turn_hash: [0u8; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 0,
            effects_hash: [0u8; 32],
            computrons_used: 0,
            action_count: 0,
            previous_receipt_hash: None,
            agent: dregg_types::CellId::from_bytes([0u8; 32]),
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    // ---- PI completeness adversarial tests (EXECUTOR-HONESTY-AUDIT #3) ----

    /// Build the ROTATED-SHAPED PI vector a real `"effect-vm-rotated"` leg carries
    /// for `receipt`: the v1 prefix `[0, V1_PI_COUNT)` plus the four appended rotated
    /// pins, with `PI[TURN_HASH_BASE..+4]` filled the way the honest producer fills it
    /// (`turn_prover::proven_receipt`). Deliberately `ROT_PI_COUNT` felts and NOT
    /// `ACTIVE_BASE_COUNT` — a 213-slot vector is a shape no leg ships, and testing
    /// against one is exactly how this check hid.
    fn rotated_pi_from_receipt(receipt: &dregg_turn::TurnReceipt) -> Vec<u32> {
        use dregg_circuit::effect_vm::pi;
        use dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT;
        use dregg_commit::typed::canonical_32_to_felts_4;
        let mut pi_vec = vec![0u32; ROT_PI_COUNT];
        let th = canonical_32_to_felts_4(&receipt.turn_hash);
        for i in 0..pi::TURN_HASH_LEN {
            pi_vec[pi::TURN_HASH_BASE + i] = th[i].as_u32();
        }
        pi_vec
    }

    #[test]
    fn pi_binding_accepts_consistent_pi() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        let piv = rotated_pi_from_receipt(&r);
        assert!(
            check_receipt_pi_binding(&r, &piv, None).is_none(),
            "consistent PI must not be rejected"
        );
    }

    #[test]
    fn pi_binding_rejects_tampered_turn_hash() {
        use dregg_circuit::effect_vm::pi;
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        let mut piv = rotated_pi_from_receipt(&r);
        // Tamper with PI[TURN_HASH_BASE]: even though the proof would
        // verify algebraically (we don't run the STARK here), the
        // verifier MUST reject because the PI no longer matches the
        // receipt's claimed turn_hash. Closes T11 at the verifier layer.
        piv[pi::TURN_HASH_BASE] ^= 0xDEAD_BEEF;
        let reason = check_receipt_pi_binding(&r, &piv, None)
            .expect("tampered PI[TURN_HASH_BASE] must be rejected");
        assert!(
            reason.contains("TURN_HASH_BASE"),
            "rejection should name TURN_HASH_BASE; got: {reason}"
        );
    }

    #[test]
    fn pi_binding_rejects_non_genesis_chain_head() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        r.previous_receipt_hash = Some([0x33u8; 32]);
        let piv = rotated_pi_from_receipt(&r);
        let reason = check_receipt_pi_binding(&r, &piv, None)
            .expect("chain head with a previous_receipt_hash must be rejected");
        assert!(
            reason.contains("chain head"),
            "rejection should name chain head; got: {reason}"
        );
    }

    #[test]
    fn pi_binding_rejects_chain_walk_break() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        // The receipt's previous_receipt_hash says one thing...
        r.previous_receipt_hash = Some([0x77u8; 32]);
        let piv = rotated_pi_from_receipt(&r);
        // ...but the chain-walk says the prior receipt hashed to
        // something else. The verifier must catch this (T8).
        let reason = check_receipt_pi_binding(&r, &piv, Some([0x88u8; 32]))
            .expect("chain-walk break must be rejected");
        assert!(
            reason.contains("chain-walk"),
            "rejection should name chain-walk; got: {reason}"
        );
    }

    #[test]
    fn pi_binding_rejects_missing_previous_receipt_hash_in_chain() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        // Receipt claims to be a head (no previous_receipt_hash)...
        r.previous_receipt_hash = None;
        let piv = rotated_pi_from_receipt(&r);
        // ...but the chain-walk says it should chain from somewhere.
        let reason = check_receipt_pi_binding(&r, &piv, Some([0x55u8; 32]))
            .expect("missing previous_receipt_hash mid-chain must be rejected");
        assert!(
            reason.contains("chain-walk"),
            "rejection should name chain-walk; got: {reason}"
        );
    }

    #[test]
    fn pi_binding_rejects_short_pi() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        let reason = check_receipt_pi_binding(&r, &vec![0u32; 10], None)
            .expect("PI too short to carry turn-identity slots must be rejected");
        assert!(
            reason.contains("too short"),
            "rejection should name 'too short'; got: {reason}"
        );
    }

    /// THE PRECONDITION IS DERIVED FROM THE READS, NOT WRITTEN DOWN. A vector one
    /// felt shy of the last TURN_HASH slot is refused; the exact length is accepted.
    /// Both poles, so a future widening of the precondition that would re-orphan the
    /// check on a real leg fails HERE.
    #[test]
    fn pi_binding_precondition_is_exactly_the_highest_offset_it_reads() {
        use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        let piv = rotated_pi_from_receipt(&r);

        assert!(
            RECEIPT_PI_BINDING_MIN_LEN <= V1_PI_COUNT,
            "the precondition ({RECEIPT_PI_BINDING_MIN_LEN}) must fit inside the v1 PI window a \
             rotated leg publishes ({V1_PI_COUNT}); above it, the check is unreachable on the \
             only leg that ships"
        );
        let short = piv[..RECEIPT_PI_BINDING_MIN_LEN - 1].to_vec();
        assert!(
            check_receipt_pi_binding(&r, &short, None).is_some_and(|m| m.contains("too short")),
            "one felt short of the last TURN_HASH slot must be refused"
        );
        let exact = piv[..RECEIPT_PI_BINDING_MIN_LEN].to_vec();
        assert!(
            check_receipt_pi_binding(&r, &exact, None).is_none(),
            "exactly the offsets the body reads must be enough to DECIDE"
        );
    }
}

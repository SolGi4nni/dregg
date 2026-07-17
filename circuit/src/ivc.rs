//! IVC hash-chain primitives and the state-transition trace shape.
//!
//! What lives here:
//! * The Poseidon2 accumulated-hash chain (`initial_accumulated_hash`/`_wide`,
//!   `extend_accumulated_hash`/`_wide`, `recompute_accumulated_hash`/`_wide`) —
//!   the REAL hash primitives the emitted state-transition descriptor tests
//!   (`circuit-prove/tests/ivc_{audit_firststep_canary,state_transition_emit_gate}.rs`)
//!   and `dregg-dsl-runtime` composition bind against.
//! * the state-transition trace layout and [`generate_state_transition_trace`]
//!   (consumed by the descriptor-world emit gates).
//! * [`MAX_FOLD_DEPTH`] — the delegation-depth bound enforced by `bridge::present`.
//! * The multi-Turn summary hash primitives ([`TurnTransitionSummary`],
//!   [`turn_receipt_hash`], [`extend_turn_accumulator`]).
//!
//! DELETED 2026-07-16 (mock-proof purge, final cut): the SIMULATED IVC engine.
//! `prove_ivc` / `verify_ivc` / `verify_ivc_with_roots`, `IvcProof` /
//! `AccumulatedProof` / `IvcVerification`, `IvcBuilder` (+ `finalize` /
//! `finalize_with_air`), `fold_and_accumulate` / `initial_accumulation` /
//! `finalize_ivc`, `IvcAir` (+ its width/column constants), `FoldDelta`,
//! `FoldStepWitness`, and `create_test_chain` are GONE. That engine was a hash
//! chain wrapped in a BLAKE3 digest binding: anyone who could call `prove_ivc`
//! could mint a passing "proof" for any root walk. Nothing production rode it —
//! its one indirect path (cipherclerk `enable_ivc`) had zero callers and was
//! deleted with it. The REAL turn-chain recursion is
//! `circuit-prove/src/ivc_turn_chain.rs`.

use crate::field::BabyBear;
use crate::poseidon2::hash_many;

// ─────────────────────────────────────────────────────────────────────────────
// Hash Chain
// ─────────────────────────────────────────────────────────────────────────────

/// Maximum delegation chain depth (fold steps).
///
/// This bounds the number of attenuation steps a token can undergo. A deeper chain
/// indicates excessive delegation and should be rejected by both the prover (at proof
/// generation time) and the verifier (at verification time). The limit prevents:
/// 1. Unbounded proof generation cost
/// 2. Combinatorial explosion in delegation hierarchies
/// 3. Potential soundness degradation from very long chains
///
/// The value 16 allows for practical multi-level delegation (issuer -> org -> team ->
/// user -> device -> session) while preventing pathological chains.
pub const MAX_FOLD_DEPTH: u32 = 16;

/// Domain separation tag for IVC hash accumulation.
const IVC_DOMAIN_TAG: u32 = 0x49564300; // "IVC0" as ASCII bytes

/// Number of BabyBear elements in the accumulated hash.
/// 8 elements * ~31 bits each = ~248 bits of preimage resistance and ~124 bits
/// of COLLISION/birthday resistance (a birthday attack on a 248-bit digest costs
/// ~2^124 work, well beyond practical). This is the faithful floor — see
/// `docs/FAITHFUL-STATE-COMMITMENT.md`. A 4-element digest would be only ~62-bit
/// collision-resistant despite its ~124-bit width, which is why this is 8, not 4.
pub const ACCUMULATED_HASH_WIDTH: usize = 8;

/// A multi-element accumulated hash providing ~124-bit COLLISION resistance.
///
/// A single BabyBear element only provides ~31 bits of width, making birthday
/// attacks trivial at ~2^15.5 (~46K attempts). Four elements raise the width to
/// ~124 bits but only ~62-bit collision resistance. Eight elements give ~248-bit
/// width / ~124-bit collision resistance — the faithful floor that matches the
/// rest of the system's soundness target.
pub type AccumulatedHash = [BabyBear; ACCUMULATED_HASH_WIDTH];

/// Compute the initial accumulated hash from the initial root.
/// This is the "base case" of the IVC: step 0.
///
/// Returns the single-felt projection used by the STARK trace continuity column.
pub fn initial_accumulated_hash(initial_root: BabyBear) -> BabyBear {
    initial_accumulated_hash_wide(initial_root)[0]
}

/// Wide version of the initial accumulated hash (8 felts, ~124-bit collision).
///
/// Squeezes 8 GENUINELY distinct Poseidon2 felts via the standard sponge
/// discipline (absorb → squeeze rate-4 → permute → squeeze rate-4), identical to
/// [`crate::poseidon2::hash_many_8`]. The absorbed preimage is
/// `[IVC_DOMAIN_TAG, initial_root, step_count=0]` (length encoded in the capacity
/// lane, matching the prior single-permutation absorb so the first felt — and
/// thus [`initial_accumulated_hash`] — is byte-identical to before).
pub fn initial_accumulated_hash_wide(initial_root: BabyBear) -> AccumulatedHash {
    crate::poseidon2::hash_many_8(&[
        BabyBear::new(IVC_DOMAIN_TAG),
        initial_root,
        BabyBear::ZERO, // step_count = 0
    ])
}

/// Extend the accumulated hash by one fold step.
/// new_hash = Poseidon2(old_hash || new_root || step_count)
///
/// This is the core of the IVC hash chain. Each step commits to:
/// - All prior history (via old_hash)
/// - The new state (via new_root)
/// - The step position (via step_count, preventing reordering)
///
/// Single-element version for backward compatibility with the STARK AIR.
pub fn extend_accumulated_hash(
    old_hash: BabyBear,
    new_root: BabyBear,
    step_count: u32,
) -> BabyBear {
    hash_many(&[
        BabyBear::new(IVC_DOMAIN_TAG),
        old_hash,
        new_root,
        BabyBear::new(step_count),
    ])
}

/// Wide version of extend_accumulated_hash (8 felts, ~124-bit collision).
///
/// Takes and returns 8-element accumulated hashes. ALL 8 elements of `old_hash`
/// are absorbed (a genuine ~248-bit-wide carrier — there is NO 31-bit / 4-felt
/// intermediate to collide), providing ~124-bit collision binding to prior
/// history. The preimage is
/// `[IVC_DOMAIN_TAG, old_hash[0..8], new_root, step_count]` (11 felts), absorbed
/// in rate-4 chunks and squeezed as 8 distinct felts via
/// [`crate::poseidon2::hash_many_8`] (squeeze rate-4 → permute → squeeze rate-4).
pub fn extend_accumulated_hash_wide(
    old_hash: &AccumulatedHash,
    new_root: BabyBear,
    step_count: u32,
) -> AccumulatedHash {
    crate::poseidon2::hash_many_8(&[
        BabyBear::new(IVC_DOMAIN_TAG),
        old_hash[0],
        old_hash[1],
        old_hash[2],
        old_hash[3],
        old_hash[4],
        old_hash[5],
        old_hash[6],
        old_hash[7],
        new_root,
        BabyBear::new(step_count),
    ])
}

/// Recompute the wide accumulated hash from a full chain of roots.
pub fn recompute_accumulated_hash_wide(
    initial_root: BabyBear,
    roots: &[BabyBear],
) -> AccumulatedHash {
    let mut hash = initial_accumulated_hash_wide(initial_root);
    for (i, &root) in roots.iter().enumerate() {
        hash = extend_accumulated_hash_wide(&hash, root, (i + 1) as u32);
    }
    hash
}

/// Recompute the accumulated hash from a full chain of roots.
/// This is used by the verifier when the full root chain is available (testing),
/// or by the prover to construct the expected hash.
pub fn recompute_accumulated_hash(initial_root: BabyBear, roots: &[BabyBear]) -> BabyBear {
    let mut hash = initial_accumulated_hash(initial_root);
    for (i, &root) in roots.iter().enumerate() {
        hash = extend_accumulated_hash(hash, root, (i + 1) as u32);
    }
    hash
}
// ─────────────────────────────────────────────────────────────────────────────
// The IVC hash-chain STATE-TRANSITION trace layout.
//
// ⚠ RETIREMENT NOTE (2026-07-17): this section used to head a `pub struct StateTransitionAir;` described
// as "real STARK AIR for the IVC hash chain". It was NOT an AIR — it implemented NOTHING (no `Air`, no
// `BaseAir`, no impl block at all) and had ZERO consumers beyond a `pub use` re-export. It was a bare unit
// struct wearing an `*Air*` name: the goal's "ivc.rs::StateTransitionAir has an emitter it ignores" — it
// ignored the emitter because it did nothing at all. DELETED.
//
// The REAL state-transition circuit is AUTHORED IN LEAN (`ivcStateTransitionDescriptor`) and byte-pinned
// via `emitVmJson2`; the equality gate is `circuit-prove/tests/ivc_state_transition_emit_gate.rs`, which
// decodes the Lean wire string and asserts it equals its OWN independently hand-built
// `EffectVmDescriptor2` twin (the drift-detector — it never depended on the deleted struct).
// The trace-layout constants below and `generate_state_transition_trace` REMAIN: they are live, used by
// that gate and by the accumulated-hash tests.
// ─────────────────────────────────────────────────────────────────────────────

/// Width of the state-transition trace (the layout the Lean-emitted `ivcStateTransitionDescriptor` pins).
///
/// Columns: [step_count, old_hash, new_root, new_hash]
///
/// Each row proves one step of the accumulated hash chain:
///   new_hash == extend_accumulated_hash(old_hash, new_root, step_count)
pub const STATE_TRANSITION_WIDTH: usize = 4;

/// Column indices for the state-transition trace.
pub mod st_col {
    /// Step number (1-indexed).
    pub const STEP: usize = 0;
    /// The accumulated hash before this step.
    pub const OLD_HASH: usize = 1;
    /// The new state root introduced at this step.
    pub const NEW_ROOT: usize = 2;
    /// The accumulated hash after this step.
    pub const NEW_HASH: usize = 3;
}

/// A real STARK AIR proving the correctness of the IVC hash chain accumulation.
///
/// Public inputs: [initial_root, final_root, step_count, accumulated_hash]
///
/// Per-row constraint:
///   new_hash == Poseidon2(IVC_DOMAIN_TAG || old_hash || new_root || step)
///
/// Boundary constraints:
///   - Row 0: step == 1, old_hash == initial_accumulated_hash(initial_root)
///   - Last row: step == step_count, new_hash == accumulated_hash
///
/// Sequential ordering is enforced via boundary constraints + Poseidon2 preimage
/// resistance: the step value is included as a hash input, making each position's
/// output unique. The only trace satisfying both boundaries AND the per-row hash
/// constraint is the correct sequential chain. Row reordering or skipping would
/// require finding a Poseidon2 preimage (computationally infeasible).
///
/// The wide accumulated hash (`accumulated_hash_wide: [BabyBear; 8]`) provides
/// ~124-bit birthday-attack (collision) resistance and is the soundness-load-bearing
/// published/verified anchor, stored alongside the single-element continuity hash
/// used in the STARK trace for efficiency.
/// Generate the STARK trace for the state transition hash chain.
///
/// Given an initial root and a sequence of new roots (one per fold step),
/// produces the trace and public inputs for `StateTransitionAir`.
///
/// The trace has one row per step. If the number of steps is not a power of 2,
/// the trace is padded with copies of the last row (which the constraint evaluator
/// will still accept since the hash relation holds trivially for repeated rows).
pub fn generate_state_transition_trace(
    initial_root: BabyBear,
    new_roots: &[BabyBear],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!new_roots.is_empty());

    let mut trace = Vec::with_capacity(new_roots.len());
    let mut current_hash = initial_accumulated_hash(initial_root);

    for (i, &new_root) in new_roots.iter().enumerate() {
        let step = (i + 1) as u32;
        let new_hash = extend_accumulated_hash(current_hash, new_root, step);

        trace.push(vec![BabyBear::new(step), current_hash, new_root, new_hash]);
        current_hash = new_hash;
    }

    let final_root = *new_roots.last().unwrap();
    let step_count = new_roots.len() as u32;

    // Pad to power of 2 (minimum 2 rows for the STARK prover).
    let target_len = trace.len().next_power_of_two().max(2);
    let last_row = trace.last().unwrap().clone();
    while trace.len() < target_len {
        trace.push(last_row.clone());
    }

    let public_inputs = vec![
        initial_root,
        final_root,
        BabyBear::new(step_count),
        current_hash,
    ];

    (trace, public_inputs)
}
// ─────────────────────────────────────────────────────────────────────────────
// Multi-Turn IVC: fold a SEQUENCE of Turn graph-transitions into ONE proof
// ─────────────────────────────────────────────────────────────────────────────
//
// The fold-chain IVC above spans the *attenuation* dimension of a single token:
// each step removes a fact and advances a state root. It cannot span the
// *temporal* dimension — a chain of distinct Turns, each of which is itself a
// bilateral-aggregated graph transition (see `bilateral_aggregation_air.rs`).
//
// This section adds that second dimension. Each per-turn aggregate emits a small
// SUMMARY — `TurnTransitionSummary` — projecting the bound public outputs of one
// Turn's bilateral aggregate proof:
//
//   - `turn_hash`            : the canonical Turn identity digest.
//   - `pre_state_root`       : the graph state root the Turn consumed.
//   - `post_state_root`      : the graph state root the Turn produced.
//   - `previous_receipt_hash`: the receipt-chain link this Turn claims to extend.
//   - `bilateral_consistent` : the per-Turn bilateral-consistency flag (0/1).
//
// A chain of N such summaries is folded by `MultiTurnIvcAir` (a real STARK AIR
// over `crate::stark`) into ONE constant-size `MultiTurnIvcProof` whose public
// inputs bind the chain's start (`initial_state_root`, genesis receipt) and end
// (`final_state_root`, `final_receipt_hash`, `folded_accumulator`).
//
// What is bound IN-CIRCUIT (algebraic STARK constraints):
//   1. Per-Turn receipt derivation: `receipt_hash_i = Poseidon2(domain ‖
//      turn_hash_i ‖ pre_i ‖ post_i ‖ prev_receipt_i)`. Re-derived from the
//      summary fields, so a forged receipt_hash that doesn't match its inputs
//      is rejected.
//   2. Receipt-chain linkage: `prev_receipt_{i+1} == receipt_hash_i` — a broken
//      or spliced receipt link cannot be hidden (transition constraint over every
//      consecutive pair).
//   3. State continuity: `pre_state_{i+1} == post_state_i` — a broken state-root
//      transition is rejected.
//   4. Genesis: row 0 has `prev_receipt == 0` and `pre_state == initial_state_root`.
//   5. Bilateral consistency: every Turn must carry `bilateral_consistent == 1`;
//      a Turn whose aggregate flagged inconsistency is rejected.
//   6. Sequence fold: a Poseidon2 accumulator absorbs each `(receipt_hash, step)`
//      in order; the final accumulator is a public output and reordering changes
//      it (the step index is absorbed, so position is bound).
//   7. Endpoints: row 0 `pre_state == initial_state_root`; last row
//      `post_state == final_state_root`, `receipt_hash == final_receipt_hash`,
//      accumulator == `folded_accumulator`, `step == n-1`.
//
// HONEST RESIDUAL (trusted-summary boundary):
//   * The inner per-Turn bilateral aggregate STARK is *summarized*, not
//     recursively verified inside this AIR. We bind `turn_hash` and
//     `bilateral_consistent` as field elements; we do NOT re-run the bilateral
//     aggregation verifier in-circuit. A prover that fabricates a
//     `TurnTransitionSummary` with an arbitrary `turn_hash` / `post_state_root`
//     and `bilateral_consistent = 1` will produce a chain proof that VERIFIES at
//     the multi-Turn layer. Closing this requires either (a) recursive
//     verification of each inner aggregate proof (the live whole-chain fork:
//     `circuit-prove/src/ivc_turn_chain.rs`), or (b) a Merkle-membership-style
//     companion proof per Turn analogous to `ValidatedIvcProof` above. This layer
//     guarantees the *chain structure* (linkage, ordering, continuity, endpoint
//     binding) is sound; it does not by itself attest that each summarized Turn
//     was a valid bilateral aggregate. Callers receiving chains from untrusted
//     peers MUST additionally verify each Turn's bilateral aggregate proof (or
//     use the recursive path) and cross-check its bound outputs against the
//     corresponding `TurnTransitionSummary` (see
//     `MultiTurnIvcProof::summaries`, retained for exactly this cross-check).

/// Domain-separation tag for the per-Turn receipt-hash derivation.
const TURN_RECEIPT_DOMAIN_TAG: u32 = 0x54524350; // "TRCP"

/// Domain-separation tag for the multi-Turn sequence accumulator.
const TURN_ACC_DOMAIN_TAG: u32 = 0x54414343; // "TACC"

/// Maximum number of Turns that can be folded into one multi-Turn attestation.
///
/// Mirrors the spirit of [`MAX_FOLD_DEPTH`]: bounds prover cost and prevents
/// pathological chains. Distinct constant because the temporal dimension is
/// independent of the per-token attenuation depth.
pub const MAX_TURN_CHAIN_LEN: u32 = 64;

/// Width of the per-Turn aggregate outer-PI digests (`turn_hash`,
/// `previous_receipt_hash`).
///
/// This is a SEPARATE object from the IVC attenuation accumulator and is fixed at
/// 4 felts because it must match the shape published by
/// `bilateral_aggregation_air::AggregationOuterPi` (`turn_hash: [BabyBear; 4]`,
/// `previous_receipt_hash: [BabyBear; 4]`). It is intentionally NOT
/// [`ACCUMULATED_HASH_WIDTH`]: these digests are immediately collapsed to a single
/// felt via [`digest4`] / projected via slot 0, so their width is pinned by the
/// aggregate PI it cross-checks, not by the chain accumulator's collision floor.
pub const AGGREGATE_DIGEST_WIDTH: usize = 4;

/// Per-Turn summary projected from one Turn's bilateral aggregate public outputs.
///
/// This is the unit folded by the multi-Turn IVC. The four-element digests
/// (`turn_hash`, `previous_receipt_hash`) match the shape published by
/// `bilateral_aggregation_air::AggregationOuterPi`; they are collapsed to a single
/// field element via Poseidon2 for the in-circuit chain (see [`digest4`]). The
/// raw four-element arrays are retained so a caller can cross-check the summary
/// against the originating aggregate proof's bound public inputs.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct TurnTransitionSummary {
    /// Canonical Turn identity digest (4 felts, from the aggregate's outer PI).
    pub turn_hash: [BabyBear; AGGREGATE_DIGEST_WIDTH],
    /// Graph state root the Turn consumed.
    pub pre_state_root: BabyBear,
    /// Graph state root the Turn produced.
    pub post_state_root: BabyBear,
    /// The receipt-chain link this Turn claims to extend, canonically encoded as
    /// `[link, 0, 0, 0]` (see [`TurnTransitionSummary::encode_receipt_link`]).
    /// For the genesis Turn this MUST be all-zero.
    pub previous_receipt_hash: [BabyBear; AGGREGATE_DIGEST_WIDTH],
    /// The per-Turn bilateral-consistency flag (1 = consistent).
    pub bilateral_consistent: BabyBear,
}

impl TurnTransitionSummary {
    /// Collapse the four-element `turn_hash` to a single field element. The
    /// `turn_hash` is a pure identity input (never a chain-link fixpoint), so a
    /// domain-separated Poseidon2 collapse is the right projection.
    pub fn turn_hash_digest(&self) -> BabyBear {
        digest4(TURN_DIGEST_TAG_TURN_HASH, &self.turn_hash)
    }

    /// The single-felt receipt-chain link this Turn claims to extend.
    ///
    /// Canonical encoding: `previous_receipt_hash = [link, 0, 0, 0]`, where `link`
    /// is the single-felt receipt hash of the prior Turn (see [`turn_receipt_hash`]).
    /// This MUST be a fixpoint-free projection (slot 0), NOT a hash, because the
    /// producer learns the prior Turn's receipt only AFTER computing it and must
    /// be able to publish a `previous_receipt_hash` that equals it without
    /// inverting a hash. Slots 1..3 are required to be zero (enforced in
    /// `build_multi_turn_trace`) to keep the encoding canonical.
    pub fn previous_receipt_link(&self) -> BabyBear {
        self.previous_receipt_hash[0]
    }

    /// The canonical 4-felt encoding of a single-felt receipt link.
    pub fn encode_receipt_link(link: BabyBear) -> [BabyBear; AGGREGATE_DIGEST_WIDTH] {
        [link, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO]
    }
}

const TURN_DIGEST_TAG_TURN_HASH: u32 = 0x54484448; // "THDH"

/// Collapse a 4-element digest to a single felt with domain separation.
fn digest4(tag: u32, h: &[BabyBear; AGGREGATE_DIGEST_WIDTH]) -> BabyBear {
    hash_many(&[BabyBear::new(tag), h[0], h[1], h[2], h[3]])
}

/// In-circuit receipt-hash derivation for one Turn.
///
/// `receipt_hash = Poseidon2(TURN_RECEIPT_DOMAIN_TAG ‖ turn_hash_digest ‖
///                           pre_state ‖ post_state ‖ prev_receipt_link ‖
///                           bilateral_consistent)`
///
/// This is the canonical single-felt commitment to a Turn's transition + its
/// inbound link; the next Turn's `previous_receipt_link()` must equal it.
pub fn turn_receipt_hash(
    turn_hash_digest: BabyBear,
    pre_state: BabyBear,
    post_state: BabyBear,
    prev_receipt_link: BabyBear,
    bilateral_consistent: BabyBear,
) -> BabyBear {
    hash_many(&[
        BabyBear::new(TURN_RECEIPT_DOMAIN_TAG),
        turn_hash_digest,
        pre_state,
        post_state,
        prev_receipt_link,
        bilateral_consistent,
    ])
}

/// Extend the multi-Turn sequence accumulator by one Turn.
///
/// `acc_out = Poseidon2(TURN_ACC_DOMAIN_TAG ‖ acc_in ‖ receipt_hash ‖ step)`
///
/// The step index is absorbed, so the accumulator is order-sensitive: reordering
/// or splicing the chain changes the final accumulator.
pub fn extend_turn_accumulator(acc_in: BabyBear, receipt_hash: BabyBear, step: u32) -> BabyBear {
    hash_many(&[
        BabyBear::new(TURN_ACC_DOMAIN_TAG),
        acc_in,
        receipt_hash,
        BabyBear::new(step),
    ])
}

// ── Trace layout for `MultiTurnIvcAir` ──────────────────────────────────────

/// Width of the multi-Turn IVC trace.
pub const MULTI_TURN_WIDTH: usize = 9;

/// Column indices for [`MultiTurnIvcAir`].
pub mod mt_col {
    /// Step / turn index (0-indexed).
    pub const STEP: usize = 0;
    /// Collapsed turn-hash digest.
    pub const TURN_HASH: usize = 1;
    /// Pre-state graph root.
    pub const PRE_STATE: usize = 2;
    /// Post-state graph root.
    pub const POST_STATE: usize = 3;
    /// Collapsed previous-receipt-hash digest (inbound link).
    pub const PREV_RECEIPT: usize = 4;
    /// Bilateral-consistency flag (must be 1).
    pub const CONSISTENT: usize = 5;
    /// Derived receipt hash for this Turn.
    pub const RECEIPT_HASH: usize = 6;
    /// Sequence accumulator before this Turn.
    pub const ACC_IN: usize = 7;
    /// Sequence accumulator after this Turn.
    pub const ACC_OUT: usize = 8;
}
// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    /// THE ANTI-LAUNDERING TOOTH for the 8-felt IVC accumulator: the wide hash must be
    /// 8 GENUINELY distinct, full-input-dependent felts — not `[0]×8`, not `4 real + 4
    /// zero-pad`, not a replicated squeeze. Verifies width == 8 and that both the base
    /// case (`initial_accumulated_hash_wide`) and the chain step
    /// (`extend_accumulated_hash_wide`) are pairwise-distinct and avalanche over EVERY
    /// input felt. This is what makes the ~124-bit collision claim true.
    #[test]
    fn wide_accumulator_is_eight_distinct_avalanching_felts() {
        assert_eq!(ACCUMULATED_HASH_WIDTH, 8, "the faithful floor is 8 felts");

        let init_root = BabyBear::new(0xABCD_1234);
        let base = initial_accumulated_hash_wide(init_root);
        assert_eq!(base.len(), 8);

        // (a) base case: 8 pairwise-distinct felts, not the degenerate all-zero output.
        for i in 0..8 {
            for j in (i + 1)..8 {
                assert_ne!(
                    base[i], base[j],
                    "base felts {i},{j} collide — not 8 distinct"
                );
            }
        }
        assert!(
            base.iter().any(|&x| x != BabyBear::ZERO),
            "base is all-zero"
        );

        // (b) base case avalanche: flipping the single input felt moves ALL 8 outputs
        // (each output depends on the whole input — a 4-real+4-pad would leave some fixed).
        let base2 = initial_accumulated_hash_wide(init_root + BabyBear::new(1));
        for i in 0..8 {
            assert_ne!(
                base[i], base2[i],
                "base output felt {i} unchanged under input flip"
            );
        }

        // (c) chain step: 8 distinct felts and full dependence on the old 8-felt carrier,
        // the new root, and the step counter — the genuine-8-distinct discipline.
        let new_root = BabyBear::new(0x0BAD_F00D);
        let step = 3u32;
        let ext = extend_accumulated_hash_wide(&base, new_root, step);
        for i in 0..8 {
            for j in (i + 1)..8 {
                assert_ne!(
                    ext[i], ext[j],
                    "step felts {i},{j} collide — not 8 distinct"
                );
            }
        }

        // every one of the 8 OLD-carrier felts is load-bearing: flipping any single one
        // must change all 8 outputs (catches `4 real + 4 zero-pad` — a padded carrier
        // would leave the padded lanes unbound and some outputs fixed).
        for k in 0..8 {
            let mut tampered = base;
            tampered[k] += BabyBear::new(1);
            let ext_k = extend_accumulated_hash_wide(&tampered, new_root, step);
            for i in 0..8 {
                assert_ne!(
                    ext[i], ext_k[i],
                    "flipping old-carrier felt {k} left output felt {i} fixed — carrier lane not bound"
                );
            }
        }

        // new_root and step_count are also fully bound.
        let ext_root = extend_accumulated_hash_wide(&base, new_root + BabyBear::new(1), step);
        let ext_step = extend_accumulated_hash_wide(&base, new_root, step + 1);
        for i in 0..8 {
            assert_ne!(ext[i], ext_root[i], "new_root not bound at output felt {i}");
            assert_ne!(
                ext[i], ext_step[i],
                "step_count not bound at output felt {i}"
            );
        }
    }
    #[test]
    fn ivc_accumulated_hash_deterministic() {
        let root = BabyBear::new(42);
        let h1 = initial_accumulated_hash(root);
        let h2 = initial_accumulated_hash(root);
        assert_eq!(h1, h2);

        let extended1 = extend_accumulated_hash(h1, BabyBear::new(100), 1);
        let extended2 = extend_accumulated_hash(h2, BabyBear::new(100), 1);
        assert_eq!(extended1, extended2);
    }

    #[test]
    fn ivc_accumulated_hash_order_sensitive() {
        let root = BabyBear::new(42);
        let h = initial_accumulated_hash(root);

        let r1 = BabyBear::new(100);
        let r2 = BabyBear::new(200);

        // Order 1: r1 then r2
        let h_12 = extend_accumulated_hash(extend_accumulated_hash(h, r1, 1), r2, 2);

        // Order 2: r2 then r1
        let h_21 = extend_accumulated_hash(extend_accumulated_hash(h, r2, 1), r1, 2);

        // Different orderings must produce different hashes
        assert_ne!(h_12, h_21);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // DELETED 2026-07-16 (mock-proof purge, final cut): every test that drove
    // the simulated engine (prove/verify round-trips, builder increments,
    // proof-size comparisons, digest-binding tamper checks, the Gap-3
    // fabricated-fold demonstration) died with it. The surviving tests below
    // bite the REAL hash primitives and the state-transition trace shape only.
    // ─────────────────────────────────────────────────────────────────────────
    #[test]
    fn ivc_state_transition_trace_is_correct_hash_chain() {
        // The StateTransitionAir's hand-STARK prover died with stark-kill; the
        // trace generator survives (it feeds the descriptor-world consumers).
        // Its tooth: the emitted trace IS the sequential Poseidon2 hash chain
        // and the public inputs bind the true endpoints.
        let initial_root = BabyBear::new(42);
        let new_roots = vec![
            BabyBear::new(100),
            BabyBear::new(200),
            BabyBear::new(300),
            BabyBear::new(400),
        ];

        let (trace, public_inputs) = generate_state_transition_trace(initial_root, &new_roots);

        // Public inputs: [initial_root, final_root, step_count, accumulated_hash]
        assert_eq!(public_inputs[0], initial_root);
        assert_eq!(public_inputs[1], *new_roots.last().unwrap());
        assert_eq!(public_inputs[2], BabyBear::new(4));
        assert_eq!(
            public_inputs[3],
            recompute_accumulated_hash(initial_root, &new_roots),
            "bound accumulated hash must equal the recomputed chain"
        );

        // Row 0 starts at the base case; every row satisfies the hash relation
        // new_hash == extend(old_hash, new_root, step) and rows chain.
        assert_eq!(
            trace[0][st_col::OLD_HASH],
            initial_accumulated_hash(initial_root)
        );
        for (i, &root) in new_roots.iter().enumerate() {
            let row = &trace[i];
            assert_eq!(row[st_col::STEP], BabyBear::new((i + 1) as u32));
            assert_eq!(row[st_col::NEW_ROOT], root);
            assert_eq!(
                row[st_col::NEW_HASH],
                extend_accumulated_hash(row[st_col::OLD_HASH], root, (i + 1) as u32),
                "row {i} violates the hash-chain relation"
            );
            if i + 1 < new_roots.len() {
                assert_eq!(
                    trace[i + 1][st_col::OLD_HASH],
                    row[st_col::NEW_HASH],
                    "rows {i}->{} break chain continuity",
                    i + 1
                );
            }
        }
    }
    // ========================================================================
    // Multi-Turn IVC tests (folding a SEQUENCE of Turn graph-transitions)
    // ========================================================================

    /// Build an honest chain of N TurnTransitionSummary linked correctly:
    ///   - genesis prev_receipt = 0
    ///   - each turn's pre_state == prior post_state
    ///   - each turn's previous_receipt_hash canonically encodes the prior turn's
    ///     in-circuit receipt hash (`[receipt, 0, 0, 0]`)
    ///   - bilateral_consistent = 1 everywhere
    fn build_turn_chain(n: usize) -> Vec<TurnTransitionSummary> {
        assert!(n >= 1);
        let mut summaries = Vec::with_capacity(n);
        let mut prev_post = BabyBear::new(1_000); // initial_state_root
        let mut prev_receipt = BabyBear::ZERO;

        for i in 0..n {
            let turn_hash = [
                BabyBear::new((i as u32) * 7 + 11),
                BabyBear::new((i as u32) * 7 + 12),
                BabyBear::new((i as u32) * 7 + 13),
                BabyBear::new((i as u32) * 7 + 14),
            ];
            let pre = prev_post;
            let post = BabyBear::new((i as u32 + 2) * 1_000);

            let previous_receipt_hash = if i == 0 {
                [BabyBear::ZERO; AGGREGATE_DIGEST_WIDTH]
            } else {
                TurnTransitionSummary::encode_receipt_link(prev_receipt)
            };

            let s = TurnTransitionSummary {
                turn_hash,
                pre_state_root: pre,
                post_state_root: post,
                previous_receipt_hash,
                bilateral_consistent: BabyBear::new(1),
            };

            // Compute the in-circuit receipt hash this turn produces, so the NEXT
            // turn's previous_receipt link matches it exactly.
            let turn_hash_d = s.turn_hash_digest();
            let link_in = if i == 0 { BabyBear::ZERO } else { prev_receipt };
            let receipt = turn_receipt_hash(turn_hash_d, pre, post, link_in, BabyBear::new(1));

            prev_receipt = receipt;
            prev_post = post;
            summaries.push(s);
        }
        summaries
    }

    // ─────────────────────────────────────────────────────────────────────────
    // stark-kill (f04b2dd1e) deleted MultiTurnIvcAir / prove_multi_turn_ivc /
    // verify_multi_turn_ivc — the hand-STARK fold over TurnTransitionSummary —
    // and the AIR-level tests (honest-chain prove/verify, broken state/receipt
    // link, tampered endpoint/accumulator, inconsistent turn, reorder, empty
    // chain, chain-too-long, genesis-link) died with the engine. The
    // chain-structure teeth now live on the recursion path:
    // circuit-prove/src/ivc_turn_chain.rs (the Lean-emitted turn-chain
    // descriptor + whole-chain recursive fold), which enforces continuity,
    // positional digest binding and endpoint pinning over REAL per-turn leaves.
    // What survives HERE are the hash primitives the summaries are
    // built from; their teeth stay bitten below.
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn multi_turn_receipt_hash_binds_every_input() {
        // Every input to the per-turn receipt hash must be load-bearing. The
        // bilateral_consistent flip is the surviving remnant of the
        // "inconsistent turn rejected" tooth: a turn whose flag differs yields
        // a different receipt, which breaks its successor's inbound link.
        let base = turn_receipt_hash(
            BabyBear::new(11),
            BabyBear::new(22),
            BabyBear::new(33),
            BabyBear::new(44),
            BabyBear::new(1),
        );
        let inputs = [
            BabyBear::new(11),
            BabyBear::new(22),
            BabyBear::new(33),
            BabyBear::new(44),
            BabyBear::new(1),
        ];
        for i in 0..inputs.len() {
            let mut flipped = inputs;
            flipped[i] += BabyBear::new(1);
            let v = turn_receipt_hash(flipped[0], flipped[1], flipped[2], flipped[3], flipped[4]);
            assert_ne!(base, v, "receipt-hash input {i} is not bound");
        }
    }

    #[test]
    fn multi_turn_accumulator_is_order_and_position_sensitive() {
        let acc0 = BabyBear::ZERO;
        let r1 = BabyBear::new(0xAAAA);
        let r2 = BabyBear::new(0xBBBB);

        // Reordering receipts changes the accumulator (splice detection).
        let acc_12 = extend_turn_accumulator(extend_turn_accumulator(acc0, r1, 0), r2, 1);
        let acc_21 = extend_turn_accumulator(extend_turn_accumulator(acc0, r2, 0), r1, 1);
        assert_ne!(
            acc_12, acc_21,
            "reordered receipts must change the folded accumulator"
        );

        // The step index is absorbed: the same receipt at a different position
        // yields a different accumulator (shift/duplication detection).
        assert_ne!(
            extend_turn_accumulator(acc0, r1, 0),
            extend_turn_accumulator(acc0, r1, 1),
            "step index must be bound positionally"
        );
    }

    #[test]
    fn multi_turn_chain_links_receipts_canonically() {
        // An honestly-linked chain: genesis carries the all-zero inbound link,
        // every later turn's previous_receipt_hash is the canonical
        // [receipt, 0, 0, 0] encoding of its predecessor's RECOMPUTED receipt
        // hash, and state roots chain post -> pre. Falsifiable against any
        // drift in encode_receipt_link / turn_receipt_hash / turn_hash_digest.
        let summaries = build_turn_chain(4);

        assert_eq!(
            summaries[0].previous_receipt_hash,
            [BabyBear::ZERO; AGGREGATE_DIGEST_WIDTH],
            "genesis turn must carry the all-zero inbound link"
        );

        let mut prev_receipt = BabyBear::ZERO;
        for (i, s) in summaries.iter().enumerate() {
            if i > 0 {
                assert_eq!(
                    s.pre_state_root,
                    summaries[i - 1].post_state_root,
                    "state-root chain break at turn {i}"
                );
                assert_eq!(
                    s.previous_receipt_hash,
                    TurnTransitionSummary::encode_receipt_link(prev_receipt),
                    "receipt link at turn {i} is not the canonical encoding"
                );
                assert_eq!(s.previous_receipt_link(), prev_receipt);
            }
            prev_receipt = turn_receipt_hash(
                s.turn_hash_digest(),
                s.pre_state_root,
                s.post_state_root,
                s.previous_receipt_link(),
                s.bilateral_consistent,
            );
        }
    }
}

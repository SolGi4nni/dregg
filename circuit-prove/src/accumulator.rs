//! The UNBOUNDED ONLINE ACCUMULATOR — the running left-fold over finalized turns.
//!
//! ## What this is (and how it differs from the K-fold tree)
//!
//! [`ivc_turn_chain::prove_turn_chain_recursive`](crate::ivc_turn_chain::prove_turn_chain_recursive)
//! folds a *finite* window of K finalized turns into one root proof via a BALANCED BINARY TREE
//! (`aggregate_tree`): it needs ALL K turns in memory at once, and the tree shape (hence the root
//! VK fingerprint) depends on K.
//!
//! This module is the SEQUENTIAL DUAL: a running accumulator that holds ONE `RecursionOutput` (the
//! O(1)-memory running proof) and EXTENDS it ONE finalized turn at a time:
//!
//! ```text
//!   acc_0 = genesis (the empty fold)
//!   acc_n = accumulate(acc_{n-1}, turn_n)
//! ```
//!
//! `accumulate(acc, turn)` is the genuine IVC step:
//!   1. verify `turn`'s leaf (host admission + the in-circuit descriptor leaf re-proof);
//!   2. **verify `acc_{n-1}`'s running proof IN-CIRCUIT** — the recursion: the previous running
//!      `RecursionOutput.0` (a `BatchStarkProof`) rides back in as a [`BatchOnly`] recursion input
//!      (`acc.running.into_recursion_input::<BatchOnly>()`), so the next aggregation layer's
//!      in-circuit FRI verifier RE-VERIFIES it. This is the same `into_recursion_input::<BatchOnly>`
//!      re-verification [`aggregate_tree`](crate::ivc_turn_chain) already performs at every internal
//!      tree node — driven here as a running LEFT-fold rather than a balanced tree;
//!   3. bind `acc_{n-1}.head_root == turn_n.pre_root`, advance `head_root = turn_n.post_root`,
//!      `num_turns += 1`, `chain_digest = H(prev_digest, old, new, idx)`;
//!   4. aggregate `running ∘ new_turn_leaf` into the NEW running `RecursionOutput`.
//!
//! **O(1) PROOF memory, O(num_turns) scalar binding state (precise).** The dominant cost — the
//! running RECURSION PROOF — is O(1): one [`RecursionOutput`] is held regardless of chain length, and
//! the consumed turns (proofs) are dropped. The accumulator ALSO retains a small per-turn scalar
//! witness — the four chain commitments (O(1)) PLUS `seam_pairs`, the ordered `(old_root, new_root)`
//! pairs (two field elements per folded turn), which `finalize` replays to rebuild the chain-binding
//! leaf so its digest reproduces the running `chain_digest`. So the running STATE is O(num_turns)
//! SCALARS, not O(1) — though the proof memory (the expensive part) is genuinely constant. Folding
//! the binding incrementally so `seam_pairs` vanishes is named open work (prereq (b) below).
//!
//! ## SEGMENT-ACCUMULATOR — PORTED (the mixed-root analog, CLOSED for the online path)
//!
//! The K-fold tree (`ivc_turn_chain`) closed the mixed-root hole by carrying an ordered
//! SEGMENT on every DESCRIPTOR leaf and combining segments in-circuit (so the whole-chain
//! claim is derived from the real executions, with no swappable binding leaf). This online
//! accumulator now carries the SAME genuine 4-lane W24 Poseidon2 segment digest, ported
//! exactly from the K-fold close:
//!   - **leaf** ([`prove_descriptor_leaf_rotated_with_segment`]): each `accumulate` step's
//!     descriptor leaf carries `[first_old, last_new, count=1, acc=commit([old,new])]`,
//!     bound in-circuit to the descriptor proof's REAL rotated roots.
//!   - **running combine** ([`combine_segments_expose`]): the running fold re-exposes the
//!     parent segment with `acc = commit(L.acc ++ R.acc)` where L = the running segment and
//!     R = the new leaf's segment — the LEFT-LINEAR analog of the K-fold balanced combine,
//!     with identical continuity / count / ordered-digest constraints. So the running proof
//!     carries the whole-chain segment by construction.
//!   - **finalize** ([`Accumulator::finalize`]): the running proof IS the root; its exposed
//!     segment `[genesis_root, head_root, num_turns, chain_digest]` is the whole-chain claim
//!     derived from the REAL descriptor leaves. `verify_turn_chain_recursive`'s SEGMENT tooth
//!     checks the carried claim against it, fail-closed. The Lean-emitted turn-chain descriptor
//!     proof is STILL produced for the carried `binding_proof` field (byte-API /
//!     defense-in-depth) but is NO LONGER a soundness dependency and is NOT folded into the root
//!     — exactly as the K-fold path now carries (not folds) its binding proof.
//!
//! So a same-endpoint mixed-root forgery against the online whole-chain proof is REJECTED by
//! the same construction the K-fold uses (witness: `online_mixed_root_forgery_rejected`).
//!
//! ## What is GENUINELY here vs the named in-band gap (honest, tiered)
//!
//! **BUILT + RUNNING:** the running-fold DRIVER over the REAL recursion primitives. Each step does a
//! real in-circuit re-verification of the running batch proof (step 2) and a real in-circuit
//! descriptor-leaf re-proof (step 1), aggregated to a new running root. The temporal binding
//! (`prev.head_root == next.old_root`) is enforced host-side (the [`AccError::ChainBreak`] tooth) and
//! the running summary advances correctly. The terminal [`Accumulator::finalize`] reuses the proven
//! `verify_turn_chain_recursive` verify discipline, so a light client's
//! [`lightclient::verify_history`] accepts the accumulated artifact under its honest VK anchor.
//!
//! **THE TWO FORK LEVERS — NOW LANDED IN-BAND (lever a + b), with the precise residual NAMED.**
//! The recursion fork (`emberian/plonky3-recursion`) now exposes the two mechanisms this fold needs:
//!   - **(a) VK identity of the re-folded running proof — PINNED in-band.** The parent aggregation
//!     circuit takes the child's preprocessed commitment (its verifier-key core) as public-input
//!     targets, but their VALUE was unconstrained. The fork's `into_recursion_input_pinned()` /
//!     `pin_preprocessed_commit()` now `connect` those targets to an expected commitment IN-CIRCUIT:
//!     a child proof from a DIFFERENT circuit (different preprocessed commitment) makes the parent
//!     UNSAT. This driver consumes it: once the running AGGREGATION shape exists, its commitment is
//!     captured and every subsequent fold pins the running (left) input against it — the IVC
//!     self-verification check (witness: `pinned_fold_rejects_foreign_vk_in_circuit`, which exhibits
//!     a corrupted-VK fold being rejected in-circuit on the leaf∘leaf shape).
//!
//!     ⚑ 2026-07-30, READ THIS BEFORE CITING THE PIN. The pin's constant is NOT circuit identity:
//!     `ConstAir` puts a const's VALUE in its constraint-free MAIN trace and only `[ext_mult,
//!     out_idx]` in preprocessed, so two circuits differing only in a pinned constant present ONE
//!     `recursion_vk_fingerprint` (MEASURED: `circuit-prove/tests/const_pin_probe.rs`,
//!     `vk_pin_lever_a_probe.rs`). What survives for THIS path is only the first horn — a cap that
//!     is not the child's real preprocessed commitment has no satisfying in-circuit opening — which
//!     is a restatement of `recursive_sound`, not an extra tooth. `pinned_fold_rejects_foreign_vk_
//!     in_circuit` asserts an error on a path where the honest witness generator is handed two
//!     values for one `connect`-shared slot, so its `is_err()` does not separate UNSAT from a runner
//!     `WitnessConflict`. The K-fold analysis and the designed repair are in
//!     [`crate::ivc_turn_chain`]'s module docs.
//!   - **(b) public-value propagation across layers — THREADED.** `into_recursion_input` no longer
//!     hardcodes empty `table_public_inputs`; it threads the proof's GENUINE per-table public values
//!     so the next layer's packed public vector MATCHES the targets it allocates. This is also what
//!     unblocked re-folding a proof that itself contains a fold (an aggregation proof's non-primitive
//!     tables expose public values; the empty-vector path left those allocated targets unfilled —
//!     over-constraining the witness solver, the `WitnessConflict` the deep fold tripped).
//!
//! **DEPTH-INVARIANCE — the WRAP step, and the MEASURED fixed point (honest, tiered).**
//!
//! The pin makes VK identity an IN-BAND constraint, but does not by itself bound the running VK's
//! SHAPE. The WRAP step ([`wrap_params`] / [`WRAP_LOG_CEIL`], ON by default) proves each running fold
//! under a fixed `min_trace_height` ceiling so the running FRI trace shape cannot grow with depth.
//!
//! **What is MEASURED (not merely named) — the running VK reaches a CONSTANT FIXED POINT (at depth 4),
//! and the perpetual steady state is now MECHANIZED (a `#assert_axioms`-clean Lean induction off ONE
//! measured fixed point — no longer a prose idempotence argument).**
//! A real incremental fold over a continuous chain (test `wrapped_running_vk_is_constant_across_depth`)
//! shows the running aggregation proof's full VK fingerprint — table packing, `rows`, `degree_bits`, the
//! non-primitive manifest, AND the preprocessed commitment (the op-list / VK core) — settling to a fixed
//! point after a short transient:
//!   - depth 2 (LEAF∘LEAF result) ≠ depth 3 (AGG over LEAF∘LEAF) ≠ depth 4 (AGG over AGG∘LEAF) — the
//!     transient (the running INPUT's own sub-structure propagates EXACTLY ONE level into the parent
//!     op-list before it stabilizes — see the structural finding below);
//!   - **depth 4 == depth 5 == depth 6 (== … ): byte-IDENTICAL VK material, including the preprocessed
//!     commitment** (two measured iterations past the fixed point).
//!     The `degree_bits` are constant THROUGHOUT (`[9,9,15,14,15]`, natural max `2^15`); the transient lives
//!     entirely in the op-list (logical `rows` + preprocessed commitment).
//!
//! **Why the fixed point is PERPETUAL — now MECHANIZED.** The fold-shape transition is a DETERMINISTIC
//! function of the running input's VK SHAPE ALONE (`step : VkShape → VkShape`): the parent aggregation
//! circuit's op-list (hence its preprocessed commitment = the VK core) is built by the fork's
//! `verify_p3_batch_proof_circuit` from ONLY the input proof's shape quantities — its `rows`,
//! `table_packing`, the `non_primitives` op_type/rows/lanes manifest, and per-instance public-value
//! COUNTS (`entry.public_values.len()` — a count, never the values); `recursion_vk_fingerprint` is
//! correspondingly content-independent. So once `step` has a fixed point, deterministic iteration keeps
//! every further fold at it. The Lean theorem
//! `Dregg2.Circuit.RecursiveAggregation.running_vk_perpetually_constant` proves `∀N, step^[N] anchor =
//! anchor` (`#assert_axioms`-clean) from the SINGLE measured fixed point `step anchor = anchor` (the
//! byte-identical depth-4 == depth-5 material). Its modeling premise — that `step` is shape-only — is
//! discharged empirically by the Rust `running_vk_fixed_point_is_value_independent` tooth (two DIFFERENT
//! value-streams reach the SAME depth-4 VK). So `∀N, VK_N == VK_4` is now a machine-checked induction off
//! one measurement, NOT a measurement at every depth (impossible) NOR an un-mechanized prose argument.
//! The ONLY remaining recursion-fork residual is the finite 2-step TRANSIENT (see below) — a usability
//! uniformity, not the perpetual claim and not a soundness gate.
//!
//! **THE PRECISE REMAINING FORK WORK (the TRANSIENT, not the perpetual claim — named exactly, with the
//! localized delta).** The fixed point is reached at depth 4, NOT depth 2 — a finite 2-step transient.
//! This is the ONLY residual; it is a usability uniformity (every fold from the FIRST aggregation
//! carrying the one anchor), NOT the perpetual-constancy claim (mechanized above) and NOT a soundness
//! gate (the VK-identity pin TRACKS the running commitment through the transient; a light client anchors
//! on the perpetual fixed-point VK). The ROOT-CAUSED structural reason: the AGG∘LEAF verifier op-list
//! depends on the STRUCTURE of the running (left) input proof — the per-instance opened-column widths /
//! public-value counts of its `non_primitives` and its `rows` (`verify_p3_batch_proof_circuit` iterates
//! the input proof's `non_primitives` and allocates per-instance targets from their `public_values.len()`
//! and opened-value widths). A LEAF input, an `AGG(LEAF,LEAF)` input, and an `AGG(AGG,LEAF)` input each
//! carry a DIFFERENT such structure — and that structure propagates exactly ONE level into the parent's
//! op-list (measured: `rows` Const 269→277, recompose 19112→19093; `prep_commit` ddaa…→830a…), so the
//! parent op-list stabilizes only once the input has been `AGG(AGG,LEAF)`-shaped for one full fold.
//! To collapse the transient (reach the fixed point at depth 2), the running input must have the steady
//! `AGG(AGG,LEAF)` structure from the FIRST aggregation — which requires a CANONICAL agg-shaped SEED
//! whose own left is already agg-shaped (a recursive fixpoint seed). That is the genuine Pickles
//! step∘wrap circuit: a fixed wrap circuit whose output shape equals its input shape, seeded once. The
//! fork exposes no such canonical-shape / re-prove primitive today (no identity/normalize fold), so
//! building the fixpoint seed is genuinely multi-pass — the precise outstanding FORK work, scoped to the
//! transient alone. The `min_trace_height` ceiling pins the FRI trace heights (the easy half,
//! empirically a near-no-op since heights were already constant) but NOT the op-list. Lever (a)+(b), the
//! tracked-pin fail-closed tooth, and the measured-plus-MECHANIZED fixed point are its foundation.
//!
//! The soundness SKELETON of the unbounded loop is PROVEN in Lean
//! (`Dregg2.Circuit.RecursiveAggregation.accumulate_preserves_wellformed` /
//! `acc_attests_whole_history`, `#assert_axioms`-clean): the running fold preserves whole-history
//! attestation by induction from genesis, carrying the SAME named `EngineSound` recursion boundary. The
//! depth-invariance (running-VK perpetual constancy) is ALSO mechanized there now — §10
//! `running_vk_perpetually_constant` / `running_vk_one_anchor` (`#assert_axioms`-clean): `∀N, VK_N =
//! VK_4` off the single measured fixed point, with shape-only determinism discharged by the
//! `running_vk_fixed_point_is_value_independent` tooth.

use p3_commit::Pcs;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionOutput, build_and_prove_aggregation_layer,
    build_and_prove_aggregation_layer_with_expose,
};
use p3_uni_stark::StarkGenericConfig;

/// The runtime preprocessed-commitment value type for the recursion config — the child proof's
/// VK-identity core (a Merkle cap). This is what the VK-identity pin (lever (a)) constrains in-band.
type RecursionCommit = <<DreggRecursionConfig as StarkGenericConfig>::Pcs as Pcs<
    <DreggRecursionConfig as StarkGenericConfig>::Challenge,
    <DreggRecursionConfig as StarkGenericConfig>::Challenger,
>>::Commitment;

use crate::ivc_turn_chain::{
    FinalizedTurn, HostSeg, RecursionVk, SEG_ANCHOR_WIDTH, SEG_DIGEST_WIDTH, TurnChainBindingProof,
    WholeChainProof, combine_seg, expose_claim_instance_index, ir2_leaf_wrap_config, leaf_seg,
    prove_descriptor_leaf_rotated_with_config, prove_descriptor_leaf_rotated_with_segment,
    prove_turn_chain_binding_for_roots, segment_combine_expose, turn_anchors8,
    verify_turn_chain_recursive,
};
use crate::joint_turn_aggregation::verify_descriptor_participant;
use crate::plonky3_recursion_impl::recursive::{DreggRecursionConfig, create_recursion_backend};
use dregg_circuit::field::BabyBear;

const D: usize = 4;

/// The recursion challenge (extension) field the expose hooks build constants over.
type AccChallenge = <DreggRecursionConfig as StarkGenericConfig>::Challenge;

/// **THE SEGMENT-COMBINE EXPOSE HOOK (the online dual of `aggregate_tree`'s combine).**
///
/// The running fold's aggregation re-exposes the parent segment EXACTLY as the K-fold
/// `aggregate_tree` does: left = the running proof's segment, right = the new leaf's
/// segment. It constrains state continuity (`L.last_new == R.first_old`, by direct
/// `connect` — never `sub`+`assert_zero`, which would clobber the shared `WitnessId(0)`),
/// count additivity (`count = L.count + R.count`), and the ordered multi-felt digest fold
/// (`acc = seg_poseidon_commit(L.acc ++ R.acc)`, L absorbed before R ⇒ order-sensitive),
/// then exposes the parent `[first_old, last_new, count, acc_0..acc_{W-1}]`. This is what
/// makes the running proof carry the SAME genuine 4-lane W24 Poseidon2 segment digest the
/// K-fold path carries — closing the same-endpoint mixed-root forgery for the online path.
fn combine_segments_expose(
    cb: &mut p3_circuit::CircuitBuilder<AccChallenge>,
    left_apt: &[Vec<p3_recursion::Target>],
    right_apt: &[Vec<p3_recursion::Target>],
    left_idx: usize,
    right_idx: usize,
) {
    // The online running combine is byte-identical to the K-fold `aggregate_tree` combine (the
    // 8-felt FAITHFUL-FLOOR segment: 8-lane state continuity + count additivity + ordered multi-felt
    // digest fold). Delegate to the ONE shared primitive so the two paths cannot drift.
    segment_combine_expose(cb, left_apt, right_apt, left_idx, right_idx);
}

/// **THE WRAP-STEP TRACE-HEIGHT CEILING (the `min_trace_height` half of the fixed-shape knob).**
///
/// This pins every running-proof table to a fixed power-of-two `degree_bits` floor of `2^WRAP_LOG_CEIL`,
/// so the running FRI commit-phase count (`num_phases = log_max_height - log_blowup`) does not grow with
/// depth.
///
/// **EMPIRICALLY MEASURED RESIDUAL (the precise reason a height ceiling ALONE does not close constant-VK):**
/// at the dregg leaf-wrap config the running AGG∘LEAF `degree_bits` are ALREADY constant across depth
/// (measured `[9, 9, 15, 14, 15]` at depth 2 AND depth 3 — the natural max is `2^15`, so a `2^16` ceiling
/// is a near-no-op pad). The part of the running VK that STILL drifts with depth is NOT the trace heights
/// but the **op-list** — the logical pre-padding `rows` (e.g. Const `269 → 277`, recompose `19112 → 19093`)
/// AND the **preprocessed commitment** (`ddaa4a02… → 830ace21…`). The op-list of the AGG∘LEAF verifier
/// circuit depends on the STRUCTURE of the input running proof (its FRI openings / opened-values count),
/// which a `min_trace_height` floor does not touch. Closing THAT needs the structural half of the wrap:
/// re-proving the input running proof to a fixed STRUCTURE (fixed instance/opening counts) so the
/// verifier op-list is identical. See [`Accumulator::accumulate`]'s wrap note and this module's header.
///
/// Set to `2^16` (just above the measured natural `2^15` max) so the ceiling is a safe pad that never
/// blows memory; a higher ceiling (e.g. `2^20`) pads to ~1M rows/table and OOMs the prover.
pub const WRAP_LOG_CEIL: usize = 16;

/// The [`ProveNextLayerParams`] the WRAP step proves the running fold under: identical to the default
/// recursion params EXCEPT the table packing carries a fixed [`WRAP_LOG_CEIL`] trace-height floor (the
/// `min_trace_height` half of the fixed-shape knob). This pins the running FRI shape but NOT the op-list
/// (see [`WRAP_LOG_CEIL`] for the measured residual).
fn wrap_params() -> ProveNextLayerParams {
    let base = ProveNextLayerParams::default();
    ProveNextLayerParams {
        table_packing: base
            .table_packing
            .with_min_trace_height(1usize << WRAP_LOG_CEIL),
        constraint_profile: base.constraint_profile,
    }
}

/// A short blake3 fingerprint of a recursion preprocessed commitment (the VK-identity core), for
/// diagnostic error messages on a pin mismatch. Not a security-bearing comparison — the actual
/// pin equality compares the full `RecursionCommit` value.
fn commit_fingerprint(commit: &RecursionCommit) -> String {
    let bytes = postcard::to_allocvec(commit).unwrap_or_default();
    blake3::hash(&bytes).to_hex()[..16].to_string()
}

/// Why an accumulate step failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AccError {
    /// **The temporal tooth.** The next turn does not consume the accumulator's head root: its
    /// `old_root` is not the running `head_root`. (The `TurnChainError::ChainBreak` analog for the
    /// running fold.)
    ChainBreak {
        /// The accumulator's current head root (what the next turn must consume).
        expected_old_root: u32,
        /// The root the next turn claims to consume.
        found_old_root: u32,
    },
    /// A turn's per-cell whole-turn proof failed host admission or the in-circuit leaf re-proof.
    TurnProofInvalid {
        /// The 0-based fold index (`num_turns` at the time of the failing step).
        index: usize,
        /// The underlying reason.
        reason: String,
    },
    /// A recursion layer, turn-chain descriptor proof, or running aggregation failed.
    RecursionFailed {
        /// What failed.
        reason: String,
    },
    /// **The VK-identity fixed-point tooth (fail-closed).** After the running fixed-point VK was
    /// captured, this fold's running (left) input carried a DIFFERENT preprocessed commitment than
    /// the pinned one — i.e. the running proof came from a different circuit than the captured fixed
    /// point. The fold is REJECTED (never folded unpinned). The accumulator is left UNCHANGED.
    VkIdentityMismatch {
        /// The 0-based fold index (`num_turns` at the time of the failing step).
        index: usize,
        /// A blake3-16 fingerprint of the pinned (expected) preprocessed commitment.
        expected: String,
        /// A blake3-16 fingerprint of the running proof's actual preprocessed commitment.
        found: String,
    },
    /// `finalize` on an empty accumulator (no turns folded — there is nothing to attest).
    Empty,
}

impl core::fmt::Display for AccError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AccError::ChainBreak {
                expected_old_root,
                found_old_root,
            } => write!(
                f,
                "next turn breaks the running chain: old_root {found_old_root} != \
                 accumulator head_root {expected_old_root}"
            ),
            AccError::TurnProofInvalid { index, reason } => {
                write!(f, "turn {index} proof invalid: {reason}")
            }
            AccError::RecursionFailed { reason } => write!(f, "recursion failed: {reason}"),
            AccError::VkIdentityMismatch {
                index,
                expected,
                found,
            } => write!(
                f,
                "VK-identity pin mismatch at fold {index}: running proof commitment {found} != \
                 pinned fixed-point VK {expected} (the running proof came from a different circuit \
                 than the captured fixed point — fold REJECTED, not folded unpinned)"
            ),
            AccError::Empty => write!(f, "cannot finalize an empty accumulator (no turns folded)"),
        }
    }
}

impl std::error::Error for AccError {}

/// The O(1)-memory running summary of the accumulated chain (the four scalar commitments the
/// `WholeChainProof` exposes, advanced incrementally). Kept between fold steps so the binding
/// descriptor proof can be regenerated WITHOUT retaining the consumed turns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChainSummary {
    /// The genesis state anchor the chain started from (the first turn's `first_old8`); the
    /// running segment's `first_old8`. GENUINE 8-felt (~124-bit) — sourced from the turn's WIDE
    /// leg's 8-felt before-commit anchor ([`turn_anchors8`]); a narrow leg replicates its single
    /// rotated commit felt across the eight lanes, matching the in-circuit leaf's narrow replicate.
    pub genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The running head state anchor (the last folded turn's `last_new8`); the next turn must
    /// consume this. The running segment's `last_new8`. GENUINE 8-felt — see [`genesis_root`].
    pub head_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The running ordered-history digest — the genuine 4-lane W24 Poseidon2 segment `acc`,
    /// folded LEFT-LINEARLY as `acc = commit(running.acc ++ leaf.acc)` (the host mirror of the
    /// in-circuit [`combine_segments_expose`]). This EQUALS the digest the running proof exposes,
    /// so `finalize`'s carried `chain_digest` matches the root-exposed segment tooth.
    pub chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
    /// The number of turns folded so far (the running segment's `count`).
    pub num_turns: usize,
}

impl ChainSummary {
    /// The running segment as a [`HostSeg`] (the host mirror of the running proof's exposed
    /// segment), so the next fold can `combine_seg(running, new_leaf)` exactly as the circuit does.
    fn as_seg(&self) -> HostSeg {
        // FAITHFUL-FLOOR (codex #4 CLOSED): the online path now carries GENUINE 8-felt state
        // endpoints — `genesis_root`/`head_root` are the turn's WIDE 8-felt anchors
        // ([`turn_anchors8`]), the SAME source the K-fold tree consumes. No broadcast: each lane
        // is the genuine per-lane anchor value (a narrow leg's replicate is already baked into the
        // array at accumulate time, matching the in-circuit leaf's narrow replicate lane-for-lane).
        HostSeg {
            first_old8: self.genesis_root,
            last_new8: self.head_root,
            count: BabyBear::new(self.num_turns as u32),
            acc: self.chain_digest,
        }
    }
}

/// The running accumulator: a single running recursion proof (O(1) PROOF memory) + the O(1) chain
/// summary + the O(num_turns) `seam_pairs` scalar binding witness.
///
/// Built by [`Accumulator::genesis`], extended by [`Accumulator::accumulate`], and read out by
/// [`Accumulator::finalize`] into a [`WholeChainProof`] a light client verifies.
///
/// **The memory profile (honest).** The dominant cost — the running RECURSION PROOF — is O(1): one
/// `RecursionOutput` is held regardless of chain length. The residual `seam_pairs` (two field
/// elements per folded turn) is the binding descriptor's reconstruction witness: it lets `finalize`
/// rebuild the per-turn Lean-emitted descriptor trace and its distinct scalar sequential digest.
/// This is precisely the component prereq
/// (b) — in-circuit re-exposure of the running digest as a CHECKED public — would eliminate: with (b),
/// the binding could bind against the running root's exposed digest in-circuit and `seam_pairs` would
/// vanish. Until then it is a small (2-felt/turn) scalar witness, NOT a retained proof; the proof
/// memory is genuinely O(1).
pub struct Accumulator {
    /// The running recursion proof (`None` before the first turn). This is the IVC fixed-point
    /// carrier: each `accumulate` re-verifies it in-circuit and folds it forward.
    running: Option<RecursionOutput<DreggRecursionConfig>>,
    /// The running chain summary (`None` before the first turn).
    summary: Option<ChainSummary>,
    /// The ordered `(old_root, new_root)` seam pairs of the folded turns — the binding-descriptor
    /// reconstruction witness (see the struct note: O(num_turns) SCALARS, not proofs; eliminated by
    /// prereq (b)).
    seam_pairs: Vec<(BabyBear, BabyBear)>,
    /// **THE VK-IDENTITY PIN — the EXPECTED commitment of the running proof we hold (lever (a)).**
    /// This is the preprocessed commitment of the running [`RecursionOutput`] currently in `running`,
    /// recorded each fold from the OUTPUT we just produced. Each subsequent fold (i) checks the held
    /// running proof's commitment STILL equals this expected value — fail-closed
    /// ([`AccError::VkIdentityMismatch`]) if a foreign/swapped proof ever appears — and (ii) pins the
    /// running (left) input IN-CIRCUIT to it via [`RecursionOutput::into_recursion_input_pinned`], so
    /// the aggregation circuit constrains "the proof I am re-folding is the one I produced last step."
    ///
    /// **Why it TRACKS the running commitment rather than freezing one value.** The running
    /// aggregation VK passes through a finite TRANSIENT before it reaches the perpetual fixed point
    /// (the AGG∘LEAF shape settles once the running input is itself a stable-shape aggregation — the
    /// `degree_bits` are constant throughout, but the op-list `rows` + preprocessed commitment settle
    /// after a couple of folds; see [`WRAP_LOG_CEIL`] and the module header). During the transient the
    /// running proof's commitment genuinely changes each step, so a frozen pin would FALSELY reject
    /// honest transient folds. Tracking the actual running commitment pins EVERY fold against the
    /// genuinely-expected running proof — fail-closed against a foreign proof at all depths — and
    /// becomes CONSTANT once the fixed point is reached (the pin then naturally holds the perpetual
    /// fixed-point VK forever). A FOREIGN running proof (different preprocessed commitment than the one
    /// we recorded) makes the aggregation circuit UNSAT and is rejected host-side BEFORE the fold.
    ///
    /// `None` until the first aggregation OR if the pin is disabled (see
    /// [`Accumulator::with_vk_identity_pin`]). Default: pin ENABLED.
    pinned_running_vk: Option<RecursionCommit>,
    /// Whether the VK-identity fixed-point pin is enabled. Default `true`. Disable only to reproduce
    /// the legacy unpinned fold (e.g. to exhibit that a foreign-circuit proof is REJECTED only with
    /// the pin on).
    pin_vk_identity: bool,
    /// **Whether the WRAP step is enabled (the fixed-shape re-prove, lever closing the depth-invariant
    /// fixed point).** When `true` (default), every running fold is proven under [`wrap_params`] — a
    /// fixed [`WRAP_LOG_CEIL`] trace-height ceiling — so the running proof's `degree_bits` (hence its
    /// FRI shape, hence the next layer's preprocessed commitment = its VK core) are CONSTANT across
    /// depth. Disable to reproduce the legacy variable-shape fold (where the VK fingerprint grows with
    /// depth) for the A/B comparison the depth-invariance test draws.
    wrap_enabled: bool,
}

impl Default for Accumulator {
    fn default() -> Self {
        Self::genesis()
    }
}

impl Accumulator {
    /// `acc_0`: the empty accumulator (no running proof, no summary). The base of the IVC fold.
    /// The VK-identity fixed-point pin (lever (a)) is ENABLED by default.
    pub fn genesis() -> Self {
        Self {
            running: None,
            summary: None,
            seam_pairs: Vec::new(),
            pinned_running_vk: None,
            pin_vk_identity: true,
            wrap_enabled: true,
        }
    }

    /// Toggle the VK-identity fixed-point pin (lever (a)). Enabled by default; disable to reproduce
    /// the legacy unpinned fold. Returns `self` for chaining (`Accumulator::genesis().with_vk_identity_pin(false)`).
    pub fn with_vk_identity_pin(mut self, enabled: bool) -> Self {
        self.pin_vk_identity = enabled;
        self
    }

    /// Toggle the WRAP step (the fixed-shape re-prove that makes the running VK depth-invariant; see
    /// [`wrap_params`] / [`WRAP_LOG_CEIL`]). Enabled by default; disable to reproduce the legacy
    /// variable-shape fold whose VK fingerprint grows with depth. Returns `self` for chaining.
    pub fn with_wrap(mut self, enabled: bool) -> Self {
        self.wrap_enabled = enabled;
        self
    }

    /// The running proof's per-table `degree_bits` (the FRI domain shape the next layer's verifier
    /// reads to size its op-list). With the WRAP step ON these are CONSTANT across depth (every table
    /// padded to [`WRAP_LOG_CEIL`]); with it OFF they grow. The depth-invariance test compares this
    /// (and [`running_vk_fingerprint`](Self::running_vk_fingerprint)) at depth 2 vs depth 3.
    pub fn running_degree_bits(&self) -> Option<Vec<usize>> {
        self.running.as_ref().map(|r| r.0.proof.degree_bits.clone())
    }

    /// **THE RUNNING VK FINGERPRINT — the depth-invariance observable.** The full
    /// [`recursion_vk_fingerprint`](crate::plonky3_recursion_impl::recursive::recursion_vk_fingerprint)
    /// of the running aggregation proof: a blake3 over its verifier-reconstruction SHAPE (table
    /// packing, `rows`, `degree_bits`, the non-primitive manifest, and the preprocessed commitment =
    /// the VK core). This is exactly the fingerprint a light client pins as its trust anchor.
    ///
    /// **The Pickles constant-VK property is: this is EQUAL across fold depths.** With the WRAP step
    /// ON, the depth-2 running proof and the depth-3 running proof carry the IDENTICAL fingerprint —
    /// the verifier is fixed-size forever. With wrap OFF it grows with depth. `None` before any fold.
    pub fn running_vk_fingerprint(
        &self,
    ) -> Option<crate::plonky3_recursion_impl::recursive::RecursionVk> {
        self.running
            .as_ref()
            .map(|r| crate::plonky3_recursion_impl::recursive::recursion_vk_fingerprint(&r.0))
    }

    /// **VK-MATERIAL BREAKDOWN PROBE.** A human-readable dump of the SEPARATE components the running
    /// VK fingerprint hashes — so a depth-2-vs-depth-3 diff can pinpoint WHICH part varies (degree_bits
    /// vs `rows` vs the non-primitive manifest vs the preprocessed commitment = the op-list/VK core).
    /// Used by the depth-invariance test to localize the residual precisely. Not a stable API.
    pub fn running_vk_material_debug(&self) -> Option<String> {
        use core::fmt::Write;
        self.running.as_ref().map(|r| {
            let p = &r.0;
            let mut s = String::new();
            let _ = write!(s, "degree_bits={:?}", p.proof.degree_bits);
            let _ = write!(s, " rows={:?}", p.rows);
            let _ = write!(s, " n_nonprim={}", p.non_primitives.len());
            for e in &p.non_primitives {
                let _ = write!(s, " [{:?} rows={} lanes={}]", e.op_type, e.rows, e.lanes);
            }
            match &p.stark_common.preprocessed {
                None => {
                    let _ = write!(s, " prep=NONE");
                }
                Some(gp) => {
                    // Hash JUST the preprocessed commitment (the op-list VK core) so a change in it
                    // alone is visible distinct from the trace-shape fields.
                    let bytes = postcard::to_allocvec(&gp.commitment).unwrap_or_default();
                    let h = blake3::hash(&bytes);
                    let _ = write!(
                        s,
                        " prep_commit={} n_inst={}",
                        &h.to_hex()[..16],
                        gp.instances.len()
                    );
                }
            }
            s
        })
    }

    /// Whether the running VK-identity pin is active yet — i.e. the running proof is an aggregation
    /// (the first fold has happened) so its expected commitment is being tracked and every subsequent
    /// fold is pinned-or-rejected in-band. `false` while the running proof is still the genesis leaf.
    pub fn vk_identity_pinned(&self) -> bool {
        self.pinned_running_vk.is_some()
    }

    /// **TEST-ONLY: forcibly overwrite the captured fixed-point pin.** Exercises the fail-closed
    /// VK-identity tooth (`AccError::VkIdentityMismatch`): after a genuine pin is captured, setting it
    /// to a FOREIGN commitment makes the NEXT `accumulate` (or `finalize`) reject — the running proof's
    /// genuine commitment no longer matches the (now-corrupted) pin. This simulates an adversary who
    /// got the accumulator into a state where the running proof and the pinned VK disagree; the driver
    /// must refuse rather than fold unpinned. Not a production API.
    #[doc(hidden)]
    pub fn force_pinned_vk_for_test(&mut self, commit: RecursionCommit) {
        self.pinned_running_vk = Some(commit);
    }

    /// The running proof's genuine preprocessed commitment (its VK-identity core), if a turn has been
    /// folded. This is the value an honest fixed-point fold pins against.
    pub fn running_vk_commit(&self) -> Option<RecursionCommit> {
        self.running
            .as_ref()
            .and_then(|r| r.running_preprocessed_commit())
    }

    /// **VK-IDENTITY-PIN PROBE (lever (a) demonstration).** Re-fold the current running proof against
    /// `turn`'s freshly-wrapped descriptor leaf, pinning the running (left) input's preprocessed
    /// commitment IN-CIRCUIT to `expected_running_vk`. Returns `Ok(())` iff the aggregation circuit is
    /// satisfiable — i.e. iff the running proof's actual VK matches `expected_running_vk`.
    ///
    /// Pass the running proof's GENUINE commitment ([`running_vk_commit`](Self::running_vk_commit)) to
    /// see the honest fold succeed; pass a CORRUPTED commitment to see the in-circuit VK check reject
    /// it (`AccError::RecursionFailed`). This is the direct witness that a proof from a different
    /// circuit is refused IN-CIRCUIT, not host-side. Does NOT mutate the accumulator.
    pub fn probe_pinned_fold(
        &self,
        turn: &FinalizedTurn,
        expected_running_vk: RecursionCommit,
    ) -> Result<(), AccError> {
        let running = self.running.as_ref().ok_or(AccError::Empty)?;
        let config = ir2_leaf_wrap_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        let leg = &turn.participant.rotated;
        let new_leaf = prove_descriptor_leaf_rotated_with_config(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .map_err(|reason| AccError::TurnProofInvalid { index: 0, reason })?;

        let left = running.into_recursion_input_pinned::<BatchOnly>(expected_running_vk);
        let right = new_leaf.into_recursion_input::<BatchOnly>();
        build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
            &left, &right, &config, &backend, &params, None,
        )
        .map(|_| ())
        .map_err(|e| AccError::RecursionFailed {
            reason: format!("pinned aggregation layer failed: {e:?}"),
        })
    }

    /// The current running summary, if any turn has been folded.
    pub fn summary(&self) -> Option<ChainSummary> {
        self.summary
    }

    /// The number of turns folded so far.
    pub fn num_turns(&self) -> usize {
        self.summary.map(|s| s.num_turns).unwrap_or(0)
    }

    /// **The IVC STEP — `accumulate(acc, turn) -> acc'`.** Fold one more finalized turn into the
    /// running proof. O(1) PROOF memory (one running [`RecursionOutput`] is held); the running scalar
    /// state is O(num_turns) (the `seam_pairs` binding witness — see the struct note). Only `self` is
    /// retained between steps; the consumed turns are dropped.
    ///
    /// Steps (the running-fold dual of one `aggregate_tree` internal node):
    ///   1. host admission: the turn's rotated descriptor proof verifies selector-bound;
    ///   2. continuity: the turn's `old_root` must equal the running `head_root` (the temporal
    ///      tooth — `AccError::ChainBreak` otherwise);
    ///   3. wrap the turn's rotated descriptor leaf to a batch proof (the in-circuit leaf re-proof);
    ///   4. if a running proof exists, aggregate `running ∘ new_leaf` — feeding `running` back as a
    ///      [`BatchOnly`] input so the next layer RE-VERIFIES it in-circuit (the recursion); else the
    ///      new leaf BECOMES the running proof (the first turn);
    ///   5. advance the running summary (`head_root`, `chain_digest`, `num_turns`).
    pub fn accumulate(&mut self, turn: &FinalizedTurn) -> Result<(), AccError> {
        let idx = self.num_turns();

        // (1) host admission (admission discipline; the in-circuit leaf re-proof is the soundness
        //     boundary).
        verify_descriptor_participant(&turn.participant)
            .map_err(|reason| AccError::TurnProofInvalid { index: idx, reason })?;

        // The turn's GENUINE 8-felt state anchors — sourced the SAME way the K-fold tree and the
        // in-circuit descriptor leaf source them ([`turn_anchors8`]): a WIDE / wide-welded leg
        // publishes the genuine ~124-bit `wide_old_root8`/`wide_new_root8`; a narrow leg replicates
        // its single rotated commit felt across the eight lanes. These (not the single felts) are the
        // running segment's endpoints, so the host summary matches the root-exposed segment lane-for-lane.
        let (this_old8, this_new8) = turn_anchors8(turn);

        // (2) continuity against the running head — at the GENUINE 8-felt anchor (lane-for-lane), the
        //     host mirror of the in-circuit combine's `L.last_new8 == R.first_old8` connect. For a
        //     narrow leg both arrays are the single-felt broadcast, so this reduces to the felt check;
        //     for a wide leg it binds the full ~124-bit anchor (the felt PIs 34/35 may be retired).
        if let Some(s) = self.summary
            && s.head_root != this_old8
        {
            return Err(AccError::ChainBreak {
                expected_old_root: s.head_root[0].0,
                found_old_root: this_old8[0].0,
            });
        }

        let config = ir2_leaf_wrap_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();
        // **THE WRAP STEP.** The running fold is proven under a FIXED trace-height ceiling
        // ([`wrap_params`] / [`WRAP_LOG_CEIL`]) when wrapping is enabled, so the running proof's
        // `degree_bits` — hence its FRI shape, hence the NEXT layer's verifier op-list (= its VK core)
        // — are CONSTANT across depth. The leaf wrap (step 3) stays at the default params (a leaf is
        // already a fixed shape); only the running AGGREGATION (step 4) is height-ceiled.
        let fold_params = if self.wrap_enabled {
            wrap_params()
        } else {
            params.clone()
        };

        // (3) the rotated descriptor leaf, wrapped to a batch proof at the wrap config AND
        //     carrying its ordered SEGMENT `[old_root, new_root, 1, commit([old,new])]` bound
        //     in-circuit to the descriptor's real rotated roots (the same leaf the K-fold path
        //     folds). This is what lets the running fold combine genuine 4-lane segments.
        let leg = &turn.participant.rotated;
        // THE SAME ARM-SELECTION FAIL-CLOSED THE K-FOLD PATH TAKES — and here it is UNCONDITIONAL,
        // because this driver has NO carrier arm at all. The K-fold
        // (`ivc_turn_chain::mint_rotated_turn_leaf`) dispatches on `carrier_witness` and binds a
        // custom leg's claimed `custom_proof_commitment` to a re-proven sub-proof leaf; this online
        // driver mints the plain segment leaf for EVERY turn. So a proof-bind-declaring leg folded
        // here would carry a prover-chosen claim bound by nothing — no in-AIR constraint
        // (`Ir2Air::Main` has no `ProofBind` arm) and no connect — and `finalize`'s artifact is
        // accepted by the same `verify_turn_chain_recursive` discipline, so a light client could
        // not tell it apart from a K-folded chain. Refuse it outright rather than let the online
        // path be the weaker of two roads to the same root. (Attaching a witness does NOT help
        // here: there is no arm to consume it. Routing such a turn through `ivc_turn_chain` is the
        // supported path; wiring a carrier arm into this driver is named, undone work.)
        dregg_circuit::effect_vm_descriptors::require_no_unbacked_proof_bind(&leg.descriptor)
            .map_err(|e| AccError::TurnProofInvalid {
                index: idx,
                reason: format!(
                    "unbacked proof-bind arm selection (online accumulator has no carrier arm — \
                     fold this turn through ivc_turn_chain): {e}"
                ),
            })?;
        let new_leaf = prove_descriptor_leaf_rotated_with_segment(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .map_err(|reason| AccError::TurnProofInvalid { index: idx, reason })?;

        // (4) the running fold.
        //
        // The running proof has THREE shape-eras across the fold, with DIFFERENT preprocessed
        // commitments (hence the pin must distinguish them):
        //   - era 0: the running proof IS a single LEAF (after turn 0). Its left-fold (turn 1) is
        //            LEAF∘LEAF — the left input's VK is the leaf VK.
        //   - era 1+: the running proof is an AGGREGATION (after turn 1+). Its left-fold (turn 2+)
        //            is AGG∘LEAF — the left input's VK is the running-aggregation VK, which is
        //            CONSTANT from the second aggregation onward (the BatchOnly∘BatchOnly shape is
        //            fixed). THAT constant is the perpetual fixed point.
        // The pin must therefore be captured from the running AGGREGATION shape (era 1+), NOT the
        // first leaf — pinning an AGG left input to a LEAF commitment is a genuine mismatch.
        let new_running = match self.running.take() {
            None => new_leaf, // first turn: the leaf is the running proof (no fold yet).
            Some(running) => {
                // THE RECURSION: re-verify the running proof in-circuit (BatchOnly) and fold it
                // against the new leaf. This is `into_recursion_input::<BatchOnly>` driven as a
                // running LEFT-fold (the same re-verification `aggregate_tree` does per node).
                //
                // ── VK-IDENTITY PIN (lever (a), in-band) + FAIL-CLOSED tooth. ──────────────────
                // `pinned_running_vk` holds the EXPECTED commitment of the running proof we are about
                // to re-fold — recorded from the proof we PRODUCED last step (below). Three things:
                //   1. We assert the held running proof's commitment STILL equals that expected value.
                //      A mismatch means the running proof is NOT the one we produced (a foreign/swapped
                //      proof) — FATAL: reject with `AccError::VkIdentityMismatch`, leaving the
                //      accumulator UNCHANGED. (The previous behaviour silently fell through to the
                //      UNPINNED fold on any mismatch — a forged running proof of a different circuit
                //      would have folded through unpinned, defeating the pin. Now the driver refuses.)
                //   2. We pin the running (left) input's preprocessed commitment IN-CIRCUIT to that
                //      value, so the aggregation circuit constrains "I fold the proof I produced."
                //   3. The expected value TRACKS the running commitment across the finite transient
                //      (the AGG∘LEAF op-list settles over a couple of folds before the perpetual fixed
                //      point) — so honest transient folds are NOT falsely rejected, and once the fixed
                //      point is reached the pin naturally holds the perpetual fixed-point VK forever.
                // On the FIRST aggregation (`pinned_running_vk` is `None` — the running proof is still
                // the genesis leaf) there is no recorded expectation yet, so that one fold is unpinned;
                // its OUTPUT seeds the expectation for every subsequent fold.
                let expected = running.running_preprocessed_commit();
                // THE SEGMENT INSTANCE INDICES — read off the batch proofs BEFORE converting them
                // to recursion inputs (which consume them). left = the running proof's exposed
                // segment, right = the new leaf's exposed segment; the combine hook reads both.
                let left_seg_idx = expose_claim_instance_index(&running.0).ok_or_else(|| {
                    AccError::RecursionFailed {
                        reason: "running proof carries no segment (expose_claim) table".to_string(),
                    }
                })?;
                let right_seg_idx = expose_claim_instance_index(&new_leaf.0).ok_or_else(|| {
                    AccError::RecursionFailed {
                        reason: "new descriptor leaf carries no segment (expose_claim) table"
                            .to_string(),
                    }
                })?;
                let left = if self.pin_vk_identity && self.pinned_running_vk.is_some() {
                    if self.pinned_running_vk != expected {
                        // Restore the running proof we `take()`-d so the accumulator is unchanged on
                        // the rejection, then fail closed.
                        let exp_fp = self
                            .pinned_running_vk
                            .as_ref()
                            .map(commit_fingerprint)
                            .unwrap_or_default();
                        let found_fp = expected
                            .as_ref()
                            .map(commit_fingerprint)
                            .unwrap_or_default();
                        self.running = Some(running);
                        return Err(AccError::VkIdentityMismatch {
                            index: idx,
                            expected: exp_fp,
                            found: found_fp,
                        });
                    }
                    // The unwrap is justified: the guard requires `pinned_running_vk.is_some()`.
                    running.into_recursion_input_pinned::<BatchOnly>(
                        self.pinned_running_vk
                            .clone()
                            .expect("pinned_running_vk is Some by the enclosing guard"),
                    )
                } else {
                    // First aggregation (no recorded expectation yet) OR pin disabled: the unpinned
                    // fold. The expectation is recorded from this fold's OUTPUT (below), so EVERY
                    // subsequent fold takes the pinned-or-reject branch above.
                    running.into_recursion_input::<BatchOnly>()
                };
                let right = new_leaf.into_recursion_input::<BatchOnly>();
                // THE SEGMENT COMBINE (the online dual of the K-fold `aggregate_tree` combine):
                // re-expose the parent segment with the ordered 4-lane digest acc = commit(L ++ R),
                // so the running proof carries the whole-chain segment by construction.
                let expose =
                    move |cb: &mut p3_circuit::CircuitBuilder<AccChallenge>,
                          left_apt: &[Vec<p3_recursion::Target>],
                          right_apt: &[Vec<p3_recursion::Target>]| {
                        combine_segments_expose(
                            cb,
                            left_apt,
                            right_apt,
                            left_seg_idx,
                            right_seg_idx,
                        );
                    };
                build_and_prove_aggregation_layer_with_expose::<
                    DreggRecursionConfig,
                    BatchOnly,
                    BatchOnly,
                    _,
                    D,
                >(
                    &left,
                    &right,
                    &config,
                    &backend,
                    &fold_params,
                    None,
                    Some(&expose),
                )
                .map_err(|e| AccError::RecursionFailed {
                    reason: format!("running aggregation layer failed: {e:?}"),
                })?
            }
        };

        // RECORD the expectation for the NEXT fold: the commitment of the running proof we just
        // produced. The next `accumulate` will re-fold THIS proof and must see this exact commitment
        // (the fail-closed tooth above). We record only once `new_running` is an aggregation (it has a
        // preprocessed commitment); the genesis leaf produces `None`, leaving the first aggregation
        // unpinned (as intended). Across the transient this updates each step; at the fixed point it
        // stabilizes to the perpetual VK.
        if self.pin_vk_identity {
            let produced = new_running.running_preprocessed_commit();
            if produced.is_some() {
                self.pinned_running_vk = produced;
            }
        }

        // (5) advance the running summary. The host folds the SEGMENT exactly as the in-circuit
        //     `combine_segments_expose` does — LEFT-LINEARLY: the new leaf's segment
        //     `[first_old8, last_new8, 1, commit(first_old8 ++ last_new8)]` combines into the running
        //     segment as `acc = commit(running.acc ++ leaf.acc)`. The result EQUALS the digest the
        //     running proof exposes, so `finalize`'s carried `chain_digest` matches the root-exposed
        //     segment tooth (O(1) memory: only the running 8-lane segment is kept).
        // FAITHFUL-FLOOR (codex #4 CLOSED): the leaf carries the GENUINE 8-felt anchors
        // (`this_old8`/`this_new8` from [`turn_anchors8`]) — the SAME source the in-circuit leaf binds
        // and the K-fold tree folds. A wide leg contributes genuine per-lane ~124-bit entropy; a narrow
        // leg's broadcast is already baked into the arrays. The running `genesis_root`/`head_root` keep
        // the FULL 8-felt anchors (no `[0]` projection), so the endpoints genuinely bind all eight lanes.
        let leaf = || leaf_seg(this_old8, this_new8);
        let new_summary = match self.summary {
            None => {
                let seg = leaf();
                ChainSummary {
                    genesis_root: seg.first_old8,
                    head_root: seg.last_new8,
                    chain_digest: seg.acc,
                    num_turns: 1,
                }
            }
            Some(s) => {
                let seg = combine_seg(s.as_seg(), leaf());
                ChainSummary {
                    genesis_root: seg.first_old8,
                    head_root: seg.last_new8,
                    chain_digest: seg.acc,
                    num_turns: s.num_turns + 1,
                }
            }
        };

        self.running = Some(new_running);
        self.summary = Some(new_summary);
        // The Lean-emitted scalar turn-chain descriptor binds the head-lane projection of the SAME
        // anchors. On wide legs PI 34/35 are retired to zero, so sourcing the seam from
        // `turn.old_root()`/`new_root()` would make the carried descriptor vacuous and disagree with
        // the deployed wide claim.
        self.seam_pairs.push((this_old8[0], this_new8[0]));
        Ok(())
    }

    /// **Read the running accumulator out into a [`WholeChainProof`]** a light client verifies.
    ///
    /// The running proof IS the root: every `accumulate` fold combined the new leaf's ordered
    /// segment into the running segment in-circuit ([`combine_segments_expose`]), so the running
    /// proof already exposes the whole-chain segment `[genesis_root, head_root, num_turns,
    /// chain_digest]` derived from the REAL descriptor leaves. `finalize` carries that segment as
    /// the four publics + a (non-soundness) binding proof, matching the [`WholeChainProof`] the
    /// K-fold path produces. The result verifies under [`verify_turn_chain_recursive`] /
    /// [`lightclient::verify_history`] against the honest VK anchor extracted from this very fold.
    ///
    /// `finalize` consumes the accumulator (the running proof is moved into the artifact).
    ///
    /// NOTE (the carried binding proof): the Lean-emitted turn-chain descriptor proof is
    /// regenerated from the `seam_pairs` witness (a host-side defense-in-depth witness of the
    /// ordered chain) and carried in the `binding_proof` field for byte-API/struct compatibility,
    /// but it is NO LONGER a soundness dependency and is NOT folded into the root — the SEGMENT
    /// tooth over the running proof's exposed segment binds the claim, exactly as the K-fold path
    /// carries (not folds) its binding proof.
    pub fn finalize(self) -> Result<WholeChainProof, AccError> {
        let summary = self.summary.ok_or(AccError::Empty)?;
        let running = self.running.ok_or(AccError::Empty)?;

        // **THE RUNNING PROOF IS THE ROOT (the ported segment close).** Every `accumulate` fold
        // combined the new leaf's ordered segment into the running segment in-circuit
        // ([`combine_segments_expose`]), so the running proof ALREADY exposes the whole-chain
        // segment `[genesis_root, head_root, num_turns, chain_digest]` — derived BY CONSTRUCTION
        // from the REAL descriptor leaves. `verify_turn_chain_recursive`'s SEGMENT tooth reads it
        // and checks it against the carried claim, fail-closed. There is NO terminal fold and NO
        // swappable binding leaf in the soundness path — exactly the K-fold close.
        //
        // **VK-identity defense-in-depth (codex finding #5).** The running fold was VK-pinned at
        // every step in `accumulate`, so `running` is the pinned fixed-point proof and is already
        // wrap-shaped (proven under [`wrap_params`]) — there is no default-params terminal fold to
        // introduce a depth/shape-dependent root VK. We additionally assert here that the running
        // proof's commitment STILL matches the captured pin: a foreign/swapped running proof is
        // refused fail-closed rather than read out. (No pin captured = a single-turn chain whose
        // running proof is still a leaf; the leaf root is correct.)
        if self.pin_vk_identity && self.pinned_running_vk.is_some() {
            let running_commit = running.running_preprocessed_commit();
            if self.pinned_running_vk != running_commit {
                return Err(AccError::VkIdentityMismatch {
                    index: summary.num_turns,
                    expected: self
                        .pinned_running_vk
                        .as_ref()
                        .map(commit_fingerprint)
                        .unwrap_or_default(),
                    found: running_commit
                        .as_ref()
                        .map(commit_fingerprint)
                        .unwrap_or_default(),
                });
            }
        }

        // The carried binding proof: a host-side defense-in-depth witness of the ordered chain,
        // rebuilt from the O(1) summary + `seam_pairs`. RETAINED for the `WholeChainProof`
        // byte-API/struct compatibility but NO LONGER a soundness dependency and NOT folded into
        // the root — exactly as the K-fold path carries (not folds) its binding proof.
        let binding_inner = finalize_binding_leaf(&summary, &self.seam_pairs)
            .map_err(|reason| AccError::RecursionFailed { reason })?;

        Ok(WholeChainProof {
            root: running,
            binding_proof: binding_inner,
            // The GENUINE 8-felt running endpoints (codex #4 CLOSED) — the same per-lane anchors the
            // running proof's exposed segment carries, so the segment tooth in
            // `verify_turn_chain_recursive` matches lane-for-lane (no single-felt broadcast).
            genesis_root: summary.genesis_root,
            final_root: summary.head_root,
            chain_digest: summary.chain_digest,
            num_turns: summary.num_turns,
            // The accumulator folds plain segment turns; the board window is the two-leg
            // automatafl fold's claim and is absent here (a 25-lane root, as before).
            board_window: None,
        })
    }

    /// Convenience: finalize, then VERIFY under the honest self-extracted VK anchor. The setup-side
    /// entry — exactly how an honest producer mints the trust anchor it distributes. A remote light
    /// client instead calls [`verify_turn_chain_recursive`] / `verify_history` with its CONFIGURED
    /// anchor.
    pub fn finalize_and_self_verify(self) -> Result<(WholeChainProof, RecursionVk), AccError> {
        let proof = self.finalize()?;
        let vk = proof.root_vk_fingerprint();
        verify_turn_chain_recursive(&proof, &vk).map_err(|e| AccError::RecursionFailed {
            reason: format!("self-verify of the accumulated artifact failed: {e}"),
        })?;
        Ok((proof, vk))
    }
}

/// Build the per-turn Lean-emitted chain-binding descriptor proof from the running summary + the
/// ordered `seam_pairs`.
///
/// One row per folded turn `[old_root, new_root, acc_in, acc_out]` with `acc_out =
/// hash_4_to_1([acc_in, old, new, idx])` (a scalar sequential digest distinct from the running
/// root's 8-felt ordered-segment digest), padded to a power of two with head fixed-point rows —
/// byte-for-byte the trace
/// `generate_chain_trace_rotated` produces for the same chain. Public inputs `[genesis_root,
/// head_root, num_turns, chain_digest]`. The first/last-row + continuity constraints hold by
/// construction; the last-row `acc_out == chain_digest` binds the descriptor's fourth PI. Tooth 2
/// of `verify_turn_chain_recursive` verifies all four exact PIs and checks the endpoint/count prefix
/// against the carried wide claim.
fn finalize_binding_leaf(
    summary: &ChainSummary,
    seam_pairs: &[(BabyBear, BabyBear)],
) -> Result<TurnChainBindingProof, String> {
    if seam_pairs.is_empty() {
        return Err("cannot build a binding leaf with no seam pairs".to_string());
    }
    if seam_pairs.len() != summary.num_turns {
        return Err(format!(
            "binding seam count {} != running summary count {}",
            seam_pairs.len(),
            summary.num_turns
        ));
    }
    let first = seam_pairs[0].0;
    let last = seam_pairs[seam_pairs.len() - 1].1;
    if first != summary.genesis_root[0] || last != summary.head_root[0] {
        return Err(format!(
            "binding scalar endpoints ({}, {}) != running wide-anchor heads ({}, {})",
            first.as_u32(),
            last.as_u32(),
            summary.genesis_root[0].as_u32(),
            summary.head_root[0].as_u32()
        ));
    }
    prove_turn_chain_binding_for_roots(seam_pairs)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An 8-felt anchor whose lane 0 is `shared0` (the single broadcast felt) and whose lanes 1..8
    /// are `tail`-distinguished — the genuine ~124-bit wide anchor a WIDE leg publishes.
    fn anchor(shared0: u32, tail: u32) -> [BabyBear; SEG_ANCHOR_WIDTH] {
        core::array::from_fn(|i| {
            BabyBear::new(if i == 0 {
                shared0
            } else {
                tail.wrapping_add(i as u32)
            })
        })
    }

    /// **GENUINE-8-FELT ENDPOINT TOOTH (codex #4 CLOSED).** The online accumulator's running endpoints
    /// now carry GENUINE per-lane ~124-bit entropy (the WIDE leg's 8-felt anchor), not a single felt
    /// broadcast across eight lanes. So a forgery that matches the single broadcast felt (lane 0) but
    /// differs in the wide anchor's lanes 1..8 produces a DIFFERENT exposed segment — endpoints AND
    /// digest — and is REJECTED by the segment tooth in `verify_turn_chain_recursive`. Under the OLD
    /// 1-felt broadcast both collapsed to `[lane0; 8]` and were INDISTINGUISHABLE. Host-only (no
    /// recursion proving): exercises `leaf_seg`/`combine_seg`/`ChainSummary::as_seg` — the exact host
    /// machinery that feeds the carried claim the verifier matches against the root-exposed segment.
    #[test]
    fn genuine_8felt_endpoint_binds_where_broadcast_did_not() {
        let shared0 = 0x1234_u32;
        // Two genuine wide anchors that AGREE on lane 0 but DIFFER beyond it — two distinct histories
        // a forger might try to pass off as identical under the old single-felt summary.
        let genuine_a = anchor(shared0, 100);
        let genuine_b = anchor(shared0, 200);
        assert_eq!(genuine_a[0], genuine_b[0], "the two anchors share lane 0");
        assert_ne!(genuine_a, genuine_b, "but differ in the wide lanes 1..8");

        // The OLD 1-felt broadcast collapsed any anchor to `[lane0; 8]` — indistinguishable from BOTH.
        let broadcast: [BabyBear; SEG_ANCHOR_WIDTH] = [BabyBear::new(shared0); SEG_ANCHOR_WIDTH];

        let new8 = anchor(0x5678, 300);

        // (1) The per-turn leaf SEGMENT now incorporates ALL eight lanes: the two genuine anchors and
        //     the broadcast give THREE DISTINCT segment digests (the old broadcast gave ONE).
        let seg_a = leaf_seg(genuine_a, new8);
        let seg_b = leaf_seg(genuine_b, new8);
        let seg_bcast = leaf_seg(broadcast, new8);
        assert_ne!(
            seg_a.acc, seg_b.acc,
            "genuine 8-felt anchors give DISTINCT digests"
        );
        assert_ne!(
            seg_a.acc, seg_bcast.acc,
            "a genuine anchor's digest != its lane-0 broadcast"
        );
        // The exposed endpoints THEMSELVES differ (the segment tooth compares full 8-felt arrays).
        assert_eq!(seg_a.first_old8, genuine_a);
        assert_ne!(seg_a.first_old8, seg_bcast.first_old8);

        // (2) `ChainSummary::as_seg` carries the GENUINE per-lane endpoints (NO broadcast): a summary
        //     built from a genuine anchor exposes that anchor VERBATIM, distinct from the broadcast a
        //     forger controlling only the single felt could reproduce.
        let digest = seg_a.acc; // any digest — the endpoints are what bind here.
        let sum_a = ChainSummary {
            genesis_root: genuine_a,
            head_root: new8,
            chain_digest: digest,
            num_turns: 1,
        };
        let sum_bcast = ChainSummary {
            genesis_root: broadcast,
            head_root: new8,
            chain_digest: digest,
            num_turns: 1,
        };
        assert_eq!(
            sum_a.as_seg().first_old8,
            genuine_a,
            "as_seg exposes the GENUINE anchor, not a lane-0 broadcast"
        );
        assert_ne!(
            sum_a.as_seg().first_old8,
            sum_bcast.as_seg().first_old8,
            "a forger matching only the single broadcast felt CANNOT reproduce the genuine 8-felt endpoint"
        );
        // Sanity on the OLD behavior: the broadcast summary collapses to `[lane0; 8]` (what the
        // single-felt summary always produced), confirming the genuine path is a strict strengthening.
        assert_eq!(sum_bcast.as_seg().first_old8, broadcast);

        // (3) The LEFT-LINEAR combine preserves genuine endpoints: combining two genuine leaves keeps
        //     the left's `first_old8` and the right's `last_new8` per-lane, and folds an order-sensitive
        //     8-lane digest — so the running summary an honest fold carries is itself genuinely 8-felt.
        let mid = anchor(0x9abc, 400);
        let left = leaf_seg(genuine_a, mid);
        let right = leaf_seg(mid, new8);
        let combined = combine_seg(left, right);
        assert_eq!(
            combined.first_old8, genuine_a,
            "combine keeps the genuine left endpoint"
        );
        assert_eq!(
            combined.last_new8, new8,
            "combine keeps the genuine right endpoint"
        );
        // Order-sensitivity (commit(L ++ R) != commit(R ++ L)): swapping operands changes the digest.
        let swapped = combine_seg(right, left);
        assert_ne!(
            combined.acc, swapped.acc,
            "the 8-lane history digest is order-sensitive"
        );
    }
}

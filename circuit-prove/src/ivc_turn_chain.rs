//! GOLD endgame: a continuous whole-chain IVC accumulator over **finalized turns**.
//!
//! ## What this is
//!
//! [`ivc`](dregg_circuit::ivc) accumulates an *attenuation* fold-chain (delegation
//! depth) into one proof. [`joint_turn_recursive`](crate::joint_turn_recursive)
//! folds the N **per-cell** proofs of a *single* shared turn (the hyperedge
//! apex) into one recursive proof. Neither is the whole-chain accumulator.
//!
//! This module is that accumulator: it folds the sequence of *finalized turn*
//! proofs — in the exact order the node's `tau`/blocklace finality produces
//! (`node::blocklace_sync::poll_finalized_blocks` -> `FinalizedBlock`) — into
//! ONE running recursive proof attesting:
//!
//!   "all turns 1..K executed correctly **and** the finalized state root
//!    advanced correctly from the genesis root to the final root, in that
//!    order."
//!
//! It is the sequential dual of the joint-turn (which is cross-cell at one
//! instant). Here the binding is *temporal*: turn N's post-state root must be
//! turn N+1's pre-state root (`prev.NEW_COMMIT == next.OLD_COMMIT`) — the
//! happened-before chain over the *finalized* order, exactly the property the
//! node's tau ordering establishes.
//!
//! ## The two pieces
//!
//! 1. **[`TurnChainBindingAir`]** (one row per folded position): binds the
//!    sequential chain AND the running ordered-history digest. Each row carries
//!    `[old_root, new_root, acc_in, acc_out, idx, is_real, real_count]` plus the
//!    per-row Poseidon2 permutation aux block, with constraints:
//!      - chain continuity: `new_root[i] == old_root[i+1]` (the temporal tooth);
//!      - first row `old_root == genesis_root` (public input);
//!      - last row `new_root == final_root` (public input);
//!      - **running digest `acc_out == hash_4_to_1([acc_in, old_root, new_root,
//!        idx])` ENFORCED in-circuit** (the genuine round-by-round Poseidon2 of
//!        [`poseidon2_permute_expr`], NOT a free witness column), first row
//!        `acc_in == 0`, last row `acc_out == chain_digest` (public);
//!      - `idx` is a positional counter (`0,1,2,…`) so the digest is positionally
//!        bound;
//!      - `num_turns` (public) is pinned to `real_count[last]`, the cumulative
//!        count of the non-padding (`is_real`) rows.
//!
//!    A trace whose turns are reordered, or that drops/inserts a turn, breaks
//!    continuity and is UNSAT; a forged `chain_digest` has no satisfying Poseidon2
//!    witness; a forged `num_turns` mismatches the real-row count — those are the
//!    load-bearing rejections.
//!
//! 2. **The recursion tree (Gold) — REAL leaves.** Each finalized turn's leaf
//!    is the **Lean-descriptor EffectVM AIR itself** ([`EffectVmDescriptorAir`],
//!    the graduated ONE-circuit cutover constraint set: Poseidon2 state-commit
//!    hash sites, per-row gates, transition continuity, `OLD_COMMIT`/`NEW_COMMIT`
//!    PI bindings, balance range checks), re-proven as a recursion-compatible
//!    uni-STARK over the **same 186-column execution trace** the turn's
//!    production rotated IR-v2 batch proof (the retired v1 `EffectVmP3Proof`)
//!    attests, then wrapped in its own **in-circuit verifier layer**
//!    (uni->batch via `build_and_prove_next_layer`). The chain-binding leaf is
//!    wrapped too, and all batch leaves are pairwise aggregated up a binary tree
//!    (`build_and_prove_aggregation_layer`, chained via [`BatchOnly`]) to ONE
//!    root batch-STARK proof. The verifier checks ONLY the root; its cost is
//!    independent of K.
//!
//! ## What the leaf wrap proves (the statement-equality argument)
//!
//! The production turn artifact is a `p3-batch-stark` proof of
//! `EffectVmDescriptorAir(desc)` over `(extend_vm_trace(base_trace), dpis)`,
//! where `dpis` is the descriptor PI prefix (carrying the chain roots at
//! [`pi::OLD_COMMIT`] / [`pi::NEW_COMMIT`]). The recursion fork's in-circuit
//! verifier consumes uni-STARK proofs under the recursion `StarkConfig`, while
//! the production proof is a batch proof under the audited prover config — two
//! FRI engine instantiations of the SAME constraint set. The fold therefore
//! re-proves the IDENTICAL statement — same AIR (`EffectVmDescriptorAir::eval`,
//! config-agnostic), same extended trace ([`descriptor_recursion_matrix`] =
//! the same `extend_vm_trace` surface `prove_vm_descriptor` uses), same PI
//! prefix — as a recursion-compatible uni-STARK, and THAT proof is verified
//! in-circuit by the wrap layer. A claimed `(old_root, new_root)` with no
//! satisfying execution trace has no satisfying leaf under EITHER config (the
//! descriptor's hash sites force `NEW_COMMIT` to be the genuine Poseidon2
//! post-state commitment), so a prover that skips the host-side gate still
//! CANNOT produce a verifying root for a forged turn — that is the tooth
//! `ungated_prover_with_forged_post_commit_cannot_produce_a_root` bites on.
//!
//! ## What the verifier checks (three teeth, in order)
//!
//! [`verify_turn_chain_recursive`] takes the proof AND a caller-held trust
//! anchor (a [`RecursionVk`] — the root circuit's verifier-key fingerprint,
//! obtained once from an honest setup fold, distributed exactly like any
//! SNARK VK) and refuses unless ALL of:
//!
//!   1. **VK pin** — the root proof's verifier-reconstruction inputs (table
//!      shapes, packing, NPO manifest shape, and the preprocessed Merkle
//!      commitment binding the root verifier circuit's op-list) fingerprint
//!      to the anchor. This closes the from-scratch-prover route through
//!      `verify_recursive_batch_proof`'s reconstruct-from-the-proof
//!      discipline: a root proof of a DIFFERENT circuit no longer verifies
//!      "as if" it were the chain fold. (Guarantee, precisely: under blake3
//!      collision resistance + MMCS binding, the accepted root is a valid
//!      batch-STARK of the SAME root verifier-circuit structure the anchor
//!      was extracted from.)
//!   2. **Claimed-publics attestation** — the carried `genesis_root` /
//!      `final_root` / `num_turns` / `chain_digest` must verify as the public
//!      inputs of the carried chain-binding uni-STARK
//!      (`WholeChainProof::binding_proof`, the same statement the fold wraps
//!      in-circuit). Fiat–Shamir binds all four PIs into that proof, so
//!      relabeling any carried field is refused outright.
//!   3. **The root** — `verify_recursive_batch_proof` on the single root.
//!
//! ## CRITICAL HOLE #2 — CLOSED; #1/#6 still open (codex review 2026-06-24)
//!
//! A cross-model adversarial review (`docs/CODEX-IVC-SOUNDNESS-REVIEW.md`, findings
//! #1/#6 and #2) found two residuals admitting a FORGED whole-chain claim the verifier
//! ACCEPTS. **#2 is now CLOSED in-band** (this AIR); #1/#6 remains a fork follow-up.
//!
//!   - **#2 — digest + num_turns unconstrained: CLOSED.** [`TurnChainBindingAir`] now
//!     enforces the per-row hash `acc_out == hash_4_to_1([acc_in, old_root, new_root,
//!     idx])` IN-CIRCUIT — the genuine round-by-round Poseidon2 ([`poseidon2_permute_expr`],
//!     the SAME arithmetization the descriptor leaves use), with `acc_out` no longer a
//!     free column. `idx` is a positional counter, and `num_turns` (pv[2]) is pinned to
//!     `real_count[last]`, the cumulative count of non-padding rows (an `is_real` flag,
//!     boolean + monotone, that survives the power-of-two padding). So a forged
//!     `chain_digest` has no satisfying Poseidon2 witness and a forged `num_turns`
//!     mismatches the real-row count — both UNSAT. The forge teeth
//!     `binding_air_forged_digest_unsat` / `binding_air_forged_num_turns_unsat`
//!     (`circuit-prove/tests/ivc_turn_chain_rotated.rs`) pin the verify→reject flip.
//!   - **#1/#6 — binding↔root NOT linked (still open; mechanism root-caused).**
//!     [`verify_turn_chain_recursive`] checks the carried binding proof, the root VK
//!     fingerprint, and the root proof INDEPENDENTLY — never that the carried binding proof
//!     IS the binding leaf folded into that root. A GENUINE root for history A, paired with a
//!     GENUINE binding proof for a DIFFERENT history B (+ B's publics), passes all three
//!     teeth. EMPIRICALLY: a real K=2 root's `non_primitives` are only `[poseidon2_perm,
//!     recompose]`, BOTH with ZERO public values — the binding leaf's chain publics are
//!     consumed in-circuit and NEVER re-exposed at the root, so the host CANNOT compare
//!     `root-exposed publics == carried claim`.
//!
//!     **THE EXACT REMAINING MECHANISM (source-confirmed 2026-06-24).** The ONLY
//!     host-readable, FRI-bound scalar channel a `BatchStarkProof` carries is
//!     `non_primitives[i].public_values`. The 4 chain publics enter every recursion layer
//!     ONLY as the parent verifier circuit's `air_public_targets`, which the fork allocates
//!     via `circuit.public_input()` (an `Op::Public` → the *constraint-free `Public`
//!     PRIMITIVE table*), NOT as any non-primitive `public_values`. The grandparent allocates
//!     child-public targets solely from each child `non_primitives[].public_values.len()`, so
//!     the publics are consumed ONE layer up and vanish before the root. No NPO table in the
//!     fork populates `public_values` non-empty (`poseidon2`/`recompose` hardcode
//!     `Vec::new()`), so the exposed-public channel is *unbuilt machinery*. The host-only fix
//!     is provably impossible (A and B share the op-list → identical preprocessed/VK
//!     commitment; their distinguishing trace/FRI commitments are consumed in-circuit, never
//!     surfaced). A genuine REJECT therefore requires, in the FORK: (i) an "exposed-claim"
//!     channel — a new constrained NPO table whose `public_values` carry the 4 chain claims,
//!     OR an "expose-target-as-proof-public" hook wired through `build_verifier_circuit` →
//!     `prove_all_tables` → `non_primitives[].public_values` — emitted at the binding-leaf
//!     wrap (`prove_chain_binding_leaf_rotated` + its `build_and_prove_next_layer`); and
//!     (ii) re-emission with an IN-CIRCUIT equality constraint to the verified child at EACH
//!     `build_and_prove_aggregation_layer` up to the root, so the root's
//!     `non_primitives[exposed].public_values` carry the genuine folded endpoints. Then the
//!     host adds tooth (4): `root_exposed_publics == [genesis, final, num_turns, digest]`,
//!     fail-closed. This is multi-pass shared-recursion-engine work; it was NOT landed in this
//!     pass to avoid destabilizing the engine every other dregg proof depends on. The
//!     executable witness `carried_binding_proof_unlinked_to_root_is_an_open_hole`
//!     (`circuit-prove/tests/ivc_turn_chain_rotated.rs`) HONESTLY asserts `is_ok()` (hole
//!     open) and flips to `is_err()` the instant the channel + tooth (4) land.
//!
//! ## The honest residual floor (named, not hidden)
//!
//! - **Engine soundness** (`recursive_sound`): the wrap layer's in-circuit FRI
//!   verifier and the root batch-STARK verifier are the plonky3 recursion
//!   fork's; their soundness is the named crypto carrier, as everywhere else.
//! - **Child-circuit identity under the VK pin (fork follow-up, precise).**
//!   The harness-level VK pin (tooth 1) pins the ROOT layer's circuit
//!   structure, but the fork's aggregation circuit takes each CHILD batch
//!   proof's preprocessed commitment as a runtime PUBLIC INPUT of the parent
//!   circuit (`MerkleCapTargets::new` allocates `alloc_public_input_array`
//!   targets; `CommonDataTargets::get_values` packs the child VK into the
//!   parent's public vector), and circuit public-input VALUES live in the
//!   constraint-free `PublicAir` main trace — `verify_all_tables` never
//!   checks them against caller-supplied values. So a from-scratch prover is
//!   now forced to (a) produce REAL valid batch proofs of SAME-SHAPED
//!   circuits and (b) aggregate them through the honest-shape aggregation
//!   circuit — but the leaf circuits' op-list identity is not yet pinned
//!   in-band. Full closure is fork work, exactly: (i) check the circuit
//!   public-input vector at host verification (today `verify_all_tables`
//!   takes no public values at all), and (ii) either bake child preprocessed
//!   commitments into the parent circuit as constants or re-expose them up
//!   the tree as checked publics.
//! - **Public-value propagation across aggregation layers (fork follow-up,
//!   precise).** `into_recursion_input::<BatchOnly>` hardcodes empty
//!   `table_public_inputs`, and the fork's `build_verifier_circuit` for the
//!   `BatchStark` arm IGNORES them (`table_public_inputs: _`), so leaf public
//!   values are NOT re-exposed at the root. The chain publics are bound to
//!   the leaves at PROVE time (every wrap fails unless its PIs match what its
//!   proof attests — in-circuit) and at VERIFY time by tooth 2's carried
//!   binding proof. What tooth 2 does NOT give: (a) in-band linkage of the
//!   CARRIED binding proof to the binding leaf folded INSIDE the root (an
//!   attacker who could independently satisfy tooth 1's pinned tree could
//!   pair it with a freshly fabricated binding proof — the binding AIR alone
//!   attests hash-chain structure over claimed roots, not execution), and
//!   (b) in-circuit cross-leaf equality between the binding rows'
//!   `(old, new)` pairs and the descriptor leaves' `OLD/NEW_COMMIT` PIs
//!   (today that equality is enforced by the prover constructing both from
//!   the same PI vector, and per-leaf PIs are wrap-bound — but no aggregation
//!   constraint relates two SIBLING leaves). Both need the same fork lever:
//!   thread `table_public_inputs` through batch-to-batch chaining and check
//!   them at the root.
//!
//! ## K-fold vs unbounded
//!
//! [`prove_turn_chain_recursive`] folds an arbitrary *finite* K into one proof.
//! This is genuine IVC for a bounded window: the verifier checks one
//! constant-cost root proof for the whole window.
//!
//! The fully *unbounded* online accumulator — where a single running proof is
//! re-folded with each newly-finalized turn forever, with the previous running
//! proof verified in-circuit so memory stays O(1) — needs the recursion fork's
//! `into_recursion_input::<BatchOnly>` chaining to be driven as a *fold* rather
//! than a *tree*. The 2-step inductive core of that loop is [`fold_two_turns`]
//! (`running ∘ next_turn -> new_running`); see its docs for what the unbounded
//! driver still needs.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput,
    build_and_prove_aggregation_layer, build_and_prove_next_layer,
};

use crate::joint_turn_aggregation::{DescriptorParticipant, verify_descriptor_participant};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, create_recursion_backend,
    recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
};
use dregg_circuit::descriptor_ir2::Ir2BatchProof;
use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::{
    POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH, poseidon2_permute_aux_witness, poseidon2_permute_expr,
};
use dregg_circuit::poseidon2::hash_4_to_1;

// Re-exported so chain consumers (the light client) name the trust-anchor type
// from the module that defines the verification discipline around it.
pub use crate::plonky3_recursion_impl::recursive::RecursionVk;

const D: usize = 4;

fn to_p3(v: BabyBear) -> P3BabyBear {
    P3BabyBear::from_u64(v.0 as u64)
}

// ============================================================================
// One finalized turn: a whole-turn descriptor proof + the trace it attests +
// the (old_root, new_root) it advances.
// ============================================================================

/// A single finalized turn in the chain.
///
/// **Bucket-F (PATH-PRESERVE Phase 5a):** the `participant` carries the MANDATORY ROTATED leg —
/// the per-cell whole-turn rotated multi-table `Ir2BatchProof` (the [`RotatedParticipantLeg`])
/// plus its 38-PI vector. Host admission is [`verify_descriptor_participant`] (the rotated proof
/// verified standalone + selector-bound). The chain roots are read from the ROTATED commitments
/// (PI 34/35); the in-circuit leaf is the rotated batch re-proven via
/// [`prove_descriptor_leaf_rotated_with_config`]. The legacy v1 `base_trace` (the 186-column
/// EffectVM trace the old `prove_descriptor_leaf` wrap consumed) has been DROPPED — the rotated
/// leaf needs only `leg.{descriptor, proof, public_inputs}`.
pub struct FinalizedTurn {
    /// The whole-turn rotated descriptor proof (+ PI) for this finalized turn.
    pub participant: DescriptorParticipant,
}

impl FinalizedTurn {
    /// Wrap a (rotated) descriptor participant as a finalized turn.
    pub fn new(participant: DescriptorParticipant) -> Self {
        Self { participant }
    }

    /// The pre-state root this turn consumes — the ROTATED OLD-commit (PI 34).
    pub fn old_root(&self) -> BabyBear {
        self.participant.rotated.old_root()
    }

    /// The post-state root this turn produces — the ROTATED NEW-commit (PI 35). This is the next
    /// finalized turn's required `old_root` (the temporal binding).
    pub fn new_root(&self) -> BabyBear {
        self.participant.rotated.new_root()
    }
}

// ============================================================================
// Errors
// ============================================================================

/// Why folding a finalized-turn chain failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TurnChainError {
    /// Fewer than 2 turns — a chain fold needs at least 2.
    TooFewTurns {
        /// How many were supplied.
        count: usize,
    },
    /// **The temporal tooth.** Turn `index` does not continue the chain: its
    /// `old_root` is not the previous turn's `new_root`. The finalized order is
    /// broken (reordered / dropped / inserted turn).
    ChainBreak {
        /// The turn that breaks continuity.
        index: usize,
        /// The root the previous turn produced.
        expected_old_root: u32,
        /// The root this turn claims to consume.
        found_old_root: u32,
    },
    /// A turn's per-cell whole-turn proof failed to verify (host admission or
    /// the in-circuit leaf re-proof).
    TurnProofInvalid {
        /// The turn whose proof failed.
        index: usize,
        /// The underlying verification error.
        reason: String,
    },
    /// A recursion layer (leaf wrap or aggregation) failed.
    RecursionFailed {
        /// What failed.
        reason: String,
    },
    /// **The VK pin refused the root.** The root proof's verifier-key
    /// fingerprint (its verifier-reconstruction inputs, incl. the
    /// preprocessed commitment binding the root circuit's op-list) does not
    /// match the caller's trust anchor — this is a proof of a DIFFERENT
    /// circuit, exactly the from-scratch-prover route the pin closes.
    VkFingerprintMismatch {
        /// The anchor fingerprint the caller expected (hex).
        expected: String,
        /// The fingerprint the presented root actually has (hex).
        found: String,
    },
    /// **The claimed chain publics are unattested.** The carried
    /// `genesis_root`/`final_root`/`num_turns`/`chain_digest` failed to
    /// verify as the public inputs of the carried chain-binding proof —
    /// a relabeled (spliced) public claim.
    ClaimedPublicsUnattested {
        /// The underlying verification error.
        reason: String,
    },
    /// **The byte envelope did not decode.** A serialized [`WholeChainProofBytes`]
    /// was malformed, carried an unsupported version, or its embedded proof
    /// components failed to postcard-decode into the concrete recursion proof
    /// types. Fail-closed: a non-decoding envelope is refused, never half-read.
    EnvelopeDecode {
        /// What went wrong while decoding.
        reason: String,
    },
}

impl core::fmt::Display for TurnChainError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TurnChainError::TooFewTurns { count } => {
                write!(f, "turn chain needs >= 2 turns, got {count}")
            }
            TurnChainError::ChainBreak {
                index,
                expected_old_root,
                found_old_root,
            } => write!(
                f,
                "turn {index} breaks the finalized chain: old_root {found_old_root} != \
                 previous turn's new_root {expected_old_root} (order tampered)"
            ),
            TurnChainError::TurnProofInvalid { index, reason } => {
                write!(f, "turn {index} proof invalid: {reason}")
            }
            TurnChainError::RecursionFailed { reason } => {
                write!(f, "recursion failed: {reason}")
            }
            TurnChainError::VkFingerprintMismatch { expected, found } => write!(
                f,
                "root verifier-key fingerprint {found} != trust anchor {expected} \
                 (a proof of a different circuit — refused)"
            ),
            TurnChainError::ClaimedPublicsUnattested { reason } => write!(
                f,
                "claimed chain publics are not attested by the carried binding proof \
                 (relabeled genesis/final/num_turns/digest): {reason}"
            ),
            TurnChainError::EnvelopeDecode { reason } => write!(
                f,
                "whole-chain proof byte envelope did not decode: {reason}"
            ),
        }
    }
}

impl std::error::Error for TurnChainError {}

// ============================================================================
// TurnChainBindingAir: the sequential (temporal) chain binding.
// ============================================================================

// Column layout of the chain-binding trace (one row per folded position).
//
// SOUNDNESS NOTE (#2 fix): the running digest `acc_out` is NO LONGER a free
// witness column. Each row carries the FULL in-circuit Poseidon2 permutation aux
// block, and `acc_out` is forced to be `poseidon2([acc_in, old_root, new_root,
// idx, 4, 0..])[0]` — exactly the `hash_4_to_1` the trace generator computes.
// A forged `chain_digest` (a tampered `acc_out` on the last row) therefore has
// no satisfying witness, and a forged `num_turns` is rejected by the real-row
// counter binding (`real_count[last] == num_turns`).
const COL_OLD_ROOT: usize = 0;
const COL_NEW_ROOT: usize = 1;
const COL_ACC_IN: usize = 2;
const COL_ACC_OUT: usize = 3;
const COL_IDX: usize = 4;
const COL_IS_REAL: usize = 5;
const COL_REAL_COUNT: usize = 6;
/// First column of the per-row Poseidon2 permutation aux block.
const BINDING_AUX0: usize = 7;
/// Total binding-AIR trace width: 7 scalar columns + the Poseidon2 aux block.
const BINDING_WIDTH: usize = BINDING_AUX0 + POSEIDON2_PERM_AUX_COLS;
/// The arity domain-separation tag `hash_4_to_1` seeds at state position 4.
const HASH_ARITY_TAG: u32 = 4;

/// AIR binding the finalized turn order AND the running ordered-history digest.
/// One row per folded position: `[old_root, new_root, acc_in, acc_out, idx,
/// is_real, real_count, <Poseidon2 aux block>]`.
///
/// Public inputs `[genesis_root, final_root, num_turns, chain_digest]`.
///
/// Constraints:
///   1. chain continuity (transition): `new_root[i] == old_root[i+1]` — the
///      temporal tooth. A reordered/dropped/inserted turn breaks this and is
///      UNSAT.
///   2. first row `old_root == genesis_root`.
///   3. last row `new_root == final_root`.
///   4. running digest continuity: `acc_out[i] == acc_in[i+1]`; first row
///      `acc_in == 0`; last row `acc_out == chain_digest`.
///   5. **per-row hash binding (THE #2 fix):** `acc_out == poseidon2([acc_in,
///      old_root, new_root, idx], arity=4)[0]`, the genuine in-circuit Poseidon2
///      (the SAME arithmetization `P3MerklePoseidon2Air` uses, via
///      [`poseidon2_permute_expr`]). `acc_out` is no longer free — a forged
///      `chain_digest` has no satisfying witness.
///   6. **idx counter:** `idx == 0` on the first row, `idx[i+1] == idx[i] + 1`
///      on transitions — the hash is POSITIONALLY bound (rows cannot be
///      permuted without breaking the digest).
///   7. **num_turns binding:** `is_real` is boolean and monotone non-increasing
///      (real rows first, then padding); `real_count` runs the cumulative count
///      of real rows; the last row pins `real_count == num_turns`. A forged
///      `num_turns` (≠ the real folded count) is UNSAT.
///
/// The digest commits to the ordered (old_root, new_root, idx) triples, so two
/// distinct finalized histories with the same endpoints still yield distinct
/// digests, and a reordering moves `idx` and so the digest.
pub struct TurnChainBindingAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for TurnChainBindingAir {
    fn width(&self) -> usize {
        BINDING_WIDTH
    }

    fn num_public_values(&self) -> usize {
        4 // [genesis_root, final_root, num_turns, chain_digest]
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        // Next-row reads: old_root (continuity), acc_in (digest chain), idx
        // (counter), is_real (monotonicity), real_count (cumulative count).
        vec![
            COL_OLD_ROOT,
            COL_ACC_IN,
            COL_IDX,
            COL_IS_REAL,
            COL_REAL_COUNT,
        ]
    }
}

impl<AB: AirBuilder> Air<AB> for TurnChainBindingAir
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let old_root: AB::Expr = local[COL_OLD_ROOT].into();
        let new_root: AB::Expr = local[COL_NEW_ROOT].into();
        let acc_in: AB::Expr = local[COL_ACC_IN].into();
        let acc_out: AB::Expr = local[COL_ACC_OUT].into();
        let idx: AB::Expr = local[COL_IDX].into();
        let is_real: AB::Expr = local[COL_IS_REAL].into();
        let real_count: AB::Expr = local[COL_REAL_COUNT].into();
        let next_old_root: AB::Expr = next[COL_OLD_ROOT].into();
        let next_acc_in: AB::Expr = next[COL_ACC_IN].into();
        let next_idx: AB::Expr = next[COL_IDX].into();
        let next_is_real: AB::Expr = next[COL_IS_REAL].into();
        let next_real_count: AB::Expr = next[COL_REAL_COUNT].into();

        let public_values = builder.public_values();
        let genesis_root: AB::Expr = public_values[0].into();
        let final_root: AB::Expr = public_values[1].into();
        let num_turns: AB::Expr = public_values[2].into();
        let chain_digest: AB::Expr = public_values[3].into();

        // Constraint 1 (THE temporal tooth): chain continuity. Each turn's
        // new_root must be the next turn's old_root.
        builder
            .when_transition()
            .assert_zero(new_root.clone() - next_old_root);

        // Constraint 2: first row old_root == genesis_root.
        builder
            .when_first_row()
            .assert_zero(old_root.clone() - genesis_root);

        // Constraint 3: last row new_root == final_root.
        builder
            .when_last_row()
            .assert_zero(new_root.clone() - final_root);

        // Constraint 4: running digest chain.
        builder.when_first_row().assert_zero(acc_in.clone());
        builder
            .when_transition()
            .assert_zero(acc_out.clone() - next_acc_in);
        builder
            .when_last_row()
            .assert_zero(acc_out.clone() - chain_digest);

        // Constraint 5 (THE #2 FIX): per-row hash binding. The running digest is
        // FORCED to be the genuine Poseidon2 of `[acc_in, old_root, new_root,
        // idx]` with the arity-4 domain tag — byte-identical to the trace
        // generator's `hash_4_to_1`. `acc_out` is no longer a free column.
        let aux: &[AB::Var] = &local[BINDING_AUX0..BINDING_AUX0 + POSEIDON2_PERM_AUX_COLS];
        let arity_tag = AB::F::from_u32(HASH_ARITY_TAG);
        let input_state: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|i| match i {
            0 => acc_in.clone(),
            1 => old_root.clone(),
            2 => new_root.clone(),
            3 => idx.clone(),
            4 => AB::Expr::from(arity_tag),
            _ => AB::Expr::ZERO,
        });
        let digest = poseidon2_permute_expr(builder, input_state, aux);
        builder.assert_zero(acc_out - digest);

        // Constraint 6: idx is a positional counter (0, 1, 2, ...).
        builder.when_first_row().assert_zero(idx.clone());
        builder
            .when_transition()
            .assert_zero(next_idx - (idx + AB::Expr::ONE));

        // Constraint 7: num_turns is the count of REAL (non-padding) rows.
        //   - is_real is boolean;
        //   - is_real is monotone non-increasing (real rows first, then padding):
        //     a 0->1 transition is forbidden, so `next_is_real * (1 - is_real) == 0`;
        //   - real_count starts at is_real[0] and accumulates is_real;
        //   - the last row pins real_count == num_turns.
        builder.assert_bool(is_real.clone());
        builder
            .when_transition()
            .assert_zero(next_is_real.clone() * (AB::Expr::ONE - is_real.clone()));
        builder
            .when_first_row()
            .assert_zero(real_count.clone() - is_real);
        builder
            .when_transition()
            .assert_zero(next_real_count - (real_count.clone() + next_is_real));
        builder.when_last_row().assert_zero(real_count - num_turns);
    }
}

// ============================================================================
// Trace generation for the chain binding.
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the v1 `generate_chain_trace` /
// `generate_chain_trace_unchecked` (which read v1 OLD/NEW_COMMIT at PI 0/4) are DELETED.
// The rotated fold builds its binding trace via `generate_chain_trace_rotated` (reading the
// ROTATED commitments at PI 34/35).

fn trace_to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    debug_assert!(
        trace.iter().all(|row| row.len() == BINDING_WIDTH),
        "binding trace rows must all be {BINDING_WIDTH} wide"
    );
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, BINDING_WIDTH)
}

/// Read a finalized turn's chain roots from its mandatory ROTATED leg (PI 34/35).
///
/// Bucket-F (PATH-PRESERVE Phase 5a): the rotated leg is MANDATORY — `FinalizedTurn` carries
/// exactly one [`crate::joint_turn_aggregation::RotatedParticipantLeg`], so reading its roots is
/// infallible (no v1 fallback leg, no `Option`).
fn rotated_roots(t: &FinalizedTurn) -> (BabyBear, BabyBear) {
    let leg = &t.participant.rotated;
    (leg.old_root(), leg.new_root())
}

/// [`generate_chain_trace`] reading the ROTATED chain roots (PI 34/35) instead of the v1
/// OLD/NEW_COMMIT (PI 0/4). The binding leaf the rotated fold wraps therefore commits to the
/// rotated v9 commitments.
fn generate_chain_trace_rotated(
    turns: &[&FinalizedTurn],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>, BabyBear), TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    for i in 1..turns.len() {
        let (_, prev_new) = rotated_roots(turns[i - 1]);
        let (this_old, _) = rotated_roots(turns[i]);
        if prev_new != this_old {
            return Err(TurnChainError::ChainBreak {
                index: i,
                expected_old_root: prev_new.0,
                found_old_root: this_old.0,
            });
        }
    }
    let n = turns.len();
    let padded_len = n.next_power_of_two().max(2);
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(padded_len);
    let mut acc = BabyBear::ZERO;
    let mut real_count = BabyBear::ZERO;
    for (i, t) in turns.iter().enumerate() {
        let (old_root, new_root) = rotated_roots(t);
        let idx = BabyBear::new(i as u32);
        real_count += BabyBear::ONE;
        let (acc_out, row) = binding_row(
            old_root, new_root, acc, idx, /* is_real */ true, real_count,
        );
        trace.push(row);
        acc = acc_out;
    }
    let final_root = trace.last().unwrap()[COL_NEW_ROOT];
    for i in n..padded_len {
        let idx = BabyBear::new(i as u32);
        // Padding rows carry is_real = 0 (real_count frozen at n) and continue the
        // genuine hash chain over the (final_root, final_root, idx) triple.
        let (acc_out, row) = binding_row(
            final_root, final_root, acc, idx, /* is_real */ false, real_count,
        );
        trace.push(row);
        acc = acc_out;
    }
    let genesis_root = trace[0][COL_OLD_ROOT];
    let chain_digest = trace.last().unwrap()[COL_ACC_OUT];
    let pis = vec![
        genesis_root,
        final_root,
        BabyBear::new(n as u32),
        chain_digest,
    ];
    let digest = pis[3];
    Ok((trace, pis, digest))
}

/// Build one wide binding-trace row and return `(acc_out, row)`.
///
/// `acc_out = hash_4_to_1([acc_in, old_root, new_root, idx])` — the SAME digest the
/// in-circuit constraint forces — and the Poseidon2 aux block is the genuine
/// intermediate-state witness [`poseidon2_permute_expr`] checks round-by-round,
/// seeded from `[acc_in, old_root, new_root, idx, 4, 0..]` (the `hash_4_to_1`
/// state).
fn binding_row(
    old_root: BabyBear,
    new_root: BabyBear,
    acc_in: BabyBear,
    idx: BabyBear,
    is_real: bool,
    real_count: BabyBear,
) -> (BabyBear, Vec<BabyBear>) {
    let acc_out = hash_4_to_1(&[acc_in, old_root, new_root, idx]);

    let mut input_state = [BabyBear::ZERO; POSEIDON2_WIDTH];
    input_state[0] = acc_in;
    input_state[1] = old_root;
    input_state[2] = new_root;
    input_state[3] = idx;
    input_state[4] = BabyBear::new(HASH_ARITY_TAG);
    let aux = poseidon2_permute_aux_witness(input_state);
    debug_assert_eq!(aux.len(), POSEIDON2_PERM_AUX_COLS);
    // The aux block's final state[0] IS the digest (the gadget returns state[0]).
    debug_assert_eq!(aux[POSEIDON2_PERM_AUX_COLS - POSEIDON2_WIDTH], acc_out);

    let mut row = Vec::with_capacity(BINDING_WIDTH);
    row.push(old_root); // COL_OLD_ROOT
    row.push(new_root); // COL_NEW_ROOT
    row.push(acc_in); // COL_ACC_IN
    row.push(acc_out); // COL_ACC_OUT
    row.push(idx); // COL_IDX
    row.push(if is_real {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    }); // COL_IS_REAL
    row.push(real_count); // COL_REAL_COUNT
    row.extend_from_slice(&aux); // BINDING_AUX0..
    debug_assert_eq!(row.len(), BINDING_WIDTH);
    (acc_out, row)
}

// ============================================================================
// Per-turn leaf: the ROTATED descriptor batch re-proven recursion-compatibly.
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the v1 `prove_descriptor_leaf` (which re-proved the
// 186-column `EffectVmDescriptorAir` uni-STARK over a `FinalizedTurn::base_trace`) is DELETED.
// The mandatory per-turn leaf is the ROTATED multi-table `Ir2BatchProof` carried on
// `participant.rotated`, wrapped in-circuit by `prove_descriptor_leaf_rotated_with_config`
// below — `FinalizedTurn` no longer carries a v1 `base_trace`, so there is nothing for the v1
// leaf to consume.

/// The FRI knobs the production IR-v2 descriptor batch (`descriptor_ir2::ir2_config`) is
/// minted under: `log_blowup = 6`, `log_final_poly_len = 0`, `commit_pow = 0`,
/// `query_pow = 16` (19 queries, max_log_arity 3 — both read from the proof in-circuit, so
/// they need no entry here). The native-batch leaf-wrap's in-circuit FRI verifier is built
/// with `FriVerifierParams` matching these (via
/// [`create_recursion_config_for_inner_fri`]) so an `ir2_config` proof verifies as-is — the
/// SIDESTEP (C3 PART 2a): the inner proof keeps its production FRI engine; only the
/// recursion verifier's params are retargeted. The leaf-wrap OUTPUT is a standard
/// recursion-config (`log_blowup = 3`, 38-query) proof.
const IR2_INNER_LOG_BLOWUP: usize = 6;
const IR2_INNER_LOG_FINAL_POLY_LEN: usize = 0;
const IR2_INNER_COMMIT_POW_BITS: usize = 0;
const IR2_INNER_QUERY_POW_BITS: usize = 16;

/// THREAD 1 (C3 cutover) — the rotated multi-table `Ir2BatchProof` native-batch leaf-wrap.
///
/// Re-prove one rotated finalized-turn DESCRIPTOR batch (`transferVmDescriptor2R24` &c — the
/// IR-v2 multi-table `Ir2BatchProof`: main + chip + range + memory + map tables, the degree-7
/// S-box, LogUp buses) as a recursion-compatible BatchStark leaf, with the descriptor PI
/// prefix (carrying the chain roots) bound in-circuit by the wrap layer. The leaf's in-circuit
/// constraint evaluation is the REAL `Ir2Air` set's `eval_folded_circuit` per instance — NOT
/// the recursion's fixed `CircuitTablesAir[Const/Public/Alu]+NPO` reconstruction.
///
/// **How the two walls of the prior pass are crossed:**
///   1. **Proof-type wall** — `Ir2BatchProof = p3_batch_stark::BatchProof` (bare native) is
///      no longer wrapped as `RecursionInput::BatchStark` (which holds the circuit-prover
///      `BatchStarkProof` wrapper). It rides the NEW `RecursionInput::NativeBatchStark`
///      variant, whose backend arm allocates verifier inputs from the BARE batch proof
///      (`BatchStarkVerifierInputsBuilder::allocate`, which already takes
///      `&p3_batch_stark::BatchProof`) and runs the caller's `&[Ir2Air]` straight through the
///      generic `verify_batch_circuit`.
///   2. **Config wall** — the production `Ir2BatchProof` (`ir2_config`: log_blowup 6, 19
///      queries, 16 query-PoW) is verified in-circuit by a recursion config whose
///      `FriVerifierParams` are retargeted to `ir2_config`'s FRI knobs
///      (`create_recursion_config_for_inner_fri`); `num_queries` + folding arity are read
///      from the inner proof structure in-circuit, so only log_blowup / pow need matching.
///      The MMCS hash / compress / challenger / field are byte-identical between the two
///      configs already (both `PaddingFreeSponge`+`TruncatedPermutation` over Poseidon2-w16,
///      DuplexChallenger, BabyBear-deg4), which is what makes the SIDESTEP a verifier-param
///      retarget rather than a re-prove.
///
/// The wrap layer's output is a standard recursion-config batch proof (the same type the v1
/// `prove_descriptor_leaf` wrap and the aggregation tree consume), so a rotated descriptor
/// leaf now folds into the SAME `aggregate_tree` / chain machinery.
///
/// **STATUS (2026-06-13): GREEN — all three walls crossed.** This compiles, runs, builds the
/// in-circuit verifier, PASSES in-circuit FRI MMCS verification, the recursion verifier circuit's
/// own `WitnessChecks` LogUp bus BALANCES, and the wrapped root self-verifies in-circuit. The
/// final wall was the foreign-multi-table-LogUp-leaf `WitnessChecks` accounting: a descriptor
/// public input asserted equal to the zero constant put it in `ExprId::ZERO`'s connect-class, so
/// `WitnessId(0)` had TWO bus creators (the zero `Const` AND a `Public` op) → net +779 on the
/// all-zero tuple (config/arity-INDEPENDENT). The fork now demotes such a duplicate `Public` to a
/// bus READER (`p3_circuit::PreprocessedColumns::dup_public_outputs` → multiplicity −1 in
/// `get_airs_and_degrees_with_prep`), which both restores the one-creator-per-witness invariant
/// AND soundly binds the public value to the zero constant. The transfer leaf (3 instances: main
/// w=331 / 38 PV / 50 global lookups · chip w=364 / 2 global · byte w=2 / 1 global) folds GREEN;
/// the smoke test `rotation_batchstark_leaf_smoke.rs` asserts it (no longer `#[ignore]`'d).
///
/// **The inner proof is a `BatchProof<DreggRecursionConfig>` (SIDESTEP option a):** the
/// rotated prover mints the IR-v2 batch under the recursion config TYPE (with `ir2`'s FRI
/// knobs, via [`dregg_circuit::descriptor_ir2::prove_vm_descriptor2_for_config`] +
/// [`create_recursion_config_for_inner_fri`]) so the in-circuit verifier consumes it with no
/// cross-config type mismatch. `RecursionInput::NativeBatchStark.proof` is
/// `&p3_batch_stark::BatchProof<SC>` with `SC = DreggRecursionConfig`, so the inner proof and
/// the recursion pipeline share one config type. Use
/// [`ir2_airs_and_common_for_config`](dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config)
/// to obtain the matching `(airs, table_public_inputs, common)` triple.
pub fn prove_descriptor_leaf_rotated(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    prove_descriptor_leaf_rotated_with_config(desc, proof, descriptor_pis, &ir2_leaf_wrap_config())
}

/// The self-consistent recursion config the rotated native-batch leaf-wrap runs at: its FRI
/// engine (StarkConfig PCS + in-circuit `FriVerifierParams`) is set to `ir2_config`'s knobs
/// (log_blowup 6, max_log_arity 3, 19 queries, 16 query-PoW), so the INNER proof is minted,
/// VERIFIED in-circuit, and the OUTPUT proven all at ONE FRI engine — the Merkle path lengths
/// the verifier circuit allocates match the siblings the inner proof carries. The inner proof
/// fed to [`prove_descriptor_leaf_rotated`] must be minted under THIS config (see
/// `descriptor_ir2::prove_vm_descriptor2_for_config`).
pub fn ir2_leaf_wrap_config() -> DreggRecursionConfig {
    // Fixed `IR2_INNER_*` knobs ⇒ identical config on every call; build once per thread and clone
    // on access (Arc-backed, cheap). `thread_local` sidesteps any `Sync` requirement; the cached
    // value is identical to a fresh `create_recursion_config_for_inner_fri(..)` at these constants.
    thread_local! {
        static LEAF_WRAP_CONFIG: DreggRecursionConfig =
            crate::plonky3_recursion_impl::recursive::create_recursion_config_for_inner_fri(
                IR2_INNER_LOG_BLOWUP,
                IR2_INNER_LOG_FINAL_POLY_LEN,
                IR2_INNER_COMMIT_POW_BITS,
                IR2_INNER_QUERY_POW_BITS,
            );
    }
    LEAF_WRAP_CONFIG.with(|c| c.clone())
}

/// [`prove_descriptor_leaf_rotated`] under an explicit recursion config (the inner proof must
/// have been minted under the SAME config — same FRI engine). Exposed so the smoke test +
/// future chain wiring share one config object for mint + wrap + output-verify.
pub fn prove_descriptor_leaf_rotated_with_config(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    // The verify-path triple under the SAME config TYPE as the inner proof: the present-table
    // `Ir2Air` set, the per-table public-input vectors (descriptor PIs on the main instance,
    // empty elsewhere), and the canonical symbolic `CommonData<DreggRecursionConfig>` (the
    // IR-v2 AIRs have NO preprocessed columns, so `common` is config-value-independent).
    let (airs, table_public_inputs, common) =
        dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config(
            desc,
            proof,
            descriptor_pis,
            config,
        )?;

    let input: RecursionInput<'_, DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    let backend = create_recursion_backend();

    build_and_prove_next_layer::<DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air, _, D>(
        &input,
        config,
        &backend,
        &ProveNextLayerParams::default(),
    )
    .map_err(|e| format!("rotated native-batch leaf-wrap failed: {e:?}"))
}

// ============================================================================
// The whole-chain IVC artifact (K-fold).
// ============================================================================

/// The Gold whole-chain artifact: ONE succinct recursive proof attesting that
/// **all** K finalized-turn leaves AND the sequential chain-binding leaf
/// verified in-circuit. The verifier checks only the root; cost is independent
/// of K.
pub struct WholeChainProof {
    /// The single root batch-STARK proof (the whole tree folded to one).
    pub root: RecursionOutput<DreggRecursionConfig>,
    /// The chain-binding uni-STARK (the SAME statement the fold wraps
    /// in-circuit as the binding leaf), carried so the verifier can check the
    /// claimed publics below AGAINST A PROOF instead of trusting bare fields:
    /// Fiat–Shamir binds `[genesis_root, final_root, num_turns, chain_digest]`
    /// into this proof, so relabeling any of them is refused at verify time.
    pub binding_proof: RecursionCompatibleProof,
    /// The genesis root the chain starts from.
    pub genesis_root: BabyBear,
    /// The final root the chain reaches.
    pub final_root: BabyBear,
    /// The running digest committing to the ordered (old_root, new_root) pairs.
    pub chain_digest: BabyBear,
    /// Number of finalized turns folded.
    pub num_turns: usize,
}

impl WholeChainProof {
    /// The root proof's verifier-key fingerprint (see [`RecursionVk`]).
    ///
    /// An HONEST SETUP party extracts this ONCE from a locally produced fold
    /// and distributes it as the light client's trust anchor (exactly like a
    /// SNARK VK). A VERIFIER must NEVER take the anchor from the artifact it
    /// is verifying — [`verify_turn_chain_recursive`] recomputes this from
    /// the presented root and compares it to the caller-held anchor.
    ///
    /// Note the fingerprint is a function of the root circuit SHAPE, which
    /// varies with the tree structure (`num_turns`) and the leaf trace
    /// heights: an anchor pins one accepted window shape; a client accepting
    /// several window shapes holds one anchor per shape.
    pub fn root_vk_fingerprint(&self) -> RecursionVk {
        recursion_vk_fingerprint(&self.root.0)
    }

    /// Serialize the VERIFY-SUFFICIENT subset of this proof into a versioned byte
    /// envelope ([`WholeChainProofBytes`]) that round-trips over a wire.
    ///
    /// A whole [`WholeChainProof`] is NOT byte-encodable: its `root.1`
    /// (`Rc<CircuitProverData>`) is prover-chaining data with no serde and no
    /// verifier use. The envelope therefore carries only what
    /// [`verify_turn_chain_recursive_from_parts`] reads — the root
    /// [`BatchStarkProof`] (`root.0`), the chain-binding `Proof`, and the four
    /// public scalars — as a self-describing, version-tagged blob. The producer
    /// (a node/relayer that ran the history) ships this; the consumer (a wasm tab,
    /// a pg-dregg SRF) calls [`verify_whole_chain_proof_bytes`] on it.
    ///
    /// Infallible: the alloc/postcard serializer does not fail on a well-formed
    /// value, and both proof components derive `Serialize` (`#[serde(bound = "")]`).
    pub fn to_bytes(&self) -> Vec<u8> {
        WholeChainProofBytes::from_proof(self).to_postcard()
    }
}

/// The versioned, wire-crossable byte envelope of a [`WholeChainProof`] — the S1
/// artifact (`docs/PG-DREGG.md` §10.2, `WEB-FORWARD.md` §7).
///
/// It carries the VERIFY-SUFFICIENT subset of a [`WholeChainProof`]: the
/// prover-only `root.1` (`Rc<CircuitProverData>`) is omitted because the verifier
/// never reads it. Both proof components ride as opaque postcard blobs so the
/// envelope itself is a plain serde value; the four publics ride as canonical
/// `u32`s (a `BabyBear` is one field element). A carried `vk_fingerprint_hex`
/// rides as a producer CLAIM for diagnostics and is NEVER trusted at verify — the
/// verifier compares the RECOMPUTED fingerprint against a caller-held anchor.
///
/// The version pin fail-closes a layout change: a stale producer's bytes are
/// refused (`EnvelopeDecode`), never misread as a different shape.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct WholeChainProofBytes {
    /// The envelope format version ([`WHOLE_CHAIN_PROOF_ENVELOPE_V1`]).
    pub version: u16,
    /// The producer's CLAIMED root-circuit VK fingerprint (hex). NEVER trusted at
    /// verify — the verifier recomputes it from `root_proof` and compares to the
    /// caller-held anchor. Carried only so a consumer can render the precise
    /// "built-for-circuit X, your anchor pins Y" diagnostic.
    pub vk_fingerprint_hex: String,
    /// Postcard bytes of `WholeChainProof.root.0` — the root [`BatchStarkProof`].
    /// Teeth 1 (VK pin) and 3 (root batch verify) read exactly this.
    pub root_proof: Vec<u8>,
    /// Postcard bytes of `WholeChainProof.binding_proof` — the chain-binding
    /// uni-STARK `Proof`. Tooth 2 verifies the four publics AS its public inputs.
    pub binding_proof: Vec<u8>,
    /// The genesis root the chain starts from (canonical `BabyBear` as `u32`).
    pub genesis_root: u32,
    /// The final root the chain reaches.
    pub final_root: u32,
    /// The ordered-history digest over the (old_root, new_root) pairs.
    pub chain_digest: u32,
    /// The number of finalized turns folded.
    pub num_turns: u64,
}

/// The on-the-wire version tag of [`WholeChainProofBytes`]. Bumped on any layout
/// change so an old producer's bytes are refused (fail-closed) not misread.
pub const WHOLE_CHAIN_PROOF_ENVELOPE_V1: u16 = 1;

impl WholeChainProofBytes {
    /// Project a [`WholeChainProof`] to its verify-sufficient byte envelope.
    pub fn from_proof(proof: &WholeChainProof) -> Self {
        let root_proof = postcard::to_allocvec(&proof.root.0)
            .expect("root BatchStarkProof postcard-encodes (serde(bound=\"\"))");
        let binding_proof = postcard::to_allocvec(&proof.binding_proof)
            .expect("binding Proof postcard-encodes (serde(bound=\"\"))");
        WholeChainProofBytes {
            version: WHOLE_CHAIN_PROOF_ENVELOPE_V1,
            vk_fingerprint_hex: proof.root_vk_fingerprint().to_hex(),
            root_proof,
            binding_proof,
            genesis_root: proof.genesis_root.as_u32(),
            final_root: proof.final_root.as_u32(),
            chain_digest: proof.chain_digest.as_u32(),
            num_turns: proof.num_turns as u64,
        }
    }

    /// Encode to wire bytes (postcard). Infallible on a well-formed value.
    pub fn to_postcard(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("WholeChainProofBytes postcard-encodes")
    }

    /// Decode from wire bytes. Fail-closed: empty input, a malformed body, a wrong
    /// version, or an empty proof component is an `Err` — never a silently-accepted
    /// half-envelope.
    pub fn from_postcard(bytes: &[u8]) -> Result<Self, TurnChainError> {
        if bytes.is_empty() {
            return Err(TurnChainError::EnvelopeDecode {
                reason: "empty whole-chain proof envelope".to_string(),
            });
        }
        let env: WholeChainProofBytes =
            postcard::from_bytes(bytes).map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("envelope body does not decode: {e}"),
            })?;
        if env.version != WHOLE_CHAIN_PROOF_ENVELOPE_V1 {
            return Err(TurnChainError::EnvelopeDecode {
                reason: format!(
                    "unsupported envelope version {} (this build reads v{})",
                    env.version, WHOLE_CHAIN_PROOF_ENVELOPE_V1
                ),
            });
        }
        if env.root_proof.is_empty() {
            return Err(TurnChainError::EnvelopeDecode {
                reason: "envelope carries an empty root proof".to_string(),
            });
        }
        if env.binding_proof.is_empty() {
            return Err(TurnChainError::EnvelopeDecode {
                reason: "envelope carries an empty binding proof".to_string(),
            });
        }
        Ok(env)
    }

    /// Decode the two opaque blobs into the concrete recursion proof types.
    /// Fail-closed on a blob that does not deserialize into its target type.
    fn decode_parts(
        &self,
    ) -> Result<
        (
            p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
            RecursionCompatibleProof,
        ),
        TurnChainError,
    > {
        let root_proof: p3_circuit_prover::BatchStarkProof<DreggRecursionConfig> =
            postcard::from_bytes(&self.root_proof).map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("root BatchStarkProof does not decode: {e}"),
            })?;
        // Re-check the structural invariants the prover enforces but a raw
        // `#[derive(Deserialize)]` can bypass (ext-degree, row counts, packing,
        // non-primitive manifest) — a malformed-but-decodable root is refused
        // BEFORE the cryptographic teeth run on it.
        root_proof
            .validate()
            .map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("root BatchStarkProof failed structural validation: {e:?}"),
            })?;
        let binding_proof: RecursionCompatibleProof = postcard::from_bytes(&self.binding_proof)
            .map_err(|e| TurnChainError::EnvelopeDecode {
                reason: format!("binding Proof does not decode: {e}"),
            })?;
        Ok((root_proof, binding_proof))
    }
}

/// **Verify a whole-chain proof straight from its byte envelope**, against a
/// caller-held trust anchor. The over-wire dual of [`verify_turn_chain_recursive`].
///
/// Decodes the [`WholeChainProofBytes`] (fail-closed on malformed/wrong-version/
/// empty-component bytes), reconstructs the two concrete proof types, and runs the
/// SAME three teeth as the in-memory verifier via
/// [`verify_turn_chain_recursive_from_parts`]. The prover-only `root.1` is never
/// needed, so byte-reconstruction of the verify path is total.
///
/// `expected_vk` is the caller's OWN configured anchor — it is NEVER read from the
/// envelope (the envelope's `vk_fingerprint_hex` is a discarded claim). A root of a
/// different circuit fails tooth 1; tampered publics fail tooth 2; a corrupted root
/// proof fails tooth 3 (or structural validation at decode).
pub fn verify_whole_chain_proof_bytes(
    bytes: &[u8],
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    let env = WholeChainProofBytes::from_postcard(bytes)?;
    let (root_proof, binding_proof) = env.decode_parts()?;
    verify_turn_chain_recursive_from_parts(
        &root_proof,
        &binding_proof,
        BabyBear::new(env.genesis_root),
        BabyBear::new(env.final_root),
        BabyBear::new(env.chain_digest),
        env.num_turns as usize,
        expected_vk,
    )
}

/// **Verify from the two OPAQUE proof-component blobs + publics** — the seam a
/// downstream that cannot name the p3 proof types (e.g. `pg-dregg`, which does not
/// depend on `p3-circuit-prover`) plugs into.
///
/// `root_blob` is the postcard of the root [`BatchStarkProof`] (`WholeChainProof.
/// root.0`) and `binding_blob` the postcard of the chain-binding `Proof`
/// (`WholeChainProof.binding_proof`) — exactly the two blobs a transport
/// (`pg-dregg`'s `SerializedWholeChainProof`, or the circuit's
/// [`WholeChainProofBytes`]) carries. This decodes them inside the circuit crate
/// (where the p3 types live), structurally validates the root, and runs the SAME
/// three teeth as [`verify_turn_chain_recursive`] via
/// [`verify_turn_chain_recursive_from_parts`]. Fail-closed on a blob that does not
/// decode. `vk_anchor` is the caller's configured 32-byte trust anchor.
#[allow(clippy::too_many_arguments)]
pub fn verify_turn_chain_recursive_from_blobs(
    root_blob: &[u8],
    binding_blob: &[u8],
    genesis_root: u32,
    final_root: u32,
    chain_digest: u32,
    num_turns: usize,
    vk_anchor: &[u8; 32],
) -> Result<(), TurnChainError> {
    if root_blob.is_empty() {
        return Err(TurnChainError::EnvelopeDecode {
            reason: "empty root proof blob".to_string(),
        });
    }
    if binding_blob.is_empty() {
        return Err(TurnChainError::EnvelopeDecode {
            reason: "empty binding proof blob".to_string(),
        });
    }
    let root_proof: p3_circuit_prover::BatchStarkProof<DreggRecursionConfig> =
        postcard::from_bytes(root_blob).map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("root BatchStarkProof blob does not decode: {e}"),
        })?;
    root_proof
        .validate()
        .map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("root BatchStarkProof failed structural validation: {e:?}"),
        })?;
    let binding_proof: RecursionCompatibleProof =
        postcard::from_bytes(binding_blob).map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("binding Proof blob does not decode: {e}"),
        })?;
    verify_turn_chain_recursive_from_parts(
        &root_proof,
        &binding_proof,
        BabyBear::new(genesis_root),
        BabyBear::new(final_root),
        BabyBear::new(chain_digest),
        num_turns,
        &RecursionVk(*vk_anchor),
    )
}

/// Fold K finalized-turn proofs into ONE whole-chain recursive proof.
///
/// `turns` must be in the node's **finalized order** (the `tau`/blocklace order
/// from `node::blocklace_sync::poll_finalized_blocks`). Each turn's `new_root`
/// must be the next turn's `old_root` — the temporal binding the chain leaf
/// enforces both host-side and in-circuit.
///
/// Steps:
///   1. host admission: every turn's production descriptor proof verifies
///      SELECTOR-BOUND through the Lean descriptor verifier
///      ([`verify_descriptor_participant`]) — this also determines each turn's
///      descriptor selector;
///   2. host-side: >= 2 turns, sequential continuity;
///   3. prove the chain-binding leaf (rejects a broken order in-circuit too);
///   4. re-prove each turn's REAL descriptor AIR over its OWN execution trace
///      as a recursion-compatible uni-STARK ([`prove_descriptor_leaf`]);
///   5. wrap every leaf in its own IN-CIRCUIT verifier layer (uni->batch) —
///      per-turn execution soundness is verified inside the recursion, not
///      merely at the host gate;
///   6. pairwise-aggregate all batch leaves up a binary tree to ONE root.
///
/// The host gate (step 1) is an admission discipline, NOT the soundness
/// boundary: a prover that skips it (see
/// [`prove_turn_chain_recursive_without_host_gate`]) still cannot produce a
/// verifying root for a forged turn, because steps 4-5 have no satisfying
/// witness for a forged `(old_root, new_root)`.
pub fn prove_turn_chain_recursive(
    turns: &[FinalizedTurn],
) -> Result<WholeChainProof, TurnChainError> {
    // (1) host admission: descriptor-verify every turn, selector-bound.
    let mut selectors = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, &selectors)
}

/// **THE UNGATED PROVER (tamper surface).** Fold a chain WITHOUT the host-side
/// descriptor admission, taking the prover's CLAIMED selectors at face value.
///
/// This exists to make the soundness claim falsifiable: the host gate in
/// [`prove_turn_chain_recursive`] must NOT be load-bearing. A malicious prover
/// that skips it and feeds a forged turn (a post-commit lie in the PIs, a stub
/// trace, an absent/borrowed proof object) still has to satisfy the REAL
/// descriptor AIR in-circuit at the leaf wrap — and a forged statement has no
/// satisfying witness, so the fold fails and no verifying root exists. The
/// tests `ungated_prover_with_forged_post_commit_cannot_produce_a_root` and
/// `ungated_prover_with_stub_leaf_cannot_produce_a_root` drive this path.
pub fn prove_turn_chain_recursive_without_host_gate(
    turns: &[FinalizedTurn],
    claimed_selectors: &[usize],
) -> Result<WholeChainProof, TurnChainError> {
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, claimed_selectors)
}

// ============================================================================
// THE ROTATED whole-chain fold (Bucket-F: the ONLY fold — the v1 `prove_chain_core`
// + v1 leaf are deleted; `prove_turn_chain_recursive` routes straight here).
// ============================================================================

/// Fold K finalized turns into one whole-chain proof through the ROTATED leaf-wrap.
///
/// Identical in shape to [`prove_turn_chain_recursive`], but every per-turn leaf is the
/// rotated multi-table `Ir2BatchProof` (carried on `participant.rotated`), minted in-circuit
/// via [`prove_descriptor_leaf_rotated_with_config`] at [`ir2_leaf_wrap_config`] — NOT the v1
/// uni-STARK `EffectVmDescriptorAir` wrap. The whole tree (binding leaf + aggregation) runs at
/// the ONE wrap config, exactly as the aggregation gate
/// (`rotation_batchstark_leaf_smoke::two_rotated_leaves_aggregate_at_wrap_config`) proves it
/// folds. Every turn MUST carry a rotated leg (`participant.rotated == Some`); a missing leg
/// fails closed.
///
/// The temporal binding is read from the ROTATED commitments (PI 34/35 — the rotated trace's
/// before/after `state_commit` carriers), so the chain continuity tooth
/// (`prev.new_root == next.old_root`) binds the rotated v9 commitment.
pub fn prove_turn_chain_recursive_rotated(
    turns: &[FinalizedTurn],
) -> Result<WholeChainProof, TurnChainError> {
    // Host admission: descriptor-verify every turn, selector-bound (the v1 leg gate; the
    // rotated leaf re-proof is the soundness boundary, this is admission discipline).
    let mut selectors = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, &selectors)
}

/// The rotated fold core: like [`prove_chain_core`] but mints rotated native-batch leaves and
/// runs the whole tree at [`ir2_leaf_wrap_config`].
fn prove_chain_core_rotated(
    turns: &[&FinalizedTurn],
    selectors: &[usize],
) -> Result<WholeChainProof, TurnChainError> {
    if selectors.len() != turns.len() {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "selector count {} != turn count {}",
                selectors.len(),
                turns.len()
            ),
        });
    }
    // Host-side continuity + the binding witness. The binding leaf reads the chain roots from
    // `FinalizedTurn::old_root/new_root`, which the rotated path overrides to the rotated
    // commitments (see `generate_chain_trace_rotated`).
    let (_, chain_pis, chain_digest) = generate_chain_trace_rotated(turns)?;
    let genesis_root = chain_pis[0];
    let final_root = chain_pis[1];

    // The ONE FRI engine the whole rotated tree runs at (inner proof + leaf-wrap + binding +
    // aggregation), so the in-circuit FRI verifier params match every child's FRI engine.
    let config = ir2_leaf_wrap_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // Chain-binding leaf, wrapped to a batch at the wrap config.
    let (binding_inner, binding_pis) = prove_chain_binding_leaf_rotated(turns)?;

    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(turns.len() + 1);

    // One rotated descriptor leaf per finalized turn.
    for (i, t) in turns.iter().enumerate() {
        let leg = &t.participant.rotated;
        let wrapped = prove_descriptor_leaf_rotated_with_config(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        batch_leaves.push(wrapped);
    }

    // The chain-binding leaf wrapped uni->batch at the wrap config.
    {
        let air = TurnChainBindingAir;
        let p3_pis: Vec<P3BabyBear> = binding_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &binding_inner,
            air: &air,
            public_inputs: p3_pis,
            preprocessed_commit: None,
        };
        let wrapped =
            build_and_prove_next_layer::<DreggRecursionConfig, TurnChainBindingAir, _, D>(
                &input, &config, &backend, &params,
            )
            .map_err(|e| TurnChainError::RecursionFailed {
                reason: format!("recursive chain-binding leaf failed: {e:?}"),
            })?;
        batch_leaves.push(wrapped);
    }

    let root = aggregate_tree(batch_leaves, &config, &backend, &params)?;

    Ok(WholeChainProof {
        root,
        binding_proof: binding_inner,
        genesis_root,
        final_root,
        chain_digest,
        num_turns: turns.len(),
    })
}

/// Build the chain-binding leaf reading the ROTATED chain roots (PI 34/35), at the wrap config.
///
/// **Bucket-F fix:** the binding-leaf inner proof MUST be minted at [`ir2_leaf_wrap_config`]
/// (log_blowup 6), the SAME FRI engine the whole rotated tree runs at — it is wrapped and
/// aggregated with the rotated descriptor leaves at that config, so proving it at the default
/// `create_recursion_config` (log_blowup 3) and then wrapping at the wrap config raises
/// `InvalidProofShape("Fewer siblings in proof than op_ids provided")` in-circuit.
fn prove_chain_binding_leaf_rotated(
    turns: &[&FinalizedTurn],
) -> Result<(RecursionCompatibleProof, Vec<BabyBear>), TurnChainError> {
    use crate::plonky3_recursion_impl::recursive::{
        prove_inner_for_air_with_config, verify_inner_for_air_with_config,
    };
    let (trace, pis, _digest) = generate_chain_trace_rotated(turns)?;
    let matrix = trace_to_matrix(&trace);
    let air = TurnChainBindingAir;
    let wrap_config = ir2_leaf_wrap_config();
    let proof = prove_inner_for_air_with_config(&air, matrix, &pis, &wrap_config);
    verify_inner_for_air_with_config(&air, &proof, &pis, &wrap_config)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;
    Ok((proof, pis))
}

/// Fold a vector of batch-STARK proofs to ONE via 2-to-1 aggregation layers.
/// (Same binary-tree fold as [`joint_turn_recursive`](crate::joint_turn_recursive).)
fn aggregate_tree(
    mut proofs: Vec<RecursionOutput<DreggRecursionConfig>>,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    if proofs.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "no leaves to aggregate".to_string(),
        });
    }
    while proofs.len() > 1 {
        let mut next_level: Vec<RecursionOutput<DreggRecursionConfig>> =
            Vec::with_capacity(proofs.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < proofs.len() {
            let left = proofs[i].into_recursion_input::<BatchOnly>();
            let right = proofs[i + 1].into_recursion_input::<BatchOnly>();
            let out = build_and_prove_aggregation_layer::<
                DreggRecursionConfig,
                BatchOnly,
                BatchOnly,
                _,
                D,
            >(&left, &right, config, backend, params, None)
            .map_err(|e| TurnChainError::RecursionFailed {
                reason: format!("aggregation layer failed: {e:?}"),
            })?;
            next_level.push(out);
            i += 2;
        }
        if i < proofs.len() {
            next_level.push(proofs.pop().unwrap());
        }
        proofs = next_level;
    }
    Ok(proofs.pop().unwrap())
}

/// Verify the whole-chain artifact against a caller-held trust anchor.
/// Cost is independent of the number of folded turns. Three teeth, in order
/// (see the module docs for what each one guarantees, precisely):
///
///   1. **VK pin** — recompute the presented root's verifier-key fingerprint
///      and compare it to `expected_vk` (the anchor an honest setup
///      distributed). A root proof of a different circuit — the from-scratch
///      aggregation route — is refused here, BEFORE any cryptographic check
///      trusts the proof's self-described circuit data.
///   2. **Claimed-publics attestation** — the carried `genesis_root` /
///      `final_root` / `num_turns` / `chain_digest` must verify as the public
///      inputs of the carried chain-binding proof (Fiat–Shamir binds all
///      four). Relabeled public claims are refused.
///   3. **The root** — the single root batch-STARK proof verifies.
pub fn verify_turn_chain_recursive(
    proof: &WholeChainProof,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    verify_turn_chain_recursive_from_parts(
        &proof.root.0,
        &proof.binding_proof,
        proof.genesis_root,
        proof.final_root,
        proof.chain_digest,
        proof.num_turns,
        expected_vk,
    )
}

/// The verify core, taking the VERIFY-SUFFICIENT PARTS directly instead of a whole
/// [`WholeChainProof`] value.
///
/// This is the byte-path's verifier: a [`WholeChainProof`] cannot be reconstructed
/// from bytes because its `root.1` (`Rc<CircuitProverData>`) is prover-only and not
/// serde — but the verifier never reads `root.1`. The three teeth use only
/// `root.0` (the root [`BatchStarkProof`]), the chain-binding `Proof`, and the four
/// public scalars, which is exactly this signature. [`verify_turn_chain_recursive`]
/// is a thin wrapper that forwards a whole value's parts here, and
/// [`verify_whole_chain_proof_bytes`] decodes a [`WholeChainProofBytes`] envelope and
/// calls this — so the in-memory and over-wire paths share ONE verifier body.
///
/// The teeth, in order (identical to [`verify_turn_chain_recursive`]):
///   1. **VK pin** — recompute the root's verifier-key fingerprint and compare to
///      `expected_vk` (a foreign-circuit root is refused before any check trusts it).
///   2. **Claimed-publics attestation** — `genesis_root`/`final_root`/`num_turns`/
///      `chain_digest` must verify as the public inputs of the carried binding proof
///      (Fiat–Shamir binds all four); a relabeled public is refused.
///   3. **The root** — the single root batch-STARK proof verifies.
#[allow(clippy::too_many_arguments)]
pub fn verify_turn_chain_recursive_from_parts(
    root_proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    binding_proof: &RecursionCompatibleProof,
    genesis_root: BabyBear,
    final_root: BabyBear,
    chain_digest: BabyBear,
    num_turns: usize,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    // (1) VK pin.
    let found = recursion_vk_fingerprint(root_proof);
    if found != *expected_vk {
        return Err(TurnChainError::VkFingerprintMismatch {
            expected: expected_vk.to_hex(),
            found: found.to_hex(),
        });
    }

    // (2) Claimed publics, read against the carried binding proof. The binding proof is minted at
    // the rotated leaf-wrap config (log_blowup 6, `prove_chain_binding_leaf_rotated`), so it must
    // be verified under that SAME config.
    let claimed_pis = vec![
        genesis_root,
        final_root,
        BabyBear::new(num_turns as u32),
        chain_digest,
    ];
    crate::plonky3_recursion_impl::recursive::verify_inner_for_air_with_config(
        &TurnChainBindingAir,
        binding_proof,
        &claimed_pis,
        &ir2_leaf_wrap_config(),
    )
    .map_err(|reason| TurnChainError::ClaimedPublicsUnattested { reason })?;

    // (3) The root. The root batch proof is produced by `aggregate_tree` at the rotated
    // leaf-wrap config (`ir2_leaf_wrap_config`, log_blowup 6 / 19 queries — the SAME FRI engine
    // the whole rotated tree runs at), NOT the default `create_recursion_config` (log_blowup 3 /
    // 38 queries). It MUST be verified under that same config, else FRI reconstruction expects
    // the wrong query count (`QueryProofCountMismatch { expected: 38, got: 19 }`).
    verify_recursive_batch_proof_with_config(root_proof, &ir2_leaf_wrap_config())
        .map_err(|reason| TurnChainError::RecursionFailed { reason })
}

// ============================================================================
// The 2-step inductive core of the UNBOUNDED accumulator.
// ============================================================================

/// The inductive core of a continuous (unbounded) accumulator:
/// `fold_two_turns(running, next) -> new_running`.
///
/// This proves the *binary* step that, iterated, gives the unbounded loop:
/// given a proof of "turns 1..N executed and the root advanced to `mid_root`"
/// and the next finalized turn `(mid_root -> new_root)`, produce a proof of
/// "turns 1..N+1 executed and the root advanced to `new_root`". The two leaves
/// (running summary + next turn) are wrapped and aggregated into one batch
/// proof — the same fold the K-fold tree applies at each internal node.
///
/// ## What this IS
///
/// A genuine 2-to-1 recursive fold over real in-circuit-verified leaves, with
/// the temporal binding (`prev.new_root == next.old_root`) enforced by the
/// chain-binding leaf over the 2-turn window. Iterating it left-to-right over a
/// finalized stream reproduces [`prove_turn_chain_recursive`]'s result.
///
/// ## What the UNBOUNDED driver still needs (named open)
///
/// To make the running proof itself *constant memory* across an unbounded
/// stream — i.e. fold `running_proof ∘ next_turn` where `running_proof` is the
/// PREVIOUS fold's output re-verified IN-CIRCUIT — the running batch proof must
/// be fed back as a [`BatchOnly`] recursion input to the next layer (the fork's
/// `into_recursion_input::<BatchOnly>` already supports this; it is what
/// [`aggregate_tree`] uses internally). The open work is the *driver*: a
/// persistent accumulator struct that (a) holds the single running
/// `RecursionOutput`, (b) on each `poll_finalized_blocks` tick builds the next
/// turn leaf + a 2-row chain-binding leaf binding `running.final_root ->
/// new_root`, and (c) re-aggregates `running ∘ {turn, binding}` into the new
/// running output. The cryptographic machinery is all present and exercised
/// here; what remains is wiring it to the node's live finality stream and
/// persisting the running output across restarts.
pub fn fold_two_turns(
    running: &FinalizedTurn,
    next: &FinalizedTurn,
) -> Result<WholeChainProof, TurnChainError> {
    // The 2-turn window IS a turn chain of length 2 — reuse the proven path
    // (by reference: the descriptor proof artifact is move-only, so the window
    // borrows the turns instead of cloning them).
    let window: [&FinalizedTurn; 2] = [running, next];
    let mut selectors = Vec::with_capacity(2);
    for (i, t) in window.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    prove_chain_core_rotated(&window, &selectors)
}

// ============================================================================
// Tests
// ============================================================================
//
// Bucket-F (PATH-PRESERVE Phase 5a): the in-lib `#[cfg(test)] mod tests` (the K-fold,
// broken-order, ungated-forged-post-commit, stub-leaf, foreign-circuit-VK-pin,
// in-circuit-wrap, and 2-step-inductive teeth) RELOCATED to the integration test
// `circuit/tests/ivc_turn_chain_rotated.rs`, which can mint the mandatory ROTATED
// participant through `dregg_turn::rotation_witness::mint_rotated_participant_leg`
// (the circuit lib cannot — it has no `dregg-cell` / `dregg-turn` dependency, the cycle).

//! GOLD endgame: a continuous whole-chain IVC accumulator over **finalized turns**.
//!
//! ## What this is
//!
//! [`ivc`](crate::ivc) accumulates an *attenuation* fold-chain (delegation
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
//! 1. **[`TurnChainBindingAir`]** (width 4, one row per finalized turn): binds
//!    the sequential chain. Each row carries `[old_root, new_root, acc_in,
//!    acc_out]` with constraints:
//!      - chain continuity: `new_root[i] == old_root[i+1]` (the temporal tooth);
//!      - first row `old_root == genesis_root` (public input);
//!      - last row `new_root == final_root` (public input);
//!      - running digest `acc_out = hash_4_to_1([acc_in, old_root, new_root, idx])`,
//!        first row `acc_in == 0`, last row `acc_out == chain_digest` (public).
//!
//!    A trace whose turns are reordered, or that drops/inserts a turn, breaks
//!    continuity and is UNSAT — that is the load-bearing rejection.
//!
//! 2. **The recursion tree (Gold) — REAL leaves.** Each finalized turn's leaf
//!    is the **Lean-descriptor EffectVM AIR itself** ([`EffectVmDescriptorAir`],
//!    the graduated ONE-circuit cutover constraint set: Poseidon2 state-commit
//!    hash sites, per-row gates, transition continuity, `OLD_COMMIT`/`NEW_COMMIT`
//!    PI bindings, balance range checks), re-proven as a recursion-compatible
//!    uni-STARK over the **same 186-column execution trace** the turn's
//!    production [`EffectVmP3Proof`](crate::effect_vm_p3_full_air::EffectVmP3Proof)
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

#![cfg(feature = "recursion")]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput,
    build_and_prove_aggregation_layer, build_and_prove_next_layer,
};

#[cfg(feature = "recursion")]
use crate::descriptor_ir2::Ir2BatchProof;
use crate::field::BabyBear;
use crate::joint_turn_aggregation::{DescriptorParticipant, verify_descriptor_participant};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, create_recursion_backend,
    recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
};
use crate::poseidon2::hash_4_to_1;

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
        }
    }
}

impl std::error::Error for TurnChainError {}

// ============================================================================
// TurnChainBindingAir: the sequential (temporal) chain binding.
// ============================================================================

/// Width-4 AIR binding the finalized turn order. One row per finalized turn:
/// `[old_root, new_root, acc_in, acc_out]`.
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
///
/// The digest commits to the ordered (old_root, new_root) pairs, so two distinct
/// finalized histories with the same endpoints still yield distinct digests.
pub struct TurnChainBindingAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for TurnChainBindingAir {
    fn width(&self) -> usize {
        4
    }

    fn num_public_values(&self) -> usize {
        4 // [genesis_root, final_root, num_turns, chain_digest]
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        (0..4).collect()
    }
}

impl<AB: AirBuilder> Air<AB> for TurnChainBindingAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let old_root: AB::Expr = local[0].into();
        let new_root: AB::Expr = local[1].into();
        let acc_in: AB::Expr = local[2].into();
        let acc_out: AB::Expr = local[3].into();
        let next_old_root: AB::Expr = next[0].into();
        let next_acc_in: AB::Expr = next[2].into();

        let public_values = builder.public_values();
        let genesis_root: AB::Expr = public_values[0].into();
        let final_root: AB::Expr = public_values[1].into();
        // public_values[2] = num_turns (carried for the caller; not constrained
        // here since the trace length encodes it, and binding it would require a
        // row-count selector the fork's AirBuilder does not expose cheaply).
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
        builder.when_last_row().assert_zero(new_root - final_root);

        // Constraint 4: running digest chain.
        builder.when_first_row().assert_zero(acc_in.clone());
        builder
            .when_transition()
            .assert_zero(acc_out.clone() - next_acc_in);
        builder.when_last_row().assert_zero(acc_out - chain_digest);
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

fn trace_to_matrix(trace: &[[BabyBear; 4]]) -> RowMajorMatrix<P3BabyBear> {
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, 4)
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
) -> Result<(Vec<[BabyBear; 4]>, Vec<BabyBear>, BabyBear), TurnChainError> {
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
    let mut trace: Vec<[BabyBear; 4]> = Vec::with_capacity(padded_len);
    let mut acc = BabyBear::ZERO;
    for (i, t) in turns.iter().enumerate() {
        let (old_root, new_root) = rotated_roots(t);
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[acc, old_root, new_root, idx]);
        trace.push([old_root, new_root, acc, acc_out]);
        acc = acc_out;
    }
    let final_root = trace.last().unwrap()[1];
    for i in n..padded_len {
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[acc, final_root, final_root, idx]);
        trace.push([final_root, final_root, acc, acc_out]);
        acc = acc_out;
    }
    let genesis_root = trace[0][0];
    let chain_digest = trace.last().unwrap()[3];
    let pis = vec![
        genesis_root,
        final_root,
        BabyBear::new(n as u32),
        chain_digest,
    ];
    let digest = pis[3];
    Ok((trace, pis, digest))
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
#[cfg(feature = "recursion")]
const IR2_INNER_LOG_BLOWUP: usize = 6;
#[cfg(feature = "recursion")]
const IR2_INNER_LOG_FINAL_POLY_LEN: usize = 0;
#[cfg(feature = "recursion")]
const IR2_INNER_COMMIT_POW_BITS: usize = 0;
#[cfg(feature = "recursion")]
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
/// knobs, via [`crate::descriptor_ir2::prove_vm_descriptor2_for_config`] +
/// [`create_recursion_config_for_inner_fri`]) so the in-circuit verifier consumes it with no
/// cross-config type mismatch. `RecursionInput::NativeBatchStark.proof` is
/// `&p3_batch_stark::BatchProof<SC>` with `SC = DreggRecursionConfig`, so the inner proof and
/// the recursion pipeline share one config type. Use
/// [`ir2_airs_and_common_for_config`](crate::descriptor_ir2::ir2_airs_and_common_for_config)
/// to obtain the matching `(airs, table_public_inputs, common)` triple.
#[cfg(feature = "recursion")]
pub fn prove_descriptor_leaf_rotated(
    desc: &crate::descriptor_ir2::EffectVmDescriptor2,
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
#[cfg(feature = "recursion")]
pub fn ir2_leaf_wrap_config() -> DreggRecursionConfig {
    crate::plonky3_recursion_impl::recursive::create_recursion_config_for_inner_fri(
        IR2_INNER_LOG_BLOWUP,
        IR2_INNER_LOG_FINAL_POLY_LEN,
        IR2_INNER_COMMIT_POW_BITS,
        IR2_INNER_QUERY_POW_BITS,
    )
}

/// [`prove_descriptor_leaf_rotated`] under an explicit recursion config (the inner proof must
/// have been minted under the SAME config — same FRI engine). Exposed so the smoke test +
/// future chain wiring share one config object for mint + wrap + output-verify.
#[cfg(feature = "recursion")]
pub fn prove_descriptor_leaf_rotated_with_config(
    desc: &crate::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    // The verify-path triple under the SAME config TYPE as the inner proof: the present-table
    // `Ir2Air` set, the per-table public-input vectors (descriptor PIs on the main instance,
    // empty elsewhere), and the canonical symbolic `CommonData<DreggRecursionConfig>` (the
    // IR-v2 AIRs have NO preprocessed columns, so `common` is config-value-independent).
    let (airs, table_public_inputs, common) =
        crate::descriptor_ir2::ir2_airs_and_common_for_config(desc, proof, descriptor_pis, config)?;

    let input: RecursionInput<'_, DreggRecursionConfig, crate::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    let backend = create_recursion_backend();

    build_and_prove_next_layer::<DreggRecursionConfig, crate::descriptor_ir2::Ir2Air, _, D>(
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
    // (1) VK pin.
    let found = recursion_vk_fingerprint(&proof.root.0);
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
        proof.genesis_root,
        proof.final_root,
        BabyBear::new(proof.num_turns as u32),
        proof.chain_digest,
    ];
    crate::plonky3_recursion_impl::recursive::verify_inner_for_air_with_config(
        &TurnChainBindingAir,
        &proof.binding_proof,
        &claimed_pis,
        &ir2_leaf_wrap_config(),
    )
    .map_err(|reason| TurnChainError::ClaimedPublicsUnattested { reason })?;

    // (3) The root. The root batch proof is produced by `aggregate_tree` at the rotated
    // leaf-wrap config (`ir2_leaf_wrap_config`, log_blowup 6 / 19 queries — the SAME FRI engine
    // the whole rotated tree runs at), NOT the default `create_recursion_config` (log_blowup 3 /
    // 38 queries). It MUST be verified under that same config, else FRI reconstruction expects
    // the wrong query count (`QueryProofCountMismatch { expected: 38, got: 19 }`).
    verify_recursive_batch_proof_with_config(&proof.root.0, &ir2_leaf_wrap_config())
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

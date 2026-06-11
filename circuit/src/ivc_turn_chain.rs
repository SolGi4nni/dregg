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

use crate::effect_vm::pi;
use crate::effect_vm_descriptors::descriptor_for_selector;
use crate::field::BabyBear;
use crate::joint_turn_aggregation::{DescriptorParticipant, verify_descriptor_participant};
use crate::lean_descriptor_air::{
    EffectVmDescriptorAir, descriptor_recursion_matrix, parse_vm_descriptor,
};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, create_recursion_backend,
    create_recursion_config, prove_inner_for_air, recursion_vk_fingerprint, verify_inner_for_air,
    verify_recursive_batch_proof,
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
/// The `participant` carries the per-cell whole-turn DESCRIPTOR-INTERPRETER
/// proof (`EffectVmP3Proof`, the production cutover wire type) + the public
/// inputs it attests; host admission is [`verify_descriptor_participant`]
/// (selector-bound through the Lean descriptor verifier). The aggregator reads
/// the cell's pre/post state commitment out of the PI prefix as the chain
/// roots.
///
/// `base_trace` is the 186-column EffectVM execution trace the proof attests —
/// the prover-side witness from which the in-circuit leaf is re-proven (the
/// fold wraps the REAL descriptor constraint set over THIS trace; see the
/// module docs' statement-equality argument). The chain prover is the node
/// that produced the history, so it holds the traces it executed.
pub struct FinalizedTurn {
    /// The whole-turn descriptor-interpreter proof for this finalized turn.
    pub participant: DescriptorParticipant,
    /// The base EffectVM execution trace the proof attests (width =
    /// the descriptor's `trace_width`, i.e. `EFFECT_VM_WIDTH`).
    pub base_trace: Vec<Vec<BabyBear>>,
}

impl FinalizedTurn {
    /// Wrap a descriptor participant + its execution trace as a finalized turn.
    pub fn new(participant: DescriptorParticipant, base_trace: Vec<Vec<BabyBear>>) -> Self {
        Self {
            participant,
            base_trace,
        }
    }

    /// The pre-state root this turn consumes (`OLD_COMMIT` position 0).
    pub fn old_root(&self) -> BabyBear {
        self.participant.public_inputs[pi::OLD_COMMIT]
    }

    /// The post-state root this turn produces (`NEW_COMMIT` position 0). This is
    /// the next finalized turn's required `old_root` — the temporal binding.
    pub fn new_root(&self) -> BabyBear {
        self.participant.public_inputs[pi::NEW_COMMIT]
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

/// Host-side chain checks (>= 2 turns, sequential continuity) + the binding
/// trace. Returns `(trace, public_inputs, chain_digest)`.
///
/// Surfaces a [`TurnChainError::ChainBreak`] at the witness level so we never
/// hand the prover an unsatisfiable trace — but the AIR's constraint 1 rejects
/// it too (see [`generate_chain_trace_unchecked`]).
fn generate_chain_trace(
    turns: &[&FinalizedTurn],
) -> Result<(Vec<[BabyBear; 4]>, Vec<BabyBear>, BabyBear), TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    // Sequential continuity (the temporal tooth, host side).
    for i in 1..turns.len() {
        let prev_new = turns[i - 1].new_root();
        let this_old = turns[i].old_root();
        if prev_new != this_old {
            return Err(TurnChainError::ChainBreak {
                index: i,
                expected_old_root: prev_new.0,
                found_old_root: this_old.0,
            });
        }
    }
    let (trace, pis) = generate_chain_trace_unchecked(turns);
    let digest = pis[3];
    Ok((trace, pis, digest))
}

/// Build the chain-binding trace WITHOUT the host continuity check. The AIR's
/// constraint 1 still enforces it; the negative test uses this to confirm the
/// *circuit* rejects a broken order.
fn generate_chain_trace_unchecked(turns: &[&FinalizedTurn]) -> (Vec<[BabyBear; 4]>, Vec<BabyBear>) {
    let n = turns.len();
    let padded_len = n.next_power_of_two().max(2);
    let mut trace: Vec<[BabyBear; 4]> = Vec::with_capacity(padded_len);
    let mut acc = BabyBear::ZERO;

    for (i, t) in turns.iter().enumerate() {
        let old_root = t.old_root();
        let new_root = t.new_root();
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[acc, old_root, new_root, idx]);
        trace.push([old_root, new_root, acc, acc_out]);
        acc = acc_out;
    }

    // Pad to power of two. Padding rows are NoOp self-loops on the final root
    // (old_root == new_root == final new_root) so continuity + digest hold.
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
    (trace, pis)
}

fn trace_to_matrix(trace: &[[BabyBear; 4]]) -> RowMajorMatrix<P3BabyBear> {
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, 4)
}

// ============================================================================
// Per-turn leaf: the REAL descriptor AIR re-proven recursion-compatibly.
// ============================================================================

/// Re-prove one finalized turn's DESCRIPTOR constraint set as a
/// recursion-compatible uni-STARK over the turn's own execution trace, with the
/// descriptor PI prefix (carrying the chain roots at `pi::OLD_COMMIT` /
/// `pi::NEW_COMMIT`) as the public inputs the wrap layer binds in-circuit.
///
/// Returns the AIR (needed again by the wrap), the inner proof, and the PI
/// prefix. The statement is IDENTICAL to the production `EffectVmP3Proof`'s
/// (same AIR, same extended trace, same PIs) — see the module docs.
///
/// A turn whose claimed PIs have no satisfying trace (forged post-commit, stub
/// trace, absent execution) FAILS here: the prover refuses the unsatisfiable
/// trace (debug) or the self-verify rejects (release). Either way no leaf
/// exists to wrap, so no root can be produced.
pub(crate) fn prove_descriptor_leaf(
    turn: &FinalizedTurn,
    selector: usize,
) -> Result<
    (
        EffectVmDescriptorAir,
        RecursionCompatibleProof,
        Vec<BabyBear>,
    ),
    String,
> {
    let json = descriptor_for_selector(selector)
        .ok_or_else(|| format!("no descriptor registered for selector {selector}"))?;
    let desc = parse_vm_descriptor(json)?;
    if turn.participant.public_inputs.len() < desc.public_input_count {
        return Err(format!(
            "participant PI vector too short for descriptor: {} < {}",
            turn.participant.public_inputs.len(),
            desc.public_input_count
        ));
    }
    let dpis: Vec<BabyBear> = turn.participant.public_inputs[..desc.public_input_count].to_vec();
    let matrix = descriptor_recursion_matrix(&desc, &turn.base_trace)?;
    let air = EffectVmDescriptorAir::new(desc);
    let proof = prove_inner_for_air(&air, matrix, &dpis);
    verify_inner_for_air(&air, &proof, &dpis)?;
    Ok((air, proof, dpis))
}

/// Build + prove the chain-binding leaf (the sequential temporal binding).
fn prove_chain_binding_leaf(
    turns: &[&FinalizedTurn],
) -> Result<(RecursionCompatibleProof, Vec<BabyBear>), TurnChainError> {
    let (trace, pis, _digest) = generate_chain_trace(turns)?;
    let matrix = trace_to_matrix(&trace);
    let air = TurnChainBindingAir;
    let proof = prove_inner_for_air(&air, matrix, &pis);
    verify_inner_for_air(&air, &proof, &pis)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;
    Ok((proof, pis))
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
    prove_chain_core(&refs, &selectors)
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
    prove_chain_core(&refs, claimed_selectors)
}

/// The shared fold core (steps 2-6 of [`prove_turn_chain_recursive`]).
fn prove_chain_core(
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
    // (2) host-side continuity + the binding witness.
    let (_, chain_pis, chain_digest) = generate_chain_trace(turns)?;
    let genesis_root = chain_pis[0];
    let final_root = chain_pis[1];

    let config = create_recursion_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // (3) chain-binding leaf.
    let (binding_inner, binding_pis) = prove_chain_binding_leaf(turns)?;

    // (4)+(5) one REAL descriptor leaf per finalized turn, each re-proven over
    // its own execution trace and wrapped uni->batch (verified in-circuit).
    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(turns.len() + 1);

    for (i, t) in turns.iter().enumerate() {
        let (air, leaf_inner, leaf_pis) = prove_descriptor_leaf(t, selectors[i])
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        let p3_pis: Vec<P3BabyBear> = leaf_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &leaf_inner,
            air: &air,
            public_inputs: p3_pis,
            preprocessed_commit: None,
        };
        let wrapped =
            build_and_prove_next_layer::<DreggRecursionConfig, EffectVmDescriptorAir, _, D>(
                &input, &config, &backend, &params,
            )
            .map_err(|e| TurnChainError::TurnProofInvalid {
                index: i,
                reason: format!("recursive descriptor leaf failed: {e:?}"),
            })?;
        batch_leaves.push(wrapped);
    }

    // The chain-binding leaf wrapped uni->batch.
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

    // (6) Pairwise-aggregate up a binary tree to ONE root batch proof.
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

    // (2) Claimed publics, read against the carried binding proof.
    let claimed_pis = vec![
        proof.genesis_root,
        proof.final_root,
        BabyBear::new(proof.num_turns as u32),
        proof.chain_digest,
    ];
    verify_inner_for_air(&TurnChainBindingAir, &proof.binding_proof, &claimed_pis)
        .map_err(|reason| TurnChainError::ClaimedPublicsUnattested { reason })?;

    // (3) The root.
    verify_recursive_batch_proof(&proof.root.0)
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
    prove_chain_core(&window, &selectors)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm::columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE, state};
    use crate::effect_vm::{CellState, EFFECT_VM_WIDTH, Effect, generate_effect_vm_trace, pi, sel};
    use crate::field::BabyBear;
    use crate::lean_descriptor_air::prove_vm_descriptor;

    /// Build a REAL finalized turn on the production descriptor path: execute a
    /// `Transfer` of `amount` (direction 1 = debit) from `(balance, nonce)`,
    /// prove the 186-column trace through the Lean transfer descriptor
    /// (`prove_vm_descriptor`, the audited p3 batch prover — the SAME wire
    /// artifact the SDK cutover path emits), and carry the trace as the leaf
    /// witness. Returns the finalized turn plus its REAL `(old_root, new_root)`
    /// — the genuine Poseidon2 state commitments the trace generator derives,
    /// NOT fabricated values (the descriptor's hash sites bind them to the
    /// trace, so they cannot be overridden).
    fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount,
            direction: 1,
        }];
        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let old_root = public_inputs[pi::OLD_COMMIT];
        let new_root = public_inputs[pi::NEW_COMMIT];
        let json = descriptor_for_selector(sel::TRANSFER).expect("transfer descriptor registered");
        let desc = parse_vm_descriptor(json).expect("transfer descriptor parses");
        let dpis = &public_inputs[..desc.public_input_count];
        let proof =
            prove_vm_descriptor(&desc, &trace, dpis).expect("descriptor proves honest transfer");
        (
            FinalizedTurn::new(
                DescriptorParticipant {
                    proof,
                    public_inputs,
                },
                trace,
            ),
            old_root,
            new_root,
        )
    }

    /// Build a continuous chain of `k` real finalized turns: each turn debits
    /// `step` from the balance and the next turn starts from the post-state, so
    /// turn i's real `new_root` is turn i+1's real `old_root`. Returns the turns
    /// plus the genesis and final roots.
    fn make_chain(
        start_balance: u64,
        start_nonce: u32,
        step: u64,
        k: usize,
    ) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
        let mut turns = Vec::with_capacity(k);
        let mut balance = start_balance;
        let mut nonce = start_nonce;
        let mut genesis = BabyBear::ZERO;
        let mut final_root = BabyBear::ZERO;
        for i in 0..k {
            let (turn, old_root, new_root) = make_turn(balance, nonce, step);
            if i == 0 {
                genesis = old_root;
            } else {
                // The previous turn's post-state IS this turn's pre-state, so the
                // real commitments must already chain.
                assert_eq!(
                    old_root, final_root,
                    "turn {i} old_root must equal previous new_root (real chain)"
                );
            }
            final_root = new_root;
            turns.push(turn);
            balance -= step;
            nonce += 1; // one non-NoOp (Transfer) row bumps the nonce by 1.
        }
        (turns, genesis, final_root)
    }

    fn refs(turns: &[FinalizedTurn]) -> Vec<&FinalizedTurn> {
        turns.iter().collect()
    }

    /// GOLD whole-chain: fold K=3 REAL finalized turns — REAL descriptor leaves,
    /// each the full `EffectVmDescriptorAir` constraint set re-proven over its
    /// own execution trace and verified IN-CIRCUIT by the wrap layer — into ONE
    /// recursive proof that verifies. Each turn's real post-state commitment is
    /// the next turn's real pre-state commitment (genesis -> r1 -> r2 -> final).
    /// The verifier checks only the root (+ the VK pin and the carried binding
    /// attestation).
    ///
    /// Piggybacked REFUSED cases (no extra proving): a mismatched VK anchor is
    /// refused, and RELABELED carried publics (final_root / chain_digest /
    /// num_turns / genesis_root spliced after the fold) are refused by the
    /// claimed-publics attestation — the verify path now reads the publics
    /// against the carried binding proof instead of trusting bare fields.
    #[test]
    fn k_fold_turn_chain_proves_and_verifies() {
        let (turns, genesis, final_root) = make_chain(1000, 0, 7, 3);
        assert_eq!(turns.len(), 3);

        let mut whole = prove_turn_chain_recursive(&turns)
            .expect("a continuous 3-turn finalized chain must fold recursively");
        assert_eq!(whole.num_turns, 3);
        assert_eq!(whole.genesis_root, genesis);
        assert_eq!(whole.final_root, final_root);

        // The trust anchor an honest setup would distribute.
        let vk = whole.root_vk_fingerprint();
        verify_turn_chain_recursive(&whole, &vk)
            .expect("the whole-chain root proof must verify under its honest anchor");

        // REFUSED: a mismatched VK anchor (the caller pinned a different circuit).
        let mut wrong = vk;
        wrong.0[0] ^= 0xFF;
        match verify_turn_chain_recursive(&whole, &wrong) {
            Err(TurnChainError::VkFingerprintMismatch { .. }) => {}
            other => panic!("a mismatched VK anchor must be refused; got {other:?}"),
        }

        // REFUSED: relabeled final_root (splicing a foreign endpoint onto the artifact).
        let honest_final = whole.final_root;
        whole.final_root = honest_final + BabyBear::ONE;
        match verify_turn_chain_recursive(&whole, &vk) {
            Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
            other => panic!("a relabeled final_root must be refused; got {other:?}"),
        }
        whole.final_root = honest_final;

        // REFUSED: relabeled chain_digest (claiming a different ordered history).
        let honest_digest = whole.chain_digest;
        whole.chain_digest = honest_digest + BabyBear::ONE;
        match verify_turn_chain_recursive(&whole, &vk) {
            Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
            other => panic!("a relabeled chain_digest must be refused; got {other:?}"),
        }
        whole.chain_digest = honest_digest;

        // REFUSED: relabeled num_turns (the binding proof Fiat–Shamir-binds pv[2]
        // even though the AIR leaves it unconstrained).
        let honest_n = whole.num_turns;
        whole.num_turns = honest_n + 1;
        match verify_turn_chain_recursive(&whole, &vk) {
            Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
            other => panic!("a relabeled num_turns must be refused; got {other:?}"),
        }
        whole.num_turns = honest_n;

        // REFUSED: relabeled genesis_root.
        let honest_genesis = whole.genesis_root;
        whole.genesis_root = honest_genesis + BabyBear::ONE;
        match verify_turn_chain_recursive(&whole, &vk) {
            Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
            other => panic!("a relabeled genesis_root must be refused; got {other:?}"),
        }
        whole.genesis_root = honest_genesis;

        // And the restored artifact still verifies (the refusals were the lies,
        // not collateral damage).
        verify_turn_chain_recursive(&whole, &vk)
            .expect("the restored honest artifact must verify again");
    }

    /// **THE VK-PIN TOOTH (from-scratch prover, REFUSED).** Today's exact hole,
    /// closed: `verify_recursive_batch_proof` reconstructs circuit common data
    /// FROM the proof, so ANY valid recursive proof — here a wrap of the
    /// unrelated `AggregationAir` — passes the bare root check. The pinned
    /// verifier must refuse it: its verifier-key fingerprint is not the chain
    /// fold's. Both halves are asserted: the bare engine ACCEPTS the foreign
    /// root (showing the pin is load-bearing, not redundant), and
    /// `verify_turn_chain_recursive` REFUSES it with `VkFingerprintMismatch`.
    #[test]
    fn foreign_circuit_root_is_refused_by_vk_pin() {
        use crate::plonky3_recursion::AggregationAir;

        // An honest K=2 fold (the artifact whose carried publics + binding proof
        // the attacker will try to pair with a foreign root).
        let (turns, _g, _f) = make_chain(1000, 0, 7, 2);
        let mut whole =
            prove_turn_chain_recursive(&turns).expect("the honest 2-turn chain must fold");
        let vk = whole.root_vk_fingerprint();
        verify_turn_chain_recursive(&whole, &vk).expect("honest artifact verifies");

        // A from-scratch prover's root: a perfectly VALID recursive proof — of a
        // DIFFERENT circuit (the AggregationAir smoke wrap).
        let foreign = {
            use crate::plonky3_recursion_impl::recursive::prove_recursive_layer_for_air;
            use p3_field::PrimeCharacteristicRing;
            let pv1 = P3BabyBear::from_u64(0xC0FFEE);
            let rows: Vec<P3BabyBear> = vec![
                P3BabyBear::ZERO,
                P3BabyBear::from_u64(1),
                P3BabyBear::from_u64(2),
                P3BabyBear::from_u64(10),
                P3BabyBear::from_u64(10),
                P3BabyBear::from_u64(3),
                P3BabyBear::from_u64(4),
                P3BabyBear::from_u64(20),
                P3BabyBear::from_u64(20),
                P3BabyBear::from_u64(5),
                P3BabyBear::from_u64(6),
                P3BabyBear::from_u64(30),
                P3BabyBear::from_u64(30),
                P3BabyBear::from_u64(7),
                P3BabyBear::from_u64(8),
                pv1,
            ];
            let matrix = RowMajorMatrix::new(rows, 4);
            let pis = vec![BabyBear::ZERO, BabyBear::new(0xC0FFEE)];
            let air = AggregationAir;
            let inner = prove_inner_for_air(&air, matrix, &pis);
            prove_recursive_layer_for_air(&air, &inner, &pis)
                .expect("the foreign AIR wraps fine — it is a VALID recursive proof")
        };

        // The bare engine check ACCEPTS the foreign root — the exact reason the
        // pin exists.
        verify_recursive_batch_proof(&foreign.0)
            .expect("the bare engine accepts ANY valid recursive proof — the pre-pin hole");

        // Splice the foreign root under the honest carried publics/binding.
        whole.root = foreign;
        match verify_turn_chain_recursive(&whole, &vk) {
            Err(TurnChainError::VkFingerprintMismatch { .. }) => {}
            Ok(()) => panic!("a foreign circuit's root must NOT verify as the chain fold"),
            Err(other) => panic!("expected VkFingerprintMismatch, got {other:?}"),
        }
    }

    /// TEMPORAL TOOTH (host): a turn whose real old_root != previous new_root
    /// breaks the finalized order and is rejected at the chain check — before any
    /// tree. We splice an out-of-sequence turn (a fresh chain's turn, whose
    /// pre-state commitment does not match) into the middle.
    #[test]
    fn broken_order_rejected() {
        let (mut turns, _g, _f) = make_chain(1000, 0, 7, 3);
        // Replace turn 1 with a turn from an UNRELATED chain (different starting
        // balance), so its real old_root does not continue turn 0's new_root.
        let (foreign, foreign_old, _foreign_new) = make_turn(500, 50, 3);
        let prev_new = turns[0].new_root();
        assert_ne!(
            foreign_old, prev_new,
            "the foreign turn must NOT continue the chain (that is the point)"
        );
        turns[1] = foreign;

        match prove_turn_chain_recursive(&turns) {
            Err(TurnChainError::ChainBreak {
                index,
                expected_old_root,
                found_old_root,
            }) => {
                assert_eq!(index, 1);
                assert_eq!(expected_old_root, prev_new.0);
                assert_eq!(found_old_root, foreign_old.0);
            }
            Ok(_) => panic!("a broken finalized order must not produce a whole-chain proof"),
            Err(other) => panic!("expected ChainBreak, got {other:?}"),
        }
    }

    /// TEMPORAL TOOTH (circuit): even bypassing the host check, the
    /// `TurnChainBindingAir` continuity constraint makes a reordered trace
    /// UNSAT. We build the binding trace for a broken order and confirm the
    /// inner proof fails to verify (or the prover refuses it in debug).
    #[test]
    fn broken_order_unsat_in_circuit() {
        let (mut turns, _g, _f) = make_chain(1000, 0, 7, 2);
        let (foreign, _fo, _fn) = make_turn(500, 50, 3);
        turns[1] = foreign; // breaks continuity

        let (trace, pis) = generate_chain_trace_unchecked(&refs(&turns));
        // row 0 new_root != row 1 old_root -> continuity broken.
        assert_ne!(trace[0][1], trace[1][0], "the spliced order must be broken");

        let air = TurnChainBindingAir;
        let matrix = trace_to_matrix(&trace);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let inner = prove_inner_for_air(&air, matrix, &pis);
            verify_inner_for_air(&air, &inner, &pis)
        }));

        let rejected = match result {
            Ok(Ok(())) => false, // verified a broken chain — soundness hole!
            Ok(Err(_)) => true,  // verifier rejected.
            Err(_) => true,      // prover panicked on unsatisfiable trace.
        };
        assert!(
            rejected,
            "a reordered finalized chain must be UNSAT under TurnChainBindingAir continuity"
        );
    }

    /// **THE LEAF TOOTH (host-gate-skipping prover, forged post-commit).** The
    /// claim this module makes is that per-turn execution soundness does NOT
    /// rest on the prover having run the host-side descriptor admission. So:
    /// run the UNGATED prover on a chain whose second turn LIES about its
    /// post-state root in the PIs (the execution trace is honest; only the
    /// claimed `NEW_COMMIT` is forged — exactly the lie a malicious prover
    /// would tell to advance the chain to a state that never happened). The
    /// descriptor AIR's PI binding + Poseidon2 state-commit hash sites make
    /// that leaf UNSATISFIABLE, so the in-circuit re-proof fails and NO
    /// verifying root can be produced — the host gate was never load-bearing.
    #[test]
    fn ungated_prover_with_forged_post_commit_cannot_produce_a_root() {
        let (t0, _o0, n0) = make_turn(1000, 0, 7);
        let (mut t1, o1, n1) = make_turn(993, 1, 7);
        assert_eq!(o1, n0, "honest turns chain by construction");

        // The PI lie: claim a post-state root that execution never reached.
        let lie = n1 + BabyBear::ONE;
        t1.participant.public_inputs[pi::NEW_COMMIT] = lie;
        let turns = [t0, t1];

        // (a) The GATED prover rejects at host admission (the forged PIs no
        //     longer verify the production descriptor proof).
        match prove_turn_chain_recursive(&turns) {
            Err(TurnChainError::TurnProofInvalid { index, .. }) => assert_eq!(index, 1),
            Ok(_) => panic!("the gated prover accepted a forged post-commit"),
            Err(other) => panic!("expected TurnProofInvalid at the host gate, got {other:?}"),
        }

        // (b) THE TOOTH: the UNGATED prover — which never runs the host gate —
        //     must ALSO fail, at the in-circuit leaf. The unsatisfiable leaf
        //     surfaces as a prover panic (debug: check_constraints refuses) or
        //     an Err (release: self-verify rejects). Either is "no root".
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_turn_chain_recursive_without_host_gate(&turns, &[sel::TRANSFER, sel::TRANSFER])
        }));
        let rejected = match result {
            Ok(Ok(_)) => false, // a verifying root for a forged turn — soundness hole!
            Ok(Err(_)) => true,
            Err(_) => true,
        };
        assert!(
            rejected,
            "a host-gate-skipping prover with a forged post-commit must NOT obtain a \
             whole-chain root — the descriptor leaf is the in-circuit tooth"
        );
    }

    /// **THE LEAF TOOTH (host-gate-skipping prover, stub leaf).** The
    /// pre-cutover fold wrapped fabricated `EffectVmShapeAir`-style passthrough
    /// traces as leaves; its own docs admitted such a trace would NOT pass the
    /// full Effect VM AIR. This test pins that a prover trying exactly that
    /// against TODAY's fold fails: a fabricated 186-column passthrough stub
    /// (selector row + NoOp rows, claimed roots written into the state-commit
    /// cells) does not satisfy the REAL descriptor constraint set (the hash
    /// sites force the commit cells to be genuine Poseidon2 digests of the
    /// row's state, which the stub's are not), so the ungated fold refuses and
    /// no root exists.
    #[test]
    fn ungated_prover_with_stub_leaf_cannot_produce_a_root() {
        let (t0, _o0, n0) = make_turn(1000, 0, 7);
        // A donor proof object for the stub participant: the attacker has SOME
        // bytes to put in the proof slot (the ungated path never inspects them);
        // soundness must come from the in-circuit leaf, not the proof slot.
        let (donor, _do, _dn) = make_turn(500, 50, 3);

        // The stub: claim to continue n0 -> n0+1 with a fabricated passthrough
        // trace (the OLD shape-stub recipe at the real 186-column width).
        let claimed_old = n0;
        let claimed_new = n0 + BabyBear::ONE;
        let mut stub_trace: Vec<Vec<BabyBear>> = Vec::with_capacity(4);
        let mut row0 = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row0[sel::TRANSFER] = BabyBear::ONE;
        row0[STATE_BEFORE_BASE + state::STATE_COMMIT] = claimed_old;
        row0[STATE_AFTER_BASE + state::STATE_COMMIT] = claimed_new;
        stub_trace.push(row0);
        for _ in 1..4 {
            let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
            row[sel::NOOP] = BabyBear::ONE;
            row[STATE_BEFORE_BASE + state::STATE_COMMIT] = claimed_new;
            row[STATE_AFTER_BASE + state::STATE_COMMIT] = claimed_new;
            stub_trace.push(row);
        }
        let mut stub_pis = vec![BabyBear::ZERO; pi::BASE_COUNT];
        stub_pis[pi::OLD_COMMIT] = claimed_old;
        stub_pis[pi::NEW_COMMIT] = claimed_new;

        let stub_turn = FinalizedTurn::new(
            DescriptorParticipant {
                proof: donor.participant.proof,
                public_inputs: stub_pis,
            },
            stub_trace,
        );
        let turns = [t0, stub_turn];

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_turn_chain_recursive_without_host_gate(&turns, &[sel::TRANSFER, sel::TRANSFER])
        }));
        let rejected = match result {
            Ok(Ok(_)) => false, // a verifying root over a stub leaf — soundness hole!
            Ok(Err(_)) => true,
            Err(_) => true,
        };
        assert!(
            rejected,
            "a host-gate-skipping prover wrapping a fabricated stub leaf must NOT obtain \
             a whole-chain root — the descriptor constraint set is what the leaf proves"
        );
    }

    /// **THE IN-CIRCUIT WRAP TOOTH (the load-bearing one).** A descriptor leaf
    /// honestly proven for its real `(old_root, new_root)` but fed to the
    /// recursive verifier layer with public inputs claiming a FORGED post-state
    /// root. The wrap layer's IN-CIRCUIT verifier pins the claimed PIs against
    /// the proof, so the mismatched-PI leaf is unsatisfiable and
    /// `build_and_prove_next_layer` MUST fail. This proves the rejection is the
    /// recursion itself — even a "valid proof object" cannot be re-labelled
    /// with different chain roots at the wrap.
    #[test]
    fn recursive_layer_rejects_forged_leaf_public_inputs() {
        let (t, _o, _n) = make_turn(1000, 0, 7);
        let (air, inner, dpis) =
            prove_descriptor_leaf(&t, sel::TRANSFER).expect("honest descriptor leaf proves");

        let config = create_recursion_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        // FORGE the post-state root in the PIs fed to the wrap layer.
        let mut forged = dpis.clone();
        forged[pi::NEW_COMMIT] = forged[pi::NEW_COMMIT] + BabyBear::ONE;
        let p3_forged: Vec<P3BabyBear> = forged.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &inner,
            air: &air,
            public_inputs: p3_forged,
            preprocessed_commit: None,
        };

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            build_and_prove_next_layer::<DreggRecursionConfig, EffectVmDescriptorAir, _, D>(
                &input, &config, &backend, &params,
            )
        }));
        let rejected = match result {
            Ok(Ok(_)) => false, // wrapped a forged-PI leaf — soundness hole!
            Ok(Err(_)) => true, // recursion returned an error — rejected.
            Err(_) => true,     // unsatisfiable verifier circuit panicked — rejected.
        };
        assert!(
            rejected,
            "a descriptor leaf fed forged chain roots must be rejected by the IN-CIRCUIT \
             recursive verifier — the recursion, not the host check, is the tooth"
        );
    }

    /// 2-step inductive core: fold_two_turns over a continuous pair yields a
    /// verifying whole-chain proof of the 2-turn window (the unbounded loop's
    /// inductive step).
    #[test]
    fn two_step_inductive_core_proves_and_verifies() {
        let (turns, genesis, final_root) = make_chain(1000, 0, 11, 2);

        let folded =
            fold_two_turns(&turns[0], &turns[1]).expect("a continuous pair must fold via the core");
        assert_eq!(folded.num_turns, 2);
        assert_eq!(folded.genesis_root, genesis);
        assert_eq!(folded.final_root, final_root);
        let vk = folded.root_vk_fingerprint();
        verify_turn_chain_recursive(&folded, &vk).expect("the 2-step folded proof must verify");
    }

    /// fold_two_turns rejects a discontinuous pair (the inductive step refuses
    /// to extend the running chain with a turn that does not consume its root).
    #[test]
    fn two_step_core_rejects_discontinuity() {
        let (running, _o, _n) = make_turn(1000, 0, 11);
        let (bad_next, _bo, _bn) = make_turn(500, 50, 3); // unrelated chain

        match fold_two_turns(&running, &bad_next) {
            Err(TurnChainError::ChainBreak { index, .. }) => assert_eq!(index, 1),
            Ok(_) => panic!("a discontinuous pair must not fold"),
            Err(other) => panic!("expected ChainBreak, got {other:?}"),
        }
    }
}

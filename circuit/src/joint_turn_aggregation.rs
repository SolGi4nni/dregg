//! Cross-cell joint-turn aggregation: ONE proof binding N per-cell whole-turn
//! proofs of a SINGLE shared turn (the Silver -> Gold step).
//!
//! ## What this is, and how it differs from `proof_forest`
//!
//! [`proof_forest`](crate::proof_forest) links per-step proofs *sequentially*
//! inside one cell (`prev.NEW_COMMIT == next.OLD_COMMIT`). That is the
//! happened-before chain *within* a cell's history. It explicitly does **not**
//! do cross-cell binding (its own docs: "no cross-cell `Σδ = 0` family
//! binding").
//!
//! This module does the **orthogonal** thing the metatheory calls the
//! *hyperedge* / `SharedTurnId` pullback (`Dregg2.Spec.JointViaHyper`,
//! `Dregg2.Hyperedge`): take 2+ per-cell whole-turn proofs that all claim to be
//! participants of the **same** turn, and produce ONE aggregated proof that
//! verifies them together **and** binds their shared turn identity (CG-2 of the
//! hyperedge: every leg agrees on `tid`). Per-cell soundness alone cannot supply
//! this — two individually-valid proofs from *different* turns must be rejected.
//! That rejection is exactly the cross-cell binding's load-bearing content.
//!
//! ## The aggregation AIR
//!
//! [`JointTurnAggregationAir`] is a uni-STARK AIR over a width-4 trace, one row
//! per participating cell:
//!
//! - col 0: `shared_turn_id`  — the turn identity this cell's proof attests
//!   (the `TURN_HASH` public input, projected to one felt). The wide-pullback
//!   apex: **every row must carry the same value** (CG-2).
//! - col 1: `cell_commit`     — this cell's post-state commitment (`NEW_COMMIT`
//!   position 0), the per-cell content folded into the bundle digest.
//! - col 2: `acc_in`          — commitment hash-chain state before this row.
//! - col 3: `acc_out = hash_4_to_1([acc_in, shared_turn_id, cell_commit, idx])`
//!   — the running bundle digest.
//!
//! Public inputs `[shared_turn_id, initial_acc(=0), final_acc]`.
//!
//! Constraints:
//!   1. (CG-2, the cross-cell binding) **every** row's `shared_turn_id` equals
//!      the published `shared_turn_id` public input.  ← rejects mismatched turns
//!   2. first row `acc_in == initial_acc (== 0)`.
//!   3. last row `acc_out == final_acc`.
//!   4. chain continuity `acc_out[i] == acc_in[i+1]`.
//!
//! Constraint 1 is the tooth: a bundle whose cells disagree on the turn id (or
//! disagree with the published id) is UNSAT, even when every per-cell proof is
//! individually valid. That is precisely "validity != joint membership" — the
//! `SharedTurnId` pullback enforced at the apex.
//!
//! ## Silver vs Gold
//!
//! - **Silver** ([`prove_joint_turn`] / [`verify_joint_turn`]): a bundle =
//!   {per-cell proofs} + the aggregation proof. The aggregation proof is a
//!   single constant-size STARK binding the shared-turn-id agreement and the
//!   commitment digest; the per-cell proofs are still carried for full
//!   soundness. This is the deliverable.
//! - **Gold** (`recursion` feature, [`prove_joint_turn_recursive`]): the
//!   aggregation AIR is additionally wrapped in ONE recursive in-circuit STARK
//!   layer via the emberian `plonky3-recursion` fork, so the verifier checks a
//!   single succinct recursive proof instead of re-running the aggregation
//!   prover. The per-cell inner proofs are verified through the same engine.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use crate::effect_vm::EffectVmAir;
use crate::effect_vm::pi;
use crate::field::BabyBear;
use crate::plonky3_prover::{DreggProof, create_config, to_p3};
use crate::poseidon2::hash_4_to_1;
use crate::stark::{self, StarkProof};

// ============================================================================
// One participant in a joint turn: a per-cell whole-turn proof + its PI.
// ============================================================================

/// A single cell's whole-turn proof, as a participant in a joint (cross-cell)
/// turn. The proof is a real EffectVm whole-turn STARK (the same production path
/// `proof_forest` uses). The public inputs are the full EffectVm PI vector this
/// proof attests; the aggregator reads [`pi::TURN_HASH_BASE`] (shared turn id)
/// and [`pi::NEW_COMMIT_BASE`] (post-state commitment) out of it.
pub struct JointParticipant {
    /// The per-cell whole-turn EffectVm STARK proof.
    pub proof: StarkProof,
    /// The full EffectVm public-input vector this proof attests.
    pub public_inputs: Vec<BabyBear>,
}

/// Verify one participant's per-cell whole-turn proof under the EffectVm AIR
/// reconstructed from the proof's declared trace height (matching
/// `proof_forest::verify_forest`'s per-proof seam).
fn verify_participant(p: &JointParticipant) -> Result<(), String> {
    let air = EffectVmAir::new(p.proof.trace_len);
    stark::verify(&air, &p.proof, &p.public_inputs)
}

/// Public re-export of the per-cell whole-turn soundness check, so the
/// whole-chain IVC accumulator ([`crate::ivc_turn_chain`]) reuses exactly the
/// same per-turn admission discipline.
pub fn verify_participant_pub(p: &JointParticipant) -> Result<(), String> {
    verify_participant(p)
}

// ============================================================================
// DESCRIPTOR-BACKED PARTICIPANT — the ONE-circuit cutover of the joint-turn seam.
// ============================================================================
//
// `verify_participant` above is the LEGACY per-cell soundness seam: it verifies a
// bespoke-`stark` `EffectVmAir` proof. The ONE-circuit migration re-points the
// joint-turn consumer's per-cell admission onto the verified-by-construction Lean
// DESCRIPTOR INTERPRETER for the GRADUATED single-effect selectors. A descriptor
// participant carries an `EffectVmP3Proof` (the SAME wire type the SDK production
// prove-path emits), verified SELECTOR-BOUND through the descriptor verifier (the
// Lean `selectorGate s` tooth makes a sound proof verify under EXACTLY ONE
// selector — the differential harness's `descriptor_proof_binds_to_its_selector`).
// The CG-2 shared-turn-id binding and the bundle-digest aggregation are UNCHANGED
// (they read the same PI projections), so the cross-cell tooth holds identically;
// only the per-cell crypto seam swaps from the hand-AIR to the descriptor circuit.
// The bespoke `verify_participant` is RETAINED as the transitional guard.

/// A single cell's whole-turn DESCRIPTOR-INTERPRETER proof as a joint-turn
/// participant. The proof is an `EffectVmP3Proof` (audited p3 batch-stark, the
/// production cutover wire type); the PI projections the aggregator reads
/// ([`pi::TURN_HASH_BASE`], [`pi::NEW_COMMIT_BASE`]) are identical to
/// [`JointParticipant`]'s.
pub struct DescriptorParticipant {
    /// The per-cell whole-turn descriptor-interpreter proof.
    pub proof: crate::effect_vm_p3_full_air::EffectVmP3Proof,
    /// The full EffectVM public-input vector this proof attests.
    pub public_inputs: Vec<BabyBear>,
}

impl DescriptorParticipant {
    /// The shared turn identity this participant claims (`TURN_HASH` position 0).
    pub fn shared_turn_id(&self) -> BabyBear {
        self.public_inputs[pi::TURN_HASH_BASE]
    }

    /// This cell's post-state commitment (`NEW_COMMIT` position 0).
    pub fn cell_commit(&self) -> BabyBear {
        self.public_inputs[pi::NEW_COMMIT_BASE]
    }
}

/// Verify one descriptor participant's per-cell proof SELECTOR-BOUND through the
/// descriptor interpreter (the cutover replacement for [`verify_participant`]). A
/// sound descriptor proof verifies under EXACTLY ONE cutover selector — its own
/// effect; zero (not a graduated descriptor proof) or multiple (ambiguous, must not
/// happen with the gate in place) are rejected. Returns the bound selector.
pub fn verify_descriptor_participant(p: &DescriptorParticipant) -> Result<usize, String> {
    use crate::effect_vm_descriptors::descriptor_for_selector;
    use crate::lean_descriptor_air::{parse_vm_descriptor, verify_vm_descriptor};

    let mut bound: Vec<usize> = Vec::new();
    for &s in crate::proof_forest::CUTOVER_READY_SELECTORS {
        if let Some(json) = descriptor_for_selector(s) {
            if let Ok(desc) = parse_vm_descriptor(json) {
                if p.public_inputs.len() >= desc.public_input_count {
                    let dpis = &p.public_inputs[..desc.public_input_count];
                    if verify_vm_descriptor(&desc, &p.proof, dpis).is_ok() {
                        bound.push(s);
                    }
                }
            }
        }
    }
    match bound.as_slice() {
        [only] => Ok(*only),
        [] => Err("descriptor participant verified under NO cutover selector".into()),
        multi => Err(format!(
            "descriptor participant verified under MULTIPLE cutover selectors {multi:?} — ambiguous"
        )),
    }
}

/// CG-2 host check + per-cell descriptor soundness over descriptor participants —
/// the cutover analogue of the precondition gate in [`prove_joint_turn`]. Verifies
/// (1) `>= 2` participants, (2) each per-cell proof verifies selector-bound through
/// the descriptor interpreter, (3) all participants agree on the shared turn id.
/// Returns the agreed shared turn id. (The aggregation trace/proof is shape-identical
/// to the Silver path and is produced from the same PI projections.)
pub fn check_descriptor_joint_preconditions(
    participants: &[DescriptorParticipant],
) -> Result<BabyBear, JointAggError> {
    if participants.len() < 2 {
        return Err(JointAggError::TooFewParticipants {
            count: participants.len(),
        });
    }
    for (i, p) in participants.iter().enumerate() {
        verify_descriptor_participant(p).map_err(|e| {
            JointAggError::ParticipantProofInvalid {
                index: i,
                reason: e,
            }
        })?;
    }
    let shared_tid = participants[0].shared_turn_id();
    for (i, p) in participants.iter().enumerate() {
        if p.shared_turn_id() != shared_tid {
            return Err(JointAggError::SharedTurnIdMismatch {
                index: i,
                expected: shared_tid.0,
                found: p.shared_turn_id().0,
            });
        }
    }
    Ok(shared_tid)
}

impl JointParticipant {
    /// The shared turn identity this participant claims (`TURN_HASH` position 0).
    /// Every participant of one joint turn MUST agree on this value — the
    /// `SharedTurnId` pullback / hyperedge CG-2.
    pub fn shared_turn_id(&self) -> BabyBear {
        self.public_inputs[pi::TURN_HASH_BASE]
    }

    /// This cell's post-state commitment (`NEW_COMMIT` position 0) — the
    /// per-cell content folded into the bundle digest.
    pub fn cell_commit(&self) -> BabyBear {
        self.public_inputs[pi::NEW_COMMIT_BASE]
    }

    /// The minimal PI length needed to carry both projections.
    fn min_pi_len() -> usize {
        // TURN_HASH_BASE + TURN_HASH_LEN and NEW_COMMIT_BASE + NEW_COMMIT_LEN;
        // TURN_HASH is the larger offset.
        (pi::TURN_HASH_BASE + pi::TURN_HASH_LEN).max(pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN)
    }
}

// ============================================================================
// JointTurnAggregationAir
// ============================================================================

/// AIR binding the shared-turn-id agreement (CG-2) across N per-cell proofs and
/// folding their commitments into a single bundle digest.
///
/// Width 4: `[shared_turn_id, cell_commit, acc_in, acc_out]`.
/// Public inputs: `[shared_turn_id, initial_acc, final_acc]`.
pub struct JointTurnAggregationAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for JointTurnAggregationAir {
    fn width(&self) -> usize {
        4
    }

    fn num_public_values(&self) -> usize {
        3 // [shared_turn_id, initial_acc, final_acc]
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        (0..4).collect()
    }
}

impl<AB: AirBuilder> Air<AB> for JointTurnAggregationAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let row_tid: AB::Expr = local[0].into();
        let acc_in: AB::Expr = local[2].into();
        let acc_out: AB::Expr = local[3].into();
        let next_acc_in: AB::Expr = next[2].into();

        let public_values = builder.public_values();
        let pub_tid: AB::Expr = public_values[0].into();
        let initial_acc: AB::Expr = public_values[1].into();
        let final_acc: AB::Expr = public_values[2].into();

        // Constraint 1 (CG-2, THE cross-cell binding): EVERY row's shared_turn_id
        // equals the published shared turn id. A bundle whose any cell disagrees
        // on the turn id is UNSAT, regardless of per-cell validity. This is the
        // `SharedTurnId` pullback / hyperedge apex agreement.
        builder.assert_zero(row_tid - pub_tid);

        // Constraint 2: first row accumulator is the initial value.
        builder
            .when_first_row()
            .assert_zero(acc_in.clone() - initial_acc);

        // Constraint 3: last row accumulator_out is the final digest.
        builder
            .when_last_row()
            .assert_zero(acc_out.clone() - final_acc);

        // Constraint 4: chain continuity (acc_out[i] == acc_in[i+1]).
        builder.when_transition().assert_zero(acc_out - next_acc_in);
    }
}

// ============================================================================
// Trace generation
// ============================================================================

/// Build the aggregation trace + public inputs for a sequence of participants.
///
/// Returns `Err` if the participants disagree on the shared turn id — i.e. the
/// `SharedTurnId` pullback is violated at the witness level (we surface it here
/// rather than handing the prover an unsatisfiable trace, but the AIR rejects it
/// too: see [`generate_joint_trace_unchecked`] used by the negative test).
fn generate_joint_trace(
    participants: &[JointParticipant],
) -> Result<(Vec<[BabyBear; 4]>, Vec<BabyBear>, BabyBear), JointAggError> {
    if participants.len() < 2 {
        return Err(JointAggError::TooFewParticipants {
            count: participants.len(),
        });
    }
    let shared_tid = participants[0].shared_turn_id();
    for (i, p) in participants.iter().enumerate() {
        if p.shared_turn_id() != shared_tid {
            return Err(JointAggError::SharedTurnIdMismatch {
                index: i,
                expected: shared_tid.0,
                found: p.shared_turn_id().0,
            });
        }
    }
    let (trace, pis) = generate_joint_trace_unchecked(participants, shared_tid);
    Ok((trace, pis, shared_tid))
}

/// Build the trace WITHOUT the witness-level shared-tid check. The AIR's
/// constraint 1 still enforces agreement; this is the entry point the negative
/// test uses to confirm the *circuit* (not just the host check) rejects a
/// tampered turn id.
fn generate_joint_trace_unchecked(
    participants: &[JointParticipant],
    published_tid: BabyBear,
) -> (Vec<[BabyBear; 4]>, Vec<BabyBear>) {
    let n = participants.len();
    let padded_len = n.next_power_of_two().max(2);
    let mut trace: Vec<[BabyBear; 4]> = Vec::with_capacity(padded_len);
    let mut accumulator = BabyBear::ZERO;

    for (i, p) in participants.iter().enumerate() {
        let tid = p.shared_turn_id();
        let commit = p.cell_commit();
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[accumulator, tid, commit, idx]);
        trace.push([tid, commit, accumulator, acc_out]);
        accumulator = acc_out;
    }

    // Pad to power of two. Padding rows carry the published turn id (so
    // constraint 1 still holds on them) with zero commitment, continuing the
    // chain.
    for i in n..padded_len {
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[accumulator, published_tid, BabyBear::ZERO, idx]);
        trace.push([published_tid, BabyBear::ZERO, accumulator, acc_out]);
        accumulator = acc_out;
    }

    let final_acc = trace.last().unwrap()[3];
    let pis = vec![published_tid, BabyBear::ZERO, final_acc];
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
// Shared seams reused by the Gold (recursive) path.
// ============================================================================

/// Run the joint-turn preconditions and return the agreed shared turn id.
///
/// This is the Silver per-cell soundness gate + the host-side CG-2 check,
/// factored out so the Gold (`joint_turn_recursive`) path reuses **exactly**
/// the same admission discipline before building any recursion tree:
///
///   1. `>= 2` participants;
///   2. each participant's PI vector long enough to carry the projections;
///   3. **per-cell soundness** — every per-cell whole-turn proof verifies under
///      the real [`EffectVmAir`] (the first line of the tooth: a tampered
///      participant proof is rejected here, at its index);
///   4. **CG-2** — all participants agree on the shared turn id (a disagreeing
///      cell is rejected with [`JointAggError::SharedTurnIdMismatch`]).
///
/// Returns the shared turn id on success.
pub fn check_joint_preconditions(
    participants: &[JointParticipant],
) -> Result<BabyBear, JointAggError> {
    if participants.len() < 2 {
        return Err(JointAggError::TooFewParticipants {
            count: participants.len(),
        });
    }
    let min_len = JointParticipant::min_pi_len();
    for (i, p) in participants.iter().enumerate() {
        if p.public_inputs.len() < min_len {
            return Err(JointAggError::MalformedPublicInputs {
                index: i,
                len: p.public_inputs.len(),
            });
        }
    }
    // (3) per-cell soundness gate.
    for (i, p) in participants.iter().enumerate() {
        verify_participant(p).map_err(|e| JointAggError::ParticipantProofInvalid {
            index: i,
            reason: e,
        })?;
    }
    // (4) CG-2 host check.
    let shared_tid = participants[0].shared_turn_id();
    for (i, p) in participants.iter().enumerate() {
        if p.shared_turn_id() != shared_tid {
            return Err(JointAggError::SharedTurnIdMismatch {
                index: i,
                expected: shared_tid.0,
                found: p.shared_turn_id().0,
            });
        }
    }
    Ok(shared_tid)
}

/// Build the [`JointTurnAggregationAir`] trace as a `p3` matrix plus its public
/// inputs, for the Gold recursive binding leaf. Mirrors the Silver
/// [`prove_joint_turn`] trace, but hands back a `RowMajorMatrix` so the
/// recursion-compatible prover can consume it directly.
///
/// Errors if the participants disagree on the shared turn id (the same CG-2
/// rejection the Silver path enforces).
pub fn recursion_binding_trace(
    participants: &[JointParticipant],
) -> Result<(RowMajorMatrix<P3BabyBear>, Vec<BabyBear>), JointAggError> {
    let (trace, pis, _shared) = generate_joint_trace(participants)?;
    Ok((trace_to_matrix(&trace), pis))
}

// ============================================================================
// Errors
// ============================================================================

/// Why a joint-turn aggregation failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JointAggError {
    /// Fewer than 2 participants — a joint turn needs at least 2 cells.
    TooFewParticipants {
        /// How many were supplied.
        count: usize,
    },
    /// A participant's PI vector is too short to carry the turn-id / commit
    /// projections.
    MalformedPublicInputs {
        /// The malformed participant.
        index: usize,
        /// Its PI length.
        len: usize,
    },
    /// **The load-bearing rejection.** Participant `index` claims a different
    /// shared turn id than the others — it is NOT a participant of this joint
    /// turn. Per-cell validity does not make it one.
    SharedTurnIdMismatch {
        /// The disagreeing participant.
        index: usize,
        /// The turn id the bundle agreed on (felt as u32).
        expected: u32,
        /// The turn id this participant carried (felt as u32).
        found: u32,
    },
    /// A participant's per-cell proof failed to verify against its public
    /// inputs.
    ParticipantProofInvalid {
        /// The participant whose proof failed.
        index: usize,
        /// The underlying verification error.
        reason: String,
    },
    /// The aggregation STARK proof failed to verify.
    AggregationProofInvalid {
        /// The verification error.
        reason: String,
    },
}

impl core::fmt::Display for JointAggError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            JointAggError::TooFewParticipants { count } => {
                write!(f, "joint turn needs >= 2 participants, got {count}")
            }
            JointAggError::MalformedPublicInputs { index, len } => {
                write!(f, "participant {index} PI malformed: len {len}")
            }
            JointAggError::SharedTurnIdMismatch {
                index,
                expected,
                found,
            } => write!(
                f,
                "participant {index} shared turn id {found} != bundle turn id {expected} \
                 (not a participant of this joint turn)"
            ),
            JointAggError::ParticipantProofInvalid { index, reason } => {
                write!(f, "participant {index} proof invalid: {reason}")
            }
            JointAggError::AggregationProofInvalid { reason } => {
                write!(f, "aggregation proof invalid: {reason}")
            }
        }
    }
}

impl std::error::Error for JointAggError {}

// ============================================================================
// Silver: the joint-turn aggregation bundle.
// ============================================================================

/// The Silver deliverable: ONE aggregation proof binding N per-cell whole-turn
/// proofs of a shared turn, plus the participants (carried for full soundness).
pub struct JointTurnProof {
    /// The single aggregation STARK proof (binds shared-turn-id agreement +
    /// commitment digest). This is the uni-STARK over [`JointTurnAggregationAir`]
    /// (the `plonky3_prover` config), distinct from the per-cell EffectVm proofs.
    pub aggregation_proof: DreggProof,
    /// The per-cell participants (still needed for full verification).
    pub participants: Vec<JointParticipant>,
    /// The shared turn id all participants agree on.
    pub shared_turn_id: BabyBear,
    /// The final bundle digest (commitment to the ordered cell commitments under
    /// the shared turn id).
    pub bundle_digest: BabyBear,
    /// Number of participating cells.
    pub num_cells: usize,
}

/// Prove a joint (cross-cell) turn: aggregate N per-cell whole-turn proofs into
/// ONE proof that binds their shared turn id and folds their commitments.
///
/// Steps:
///   1. structural check (>= 2 participants, PI long enough);
///   2. verify every per-cell proof against its own public inputs;
///   3. witness-level `SharedTurnId` agreement check (CG-2);
///   4. build + prove the [`JointTurnAggregationAir`] trace.
pub fn prove_joint_turn(
    participants: Vec<JointParticipant>,
) -> Result<JointTurnProof, JointAggError> {
    if participants.len() < 2 {
        return Err(JointAggError::TooFewParticipants {
            count: participants.len(),
        });
    }
    let min_len = JointParticipant::min_pi_len();
    for (i, p) in participants.iter().enumerate() {
        if p.public_inputs.len() < min_len {
            return Err(JointAggError::MalformedPublicInputs {
                index: i,
                len: p.public_inputs.len(),
            });
        }
    }

    // (2) Per-cell soundness.
    for (i, p) in participants.iter().enumerate() {
        verify_participant(p).map_err(|e| JointAggError::ParticipantProofInvalid {
            index: i,
            reason: e,
        })?;
    }

    // (3) + trace.
    let (trace, pis, shared_tid) = generate_joint_trace(&participants)?;

    // (4) Prove the aggregation.
    let config = create_config();
    let air = JointTurnAggregationAir;
    let matrix = trace_to_matrix(&trace);
    let p3_public: Vec<P3BabyBear> = pis.iter().map(|&v| to_p3(v)).collect();

    let aggregation_proof = p3_uni_stark::prove(&config, &air, matrix, &p3_public);
    p3_uni_stark::verify(&config, &air, &aggregation_proof, &p3_public).map_err(|e| {
        JointAggError::AggregationProofInvalid {
            reason: format!("{e:?}"),
        }
    })?;

    let bundle_digest = pis[2];
    let num_cells = participants.len();
    Ok(JointTurnProof {
        aggregation_proof,
        participants,
        shared_turn_id: shared_tid,
        bundle_digest,
        num_cells,
    })
}

/// Verify a joint-turn aggregation proof:
///   1. the aggregation STARK verifies against the recomputed public inputs;
///   2. the participants genuinely agree on the shared turn id (recomputed);
///   3. every per-cell proof verifies individually.
///
/// A bundle whose participants disagree on the turn id is rejected at step 2
/// even if each per-cell proof is valid — the cross-cell binding.
pub fn verify_joint_turn(jt: &JointTurnProof) -> Result<(), JointAggError> {
    // (2) recompute the shared-tid agreement + trace (rejects mismatch).
    let (_, pis, shared_tid) = generate_joint_trace(&jt.participants)?;
    if shared_tid != jt.shared_turn_id {
        return Err(JointAggError::SharedTurnIdMismatch {
            index: 0,
            expected: jt.shared_turn_id.0,
            found: shared_tid.0,
        });
    }

    // (1) aggregation proof.
    let config = create_config();
    let air = JointTurnAggregationAir;
    let p3_public: Vec<P3BabyBear> = pis.iter().map(|&v| to_p3(v)).collect();
    p3_uni_stark::verify(&config, &air, &jt.aggregation_proof, &p3_public).map_err(|e| {
        JointAggError::AggregationProofInvalid {
            reason: format!("{e:?}"),
        }
    })?;

    // (3) per-cell soundness.
    for (i, p) in jt.participants.iter().enumerate() {
        verify_participant(p).map_err(|e| JointAggError::ParticipantProofInvalid {
            index: i,
            reason: e,
        })?;
    }
    Ok(())
}

// ============================================================================
// Gold: recursive in-circuit verification of the aggregation layer.
// ============================================================================

#[cfg(feature = "recursion")]
pub mod recursive {
    //! Gold reach: wrap the [`JointTurnAggregationAir`] in ONE recursive
    //! in-circuit STARK layer via the emberian `plonky3-recursion` fork, so the
    //! verifier checks a single succinct recursive proof.

    use super::{
        JointAggError, JointParticipant, JointTurnAggregationAir, generate_joint_trace,
        verify_participant,
    };
    use crate::field::BabyBear;
    use crate::plonky3_recursion_impl::recursive::{
        DreggRecursionConfig, prove_inner_for_air, prove_recursive_layer_for_air,
        verify_inner_for_air, verify_recursive_layer,
    };
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::PrimeCharacteristicRing as _;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_recursion::RecursionOutput;

    fn to_p3(v: BabyBear) -> P3BabyBear {
        P3BabyBear::from_u64(v.0 as u64)
    }

    /// Prove a joint turn and wrap the aggregation layer in ONE recursive STARK.
    /// Returns the recursive output (a single succinct proof) plus the shared
    /// turn id and the public inputs needed to verify the inner layer.
    pub fn prove_joint_turn_recursive(
        participants: &[JointParticipant],
    ) -> Result<(RecursionOutput<DreggRecursionConfig>, Vec<BabyBear>), JointAggError> {
        // Per-cell soundness up front (same as Silver).
        for (i, p) in participants.iter().enumerate() {
            verify_participant(p).map_err(|e| JointAggError::ParticipantProofInvalid {
                index: i,
                reason: e,
            })?;
        }
        let (trace, pis, _tid) = generate_joint_trace(participants)?;
        let air = JointTurnAggregationAir;

        // Inner aggregation proof through the recursion-compatible config.
        let values: Vec<P3BabyBear> = trace
            .iter()
            .flat_map(|row| row.iter().map(|&v| to_p3(v)))
            .collect();
        let matrix = RowMajorMatrix::new(values, 4);
        let inner = prove_inner_for_air(&air, matrix, &pis);
        verify_inner_for_air(&air, &inner, &pis).map_err(|e| {
            JointAggError::AggregationProofInvalid { reason: e }
        })?;

        // ONE recursive layer verifying the aggregation in-circuit.
        let rec = prove_recursive_layer_for_air(&air, &inner, &pis)
            .map_err(|e| JointAggError::AggregationProofInvalid { reason: e })?;
        Ok((rec, pis))
    }

    /// Verify the recursive joint-turn proof (the succinct Gold artifact).
    pub fn verify_joint_turn_recursive(
        output: &RecursionOutput<DreggRecursionConfig>,
    ) -> Result<(), JointAggError> {
        verify_recursive_layer(output)
            .map_err(|e| JointAggError::AggregationProofInvalid { reason: e })
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::effect_vm::pi;
        use crate::effect_vm::{CellState, Effect, EffectVmAir, generate_effect_vm_trace};
        use crate::field::BabyBear;
        use crate::stark;

        fn make_participant(balance: u64, nonce: u32, turn_id: u32) -> JointParticipant {
            let state = CellState::new(balance, nonce);
            let effects = vec![Effect::Transfer {
                amount: 5,
                direction: 1,
            }];
            let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
            public_inputs[pi::TURN_HASH_BASE] = BabyBear::new(turn_id);
            let air = EffectVmAir::new(trace.len());
            let proof = stark::prove(&air, &trace, &public_inputs);
            JointParticipant {
                proof,
                public_inputs,
            }
        }

        /// GOLD: a 2-cell joint turn, aggregated AND wrapped in ONE recursive
        /// in-circuit STARK layer (via the emberian plonky3-recursion fork), and
        /// the single succinct recursive proof verifies.
        #[test]
        fn two_cell_joint_turn_recursive_proves_and_verifies() {
            let p0 = make_participant(100, 0, 0xABCD);
            let p1 = make_participant(200, 7, 0xABCD);
            let participants = vec![p0, p1];

            let (rec, _pis) = prove_joint_turn_recursive(&participants)
                .expect("agreeing 2-cell joint turn must prove recursively");
            verify_joint_turn_recursive(&rec)
                .expect("recursive joint-turn proof must verify");
        }

        /// GOLD teeth: disagreeing turn ids are rejected before any recursive
        /// layer is built — the cross-cell binding holds in the Gold path too.
        #[test]
        fn recursive_rejects_disagreeing_turn_ids() {
            let p0 = make_participant(100, 0, 0xABCD);
            let p1 = make_participant(200, 7, 0x1234);
            let participants = vec![p0, p1];

            let res = prove_joint_turn_recursive(&participants);
            match res {
                Err(JointAggError::SharedTurnIdMismatch { found, expected, .. }) => {
                    assert_eq!(expected, 0xABCD);
                    assert_eq!(found, 0x1234);
                }
                Ok(_) => panic!("disagreeing turn ids must not produce a recursive proof"),
                Err(other) => panic!("expected SharedTurnIdMismatch, got {other:?}"),
            }
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm::{CellState, Effect, generate_effect_vm_trace};

    /// Extract the rejection error, panicking if the aggregation unexpectedly
    /// succeeded. (`JointTurnProof` is not `Debug`, so we cannot use
    /// `Result::expect_err` directly.)
    fn expect_rejected(r: Result<JointTurnProof, JointAggError>, msg: &str) -> JointAggError {
        match r {
            Ok(_) => panic!("{msg}"),
            Err(e) => e,
        }
    }

    /// Build a real EffectVm whole-turn proof for one cell, then OVERRIDE its
    /// `TURN_HASH` public input to a chosen shared turn id (the projection the
    /// aggregator reads) and re-prove against the modified PI so the proof
    /// remains individually valid. This lets us construct participants that are
    /// each valid yet (dis)agree on the turn id at will — the production EffectVm
    /// path (`generate_effect_vm_trace` -> `EffectVmAir` -> `stark::prove`), the
    /// same substrate `proof_forest` uses.
    fn make_participant(balance: u64, nonce: u32, turn_id: u32) -> JointParticipant {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount: 5,
            direction: 1,
        }];
        let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
        // Pin the shared turn id projection (TURN_HASH position 0). The EffectVm
        // AIR does not constrain TURN_HASH (it is an executor-trusted shared PI),
        // so re-proving against the edited PI yields a still-valid proof.
        public_inputs[pi::TURN_HASH_BASE] = BabyBear::new(turn_id);
        let air = EffectVmAir::new(trace.len());
        let proof = stark::prove(&air, &trace, &public_inputs);
        JointParticipant {
            proof,
            public_inputs,
        }
    }

    /// (1) POSITIVE: two cells that AGREE on the shared turn id aggregate into
    /// one proof that verifies.
    #[test]
    fn two_cell_joint_turn_aggregates_and_verifies() {
        let p0 = make_participant(100, 0, 0xABCD);
        let p1 = make_participant(200, 7, 0xABCD);

        // Sanity: they agree on the turn id (the pullback precondition).
        assert_eq!(p0.shared_turn_id(), p1.shared_turn_id());

        let jt = prove_joint_turn(vec![p0, p1]).expect("agreeing 2-cell joint turn must aggregate");
        assert_eq!(jt.num_cells, 2);
        assert_eq!(jt.shared_turn_id, BabyBear::new(0xABCD));

        verify_joint_turn(&jt).expect("aggregated joint turn must verify");
    }

    /// (2) NEGATIVE (THE TEETH): two cells that DISAGREE on the shared turn id
    /// must be REJECTED, even though each per-cell proof is individually valid.
    /// This is the cross-cell binding: per-cell validity does not make two
    /// proofs participants of the same turn.
    #[test]
    fn disagreeing_turn_id_rejected_even_with_valid_proofs() {
        let p0 = make_participant(100, 0, 0xABCD);
        let p1 = make_participant(200, 7, 0x1234); // DIFFERENT turn id

        // Load-bearing: each per-cell proof is individually valid.
        verify_participant(&p0).expect("cell 0 proof must be valid");
        verify_participant(&p1).expect("cell 1 proof must be valid");

        // Yet the JOINT aggregation must reject — at the shared-turn-id check.
        let err = expect_rejected(
            prove_joint_turn(vec![p0, p1]),
            "disagreeing turn ids must be rejected despite valid per-cell proofs",
        );
        match err {
            JointAggError::SharedTurnIdMismatch {
                index,
                expected,
                found,
            } => {
                assert_eq!(index, 1);
                assert_eq!(expected, 0xABCD);
                assert_eq!(found, 0x1234);
            }
            other => panic!(
                "expected SharedTurnIdMismatch (the cross-cell binding), got {other:?} — \
                 a non-binding rejection would mean the test is not exercising joint membership"
            ),
        }
    }

    /// (2b) CIRCUIT-LEVEL teeth: even bypassing the host check, the
    /// `JointTurnAggregationAir` constraint 1 makes a tampered-turn-id trace
    /// UNSAT. We build a trace where one row carries the wrong turn id and feed
    /// it the *published* (correct) turn id; proving must produce a proof that
    /// FAILS verification (the constraint is violated).
    #[test]
    fn tampered_row_turn_id_unsat_in_circuit() {
        let p0 = make_participant(100, 0, 0xABCD);
        let p1 = make_participant(200, 7, 0x1234);
        let participants = vec![p0, p1];
        let published = BabyBear::new(0xABCD);

        // Unchecked trace: row 1 carries 0x1234 while we publish 0xABCD.
        let (trace, pis) = generate_joint_trace_unchecked(&participants, published);
        assert_eq!(trace[1][0], BabyBear::new(0x1234), "row 1 carries the bad tid");
        assert_eq!(pis[0], published, "published tid is the agreed one");

        let config = create_config();
        let p3_public: Vec<P3BabyBear> = pis.iter().map(|&v| to_p3(v)).collect();

        // Under the aggregation AIR's CG-2 constraint (row_tid == pub_tid), the
        // tampered trace is UNSATISFIABLE. The rejection must hold in BOTH build
        // modes, so we check the two mode-independent ways it can surface:
        //   * debug builds: `p3_uni_stark::prove` runs `p3_air::check_constraints`
        //     (gated on `cfg(debug_assertions)`) and PANICS on an unsatisfiable
        //     trace — the prover refuses to forge a proof;
        //   * release builds: the debug check is compiled out, so `prove` may
        //     emit a (bogus) proof — but `p3_uni_stark::verify` then REJECTS it,
        //     because the published `pub_tid` cannot equal the tampered row's
        //     turn id at every row.
        // Either way the tampered trace is rejected; an honest (matching) trace
        // proves AND verifies fine (the positive tests).
        let trace_for_move = trace.clone();
        let pub_for_move = p3_public.clone();
        let config_for_move = config.clone();
        let prove_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let air = JointTurnAggregationAir;
            let matrix = trace_to_matrix(&trace_for_move);
            p3_uni_stark::prove(&config_for_move, &air, matrix, &pub_for_move)
        }));

        let rejected = match prove_result {
            // Debug: prover panicked on the unsatisfiable trace — rejected.
            Err(_) => true,
            // Release: prover emitted a proof; the verifier MUST reject it.
            Ok(proof) => {
                let air = JointTurnAggregationAir;
                p3_uni_stark::verify(&config, &air, &proof, &p3_public).is_err()
            }
        };
        assert!(
            rejected,
            "tampered-turn-id trace must be rejected under the aggregation AIR's CG-2 constraint \
             — the prover refuses it (debug) or the verifier rejects the forged proof (release)"
        );
    }

    /// (DESCRIPTOR CUTOVER) POSITIVE + TEETH: build two descriptor-interpreter
    /// participants that AGREE on the shared turn id, confirm the descriptor
    /// per-cell soundness + CG-2 host gate accepts them; then a third that DISAGREES
    /// is rejected at the shared-turn-id binding — the cross-cell tooth holds on the
    /// descriptor path exactly as on the bespoke path.
    #[test]
    fn descriptor_participants_cg2_binding_holds() {
        use crate::effect_vm_descriptors::descriptor_for_selector;
        use crate::effect_vm::columns::sel;
        use crate::lean_descriptor_air::{parse_vm_descriptor, prove_vm_descriptor};

        let make = |balance: u64, nonce: u32, turn_id: u32| -> DescriptorParticipant {
            let state = CellState::new(balance, nonce);
            let effects = vec![Effect::Transfer { amount: 5, direction: 1 }];
            let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
            public_inputs[pi::TURN_HASH_BASE] = BabyBear::new(turn_id);
            let json = descriptor_for_selector(sel::TRANSFER).unwrap();
            let desc = parse_vm_descriptor(json).unwrap();
            let dpis = &public_inputs[..desc.public_input_count];
            let proof = prove_vm_descriptor(&desc, &trace, dpis)
                .expect("descriptor proves the honest transfer participant");
            DescriptorParticipant { proof, public_inputs }
        };

        let p0 = make(100, 0, 0xABCD);
        let p1 = make(200, 7, 0xABCD);
        // Each verifies selector-bound to TRANSFER.
        assert_eq!(verify_descriptor_participant(&p0).unwrap(), sel::TRANSFER);
        assert_eq!(verify_descriptor_participant(&p1).unwrap(), sel::TRANSFER);
        // Agreeing pair passes the descriptor CG-2 gate.
        let tid = check_descriptor_joint_preconditions(&[p0, p1])
            .expect("agreeing descriptor participants must pass CG-2");
        assert_eq!(tid, BabyBear::new(0xABCD));

        // Disagreeing turn id is rejected at the binding (the cross-cell tooth).
        let q0 = make(100, 0, 0xABCD);
        let q1 = make(200, 7, 0x1234);
        match check_descriptor_joint_preconditions(&[q0, q1]) {
            Err(JointAggError::SharedTurnIdMismatch { index, expected, found }) => {
                assert_eq!(index, 1);
                assert_eq!(expected, 0xABCD);
                assert_eq!(found, 0x1234);
            }
            other => panic!("expected SharedTurnIdMismatch on descriptor path, got {other:?}"),
        }
    }

    /// (3) NEGATIVE: a single participant is not a joint turn.
    #[test]
    fn single_participant_rejected() {
        let p0 = make_participant(100, 0, 0xABCD);
        let err = expect_rejected(prove_joint_turn(vec![p0]), "one cell is not a joint turn");
        assert!(matches!(err, JointAggError::TooFewParticipants { count: 1 }));
    }

    /// (4) POSITIVE: three agreeing cells aggregate (N-ary, not just binary).
    #[test]
    fn three_cell_joint_turn_aggregates() {
        let ps = vec![
            make_participant(100, 0, 0x55),
            make_participant(200, 1, 0x55),
            make_participant(300, 2, 0x55),
        ];
        let jt = prove_joint_turn(ps).expect("agreeing 3-cell joint turn must aggregate");
        assert_eq!(jt.num_cells, 3);
        verify_joint_turn(&jt).expect("3-cell aggregated joint turn must verify");
    }

    /// (5) NEGATIVE: a corrupted per-cell proof is rejected at the per-cell
    /// check (distinct from the turn-id binding failure mode).
    #[test]
    fn corrupted_participant_proof_rejected() {
        let p0 = make_participant(100, 0, 0xABCD);
        let mut p1 = make_participant(200, 7, 0xABCD);
        // Corrupt p1's proof commitment; turn ids still agree, so this must
        // fail at the per-cell check, not the binding.
        p1.proof.trace_commitment[0] ^= 0xFF;

        let err = expect_rejected(
            prove_joint_turn(vec![p0, p1]),
            "corrupted per-cell proof must be rejected",
        );
        match err {
            JointAggError::ParticipantProofInvalid { index, .. } => assert_eq!(index, 1),
            other => panic!("expected ParticipantProofInvalid at cell 1, got {other:?}"),
        }
    }
}

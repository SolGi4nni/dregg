//! **THE KIMCHI→WIRE MARSHALLER.** A `ProverProof` our prover produced, plus the statement
//! scalars, into the record Mina's tooling reads.
//!
//! ## What was missing
//!
//! `wire` can spell a `PicklesProofProofsVerified2ReprStableV2` in both grammars, and does it
//! byte-identically on seven real block proofs. `pickles-wrapmain-harness` can PROVE a Pallas
//! kimchi circuit. Between the two there was nothing: the only construction site of
//! `PicklesWrapWireProofStableV1 { … }` in this tree was the synthetic object in
//! `bin/pickles_proof_wire.rs`, whose every field is a counter. This module is the join.
//!
//! ## The spec it was written from — and where it departs from it
//!
//! openmina has a working forward map: `impl From<&WrapProof> for
//! PicklesProofProofsVerified2ReprStableV2` at
//! `mina-rust/crates/ledger/src/proofs/zkapp.rs:1410-1650`. It was READ as a specification of
//! *which wire field each kimchi field lands in*, and not transcribed; agreement with a copy
//! measures nothing. The inverse — `ledger/src/proofs/prover.rs:30 make_padded_proof_from_p2p`,
//! reproduced in this crate at `src/main.rs:528` and driven through
//! `kimchi::verifier::verify` on a real devnet block — is the *measured* justification for every
//! correspondence below: whatever that inverse reads a field back into is what the field means.
//!
//! ### Provenance of every wire field
//!
//! | wire field | source | why |
//! |---|---|---|
//! | `proof.commitments.w_comm[i]` | `commitments.w_comm[i].chunks[0]` | single chunk at `num_chunks = 1` |
//! | `proof.commitments.z_comm` | `commitments.z_comm.chunks[0]` | ditto |
//! | `proof.commitments.t_comm[i]`, i<7 | `commitments.t_comm.chunks[i]` | `prover.rs:889` commits t with `7 * num_chunks` chunks |
//! | `proof.evaluations.X` | `evals.X.zeta[0]`, `evals.X.zeta_omega[0]` | wire carries one chunk per point |
//! | `proof.ft_eval1` | `ft_eval1` | |
//! | `proof.bulletproof.{lr,z_1,z_2,delta,challenge_polynomial_commitment}` | `proof.{lr,z1,z2,delta,sg}` | |
//! | `…messages_for_next_step_proof.challenge_polynomial_commitments[i]` | `prev_challenges[WRAP_PAD_SLOTS + i].comm.chunks[0]` | ⚑ see below |
//! | `…messages_for_next_wrap_proof.old_bulletproof_challenges[i][j]` | caller, **CHECKED** against `prev_challenges[i].chals[j]` | ⚑ see below |
//!
//! ### ⚑⚑⚑ THE RECURSION PAIR — WHICH TWO FIELDS, MEASURED RATHER THAN ASSUMED
//!
//! Those two rows are **one object**, and it is not the object the field names suggest. The
//! accumulator relation Mina's own reader reconstructs is
//!
//! ```text
//! messages_for_next_step_proof.challenge_polynomial_commitments[i]
//!     == ⟨ b_poly_coefficients( messages_for_next_wrap_proof.old_bulletproof_challenges[i] ),
//!          pallas_srs.g ⟩                       -- FIFTEEN, Fq, over 2^15 Pallas generators
//! ```
//!
//! — front-padded to `PROOFS_VERIFIED` with `dummy_ipa_wrap_sg()` and then `zip`ped, identically in
//! the prover (`wrap.rs:729-748`) and the reader (`prover.rs:113-158
//! make_padded_proof_from_p2p`, the map that feeds `kimchi::verifier::verify`).
//!
//! **Measured on devnet block 539508** by `bin/wire_recursion_pairing_probe`: that relation is
//! `true` at both slots; the same commitment against `messages_for_next_step_proof
//! .old_bulletproof_challenges` is `false` at fifteen rounds and `false` at sixteen; and the
//! SWAPPED-index control is `false`, so slot order is load-bearing rather than incidental.
//!
//! ⚠ **So `messages_for_next_step_proof.old_bulletproof_challenges` is NOT the commitment's
//! partner.** It is `PaddedSeq<…, 16>` — Tick rounds, `BACKEND_TICK_ROUNDS_N` — and the whole of it
//! is consumed by exactly one thing, `MessagesForNextStepProof::to_fields`
//! (`public_input/messages.rs:209-216`, `fields.extend_from_slice(old)`), i.e. the hash that is
//! wrap public word 12. There is no fifteen-into-sixteen reconciliation to perform, and the
//! sixteenth entry is not a pad: `PaddedSeq<T, N>` is `[T; N]` with every entry written, read and
//! hashed (`pseq.rs`), the trailing binprot `()` being the OCaml `Vector` nil and not a slot.
//! | `prev_evals.*` | the **step** proof's `ProofEvaluations` over `Fp` | `verification.rs:230 prev_evals_to_p2p` |
//! | everything else in `statement.proof_state` | caller | `wrap_main`'s output, which we do not yet produce |
//!
//! ### ⚑ Two departures from openmina, both in the direction of binding
//!
//! 1. **openmina's forward map DISCARDS the kimchi proof's `prev_challenges`** — literally
//!    `prev_challenges: _` in the destructuring at `zkapp.rs:1435`. The wire object's recursion
//!    data is taken wholly from the statement, and nothing ever checks the two agree. Here,
//!    `challenge_polynomial_commitments` is taken FROM THE PROOF, and the caller's prechallenges
//!    are REFUSED unless they endo-expand to the proof's `chals` — see
//!    [`MarshalError::PreChallengeMismatch`]. That is a real tie between the statement and the
//!    proof it is supposed to describe.
//!
//!    ⚠ The expansion is one-way, so this could not have been a derivation. The wire carries the
//!    **128-bit prechallenge** (`Scalar_challenge.t = Hex64 * Hex64`); the kimchi proof carries
//!    the **endo-expanded field element** (`ScalarChallenge::to_field`, `poseidon/src/sponge.rs:95`;
//!    openmina's inverse applies `limbs_to_field` at `ledger/src/proofs/util.rs:52`). Truncating
//!    `chals[j]` to two limbs — which is what openmina's map does to the *statement's* already-
//!    unexpanded values — would be wrong applied to a kimchi `chals` entry.
//!
//! 2. **A point at infinity is REFUSED, not silently emitted as `(0,0)`.** openmina's `to_tuple`
//!    reads `.x`/`.y` off the affine point unconditionally. arkworks stores infinity as
//!    `(0, 0, infinity: true)`, and `(0,0)` is not on Pallas — so an infinity chunk becomes an
//!    off-curve wire point with no complaint. This is reachable: `poly-commitment/src/ipa.rs:467`
//!    pads a `PolyComm` up to `num_chunks` when the polynomial is shorter than the SRS, which is
//!    exactly what happens to `t_comm` if the SRS is made larger than the domain.
//!
//! ## What it does not do
//!
//! Nothing here proves, verifies, or checks membership. The marshaller's contract is: *the wire
//! record is a function of the proof and the statement, it refuses every shape a real
//! `Proofs_verified_2` cannot have, and every proof-side field tracks the proof.* Whether the
//! object VERIFIES is a question for `wrap_main`, not for a marshaller.

use ark_ff::{BigInteger, PrimeField};
use kimchi::curve::KimchiCurve;
use kimchi::proof::{PointEvaluations, ProofEvaluations, ProverProof};
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
use mina_p2p_messages::array::ArrayN16;
use mina_p2p_messages::bigint::BigInt;
use mina_p2p_messages::list::List;
use mina_p2p_messages::pseq::PaddedSeq;
use mina_p2p_messages::v2::*;
use mina_poseidon::pasta::FULL_ROUNDS;
use mina_poseidon::sponge::ScalarChallenge;
use poly_commitment::ipa::OpeningProof;

/// The wrap-side proof: Pallas-committed, `Fq`-scalar. `wrap_main_inputs.ml:4,6` sets `Me = Tock`.
///
/// ⚑ The const parameter is kimchi's `FULL_ROUNDS` (55 for Pasta,
/// `poseidon/src/pasta/mod.rs:6`), not the column count and not the IPA round count. Both of
/// those are 15 and it is easy to write `ProverProof<Pallas, OpeningProof<Pallas, 15>, 15>` and
/// have it mean a Poseidon with fifteen full rounds.
pub type WrapKimchiProof = ProverProof<Pallas, OpeningProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>;

/// The step-side proof: Vesta-committed, `Fp`-scalar. Only its evaluations reach the wire.
pub type StepKimchiProof = ProverProof<Vesta, OpeningProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>;

/// IPA rounds of a wrap proof = `log2` of the Tock domain. Fixes `lr`, and the length of each
/// `messages_for_next_wrap_proof.old_bulletproof_challenges` entry
/// (`generated.rs:973` — `PaddedSeq<…A, 15>`).
pub const WRAP_ROUNDS: usize = 15;

/// IPA rounds of a step proof = `log2` of the Tick domain. Fixes
/// `deferred_values.bulletproof_challenges` and each `messages_for_next_step_proof`
/// entry (`generated.rs:806, 957` — `PaddedSeq<…A, 16>`).
pub const STEP_ROUNDS: usize = 16;

/// `prover.rs:889` — the quotient polynomial is committed in `7 * num_chunks` chunks.
pub const T_CHUNKS: usize = 7;

/// `Proofs_verified_2`: `Max_proofs_verified` — the WRAP side's two recursion slots, and the two
/// `messages_for_next_wrap_proof` entries `step.rs:2764-2772` pads to explicitly.
///
/// ⚠ **THIS IS NOT THE STEP RECORD'S ARITY.** Until 2026-08-07 this one constant served both, which
/// is how `messages_for_next_step_proof` came to carry two slots for a rule with one `verify_one`.
/// See [`STEP_RECURSION_SLOTS`].
pub const PROOFS_VERIFIED: usize = 2;

/// ⚑⚑ **`actual_proofs_verified` — THE STEP PROOF'S OWN KIMCHI RECURSION ARITY, AND THE STEP
/// RECORD'S LENGTH. ONE.**
///
/// `wrap.rs:658-666` is literally
/// `actual_proofs_verified = <messages_for_next_step_proof>.old_bulletproof_challenges.len()`, so
/// the RECORD defines the arity rather than reporting it, and `step.rs:2848-2857` builds that
/// record UNPADDED at `N_PREVIOUS` while the same function pads `unfinalized_proofs` and
/// `messages_for_next_wrap_proof` to two in view. Dregg's step rule assembles ONE `verify_one`, so
/// this is 1 — the same number [`crate::gates::STEP_RULE_N_PREVIOUS`] names from the other side.
///
/// ⚠ **IT MOVES THREE THINGS AT ONCE OR NOTHING.** `gate_b` folds the same vector into
/// `expand_deferred`'s `challenges_digest` and kimchi's Fr-sponge folds it into
/// `prev_challenge_digest` (`verifier.rs:289-299`) at the same transcript position, so truncating
/// the record alone makes ξ stop agreeing. `prove_step` therefore folds ONE `RecursionChallenge`,
/// which is what re-bakes `STEP_PREVCOMM_XY` (4 coordinates → 2) and with it `WH_REAL_SLOTS` and
/// every wrap fixture below the `sg_old` block.
pub const STEP_RECURSION_SLOTS: usize = 1;

/// ⚑⚑ **HOW MANY OF THE WRAP PROOF'S RECURSION SLOTS ARE MINA'S OWN `Wrap_hack` PAD — AND THE PAD
/// IS AT THE FRONT.**
///
/// `wrap.rs:729-737` is the wrap prover building its own kimchi `prev_challenges`:
///
/// ```text
/// let mut vec = <the step record>.challenge_polynomial_commitments.clone();
/// while vec.len() < MAX_PROOFS_VERIFIED_N { vec.insert(0, dummy_ipa_wrap_sg()); }
/// vec.into_iter().zip(<the wrap record>.old_bulletproof_challenges)
/// ```
///
/// and `prover.rs:130-140` is the READER doing the identical `push_front` before the identical
/// `zip`. So on a rule with one `verify_one` the wrap proof's slots are `[pad, real]`, and the
/// accumulator list the wire carries is the **trailing** [`STEP_RECURSION_SLOTS`] of them —
/// `Wrap_hack.pad_vector` is `Vector.extend_front_exn` (`wrap_hack.ml:26-28`) and
/// `KimchiWrapHackDigest`'s `whNPad WH_REAL_SLOTS = 1` is the same fact on the Lean side.
///
/// ⚠ **THIS WAS A `take(STEP_RECURSION_SLOTS)` UNTIL 2026-08-10, WHICH TOOK THE PAD AND DROPPED THE
/// REAL SLOT.** Nothing could see it: the marshaller emitted a one-entry list, every parse gate
/// accepted, `accumulator_check` is a different pair and stayed `Ok(true)`, and the mispairing only
/// exists after a reader front-pads — which no gate in this tree ran. `gate_a2` is that reader,
/// and it reports both slots.
pub const WRAP_PAD_SLOTS: usize = PROOFS_VERIFIED - STEP_RECURSION_SLOTS;

/// ⚑ **THE FLOOR A PUBLISHED SLOT'S PRECHALLENGES MUST CLEAR.** Measured on devnet block 539508
/// (`bin/wire_recursion_pairing_probe.rs`): all 62 prechallenges in the object are **120–128 bits**
/// — `wrap_record` slots at 124–128 and 125–128, `step_record` slots at 123–128 and 120–128,
/// `deferred_values` at 127–128. `KimchiStepMainCore.stmtDummyVal`'s filler WAS 24–25; since
/// 2026-08-10 its `.bpChallenge` slots are `MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS`, 123–128,
/// so the emitted padding block clears this floor too.
/// 100 sits under every real value with twenty bits of margin and over every ladder by seventy-five.
pub const ACCUMULATOR_PRECHALLENGE_MIN_BITS: u32 = 100;

/// A 128-bit scalar prechallenge, little-endian limbs — exactly what the wire's
/// `Limb_vector.Constant.Hex64 * Hex64` carries.
pub type PreChallenge = [u64; 2];

/// Bit length of a two-limb prechallenge.
pub fn prechallenge_bits(p: &PreChallenge) -> u32 {
    if p[1] != 0 {
        128 - p[1].leading_zeros()
    } else {
        64 - p[0].leading_zeros()
    }
}

// ───────────────────────────── refusals ─────────────────────────────

/// Every shape a `Proofs_verified_2` wire object cannot have. A marshaller that fills these in
/// rather than refusing is inventing the fields it cannot derive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MarshalError {
    /// A `PolyComm` did not carry the chunk count the wire field has room for.
    Chunks {
        field: &'static str,
        got: usize,
        want: usize,
    },
    /// A `PointEvaluations` carried a chunk count the wire cannot express (it has one slot).
    EvalChunks {
        field: &'static str,
        got: usize,
        want: usize,
    },
    /// The proof does not carry two recursion slots.
    RecursionArity { got: usize, want: usize },
    /// A recursion slot's challenge vector is not `WRAP_ROUNDS` long.
    RecursionChals {
        index: usize,
        got: usize,
        want: usize,
    },
    /// The caller's prechallenge does not endo-expand to the challenge the PROOF carries.
    PreChallengeMismatch {
        slot: usize,
        round: usize,
        from_statement: String,
        from_proof: String,
    },
    /// A curve point is the point at infinity, whose `(x, y)` is `(0, 0)` and off the curve.
    PointAtInfinity { field: String },
    /// A pair of coordinates that is not a point of the curve the wire field is READ as. ⚑ This is
    /// the class the two parse gates cannot see: `binprot_read` and `Pickles.proofOfBase64` both
    /// reconstruct the record from two bare `BigInt`s and never ask whether the pair is a point, so
    /// an off-curve — or right-curve-wrong-group — value reaches Mina's verifier unremarked and
    /// aborts it (`StatementProofState::try_from` builds curve points with `Affine::new`, which
    /// ASSERTS). Refused here instead, naming the curve that was expected.
    OffCurve {
        field: String,
        expected: &'static str,
    },
    /// The step-side statement data does not have one entry per recursion slot.
    StepChallengeArity { got: usize, want: usize },
    /// The caller's step-side prechallenge does not endo-expand to the challenge the STEP PROOF
    /// carries in that recursion slot. The Tick mirror of [`Self::PreChallengeMismatch`].
    StepPreChallengeMismatch {
        slot: usize,
        round: usize,
        from_statement: String,
        from_proof: String,
    },
    /// The step proof carried no public-input evaluation, or carried it chunked.
    PublicEval { got: Option<usize> },
    /// ⚑⚑ **A SLOT THE ACCUMULATOR LIST SELECTS CARRIES A PRECHALLENGE THAT IS NOT A SQUEEZE.**
    ///
    /// `messages_for_next_step_proof.challenge_polynomial_commitments[i]` is the commitment to
    /// `b_poly(messages_for_next_wrap_proof.old_bulletproof_challenges[i])` — measured true on both
    /// slots of devnet block 539508, with the swapped-index control refuting
    /// (`bin/wire_recursion_pairing_probe.rs`). A slot the marshaller PUBLISHES is therefore a
    /// slot whose fifteen prechallenges Mina will endo-expand and fold, and each of them is an
    /// `Ro.scalar_chal ()` draw: **120–128 bits on that block, minimum 120 over all 62 values in
    /// it.** A structured filler is not one, and a filler is exactly what got published — the
    /// padding block's fifteen were `KimchiStepMainCore.stmtDummyVal`, `(7 + 1000003·j) % 2^127`,
    /// **24–25 bits.** ⛑ REPAIRED 2026-08-10 at the source: those fifteen slots now carry
    /// `MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS` — `Dummy.Ipa.Wrap.challenges`, 123–128 bits — so
    /// no emission of this tree reaches this refusal. It stays because the refusal is about the
    /// SHAPE and not about one emitter, and because the emitter it was aimed at can regress.
    ///
    /// [`ACCUMULATOR_PRECHALLENGE_MIN_BITS`] is the floor, set well under the 120 a real block
    /// shows and far over anything a ladder produces.
    AccumulatorPrechallengeTooSmall {
        slot: usize,
        round: usize,
        bits: u32,
        floor: u32,
    },
}

impl std::fmt::Display for MarshalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Chunks { field, got, want } => {
                write!(f, "{field}: PolyComm has {got} chunks, wire field takes {want}")
            }
            Self::EvalChunks { field, got, want } => {
                write!(f, "{field}: evaluation has {got} chunks, wire field takes {want}")
            }
            Self::RecursionArity { got, want } => write!(
                f,
                "proof carries {got} recursion challenges; Proofs_verified_2 is {want}"
            ),
            Self::RecursionChals { index, got, want } => write!(
                f,
                "recursion slot {index}: {got} challenges, a wrap IPA has {want}"
            ),
            Self::PreChallengeMismatch {
                slot,
                round,
                from_statement,
                from_proof,
            } => write!(
                f,
                "slot {slot} round {round}: the statement's prechallenge expands to {from_statement}, \
                 the proof carries {from_proof} — the statement does not describe this proof"
            ),
            Self::PointAtInfinity { field } => {
                write!(f, "{field}: point at infinity has no on-curve (x, y)")
            }
            Self::OffCurve { field, expected } => write!(
                f,
                "{field}: the (x, y) pair is not a point of {expected}, which is the curve Mina reads \
                 this field as"
            ),
            Self::StepChallengeArity { got, want } => write!(
                f,
                "statement carries {got} step-side challenge vectors, proof has {want} recursion slots"
            ),
            Self::StepPreChallengeMismatch {
                slot,
                round,
                from_statement,
                from_proof,
            } => write!(
                f,
                "step slot {slot} round {round}: the statement's prechallenge expands to \
                 {from_statement}, the STEP proof carries {from_proof} — expand_deferred's \
                 challenges_digest and kimchi's prev_challenge_digest would disagree, and ξ with them"
            ),
            Self::PublicEval { got } => match got {
                None => write!(f, "step proof carries no public-input evaluation"),
                Some(n) => write!(f, "step proof's public-input evaluation has {n} chunks, wire takes 1"),
            },
            Self::AccumulatorPrechallengeTooSmall {
                slot,
                round,
                bits,
                floor,
            } => write!(
                f,
                "wrap slot {slot} round {round}: the prechallenge is {bits} bits, under the {floor}-bit \
                 floor — this slot's commitment is PUBLISHED as \
                 messages_for_next_step_proof.challenge_polynomial_commitments, so these fifteen are \
                 what Mina endo-expands and folds against it, and a squeeze is 120-128 bits on a real \
                 block while a structured filler is not"
            ),
        }
    }
}

impl std::error::Error for MarshalError {}

// ───────────────────────────── the caller's half ─────────────────────────────

/// The scalars `wrap_main` derives and a marshaller cannot: the Fiat–Shamir challenges, the
/// deferred values, the branch selection, the accumulator.
///
/// Every challenge here is the **unexpanded 128-bit prechallenge**, which is what the wire
/// carries. [`marshal`] refuses if `old_wrap_bulletproof_challenges` does not expand to the
/// challenges the proof itself carries.
#[derive(Debug, Clone)]
pub struct WrapStatementScalars {
    pub alpha: PreChallenge,
    pub beta: PreChallenge,
    pub gamma: PreChallenge,
    pub zeta: PreChallenge,
    /// `None` is what every real block wrap proof carries (no lookups).
    pub joint_combiner: Option<PreChallenge>,
    pub feature_flags:
        PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkFeatureFlags,
    /// The STEP proof's IPA challenges — 16, the Tick domain.
    pub bulletproof_challenges: [PreChallenge; STEP_ROUNDS],
    pub branch_proofs_verified: PicklesBaseProofsVerifiedStableV1,
    pub branch_domain_log2: u8,
    pub sponge_digest_before_evaluations: [u64; 4],
    /// The next wrap accumulator. `wrap.rs:700-724` builds it from the PREVIOUS step statement,
    /// before this proof exists, so it is not derivable from this proof's `sg`.
    ///
    /// ⚑ **VESTA, NOT PALLAS, AND THIS WAS WRONG UNTIL 2026-08-05.** The two `challenge_polynomial`
    /// fields of a wrap statement live on DIFFERENT curves and the wire cannot tell you which:
    /// both are two bare `BigInt`s. `messages_for_next_wrap_proof.challenge_polynomial_commitment`
    /// is the STEP proof's accumulator that the next WRAP consumes — Tick, i.e. **Vesta** — read as
    /// `Vesta::of_coordinates` by `accumulator_check` (openmina `proofs/accumulator_check.rs:44-53`)
    /// and built with `Affine::<VestaParameters>::new` by `StatementProofState::try_from`
    /// (`proofs/step.rs`), which ASSERTS on-curve. `messages_for_next_step_proof.
    /// challenge_polynomial_commitments` is the mirror — `InnerCurve<Fp>`, i.e. **Pallas**
    /// (`proofs/verification.rs:444`) — and is correct below.
    ///
    /// MEASURED, not looked up: `mina_verdict` reads this field out of real block proofs
    /// (`metatheory/fixtures/mina-blocks/devnet-540890`, `mainnet-541858`) and reports it on Vesta
    /// and not on Pallas, while the value this marshaller used to emit was on Pallas and not on
    /// Vesta. `verify_zkapp` did not return false on it — it ABORTED THE PROCESS. Neither parse
    /// gate saw anything wrong, which is why [`MarshalError::OffCurve`] now exists.
    pub next_wrap_challenge_polynomial_commitment: Vesta,
    /// The prechallenges of the two previous WRAP proofs. Checked against the proof.
    pub old_wrap_bulletproof_challenges: [[PreChallenge; WRAP_ROUNDS]; PROOFS_VERIFIED],
    /// The prechallenges of the two previous STEP proofs. Not present in the kimchi proof at all.
    pub step_old_bulletproof_challenges: Vec<[PreChallenge; STEP_ROUNDS]>,
}

/// The previous STEP proof's evaluations, which the wrap wire record carries verbatim.
/// Produced from a real step-side kimchi proof by [`prev_step_evals_from_proof`].
#[derive(Debug, Clone)]
pub struct PrevStepEvals {
    pub public_input: (Fp, Fp),
    pub ft_eval1: Fp,
    pub evals: ProofEvaluations<PointEvaluations<Vec<Fp>>>,
    /// The step proof's own recursion challenges, endo-expanded, one vector per slot.
    ///
    /// ⚑ These are NOT decoration and they are NOT free. kimchi's Fr-sponge absorbs a
    /// `prev_challenge_digest` over exactly these (`verifier.rs:289-299`) before it squeezes ξ and
    /// r, and Pickles' `expand_deferred` absorbs a `challenges_digest` over
    /// `messages_for_next_step_proof.old_bulletproof_challenges` at the same position
    /// (`step.rs:1997-2013`). The two ξ agree **iff those two vectors are the same vector**. A step
    /// proof with no recursion slots against a statement that claims two is the whole reason the
    /// deferred values used to fork, and [`MarshalError::StepPreChallengeMismatch`] is what makes
    /// that a refusal instead of a silent disagreement.
    pub prev_chals: Vec<Vec<Fp>>,
}

/// Read the wire's `prev_evals` out of a step-side kimchi proof. `evals.public` is filled by
/// `kimchi/src/prover.rs:995`; a step circuit with no public input has none, and this refuses
/// rather than substituting zeros.
pub fn prev_step_evals_from_proof(step: &StepKimchiProof) -> Result<PrevStepEvals, MarshalError> {
    let public = step
        .evals
        .public
        .as_ref()
        .ok_or(MarshalError::PublicEval { got: None })?;
    if public.zeta.len() != 1 || public.zeta_omega.len() != 1 {
        return Err(MarshalError::PublicEval {
            got: Some(public.zeta.len()),
        });
    }
    Ok(PrevStepEvals {
        public_input: (public.zeta[0], public.zeta_omega[0]),
        ft_eval1: step.ft_eval1,
        evals: step.evals.clone(),
        prev_chals: step
            .prev_challenges
            .iter()
            .map(|rc| rc.chals.clone())
            .collect(),
    })
}

// ───────────────────────────── field conversions ─────────────────────────────

fn f_to_bigint<F: PrimeField>(v: &F) -> BigInt {
    let le = v.into_bigint().to_bytes_le();
    let mut b = [0u8; 32];
    let n = le.len().min(32);
    b[..n].copy_from_slice(&le[..n]);
    BigInt::from_bytes(b)
}

fn hex64(v: u64) -> LimbVectorConstantHex64StableV1 {
    LimbVectorConstantHex64StableV1(v.into())
}

fn challenge(
    c: &PreChallenge,
) -> PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2AChallenge {
    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2AChallenge {
        inner: PaddedSeq([hex64(c[0]), hex64(c[1])]),
    }
}

fn bp(
    c: &PreChallenge,
) -> PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2A {
    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2A {
        prechallenge: challenge(c),
    }
}

/// A Pallas point as the wire's `(x, y)`. Refuses infinity — see the module header.
/// A wire point, refusing both shapes a real one cannot have.
///
/// ⚑ `expected` is not decoration: the wire carries two bare `BigInt`s and the GROUP is decided by
/// the READER, so a field's curve is a fact about Mina's code, not about the bytes. Naming it here
/// is what makes a wrong-group value a refusal with an explanation rather than an abort inside
/// arkworks two layers down.
fn point<P: ark_ec::short_weierstrass::SWCurveConfig>(
    field: &str,
    expected: &'static str,
    g: &ark_ec::short_weierstrass::Affine<P>,
) -> Result<(BigInt, BigInt), MarshalError>
where
    P::BaseField: PrimeField,
{
    if g.infinity {
        return Err(MarshalError::PointAtInfinity {
            field: field.to_string(),
        });
    }
    if !g.is_on_curve() {
        return Err(MarshalError::OffCurve {
            field: field.to_string(),
            expected,
        });
    }
    Ok((f_to_bigint(&g.x), f_to_bigint(&g.y)))
}

fn one_chunk(
    field: &'static str,
    c: &poly_commitment::PolyComm<Pallas>,
) -> Result<(BigInt, BigInt), MarshalError> {
    if c.chunks.len() != 1 {
        return Err(MarshalError::Chunks {
            field,
            got: c.chunks.len(),
            want: 1,
        });
    }
    point(field, "Pallas", &c.chunks[0])
}

/// The Tick mirror of [`expand_prechallenge`]: a 128-bit prechallenge lifted into `Fp` with
/// **Vesta**'s endo coefficient, which is the lift `accumulator_check.rs:23-38` applies and the one
/// a step proof's IPA challenges come out of.
///
/// ⚑ The two constants are different and the wire cannot tell you which a field wants — both sides
/// are two bare limbs. Using the wrong one produces a field element every reader accepts and Mina's
/// arithmetic refuses.
pub fn expand_step_prechallenge(c: &PreChallenge) -> Fp {
    let mut limbs = [0u64; 4];
    limbs[..2].copy_from_slice(c);
    let raw = Fp::from(ark_ff::BigInt::<4>(limbs));
    let (_, endo_r) = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos();
    ScalarChallenge(raw).to_field(endo_r)
}

/// `ScalarChallenge::to_field` — the endo expansion the PROVER applied
/// (`poseidon/src/sponge.rs:95`), with kimchi's own Pallas scalar endo coefficient.
pub fn expand_prechallenge(c: &PreChallenge) -> Fq {
    let mut limbs = [0u64; 4];
    limbs[..2].copy_from_slice(c);
    let raw = Fq::from(ark_ff::BigInt::<4>(limbs));
    let (_, endo_r) = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos();
    ScalarChallenge(raw).to_field(endo_r)
}

fn pt_pair(
    field: &'static str,
    p: &PointEvaluations<Vec<Fq>>,
) -> Result<(BigInt, BigInt), MarshalError> {
    if p.zeta.len() != 1 || p.zeta_omega.len() != 1 {
        return Err(MarshalError::EvalChunks {
            field,
            got: p.zeta.len().max(p.zeta_omega.len()),
            want: 1,
        });
    }
    Ok((f_to_bigint(&p.zeta[0]), f_to_bigint(&p.zeta_omega[0])))
}

/// The step-side (chunked) shape: the wire keeps every chunk here, unlike the wrap side.
fn pt_chunks(p: &PointEvaluations<Vec<Fp>>) -> (ArrayN16<BigInt>, ArrayN16<BigInt>) {
    (
        p.zeta.iter().map(f_to_bigint).collect::<Vec<_>>().into(),
        p.zeta_omega
            .iter()
            .map(f_to_bigint)
            .collect::<Vec<_>>()
            .into(),
    )
}

fn pt_chunks_opt(
    p: &Option<PointEvaluations<Vec<Fp>>>,
) -> Option<(ArrayN16<BigInt>, ArrayN16<BigInt>)> {
    p.as_ref().map(pt_chunks)
}

// ───────────────────────────── the marshaller ─────────────────────────────

/// **`(kimchi proof, step evals, statement) → the record Mina's tooling reads.`**
///
/// Total on its inputs modulo the refusals in [`MarshalError`]; every one of those is a shape a
/// real `Proofs_verified_2` cannot have.
pub fn marshal(
    proof: &WrapKimchiProof,
    prev: &PrevStepEvals,
    st: &WrapStatementScalars,
) -> Result<PicklesProofProofsVerified2ReprStableV2, MarshalError> {
    // ---- the recursion slots, and the tie between the statement and the proof ----
    if proof.prev_challenges.len() != PROOFS_VERIFIED {
        return Err(MarshalError::RecursionArity {
            got: proof.prev_challenges.len(),
            want: PROOFS_VERIFIED,
        });
    }
    if st.step_old_bulletproof_challenges.len() != STEP_RECURSION_SLOTS {
        return Err(MarshalError::StepChallengeArity {
            got: st.step_old_bulletproof_challenges.len(),
            want: STEP_RECURSION_SLOTS,
        });
    }
    // ⚑ The Tick tie, added 2026-08-05. `messages_for_next_step_proof.old_bulletproof_challenges`
    // is the vector `expand_deferred` folds into `challenges_digest` (`step.rs:1997-2013`) and
    // kimchi's Fr-sponge folds into `prev_challenge_digest` (`verifier.rs:289-299`) at the SAME
    // position of the SAME transcript. If the statement's copy is not the step proof's own, the
    // two ξ diverge — silently, because the wire carries no ξ to disagree with.
    if prev.prev_chals.len() != STEP_RECURSION_SLOTS {
        return Err(MarshalError::StepChallengeArity {
            got: prev.prev_chals.len(),
            want: STEP_RECURSION_SLOTS,
        });
    }
    for (i, chals) in prev.prev_chals.iter().enumerate() {
        if chals.len() != STEP_ROUNDS {
            return Err(MarshalError::RecursionChals {
                index: i,
                got: chals.len(),
                want: STEP_ROUNDS,
            });
        }
        for (j, chal) in chals.iter().enumerate() {
            let expanded = expand_step_prechallenge(&st.step_old_bulletproof_challenges[i][j]);
            if expanded != *chal {
                return Err(MarshalError::StepPreChallengeMismatch {
                    slot: i,
                    round: j,
                    from_statement: format!("{expanded}"),
                    from_proof: format!("{chal}"),
                });
            }
        }
    }
    for (i, rc) in proof.prev_challenges.iter().enumerate() {
        if rc.chals.len() != WRAP_ROUNDS {
            return Err(MarshalError::RecursionChals {
                index: i,
                got: rc.chals.len(),
                want: WRAP_ROUNDS,
            });
        }
        for (j, chal) in rc.chals.iter().enumerate() {
            let expanded = expand_prechallenge(&st.old_wrap_bulletproof_challenges[i][j]);
            if expanded != *chal {
                return Err(MarshalError::PreChallengeMismatch {
                    slot: i,
                    round: j,
                    from_statement: format!("{expanded}"),
                    from_proof: format!("{chal}"),
                });
            }
        }
    }

    // ---- statement.proof_state ----
    let plonk = PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonk {
        alpha: challenge(&st.alpha),
        beta: PaddedSeq([hex64(st.beta[0]), hex64(st.beta[1])]),
        gamma: PaddedSeq([hex64(st.gamma[0]), hex64(st.gamma[1])]),
        zeta: challenge(&st.zeta),
        joint_combiner: st.joint_combiner.as_ref().map(challenge),
        feature_flags: st.feature_flags.clone(),
    };

    let deferred_values =
        PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValues {
            plonk,
            bulletproof_challenges: PaddedSeq(std::array::from_fn(|i| {
                bp(&st.bulletproof_challenges[i])
            })),
            branch_data: CompositionTypesBranchDataStableV1 {
                proofs_verified: st.branch_proofs_verified.clone(),
                domain_log2: CompositionTypesBranchDataDomainLog2StableV1(
                    st.branch_domain_log2.into(),
                ),
            },
        };

    let proof_state = PicklesProofProofsVerified2ReprStableV2StatementProofState {
        deferred_values,
        sponge_digest_before_evaluations: CompositionTypesDigestConstantStableV1(PaddedSeq(
            std::array::from_fn(|i| hex64(st.sponge_digest_before_evaluations[i])),
        )),
        messages_for_next_wrap_proof:
            PicklesProofProofsVerified2ReprStableV2MessagesForNextWrapProof {
                challenge_polynomial_commitment: point(
                    "statement.proof_state.messages_for_next_wrap_proof.challenge_polynomial_commitment",
                    "Vesta",
                    &st.next_wrap_challenge_polynomial_commitment,
                )?,
                old_bulletproof_challenges: PaddedSeq(std::array::from_fn(|i| {
                    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2(
                        PaddedSeq(std::array::from_fn(|j| {
                            bp(&st.old_wrap_bulletproof_challenges[i][j])
                        })),
                    )
                })),
            },
    };

    // ---- statement.messages_for_next_step_proof ----
    // ⚑ The commitments come out of the PROOF. openmina takes them from its statement and drops
    // `prev_challenges` entirely.
    // ⚑⚑ **AND THERE ARE `STEP_RECURSION_SLOTS` OF THEM, NOT `PROOFS_VERIFIED`.** The record's two
    // vectors are one `Vector.t (…, N_PREVIOUS)` each (`step.rs:2848-2857`) and must have the SAME
    // length, so this walks the step record's arity rather than the wrap side's `Max_proofs_verified`.
    // A two-entry commitment vector beside a one-entry challenge vector is not a padded record; it
    // is a record `MessagesForNextStepProof::to_fields` would hash as neither shape.
    //
    // ⚑⚑⚑ **AND THEY ARE THE TRAILING SLOTS.** See [`WRAP_PAD_SLOTS`]: both the wrap prover
    // (`wrap.rs:729-737`) and the reader (`prover.rs:130-140`) FRONT-pad this list back to
    // `PROOFS_VERIFIED` and then `zip` it, in order, against
    // `messages_for_next_wrap_proof.old_bulletproof_challenges` — the fifteen, not the sixteen.
    // Publishing the leading slots hands Mina a proof whose every recursion pair is shifted by one.
    let mut cpc: Vec<(BigInt, BigInt)> = Vec::with_capacity(STEP_RECURSION_SLOTS);
    for (i, rc) in proof
        .prev_challenges
        .iter()
        .enumerate()
        .skip(WRAP_PAD_SLOTS)
    {
        if rc.comm.chunks.len() != 1 {
            return Err(MarshalError::Chunks {
                field: "prev_challenges[_].comm",
                got: rc.comm.chunks.len(),
                want: 1,
            });
        }
        // ⚑⚑ **THE FLOOR, ON THE SLOTS THIS RECORD PUBLISHES AND ONLY THOSE.** A slot whose
        // commitment reaches the wire is a slot whose fifteen prechallenges Mina endo-expands and
        // folds against it. `ACCUMULATOR_PRECHALLENGE_MIN_BITS` is measured against a real block;
        // the ladder this pipeline used to publish here is 24 bits and does not clear it.
        for (j, p) in st.old_wrap_bulletproof_challenges[i].iter().enumerate() {
            let bits = prechallenge_bits(p);
            if bits < ACCUMULATOR_PRECHALLENGE_MIN_BITS {
                return Err(MarshalError::AccumulatorPrechallengeTooSmall {
                    slot: i,
                    round: j,
                    bits,
                    floor: ACCUMULATOR_PRECHALLENGE_MIN_BITS,
                });
            }
        }
        cpc.push(point(
            &format!("prev_challenges[{i}].comm.chunks[0]"),
            // openmina reads these as `InnerCurve<Fp>` (`proofs/verification.rs:444`) — Pallas, the
            // mirror of the Vesta field above. The two are one line apart on the wire.
            "Pallas",
            &rc.comm.chunks[0],
        )?);
    }

    let messages_for_next_step_proof =
        PicklesProofProofsVerified2ReprStableV2MessagesForNextStepProof {
            app_state: (),
            challenge_polynomial_commitments: cpc.into_iter().collect::<List<_>>(),
            old_bulletproof_challenges: st
                .step_old_bulletproof_challenges
                .iter()
                .map(|v| PaddedSeq(std::array::from_fn(|i| bp(&v[i]))))
                .collect::<List<_>>(),
        };

    // ---- prev_evals: the STEP proof's evaluations, chunk counts preserved ----
    let e = &prev.evals;
    let prev_evals = PicklesProofProofsVerified2ReprStableV2PrevEvals {
        evals: PicklesProofProofsVerified2ReprStableV2PrevEvalsEvals {
            public_input: (
                f_to_bigint(&prev.public_input.0),
                f_to_bigint(&prev.public_input.1),
            ),
            evals: PicklesProofProofsVerified2ReprStableV2PrevEvalsEvalsEvals {
                w: PaddedSeq(e.w.each_ref().map(pt_chunks)),
                coefficients: PaddedSeq(e.coefficients.each_ref().map(pt_chunks)),
                z: pt_chunks(&e.z),
                s: PaddedSeq(e.s.each_ref().map(pt_chunks)),
                generic_selector: pt_chunks(&e.generic_selector),
                poseidon_selector: pt_chunks(&e.poseidon_selector),
                complete_add_selector: pt_chunks(&e.complete_add_selector),
                mul_selector: pt_chunks(&e.mul_selector),
                emul_selector: pt_chunks(&e.emul_selector),
                endomul_scalar_selector: pt_chunks(&e.endomul_scalar_selector),
                range_check0_selector: pt_chunks_opt(&e.range_check0_selector),
                range_check1_selector: pt_chunks_opt(&e.range_check1_selector),
                foreign_field_add_selector: pt_chunks_opt(&e.foreign_field_add_selector),
                foreign_field_mul_selector: pt_chunks_opt(&e.foreign_field_mul_selector),
                xor_selector: pt_chunks_opt(&e.xor_selector),
                rot_selector: pt_chunks_opt(&e.rot_selector),
                lookup_aggregation: pt_chunks_opt(&e.lookup_aggregation),
                lookup_table: pt_chunks_opt(&e.lookup_table),
                lookup_sorted: PaddedSeq(e.lookup_sorted.each_ref().map(pt_chunks_opt)),
                runtime_lookup_table: pt_chunks_opt(&e.runtime_lookup_table),
                runtime_lookup_table_selector: pt_chunks_opt(&e.runtime_lookup_table_selector),
                xor_lookup_selector: pt_chunks_opt(&e.xor_lookup_selector),
                lookup_gate_lookup_selector: pt_chunks_opt(&e.lookup_gate_lookup_selector),
                range_check_lookup_selector: pt_chunks_opt(&e.range_check_lookup_selector),
                foreign_field_mul_lookup_selector: pt_chunks_opt(
                    &e.foreign_field_mul_lookup_selector,
                ),
            },
        },
        ft_eval1: f_to_bigint(&prev.ft_eval1),
    };

    // ---- the proof proper ----
    let c = &proof.commitments;
    let mut w_comm: Vec<(BigInt, BigInt)> = Vec::with_capacity(15);
    for wc in c.w_comm.iter() {
        w_comm.push(one_chunk("commitments.w_comm", wc)?);
    }
    if c.t_comm.chunks.len() != T_CHUNKS {
        return Err(MarshalError::Chunks {
            field: "commitments.t_comm",
            got: c.t_comm.chunks.len(),
            want: T_CHUNKS,
        });
    }
    let mut t_comm: Vec<(BigInt, BigInt)> = Vec::with_capacity(T_CHUNKS);
    for (i, g) in c.t_comm.chunks.iter().enumerate() {
        t_comm.push(point(
            &format!("commitments.t_comm.chunks[{i}]"),
            "Pallas",
            g,
        )?);
    }

    let ev = &proof.evals;
    let mut w_ev: Vec<(BigInt, BigInt)> = Vec::with_capacity(15);
    for p in ev.w.iter() {
        w_ev.push(pt_pair("evals.w", p)?);
    }
    let mut coeff_ev: Vec<(BigInt, BigInt)> = Vec::with_capacity(15);
    for p in ev.coefficients.iter() {
        coeff_ev.push(pt_pair("evals.coefficients", p)?);
    }
    let mut s_ev: Vec<(BigInt, BigInt)> = Vec::with_capacity(6);
    for p in ev.s.iter() {
        s_ev.push(pt_pair("evals.s", p)?);
    }

    let op = &proof.proof;
    let mut lr: Vec<((BigInt, BigInt), (BigInt, BigInt))> = Vec::with_capacity(op.lr.len());
    for (i, (l, r)) in op.lr.iter().enumerate() {
        lr.push((
            point(&format!("proof.lr[{i}].0"), "Pallas", l)?,
            point(&format!("proof.lr[{i}].1"), "Pallas", r)?,
        ));
    }

    let wire_proof = PicklesWrapWireProofStableV1 {
        commitments: PicklesWrapWireProofCommitmentsStableV1 {
            w_comm: PaddedSeq(std::array::from_fn(|i| w_comm[i].clone())),
            z_comm: one_chunk("commitments.z_comm", &c.z_comm)?,
            t_comm: PaddedSeq(std::array::from_fn(|i| t_comm[i].clone())),
        },
        evaluations: PicklesWrapWireProofEvaluationsStableV1 {
            w: PaddedSeq(std::array::from_fn(|i| w_ev[i].clone())),
            coefficients: PaddedSeq(std::array::from_fn(|i| coeff_ev[i].clone())),
            z: pt_pair("evals.z", &ev.z)?,
            s: PaddedSeq(std::array::from_fn(|i| s_ev[i].clone())),
            generic_selector: pt_pair("evals.generic_selector", &ev.generic_selector)?,
            poseidon_selector: pt_pair("evals.poseidon_selector", &ev.poseidon_selector)?,
            complete_add_selector: pt_pair(
                "evals.complete_add_selector",
                &ev.complete_add_selector,
            )?,
            mul_selector: pt_pair("evals.mul_selector", &ev.mul_selector)?,
            emul_selector: pt_pair("evals.emul_selector", &ev.emul_selector)?,
            endomul_scalar_selector: pt_pair(
                "evals.endomul_scalar_selector",
                &ev.endomul_scalar_selector,
            )?,
        },
        ft_eval1: f_to_bigint(&proof.ft_eval1),
        bulletproof: PicklesWrapWireProofStableV1Bulletproof {
            lr: lr.into(),
            z_1: f_to_bigint(&op.z1),
            z_2: f_to_bigint(&op.z2),
            delta: point("proof.delta", "Pallas", &op.delta)?,
            challenge_polynomial_commitment: point("proof.sg", "Pallas", &op.sg)?,
        },
    };

    Ok(PicklesProofProofsVerified2ReprStableV2 {
        statement: PicklesProofProofsVerified2ReprStableV2Statement {
            proof_state,
            messages_for_next_step_proof,
        },
        prev_evals,
        proof: wire_proof,
    })
}

// ───────────────────────── which field moved ─────────────────────────

/// Every wire field of a `Proofs_verified_2` record, named, as a comparable string.
///
/// This is what makes a perturbation legible: a proof-side change must move a proof-side field
/// and nothing else. It walks the record explicitly rather than diffing the encodings, so the
/// answer is a FIELD PATH and not a byte offset.
pub fn field_table(p: &PicklesProofProofsVerified2ReprStableV2) -> Vec<(String, String)> {
    let mut v: Vec<(String, String)> = Vec::new();
    let mut put = |k: String, s: String| v.push((k, s));

    let pair = |t: &(BigInt, BigInt)| format!("{:?}|{:?}", t.0, t.1);
    let chal = |c: &PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2AChallenge| {
        format!("{:016x}{:016x}", c.inner.0[0].0.as_u64(), c.inner.0[1].0.as_u64())
    };

    let ps = &p.statement.proof_state;
    let dv = &ps.deferred_values;
    put(
        "statement.proof_state.deferred_values.plonk.alpha".into(),
        chal(&dv.plonk.alpha),
    );
    put(
        "statement.proof_state.deferred_values.plonk.beta".into(),
        format!(
            "{:016x}{:016x}",
            dv.plonk.beta.0[0].0.as_u64(),
            dv.plonk.beta.0[1].0.as_u64()
        ),
    );
    put(
        "statement.proof_state.deferred_values.plonk.gamma".into(),
        format!(
            "{:016x}{:016x}",
            dv.plonk.gamma.0[0].0.as_u64(),
            dv.plonk.gamma.0[1].0.as_u64()
        ),
    );
    put(
        "statement.proof_state.deferred_values.plonk.zeta".into(),
        chal(&dv.plonk.zeta),
    );
    put(
        "statement.proof_state.deferred_values.plonk.joint_combiner".into(),
        format!("{:?}", dv.plonk.joint_combiner.as_ref().map(chal)),
    );
    put(
        "statement.proof_state.deferred_values.plonk.feature_flags".into(),
        format!("{:?}", dv.plonk.feature_flags),
    );
    for (i, b) in dv.bulletproof_challenges.0.iter().enumerate() {
        put(
            format!("statement.proof_state.deferred_values.bulletproof_challenges[{i}]"),
            chal(&b.prechallenge),
        );
    }
    put(
        "statement.proof_state.deferred_values.branch_data".into(),
        format!(
            "{:?}/{}",
            dv.branch_data.proofs_verified,
            dv.branch_data.domain_log2.0.as_u8()
        ),
    );
    put(
        "statement.proof_state.sponge_digest_before_evaluations".into(),
        ps.sponge_digest_before_evaluations
            .0
             .0
            .iter()
            .map(|l| format!("{:016x}", l.0.as_u64()))
            .collect::<String>(),
    );
    let mw = &ps.messages_for_next_wrap_proof;
    put(
        "statement.proof_state.messages_for_next_wrap_proof.challenge_polynomial_commitment".into(),
        pair(&mw.challenge_polynomial_commitment),
    );
    for (i, vec15) in mw.old_bulletproof_challenges.0.iter().enumerate() {
        for (j, b) in vec15.0 .0.iter().enumerate() {
            put(
                format!("statement.proof_state.messages_for_next_wrap_proof.old_bulletproof_challenges[{i}][{j}]"),
                chal(&b.prechallenge),
            );
        }
    }
    let ms = &p.statement.messages_for_next_step_proof;
    for (i, c) in ms.challenge_polynomial_commitments.iter().enumerate() {
        put(
            format!("statement.messages_for_next_step_proof.challenge_polynomial_commitments[{i}]"),
            pair(c),
        );
    }
    for (i, vec16) in ms.old_bulletproof_challenges.iter().enumerate() {
        for (j, b) in vec16.0.iter().enumerate() {
            put(
                format!(
                    "statement.messages_for_next_step_proof.old_bulletproof_challenges[{i}][{j}]"
                ),
                chal(&b.prechallenge),
            );
        }
    }

    let epair = |t: &(ArrayN16<BigInt>, ArrayN16<BigInt>)| format!("{:?}|{:?}", t.0, t.1);
    let pe = &p.prev_evals;
    put(
        "prev_evals.evals.public_input".into(),
        pair(&pe.evals.public_input),
    );
    put("prev_evals.ft_eval1".into(), format!("{:?}", pe.ft_eval1));
    let e = &pe.evals.evals;
    for (i, x) in e.w.0.iter().enumerate() {
        put(format!("prev_evals.evals.evals.w[{i}]"), epair(x));
    }
    for (i, x) in e.coefficients.0.iter().enumerate() {
        put(
            format!("prev_evals.evals.evals.coefficients[{i}]"),
            epair(x),
        );
    }
    put("prev_evals.evals.evals.z".into(), epair(&e.z));
    for (i, x) in e.s.0.iter().enumerate() {
        put(format!("prev_evals.evals.evals.s[{i}]"), epair(x));
    }
    put(
        "prev_evals.evals.evals.generic_selector".into(),
        epair(&e.generic_selector),
    );
    put(
        "prev_evals.evals.evals.poseidon_selector".into(),
        epair(&e.poseidon_selector),
    );
    put(
        "prev_evals.evals.evals.complete_add_selector".into(),
        epair(&e.complete_add_selector),
    );
    put(
        "prev_evals.evals.evals.mul_selector".into(),
        epair(&e.mul_selector),
    );
    put(
        "prev_evals.evals.evals.emul_selector".into(),
        epair(&e.emul_selector),
    );
    put(
        "prev_evals.evals.evals.endomul_scalar_selector".into(),
        epair(&e.endomul_scalar_selector),
    );

    let pf = &p.proof;
    for (i, x) in pf.commitments.w_comm.0.iter().enumerate() {
        put(format!("proof.commitments.w_comm[{i}]"), pair(x));
    }
    put(
        "proof.commitments.z_comm".into(),
        pair(&pf.commitments.z_comm),
    );
    for (i, x) in pf.commitments.t_comm.0.iter().enumerate() {
        put(format!("proof.commitments.t_comm[{i}]"), pair(x));
    }
    for (i, x) in pf.evaluations.w.0.iter().enumerate() {
        put(format!("proof.evaluations.w[{i}]"), pair(x));
    }
    for (i, x) in pf.evaluations.coefficients.0.iter().enumerate() {
        put(format!("proof.evaluations.coefficients[{i}]"), pair(x));
    }
    put("proof.evaluations.z".into(), pair(&pf.evaluations.z));
    for (i, x) in pf.evaluations.s.0.iter().enumerate() {
        put(format!("proof.evaluations.s[{i}]"), pair(x));
    }
    put(
        "proof.evaluations.generic_selector".into(),
        pair(&pf.evaluations.generic_selector),
    );
    put(
        "proof.evaluations.poseidon_selector".into(),
        pair(&pf.evaluations.poseidon_selector),
    );
    put(
        "proof.evaluations.complete_add_selector".into(),
        pair(&pf.evaluations.complete_add_selector),
    );
    put(
        "proof.evaluations.mul_selector".into(),
        pair(&pf.evaluations.mul_selector),
    );
    put(
        "proof.evaluations.emul_selector".into(),
        pair(&pf.evaluations.emul_selector),
    );
    put(
        "proof.evaluations.endomul_scalar_selector".into(),
        pair(&pf.evaluations.endomul_scalar_selector),
    );
    put("proof.ft_eval1".into(), format!("{:?}", pf.ft_eval1));
    for (i, (l, r)) in pf.bulletproof.lr.iter().enumerate() {
        put(
            format!("proof.bulletproof.lr[{i}]"),
            format!("{}/{}", pair(l), pair(r)),
        );
    }
    put(
        "proof.bulletproof.z_1".into(),
        format!("{:?}", pf.bulletproof.z_1),
    );
    put(
        "proof.bulletproof.z_2".into(),
        format!("{:?}", pf.bulletproof.z_2),
    );
    put(
        "proof.bulletproof.delta".into(),
        pair(&pf.bulletproof.delta),
    );
    put(
        "proof.bulletproof.challenge_polynomial_commitment".into(),
        pair(&pf.bulletproof.challenge_polynomial_commitment),
    );
    v
}

/// The named wire fields on which two records differ.
pub fn field_diff(
    a: &PicklesProofProofsVerified2ReprStableV2,
    b: &PicklesProofProofsVerified2ReprStableV2,
) -> Vec<String> {
    let (ta, tb) = (field_table(a), field_table(b));
    assert_eq!(ta.len(), tb.len(), "field tables must be the same shape");
    ta.iter()
        .zip(tb.iter())
        .filter(|((ka, va), (kb, vb))| {
            assert_eq!(ka, kb, "field tables must be in the same order");
            va != vb
        })
        .map(|((k, _), _)| k.clone())
        .collect()
}

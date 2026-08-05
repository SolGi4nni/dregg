//! **THE PROVER'S SIDE OF WHAT PICKLES DEFERS.**
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! Nothing in this module is an AIR. It authors no constraint, no `Builder` gadget and no
//! `air_accepts` predicate. It is a **prover**: it reads scalars out of a kimchi proof that our
//! own prover produced, and it evaluates one 65,536-point multi-scalar multiplication natively.
//! Both of those are Rust's job. The circuit stays in Lean.
//!
//! ## What was missing, measured
//!
//! `marshal::WrapStatementScalars` is the caller's half of a wrap statement, and until this module
//! existed **every scalar in it was a counter** — `pickles_kimchi_marshal.rs` filled α, β, γ, ζ,
//! the sixteen bulletproof challenges and the sponge digest from `k(n) = n·0x9E3779B97F4A7C15 | 1`,
//! and the next-wrap accumulator from `Vesta::generator() * 7`. `marshal.rs`'s own header said so:
//! *"everything else in `statement.proof_state` | caller | `wrap_main`'s output, **which we do not
//! yet produce**."*
//!
//! Those are not free values. Two of them are **checked natively by Mina before it ever consults a
//! verification key**:
//!
//! * `messages_for_next_wrap_proof.challenge_polynomial_commitment` must be the multi-scalar
//!   multiplication of the SRS by the challenge polynomial of `deferred_values.
//!   bulletproof_challenges` — openmina `proofs/accumulator_check.rs:10-64` →
//!   `urs_utils.rs:11-68`, OCaml `verify.ml:135-146`. `7·G` fails this arithmetically and **no
//!   circuit change affects it**.
//! * the rest are the Fiat–Shamir transcript of the **previous step proof** — the object
//!   `expand_deferred` (`proofs/step.rs:1915-2072`) re-derives from `prev_evals` before handing
//!   its own recomputation on. A counter there is not refused; it is silently replaced, and then
//!   the wrap circuit's public input is a statement about a proof that does not exist.
//!
//! [`accumulator`] produces the first. [`step_transcript`] produces the second, by running
//! **kimchi's own verifier-side Fiat–Shamir** (`ProverProof::oracles`, `verifier.rs:126-290`) over
//! a step proof we actually proved, and then the IPA prechallenge squeezes in the order
//! `poly-commitment/src/ipa.rs:190-198` performs them.
//!
//! ## ⚑ The fork that was not a fork
//!
//! The first run of this module reported ξ disagreeing between `expand_deferred` and the step
//! proof's own transcript, and the disagreement was written up as a protocol difference: *"Pickles
//! restarts from `sponge_digest_before_evaluations`, absorbs a `challenges_digest` that kimchi has
//! no notion of."* **kimchi has exactly that notion.** `verifier.rs:289-299` absorbs a
//! `prev_challenge_digest` over the proof's own recursion challenges at the same position, and the
//! two evaluation orders are the same list (`plonk_sponge.rs:87-…` and `util.rs:215-258` both open
//! `z, generic, poseidon, complete_add, mul, emul, endomul_scalar` and then `w, coefficients, s`).
//! openmina's step prover is stock `kimchi::proof::ProverProof::create_recursive` with the stock
//! `DefaultFrSponge` (`transaction.rs:3976, 4009`), so there is no second sponge anywhere.
//!
//! What actually differed was that the step proof was proved with **zero** recursion slots while
//! the statement claimed **two**, filled with counters. Give the proof the two slots the statement
//! claims and ξ, `b` and `combined_inner_product` agree bit-for-bit. The lesson is the cheap one:
//! a disagreement between two implementations is a hypothesis about the implementations and a
//! hypothesis about the inputs, and the inputs are the one to check first.
//!
//! `marshal::MarshalError::StepPreChallengeMismatch` is what keeps it closed — the statement's
//! step-side prechallenges must endo-expand to the ones the step proof folded.

use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{One, PrimeField};
use ark_poly::EvaluationDomain as _;
use kimchi::oracles::OraclesResult;
use kimchi::verifier_index::VerifierIndex;
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::pasta::FULL_ROUNDS;
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
use mina_poseidon::FqSponge as _;
use poly_commitment::commitment::{b_poly, b_poly_coefficients, shift_scalar};
use poly_commitment::ipa::SRS;
use poly_commitment::{PolyComm, SRS as _};

use crate::marshal::{expand_step_prechallenge, PreChallenge, StepKimchiProof, STEP_ROUNDS};

/// The step side is Vesta-committed and `Fp`-scalar (`wrap_main_inputs.ml:4,6` sets `Me = Tock`,
/// so the proof a wrap verifies is Tick).
pub type StepBase = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
pub type StepScalar = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// The step verifier index shape this module reads.
pub type StepVerifierIndex = VerifierIndex<FULL_ROUNDS, Vesta, SRS<Vesta>>;

/// `|srs.g|` on the Tick side — `Fq::SRS_DEPTH`, `mina-rust/crates/ledger/src/proofs/field.rs:125`,
/// and the length `b_poly_coefficients` of sixteen challenges tiles exactly.
pub const TICK_SRS_LEN: usize = 1 << STEP_ROUNDS;

// ───────────────────────── the endo lift, and whose it is ─────────────────────────

/// **Does kimchi's endo lift equal the one Pickles' native accumulator check applies?**
///
/// `accumulator_check.rs:23-38` lifts each wire prechallenge with
/// `ledger::…::ScalarChallenge::limbs_to_field::<Fp>`, which is openmina's own re-implementation
/// of `scalar_challenge.ml`. Our step proof's IPA challenges come from kimchi's `squeeze_challenge`.
/// If those two disagree the accumulator can never match, and the disagreement would be invisible
/// — both produce a perfectly good field element. So it is MEASURED, not assumed.
pub fn endo_lift_agrees_with_mina(c: &PreChallenge) -> bool {
    use ledger::proofs::public_input::scalar_challenge::ScalarChallenge as MinaScalarChallenge;
    expand_step_prechallenge(c) == MinaScalarChallenge::limbs_to_field::<Fp>(c)
}

/// The two limbs of a 128-bit challenge squeezed as a field element.
///
/// Refuses rather than truncating: a `challenge()` squeeze is 128 bits by construction
/// (`sponge.rs`, `squeeze_limbs`), and anything wider here means the sponge was read wrong.
pub fn limbs_of(v: &Fp) -> PreChallenge {
    let b = v.into_bigint().0;
    assert_eq!(
        (b[2], b[3]),
        (0, 0),
        "a 128-bit challenge does not fit two limbs: {v}"
    );
    [b[0], b[1]]
}

/// The four limbs of a full field element — what the wire's `sponge_digest_before_evaluations`
/// and both `messages_for_next_*_proof` hashes carry.
pub fn limbs4_of(v: &Fp) -> [u64; 4] {
    v.into_bigint().0
}

// ───────────────────────── Gate A, from the prover's side ─────────────────────────

/// **`⟨ b_poly_coefficients(u⃗), srs.g ⟩`** — the accumulator Pickles will recompute and compare.
///
/// This is the *prover's* side of `batch_dlog_accumulator_check` (`urs_utils.rs:11-68`). The
/// verifier folds `N` claims at one random `r` and asks whether the batch vanishes; the prover
/// simply evaluates the claim. Same object, opposite direction.
///
/// `srs` must be the SRS the deferred claim is stated over — `get_srs::<Fp>()`, i.e.
/// `SRS::<Vesta>::create(65536)`. Passing a different SRS produces a point that is perfectly
/// well-formed and that Mina refuses, which is the whole hazard this signature makes explicit.
pub fn accumulator(srs: &SRS<Vesta>, chals: &[PreChallenge]) -> Vesta {
    let fields: Vec<Fp> = chals.iter().map(expand_step_prechallenge).collect();
    let coeffs = b_poly_coefficients(&fields);
    assert_eq!(
        coeffs.len(),
        srs.g.len(),
        "the challenge polynomial has {} coefficients and the SRS has {} generators — \
         b_poly_coefficients of {} challenges does not tile this SRS",
        coeffs.len(),
        srs.g.len(),
        chals.len()
    );
    let bigs: Vec<_> = coeffs.iter().map(|c| c.into_bigint()).collect();
    <Vesta as AffineRepr>::Group::msm_bigint(&srs.g, &bigs).into_affine()
}

// ───────────────────────── the step proof's real transcript ─────────────────────────

/// Every scalar of a wrap statement that is a fact about the **previous step proof**, read out of
/// an actual step proof by running the verifier's own Fiat–Shamir over it.
#[derive(Debug, Clone)]
pub struct StepTranscript {
    /// `RandomOracles::alpha_chal` — the prechallenge, not the endo-expanded `alpha`.
    pub alpha: PreChallenge,
    /// `RandomOracles::beta` — a raw 128-bit squeeze, NOT a scalar challenge. The wire carries it
    /// as two bare limbs (`PaddedSeq<Hex64, 2>`) and `expand_deferred` uses it unlifted.
    pub beta: PreChallenge,
    /// `RandomOracles::gamma` — likewise raw.
    pub gamma: PreChallenge,
    /// `RandomOracles::zeta_chal`.
    pub zeta: PreChallenge,
    /// `RandomOracles::v_chal` — Pickles calls it ξ. Not on the wire; Pickles re-squeezes it, and
    /// this is what its re-squeeze is compared against.
    pub xi: PreChallenge,
    /// `RandomOracles::u_chal` — Pickles calls it r. Also re-squeezed, also not on the wire.
    pub r: PreChallenge,
    /// `OraclesResult::digest` — the Fq-sponge state at the moment before evaluations are
    /// absorbed. This IS `sponge_digest_before_evaluations`.
    pub sponge_digest: [u64; 4],
    /// The sixteen IPA prechallenges, in round order.
    pub bulletproof_challenges: [PreChallenge; STEP_ROUNDS],
    /// `OraclesResult::combined_inner_product`, kimchi's. Not on the wire.
    pub combined_inner_product: Fp,
    /// `b_poly(u⃗, ζ) + r·b_poly(u⃗, ζω)`. Not on the wire.
    pub b: Fp,
    /// `log2` of the step proof's evaluation domain — the wire's `branch_data.domain_log2`.
    pub domain_log2: u8,
    /// The step proof's own `opening.sg`. If the IPA is honest this equals
    /// [`accumulator`] of `bulletproof_challenges`; the binary MEASURES that rather than
    /// assuming it.
    pub sg: Vesta,
}

/// Commit to the **negated** public input polynomial.
///
/// Transcribed from `kimchi/src/verifier.rs:834-857`, which is a private prologue of `to_batch`
/// and cannot be called. It is not a re-derivation: `oracles` absorbs this commitment
/// (`verifier.rs:171`) and every challenge downstream depends on it, so a transcript computed
/// against a different `public_comm` is a transcript of nothing.
fn public_comm(index: &StepVerifierIndex, public_input: &[Fp]) -> PolyComm<Vesta> {
    let d1_size = index.domain.size();
    let chunk_size = if d1_size < index.max_poly_size {
        1
    } else {
        d1_size / index.max_poly_size
    };
    assert_eq!(
        public_input.len(),
        index.public,
        "public input length {} != verifier index public {}",
        public_input.len(),
        index.public
    );
    let lgr_comm = index.srs().get_lagrange_basis(index.domain);
    let com: Vec<_> = lgr_comm.iter().take(index.public).collect();
    if public_input.is_empty() {
        PolyComm::new(vec![index.srs().blinding_commitment(); chunk_size])
    } else {
        let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
        let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
        index
            .srs()
            .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
            .expect("mask_custom")
            .commitment
    }
}

/// **Run the verifier's Fiat–Shamir over a step proof and keep every scalar a wrap statement
/// needs.**
///
/// The order matters and is not ours: `oracles` (`verifier.rs:126-290`) leaves the Fq-sponge
/// positioned exactly where the IPA expects it, then `ipa.rs:190-198` absorbs
/// `shift_scalar(combined_inner_product)`, squeezes the group-map point `t`, and only then walks
/// the `lr` rounds. `OpeningProof::prechallenges` (`ipa.rs:996-1010`) performs the `t` squeeze
/// itself, so it is NOT squeezed here.
pub fn step_transcript(
    proof: &StepKimchiProof,
    index: &StepVerifierIndex,
    public_input: &[Fp],
) -> StepTranscript {
    let pc = public_comm(index, public_input);
    let OraclesResult {
        mut fq_sponge,
        digest,
        oracles,
        combined_inner_product,
        ..
    } = proof
        .oracles::<StepBase, StepScalar, _>(index, &pc, Some(public_input))
        .expect("the step proof's own oracles must run");

    fq_sponge.absorb_fr(&[shift_scalar::<Vesta>(combined_inner_product)]);
    let prechals = proof.proof.prechallenges::<StepBase>(&mut fq_sponge);
    assert_eq!(
        prechals.len(),
        STEP_ROUNDS,
        "a Tick IPA has {STEP_ROUNDS} rounds; this proof has {} — its max_poly_size is not 2^{}",
        prechals.len(),
        STEP_ROUNDS
    );
    let bulletproof_challenges: [PreChallenge; STEP_ROUNDS] =
        std::array::from_fn(|i| limbs_of(&prechals[i].0));

    // `b` as `expand_deferred` computes it (`step.rs:2044-2048`), with the challenges lifted the
    // same way and `r` the transcript's own.
    let lifted: Vec<Fp> = bulletproof_challenges
        .iter()
        .map(expand_step_prechallenge)
        .collect();
    let zetaw = oracles.zeta * index.domain.group_gen;
    let b = b_poly(&lifted, oracles.zeta) + oracles.u * b_poly(&lifted, zetaw);

    StepTranscript {
        alpha: limbs_of(&oracles.alpha_chal.0),
        beta: limbs_of(&oracles.beta),
        gamma: limbs_of(&oracles.gamma),
        zeta: limbs_of(&oracles.zeta_chal.0),
        xi: limbs_of(&oracles.v_chal.0),
        r: limbs_of(&oracles.u_chal.0),
        sponge_digest: limbs4_of(&digest),
        bulletproof_challenges,
        combined_inner_product,
        b,
        domain_log2: index.domain.log_size_of_group as u8,
        sg: proof.proof.sg,
    }
}

/// The challenge polynomial of a prechallenge vector, evaluated at `x`. The binary uses it to
/// report the `b` identity without importing `poly_commitment`.
pub fn challenge_poly_at(chals: &[PreChallenge], x: Fp) -> Fp {
    let lifted: Vec<Fp> = chals.iter().map(expand_step_prechallenge).collect();
    b_poly(&lifted, x)
}

//! A product-of-two-multilinears sumcheck, proved and verified end-to-end with
//! `p3-sumcheck` at the workspace's pinned Plonky3 revision (82cfad73).
//!
//! # What the protocol here actually proves
//!
//! Given two multilinear extensions `f, g : {0,1}^n -> BabyBear` held as full
//! evaluation tables, and a claimed value `S`, the prover convinces a verifier
//! that
//!
//! ```text
//!     S = sum_{x in {0,1}^n} f(x) * g(x)
//! ```
//!
//! by `n` rounds of quadratic sumcheck, reducing the claim to a single point
//! `r in EF^n`. What is left at the end is a *pair* of obligations:
//!
//! - `g(r)`, which the verifier computes itself (`g` is public here), and
//! - `f(r)`, which the prover *asserts* and the verifier cannot check.
//!
//! ⚠ That second obligation is the whole reason a sumcheck is not on its own an
//! argument of knowledge: this toy has **no polynomial commitment**, so
//! `proof.final_eval` is an unbacked claim about `f`. A real deployment discharges
//! it against a commitment to `f` (that is what `p3-sumcheck`'s `layout` module
//! and its `OpeningProtocol` exist for). Everything upstream of that final
//! opening — the round messages, the Fiat-Shamir binding, the fold — is real and
//! is what this crate measures. Do not read a passing [`verify_product`] as
//! "the prover knew an `f`".
//!
//! # What is NOT authored here
//!
//! No constraint system, no AIR, no gadget. `p3-sumcheck` has a `Constraint` type
//! for absorbing STIR/WHIR evaluation claims between folding rounds; this crate
//! passes `None` to it in every call and never builds one. The vector-relation
//! descriptor that M1 needs is a Lean object.

use core::fmt;

use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{DuplexChallenger, FieldChallenger};
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PackedValue, PrimeCharacteristicRing, PrimeField32};
use p3_multilinear_util::point::Point;
use p3_multilinear_util::poly::Poly;
use p3_sumcheck::product_polynomial::ProductPolynomial;
use p3_sumcheck::strategy::{SumcheckProver, VariableOrder};
use p3_sumcheck::{SumcheckData, SumcheckError};
use p3_util::log2_strict_usize;

/// Base field. Same field the deployed STARK prover uses.
pub type F = BabyBear;

/// Challenge field: the degree-4 binomial extension, ~2^123.6 of usable
/// challenge space at BabyBear.
pub type EF = BinomialExtensionField<BabyBear, 4>;

/// Width-16 Poseidon2 over BabyBear.
pub type Perm16 = Poseidon2BabyBear<16>;

/// The Fiat-Shamir transcript. Structurally identical to the deployed
/// `DuplexChallenger<P3BabyBear, Perm16, 16, 8>` in `circuit/src/stark_zk.rs`
/// and `circuit/src/plonky3_prover.rs`, and to `p3-sumcheck`'s own test
/// challenger — with one deliberate difference: the permutation constants are
/// the audited `default_babybear_poseidon2_16()` the node runs, not the
/// RNG-derived constants the upstream tests use.
pub type Challenger = DuplexChallenger<F, Perm16, 16, 8>;

/// Builds a fresh transcript over the deployed Poseidon2 constants.
///
/// Prover and verifier must each start from one of these and observe exactly
/// the same things in exactly the same order.
#[must_use]
pub fn challenger() -> Challenger {
    Challenger::new(default_babybear_poseidon2_16())
}

/// Which backing representation the prover uses for the round polynomials.
///
/// Both are the same protocol and must produce byte-identical transcripts; the
/// choice is purely how the `2^n` evaluations are laid out in memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Packing {
    /// SIMD-packed extension elements. Requires `n >= log2(F::Packing::WIDTH)`;
    /// falls back to scalar automatically once folding shrinks it that far.
    Packed,
    /// One scalar extension element per hypercube point.
    Scalar,
}

/// Everything the prover sends.
#[derive(Clone, Debug)]
pub struct ProductSumcheckProof {
    /// One `[h(0), h(inf)]` pair per round, plus PoW witnesses if grinding is on.
    pub rounds: SumcheckData<F, EF>,
    /// The prover's claim for `f(r)` at the point the rounds folded down to.
    ///
    /// ⚠ Unbacked in this toy — see the module docblock.
    pub final_eval: EF,
}

/// Why [`verify_product`] refused.
#[derive(Debug)]
pub enum VerifyError {
    /// The proof carries a different number of rounds than `g` has variables.
    RoundCount { expected: usize, actual: usize },
    /// `p3-sumcheck`'s own round verification refused (PoW, shape).
    Sumcheck(SumcheckError),
    /// The folded claim did not equal `f(r) * g(r)`.
    FinalCheck { folded: EF, expected: EF },
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RoundCount { expected, actual } => {
                write!(f, "round count mismatch: expected {expected}, got {actual}")
            }
            Self::Sumcheck(e) => write!(f, "sumcheck round verification failed: {e}"),
            Self::FinalCheck { folded, expected } => {
                write!(
                    f,
                    "final check failed: folded {folded:?} != f(r)*g(r) {expected:?}"
                )
            }
        }
    }
}

/// The honest sum `sum_{x} f(x) * g(x)`, computed in the base field.
///
/// # Panics
///
/// - `f` and `g` must have the same number of variables.
pub fn product_sum(f: &Poly<F>, g: &Poly<F>) -> EF {
    assert_eq!(
        f.num_variables(),
        g.num_variables(),
        "product sumcheck needs both multilinears over the same hypercube"
    );
    let s: F = f.iter().zip(g.iter()).map(|(&a, &b)| a * b).sum::<F>();
    EF::from(s)
}

/// Runs the prover.
///
/// `challenger` is advanced by `2n` extension elements observed (`h(0)`, `h(inf)`
/// per round), `n` challenges sampled, one grind per round if `pow_bits > 0`, and
/// finally one observation of `final_eval`. A verifier must replay exactly that.
///
/// Returns the honest claimed sum alongside the proof, so a caller can see the
/// value the transcript was actually built for.
///
/// # Panics
///
/// - `f` and `g` must have the same, nonzero, number of variables.
/// - [`Packing::Packed`] needs `n >= log2(F::Packing::WIDTH)`.
pub fn prove_product(
    f: &Poly<F>,
    g: &Poly<F>,
    pow_bits: usize,
    packing: Packing,
    challenger: &mut Challenger,
) -> (EF, ProductSumcheckProof) {
    let n = f.num_variables();
    assert_eq!(n, g.num_variables(), "arity mismatch");
    assert!(n > 0, "a 0-variable sumcheck has no rounds to run");

    let claimed_sum = product_sum(f, g);

    // The prover works over EF throughout: the pair is (evals, weights) and both
    // get folded by the same extension-field challenge each round.
    let f_ef = Poly::new(f.iter().copied().map(EF::from).collect());
    let g_ef = Poly::new(g.iter().copied().map(EF::from).collect());

    let poly = match packing {
        Packing::Packed => {
            let lanes = log2_strict_usize(<F as Field>::Packing::WIDTH);
            assert!(
                n >= lanes,
                "packed mode needs at least log2(SIMD width) = {lanes} variables"
            );
            ProductPolynomial::new_packed(
                VariableOrder::Prefix,
                f_ef.pack::<F, EF>(),
                g_ef.pack::<F, EF>(),
            )
        }
        Packing::Scalar => ProductPolynomial::new_unpacked(VariableOrder::Prefix, f_ef, g_ef),
    };

    let mut prover = SumcheckProver::new(poly, claimed_sum);
    let mut rounds = SumcheckData::default();

    // All `n` rounds in one batch, no intermediate constraint absorption.
    let _r = prover.compute_sumcheck_polynomials(&mut rounds, challenger, n, pow_bits, None);

    // After n rounds both polynomials are constants; `evals()` is the f-side one.
    let final_eval = prover
        .evals()
        .as_constant()
        .expect("n rounds must fold an n-variable polynomial to a constant");

    // Bind the final claim into the transcript so anything sampled after this
    // point depends on it.
    challenger.observe_algebra_element(final_eval);

    (claimed_sum, ProductSumcheckProof { rounds, final_eval })
}

/// Runs the verifier.
///
/// `g` is public to the verifier here, so it evaluates `g(r)` itself. The
/// verifier never sees `f`.
///
/// On success returns the folding randomness `r`, which is what a real
/// deployment would hand to a PCS opening for `f`.
///
/// # Errors
///
/// [`VerifyError`] — round-count mismatch, a `p3-sumcheck` round failure, or the
/// final `folded == f(r) * g(r)` check.
pub fn verify_product(
    g: &Poly<F>,
    claimed_sum: EF,
    proof: &ProductSumcheckProof,
    pow_bits: usize,
    challenger: &mut Challenger,
) -> Result<Point<EF>, VerifyError> {
    let n = g.num_variables();
    if proof.rounds.num_rounds() != n {
        return Err(VerifyError::RoundCount {
            expected: n,
            actual: proof.rounds.num_rounds(),
        });
    }

    // `verify_rounds` folds `claimed_sum` forward through every round message
    // and hands back the challenges. It does NOT check the claim against
    // anything -- that is the caller's job, immediately below.
    let mut folded = claimed_sum;
    let r = proof
        .rounds
        .verify_rounds(challenger, &mut folded, pow_bits)
        .map_err(VerifyError::Sumcheck)?;

    // Same transcript step the prover took.
    challenger.observe_algebra_element(proof.final_eval);

    // `VariableOrder::Prefix` binds x_1 first, so the challenge point is read in
    // the same order the evaluation table is indexed. (`Suffix` would need
    // `r.reversed()` here.)
    let expected = proof.final_eval * g.eval_base::<EF>(&r);
    if folded == expected {
        Ok(r)
    } else {
        Err(VerifyError::FinalCheck { folded, expected })
    }
}

/// A deterministic multilinear over `n` variables, seeded by `seed`.
///
/// Deliberately not `rand`-backed: the workspace carries no `rand` at the 0.10
/// series Plonky3 uses, and a fixture that reproduces exactly is worth more here
/// than statistical quality. SplitMix64 -> reduce into BabyBear.
pub fn fixture_poly(n: usize, seed: u64) -> Poly<F> {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    let evals = (0..(1usize << n))
        .map(|_| {
            state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^= z >> 31;
            // Reduce into the field; BabyBear's canonical range is < 2^31 - 2^27 + 1.
            F::from_u64(z % u64::from(F::ORDER_U32))
        })
        .collect();
    Poly::new(evals)
}

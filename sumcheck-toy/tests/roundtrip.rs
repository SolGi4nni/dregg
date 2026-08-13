//! M0 gate: `p3-sumcheck` proves and verifies a product-of-two-multilinears at
//! the pinned Plonky3 rev, over BabyBear with Ext4 challenges, through the
//! DuplexChallenger the node deploys.
//!
//! Every rejection test below is CONSTRUCTIVE about its mutation: it asserts the
//! mutated object actually differs from the honest one before reading the
//! verifier's verdict. A falsifier that silently stops falsifying (a `replacen`
//! against a string that left the fixture; a corruption that lands on the same
//! value) leaves a green suite with no teeth, and that is a failure mode this
//! repo has paid for.

use p3_field::PrimeCharacteristicRing;
use p3_multilinear_util::poly::Poly;
use p3_sumcheck::SumcheckData;
use sumcheck_toy::{
    EF, F, Packing, ProductSumcheckProof, VerifyError, challenger, fixture_poly, product_sum,
    prove_product, verify_product,
};

const N: usize = 10;

fn fixtures() -> (Poly<F>, Poly<F>) {
    (fixture_poly(N, 0xF00D), fixture_poly(N, 0xBEEF))
}

/// Honest prove -> honest verify, both packings, with and without grinding.
#[test]
fn honest_roundtrip_accepts() {
    let (f, g) = fixtures();

    for packing in [Packing::Scalar, Packing::Packed] {
        for pow_bits in [0usize, 8] {
            let mut p_chal = challenger();
            let (claimed, proof) = prove_product(&f, &g, pow_bits, packing, &mut p_chal);

            assert_eq!(
                claimed,
                product_sum(&f, &g),
                "the prover must build its transcript for the true sum"
            );
            assert_eq!(proof.rounds.num_rounds(), N, "one round per variable");
            assert_eq!(
                proof.rounds.polynomial_evaluations().len(),
                N,
                "each round sends exactly [h(0), h(inf)]"
            );

            let mut v_chal = challenger();
            let r =
                verify_product(&g, claimed, &proof, pow_bits, &mut v_chal).unwrap_or_else(|e| {
                    panic!("{packing:?} pow={pow_bits}: honest proof rejected: {e}")
                });
            assert_eq!(
                r.num_variables(),
                N,
                "folding randomness has one coord per round"
            );

            // The final claim is the honest f(r) -- the verifier could not check
            // this (no commitment), but the test can.
            assert_eq!(
                proof.final_eval,
                f.eval_base::<EF>(&r),
                "prover's final_eval must be f(r) under Prefix binding"
            );
        }
    }
}

/// The two packings are the same protocol: identical transcript, identical proof.
#[test]
fn packed_and_scalar_agree_bit_for_bit() {
    let (f, g) = fixtures();

    let mut c1 = challenger();
    let (s1, p1) = prove_product(&f, &g, 0, Packing::Scalar, &mut c1);
    let mut c2 = challenger();
    let (s2, p2) = prove_product(&f, &g, 0, Packing::Packed, &mut c2);

    assert_eq!(s1, s2);
    assert_eq!(p1.final_eval, p2.final_eval);
    assert_eq!(
        p1.rounds.polynomial_evaluations(),
        p2.rounds.polynomial_evaluations(),
        "SIMD packing must not move a single round message"
    );
}

// ── teeth ────────────────────────────────────────────────────────────────────
//
// A verifier that never refuses is not a verifier. Each test below drives
// `verify_product` to a specific `Err`.

/// THE central tooth. A prover that lies about the sum runs the identical
/// protocol: the round messages `[h(0), h(inf)]` are computed from the
/// polynomials alone and do not depend on the claimed sum, and neither does the
/// fold. So "a lying prover" is exactly "an honest transcript carried by a wrong
/// `S`" -- and the only thing standing between that and acceptance is the final
/// `folded == f(r) * g(r)` check.
#[test]
fn wrong_claimed_sum_is_rejected() {
    let (f, g) = fixtures();

    let mut p_chal = challenger();
    let (honest, proof) = prove_product(&f, &g, 0, Packing::Packed, &mut p_chal);

    let lie = honest + EF::ONE;
    assert_ne!(lie, honest, "the mutation must actually change the claim");

    // Positive control: the same proof under the honest sum is accepted, so the
    // refusal below is attributable to the mutation and nothing else.
    let mut ok_chal = challenger();
    verify_product(&g, honest, &proof, 0, &mut ok_chal).expect("control: honest sum must verify");

    let mut v_chal = challenger();
    let err = verify_product(&g, lie, &proof, 0, &mut v_chal)
        .expect_err("a claimed sum off by one must be refused");
    assert!(
        matches!(err, VerifyError::FinalCheck { .. }),
        "expected FinalCheck, got {err}"
    );
}

/// Tampering with any round message desynchronises Fiat-Shamir from that round
/// on: the verifier samples different challenges, folds to a different point,
/// and the prover's `final_eval` no longer answers the question asked.
#[test]
fn tampered_round_message_is_rejected() {
    let (f, g) = fixtures();

    let mut p_chal = challenger();
    let (honest, proof) = prove_product(&f, &g, 0, Packing::Packed, &mut p_chal);

    for round in [0usize, N / 2, N - 1] {
        for coeff in [0usize, 1] {
            let mut evals = proof.rounds.polynomial_evaluations().to_vec();
            let before = evals[round][coeff];
            evals[round][coeff] += EF::ONE;
            assert_ne!(
                evals[round][coeff], before,
                "round {round} coeff {coeff}: mutation was a no-op"
            );

            let tampered = ProductSumcheckProof {
                rounds: SumcheckData {
                    polynomial_evaluations: evals,
                    pow_witnesses: proof.rounds.pow_witnesses.clone(),
                },
                final_eval: proof.final_eval,
            };

            let mut v_chal = challenger();
            let err = verify_product(&g, honest, &tampered, 0, &mut v_chal)
                .unwrap_err_or_panic(round, coeff);
            assert!(
                matches!(err, VerifyError::FinalCheck { .. }),
                "round {round} coeff {coeff}: expected FinalCheck, got {err}"
            );
        }
    }
}

/// The unbacked final evaluation is at least *bound*: forging it fails the last
/// multiplication. (This is not a substitute for a commitment to `f` -- an
/// adversary who also picks `f` freely is unconstrained here. See the crate
/// docblock.)
#[test]
fn forged_final_eval_is_rejected() {
    let (f, g) = fixtures();

    let mut p_chal = challenger();
    let (honest, proof) = prove_product(&f, &g, 0, Packing::Packed, &mut p_chal);

    let forged = ProductSumcheckProof {
        rounds: proof.rounds.clone(),
        final_eval: proof.final_eval + EF::ONE,
    };
    assert_ne!(forged.final_eval, proof.final_eval, "mutation was a no-op");

    let mut v_chal = challenger();
    let err = verify_product(&g, honest, &forged, 0, &mut v_chal)
        .expect_err("a forged f(r) must be refused");
    assert!(
        matches!(err, VerifyError::FinalCheck { .. }),
        "expected FinalCheck, got {err}"
    );
}

/// The weight polynomial is the verifier's own input. Verifying against a
/// different `g` must refuse -- otherwise the sumcheck would be proving a
/// relation nobody chose.
#[test]
fn wrong_weight_polynomial_is_rejected() {
    let (f, g) = fixtures();
    let g_other = fixture_poly(N, 0xC0FFEE);
    assert_ne!(
        g.as_slice(),
        g_other.as_slice(),
        "the two weight polynomials must actually differ"
    );

    let mut p_chal = challenger();
    let (honest, proof) = prove_product(&f, &g, 0, Packing::Packed, &mut p_chal);

    let mut v_chal = challenger();
    let err = verify_product(&g_other, honest, &proof, 0, &mut v_chal)
        .expect_err("verifying against a different weight polynomial must be refused");
    assert!(
        matches!(err, VerifyError::FinalCheck { .. }),
        "expected FinalCheck, got {err}"
    );
}

/// A short proof is refused on shape, before any field arithmetic.
#[test]
fn truncated_proof_is_rejected() {
    let (f, g) = fixtures();

    let mut p_chal = challenger();
    let (honest, proof) = prove_product(&f, &g, 0, Packing::Packed, &mut p_chal);

    let mut evals = proof.rounds.polynomial_evaluations().to_vec();
    evals.pop();
    assert_eq!(evals.len(), N - 1, "truncation must have removed a round");

    let truncated = ProductSumcheckProof {
        rounds: SumcheckData {
            polynomial_evaluations: evals,
            pow_witnesses: proof.rounds.pow_witnesses.clone(),
        },
        final_eval: proof.final_eval,
    };

    let mut v_chal = challenger();
    let err = verify_product(&g, honest, &truncated, 0, &mut v_chal)
        .expect_err("a proof with too few rounds must be refused");
    match err {
        VerifyError::RoundCount { expected, actual } => {
            assert_eq!(expected, N);
            assert_eq!(actual, N - 1);
        }
        other => panic!("expected RoundCount, got {other}"),
    }
}

/// With grinding on, a zeroed PoW witness must fail `p3-sumcheck`'s own check --
/// i.e. the `pow_bits` knob we pass through is actually load-bearing and not
/// silently dropped on the floor.
#[test]
fn zeroed_pow_witness_is_rejected() {
    let (f, g) = fixtures();
    const POW: usize = 8;

    let mut p_chal = challenger();
    let (honest, proof) = prove_product(&f, &g, POW, Packing::Packed, &mut p_chal);
    assert_eq!(
        proof.rounds.pow_witnesses.len(),
        N,
        "grinding must have produced one witness per round"
    );
    assert!(
        proof.rounds.pow_witnesses.iter().any(|w| *w != F::ZERO),
        "an all-zero honest witness vector would make this mutation a no-op"
    );

    let zeroed = ProductSumcheckProof {
        rounds: SumcheckData {
            polynomial_evaluations: proof.rounds.polynomial_evaluations().to_vec(),
            pow_witnesses: vec![F::ZERO; N],
        },
        final_eval: proof.final_eval,
    };

    let mut v_chal = challenger();
    let err = verify_product(&g, honest, &zeroed, POW, &mut v_chal)
        .expect_err("zeroed PoW witnesses must be refused");
    assert!(
        matches!(err, VerifyError::Sumcheck(_)),
        "expected a p3-sumcheck error, got {err}"
    );
}

/// Small helper so the nested loop above reports which mutation slipped through.
trait UnwrapErrOrPanic {
    fn unwrap_err_or_panic(self, round: usize, coeff: usize) -> VerifyError;
}

impl<T> UnwrapErrOrPanic for Result<T, VerifyError> {
    fn unwrap_err_or_panic(self, round: usize, coeff: usize) -> VerifyError {
        match self {
            Ok(_) => panic!("round {round} coeff {coeff}: tampered proof was ACCEPTED"),
            Err(e) => e,
        }
    }
}

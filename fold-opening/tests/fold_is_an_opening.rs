//! The demonstration: `fold_add` is certified by ONE common-point opening, on real
//! deployed-shape BFV ciphertexts — and each of the three binding conditions of
//! `~/dev/zkml-research/notes/fold-as-opening.md` §2.6 is shown to be **load-bearing**
//! by removing it and forging.
//!
//! House law: no constraint system is authored here or in the library. These are value
//! checks over an algebraic claim whose Lean statement is in the note.

use fold_opening::adversary::draw_point_without_coefficients;
use fold_opening::{
    CostModel, EF, F, FoldError, LIMB_BITS, LIMB_BOUND, LIMBS, RangeLeg, Shape, account, commit,
    fixture, flatten, lazy_fold, max_unit_batch, mle, prove, verify,
};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};

/// The batch the node actually folds: `ORDER_COUNT = 4`, fixed in
/// `metatheory/Market/DarkBazaarPrivateDescriptor.lean:44` and pinned by the session roster and the fixed-arity
/// proving family (`node/src/dark_clearing_service.rs`).
const DEPLOYED_BATCH: usize = 4;

fn batch(shape: Shape, b: usize) -> Vec<fhegg_core::bfv_lean::LeanCiphertext> {
    (0..b)
        .map(|k| fixture(shape, 0xF01D_0000 + k as u64))
        .collect()
}

// ---------------------------------------------------------------------------
// the shape we are actually talking about
// ---------------------------------------------------------------------------

#[test]
fn deployed_shape_is_what_the_node_folds() {
    let s = Shape::deployed();
    assert_eq!(s.degree, 4096, "FOLD_DEGREE");
    assert_eq!(s.moduli, 3, "FOLD_MODULI has three RNS primes");
    assert_eq!(s.polys, 2, "fold-path ciphertexts are always (c0, c1)");
    assert_eq!(s.residues(), 24_576, "M = P*L*N");
    assert_eq!(s.limbs(), 49_152, "M * LIMBS field elements");
    assert_eq!(s.num_variables(), 16, "mu = ceil(log2 49152) = 16");
}

#[test]
fn the_largest_modulus_needs_two_limbs_and_two_suffice() {
    let q_max = *fhegg_core::bfv_lean::FOLD_MODULI.iter().max().unwrap();
    assert!(
        q_max >= u64::from(F::ORDER_U32),
        "if the modulus fit BabyBear there would be no limb map to justify"
    );
    assert!(
        q_max < 1u64 << (LIMB_BITS * LIMBS as u32),
        "two 19-bit limbs must cover the 37-bit modulus"
    );
}

// ---------------------------------------------------------------------------
// the result
// ---------------------------------------------------------------------------

#[test]
fn one_common_point_opening_certifies_the_whole_fold() {
    let shape = Shape::deployed();
    let cts = batch(shape, DEPLOYED_BATCH);
    let coeffs = vec![1u64; DEPLOYED_BATCH];

    let acc = lazy_fold(&cts, &coeffs).expect("lazy fold");
    let proof = prove(&cts, &coeffs, &acc).expect("prove");
    let verified = verify(&proof).expect("the linear relation holds at the common point");

    // The whole protocol is B+1 evaluations and one field equation.
    assert_eq!(proof.values.len(), DEPLOYED_BATCH);
    assert_eq!(
        verified.point.num_variables(),
        16,
        "the opening obligation is at one point in EF^16"
    );
}

#[test]
fn linearity_is_a_polynomial_identity_not_a_lucky_point() {
    // The claim is `chat_out = sum_k a_k chat_k` AS POLYNOMIALS. If that is right the
    // identity holds at EVERY point, not just the transcript's. Check it at the
    // hypercube corners too, where the MLE is literally the limb vector.
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 64, // small so the corner sweep is cheap; the algebra is degree-free
    };
    let cts = batch(shape, 5);
    let coeffs = vec![1u64, 0, 1, 1, 0];
    let acc = lazy_fold(&cts, &coeffs).unwrap();

    let flats: Vec<_> = cts.iter().map(|c| mle(&flatten(c).unwrap())).collect();
    let out = mle(&acc.to_field());

    for corner in [0usize, 1, 2, 17, 511, 1023] {
        let pt = p3_multilinear_util::point::Point::<EF>::hypercube(corner, shape.num_variables());
        let lhs = out.eval_base(&pt);
        let rhs: EF = flats
            .iter()
            .zip(coeffs.iter())
            .map(|(f, &a)| f.eval_base(&pt) * F::from_u64(a))
            .sum();
        assert_eq!(lhs, rhs, "identity must hold at hypercube corner {corner}");
    }
}

#[test]
fn general_coefficients_work_not_only_zero_one() {
    // The deployed instance has a_k in {0,1} (the `side` bit). The statement is more
    // general; check it is, so the note's §2 is not quietly narrower than it claims.
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 256,
    };
    let cts = batch(shape, 3);
    let coeffs = vec![7u64, 11, 5];
    let acc = lazy_fold(&cts, &coeffs).unwrap();
    // weight 23 -> the range leg must widen with the coefficients, and it does.
    assert_eq!(acc.bound, 23 * (LIMB_BOUND - 1) + 1);
    let proof = prove(&cts, &coeffs, &acc).unwrap();
    let _ = verify(&proof).expect("weighted folds are certified the same way");
}

// ---------------------------------------------------------------------------
// binding condition (b): the no-reduction side condition, and its enforcement
// ---------------------------------------------------------------------------

#[test]
fn the_deployed_reducing_fold_breaks_the_identity() {
    // ⚑ THE LOAD-BEARING NEGATIVE RESULT. `bfv_lean::fold` reduces at every step
    // (`add_row`, bfv_lean.rs:497). Its output is NOT `sum_k c_k` over the integers, so
    // it does NOT satisfy the polynomial identity. The linear route therefore requires
    // CHANGING the deployed fold to lazy accumulation; it is not a proof about the
    // function as it stands today.
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 512,
    };
    // Big residues so a reduction certainly fires somewhere in the batch.
    let cts = batch(shape, 8);
    let coeffs = vec![1u64; 8];

    let reduced = fhegg_core::bfv_lean::fold(&cts, u64::MAX).expect("unbounded-t fold");
    let reduced_flat = flatten(&reduced).unwrap();
    let lazy = lazy_fold(&cts, &coeffs).unwrap();

    assert_ne!(
        reduced_flat,
        lazy.to_field(),
        "if these agreed, no reduction fired and the fixture is not exercising the point"
    );

    // And the identity fails on the reduced result, at the transcript point.
    let flats: Vec<_> = cts.iter().map(|c| mle(&flatten(c).unwrap())).collect();
    let commitments: Vec<_> = cts.iter().map(|c| commit(&flatten(c).unwrap())).collect();
    let out_commitment = commit(&reduced_flat);
    let coeff_f: Vec<F> = coeffs.iter().map(|&a| F::from_u64(a)).collect();
    let r = fold_opening::draw_point(shape, &commitments, &out_commitment, &coeff_f, lazy.bound);

    let lhs = mle(&reduced_flat).eval_base(&r);
    let rhs: EF = flats.iter().map(|f| f.eval_base(&r)).sum();
    assert_ne!(
        lhs, rhs,
        "the reducing fold must FAIL the linearity check — fail-closed, as designed"
    );
}

#[test]
fn a_field_wrap_forgery_passes_linearity_and_is_caught_by_the_range_leg() {
    // ⚑ This is the attack the range leg exists for. The linearity check proves equality
    // mod p. A result equal to the true sum PLUS p is therefore accepted by it. Only the
    // range leg separates them.
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 128,
    };
    let cts = batch(shape, DEPLOYED_BATCH);
    let coeffs = vec![1u64; DEPLOYED_BATCH];
    let honest = lazy_fold(&cts, &coeffs).unwrap();

    let mut forged = honest.clone();
    forged.limbs[7] += u64::from(F::ORDER_U32); // + p: invisible in F, real in Z

    // Linearity alone cannot tell them apart: the F-images are identical, so every
    // check that lives in F — including the common-point evaluation — accepts both.
    let image = |acc: &fold_opening::LimbAccumulator| -> Vec<F> {
        acc.limbs.iter().map(|&v| F::from_u64(v)).collect()
    };
    assert_eq!(
        image(&honest),
        image(&forged),
        "adding p is invisible to every check that lives in F"
    );

    // The range leg refuses. Note it is the DECLARED bound that does the work.
    let leg = RangeLeg::for_unit_batch(DEPLOYED_BATCH);
    leg.check(&honest).expect("honest accumulator is in range");
    let err = leg.check(&forged).unwrap_err();
    assert!(
        matches!(err, FoldError::OutOfRange { index: 7, .. }),
        "the range leg must catch the p-shifted limb, got {err}"
    );

    // And `prove` refuses to build the forgery in the first place.
    forged.bound = honest.bound;
    assert!(matches!(
        prove(&cts, &coeffs, &forged).unwrap_err(),
        FoldError::OutOfRange { .. }
    ));
}

#[test]
fn a_bound_at_or_above_the_field_order_is_refused_as_vacuous() {
    // "Prove the floor false": a range leg whose bound is >= p excludes nothing, and a
    // check that excludes nothing must refuse rather than pass.
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 64,
    };
    let cts = batch(shape, 2);
    let mut acc = lazy_fold(&cts, &[1, 1]).unwrap();
    acc.bound = u64::from(F::ORDER_U32) + 1;
    let err = prove(&cts, &[1, 1], &acc).unwrap_err();
    assert!(matches!(err, FoldError::BoundExceedsField { .. }), "{err}");
}

#[test]
fn the_batch_ceiling_is_where_the_accumulator_would_wrap_the_field() {
    let b_max = max_unit_batch();
    // 19-bit limbs in BabyBear: p/(2^19 - 1).
    assert_eq!(b_max, 3840, "the unit-coefficient batch ceiling at w=19");
    assert!(
        (b_max as u64) * (LIMB_BOUND - 1) < u64::from(F::ORDER_U32),
        "at the ceiling the accumulator still fits"
    );
    assert!(
        (b_max as u64 + 1) * (LIMB_BOUND - 1) >= u64::from(F::ORDER_U32),
        "one past it, it does not"
    );
    assert!(
        b_max > DEPLOYED_BATCH,
        "the ceiling is nowhere near the deployed batch of {DEPLOYED_BATCH}"
    );
}

// ---------------------------------------------------------------------------
// binding condition (a): the coefficients must precede the challenge
// ---------------------------------------------------------------------------

#[test]
fn forges_when_coefficients_are_chosen_after_the_challenge() {
    // ⚑ A TOTAL BREAK, demonstrated. Remove one line from the transcript — the
    // coefficients — and the prover solves ONE equation in B unknowns for ANY result.
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 128,
    };
    let cts = batch(shape, DEPLOYED_BATCH);
    let honest_coeffs = vec![1u64; DEPLOYED_BATCH];

    // The prover wants a result that is NOT the fold: a completely unrelated ciphertext.
    let lie = fixture(shape, 0xDEAD_BEEF);
    let lie_flat = flatten(&lie).unwrap();

    let flats: Vec<Vec<F>> = cts.iter().map(|c| flatten(c).unwrap()).collect();
    let commitments: Vec<_> = flats.iter().map(|f| commit(f)).collect();
    let out_commitment = commit(&lie_flat);
    let bound = RangeLeg::for_unit_batch(DEPLOYED_BATCH).bound;

    // BROKEN ORDER: r is drawn before the coefficients exist.
    let r = draw_point_without_coefficients(shape, &commitments, &out_commitment, bound);

    let vals: Vec<EF> = flats.iter().map(|f| mle(f).eval_base(&r)).collect();
    let target = mle(&lie_flat).eval_base(&r);

    // Solve a_0 * v_0 = target - sum_{k>0} a_k v_k. One equation, B unknowns, closed form.
    let tail: EF = vals[1..]
        .iter()
        .zip(honest_coeffs[1..].iter())
        .map(|(&v, &a)| v * F::from_u64(a))
        .sum();
    let forged_a0 = (target - tail) * vals[0].inverse();

    let mut forged: Vec<EF> = honest_coeffs[1..]
        .iter()
        .map(|&a| EF::from(F::from_u64(a)))
        .collect();
    forged.insert(0, forged_a0);

    let check: EF = vals.iter().zip(forged.iter()).map(|(&v, &a)| v * a).sum();
    assert_eq!(
        check, target,
        "with r already fixed, a coefficient vector certifying an ARBITRARY result exists \
         and is computed in closed form — binding condition (a) is not decoration"
    );

    // And the correct order defeats it: absorbing the forged coefficients moves r, and
    // the forged a_0 no longer solves the equation at the new point.
    let honest_a: Vec<F> = honest_coeffs.iter().map(|&a| F::from_u64(a)).collect();
    let r2 = fold_opening::draw_point(shape, &commitments, &out_commitment, &honest_a, bound);
    let vals2: Vec<EF> = flats.iter().map(|f| mle(f).eval_base(&r2)).collect();
    let target2 = mle(&lie_flat).eval_base(&r2);
    let check2: EF = vals2.iter().zip(forged.iter()).map(|(&v, &a)| v * a).sum();
    assert_ne!(
        check2, target2,
        "under the correct transcript order the same forgery fails"
    );
}

#[test]
fn a_mutated_result_is_caught() {
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 256,
    };
    let cts = batch(shape, DEPLOYED_BATCH);
    let coeffs = vec![1u64; DEPLOYED_BATCH];
    let mut acc = lazy_fold(&cts, &coeffs).unwrap();

    // Constructive mutation, asserted to have happened (a `replacen` that silently
    // matched nothing is how a falsifier stops falsifying).
    let before = acc.limbs[1234];
    acc.limbs[1234] = if before == 0 { 1 } else { before - 1 };
    assert_ne!(acc.limbs[1234], before, "the mutation must actually mutate");

    let proof = prove(&cts, &coeffs, &acc).expect("still in range, so it builds");
    let err = verify(&proof).unwrap_err();
    assert!(matches!(err, FoldError::LinearityFailed { .. }), "{err}");
}

#[test]
fn a_swapped_coefficient_vector_is_caught() {
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 256,
    };
    let cts = batch(shape, DEPLOYED_BATCH);
    let acc = lazy_fold(&cts, &[1, 1, 0, 0]).unwrap();
    // The prover folded the demand side but claims the supply side's selector.
    let mut proof = prove(&cts, &[1, 1, 0, 0], &acc).unwrap();
    proof.coeffs = vec![F::ZERO, F::ZERO, F::ONE, F::ONE];
    let err = verify(&proof).unwrap_err();
    assert!(matches!(err, FoldError::LinearityFailed { .. }), "{err}");
}

// ---------------------------------------------------------------------------
// binding condition (c): input binding — NAMED, NOT CLOSED
// ---------------------------------------------------------------------------

#[test]
fn input_binding_is_a_commitment_not_a_wire_digest() {
    // The commitment this protocol needs is over `flat(c)` — the LIMB vector in a fixed
    // layout. `order_ingress` binds an order by a digest of its proto3 wire bytes. They
    // are different functions of the same ciphertext, and nothing in this crate bridges
    // them. Asserting the difference so the seam cannot be forgotten.
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 64,
    };
    let ct = fixture(shape, 1);
    let mle_commitment = commit(&flatten(&ct).unwrap());
    let wire = ct.to_fhe_bytes();
    let wire_digest = commit(
        &wire
            .iter()
            .map(|&b| F::from_u64(u64::from(b)))
            .collect::<Vec<_>>(),
    );
    assert_ne!(
        mle_commitment, wire_digest,
        "the MLE commitment and the wire digest are different objects; closing (c) means \
         REPLACING the ingress commitment, not relating them in-circuit"
    );
}

// ---------------------------------------------------------------------------
// the ratio
// ---------------------------------------------------------------------------

#[test]
fn the_ratio_is_b_under_marginal_accounting_and_saturates_under_total() {
    let shape = Shape::deployed();
    let model = CostModel::default();

    let deployed = account(shape, DEPLOYED_BATCH, model);
    let big = account(shape, 512, model);
    let ceiling = account(shape, max_unit_batch(), model);

    // Marginal: inputs already committed (the attestation binds them anyway). Grows
    // linearly in B — this is the accounting in which "ratio = B" is true.
    // 7*(B-1)/5 exactly, under the conservative column model.
    assert!(
        (deployed.marginal_ratio() - 4.2).abs() < 0.01,
        "deployed marginal ratio {:.2}",
        deployed.marginal_ratio()
    );
    assert!(
        big.marginal_ratio() > 600.0 && big.marginal_ratio() < 800.0,
        "B=512 marginal ratio {:.1} should land near the briefed 690x",
        big.marginal_ratio()
    );
    // Linearity of the ratio in B, to two batch sizes an order of magnitude apart.
    let slope_a = big.marginal_ratio() / (512.0 - 1.0);
    let slope_b = ceiling.marginal_ratio() / (max_unit_batch() as f64 - 1.0);
    assert!(
        (slope_a - slope_b).abs() < 1e-6,
        "the marginal ratio must be exactly linear in (B-1): {slope_a} vs {slope_b}"
    );

    // Total-system: charge every input commitment. Saturates at the per-add column
    // count + 1, nowhere near B. The limit is (8B-7)/(B+5) -> 8.
    assert!(
        ceiling.total_ratio() > 7.9 && ceiling.total_ratio() < 8.0,
        "total-system ratio must saturate just under 8x, got {:.3}",
        ceiling.total_ratio()
    );
    assert!(
        deployed.total_ratio() < big.total_ratio(),
        "total-system ratio still grows, but toward a constant"
    );
}

#[test]
fn the_range_leg_does_not_grow_with_the_batch() {
    // The single most important cost fact: the reduction is amortised, not deleted, and
    // what it is amortised to does not depend on B.
    let shape = Shape::deployed();
    assert_eq!(RangeLeg::sites(shape), shape.limbs());
    for b in [1usize, 4, 512, 3839] {
        let acc_sites = RangeLeg::sites(shape);
        assert_eq!(
            acc_sites, 49_152,
            "range-check sites must be independent of B (B={b})"
        );
    }
}

#[test]
fn limbs_are_the_layout_the_statement_names() {
    // `flat` is part of the statement. Pin it: poly-major, then modulus, then
    // coefficient, then limb — little-endian within a residue.
    let shape = Shape {
        polys: 2,
        moduli: 3,
        degree: 8,
    };
    let mut ct = fixture(shape, 3);
    let v: u64 = (5u64 << LIMB_BITS) | 9;
    ct.polys[0].rows[0][0] = v;
    let flat = flatten(&ct).unwrap();
    assert_eq!(flat[0], F::from_u64(9), "limb 0 is the low LIMB_BITS bits");
    assert_eq!(flat[1], F::from_u64(5), "limb 1 is the high part");
    assert_eq!(flat.len(), shape.limbs());
}

#[test]
fn the_challenge_point_lives_in_the_EXTENSION_field() {
    // ⚑ REGRESSION GUARD for the one place this construction can silently fall below the
    // repo's ~124-bit bar. Soundness is mu/|challenge field|. At mu=16 that is 2^-120
    // over EF = F^4 and 2^-27 over F. A "simplification" to base-field challenges would
    // still typecheck, still pass every other test here, and cost 93 bits.
    use p3_field::BasedVectorSpace;

    let shape = Shape::deployed();
    let cts = batch(shape, DEPLOYED_BATCH);
    let acc = lazy_fold(&cts, &[1, 1, 1, 1]).unwrap();
    let proof = prove(&cts, &[1, 1, 1, 1], &acc).unwrap();
    let point = verify(&proof).unwrap().point;

    assert_eq!(<EF as BasedVectorSpace<F>>::DIMENSION, 4, "EF must be F^4");
    let nonbase = point
        .as_slice()
        .iter()
        .filter(|c| {
            <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(c)[1..]
                .iter()
                .any(|&x| x != F::ZERO)
        })
        .count();
    assert!(
        nonbase >= point.num_variables() - 1,
        "essentially every challenge coordinate must have nonzero non-constant basis \
         components; {nonbase}/{} did — a base-field challenge would give 0 and cost 93 \
         bits of soundness",
        point.num_variables()
    );

    // A gate that cannot go red is not a gate: build the base-field point this guard
    // exists to reject and confirm the same predicate scores it 0.
    let base_point: Vec<EF> = (0..point.num_variables())
        .map(|i| EF::from(F::from_u64(1 + i as u64)))
        .collect();
    let base_nonbase = base_point
        .iter()
        .filter(|c| {
            <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(c)[1..]
                .iter()
                .any(|&x| x != F::ZERO)
        })
        .count();
    assert_eq!(
        base_nonbase, 0,
        "the guard must score a base-field point 0, or it is not measuring what it claims"
    );
}

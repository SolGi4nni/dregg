use fhegg_solver::qp::QpProblem;
use fhegg_solver::qp_exact::{CertQpExact, QpProblemBindingError, MAX_SCALE};
use fhegg_solver::qp_strict::{verify_zero_kkt_qp, ZeroKktQpError, MAX_STRICT_QP_DIMENSION};

const SCALE: u32 = 6;
const S: i128 = 1_000_000;

fn exact_certificate() -> CertQpExact {
    // min 1/2 x^2 - x, 0 <= x <= 2, exact optimum x=1.
    CertQpExact {
        n: 1,
        mc: 1,
        scale: SCALE,
        p: vec![S],
        q: vec![-S],
        a: vec![S],
        l: vec![0],
        u: vec![2 * S],
        x: vec![S],
        y: vec![0],
        epsilon: 0,
    }
}

fn public_problem() -> QpProblem {
    QpProblem {
        n: 1,
        mc: 1,
        p: vec![1.0],
        q: vec![-1.0],
        a: vec![1.0],
        l: vec![0.0],
        u: vec![2.0],
    }
}

#[test]
fn exact_zero_kkt_mints_the_typed_capability() {
    let verified = verify_zero_kkt_qp(exact_certificate(), &public_problem(), SCALE)
        .expect("exact optimum has a zero-KKT capability");
    let (x, y, scale) = verified.solution();
    assert_eq!(x, &[S]);
    assert_eq!(y, &[0]);
    assert_eq!(scale, SCALE);
    assert_eq!(verified.report().prim_res, Some(0));
    assert_eq!(verified.report().dual_res, Some(0));
    assert_eq!(verified.report().normal_res, Some(0));
    assert_eq!(verified.report().tol, Some(0));
}

#[test]
fn arithmetic_exactness_does_not_upgrade_positive_tolerance_to_exact_kkt() {
    // x=0 has exact residual 1 and is accepted by CertQpExact at epsilon=1.
    // It must not inhabit the strict epsilon=0/global-composition premise.
    let mut approximate = exact_certificate();
    approximate.x[0] = 0;
    approximate.epsilon = S;
    assert!(
        approximate.check().valid,
        "bounded residual certificate is valid"
    );
    assert_eq!(
        verify_zero_kkt_qp(approximate, &public_problem(), SCALE)
            .expect_err("positive tolerance cannot mint exact KKT"),
        ZeroKktQpError::NonZeroTolerance { epsilon: S }
    );
}

#[test]
fn nonzero_residual_witness_is_rejected_at_zero_tolerance() {
    let mut tampered = exact_certificate();
    tampered.x[0] = 0;
    assert_eq!(
        verify_zero_kkt_qp(tampered, &public_problem(), SCALE)
            .expect_err("tampered witness cannot mint exact KKT"),
        ZeroKktQpError::NonZeroResidual
    );
}

#[test]
fn complete_independent_problem_binding_rejects_substitution() {
    let mut changed_objective = public_problem();
    changed_objective.q[0] = -2.0;
    assert_eq!(
        verify_zero_kkt_qp(exact_certificate(), &changed_objective, SCALE)
            .expect_err("same PSD matrix cannot authorize another objective"),
        ZeroKktQpError::ProblemBinding(QpProblemBindingError::FieldMismatch {
            field: "q",
            index: 0,
        })
    );

    let mut changed_region = public_problem();
    changed_region.u[0] = 3.0;
    assert_eq!(
        verify_zero_kkt_qp(exact_certificate(), &changed_region, SCALE)
            .expect_err("same witness cannot authorize another feasible region"),
        ZeroKktQpError::ProblemBinding(QpProblemBindingError::FieldMismatch {
            field: "u",
            index: 0,
        })
    );
}

#[test]
fn producer_cannot_choose_a_coarser_scale() {
    assert_eq!(
        verify_zero_kkt_qp(exact_certificate(), &public_problem(), SCALE - 1)
            .expect_err("scale is caller-pinned"),
        ZeroKktQpError::ScaleMismatch {
            certificate: SCALE,
            expected: SCALE - 1,
        }
    );
    assert_eq!(
        verify_zero_kkt_qp(exact_certificate(), &public_problem(), MAX_SCALE + 1)
            .expect_err("unsupported expected scale is refused"),
        ZeroKktQpError::ExpectedScaleTooLarge {
            expected: MAX_SCALE + 1,
            maximum: MAX_SCALE,
        }
    );
}

#[test]
fn checked_arithmetic_overflow_fails_closed() {
    let mut overflowing = exact_certificate();
    // Public problem fields remain unchanged and bind exactly. Witness-only
    // products overflow i128 during the fresh residual computation.
    overflowing.x[0] = i128::MAX;
    assert_eq!(
        verify_zero_kkt_qp(overflowing, &public_problem(), SCALE)
            .expect_err("overflow cannot wrap into a zero residual"),
        ZeroKktQpError::ArithmeticOverflow
    );
}

#[test]
fn verifier_work_is_dimension_bounded_before_residual_loops() {
    let mc = MAX_STRICT_QP_DIMENSION + 1;
    let oversized = CertQpExact {
        n: 1,
        mc,
        scale: SCALE,
        p: vec![S],
        q: vec![0],
        a: vec![0; mc],
        l: vec![0; mc],
        u: vec![0; mc],
        x: vec![0],
        y: vec![0; mc],
        epsilon: 0,
    };
    assert_eq!(
        verify_zero_kkt_qp(oversized, &public_problem(), SCALE)
            .expect_err("deployment-sized verifier refuses oversized dimensions"),
        ZeroKktQpError::DimensionTooLarge { n: 1, mc }
    );
}

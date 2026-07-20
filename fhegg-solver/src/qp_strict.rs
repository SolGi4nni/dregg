//! Typed refusal boundary for the **exact-zero KKT** subset of [`CertQpExact`].
//!
//! `CertQpExact` means its arithmetic is exact; it does not mean its tolerance
//! is zero.  A positive-tolerance certificate can validly establish bounded
//! residuals, but it does not inhabit the exact-KKT premise used by the Lean
//! global-optimality composition.  This module makes that distinction a Rust
//! type boundary.
//!
//! [`verify_zero_kkt_qp`] is the only constructor of [`VerifiedZeroKktQp`]. It
//! takes ownership of the untrusted certificate, pins the fixed-point scale,
//! bounds verifier work, recomputes all residuals with checked arithmetic,
//! requires `epsilon = primal = dual = normal = 0`, and binds the complete
//! embedded `(P,q,A,l,u)` to an independently supplied [`QpProblem`].  Callers
//! cannot mint the capability from a merely approximate certificate or mutate
//! the owned certificate after verification.
//!
//! This boundary does **not** prove `P` is PSD, authenticate a producer, decode
//! hostile bytes before allocation, or prove the Rust checker refines Lean.
//! `fhir::qp_certificate`'s `FHQPB001` transport supplies the bounded canonical
//! SDD+KKT wire/admission boundary.  Lean global optimality additionally needs
//! that same-matrix PSD premise and the named Rust-to-Lean refinement.

use std::fmt;

use crate::qp::QpProblem;
use crate::qp_exact::{CertQpExact, CertQpExactReport, QpProblemBindingError, MAX_SCALE};

/// Bound the verifier's dense dimensions.  The canonical FHQPB001 transport
/// applies the same deployment-scale dimension ceiling before allocation.
pub const MAX_STRICT_QP_DIMENSION: usize = 1_024;

/// Bound total exact scalars touched by the verifier (all public data plus the
/// primal/dual witness and epsilon).
pub const MAX_STRICT_QP_SCALARS: usize = 1 << 20;

/// Everything the exact-zero KKT capability refuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZeroKktQpError {
    ExpectedScaleTooLarge { expected: u32, maximum: u32 },
    ScaleMismatch { certificate: u32, expected: u32 },
    DimensionTooLarge { n: usize, mc: usize },
    ScalarLimit { required: usize, maximum: usize },
    MalformedCertificate,
    ArithmeticOverflow,
    ProblemBinding(QpProblemBindingError),
    NonZeroTolerance { epsilon: i128 },
    NonZeroResidual,
}

impl fmt::Display for ZeroKktQpError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpectedScaleTooLarge { expected, maximum } => {
                write!(f, "required scale {expected} exceeds maximum {maximum}")
            }
            Self::ScaleMismatch {
                certificate,
                expected,
            } => write!(
                f,
                "certificate scale {certificate} does not match required {expected}"
            ),
            Self::DimensionTooLarge { n, mc } => {
                write!(f, "QP dimensions exceed verifier limit (n={n}, mc={mc})")
            }
            Self::ScalarLimit { required, maximum } => write!(
                f,
                "QP certificate needs {required} scalars; verifier maximum is {maximum}"
            ),
            Self::MalformedCertificate => write!(f, "malformed exact-QP certificate"),
            Self::ArithmeticOverflow => {
                write!(f, "checked exact-QP residual arithmetic overflowed")
            }
            Self::ProblemBinding(error) => {
                write!(f, "certificate does not name the authorized QP: {error:?}")
            }
            Self::NonZeroTolerance { epsilon } => write!(
                f,
                "certificate tolerance is {epsilon}; exact-zero KKT requires epsilon=0"
            ),
            Self::NonZeroResidual => write!(f, "one or more exact KKT residuals are nonzero"),
        }
    }
}

impl std::error::Error for ZeroKktQpError {}

impl From<QpProblemBindingError> for ZeroKktQpError {
    fn from(value: QpProblemBindingError) -> Self {
        Self::ProblemBinding(value)
    }
}

/// An owned certificate that has crossed the strict exact-zero KKT boundary.
/// Private fields make the capability immutable and unforgeable outside this
/// module.
#[derive(Clone, Debug)]
pub struct VerifiedZeroKktQp {
    certificate: CertQpExact,
    report: CertQpExactReport,
}

impl VerifiedZeroKktQp {
    pub fn certificate(&self) -> &CertQpExact {
        &self.certificate
    }

    pub fn report(&self) -> &CertQpExactReport {
        &self.report
    }

    pub fn solution(&self) -> (&[i128], &[i128], u32) {
        (
            &self.certificate.x,
            &self.certificate.y,
            self.certificate.scale,
        )
    }
}

/// Mint the exact-zero KKT capability for one independently authorized QP.
///
/// The independent `expected_scale` is load-bearing: otherwise an untrusted
/// producer could select a coarser rounding domain before problem binding.
pub fn verify_zero_kkt_qp(
    certificate: CertQpExact,
    public_problem: &QpProblem,
    expected_scale: u32,
) -> Result<VerifiedZeroKktQp, ZeroKktQpError> {
    if expected_scale > MAX_SCALE {
        return Err(ZeroKktQpError::ExpectedScaleTooLarge {
            expected: expected_scale,
            maximum: MAX_SCALE,
        });
    }
    if certificate.scale != expected_scale {
        return Err(ZeroKktQpError::ScaleMismatch {
            certificate: certificate.scale,
            expected: expected_scale,
        });
    }
    bound_verifier_work(certificate.n, certificate.mc)?;

    // Recompute before binding: malformed and overflowing witnesses fail
    // without relying on any producer-supplied verdict or residual report.
    let report = certificate.check();
    if !report.well_formed {
        return Err(ZeroKktQpError::MalformedCertificate);
    }
    if report.overflow {
        return Err(ZeroKktQpError::ArithmeticOverflow);
    }

    // The solver cannot authorize its own public program image.
    certificate.verify_problem_binding(public_problem)?;

    if certificate.epsilon != 0 {
        return Err(ZeroKktQpError::NonZeroTolerance {
            epsilon: certificate.epsilon,
        });
    }
    if report.prim_res != Some(0)
        || report.dual_res != Some(0)
        || report.normal_res != Some(0)
        || report.tol != Some(0)
        || !report.valid
    {
        return Err(ZeroKktQpError::NonZeroResidual);
    }

    Ok(VerifiedZeroKktQp {
        certificate,
        report,
    })
}

fn bound_verifier_work(n: usize, mc: usize) -> Result<(), ZeroKktQpError> {
    if n == 0 || n > MAX_STRICT_QP_DIMENSION || mc > MAX_STRICT_QP_DIMENSION {
        return Err(ZeroKktQpError::DimensionTooLarge { n, mc });
    }
    // p + q + a + l + u + x + y + epsilon.
    let required = n
        .checked_mul(n)
        .and_then(|count| count.checked_add(n))
        .and_then(|count| mc.checked_mul(n).and_then(|mn| count.checked_add(mn)))
        .and_then(|count| count.checked_add(mc))
        .and_then(|count| count.checked_add(mc))
        .and_then(|count| count.checked_add(n))
        .and_then(|count| count.checked_add(mc))
        .and_then(|count| count.checked_add(1))
        .ok_or(ZeroKktQpError::ScalarLimit {
            required: usize::MAX,
            maximum: MAX_STRICT_QP_SCALARS,
        })?;
    if required > MAX_STRICT_QP_SCALARS {
        return Err(ZeroKktQpError::ScalarLimit {
            required,
            maximum: MAX_STRICT_QP_SCALARS,
        });
    }
    Ok(())
}

//! A self-contained, strict exact certificate for one fhIR quadratic program.
//!
//! A KKT residual certificate has its intended convex-optimization meaning
//! only when its quadratic matrix is positive semidefinite.  fhIR previously carried the
//! exact SDD=>PSD admission certificate on [`Compiled`](crate::Compiled) and
//! the exact KKT certificate on [`RunOutcome`](crate::RunOutcome), but a caller
//! exporting the latter could accidentally drop the former.  This module
//! makes that unsafe split unrepresentable at the transport boundary.
//!
//! `FHQPB001` contains both exact integer objects and verifies, from the bytes
//! alone, that:
//!
//! * the SDD admission witness is structurally valid;
//! * the KKT certificate passes its exact, overflow-checked checker; and
//! * both objects name the identical fixed-point `P` matrix and scale.
//!
//! The checksum detects corruption.  It is deliberately not authentication;
//! callers that need issuer identity must sign the canonical artifact.

use crate::compile::{
    Compiled, ConvexProgram, ExactSddPsdCertificate, ExactSddPsdCertificateError,
    QP_CERT_EXACT_SCALE,
};
use crate::solver_bridge::{run, ExactCertQpVerdict, RunOutcome};
use fhegg_solver::qp::CertQp;
use fhegg_solver::qp_exact::{lift_cert, CertQpExact, QpProblemBindingError};
use fhegg_solver::qp_strict::{verify_zero_kkt_qp, VerifiedZeroKktQp, ZeroKktQpError};
use sha2::{Digest, Sha256};

const MAGIC: &[u8; 8] = b"FHQPB001";
const VERSION: u8 = 1;
const CHECKSUM_DOMAIN: &[u8] = b"fhir/exact-qp-certificate-bundle/v1";
const PROGRAM_DIGEST_DOMAIN: &[u8] = b"fhir/exact-qp-public-program/v1";
const HEADER_LEN: usize = 8 + 1 + 4 + 4 + 4 + 4;
const CHECKSUM_LEN: usize = 32;

/// Deliberately below the independent SDD carrier's limit: the KKT artifact
/// also contains an `m*n` constraint matrix and must remain cheaply bounded
/// before allocation.
pub const MAX_QP_BUNDLE_DIMENSION: usize = 1024;
pub const MAX_QP_BUNDLE_WIRE_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactQpCertificateBundle {
    admission: ExactSddPsdCertificate,
    kkt: CertQpExact,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactQpCertificateBundleError {
    NotQp,
    MissingAdmission,
    Admission(ExactSddPsdCertificateError),
    KktInvalid,
    ScaleMismatch,
    DimensionMismatch,
    MatrixMismatch { index: usize },
    DimensionTooLarge { n: usize, mc: usize },
    ArithmeticOverflow,
    WireTooLarge { actual: usize, maximum: usize },
    MalformedWire,
    UnsupportedVersion { found: u8 },
    ChecksumMismatch,
    ProgramBinding(QpProblemBindingError),
    ZeroKkt(ZeroKktQpError),
}

impl std::fmt::Display for ExactQpCertificateBundleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for ExactQpCertificateBundleError {}

impl From<ExactSddPsdCertificateError> for ExactQpCertificateBundleError {
    fn from(value: ExactSddPsdCertificateError) -> Self {
        Self::Admission(value)
    }
}

impl From<QpProblemBindingError> for ExactQpCertificateBundleError {
    fn from(value: QpProblemBindingError) -> Self {
        Self::ProgramBinding(value)
    }
}

impl From<ZeroKktQpError> for ExactQpCertificateBundleError {
    fn from(value: ZeroKktQpError) -> Self {
        Self::ZeroKkt(value)
    }
}

/// An externally supplied optimizer result that has been checked against the
/// independently compiled fhIR program.  Construction is private: callers can
/// obtain this authority only through [`verify_certified_qp`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedExactQpCertificate {
    bundle: ExactQpCertificateBundle,
    program_digest: [u8; 32],
}

/// A canonical fhIR QP bundle whose PSD admission, complete public problem,
/// and exact-zero KKT witness have all been independently checked.
///
/// Construction is private.  In particular, a valid positive-tolerance
/// [`VerifiedExactQpCertificate`] cannot be converted into this stronger
/// capability without replaying the zero-tolerance checker.
#[derive(Clone, Debug)]
pub struct VerifiedZeroKktQpCertificate {
    certified: VerifiedExactQpCertificate,
    zero_kkt: VerifiedZeroKktQp,
}

impl VerifiedZeroKktQpCertificate {
    /// The checked canonical bundle, including its same-matrix SDD admission.
    pub fn certified(&self) -> &VerifiedExactQpCertificate {
        &self.certified
    }

    /// Exact-zero residual evidence over the very KKT certificate embedded in
    /// [`Self::certified`].
    pub fn zero_kkt(&self) -> &VerifiedZeroKktQp {
        &self.zero_kkt
    }

    pub fn program_digest(&self) -> [u8; 32] {
        self.certified.program_digest()
    }

    pub fn solution(&self) -> (&[i128], &[i128], u32) {
        self.zero_kkt.solution()
    }
}

impl VerifiedExactQpCertificate {
    /// Digest of the exact fixed-point public problem `(P,q,A,l,u)` authorized
    /// by the compiler.  It excludes the optimizer witness and tolerance.
    pub fn program_digest(&self) -> [u8; 32] {
        self.program_digest
    }

    pub fn bundle(&self) -> &ExactQpCertificateBundle {
        &self.bundle
    }

    /// The verified fixed-point primal and dual witness plus its decimal scale.
    pub fn solution(&self) -> (&[i128], &[i128], u32) {
        (
            &self.bundle.kkt.x,
            &self.bundle.kkt.y,
            self.bundle.kkt.scale,
        )
    }
}

impl ExactQpCertificateBundle {
    /// Join two independently executable exact certificates.  Construction
    /// rechecks both; no cached report bit becomes authority.
    pub fn new(
        admission: ExactSddPsdCertificate,
        kkt: CertQpExact,
    ) -> Result<Self, ExactQpCertificateBundleError> {
        let bundle = Self { admission, kkt };
        bundle.verify()?;
        Ok(bundle)
    }

    pub fn admission(&self) -> &ExactSddPsdCertificate {
        &self.admission
    }

    pub fn kkt(&self) -> &CertQpExact {
        &self.kkt
    }

    /// Verify the complete standalone claim.  Re-encoding the SDD carrier is
    /// also its public structural verifier; the exact KKT checker recomputes
    /// all residuals with checked i128 arithmetic.
    pub fn verify(&self) -> Result<(), ExactQpCertificateBundleError> {
        self.admission.to_wire_bytes()?;
        if self.kkt.n == 0
            || self.kkt.n > MAX_QP_BUNDLE_DIMENSION
            || self.kkt.mc > MAX_QP_BUNDLE_DIMENSION
        {
            return Err(ExactQpCertificateBundleError::DimensionTooLarge {
                n: self.kkt.n,
                mc: self.kkt.mc,
            });
        }
        if self.admission.scale() != QP_CERT_EXACT_SCALE || self.kkt.scale != QP_CERT_EXACT_SCALE {
            return Err(ExactQpCertificateBundleError::ScaleMismatch);
        }
        if self.admission.dimension() != self.kkt.n
            || self.admission.exact_entries().len() != self.kkt.p.len()
        {
            return Err(ExactQpCertificateBundleError::DimensionMismatch);
        }
        for (index, (admitted, used)) in self
            .admission
            .exact_entries()
            .iter()
            .zip(&self.kkt.p)
            .enumerate()
        {
            if admitted != used {
                return Err(ExactQpCertificateBundleError::MatrixMismatch { index });
            }
        }
        if !self.kkt.check().valid {
            return Err(ExactQpCertificateBundleError::KktInvalid);
        }
        exact_wire_len(&self.kkt, self.admission.to_wire_bytes()?.len())?;
        Ok(())
    }

    /// Attach this internally consistent bundle to the exact fhIR QP that a
    /// relying party independently compiled.
    ///
    /// [`verify`](Self::verify) establishes that the embedded problem and
    /// witness form one valid PSD-plus-KKT object.  It does not establish that
    /// the embedded public problem is the product the relying party intended.
    /// This method closes that source-binding edge by comparing all of
    /// `(P,q,A,l,u)`, after the same exact fixed-point lift, and by rechecking
    /// the compiler's independent PSD admission carrier.
    pub fn verify_against_compiled(
        &self,
        compiled: &Compiled,
    ) -> Result<[u8; 32], ExactQpCertificateBundleError> {
        self.verify()?;
        self.bind_checked_bundle_to_compiled(compiled)
    }

    /// Program binding after this bundle has already passed [`Self::verify`].
    /// Kept private so public callers cannot skip the certificate checks, while
    /// decode/run paths avoid re-running the O(n²+mn) KKT verifier merely to
    /// attach an already-checked object to its source program.
    fn bind_checked_bundle_to_compiled(
        &self,
        compiled: &Compiled,
    ) -> Result<[u8; 32], ExactQpCertificateBundleError> {
        compiled.verify_exact_sdd_psd_certificate()?;
        let ConvexProgram::Qp(problem) = &compiled.program else {
            return Err(ExactQpCertificateBundleError::NotQp);
        };
        self.kkt.verify_problem_binding(problem)?;
        Ok(exact_qp_program_digest(&self.kkt))
    }

    /// Canonical, bounded, exact-EOF transport.  Every i128 uses network-order
    /// two's complement; all vector lengths are implied by `(n, mc)`.
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, ExactQpCertificateBundleError> {
        self.verify()?;
        self.to_wire_bytes_checked()
    }

    /// Encode an already-verified bundle. Only private checked construction and
    /// public `to_wire_bytes` reach this helper.
    fn to_wire_bytes_checked(&self) -> Result<Vec<u8>, ExactQpCertificateBundleError> {
        let admission = self.admission.to_wire_bytes()?;
        let wire_len = exact_wire_len(&self.kkt, admission.len())?;
        let mut out = Vec::with_capacity(wire_len);
        out.extend_from_slice(MAGIC);
        out.push(VERSION);
        out.extend_from_slice(&(admission.len() as u32).to_be_bytes());
        out.extend_from_slice(&(self.kkt.n as u32).to_be_bytes());
        out.extend_from_slice(&(self.kkt.mc as u32).to_be_bytes());
        out.extend_from_slice(&self.kkt.scale.to_be_bytes());
        out.extend_from_slice(&admission);
        push_i128s(&mut out, &self.kkt.p);
        push_i128s(&mut out, &self.kkt.q);
        push_i128s(&mut out, &self.kkt.a);
        push_i128s(&mut out, &self.kkt.l);
        push_i128s(&mut out, &self.kkt.u);
        push_i128s(&mut out, &self.kkt.x);
        push_i128s(&mut out, &self.kkt.y);
        out.extend_from_slice(&self.kkt.epsilon.to_be_bytes());
        let checksum = checksum(&out);
        out.extend_from_slice(&checksum);
        debug_assert_eq!(out.len(), wire_len);
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, ExactQpCertificateBundleError> {
        if bytes.len() > MAX_QP_BUNDLE_WIRE_BYTES {
            return Err(ExactQpCertificateBundleError::WireTooLarge {
                actual: bytes.len(),
                maximum: MAX_QP_BUNDLE_WIRE_BYTES,
            });
        }
        if bytes.len() < HEADER_LEN + CHECKSUM_LEN {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        let payload_len = bytes.len() - CHECKSUM_LEN;
        if bytes[payload_len..] != checksum(&bytes[..payload_len]) {
            return Err(ExactQpCertificateBundleError::ChecksumMismatch);
        }
        let mut cursor = Cursor::new(&bytes[..payload_len]);
        if cursor.take::<8>()? != *MAGIC {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        let version = cursor.take::<1>()?[0];
        if version != VERSION {
            return Err(ExactQpCertificateBundleError::UnsupportedVersion { found: version });
        }
        let admission_len = u32::from_be_bytes(cursor.take::<4>()?) as usize;
        let n = u32::from_be_bytes(cursor.take::<4>()?) as usize;
        let mc = u32::from_be_bytes(cursor.take::<4>()?) as usize;
        let scale = u32::from_be_bytes(cursor.take::<4>()?);
        if n == 0 || n > MAX_QP_BUNDLE_DIMENSION || mc > MAX_QP_BUNDLE_DIMENSION {
            return Err(ExactQpCertificateBundleError::DimensionTooLarge { n, mc });
        }
        let expected = exact_wire_len_for_dimensions(n, mc, admission_len)?;
        if expected != bytes.len() {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        let admission = ExactSddPsdCertificate::from_wire_bytes(cursor.take_slice(admission_len)?)?;
        let nn = n
            .checked_mul(n)
            .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
        let mn = mc
            .checked_mul(n)
            .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
        let kkt = CertQpExact {
            n,
            mc,
            scale,
            p: cursor.take_i128s(nn)?,
            q: cursor.take_i128s(n)?,
            a: cursor.take_i128s(mn)?,
            l: cursor.take_i128s(mc)?,
            u: cursor.take_i128s(mc)?,
            x: cursor.take_i128s(n)?,
            y: cursor.take_i128s(mc)?,
            epsilon: i128::from_be_bytes(cursor.take::<16>()?),
        };
        if !cursor.is_finished() {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        let bundle = Self::new(admission, kkt)?;
        if bundle.to_wire_bytes_checked()?.as_slice() != bytes {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        Ok(bundle)
    }
}

/// Compile-time PSD admission and run-time fixed-point KKT residual acceptance
/// packaged into one exportable exact-arithmetic artifact.  The solver remains
/// untrusted: this function only returns after independently re-running both
/// checkers. A positive tolerance is still a residual bound, not exact-zero
/// KKT/global optimality; `Market.QpCertificateBundle` proves the latter only
/// once an exact-KKT refinement has been supplied.
pub fn run_certified_qp(
    compiled: &Compiled,
) -> Result<ExactQpCertificateBundle, ExactQpCertificateBundleError> {
    if !matches!(compiled.program, ConvexProgram::Qp(_)) {
        return Err(ExactQpCertificateBundleError::NotQp);
    }
    compiled.verify_exact_sdd_psd_certificate()?;
    let admission = compiled
        .exact_sdd_psd_certificate
        .clone()
        .ok_or(ExactQpCertificateBundleError::MissingAdmission)?;
    match run(compiled) {
        RunOutcome::CertQp {
            exact: ExactCertQpVerdict::Checked { cert, .. },
            ..
        } => {
            let bundle = ExactQpCertificateBundle::new(admission, cert)?;
            bundle.bind_checked_bundle_to_compiled(compiled)?;
            Ok(bundle)
        }
        RunOutcome::InvalidCompiled { reason } => Err(reason.into()),
        RunOutcome::CertQp { .. } => Err(ExactQpCertificateBundleError::KktInvalid),
        _ => Err(ExactQpCertificateBundleError::NotQp),
    }
}

/// Canonical digest of the independently compiled exact QP public problem.
///
/// This is available before an optimizer runs and excludes every solver-owned
/// value (`x`, `y`, tolerance, diagnostics).  It uses the same fixed-point lift
/// and domain-separated `(P,q,A,l,u)` encoding that
/// [`VerifiedExactQpCertificate::program_digest`] returns after certificate
/// verification, so an external-worker request and its checked result name one
/// bit-exact problem.
pub fn canonical_qp_program_digest(
    compiled: &Compiled,
) -> Result<[u8; 32], ExactQpCertificateBundleError> {
    compiled.verify_exact_sdd_psd_certificate()?;
    let ConvexProgram::Qp(problem) = &compiled.program else {
        return Err(ExactQpCertificateBundleError::NotQp);
    };
    let public_image = CertQp {
        n: problem.n,
        mc: problem.mc,
        p: problem.p.clone(),
        q: problem.q.clone(),
        a: problem.a.clone(),
        l: problem.l.clone(),
        u: problem.u.clone(),
        x: vec![0.0; problem.n],
        y: vec![0.0; problem.mc],
        epsilon: 0.0,
        objective: 0.0,
        prim_res: 0.0,
        dual_res: 0.0,
    };
    let exact = lift_cert(&public_image, QP_CERT_EXACT_SCALE)
        .map_err(|error| QpProblemBindingError::Lift(error))?;
    Ok(exact_qp_program_digest(&exact))
}

/// Verify an optimizer-produced `FHQPB001` artifact without running ADMM.
///
/// The wire decoder replays both certificate checkers; the final binding step
/// then compares the certificate's complete exact public problem to the
/// independently compiled fhIR product.  Only that conjunction mints the
/// [`VerifiedExactQpCertificate`] consumed by settlement/application code.
pub fn verify_certified_qp(
    compiled: &Compiled,
    wire: &[u8],
) -> Result<VerifiedExactQpCertificate, ExactQpCertificateBundleError> {
    let bundle = ExactQpCertificateBundle::from_wire_bytes(wire)?;
    let program_digest = bundle.bind_checked_bundle_to_compiled(compiled)?;
    Ok(VerifiedExactQpCertificate {
        bundle,
        program_digest,
    })
}

/// Verify a hostile canonical `FHQPB001` artifact as an exact-zero KKT result.
///
/// This is a strict extension of [`verify_certified_qp`], not a second wire or
/// a parallel decoder.  It first performs the bounded canonical decode, SDD
/// admission replay, and complete `(P,q,A,l,u)` binding against `compiled`.
/// It then runs the typed exact-zero checker over the certificate embedded in
/// that already-bound bundle.  Positive-tolerance certificates remain valid
/// inputs to [`verify_certified_qp`] but cannot cross this API.
///
/// The returned capability is executable Rust evidence.  It does not claim
/// that the Rust checker refines the corresponding Lean predicate; that
/// separately named refinement boundary remains unchanged.
pub fn verify_zero_kkt_certified_qp(
    compiled: &Compiled,
    wire: &[u8],
) -> Result<VerifiedZeroKktQpCertificate, ExactQpCertificateBundleError> {
    let certified = verify_certified_qp(compiled, wire)?;
    let ConvexProgram::Qp(public_problem) = &compiled.program else {
        return Err(ExactQpCertificateBundleError::NotQp);
    };
    let zero_kkt = verify_zero_kkt_qp(
        certified.bundle().kkt().clone(),
        public_problem,
        QP_CERT_EXACT_SCALE,
    )?;
    Ok(VerifiedZeroKktQpCertificate {
        certified,
        zero_kkt,
    })
}

fn push_i128s(out: &mut Vec<u8>, values: &[i128]) {
    for value in values {
        out.extend_from_slice(&value.to_be_bytes());
    }
}

fn exact_value_count(n: usize, mc: usize) -> Result<usize, ExactQpCertificateBundleError> {
    let nn = n
        .checked_mul(n)
        .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
    let mn = mc
        .checked_mul(n)
        .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
    // p + q + a + l + u + x + y + epsilon
    nn.checked_add(n)
        .and_then(|v| v.checked_add(mn))
        .and_then(|v| v.checked_add(mc.checked_mul(2)?))
        .and_then(|v| v.checked_add(n))
        .and_then(|v| v.checked_add(mc))
        .and_then(|v| v.checked_add(1))
        .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)
}

fn exact_wire_len(
    kkt: &CertQpExact,
    admission_len: usize,
) -> Result<usize, ExactQpCertificateBundleError> {
    exact_wire_len_for_dimensions(kkt.n, kkt.mc, admission_len)
}

fn exact_wire_len_for_dimensions(
    n: usize,
    mc: usize,
    admission_len: usize,
) -> Result<usize, ExactQpCertificateBundleError> {
    if n == 0 || n > MAX_QP_BUNDLE_DIMENSION || mc > MAX_QP_BUNDLE_DIMENSION {
        return Err(ExactQpCertificateBundleError::DimensionTooLarge { n, mc });
    }
    let values = exact_value_count(n, mc)?;
    HEADER_LEN
        .checked_add(admission_len)
        .and_then(|v| v.checked_add(values.checked_mul(16)?))
        .and_then(|v| v.checked_add(CHECKSUM_LEN))
        .filter(|len| *len <= MAX_QP_BUNDLE_WIRE_BYTES)
        .ok_or(ExactQpCertificateBundleError::WireTooLarge {
            actual: usize::MAX,
            maximum: MAX_QP_BUNDLE_WIRE_BYTES,
        })
}

fn checksum(payload: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((CHECKSUM_DOMAIN.len() as u64).to_be_bytes());
    hash.update(CHECKSUM_DOMAIN);
    hash.update((payload.len() as u64).to_be_bytes());
    hash.update(payload);
    hash.finalize().into()
}

fn exact_qp_program_digest(kkt: &CertQpExact) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((PROGRAM_DIGEST_DOMAIN.len() as u64).to_be_bytes());
    hash.update(PROGRAM_DIGEST_DOMAIN);
    hash.update((kkt.n as u64).to_be_bytes());
    hash.update((kkt.mc as u64).to_be_bytes());
    hash.update(kkt.scale.to_be_bytes());
    for values in [&kkt.p, &kkt.q, &kkt.a, &kkt.l, &kkt.u] {
        hash.update((values.len() as u64).to_be_bytes());
        for value in values {
            hash.update(value.to_be_bytes());
        }
    }
    hash.finalize().into()
}

struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], ExactQpCertificateBundleError> {
        self.take_slice(N)?
            .try_into()
            .map_err(|_| ExactQpCertificateBundleError::MalformedWire)
    }

    fn take_slice(&mut self, len: usize) -> Result<&'a [u8], ExactQpCertificateBundleError> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(ExactQpCertificateBundleError::MalformedWire)?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn take_i128s(&mut self, len: usize) -> Result<Vec<i128>, ExactQpCertificateBundleError> {
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(i128::from_be_bytes(self.take::<16>()?));
        }
        Ok(values)
    }

    fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{MatrixData, Product, ProductBody};
    use crate::{compile, products};

    fn bundle() -> ExactQpCertificateBundle {
        let compiled = compile(&products::portfolio_qp_public()).expect("compile public QP");
        run_certified_qp(&compiled).expect("exact PSD+KKT bundle")
    }

    fn repair_checksum(wire: &mut [u8]) {
        let payload_len = wire.len() - CHECKSUM_LEN;
        let repaired = checksum(&wire[..payload_len]);
        wire[payload_len..].copy_from_slice(&repaired);
    }

    fn exact_zero_bundle() -> (Compiled, ExactQpCertificateBundle) {
        // min 1/2 x^2 - x, subject to x=1 and 0 <= x <= 1.
        // x=1, y=(0,0) has literal zero primal, stationarity, and
        // normal-cone residuals at fhIR's canonical scale.
        let product = Product::infer(
            "one-dimensional-exact-kkt",
            ProductBody::Portfolio {
                cov: MatrixData::public(1, 1, vec![1.0]),
                mu: vec![1.0],
                lambda: 1.0,
                w_max: 1.0,
            },
        );
        let compiled = compile(&product).expect("compile exact one-dimensional QP");
        let ConvexProgram::Qp(problem) = &compiled.program else {
            unreachable!()
        };
        let scale = 10_i128.pow(QP_CERT_EXACT_SCALE);
        let lift = |values: &[f64]| {
            values
                .iter()
                .map(|value| (value * scale as f64).round() as i128)
                .collect()
        };
        let kkt = CertQpExact {
            n: problem.n,
            mc: problem.mc,
            scale: QP_CERT_EXACT_SCALE,
            p: lift(&problem.p),
            q: lift(&problem.q),
            a: lift(&problem.a),
            l: lift(&problem.l),
            u: lift(&problem.u),
            x: vec![scale],
            y: vec![0; problem.mc],
            epsilon: 0,
        };
        let admission = compiled
            .exact_sdd_psd_certificate
            .clone()
            .expect("compiled QP carries SDD admission");
        let bundle = ExactQpCertificateBundle::new(admission, kkt)
            .expect("exact-zero witness and admission agree");
        (compiled, bundle)
    }

    #[test]
    fn exact_qp_bundle_roundtrips_and_rechecks_both_proofs() {
        let bundle = bundle();
        bundle.verify().unwrap();
        let wire = bundle.to_wire_bytes().unwrap();
        let decoded = ExactQpCertificateBundle::from_wire_bytes(&wire).unwrap();
        assert_eq!(decoded, bundle);
        decoded.verify().unwrap();

        for end in 0..wire.len() {
            assert!(ExactQpCertificateBundle::from_wire_bytes(&wire[..end]).is_err());
        }
        let mut trailing = wire.clone();
        trailing.push(0);
        assert!(ExactQpCertificateBundle::from_wire_bytes(&trailing).is_err());
        let mut corrupted = wire;
        corrupted[HEADER_LEN + 1] ^= 1;
        assert_eq!(
            ExactQpCertificateBundle::from_wire_bytes(&corrupted),
            Err(ExactQpCertificateBundleError::ChecksumMismatch)
        );
    }

    #[test]
    fn exact_qp_bundle_valid_checksum_cannot_bypass_version_or_dimensions() {
        let wire = bundle().to_wire_bytes().unwrap();

        let mut retired = wire.clone();
        retired[..8].copy_from_slice(b"FHQPB000");
        repair_checksum(&mut retired);
        assert_eq!(
            ExactQpCertificateBundle::from_wire_bytes(&retired),
            Err(ExactQpCertificateBundleError::MalformedWire)
        );

        let mut future = wire.clone();
        future[8] = 2;
        repair_checksum(&mut future);
        assert_eq!(
            ExactQpCertificateBundle::from_wire_bytes(&future),
            Err(ExactQpCertificateBundleError::UnsupportedVersion { found: 2 })
        );

        let mc = u32::from_be_bytes(wire[17..21].try_into().unwrap()) as usize;
        let mut oversized = wire;
        oversized[13..17].copy_from_slice(&((MAX_QP_BUNDLE_DIMENSION + 1) as u32).to_be_bytes());
        repair_checksum(&mut oversized);
        assert_eq!(
            ExactQpCertificateBundle::from_wire_bytes(&oversized),
            Err(ExactQpCertificateBundleError::DimensionTooLarge {
                n: MAX_QP_BUNDLE_DIMENSION + 1,
                mc,
            })
        );
    }

    #[test]
    fn exact_qp_bundle_valid_checksum_cannot_substitute_the_kkt_matrix() {
        let mut wire = bundle().to_wire_bytes().unwrap();
        let admission_len = u32::from_be_bytes(wire[9..13].try_into().unwrap()) as usize;
        let first_kkt_p_low_byte = HEADER_LEN + admission_len + 15;
        wire[first_kkt_p_low_byte] ^= 1;
        repair_checksum(&mut wire);
        assert_eq!(
            ExactQpCertificateBundle::from_wire_bytes(&wire),
            Err(ExactQpCertificateBundleError::MatrixMismatch { index: 0 })
        );
    }

    #[test]
    fn exact_qp_bundle_refuses_matrix_and_kkt_forgery() {
        let bundle = bundle();
        let mut wrong_matrix = bundle.clone();
        wrong_matrix.kkt.p[0] += 1;
        assert_eq!(
            wrong_matrix.verify(),
            Err(ExactQpCertificateBundleError::MatrixMismatch { index: 0 })
        );

        let mut wrong_witness = bundle;
        wrong_witness.kkt.x[0] += 10_i128.pow(QP_CERT_EXACT_SCALE);
        assert_eq!(
            wrong_witness.verify(),
            Err(ExactQpCertificateBundleError::KktInvalid)
        );
    }

    #[test]
    fn certified_qp_runner_refuses_non_qp() {
        let compiled = compile(&products::small_flow_clearing()).expect("compile LP");
        assert_eq!(
            run_certified_qp(&compiled),
            Err(ExactQpCertificateBundleError::NotQp)
        );
    }

    #[test]
    fn external_optimizer_result_binds_the_entire_compiled_qp() {
        let compiled = compile(&products::portfolio_qp_public()).expect("compile public QP");
        let wire = run_certified_qp(&compiled)
            .expect("run the untrusted optimizer once")
            .to_wire_bytes()
            .expect("canonical optimizer result");

        // The relying side needs no optimizer run: strict decode + both exact
        // checkers + full public-program binding mint the verified result.
        let verified = verify_certified_qp(&compiled, &wire)
            .expect("external certificate names this exact compiled product");
        let (x, y, scale) = verified.solution();
        assert_eq!(x.len(), 6);
        assert_eq!(y.len(), 7);
        assert_eq!(scale, QP_CERT_EXACT_SCALE);
        assert_ne!(verified.program_digest(), [0; 32]);
        assert_eq!(verified.bundle().to_wire_bytes().unwrap(), wire);
    }

    #[test]
    fn canonical_wire_mints_composed_psd_and_zero_kkt_capability() {
        let (compiled, bundle) = exact_zero_bundle();
        let wire = bundle.to_wire_bytes().unwrap();
        let verified = verify_zero_kkt_certified_qp(&compiled, &wire)
            .expect("one canonical artifact establishes admission, binding, and zero KKT");

        assert_eq!(verified.certified().bundle().to_wire_bytes().unwrap(), wire);
        assert_eq!(
            verified.certified().bundle().admission().exact_entries(),
            verified.zero_kkt().certificate().p
        );
        assert_eq!(verified.zero_kkt().certificate().epsilon, 0);
        assert_eq!(verified.zero_kkt().report().prim_res, Some(0));
        assert_eq!(verified.zero_kkt().report().dual_res, Some(0));
        assert_eq!(verified.zero_kkt().report().normal_res, Some(0));
        assert_eq!(verified.zero_kkt().report().tol, Some(0));
        assert_ne!(verified.program_digest(), [0; 32]);
    }

    #[test]
    fn valid_positive_tolerance_wire_cannot_cross_zero_kkt_api() {
        let (compiled, exact) = exact_zero_bundle();
        let scale = 10_i128.pow(QP_CERT_EXACT_SCALE);

        // A literal mutation to a positive tolerance remains a valid
        // FHQPB001 bounded-residual artifact, even though all residuals happen
        // to be zero. It is intentionally too weak for the strict capability.
        let mut tolerance_only = exact.to_wire_bytes().unwrap();
        let epsilon_offset = tolerance_only.len() - CHECKSUM_LEN - 16;
        tolerance_only[epsilon_offset..epsilon_offset + 16].copy_from_slice(&1_i128.to_be_bytes());
        repair_checksum(&mut tolerance_only);
        let approximate = verify_certified_qp(&compiled, &tolerance_only)
            .expect("positive tolerance remains valid approximate evidence");
        assert_eq!(approximate.bundle().kkt().epsilon, 1);
        assert!(approximate.bundle().kkt().check().valid);
        assert!(matches!(
            verify_zero_kkt_certified_qp(&compiled, &tolerance_only),
            Err(ExactQpCertificateBundleError::ZeroKkt(
                ZeroKktQpError::NonZeroTolerance { epsilon: 1 }
            ))
        ));

        // The same separation holds for a genuinely nonzero residual accepted
        // under a matching positive bound: x=0 misses both stationarity and
        // the budget row by one unit, but FHQPB001 remains a valid approximate
        // certificate at epsilon=1.
        let mut bounded = exact;
        bounded.kkt.x[0] = 0;
        bounded.kkt.epsilon = scale;
        let bounded_wire = bounded.to_wire_bytes().unwrap();
        let approximate = verify_certified_qp(&compiled, &bounded_wire)
            .expect("bounded nonzero residual remains valid approximate evidence");
        let report = approximate.bundle().kkt().check();
        assert_eq!(report.prim_res, Some(scale * scale));
        assert_eq!(report.dual_res, Some(scale * scale));
        assert!(report.valid);
        assert!(matches!(
            verify_zero_kkt_certified_qp(&compiled, &bounded_wire),
            Err(ExactQpCertificateBundleError::ZeroKkt(
                ZeroKktQpError::NonZeroTolerance { epsilon }
            )) if epsilon == scale
        ));
    }

    #[test]
    fn zero_kkt_api_reuses_hostile_decode_and_complete_program_binding() {
        let (compiled, bundle) = exact_zero_bundle();
        let wire = bundle.to_wire_bytes().unwrap();

        let mut corrupted = wire.clone();
        corrupted[HEADER_LEN + 1] ^= 1;
        assert!(matches!(
            verify_zero_kkt_certified_qp(&compiled, &corrupted),
            Err(ExactQpCertificateBundleError::ChecksumMismatch)
        ));

        let changed = compile(&Product::infer(
            "same-P-different-q-strict",
            ProductBody::Portfolio {
                cov: MatrixData::public(1, 1, vec![1.0]),
                mu: vec![2.0],
                lambda: 1.0,
                w_max: 1.0,
            },
        ))
        .expect("changed public QP remains independently admissible");
        assert!(matches!(
            verify_zero_kkt_certified_qp(&changed, &wire),
            Err(ExactQpCertificateBundleError::ProgramBinding(
                QpProblemBindingError::FieldMismatch {
                    field: "q",
                    index: 0
                }
            ))
        ));
    }

    #[test]
    fn same_psd_matrix_cannot_authorize_a_different_objective_or_feasible_region() {
        let compiled = compile(&products::portfolio_qp_public()).expect("compile source QP");
        let bundle = run_certified_qp(&compiled).expect("source certificate");
        bundle
            .verify()
            .expect("the embedded problem is internally consistent");
        let wire = bundle.to_wire_bytes().unwrap();

        let ProductBody::Portfolio {
            cov,
            mut mu,
            lambda,
            w_max,
        } = products::portfolio_qp_public().body
        else {
            unreachable!()
        };
        mu[0] += 0.01;
        let changed_objective = compile(&Product::infer(
            "same-P-different-q",
            ProductBody::Portfolio {
                cov: cov.clone(),
                mu,
                lambda,
                w_max,
            },
        ))
        .expect("the substituted QP is independently valid");
        assert!(matches!(
            verify_certified_qp(&changed_objective, &wire),
            Err(ExactQpCertificateBundleError::ProgramBinding(
                QpProblemBindingError::FieldMismatch { field: "q", .. }
            ))
        ));

        let changed_constraints = compile(&Product::infer(
            "same-P-different-box",
            ProductBody::Portfolio {
                cov,
                mu: match products::portfolio_qp_public().body {
                    ProductBody::Portfolio { mu, .. } => mu,
                    _ => unreachable!(),
                },
                lambda,
                w_max: 0.45,
            },
        ))
        .expect("the changed feasible region is independently valid");
        assert!(matches!(
            verify_certified_qp(&changed_constraints, &wire),
            Err(ExactQpCertificateBundleError::ProgramBinding(
                QpProblemBindingError::FieldMismatch { field: "u", .. }
            ))
        ));
    }
}

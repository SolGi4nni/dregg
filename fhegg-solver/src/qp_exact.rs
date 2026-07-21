//! Exact-integer CertQp checking — the first stone of the Cert-F treatment for a
//! sibling certificate.
//!
//! ## What this is (and is not)
//!
//! [`CertQpExact`] is a fixed-point **integer** carrier for the CertQp KKT
//! certificate: every entry of `(P, q, A, l, u, x, y, ε)` is an `i128` denoting
//! the rational `v / 10^scale`. [`CertQpExact::check`] decides EXACTLY the
//! accept predicate `rustCertQpCheck` of
//! `metatheory/Market/CertQpRustDenotation.lean`, restricted to rationals with
//! denominator `10^scale`:
//!
//! ```text
//!   rustPrimalResidual  ≤ ε   ∧   rustDualResidual ≤ ε   ∧   rustNormalResidual ≤ ε
//! ```
//!
//! Products of two scale-`S` values land at scale `S²`, so single-scale terms
//! (`q`, `l`, `u`, `y`, `ε`) are multiplied by `S` before comparison; every
//! comparison is then an exact integer comparison — **zero floating-point error
//! anywhere in the check**. The Lean side already proves (kernel-clean, `#guard`
//! executable):
//!
//! * `rustExactKkt_optimal` — exact feasibility + stationarity + normal-cone at
//!   a symmetric PSD `P` imply GLOBAL optimality over the OSQP feasible set;
//! * `rustForgedDual_rejected` — the wrong-sign-dual forgery (zero primal AND
//!   zero stationarity residual at a suboptimal point) is rejected by the
//!   normal-cone residual;
//! * `rustCertQpCheck_ignores_stored_reports` — stored report fields are dead to
//!   the checker (this carrier goes further: it has none).
//!
//! The tests below pin this checker to the Lean file's own `#guard` golden
//! vectors (`rustApproxWitness`, `rustForgedDualWitness`, `rustExactWitness`)
//! with EXACT residual equalities, not tolerances.
//!
//! ## Honest residuals (named, not papered)
//!
//! 1. **The f64→integer lift rounds entrywise** ([`lift_cert`]): the certified
//!    object is the ROUNDED integer problem, not the f64 problem (the same
//!    documented residual as the Cert-F bridge). The lift REFUSES non-finite
//!    values and magnitudes whose scaled image leaves the exactly-representable
//!    f64 integer range (|v·S| > 2^53) — it never silently saturates.
//! 2. **The Rust-side correspondence to `rustCertQpCheck` is by construction,
//!    not by proof**: this file mirrors the Lean definitions term-for-term over
//!    `i128` and is pinned by the shared golden vectors; the formal statement
//!    (`CertQpRustF64Refines` instantiated at THIS integer carrier, where the
//!    decode is exact and the rounding envelope vanishes) is the named residual
//!    `CertQpRustF64RefinementResidual` — now instantiable, still undischarged.
//! 3. **PSD of `P` is a hypothesis, not a check** (same as the f64 checker and
//!    the Lean theorem's `hP`): the public-program layer must pin it. A non-PSD
//!    `P` makes zero residuals meaningless (a saddle certifies nothing).
//! 4. **No descriptor / no STARK**: this is a native exact checker. The
//!    descriptor + AIR chain (the rest of the Cert-F treatment) is named in
//!    TESTQALOG, not faked here.
//!
//! Overflow anywhere in the checked arithmetic FAILS CLOSED (`overflow: true`,
//! `valid: false`) — an attacker cannot wrap a residual to zero.

use serde::Serialize;

use crate::qp::{CertQp, QpProblem};

/// Largest supported `scale` (so `10^scale` and its square stay far inside
/// `i128`; sums then overflow only via `checked_*`, which fails closed).
pub const MAX_SCALE: u32 = 18;

/// The exact-integer CertQp certificate. Every entry denotes `v / 10^scale`.
/// There are deliberately NO stored residual/objective fields — the Lean model
/// proves the checker ignores them, so this carrier does not even carry them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CertQpExact {
    pub n: usize,
    pub mc: usize,
    /// Fixed-point denominator exponent: values are `v / 10^scale`.
    pub scale: u32,
    /// `P` (n×n, row-major), scale `S`. PSD is the caller-pinned hypothesis.
    pub p: Vec<i128>,
    /// `q` (n), scale `S`.
    pub q: Vec<i128>,
    /// `A` (mc×n, row-major), scale `S`.
    pub a: Vec<i128>,
    /// `l` (mc), scale `S`.
    pub l: Vec<i128>,
    /// `u` (mc), scale `S`.
    pub u: Vec<i128>,
    /// Primal witness `x` (n), scale `S`.
    pub x: Vec<i128>,
    /// Dual witness `y` (mc), scale `S`.
    pub y: Vec<i128>,
    /// Tolerance ε ≥ 0, scale `S`.
    pub epsilon: i128,
}

/// The exact check report. Residuals are at scale `S²` and EXACT; `None` means
/// the computation overflowed (fail-closed) or the certificate was malformed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CertQpExactReport {
    pub well_formed: bool,
    /// A checked i128 operation overflowed — the check fails CLOSED.
    pub overflow: bool,
    pub primal_feasible: bool,
    pub dual_feasible: bool,
    pub normal_cone: bool,
    /// `max_i (Ax−uS)₊ + (lS−Ax)₊`, scale `S²`.
    pub prim_res: Option<i128>,
    /// `max_j |Px + qS + Aᵀy|`, scale `S²`.
    pub dual_res: Option<i128>,
    /// `max_i |Ax − clamp(Ax + yS, lS, uS)|`, scale `S²`.
    pub normal_res: Option<i128>,
    /// `ε·S` — the residual comparison threshold at scale `S²`.
    pub tol: Option<i128>,
    pub valid: bool,
}

impl CertQpExactReport {
    /// A closed-failure report: `overflow` is true only for the well-formed-but-
    /// overflowed case (a malformed certificate never reached arithmetic).
    fn failed_closed(well_formed: bool) -> Self {
        CertQpExactReport {
            well_formed,
            overflow: well_formed,
            primal_feasible: false,
            dual_feasible: false,
            normal_cone: false,
            prim_res: None,
            dual_res: None,
            normal_res: None,
            tol: None,
            valid: false,
        }
    }
}

/// Why an f64 certificate could not be lifted (the lift REFUSES, never rounds
/// silently past its stated envelope).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiftError {
    /// A value was NaN/±∞.
    NonFinite { field: &'static str, index: usize },
    /// `|v · 10^scale| > 2^53` — the scaled value leaves the range where f64
    /// holds integers exactly; refusing keeps the round-to-nearest claim honest.
    OutOfRange { field: &'static str, index: usize },
    /// The f64 certificate's own dimension fields do not match its arrays.
    BadShape,
    /// `scale > MAX_SCALE`.
    ScaleTooLarge,
    /// ε < 0.
    NegativeEpsilon,
}

/// Why an otherwise valid exact KKT certificate cannot be attached to an
/// independently supplied public QP.  The certificate carries a complete
/// `(P,q,A,l,u)` image, but verify-not-find consumers must compare that image
/// to the program they actually authorized rather than treating the embedded
/// problem as self-authenticating.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QpProblemBindingError {
    Lift(LiftError),
    DimensionMismatch {
        certificate_n: usize,
        certificate_mc: usize,
        program_n: usize,
        program_mc: usize,
    },
    FieldMismatch {
        field: &'static str,
        index: usize,
    },
}

impl From<LiftError> for QpProblemBindingError {
    fn from(value: LiftError) -> Self {
        Self::Lift(value)
    }
}

/// `2^53` — the exact-integer boundary of f64.
const F64_EXACT: f64 = 9_007_199_254_740_992.0;

fn lift_value(
    value: f64,
    scale: i128,
    field: &'static str,
    index: usize,
) -> Result<i128, LiftError> {
    if !value.is_finite() {
        return Err(LiftError::NonFinite { field, index });
    }
    let scaled = value * scale as f64;
    if scaled.abs() > F64_EXACT {
        return Err(LiftError::OutOfRange { field, index });
    }
    // Round half-away-from-zero (f64::round). The rounded value IS the
    // certified problem — documented residual (1) in the module doc.
    Ok(scaled.round() as i128)
}

fn lift_slice(vs: &[f64], s: i128, field: &'static str) -> Result<Vec<i128>, LiftError> {
    // `Result<Vec<_>, _>`'s generic `FromIterator` does not retain the source
    // slice's exact-size reservation through the short-circuiting adapter.
    // Reserve once so canonical problem/certificate lifts cannot repeatedly
    // grow their dense P/A buffers on the hot path.
    let mut lifted = Vec::with_capacity(vs.len());
    for (index, &value) in vs.iter().enumerate() {
        lifted.push(lift_value(value, s, field, index)?);
    }
    Ok(lifted)
}

/// Lift an f64 [`CertQp`] to the exact-integer carrier at `10^scale` fixed
/// point. Entrywise round-to-nearest; refuses non-finite / out-of-envelope
/// values rather than saturating.
pub fn lift_cert(cert: &CertQp, scale: u32) -> Result<CertQpExact, LiftError> {
    if scale > MAX_SCALE {
        return Err(LiftError::ScaleTooLarge);
    }
    let (n, mc) = (cert.n, cert.mc);
    let shapes_ok = n.checked_mul(n).is_some_and(|nn| cert.p.len() == nn)
        && mc.checked_mul(n).is_some_and(|mn| cert.a.len() == mn)
        && cert.q.len() == n
        && cert.l.len() == mc
        && cert.u.len() == mc
        && cert.x.len() == n
        && cert.y.len() == mc;
    if !shapes_ok {
        return Err(LiftError::BadShape);
    }
    if !cert.epsilon.is_finite() || cert.epsilon < 0.0 {
        return Err(LiftError::NegativeEpsilon);
    }
    let s = 10i128.pow(scale);
    let epsilon = lift_value(cert.epsilon, s, "epsilon", 0)?;
    Ok(CertQpExact {
        n,
        mc,
        scale,
        p: lift_slice(&cert.p, s, "p")?,
        q: lift_slice(&cert.q, s, "q")?,
        a: lift_slice(&cert.a, s, "a")?,
        l: lift_slice(&cert.l, s, "l")?,
        u: lift_slice(&cert.u, s, "u")?,
        x: lift_slice(&cert.x, s, "x")?,
        y: lift_slice(&cert.y, s, "y")?,
        epsilon,
    })
}

/// Checked dot of a matrix row with a vector (both scale `S`; result scale `S²`).
fn row_dot(row: &[i128], v: &[i128]) -> Option<i128> {
    let mut acc: i128 = 0;
    for (a, b) in row.iter().zip(v) {
        acc = acc.checked_add(a.checked_mul(*b)?)?;
    }
    Some(acc)
}

impl CertQpExact {
    fn well_formed(&self) -> bool {
        self.scale <= MAX_SCALE
            && self.n.checked_mul(self.n) == Some(self.p.len())
            && self.mc.checked_mul(self.n) == Some(self.a.len())
            && self.q.len() == self.n
            && self.l.len() == self.mc
            && self.u.len() == self.mc
            && self.x.len() == self.n
            && self.y.len() == self.mc
            && self.epsilon >= 0
            && self.l.iter().zip(&self.u).all(|(l, u)| l <= u)
    }

    /// Decide `rustCertQpCheck` exactly at the denoted rationals. Recomputes
    /// every residual from `(P,q,A,l,u,x,y)`; trusts nothing else (there is
    /// nothing else). Overflow fails CLOSED.
    pub fn check(&self) -> CertQpExactReport {
        if !self.well_formed() {
            return CertQpExactReport::failed_closed(false);
        }
        match self.residuals() {
            None => CertQpExactReport::failed_closed(true),
            Some((prim, dual, normal, tol)) => {
                let primal_feasible = prim <= tol;
                let dual_feasible = dual <= tol;
                let normal_cone = normal <= tol;
                CertQpExactReport {
                    well_formed: true,
                    overflow: false,
                    primal_feasible,
                    dual_feasible,
                    normal_cone,
                    prim_res: Some(prim),
                    dual_res: Some(dual),
                    normal_res: Some(normal),
                    tol: Some(tol),
                    valid: primal_feasible && dual_feasible && normal_cone,
                }
            }
        }
    }

    /// Bind this certificate's complete public problem image to an independent
    /// [`QpProblem`] at the certificate's exact fixed-point scale.
    ///
    /// This is deliberately stronger than comparing only `P`: PSD admission
    /// attaches to `P`, but the KKT witness also depends on the linear objective
    /// and every constraint `(q,A,l,u)`.  A certificate for a different mandate
    /// with the same covariance matrix must not authorize this one.
    pub fn verify_problem_binding(&self, problem: &QpProblem) -> Result<(), QpProblemBindingError> {
        if self.scale > MAX_SCALE {
            return Err(QpProblemBindingError::Lift(LiftError::ScaleTooLarge));
        }
        if !self.well_formed() {
            return Err(QpProblemBindingError::Lift(LiftError::BadShape));
        }
        if self.n != problem.n || self.mc != problem.mc {
            return Err(QpProblemBindingError::DimensionMismatch {
                certificate_n: self.n,
                certificate_mc: self.mc,
                program_n: problem.n,
                program_mc: problem.mc,
            });
        }
        let shapes_ok = problem
            .n
            .checked_mul(problem.n)
            .is_some_and(|nn| problem.p.len() == nn)
            && problem
                .mc
                .checked_mul(problem.n)
                .is_some_and(|mn| problem.a.len() == mn)
            && problem.q.len() == problem.n
            && problem.l.len() == problem.mc
            && problem.u.len() == problem.mc;
        if !shapes_ok {
            return Err(QpProblemBindingError::Lift(LiftError::BadShape));
        }

        let scale = 10i128.pow(self.scale);
        let compare = |field: &'static str,
                       embedded: &[i128],
                       public: &[f64]|
         -> Result<(), QpProblemBindingError> {
            // Keep the old error ordering without allocating a lifted Vec:
            // malformed public values outrank a mismatch anywhere earlier in
            // the same field, while the first mismatch wins when every value
            // is liftable. This is the exact predicate/error semantics of
            // `lift_slice(public, ..)?` followed by `position`, streamed in one
            // pass over hostile input.
            let mut first_mismatch = None;
            for (index, (&expected, &actual)) in embedded.iter().zip(public).enumerate() {
                let lifted = lift_value(actual, scale, field, index)?;
                if first_mismatch.is_none() && expected != lifted {
                    first_mismatch = Some(index);
                }
            }
            first_mismatch.map_or(Ok(()), |index| {
                Err(QpProblemBindingError::FieldMismatch { field, index })
            })
        };
        compare("p", &self.p, &problem.p)?;
        compare("q", &self.q, &problem.q)?;
        compare("a", &self.a, &problem.a)?;
        compare("l", &self.l, &problem.l)?;
        compare("u", &self.u, &problem.u)?;
        Ok(())
    }

    /// `(prim, dual, normal, tol)` at scale `S²`, or `None` on overflow.
    fn residuals(&self) -> Option<(i128, i128, i128, i128)> {
        let s = 10i128.pow(self.scale);
        let (n, mc) = (self.n, self.mc);

        // Stream each A row exactly once into both constraint residuals.  The
        // previous checker first materialized `Ax: Vec<i128>` and then scanned
        // it twice.  `collect::<Option<Vec<_>>>()` cannot retain the range's
        // exact-size hint, so a 256-row certificate grew that temporary seven
        // times (8,128 allocated bytes) on every verification.  Primal and
        // normal-cone residuals need only the current row scalar; retaining it
        // beyond this iteration changes neither exact arithmetic nor the
        // fail-closed verdict.
        let mut prim: i128 = 0;
        let mut normal: i128 = 0;
        for i in 0..mc {
            let ax_i = row_dot(&self.a[i * n..(i + 1) * n], &self.x)?;
            let us = self.u[i].checked_mul(s)?;
            let ls = self.l[i].checked_mul(s)?;
            let over = ax_i.checked_sub(us)?.max(0);
            let under = ls.checked_sub(ax_i)?.max(0);
            prim = prim.max(over.checked_add(under)?);

            // rustNormalResidual:
            // max_i |Ax − clamp(Ax + yS, lS, uS)|.
            let shifted = ax_i.checked_add(self.y[i].checked_mul(s)?)?;
            let projected = shifted.clamp(ls, us);
            normal = normal.max(ax_i.checked_sub(projected)?.checked_abs()?);
        }

        // rustDualResidual: max_j |(Px)_j + q_j·S + (Aᵀy)_j|.
        let mut dual: i128 = 0;
        for j in 0..n {
            let px_j = row_dot(&self.p[j * n..(j + 1) * n], &self.x)?;
            let mut aty_j: i128 = 0;
            for i in 0..mc {
                aty_j = aty_j.checked_add(self.a[i * n + j].checked_mul(self.y[i])?)?;
            }
            let qs = self.q[j].checked_mul(s)?;
            let stat = px_j.checked_add(qs)?.checked_add(aty_j)?;
            dual = dual.max(stat.checked_abs()?);
        }

        let tol = self.epsilon.checked_mul(s)?;
        Some((prim, dual, normal, tol))
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::qp::{markowitz, solve_admm, CertQp};

    const SC: u32 = 6;
    const S: i128 = 1_000_000; // 10^SC
    const S2: i128 = S * S;

    /// The former allocating implementation, retained only as a test oracle
    /// for the streaming cutover. This is deliberately not production code.
    fn allocating_residual_oracle(cert: &CertQpExact) -> Option<(i128, i128, i128, i128)> {
        let s = 10i128.pow(cert.scale);
        let (n, mc) = (cert.n, cert.mc);
        let ax: Vec<i128> = (0..mc)
            .map(|i| row_dot(&cert.a[i * n..(i + 1) * n], &cert.x))
            .collect::<Option<_>>()?;

        let mut prim: i128 = 0;
        for i in 0..mc {
            let us = cert.u[i].checked_mul(s)?;
            let ls = cert.l[i].checked_mul(s)?;
            let over = ax[i].checked_sub(us)?.max(0);
            let under = ls.checked_sub(ax[i])?.max(0);
            prim = prim.max(over.checked_add(under)?);
        }

        let mut dual: i128 = 0;
        for j in 0..n {
            let px_j = row_dot(&cert.p[j * n..(j + 1) * n], &cert.x)?;
            let mut aty_j: i128 = 0;
            for i in 0..mc {
                aty_j = aty_j.checked_add(cert.a[i * n + j].checked_mul(cert.y[i])?)?;
            }
            let qs = cert.q[j].checked_mul(s)?;
            let stat = px_j.checked_add(qs)?.checked_add(aty_j)?;
            dual = dual.max(stat.checked_abs()?);
        }

        let mut normal: i128 = 0;
        for i in 0..mc {
            let us = cert.u[i].checked_mul(s)?;
            let ls = cert.l[i].checked_mul(s)?;
            let shifted = ax[i].checked_add(cert.y[i].checked_mul(s)?)?;
            let projected = shifted.clamp(ls, us);
            normal = normal.max(ax[i].checked_sub(projected)?.checked_abs()?);
        }

        Some((prim, dual, normal, cert.epsilon.checked_mul(s)?))
    }

    fn small_signed(state: &mut u64) -> i128 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((*state >> 32) % 11) as i128 - 5
    }

    fn small_values(state: &mut u64, count: usize) -> Vec<i128> {
        (0..count).map(|_| small_signed(state)).collect()
    }

    #[test]
    fn streaming_residuals_match_allocating_oracle_and_hostile_overflow() {
        // Exercise every dimension/scale shape with signed coefficients rather
        // than comparing only a cooperative identity matrix.
        let mut state = 0x6b6b_742d_7374_7265;
        for n in 1..=8 {
            for mc in 0..=8 {
                for scale in 0..=3 {
                    let mut l = Vec::with_capacity(mc);
                    let mut u = Vec::with_capacity(mc);
                    for _ in 0..mc {
                        let left = small_signed(&mut state);
                        let right = small_signed(&mut state);
                        l.push(left.min(right));
                        u.push(left.max(right));
                    }
                    let cert = CertQpExact {
                        n,
                        mc,
                        scale,
                        p: small_values(&mut state, n * n),
                        q: small_values(&mut state, n),
                        a: small_values(&mut state, mc * n),
                        l,
                        u,
                        x: small_values(&mut state, n),
                        y: small_values(&mut state, mc),
                        epsilon: small_signed(&mut state).unsigned_abs() as i128,
                    };
                    assert!(cert.well_formed());
                    assert_eq!(
                        cert.residuals(),
                        allocating_residual_oracle(&cert),
                        "streaming drift at n={n}, mc={mc}, scale={scale}"
                    );
                }
            }
        }

        // The old pass computed every Ax row before checking bounds. The new
        // pass may encounter this first-row bound overflow before the hostile
        // second-row dot overflow, but both are the same observable fail-closed
        // arithmetic result; no later error can turn either into acceptance.
        let hostile = CertQpExact {
            n: 2,
            mc: 2,
            scale: MAX_SCALE,
            p: vec![0; 4],
            q: vec![0; 2],
            a: vec![0, 0, i128::MAX, i128::MAX],
            l: vec![i128::MIN, 0],
            u: vec![i128::MAX, 0],
            x: vec![2, 2],
            y: vec![0, 0],
            epsilon: 0,
        };
        assert_eq!(hostile.residuals(), allocating_residual_oracle(&hostile));
        assert_eq!(
            hostile.check(),
            CertQpExactReport::failed_closed(true),
            "hostile arithmetic must remain a closed failure"
        );
    }

    /// `rustQpOne` from CertQpRustDenotation.lean: min ½x²−x on 0≤x≤2, lifted.
    fn qp_one(x: i128, y: i128, epsilon: i128) -> CertQpExact {
        CertQpExact {
            n: 1,
            mc: 1,
            scale: SC,
            p: vec![S],
            q: vec![-S],
            a: vec![S],
            l: vec![0],
            u: vec![2 * S],
            x: vec![x],
            y: vec![y],
            epsilon,
        }
    }

    // ---- Lean-pinned golden vectors (the #guard lines of the Lean file) ----

    #[test]
    fn lean_pinned_approx_witness_accepts() {
        // rustApproxWitness: x=0, y=0, ε=1 → prim=0, dual=1, normal=0, ACCEPT
        // (Lean: rustApprox_primal_zero / rustApprox_dual_one /
        //  rustApprox_normal_zero, #guard rustCertQpCheck rustApproxWitness).
        let rep = qp_one(0, 0, S).check();
        assert_eq!(rep.prim_res, Some(0));
        assert_eq!(rep.dual_res, Some(S2), "dual residual is EXACTLY 1");
        assert_eq!(rep.normal_res, Some(0));
        assert!(rep.valid, "{rep:?}");
    }

    #[test]
    fn lean_pinned_forged_dual_rejected_at_zero_tolerance() {
        // rustForgedDualWitness: x=0, y=+1, ε=0 — the wrong-sign-dual forgery
        // with prim=dual=0. Lean: rustForgedDual_normal_one +
        // rustForgedDual_rejected. The normal-cone residual is EXACTLY 1.
        let rep = qp_one(0, S, 0).check();
        assert_eq!(rep.prim_res, Some(0));
        assert_eq!(rep.dual_res, Some(0));
        assert_eq!(rep.normal_res, Some(S2), "normal residual is EXACTLY 1");
        assert!(!rep.valid, "forged dual must be rejected: {rep:?}");
    }

    #[test]
    fn lean_pinned_exact_witness_accepts_at_zero_tolerance() {
        // rustExactWitness: x=1, y=0, ε=0 — the true optimum, certified at
        // ZERO tolerance (Lean: #guard rustCertQpCheck rustExactWitness).
        // f64 cannot honestly make an ε=0 claim; the integer carrier can.
        let rep = qp_one(S, 0, 0).check();
        assert_eq!(rep.prim_res, Some(0));
        assert_eq!(rep.dual_res, Some(0));
        assert_eq!(rep.normal_res, Some(0));
        assert!(rep.valid, "exact optimum certifies at ε=0: {rep:?}");
    }

    #[test]
    fn tolerance_scale_is_exact_one_below_rejects() {
        // ε = 1 − 10^−6 (one integer tick below the dual residual): REJECT.
        // Pins the tol=ε·S scale bookkeeping — a checker comparing at the
        // wrong scale (ε·S² say) would falsely accept.
        let rep = qp_one(0, 0, S - 1).check();
        assert_eq!(rep.dual_res, Some(S2));
        assert_eq!(rep.tol, Some((S - 1) * S));
        assert!(!rep.valid, "residual one tick over ε must reject: {rep:?}");
    }

    // ---- The f64 bridge on a real solve ----

    fn solved_markowitz() -> (CertQp, crate::qp::QpProblem) {
        let n = 5;
        let mut cov = vec![0.0f64; n * n];
        for i in 0..n {
            for j in 0..n {
                cov[i * n + j] = if i == j {
                    1.0 + i as f64 * 0.1
                } else {
                    0.2 / (1.0 + (i as f64 - j as f64).abs())
                };
            }
        }
        let mu: Vec<f64> = (0..n).map(|i| 0.05 + 0.02 * i as f64).collect();
        let prob = markowitz(&cov, &mu, 1.0, 1.0);
        let res = solve_admm(&prob, 4000, 1.0, 1e-6, 1.6);
        (CertQp::from_solution(&prob, &res, 1e-3), prob)
    }

    #[test]
    fn real_admm_solve_lifts_and_certifies_exactly() {
        let (cert, _) = solved_markowitz();
        assert!(cert.check().valid, "f64 baseline sanity");
        let exact = lift_cert(&cert, 9).expect("finite in-range certificate lifts");
        let rep = exact.check();
        assert!(rep.well_formed && !rep.overflow);
        assert!(
            rep.valid,
            "real ADMM solve certifies under the exact checker: {rep:?}"
        );
    }

    #[test]
    fn f64_and_exact_agree_on_the_solved_instance() {
        let (cert, _) = solved_markowitz();
        let exact = lift_cert(&cert, 9).expect("lifts");
        assert_eq!(
            cert.check().valid,
            exact.check().valid,
            "verdicts agree away from the ε boundary"
        );
    }

    #[test]
    fn tampered_exact_certificate_rejected() {
        let (cert, _) = solved_markowitz();
        let mut exact = lift_cert(&cert, 9).expect("lifts");
        exact.x[0] += 10i128.pow(9) / 2; // +0.5 breaks budget + stationarity
        assert!(!exact.check().valid, "tampered x must be rejected");
    }

    #[test]
    fn exact_certificate_binds_the_complete_independent_qp() {
        let cert = qp_one(S, 0, 0);
        let problem = QpProblem {
            n: 1,
            mc: 1,
            p: vec![1.0],
            q: vec![-1.0],
            a: vec![1.0],
            l: vec![0.0],
            u: vec![2.0],
        };
        cert.verify_problem_binding(&problem)
            .expect("the independent public QP is exactly the embedded problem");

        // Same PSD matrix, different linear mandate.  Comparing only P would
        // accept this substitution even though the optimum changes.
        let mut different_objective = problem.clone();
        different_objective.q[0] = -2.0;
        assert_eq!(
            cert.verify_problem_binding(&different_objective),
            Err(QpProblemBindingError::FieldMismatch {
                field: "q",
                index: 0,
            })
        );

        // And a changed feasible region cannot borrow the old certificate.
        let mut different_constraints = problem;
        different_constraints.u[0] = 3.0;
        assert_eq!(
            cert.verify_problem_binding(&different_constraints),
            Err(QpProblemBindingError::FieldMismatch {
                field: "u",
                index: 0,
            })
        );
    }

    #[test]
    fn streaming_problem_binding_preserves_hostile_lift_error_precedence() {
        let cert = CertQpExact {
            n: 2,
            mc: 1,
            scale: 0,
            p: vec![1, 0, 0, 1],
            q: vec![1, 2],
            a: vec![1, 1],
            l: vec![0],
            u: vec![2],
            x: vec![0, 0],
            y: vec![0],
            epsilon: 0,
        };
        let mut hostile = QpProblem {
            n: 2,
            mc: 1,
            p: vec![1.0, 0.0, 0.0, 1.0],
            // Coordinate zero already differs. The old allocating path lifted
            // the complete field before comparing, so a later malformed value
            // must still fail as malformed rather than being hidden by the
            // earlier mismatch.
            q: vec![9.0, f64::NAN],
            a: vec![1.0, 1.0],
            l: vec![0.0],
            u: vec![2.0],
        };
        assert_eq!(
            cert.verify_problem_binding(&hostile),
            Err(QpProblemBindingError::Lift(LiftError::NonFinite {
                field: "q",
                index: 1,
            }))
        );

        hostile.q[1] = F64_EXACT * 2.0;
        assert_eq!(
            cert.verify_problem_binding(&hostile),
            Err(QpProblemBindingError::Lift(LiftError::OutOfRange {
                field: "q",
                index: 1,
            }))
        );

        // Once the later hostile value is repaired, the first exact mutation
        // remains the reported refusal tooth.
        hostile.q[1] = 2.0;
        assert_eq!(
            cert.verify_problem_binding(&hostile),
            Err(QpProblemBindingError::FieldMismatch {
                field: "q",
                index: 0,
            })
        );
    }

    // ---- Fail-closed polarity ----

    #[test]
    fn overflow_fails_closed_not_wrapped() {
        // p·x overflows i128: the report must be overflow+invalid, never a
        // wrapped (possibly tiny) residual.
        let cert = CertQpExact {
            n: 1,
            mc: 1,
            scale: 0,
            p: vec![i128::MAX / 2],
            q: vec![0],
            a: vec![1],
            l: vec![0],
            u: vec![i128::MAX / 4],
            x: vec![4],
            y: vec![0],
            epsilon: 0,
        };
        let rep = cert.check();
        assert!(rep.well_formed);
        assert!(rep.overflow);
        assert!(!rep.valid);
        assert_eq!(rep.dual_res, None);
    }

    #[test]
    fn bad_shape_fails_closed() {
        let mut cert = qp_one(0, 0, S);
        cert.q = vec![]; // wrong length
        let rep = cert.check();
        assert!(!rep.well_formed);
        assert!(!rep.valid);
    }

    #[test]
    fn crossed_bounds_fail_closed() {
        let mut cert = qp_one(0, 0, S);
        cert.l = vec![3 * S]; // l > u
        assert!(!cert.check().valid);
    }

    #[test]
    fn scale_too_large_refused() {
        let mut cert = qp_one(0, 0, S);
        cert.scale = MAX_SCALE + 1;
        assert!(!cert.check().valid);
        let (f64_cert, _) = solved_markowitz();
        assert_eq!(
            lift_cert(&f64_cert, MAX_SCALE + 1),
            Err(LiftError::ScaleTooLarge)
        );
    }

    #[test]
    fn lift_refuses_nonfinite_and_out_of_range() {
        let (mut cert, _) = solved_markowitz();
        cert.x[0] = f64::NAN;
        assert_eq!(
            lift_cert(&cert, 9),
            Err(LiftError::NonFinite {
                field: "x",
                index: 0
            })
        );
        let (mut cert, _) = solved_markowitz();
        cert.q[1] = 1e40; // finite but |v·10^9| >> 2^53
        assert_eq!(
            lift_cert(&cert, 9),
            Err(LiftError::OutOfRange {
                field: "q",
                index: 1
            })
        );
    }

    #[test]
    fn negative_epsilon_refused_both_sides() {
        let mut cert = qp_one(S, 0, 0);
        cert.epsilon = -1;
        assert!(!cert.check().valid);
        let (mut f64_cert, _) = solved_markowitz();
        f64_cert.epsilon = -1.0;
        assert_eq!(lift_cert(&f64_cert, 9), Err(LiftError::NegativeEpsilon));
    }
}

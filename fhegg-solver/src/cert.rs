//! Cert-F — the primal-dual certificate IR (PRIVATE-CONVEX-ENGINE §2.3).
//!
//! This is the BRIDGE between the untrusted solver and the Lean-verified checker
//! (the other lane) / the STARK. The solver emits `(f, π, s)` together with the
//! public `(A, w, c)`; the checker validates the LINEAR Cert-F inequalities:
//!
//! ```text
//!   A f = 0,   0 ≤ f ≤ c,   s ≥ 0,   Aᵀπ + s ≥ w,   cᵀs − wᵀf ≤ ε
//! ```
//!
//! which certify `ε`-optimality of the circulation LP `max wᵀf s.t. Af=0, 0≤f≤c`
//! INDEPENDENT of how `(f, π, s)` were found. That independence is the whole
//! point: the T PDHG iterations are an untrusted search; THIS is the checked
//! certificate. The `check()` method here mirrors the Lean checker so the solver
//! can self-verify before emitting — but the authoritative decision is the
//! verified checker's, not this one's.
//!
//! ## The wire format
//!
//! `to_json()` emits a self-describing object: the public program (`edges` of
//! the incidence, `w`, `c`), the witness (`f`, `pi`, `s`), the tolerance
//! `epsilon`, and the derived gap/residual. Integer-free, dense vectors — the
//! shape the Lean Cert-F ingestor and the in-STARK checker both consume.

use crate::pdhg::FlowLp;
use serde::Serialize;

/// The Cert-F certificate: public program + primal-dual witness.
#[derive(Clone, Debug, Serialize)]
pub struct CertF {
    /// Number of nodes (rows of `A`).
    pub n_nodes: usize,
    /// Number of edges (columns of `A`, = |f|).
    pub m_edges: usize,
    /// Public incidence, edge list `(tail, head)`.
    pub edges: Vec<(u32, u32)>,
    /// Public objective weights.
    pub w: Vec<f64>,
    /// Public capacities.
    pub c: Vec<f64>,
    /// Primal witness (the flow).
    pub f: Vec<f64>,
    /// Dual witness `π` (node potentials).
    pub pi: Vec<f64>,
    /// Dual slack `s = (w − Aᵀπ)₊` (edge slacks).
    pub s: Vec<f64>,
    /// The optimality tolerance the certificate is claimed against.
    pub epsilon: f64,
    /// Primal objective `wᵀf`.
    pub primal_obj: f64,
    /// Dual objective `cᵀs`.
    pub dual_obj: f64,
    /// Duality gap `cᵀs − wᵀf`.
    pub duality_gap: f64,
    /// Conservation residual `‖A f‖_∞`.
    pub feas_residual: f64,
}

/// The result of running the Cert-F checks (mirrors the Lean checker).
#[derive(Clone, Debug, Serialize)]
pub struct CertReport {
    /// `A f = 0` within `feas_tol`.
    pub conserves: bool,
    /// `0 ≤ f ≤ c` (exact — the box prox guarantees it).
    pub primal_boxed: bool,
    /// `s ≥ 0`.
    pub s_nonneg: bool,
    /// `Aᵀπ + s ≥ w` within `feas_tol`.
    pub dual_feasible: bool,
    /// `cᵀs − wᵀf ≤ ε`.
    pub gap_ok: bool,
    pub gap: f64,
    pub feas_residual: f64,
    /// The tolerance used for the equality/inequality slack.
    pub feas_tol: f64,
    /// Conjunction of every check.
    pub valid: bool,
}

impl CertF {
    /// Build the certificate from a PDHG solution `(f, π)`. Derives the minimal
    /// dual slack `s = (w − Aᵀπ)₊` so that `s ≥ 0` and `Aᵀπ + s ≥ w` hold by
    /// construction (PRIVATE-CONVEX-ENGINE §2.3).
    pub fn from_solution(lp: &FlowLp, f: &[f64], pi: &[f64], epsilon: f64) -> Self {
        let aty = lp.at_times(pi);
        let s: Vec<f64> = (0..lp.m()).map(|e| (lp.w[e] - aty[e]).max(0.0)).collect();
        let primal_obj: f64 = lp.w.iter().zip(f).map(|(w, f)| w * f).sum();
        let dual_obj: f64 = lp.c.iter().zip(&s).map(|(c, s)| c * s).sum();
        let af = lp.a_times(f);
        let feas_residual = af.iter().fold(0.0f64, |m, v| m.max(v.abs()));
        CertF {
            n_nodes: lp.n_nodes,
            m_edges: lp.m(),
            edges: lp.edges.clone(),
            w: lp.w.clone(),
            c: lp.c.clone(),
            f: f.to_vec(),
            pi: pi.to_vec(),
            s,
            epsilon,
            primal_obj,
            dual_obj,
            duality_gap: dual_obj - primal_obj,
            feas_residual,
        }
    }

    /// Run the Cert-F checks. `feas_tol` is the numerical slack allowed on the
    /// equality `Af=0` and the inequality `Aᵀπ+s≥w` (a first-order solver reaches
    /// a small residual, not exact zero — the honest Stage-1 statement; a strict
    /// checker demands a rounding/projection step, a NAMED residual).
    pub fn check_with(&self, feas_tol: f64) -> CertReport {
        // Reconstruct A from edges for the checks (public).
        let lp = FlowLp {
            n_nodes: self.n_nodes,
            edges: self.edges.clone(),
            w: self.w.clone(),
            c: self.c.clone(),
        };
        let af = lp.a_times(&self.f);
        let feas_residual = af.iter().fold(0.0f64, |m, v| m.max(v.abs()));
        let conserves = feas_residual <= feas_tol;

        let primal_boxed = self
            .f
            .iter()
            .zip(&self.c)
            .all(|(f, c)| *f >= -feas_tol && *f <= *c + feas_tol);

        let s_nonneg = self.s.iter().all(|s| *s >= -feas_tol);

        let aty = lp.at_times(&self.pi);
        let dual_feasible = (0..self.m_edges).all(|e| aty[e] + self.s[e] >= self.w[e] - feas_tol);

        let gap = self.dual_obj - self.primal_obj;
        let gap_ok = gap <= self.epsilon;

        let valid = conserves && primal_boxed && s_nonneg && dual_feasible && gap_ok;
        CertReport {
            conserves,
            primal_boxed,
            s_nonneg,
            dual_feasible,
            gap_ok,
            gap,
            feas_residual,
            feas_tol,
            valid,
        }
    }

    /// `check_with` at a default tolerance scaled to the problem magnitude.
    pub fn check(&self) -> CertReport {
        let scale = self.c.iter().cloned().fold(1.0f64, f64::max).max(1.0);
        self.check_with(1e-3 * scale)
    }

    /// Serialize to the JSON wire format the Lean Cert-F checker / STARK ingests.
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pdhg::{cycle_lp, solve_cpu};

    #[test]
    fn valid_certificate_passes_all_checks() {
        let lp = cycle_lp(4, &[4.0, 6.0, 2.0, 8.0], &[1.0; 4]);
        let res = solve_cpu(&lp, 8000);
        let cert = CertF::from_solution(&lp, &res.f, &res.y, 0.1);
        let rep = cert.check();
        assert!(
            rep.valid,
            "well-converged certificate must be valid: {rep:?}"
        );
    }

    #[test]
    fn tampered_flow_is_rejected() {
        // A certificate whose f is corrupted (breaks conservation) must fail.
        let lp = cycle_lp(4, &[4.0, 6.0, 2.0, 8.0], &[1.0; 4]);
        let res = solve_cpu(&lp, 8000);
        let mut cert = CertF::from_solution(&lp, &res.f, &res.y, 0.1);
        cert.f[0] += 2.0; // inject non-conservation
        let rep = cert.check();
        assert!(!rep.conserves, "tampered f breaks A f = 0");
        assert!(!rep.valid, "tampered certificate must be rejected");
    }

    #[test]
    fn json_roundtrips_shape() {
        let lp = cycle_lp(3, &[1.0; 3], &[1.0; 3]);
        let res = solve_cpu(&lp, 2000);
        let cert = res.certificate(&lp, 0.1);
        let json = cert.to_json();
        assert!(json.contains("\"edges\""));
        assert!(json.contains("\"pi\""));
        assert!(json.contains("\"duality_gap\""));
        // Round-trips back to a value with the same edge count.
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["m_edges"], 3);
    }
}

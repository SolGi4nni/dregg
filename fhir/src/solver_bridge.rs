//! Wire to `fhegg-solver` — a compiled product's [`ConvexProgram`] RUNS through
//! the real PDHG / ADMM / aggregation engine and produces its certificate.
//!
//! This closes the loop the docs describe (`PRIVATE-CONVEX-ENGINE.md` §2.6, §3;
//! `DREGGFI-PRIVACY-TIERS.md` §2): adding a product is *writing its convex
//! program + its prox*, and the SAME oblivious solver + certificate serve all of
//! them. `run` dispatches on the compiled program and returns the engine's own
//! certificate report — the untrusted solver's output, checked by the
//! certificate (translation validation), exactly as the engine intends.

use crate::compile::{Compiled, ConvexProgram};
use fhegg_solver::cert::{CertF, CertReport};
use fhegg_solver::clearing::{allocate, clear, Allocation, Clearing};
use fhegg_solver::pdhg::solve_cpu;
use fhegg_solver::qp::{solve_admm, CertQp, CertQpReport};

/// The outcome of running a compiled product through the engine — the certificate
/// and whether it validates.
#[derive(Clone, Debug)]
pub enum RunOutcome {
    /// Uniform-price aggregation: the cleared market + conserving allocation. The
    /// `T=1` conservation certificate is `alloc.conserves()`.
    Aggregation {
        clearing: Clearing,
        allocation: Allocation,
    },
    /// Flow-LP: the Cert-F primal-dual certificate + its check report.
    CertF { cert: CertF, report: CertReport },
    /// QP: the CertQp KKT-residual certificate + its check report.
    CertQp { cert: CertQp, report: CertQpReport },
    /// The program's runner is the fhIR-1 lane (Price-Cert). The shape compiled;
    /// the engine builder is future work — stated plainly, not faked.
    NotWired { reason: &'static str },
}

impl RunOutcome {
    /// Did the certificate validate? For aggregation, conservation
    /// (`Σ buy = Σ sell`); for Cert-F/CertQp, the certificate check. `NotWired`
    /// is neither valid nor invalid — it never ran.
    pub fn certificate_valid(&self) -> Option<bool> {
        match self {
            RunOutcome::Aggregation { allocation, .. } => Some(allocation.conserves()),
            RunOutcome::CertF { report, .. } => Some(report.valid),
            RunOutcome::CertQp { report, .. } => Some(report.valid),
            RunOutcome::NotWired { .. } => None,
        }
    }

    /// A one-line human summary of the certificate.
    pub fn summary(&self) -> String {
        match self {
            RunOutcome::Aggregation {
                clearing,
                allocation,
            } => format!(
                "uniform-price: crossed={} p*={} V*={} conserves={} (buy={}, sell={})",
                clearing.crossed,
                clearing.clearing_price,
                clearing.cleared_volume,
                allocation.conserves(),
                allocation.buy_volume,
                allocation.sell_volume,
            ),
            RunOutcome::CertF { report, cert } => format!(
                "Cert-F: valid={} gap={:.3e} (ε={:.1e}) feas_residual={:.3e} primal_obj={:.4}",
                report.valid, report.gap, cert.epsilon, report.feas_residual, cert.primal_obj,
            ),
            RunOutcome::CertQp { report, cert } => format!(
                "CertQp: valid={} prim_res={:.3e} dual_res={:.3e} (ε={:.1e}) objective={:.4}",
                report.valid, report.prim_res, report.dual_res, cert.epsilon, cert.objective,
            ),
            RunOutcome::NotWired { reason } => format!("not-wired: {reason}"),
        }
    }
}

/// Run a compiled product through the engine and produce its certificate.
pub fn run(compiled: &Compiled) -> RunOutcome {
    match &compiled.program {
        ConvexProgram::Aggregation { orders, k } => {
            let clearing = clear(orders, *k);
            let allocation = allocate(orders, &clearing);
            RunOutcome::Aggregation {
                clearing,
                allocation,
            }
        }
        ConvexProgram::FlowLp(lp) => {
            let res = solve_cpu(lp, 8000);
            // ε scaled to the problem magnitude — the honest Stage-1 tolerance.
            let scale = lp.c.iter().cloned().fold(1.0f64, f64::max).max(1.0);
            let cert = res.certificate(lp, 0.05 * scale);
            let report = cert.check();
            RunOutcome::CertF { cert, report }
        }
        ConvexProgram::Qp(prob) => {
            let res = solve_admm(prob, 6000, 1.0, 1e-6, 1.6);
            let cert = CertQp::from_solution(prob, &res, 1e-3);
            let report = cert.check();
            RunOutcome::CertQp { cert, report }
        }
        ConvexProgram::StatePriceLp { .. } => RunOutcome::NotWired {
            reason:
                "Price-Cert state-price LP runner is the fhIR-1 lane; the shape type-checks here",
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::compile;
    use crate::products;

    #[test]
    fn uniform_price_runs_and_conserves() {
        let c = compile(&products::uniform_price_clearing()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        if let RunOutcome::Aggregation { clearing, .. } = &out {
            assert!(clearing.crossed);
            assert!(clearing.cleared_volume > 0);
        } else {
            panic!("expected aggregation outcome");
        }
    }

    #[test]
    fn flow_lp_runs_and_certifies() {
        let c = compile(&products::flow_lp_clearing()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
    }

    #[test]
    fn portfolio_qp_runs_and_certifies() {
        let c = compile(&products::portfolio_qp_public()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
    }

    #[test]
    fn small_flow_runs_and_certifies() {
        let c = compile(&products::small_flow_clearing()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
    }

    #[test]
    fn derivative_is_not_wired_but_typed() {
        let c = compile(&products::derivative_price_cert()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), None);
        assert!(matches!(out, RunOutcome::NotWired { .. }));
    }
}

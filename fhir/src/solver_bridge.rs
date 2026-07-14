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
use fhegg_solver::cfmm::{solve_waterfill, CertRoute, CertRouteReport};
use fhegg_solver::clearing::{allocate, clear, Allocation, Clearing};
use fhegg_solver::discriminatory::{clear_discriminatory, DiscriminatoryClearing};
use fhegg_solver::fisher::{solve_proportional_response, CertEq, CertEqReport};
use fhegg_solver::package::{clear_package, CertPackage, CertPackageReport, PackageClearing};
use fhegg_solver::pdhg::solve_cpu;
use fhegg_solver::pricecert::{
    solve_price_cert, solve_snell_cert, CertPrice, CertPriceReport, CertSnell, CertSnellReport,
    PriceOutcome,
};
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
    /// Discriminatory / pay-as-bid: the winner-determination Cert-F certificate +
    /// the clearing (fills + both settlement schemes).
    Discriminatory {
        cert: CertF,
        report: CertReport,
        clearing: DiscriminatoryClearing,
    },
    /// Welfare-max / Fisher: the equilibrium CertEq certificate + its report.
    CertEq { cert: CertEq, report: CertEqReport },
    /// CFMM routing: the CertRoute certificate + its report.
    CertRoute {
        cert: CertRoute,
        report: CertRouteReport,
    },
    /// Price-Cert (European / basket / Asian): the state-price LP CertPrice +
    /// its check report — the arbitrage-free price with its superhedging dual.
    CertPrice {
        cert: CertPrice,
        report: CertPriceReport,
    },
    /// Price-Cert (American / Bermudan): the Snell-envelope CertSnell + its check
    /// report — the certified early-exercise value.
    CertSnell {
        cert: CertSnell,
        report: CertSnellReport,
    },
    /// The market admits ARBITRAGE (no consistent state price `π ≥ 0` with
    /// `Hπ = a`) — there is NO arbitrage-free price and NO certificate. The
    /// honest negative polarity of the Price-Cert runner (a mispriced/arbitrage
    /// derivative is REJECTED, not certified).
    NoArbitrageFreePrice { reason: &'static str },
    /// Package / all-or-none clearing: the CERTIFIED-APPROXIMATION certificate
    /// (feasible integral packing + a Lagrangian near-optimality bound) + its
    /// report + the clearing (accepts, welfare, certified ratio).
    CertPackage {
        cert: CertPackage,
        report: CertPackageReport,
        clearing: PackageClearing,
    },
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
            RunOutcome::Discriminatory { report, .. } => Some(report.valid),
            RunOutcome::CertEq { report, .. } => Some(report.valid),
            RunOutcome::CertRoute { report, .. } => Some(report.valid),
            RunOutcome::CertPrice { report, .. } => Some(report.valid),
            RunOutcome::CertSnell { report, .. } => Some(report.valid),
            // Arbitrage detected → the derivative is REJECTED (no valid cert).
            RunOutcome::NoArbitrageFreePrice { .. } => Some(false),
            RunOutcome::CertPackage { report, .. } => Some(report.valid),
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
            RunOutcome::Discriminatory {
                report, clearing, ..
            } => format!(
                "pay-as-bid: valid={} V*={:.2} marginal_p*={:.3} | pay-as-bid buyer_pays={:.2} surplus={:.2} vs uniform buyer_pays={:.2} surplus=0",
                report.valid,
                clearing.volume,
                clearing.marginal_price,
                clearing.payg_buyer_pays,
                clearing.discriminatory_surplus,
                clearing.uniform_buyer_pays,
            ),
            RunOutcome::CertEq { report, cert } => format!(
                "Fisher-eq: valid={} stationary={} buyer_cs={:.3e} clearing_cs={:.3e} EG_obj={:.4} (n={} buyers, {} goods)",
                report.valid,
                report.stationary,
                report.buyer_cs,
                report.clearing_cs,
                cert.eg_objective,
                cert.n_buyers,
                cert.n_goods,
            ),
            RunOutcome::CertRoute { report, cert } => format!(
                "CFMM-route: valid={} routing_cs={:.3e} budget_cs={:.3e} λ={:.4} output={:.4} (N={} pools)",
                report.valid,
                report.routing_cs,
                report.budget_cs,
                cert.lambda,
                cert.total_output,
                cert.pools.len(),
            ),
            RunOutcome::CertPrice { report, cert } => format!(
                "Price-Cert: valid={} price(hᵀπ)={:.4} hedge(aᵀy)={:.4} gap={:.3e} (ε={:.1e}) π≥0={} Hπ=a={} yᵀH≥h={} (S={}, J={})",
                report.valid,
                cert.primal_price,
                cert.dual_cost,
                report.gap,
                cert.epsilon,
                report.pi_nonneg,
                report.consistent,
                report.superhedge,
                cert.n_scenarios,
                cert.n_instruments,
            ),
            RunOutcome::CertSnell { report, cert } => format!(
                "Snell-Cert: valid={} value(V_root)={:.4} dominates={} superharmonic={} (nodes={}, d={:.4})",
                report.valid,
                cert.root_value,
                report.dominates,
                report.superharmonic,
                cert.n_nodes,
                cert.d,
            ),
            RunOutcome::NoArbitrageFreePrice { reason } => {
                format!("no-arbitrage-free-price (REJECTED): {reason}")
            }
            RunOutcome::CertPackage {
                report, clearing, ..
            } => format!(
                "Package-Cert (certified-approx): valid={} integral={} capacity_ok={} | W={:.2} UB={:.2} ratio={:.3} (achieved ≥ {:.1}% of optimum) accepted={}/{}",
                report.valid,
                report.integral,
                report.capacity_ok,
                clearing.welfare,
                clearing.upper_bound,
                report.ratio,
                report.ratio * 100.0,
                clearing.accept.iter().filter(|&&x| x > 0.5).count(),
                clearing.accept.len(),
            ),
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
        ConvexProgram::Discriminatory { orders, prices } => {
            let (clearing, cert) = clear_discriminatory(orders, prices, 8000);
            let report = cert.check();
            RunOutcome::Discriminatory {
                cert,
                report,
                clearing,
            }
        }
        ConvexProgram::WelfareMax(market) => {
            let res = solve_proportional_response(market, 20_000);
            let cert = res.certificate(market, 1e-4);
            let report = cert.check();
            RunOutcome::CertEq { cert, report }
        }
        ConvexProgram::CfmmRouting(prob) => {
            let res = solve_waterfill(prob, 100);
            let cert = res.certificate(prob, 1e-6);
            let report = cert.check();
            RunOutcome::CertRoute { cert, report }
        }
        ConvexProgram::StatePriceLp(market) => match solve_price_cert(market) {
            PriceOutcome::Certified(cert) => {
                let report = cert.check();
                RunOutcome::CertPrice { cert, report }
            }
            PriceOutcome::Arbitrage => RunOutcome::NoArbitrageFreePrice {
                reason: "no consistent state price π≥0 with Hπ=a — the marks admit arbitrage",
            },
        },
        ConvexProgram::SnellLp(tree) => {
            let cert = solve_snell_cert(tree, 1e-9);
            let report = cert.check();
            RunOutcome::CertSnell { cert, report }
        }
        ConvexProgram::PackageClearing(auction) => {
            let (clearing, cert) = clear_package(auction, 4000);
            let report = cert.check();
            RunOutcome::CertPackage {
                cert,
                report,
                clearing,
            }
        }
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
    fn european_price_cert_runs_and_certifies() {
        // The state-price LP runs end-to-end: compile → run → CertPrice valid,
        // with the hand-checked upper price 0.48 and a tight (gap 0) superhedge.
        let c = compile(&products::derivative_price_cert()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        if let RunOutcome::CertPrice { cert, report } = &out {
            assert!((cert.primal_price - 0.48).abs() < 1e-6, "{}", out.summary());
            assert!(cert.gap.abs() < 1e-6, "tight gap: {}", cert.gap);
            assert!(report.pi_nonneg && report.consistent && report.superhedge);
        } else {
            panic!("expected a CertPrice outcome, got {}", out.summary());
        }
    }

    #[test]
    fn american_snell_runs_and_certifies() {
        // The Snell-envelope LP runs end-to-end for the early-exercise value.
        let c = compile(&products::american_put_price_cert()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        if let RunOutcome::CertSnell { cert, report } = &out {
            assert!(cert.root_value > 0.0, "ATM American put has value");
            assert!(
                report.dominates && report.superharmonic,
                "{}",
                out.summary()
            );
        } else {
            panic!("expected a CertSnell outcome, got {}", out.summary());
        }
    }

    #[test]
    fn arbitrage_derivative_is_rejected() {
        // The runner's honest negative polarity: an arbitrage market yields NO
        // certificate — certificate_valid() is NOT Some(true).
        let c = compile(&products::arbitrage_derivative_rejected()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(false), "{}", out.summary());
        assert!(matches!(out, RunOutcome::NoArbitrageFreePrice { .. }));
    }

    #[test]
    fn discriminatory_runs_and_certifies() {
        let c = compile(&products::discriminatory_clearing()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        if let RunOutcome::Discriminatory { clearing, .. } = &out {
            assert!(clearing.volume > 0.0, "an overlapping book must trade");
            // Pay-as-bid extracts more than uniform-price (auctioneer surplus > 0).
            assert!(
                clearing.discriminatory_surplus > 1e-6,
                "pay-as-bid surplus must be positive: {}",
                clearing.discriminatory_surplus
            );
        } else {
            panic!("expected discriminatory outcome");
        }
    }

    #[test]
    fn welfare_max_runs_and_certifies() {
        let c = compile(&products::welfare_max_fisher()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        assert!(matches!(out, RunOutcome::CertEq { .. }));
    }

    #[test]
    fn cfmm_routing_runs_and_certifies() {
        let c = compile(&products::cfmm_routing()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        assert!(matches!(out, RunOutcome::CertRoute { .. }));
    }
}

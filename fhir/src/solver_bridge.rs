//! Wire to `fhegg-solver` — a compiled product's [`ConvexProgram`] RUNS through
//! the real PDHG / ADMM / aggregation engine and produces its certificate.
//!
//! This closes the loop the docs describe (`PRIVATE-CONVEX-ENGINE.md` §2.6, §3;
//! `DREGGFI-PRIVACY-TIERS.md` §2): adding a product is *writing its convex
//! program + its prox*, and the SAME oblivious solver + certificate serve all of
//! them. `run` dispatches on the compiled program and returns the engine's own
//! certificate report — the untrusted solver's output, checked by the
//! certificate (translation validation), exactly as the engine intends.

use crate::compile::{Compiled, ConvexProgram, ExactSddPsdCertificateError, QP_CERT_EXACT_SCALE};
use fhegg_solver::cert::{CertF, CertReport};
use fhegg_solver::cfmm::{solve_waterfill, CertRoute, CertRouteReport};
use fhegg_solver::clearing::{allocate, clear, Allocation, Clearing, Order, Side};
use fhegg_solver::discriminatory::{clear_discriminatory, DiscriminatoryClearing};
use fhegg_solver::fisher::{solve_proportional_response, CertEq, CertEqReport};
use fhegg_solver::package::{clear_package, CertPackage, CertPackageReport, PackageClearing};
use fhegg_solver::pdhg::solve_cpu;
use fhegg_solver::pricecert::{
    solve_price_cert, solve_snell_cert, CertPrice, CertPriceReport, CertSnell, CertSnellReport,
    PriceOutcome,
};
use fhegg_solver::qp::{solve_admm, CertQp, CertQpReport};
use fhegg_solver::qp_exact::{lift_cert, CertQpExact, CertQpExactReport, LiftError};
use sha2::{Digest, Sha256};
use std::fmt;

const AGGREGATION_SOURCE_DOMAIN: &[u8] = b"fhir/aggregation-source-orders/v1";

/// Minimal retained witness for executable validation of a uniform-price
/// allocation.
///
/// `Allocation::validate` needs the complete index-aligned `(side, qty, limit)`
/// tuple for every source order; a digest alone cannot re-run its per-order cap
/// and individual-rationality checks.  The orders are therefore retained but
/// deliberately kept private and redacted from `Debug`; callers receive only
/// their count and canonical SHA-256 commitment.  This reduces accidental
/// disclosure, not in-memory exposure: a plaintext fhIR aggregation outcome is
/// not itself a hiding certificate and must not cross a Dark privacy boundary.
#[derive(Clone)]
pub struct AggregationSourceBinding {
    k: usize,
    orders: Vec<Order>,
    commitment: [u8; 32],
}

impl AggregationSourceBinding {
    /// Bind the canonical index-ordered source book used to construct an
    /// aggregation outcome. The plaintext copy is retained privately so the
    /// executable validator remains available after `Compiled` is dropped.
    pub fn new(orders: &[Order], k: usize) -> Self {
        Self {
            k,
            orders: orders.to_vec(),
            commitment: aggregation_source_commitment(orders, k),
        }
    }

    pub fn order_count(&self) -> usize {
        self.orders.len()
    }

    pub fn commitment(&self) -> [u8; 32] {
        self.commitment
    }

    /// Check an externally retained plaintext book against this outcome's
    /// canonical source commitment without exposing the internally retained
    /// copy. This is an integrity join, not a hiding proof.
    pub fn matches_source(&self, orders: &[Order], k: usize) -> bool {
        self.k == k && self.commitment == aggregation_source_commitment(orders, k)
    }

    /// Re-run the complete deterministic aggregation certificate from its
    /// retained source witness.  The stored clearing/allocation are outputs to
    /// be checked, never cached authority.
    pub fn validate(&self, clearing: &Clearing, allocation: &Allocation) -> bool {
        if self.commitment != aggregation_source_commitment(&self.orders, self.k)
            || clearing.k != self.k
        {
            return false;
        }
        let derived_clearing = clear(&self.orders, self.k);
        if !same_clearing(clearing, &derived_clearing)
            || !allocation.validate(&self.orders, clearing)
        {
            return false;
        }
        let derived_allocation = allocate(&self.orders, &derived_clearing);
        same_allocation(allocation, &derived_allocation)
    }
}

impl fmt::Debug for AggregationSourceBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AggregationSourceBinding")
            .field("k", &self.k)
            .field("order_count", &self.orders.len())
            .field("commitment", &self.commitment)
            .finish_non_exhaustive()
    }
}

fn aggregation_source_commitment(orders: &[Order], k: usize) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(AGGREGATION_SOURCE_DOMAIN);
    hash.update((k as u64).to_be_bytes());
    hash.update((orders.len() as u64).to_be_bytes());
    for order in orders {
        hash.update([match order.side {
            Side::Bid => 0,
            Side::Ask => 1,
        }]);
        hash.update(order.qty.to_be_bytes());
        hash.update(order.limit.to_be_bytes());
    }
    hash.finalize().into()
}

fn same_clearing(left: &Clearing, right: &Clearing) -> bool {
    left.k == right.k
        && left.demand == right.demand
        && left.supply == right.supply
        && left.crossed == right.crossed
        && left.clearing_price == right.clearing_price
        && left.cleared_volume == right.cleared_volume
}

fn same_allocation(left: &Allocation, right: &Allocation) -> bool {
    left.fills == right.fills
        && left.buy_volume == right.buy_volume
        && left.sell_volume == right.sell_volume
}

/// Fixed-point scale used by the product runner's exact CertQp acceptance gate.
/// The exact checker certifies the rounded `10^-9` problem; the f64 report is
/// retained only as a diagnostic twin, never as the acceptance decision.
/// Exact CertQp translation-validation result. A failed f64→fixed lift is an
/// in-band certificate refusal, not a panic or a fallback to the f64 verdict.
#[derive(Clone, Debug)]
pub enum ExactCertQpVerdict {
    Checked {
        cert: CertQpExact,
        report: CertQpExactReport,
    },
    Refused(LiftError),
}

impl ExactCertQpVerdict {
    pub fn valid(&self) -> bool {
        match self {
            // The report is a cached diagnostic. The exact certificate is the
            // executable authority, so every acceptance query re-runs its
            // fail-closed fixed-point checker.
            Self::Checked { cert, .. } => cert.check().valid,
            Self::Refused(_) => false,
        }
    }
}

/// The outcome of running a compiled product through the engine — the certificate
/// and whether it validates.
#[derive(Clone, Debug)]
pub enum RunOutcome {
    /// The compiler carrier was altered or lost its exact QP PSD admission
    /// evidence. No solver iteration or output certificate was produced.
    InvalidCompiled { reason: ExactSddPsdCertificateError },
    /// Uniform-price aggregation: the cleared market + allocation + a redacted,
    /// commitment-bound source witness capable of re-running the complete
    /// deterministic validator. The witness retains plaintext orders in memory;
    /// see [`AggregationSourceBinding`] for the exact privacy boundary.
    Aggregation {
        clearing: Clearing,
        allocation: Allocation,
        source: AggregationSourceBinding,
    },
    /// Flow-LP: the Cert-F primal-dual certificate + its check report.
    CertF { cert: CertF, report: CertReport },
    /// QP: the original f64 certificate/report for diagnostics plus the exact
    /// fixed-point checker verdict that exclusively decides acceptance.
    CertQp {
        cert: CertQp,
        report: CertQpReport,
        exact: ExactCertQpVerdict,
    },
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
    /// Did the certificate validate? Every outcome re-executes its attached
    /// checker rather than trusting a cached report. Aggregation re-hashes its
    /// retained canonical source orders, re-derives the clearing and allocation,
    /// and runs `Allocation::validate` against those exact orders.
    pub fn certificate_valid(&self) -> Option<bool> {
        match self {
            RunOutcome::InvalidCompiled { .. } => Some(false),
            RunOutcome::Aggregation {
                clearing,
                allocation,
                source,
            } => Some(source.validate(clearing, allocation)),
            // Reports are cached diagnostics, not authority. Re-run the checker
            // over the attached public program + witness so mutating a
            // certificate after solving cannot inherit an earlier green bit.
            RunOutcome::CertF { cert, .. } => Some(cert.check().valid),
            RunOutcome::CertQp { exact, .. } => Some(exact.valid()),
            RunOutcome::Discriminatory { cert, .. } => Some(cert.check().valid),
            RunOutcome::CertEq { cert, .. } => Some(cert.check().valid),
            RunOutcome::CertRoute { cert, .. } => Some(cert.check().valid),
            RunOutcome::CertPrice { cert, .. } => Some(cert.check().valid),
            RunOutcome::CertSnell { cert, .. } => Some(cert.check().valid),
            // Arbitrage detected → the derivative is REJECTED (no valid cert).
            RunOutcome::NoArbitrageFreePrice { .. } => Some(false),
            RunOutcome::CertPackage { cert, .. } => Some(cert.check().valid),
        }
    }

    /// A one-line human summary of the certificate.
    pub fn summary(&self) -> String {
        match self {
            RunOutcome::InvalidCompiled { reason } => {
                format!("compiled-program: INVALID exact-SDD-PSD-certificate={reason}")
            }
            RunOutcome::Aggregation {
                clearing,
                allocation,
                source,
            } => format!(
                "uniform-price: crossed={} p*={} V*={} valid={} conserves={} (buy={}, sell={}; source_orders={})",
                clearing.crossed,
                clearing.clearing_price,
                clearing.cleared_volume,
                source.validate(clearing, allocation),
                allocation.conserves(),
                allocation.buy_volume,
                allocation.sell_volume,
                source.order_count(),
            ),
            RunOutcome::CertF { cert, .. } => {
                let checked = cert.check();
                format!(
                    "Cert-F: valid={} gap={:.3e} (ε={:.1e}) feas_residual={:.3e} primal_obj={:.4}",
                    checked.valid,
                    checked.gap,
                    cert.epsilon,
                    checked.feas_residual,
                    cert.primal_obj,
                )
            }
            RunOutcome::CertQp {
                report,
                cert,
                exact,
            } => match exact {
                ExactCertQpVerdict::Checked {
                    cert: exact_cert, ..
                } => {
                    let checked = exact_cert.check();
                    format!(
                        "CertQp-exact: valid={} scale=1e-{} prim={:?} dual={:?} normal={:?} tol={:?}; f64 diagnostic valid={} (ε={:.1e}) objective={:.4}",
                        checked.valid,
                        exact_cert.scale,
                        checked.prim_res,
                        checked.dual_res,
                        checked.normal_res,
                        checked.tol,
                        report.valid,
                        cert.epsilon,
                        cert.objective,
                    )
                }
                ExactCertQpVerdict::Refused(error) => format!(
                    "CertQp-exact: REFUSED lift={error:?}; f64 diagnostic valid={} (not an acceptance gate)",
                    report.valid,
                ),
            },
            RunOutcome::Discriminatory { cert, clearing, .. } => format!(
                "pay-as-bid: valid={} V*={:.2} marginal_p*={:.3} | pay-as-bid buyer_pays={:.2} surplus={:.2} vs uniform buyer_pays={:.2} surplus=0",
                cert.check().valid,
                clearing.volume,
                clearing.marginal_price,
                clearing.payg_buyer_pays,
                clearing.discriminatory_surplus,
                clearing.uniform_buyer_pays,
            ),
            RunOutcome::CertEq { cert, .. } => {
                let checked = cert.check();
                let eg_objective: f64 = (0..cert.n_buyers)
                    .map(|i| {
                        let utility: f64 = (0..cert.n_goods)
                            .map(|j| cert.util[i * cert.n_goods + j] * cert.x[i * cert.n_goods + j])
                            .sum();
                        cert.budgets[i] * utility.max(1e-12).ln()
                    })
                    .sum();
                format!(
                    "Fisher-eq: valid={} stationary={} buyer_cs={:.3e} clearing_cs={:.3e} EG_obj={:.4} (n={} buyers, {} goods)",
                    checked.valid,
                    checked.stationary,
                    checked.buyer_cs,
                    checked.clearing_cs,
                    eg_objective,
                    cert.n_buyers,
                    cert.n_goods,
                )
            }
            RunOutcome::CertRoute { cert, .. } => {
                let checked = cert.check();
                let total_output: f64 = cert
                    .pools
                    .iter()
                    .zip(&cert.delta)
                    .map(|(pool, &delta)| pool.output(delta))
                    .sum();
                format!(
                    "CFMM-route: valid={} routing_cs={:.3e} budget_cs={:.3e} λ={:.4} output={:.4} (N={} pools)",
                    checked.valid,
                    checked.routing_cs,
                    checked.budget_cs,
                    cert.lambda,
                    total_output,
                    cert.pools.len(),
                )
            }
            RunOutcome::CertPrice { cert, .. } => {
                let checked = cert.check();
                let price: f64 = cert.h.iter().zip(&cert.pi).map(|(h, p)| h * p).sum();
                let cost: f64 = cert.a.iter().zip(&cert.y).map(|(a, y)| a * y).sum();
                format!(
                    "Price-Cert: valid={} price(hᵀπ)={:.4} hedge(aᵀy)={:.4} gap={:.3e} (ε={:.1e}) π≥0={} Hπ=a={} yᵀH≥h={} (S={}, J={})",
                    checked.valid,
                    price,
                    cost,
                    checked.gap,
                    cert.epsilon,
                    checked.pi_nonneg,
                    checked.consistent,
                    checked.superhedge,
                    cert.n_scenarios,
                    cert.n_instruments,
                )
            }
            RunOutcome::CertSnell { cert, .. } => {
                let checked = cert.check();
                format!(
                    "Snell-Cert: valid={} value(V_root)={:.4} dominates={} superharmonic={} (nodes={}, d={:.4})",
                    checked.valid,
                    checked.root_value,
                    checked.dominates,
                    checked.superharmonic,
                    cert.n_nodes,
                    cert.d,
                )
            }
            RunOutcome::NoArbitrageFreePrice { reason } => {
                format!("no-arbitrage-free-price (REJECTED): {reason}")
            }
            RunOutcome::CertPackage { cert, .. } => {
                let checked = cert.check();
                format!(
                    "Package-Cert (certified-approx): valid={} integral={} capacity_ok={} | W={:.2} UB={:.2} ratio={:.3} (achieved ≥ {:.1}% of optimum) accepted={}/{}",
                    checked.valid,
                    checked.integral,
                    checked.capacity_ok,
                    checked.welfare,
                    checked.upper_bound,
                    checked.ratio,
                    checked.ratio * 100.0,
                    cert.accept.iter().filter(|&&x| x > 0.5).count(),
                    cert.accept.len(),
                )
            }
        }
    }
}

/// Run a compiled product through the engine and produce its certificate.
pub fn run(compiled: &Compiled) -> RunOutcome {
    if let Err(reason) = compiled.verify_exact_sdd_psd_certificate() {
        return RunOutcome::InvalidCompiled { reason };
    }
    match &compiled.program {
        ConvexProgram::Aggregation { orders, k } => {
            let clearing = clear(orders, *k);
            let allocation = allocate(orders, &clearing);
            let source = AggregationSourceBinding::new(orders, *k);
            RunOutcome::Aggregation {
                clearing,
                allocation,
                source,
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
            let exact = match lift_cert(&cert, QP_CERT_EXACT_SCALE) {
                Ok(exact_cert) => {
                    let exact_report = exact_cert.check();
                    ExactCertQpVerdict::Checked {
                        cert: exact_cert,
                        report: exact_report,
                    }
                }
                Err(error) => ExactCertQpVerdict::Refused(error),
            };
            RunOutcome::CertQp {
                cert,
                report,
                exact,
            }
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
        if let RunOutcome::Aggregation {
            clearing, source, ..
        } = &out
        {
            assert!(clearing.crossed);
            assert!(clearing.cleared_volume > 0);
            assert_eq!(source.order_count(), 4);
            assert_ne!(source.commitment(), [0; 32]);
            let ConvexProgram::Aggregation { orders, k } = &c.program else {
                unreachable!("uniform product compiled as aggregation")
            };
            assert!(source.matches_source(orders, *k));
            let debug = format!("{source:?}");
            assert!(debug.contains("order_count"));
            assert!(!debug.contains("qty"), "source orders stay Debug-redacted");
        } else {
            panic!("expected aggregation outcome");
        }
    }

    #[test]
    fn aggregation_rechecks_source_clearing_and_allocation_in_both_directions() {
        let compiled = compile(&products::uniform_price_clearing()).unwrap();
        let baseline = run(&compiled);
        assert_eq!(baseline.certificate_valid(), Some(true));

        // Output -> source: moving one unit between active buyers keeps both
        // side volumes conserved and even passes Allocation::validate's cap/IR
        // checks, but it is not the deterministic largest-remainder allocation.
        // Re-execution, rather than a cached `conserves()` bit, refuses it.
        let mut moved = baseline.clone();
        let RunOutcome::Aggregation {
            clearing,
            allocation,
            source,
        } = &mut moved
        else {
            panic!("uniform product must aggregate")
        };
        allocation.fills[0] += 1;
        allocation.fills[1] -= 1;
        assert!(allocation.conserves());
        assert!(allocation.validate(&source.orders, clearing));
        assert_eq!(moved.certificate_valid(), Some(false));
        assert!(moved.summary().contains("valid=false"));

        // A forged aggregate curve is likewise invisible to `conserves()` and
        // Allocation::validate, but differs from the source-order fold.
        let mut forged_curve = baseline.clone();
        let RunOutcome::Aggregation {
            clearing,
            allocation,
            source,
        } = &mut forged_curve
        else {
            unreachable!()
        };
        clearing.demand[0] += 1;
        assert!(allocation.conserves());
        assert!(allocation.validate(&source.orders, clearing));
        assert_eq!(forged_curve.certificate_valid(), Some(false));

        // Source -> output: an order substitution with a recomputed, internally
        // consistent source commitment cannot inherit the old clearing/fills.
        // Swapping the two bids leaves the aggregate curves unchanged, making
        // this specifically exercise index-aligned allocation binding.
        let mut substituted_source = baseline.clone();
        let RunOutcome::Aggregation { source, .. } = &mut substituted_source else {
            unreachable!()
        };
        source.orders.swap(0, 1);
        source.commitment = aggregation_source_commitment(&source.orders, source.k);
        assert_eq!(substituted_source.certificate_valid(), Some(false));

        // The public commitment is checked too; corrupting only that cached
        // binding cannot reject by changing executable facts into another book,
        // but it must fail closed as a malformed certificate carrier.
        let mut corrupt_binding = baseline;
        let RunOutcome::Aggregation { source, .. } = &mut corrupt_binding else {
            unreachable!()
        };
        source.commitment[0] ^= 1;
        assert_eq!(corrupt_binding.certificate_valid(), Some(false));
    }

    #[test]
    fn flow_lp_runs_and_certifies() {
        let c = compile(&products::flow_lp_clearing()).unwrap();
        let out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
    }

    #[test]
    fn cert_f_outcome_rechecks_the_attached_certificate() {
        let c = compile(&products::flow_lp_clearing()).unwrap();
        let mut out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());

        let RunOutcome::CertF { cert, report } = &mut out else {
            panic!("flow product must return Cert-F")
        };
        assert!(report.valid, "cached diagnostic starts green");
        cert.f[0] = cert.c[0] + 1.0;
        assert!(
            report.valid,
            "the old cached report is deliberately unchanged"
        );
        assert_eq!(
            out.certificate_valid(),
            Some(false),
            "acceptance must re-run the attached certificate checker"
        );
        assert!(out.summary().contains("valid=false"));
    }

    #[test]
    fn portfolio_qp_runs_and_certifies() {
        let c = compile(&products::portfolio_qp_public()).unwrap();
        let certificate = c
            .exact_sdd_psd_certificate
            .as_ref()
            .expect("portfolio compiler emits exact SDD/PSD admission evidence");
        let ConvexProgram::Qp(problem) = &c.program else {
            unreachable!()
        };
        assert_eq!(certificate.dimension(), problem.n);
        certificate.verify_against(problem).unwrap();
        c.verify_exact_sdd_psd_certificate().unwrap();
        let mut out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        match &mut out {
            RunOutcome::CertQp {
                report: f64_report,
                exact:
                    ExactCertQpVerdict::Checked {
                        cert,
                        report: exact_report,
                    },
                ..
            } => {
                assert_eq!(cert.scale, QP_CERT_EXACT_SCALE);
                assert!(f64_report.valid, "the legacy diagnostic starts true");
                assert!(
                    exact_report.valid,
                    "exact checker is the gate: {exact_report:?}"
                );
                // A cached report is diagnostic only: making it red cannot
                // override the still-valid executable certificate.
                exact_report.valid = false;
            }
            other => panic!("expected exact CertQp verdict, got {other:?}"),
        }
        assert_eq!(
            out.certificate_valid(),
            Some(true),
            "a mutated cached report must not decide exact-QP acceptance"
        );

        let RunOutcome::CertQp {
            exact:
                ExactCertQpVerdict::Checked {
                    cert,
                    report: exact_report,
                },
            ..
        } = &mut out
        else {
            unreachable!("matched exact CertQp above")
        };
        exact_report.valid = true;
        cert.x.fill(0);
        assert!(
            exact_report.valid,
            "cached diagnostic is deliberately green"
        );
        assert_eq!(
            out.certificate_valid(),
            Some(false),
            "all-zero weights violate the exact budget row despite cached green"
        );
        assert!(out.summary().contains("CertQp-exact: valid=false"));
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
        let mut out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        let RunOutcome::CertPrice { cert, report } = &mut out else {
            panic!("expected a CertPrice outcome")
        };
        assert!((cert.primal_price - 0.48).abs() < 1e-6);
        assert!(cert.gap.abs() < 1e-6, "tight gap: {}", cert.gap);
        assert!(report.pi_nonneg && report.consistent && report.superhedge);

        // Cached reports are diagnostics only: making the cache red cannot
        // override a still-valid executable certificate.
        report.valid = false;
        assert_eq!(
            out.certificate_valid(),
            Some(true),
            "a mutated cached report must not reject a valid Price-Cert"
        );

        let RunOutcome::CertPrice { cert, report } = &mut out else {
            unreachable!("matched CertPrice above")
        };
        report.valid = true;
        cert.pi.fill(0.0);
        assert!(report.valid, "cached diagnostic is deliberately green");
        assert_eq!(
            out.certificate_valid(),
            Some(false),
            "zero state prices violate Hπ=a despite cached green"
        );
        assert!(out.summary().contains("Price-Cert: valid=false"));
    }

    #[test]
    fn american_snell_runs_and_certifies() {
        // The Snell-envelope LP runs end-to-end for the early-exercise value.
        let c = compile(&products::american_put_price_cert()).unwrap();
        let mut out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        let RunOutcome::CertSnell { cert, report } = &mut out else {
            panic!("expected a CertSnell outcome")
        };
        assert!(cert.root_value > 0.0, "ATM American put has value");
        assert!(report.dominates && report.superharmonic);

        cert.root_value = 12_345.0;
        report.valid = false;
        assert_eq!(
            out.certificate_valid(),
            Some(true),
            "a mutated cached report must not reject a valid Snell certificate"
        );
        let summary = out.summary();
        assert!(summary.contains("Snell-Cert: valid=true"));
        assert!(!summary.contains("value(V_root)=12345.0000"));

        let RunOutcome::CertSnell { cert, report } = &mut out else {
            unreachable!("matched CertSnell above")
        };
        report.valid = true;
        cert.v.fill(0.0);
        assert!(report.valid, "cached diagnostic is deliberately green");
        assert_eq!(
            out.certificate_valid(),
            Some(false),
            "zero node values violate payoff dominance despite cached green"
        );
        assert!(out.summary().contains("Snell-Cert: valid=false"));
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
        let mut out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        let RunOutcome::CertEq { cert, report } = &mut out else {
            panic!("expected a CertEq outcome")
        };
        assert!(report.valid, "cached diagnostic starts green");
        cert.eg_objective = 12_345.0;
        report.valid = false;
        assert_eq!(
            out.certificate_valid(),
            Some(true),
            "a mutated cached report must not reject a valid equilibrium"
        );
        let summary = out.summary();
        assert!(summary.contains("Fisher-eq: valid=true"));
        assert!(!summary.contains("EG_obj=12345.0000"));

        let RunOutcome::CertEq { cert, report } = &mut out else {
            unreachable!("matched CertEq above")
        };
        report.valid = true;
        cert.x.fill(0.0);
        assert!(report.valid, "cached diagnostic is deliberately green");
        assert_eq!(
            out.certificate_valid(),
            Some(false),
            "an empty allocation violates equilibrium KKT despite cached green"
        );
        assert!(out.summary().contains("Fisher-eq: valid=false"));
    }

    #[test]
    fn cfmm_routing_runs_and_certifies() {
        let c = compile(&products::cfmm_routing()).unwrap();
        let mut out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        let RunOutcome::CertRoute { cert, report } = &mut out else {
            panic!("expected a CertRoute outcome")
        };
        assert!(report.valid, "cached diagnostic starts green");
        cert.total_output = 12_345.0;
        report.valid = false;
        assert_eq!(
            out.certificate_valid(),
            Some(true),
            "a mutated cached report must not reject a valid route"
        );
        let summary = out.summary();
        assert!(summary.contains("CFMM-route: valid=true"));
        assert!(!summary.contains("output=12345.0000"));

        let RunOutcome::CertRoute { cert, report } = &mut out else {
            unreachable!("matched CertRoute above")
        };
        report.valid = true;
        cert.delta.fill(0.0);
        assert!(report.valid, "cached diagnostic is deliberately green");
        assert_eq!(
            out.certificate_valid(),
            Some(false),
            "an empty route violates routing KKT despite cached green"
        );
        assert!(out.summary().contains("CFMM-route: valid=false"));
    }

    #[test]
    fn package_outcome_rechecks_the_attached_certificate() {
        let c = compile(&products::package_auction_clearing()).unwrap();
        let mut out = run(&c);
        assert_eq!(out.certificate_valid(), Some(true), "{}", out.summary());
        let RunOutcome::CertPackage { cert, report, .. } = &mut out else {
            panic!("expected a CertPackage outcome")
        };
        assert!(report.valid, "cached diagnostic starts green");
        cert.welfare = 12_345.0;
        cert.upper_bound = 23_456.0;
        report.valid = false;
        assert_eq!(
            out.certificate_valid(),
            Some(true),
            "a mutated cached report must not reject a valid package clearing"
        );
        let summary = out.summary();
        assert!(summary.contains("Package-Cert (certified-approx): valid=true"));
        assert!(!summary.contains("W=12345.00"));
        assert!(!summary.contains("UB=23456.00"));

        let RunOutcome::CertPackage { cert, report, .. } = &mut out else {
            unreachable!("matched CertPackage above")
        };
        report.valid = true;
        cert.accept[0] = 0.5;
        assert!(report.valid, "cached diagnostic is deliberately green");
        assert_eq!(
            out.certificate_valid(),
            Some(false),
            "a fractional fill violates all-or-none despite cached green"
        );
        assert!(out
            .summary()
            .contains("Package-Cert (certified-approx): valid=false"));
    }
}

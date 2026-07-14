//! The compiler — `compile(product) -> Result<Compiled, TypeError>`.
//!
//! Two jobs (`FHEGG-PRODUCT-ORDER-FRONTIER.md` R2.3; `DREGGFI-PRIVACY-TIERS.md`
//! §3):
//!
//! 1. **Lower** the product AST to a back-end [`ConvexProgram`] (holding the REAL
//!    `fhegg-solver` engine types) plus its extracted [`ProgramType`] shape.
//! 2. **Infer the most-private honest tier** via [`most_private_admissible`] —
//!    the minimum tier in the privacy order at which the shape type-checks — and,
//!    if the author CLAIMED a tier, REJECT the product when the math delivers
//!    less privacy than claimed (with the precise underlying obstruction).
//!
//! The honest guarantee: if `compile` returns `Ok(c)` with `c.tier == T`, the
//! shape is `T`-admissible (the admissibility DIRECTION: compiles ⇒ runnable at
//! `T`), and `T` is the MOST private tier that holds — the compiler never
//! reports more privacy than the math delivers. The converse (admissible ⇒
//! compiles, the full iff) is the six-part theorem, the Lean lane's target.

use crate::ast::{
    BinomialSpec, EdgeSpec, FillType, MatrixData, OrderSide, OrderSpec, PackageBidSpec, Product,
    ProductBody,
};
use crate::tier::Tier;
use crate::types::{
    CertKind, Cone, Curvature, IntegerFeature, MatrixFlag, MatrixRole, ProgramKind, ProgramType,
    TypeError, Visibility,
};

use crate::ast::PoolSpec;
use fhegg_solver::cfmm::{Pool, RoutingProblem};
use fhegg_solver::clearing::{Order as EngineOrder, Side as EngineSide};
use fhegg_solver::fisher::FisherMarket;
use fhegg_solver::package::{PackageAuction, PackageBid};
use fhegg_solver::pdhg::FlowLp;
use fhegg_solver::pricecert::{american_put_binomial, Market, SnellTree};
use fhegg_solver::qp::{markowitz, QpProblem};

/// The back-end IR a product compiles to — holding the REAL `fhegg-solver`
/// engine types, so a compiled program RUNS through the engine unchanged
/// (`solver_bridge::run`).
#[derive(Clone, Debug)]
pub enum ConvexProgram {
    /// A uniform-price aggregation over `k` price levels (fhEgg `T=1`).
    Aggregation { orders: Vec<EngineOrder>, k: usize },
    /// A volume-max circulation flow-LP.
    FlowLp(FlowLp),
    /// A quadratic program (portfolio / Markowitz).
    Qp(QpProblem),
    /// A state-price / superhedging LP (Price-Cert) — the REAL `fhegg-solver`
    /// market, so a compiled derivative RUNS the state-price LP and emits its
    /// CertPrice (the fhIR-1 runner).
    StatePriceLp(Market),
    /// A Snell-envelope LP (Price-Cert American/Bermudan) — the REAL scenario
    /// tree, so a compiled early-exercise option RUNS backward induction and
    /// emits its CertSnell.
    SnellLp(SnellTree),
    /// A discriminatory / pay-as-bid clearing: the input book + the public price
    /// grid. Runs the gains-from-trade flow-LP (Cert-F) + the pay-as-bid payment.
    Discriminatory {
        orders: Vec<EngineOrder>,
        prices: Vec<f64>,
    },
    /// A welfare-max / Fisher-market equilibrium (Eisenberg–Gale).
    WelfareMax(FisherMarket),
    /// A CFMM optimal-routing program over public pool curves.
    CfmmRouting(RoutingProblem),
    /// A package / all-or-none combinatorial auction. Runs the certified-
    /// approximation clearing (an integral packing + a Lagrangian dual bound) and
    /// emits its CertPackage.
    PackageClearing(PackageAuction),
}

/// A successfully-compiled product: its program, its most-private honest tier,
/// its certificate kind, and the shape the tier was inferred from.
#[derive(Clone, Debug)]
pub struct Compiled {
    pub name: String,
    pub program: ConvexProgram,
    /// The MOST-PRIVATE tier the math honestly delivers.
    pub tier: Tier,
    pub cert: CertKind,
    pub shape: ProgramType,
}

/// The lowering result: the extracted type + the runnable program.
struct Lowered {
    shape: ProgramType,
    program: ConvexProgram,
}

/// Infer the most-private admissible tier: the minimum tier (in the privacy
/// order `Dark < Shielded < Open`) at which the shape type-checks. `Open` always
/// type-checks in fhIR-0, so this always returns a tier.
pub fn most_private_admissible(shape: &ProgramType) -> Tier {
    Tier::ALL
        .into_iter()
        .find(|&t| shape.admissible_at(t).is_ok())
        .unwrap_or(Tier::Open)
}

/// Compile a product: lower it, infer the most-private honest tier, and reject
/// an over-claim with the precise reason.
pub fn compile(p: &Product) -> Result<Compiled, TypeError> {
    let Lowered { shape, program } = lower(p);
    let honest = most_private_admissible(&shape);

    if let Some(claimed) = p.claim {
        // The author promised `claimed`. It is honest only if the delivered tier
        // is at least as private (`honest <= claimed`). Otherwise the product
        // over-claims privacy — reject with the STRUCTURAL reason it fails at the
        // claimed tier.
        if !honest.at_least_as_private_as(claimed) {
            if let Err(because) = shape.admissible_at(claimed) {
                return Err(TypeError::OverClaimsTier {
                    claimed,
                    honest,
                    because: Box::new(because),
                });
            }
        }
    }

    Ok(Compiled {
        name: p.name.clone(),
        cert: shape.cert,
        program,
        tier: honest,
        shape,
    })
}

/// Lower one product form to `(shape, program)`.
fn lower(p: &Product) -> Lowered {
    match &p.body {
        ProductBody::UniformPrice { orders, k } => lower_uniform_price(orders, *k),
        ProductBody::FlowClearing { nodes, edges } => lower_flow(*nodes, edges),
        ProductBody::Portfolio {
            cov,
            mu,
            lambda,
            w_max,
        } => lower_portfolio(cov, mu, *lambda, *w_max),
        ProductBody::Derivative {
            instruments,
            marks,
            payoff,
        } => lower_derivative(instruments, marks, payoff),
        ProductBody::American { spec } => lower_american(spec),
        ProductBody::Discriminatory { orders, k } => lower_discriminatory(orders, *k),
        ProductBody::WelfareMax {
            n_buyers,
            n_goods,
            budgets,
            supplies,
            util,
        } => lower_welfare_max(*n_buyers, *n_goods, budgets, supplies, util),
        ProductBody::CfmmRouting { pools, budget } => lower_cfmm(pools, *budget),
        ProductBody::PackageAuction {
            n_items,
            supply,
            bids,
        } => lower_package(*n_items, supply, bids),
    }
}

fn lower_uniform_price(orders: &[OrderSpec], k: usize) -> Lowered {
    let engine_orders: Vec<EngineOrder> = orders
        .iter()
        .map(|o| EngineOrder {
            side: match o.side {
                OrderSide::Bid => EngineSide::Bid,
                OrderSide::Ask => EngineSide::Ask,
            },
            qty: o.qty,
            limit: o.limit,
        })
        .collect();

    // Any all-or-none order lifts the whole batch out of the continuous regime.
    let integer_features: Vec<IntegerFeature> = orders
        .iter()
        .filter(|o| o.fill == FillType::AllOrNone)
        .map(|_| IntegerFeature::AllOrNone)
        .take(1)
        .collect();

    let shape = ProgramType {
        kind: ProgramKind::Aggregation,
        curvature: Curvature::Affine,
        // The aggregation "matrix" is the PUBLIC price-grid step-encoding — no
        // private matrix. Only the amounts (qty) are private.
        matrices: vec![MatrixFlag {
            role: MatrixRole::Constraint,
            visibility: Visibility::Public,
        }],
        cones: vec![Cone::NonNeg],
        integer_features,
        size: orders.len(),
        cert: CertKind::Aggregation,
    };
    Lowered {
        shape,
        program: ConvexProgram::Aggregation {
            orders: engine_orders,
            k,
        },
    }
}

fn lower_flow(nodes: usize, edges: &[EdgeSpec]) -> Lowered {
    let edge_list: Vec<(u32, u32)> = edges.iter().map(|e| (e.tail, e.head)).collect();
    let w: Vec<f64> = edges.iter().map(|e| e.weight).collect();
    let c: Vec<f64> = edges.iter().map(|e| e.cap).collect();
    let lp = FlowLp {
        n_nodes: nodes,
        edges: edge_list,
        w,
        c,
    };

    let shape = ProgramType {
        kind: ProgramKind::FlowLp,
        curvature: Curvature::Affine,
        // The incidence A is topology — ALWAYS public.
        matrices: vec![MatrixFlag {
            role: MatrixRole::Constraint,
            visibility: Visibility::Public,
        }],
        cones: vec![Cone::Zero, Cone::Box], // Af=0, 0≤f≤c
        integer_features: vec![],
        size: edges.len(),
        cert: CertKind::CertF,
    };
    Lowered {
        shape,
        program: ConvexProgram::FlowLp(lp),
    }
}

fn lower_portfolio(cov: &MatrixData, mu: &[f64], lambda: f64, w_max: f64) -> Lowered {
    let prob: QpProblem = markowitz(&cov.data, mu, lambda, w_max);
    let shape = ProgramType {
        kind: ProgramKind::Qp,
        curvature: Curvature::Convex, // ½xᵀΣx — quadratic
        matrices: vec![
            // The covariance Σ is the objective matrix P — its visibility is the
            // cheap-regime boundary.
            MatrixFlag {
                role: MatrixRole::Objective,
                visibility: cov.visibility,
            },
            // The budget + box constraints are public structure.
            MatrixFlag {
                role: MatrixRole::Constraint,
                visibility: Visibility::Public,
            },
        ],
        cones: vec![Cone::Box], // 0 ≤ x ≤ w_max (+ budget equality)
        integer_features: vec![],
        size: mu.len(),
        cert: CertKind::CertQp,
    };
    Lowered {
        shape,
        program: ConvexProgram::Qp(prob),
    }
}

fn lower_derivative(instruments: &MatrixData, marks: &[f64], payoff: &[f64]) -> Lowered {
    let shape = ProgramType {
        kind: ProgramKind::StatePriceLp,
        curvature: Curvature::Affine, // max hᵀπ s.t. Hπ = a — an LP
        matrices: vec![MatrixFlag {
            // The scenario-payoff grid H is PUBLIC topology.
            role: MatrixRole::Constraint,
            visibility: instruments.visibility,
        }],
        cones: vec![Cone::NonNeg], // state prices π ≥ 0
        integer_features: vec![],
        size: payoff.len(), // M scenarios
        cert: CertKind::PriceCert,
    };
    // The fhir `MatrixData` is SCENARIO-MAJOR (rows = scenarios, cols =
    // instruments); the Market transposes to the instrument-major H the Lean uses.
    let market = Market::from_scenario_major(
        instruments.rows,
        instruments.cols,
        &instruments.data,
        marks.to_vec(),
        payoff.to_vec(),
        1e-6,
    );
    Lowered {
        shape,
        program: ConvexProgram::StatePriceLp(market),
    }
}

fn lower_american(spec: &BinomialSpec) -> Lowered {
    let tree = american_put_binomial(
        spec.s0,
        spec.strike,
        spec.rate,
        spec.vol,
        spec.expiry,
        spec.steps,
        spec.is_put,
    );
    let shape = ProgramType {
        kind: ProgramKind::SnellLp,
        curvature: Curvature::Affine, // min V_root s.t. V ≥ g, V superharmonic — an LP
        matrices: vec![MatrixFlag {
            // The recombining tree topology + transition weights are PUBLIC.
            role: MatrixRole::Constraint,
            visibility: Visibility::Public,
        }],
        cones: vec![Cone::NonNeg], // V ≥ g (dominance), superharmonic rows
        integer_features: vec![],  // optimal stopping is an LP, NOT mixed-integer
        size: tree.n_nodes,
        cert: CertKind::PriceCert,
    };
    Lowered {
        shape,
        program: ConvexProgram::SnellLp(tree),
    }
}

fn lower_discriminatory(orders: &[OrderSpec], k: usize) -> Lowered {
    let engine_orders: Vec<EngineOrder> = orders
        .iter()
        .map(|o| EngineOrder {
            side: match o.side {
                OrderSide::Bid => EngineSide::Bid,
                OrderSide::Ask => EngineSide::Ask,
            },
            qty: o.qty,
            limit: o.limit,
        })
        .collect();
    // The public price grid: level j ↦ price j.
    let prices: Vec<f64> = (0..k).map(|j| j as f64).collect();

    // All-or-none lifts the whole batch out of the continuous regime (as for
    // uniform-price) — the winner-determination stops being an LP.
    let integer_features: Vec<IntegerFeature> = orders
        .iter()
        .filter(|o| o.fill == FillType::AllOrNone)
        .map(|_| IntegerFeature::AllOrNone)
        .take(1)
        .collect();

    let shape = ProgramType {
        kind: ProgramKind::Discriminatory,
        curvature: Curvature::Affine, // gains-from-trade is linear: max wᵀf
        // The two-node gains-from-trade incidence is PUBLIC topology.
        matrices: vec![MatrixFlag {
            role: MatrixRole::Constraint,
            visibility: Visibility::Public,
        }],
        cones: vec![Cone::Zero, Cone::Box], // Af=0, 0≤f≤c
        integer_features,
        size: orders.len(),
        cert: CertKind::CertF,
    };
    Lowered {
        shape,
        program: ConvexProgram::Discriminatory {
            orders: engine_orders,
            prices,
        },
    }
}

fn lower_welfare_max(
    n_buyers: usize,
    n_goods: usize,
    budgets: &[f64],
    supplies: &[f64],
    util: &MatrixData,
) -> Lowered {
    let market = FisherMarket {
        n_buyers,
        n_goods,
        budgets: budgets.to_vec(),
        supplies: supplies.to_vec(),
        util: util.data.clone(),
    };
    let shape = ProgramType {
        kind: ProgramKind::WelfareMax,
        // Σ bᵢ log Uᵢ is CONCAVE — the entropic/mirror-descent prox, outside the
        // FHE v0 affine core (so Dark rejects; Shielded is the honest tier).
        curvature: Curvature::Concave,
        matrices: vec![MatrixFlag {
            // The utility matrix carries the valuations — its visibility is the
            // cheap-regime boundary (public ⇒ everyone sees; private ⇒ solver-only).
            role: MatrixRole::Objective,
            visibility: util.visibility,
        }],
        cones: vec![Cone::NonNeg], // x ≥ 0, Σx ≤ s (nonneg orthant)
        integer_features: vec![],
        size: n_buyers * n_goods,
        cert: CertKind::CertEq,
    };
    Lowered {
        shape,
        program: ConvexProgram::WelfareMax(market),
    }
}

fn lower_cfmm(pools: &[PoolSpec], budget: f64) -> Lowered {
    let engine_pools: Vec<Pool> = pools
        .iter()
        .map(|p| Pool {
            reserve_in: p.reserve_in,
            reserve_out: p.reserve_out,
            fee: p.fee,
        })
        .collect();
    let shape = ProgramType {
        kind: ProgramKind::CfmmRouting,
        // Σ gᵢ(δᵢ) is CONCAVE (rational per-pool output) — nonlinear objective ⇒
        // Shielded, not the affine Dark core.
        curvature: Curvature::Concave,
        matrices: vec![MatrixFlag {
            // The pool curves (reserves) are PUBLIC; only the routing is private.
            role: MatrixRole::Constraint,
            visibility: Visibility::Public,
        }],
        cones: vec![Cone::NonNeg, Cone::Box], // δ ≥ 0, Σδ ≤ Δ
        integer_features: vec![],
        size: pools.len(),
        cert: CertKind::CertRoute,
    };
    Lowered {
        shape,
        program: ConvexProgram::CfmmRouting(RoutingProblem {
            pools: engine_pools,
            budget,
        }),
    }
}

fn lower_package(n_items: usize, supply: &[f64], bids: &[PackageBidSpec]) -> Lowered {
    let engine_bids: Vec<PackageBid> = bids
        .iter()
        .map(|b| PackageBid::new(b.value, b.demand.clone()))
        .collect();
    let auction = PackageAuction {
        n_items,
        supply: supply.to_vec(),
        bids: engine_bids,
    };
    let shape = ProgramType {
        kind: ProgramKind::PackageClearing,
        // The winner-determination is DISCRETE (all-or-none / 0-1 combinatorial),
        // NP-hard — outside the FHE v0 affine-aggregation core, so Dark rejects it
        // (CombinatorialObjective) and the honest tier is Shielded. Note: the
        // integer feature is INTRINSIC to the product and answered by certified
        // approximation, so it is NOT listed as an `IntegerFeature` (which would
        // force Open) — the discrete curvature is the honest signal.
        curvature: Curvature::Discrete,
        matrices: vec![MatrixFlag {
            // The bundle/demand matrix + item supply are PUBLIC structure; only the
            // bid values are private amounts.
            role: MatrixRole::Constraint,
            visibility: Visibility::Public,
        }],
        cones: vec![Cone::NonNeg, Cone::Box], // x ≥ 0, Σ dᵢxᵢ ≤ s; integrality is certified
        integer_features: vec![],
        size: bids.len(),
        cert: CertKind::CertPackage,
    };
    Lowered {
        shape,
        program: ConvexProgram::PackageClearing(auction),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::products;

    #[test]
    fn uniform_price_is_dark_aggregation() {
        let c = compile(&products::uniform_price_clearing()).unwrap();
        assert_eq!(c.tier, Tier::Dark);
        assert_eq!(c.cert, CertKind::Aggregation);
        assert!(matches!(c.program, ConvexProgram::Aggregation { .. }));
    }

    #[test]
    fn flow_clearing_at_scale_is_shielded_certf() {
        let c = compile(&products::flow_lp_clearing()).unwrap();
        assert_eq!(c.tier, Tier::Shielded);
        assert_eq!(c.cert, CertKind::CertF);
    }

    #[test]
    fn portfolio_public_cov_is_shielded_certqp() {
        let c = compile(&products::portfolio_qp_public()).unwrap();
        assert_eq!(c.tier, Tier::Shielded);
        assert_eq!(c.cert, CertKind::CertQp);
    }

    #[test]
    fn portfolio_private_cov_claiming_dark_is_rejected() {
        let err = compile(&products::portfolio_qp_private_claiming_dark()).unwrap_err();
        // The precise reason: a private objective matrix is not Dark-admissible.
        match err {
            TypeError::OverClaimsTier {
                claimed,
                honest,
                because,
            } => {
                assert_eq!(claimed, Tier::Dark);
                assert_eq!(honest, Tier::Shielded);
                assert!(matches!(
                    *because,
                    TypeError::PrivateMatrix {
                        role: MatrixRole::Objective,
                        ..
                    }
                ));
            }
            other => panic!("expected over-claim/private-matrix, got {other:?}"),
        }
    }

    #[test]
    fn all_or_none_claiming_shielded_is_rejected() {
        let err = compile(&products::all_or_none_claiming_shielded()).unwrap_err();
        match err {
            TypeError::OverClaimsTier {
                claimed,
                honest,
                because,
            } => {
                assert_eq!(claimed, Tier::Shielded);
                assert_eq!(honest, Tier::Open);
                assert!(matches!(
                    *because,
                    TypeError::IntegerFeature {
                        feature: IntegerFeature::AllOrNone,
                        ..
                    }
                ));
            }
            other => panic!("expected over-claim/integer-feature, got {other:?}"),
        }
    }

    #[test]
    fn small_flow_reports_dark() {
        // The size boundary works both ways: a SMALL circulation is Dark.
        let c = compile(&products::small_flow_clearing()).unwrap();
        assert_eq!(c.tier, Tier::Dark);
    }

    #[test]
    fn derivative_price_cert_typed() {
        let c = compile(&products::derivative_price_cert()).unwrap();
        assert_eq!(c.cert, CertKind::PriceCert);
        // Small public scenario grid → Dark; the state-price LP runs (fhIR-1).
        assert_eq!(c.tier, Tier::Dark);
        assert!(matches!(c.program, ConvexProgram::StatePriceLp(_)));
    }

    #[test]
    fn american_snell_typed() {
        let c = compile(&products::american_put_price_cert()).unwrap();
        // Same Price-Cert family; the Snell-envelope LP over a public tree (16
        // steps ⇒ 153 nodes) EXCEEDS the Dark LP envelope (64) ⇒ Shielded — the
        // American tree-size cliff (R2.1), the size boundary biting honestly.
        assert_eq!(c.cert, CertKind::PriceCert);
        assert_eq!(c.tier, Tier::Shielded);
        assert!(matches!(c.program, ConvexProgram::SnellLp(_)));
    }

    // --- the mechanism family: three more clearings on the one engine ---

    #[test]
    fn discriminatory_small_is_dark_certf() {
        // Pay-as-bid winner-determination is a linear flow-LP → Cert-F; small book
        // ⇒ Dark. Same certificate as uniform-price's neighbour, different rule.
        let c = compile(&products::discriminatory_clearing()).unwrap();
        assert_eq!(c.tier, Tier::Dark);
        assert_eq!(c.cert, CertKind::CertF);
        assert!(matches!(c.program, ConvexProgram::Discriminatory { .. }));
    }

    #[test]
    fn welfare_max_is_shielded_certeq() {
        // The Eisenberg–Gale log objective is concave ⇒ not Dark ⇒ Shielded.
        let c = compile(&products::welfare_max_fisher()).unwrap();
        assert_eq!(c.tier, Tier::Shielded);
        assert_eq!(c.cert, CertKind::CertEq);
        assert!(matches!(c.program, ConvexProgram::WelfareMax(_)));
    }

    #[test]
    fn cfmm_routing_is_shielded_certroute() {
        // Rational-concave CFMM output ⇒ not Dark ⇒ Shielded, CertRoute.
        let c = compile(&products::cfmm_routing()).unwrap();
        assert_eq!(c.tier, Tier::Shielded);
        assert_eq!(c.cert, CertKind::CertRoute);
        assert!(matches!(c.program, ConvexProgram::CfmmRouting(_)));
    }

    #[test]
    fn package_auction_is_shielded_certpackage() {
        // The all-or-none combinatorial WDP compiles to a certified-approximation
        // clearing (NOT a rejection): discrete curvature ⇒ not Dark ⇒ Shielded,
        // CertPackage. This is the better answer to the NP-hard boundary.
        let c = compile(&products::package_auction_clearing()).unwrap();
        assert_eq!(c.tier, Tier::Shielded);
        assert_eq!(c.cert, CertKind::CertPackage);
        assert!(matches!(c.program, ConvexProgram::PackageClearing(_)));
    }

    #[test]
    fn package_auction_claiming_dark_is_rejected() {
        let err = compile(&products::package_auction_claiming_dark()).unwrap_err();
        match err {
            TypeError::OverClaimsTier {
                claimed,
                honest,
                because,
            } => {
                assert_eq!(claimed, Tier::Dark);
                assert_eq!(honest, Tier::Shielded);
                assert!(matches!(*because, TypeError::CombinatorialObjective { .. }));
            }
            other => panic!("expected over-claim/combinatorial-objective, got {other:?}"),
        }
    }

    #[test]
    fn welfare_max_claiming_dark_is_rejected() {
        let err = compile(&products::welfare_max_claiming_dark()).unwrap_err();
        match err {
            TypeError::OverClaimsTier {
                claimed,
                honest,
                because,
            } => {
                assert_eq!(claimed, Tier::Dark);
                assert_eq!(honest, Tier::Shielded);
                assert!(matches!(*because, TypeError::EntropicObjective { .. }));
            }
            other => panic!("expected over-claim/entropic-objective, got {other:?}"),
        }
    }
}

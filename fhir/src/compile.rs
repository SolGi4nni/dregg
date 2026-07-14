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

use crate::ast::{EdgeSpec, FillType, MatrixData, OrderSide, OrderSpec, Product, ProductBody};
use crate::tier::Tier;
use crate::types::{
    CertKind, Cone, Curvature, IntegerFeature, MatrixFlag, MatrixRole, ProgramKind, ProgramType,
    TypeError, Visibility,
};

use fhegg_solver::clearing::{Order as EngineOrder, Side as EngineSide};
use fhegg_solver::pdhg::FlowLp;
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
    /// A state-price / superhedging LP (Price-Cert) — typed shape only in
    /// fhIR-0; the dedicated runner is the fhIR-1 lane.
    StatePriceLp {
        n_scenarios: usize,
        n_instruments: usize,
    },
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
    let _ = marks;
    let shape = ProgramType {
        kind: ProgramKind::StatePriceLp,
        curvature: Curvature::Affine, // max hᵀπ s.t. Hᵀπ = a — an LP
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
    Lowered {
        shape,
        program: ConvexProgram::StatePriceLp {
            n_scenarios: instruments.rows,
            n_instruments: instruments.cols,
        },
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
        // Small public scenario grid → Dark; the shape typechecks even though the
        // runner is the fhIR-1 lane.
        assert_eq!(c.tier, Tier::Dark);
    }
}

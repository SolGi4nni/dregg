//! The fhIR-0 example products — both polarities of the tier judgment.
//!
//! Three products that COMPILE to their `(program, tier, cert)` and RUN through
//! the engine, plus two REJECTIONS with precise reasons, plus a small-flow /
//! derivative pair that exercise the size boundary and the Price-Cert shape.
//! Each demonstrates the compiler reporting the right tier
//! (`DREGGFI-PRIVACY-TIERS.md` §3 mapping table).

use crate::ast::{EdgeSpec, MatrixData, OrderSpec, Product, ProductBody};
use crate::tier::Tier;

/// A diagonal-dominant PSD covariance (public structure for the test), n×n.
fn covariance(n: usize) -> Vec<f64> {
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
    cov
}

fn expected_returns(n: usize) -> Vec<f64> {
    (0..n).map(|i| 0.05 + 0.02 * i as f64).collect()
}

/// A directed-cycle circulation of `n` edges: `0→1→…→(n-1)→0`, unit weights and
/// caps. Well-posed (uniform circulation, optimum = min cap).
fn cycle_edges(n: usize) -> Vec<EdgeSpec> {
    (0..n)
        .map(|i| EdgeSpec {
            tail: i as u32,
            head: ((i + 1) % n) as u32,
            weight: 1.0,
            cap: 1.0,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The three compile-and-run products.
// ---------------------------------------------------------------------------

/// **Uniform-price call auction** — Tier 0 DARK, Aggregation certificate. A
/// two-sided book that genuinely crosses. The fhEgg base case: fold + one
/// crossing, `T=1`, FHE-tractable at this size.
pub fn uniform_price_clearing() -> Product {
    let orders = vec![
        OrderSpec::bid(100, 7),
        OrderSpec::bid(50, 6),
        OrderSpec::ask(80, 3),
        OrderSpec::ask(40, 4),
    ];
    Product::infer(
        "uniform-price-call-auction",
        ProductBody::UniformPrice { orders, k: 10 },
    )
}

/// **Cert-F flow-LP clearing at scale** — Tier 1 SHIELDED, CertF. A large
/// circulation (80 edges) exceeds the FHE Dark envelope, so its most-private
/// honest tier is Shielded — "matrices public, data encrypted; scale is the FHE
/// frontier" (`DREGGFI-PRIVACY-TIERS.md` §3).
pub fn flow_lp_clearing() -> Product {
    let n = 80;
    Product::infer(
        "circulation-clearing-at-scale",
        ProductBody::FlowClearing {
            nodes: n,
            edges: cycle_edges(n),
        },
    )
}

/// **Portfolio QP, public covariance** — Tier 1 SHIELDED, CertQp. Public `Σ`
/// but a convex-quadratic objective (PSD prox is outside the FHE v0 core), so
/// the honest tier is Shielded, mapping to CertQp/ADMM.
pub fn portfolio_qp_public() -> Product {
    let n = 6;
    Product::infer(
        "portfolio-markowitz-public-cov",
        ProductBody::Portfolio {
            cov: MatrixData::public(n, n, covariance(n)),
            mu: expected_returns(n),
            lambda: 5.0,
            w_max: 0.4,
        },
    )
}

// ---------------------------------------------------------------------------
// The two rejections.
// ---------------------------------------------------------------------------

/// **REJECTION — a private covariance claiming Tier 0.** The covariance is the
/// objective matrix `P`; a PRIVATE matrix breaks the FHE public-matvec, so the
/// product is NOT Dark-admissible. Claiming Dark over-claims privacy → rejected
/// with `PrivateMatrix`. Its honest tier is Shielded (the solver sees plaintext).
pub fn portfolio_qp_private_claiming_dark() -> Product {
    let n = 6;
    Product::claiming(
        "portfolio-private-cov-OVERCLAIM",
        ProductBody::Portfolio {
            cov: MatrixData::private(n, n, covariance(n)),
            mu: expected_returns(n),
            lambda: 5.0,
            w_max: 0.4,
        },
        Tier::Dark,
    )
}

/// **REJECTION — an all-or-none order claiming Tier 1.** All-or-none is an
/// integer/disjunctive constraint that breaks the continuous oblivious regime,
/// so the product is only Tier 2 Open. Claiming Shielded over-claims → rejected
/// with `IntegerFeature`.
pub fn all_or_none_claiming_shielded() -> Product {
    let orders = vec![
        OrderSpec::bid(100, 7).all_or_none(), // the integer feature
        OrderSpec::ask(80, 3),
        OrderSpec::ask(40, 4),
    ];
    Product::claiming(
        "all-or-none-auction-OVERCLAIM",
        ProductBody::UniformPrice { orders, k: 10 },
        Tier::Shielded,
    )
}

// ---------------------------------------------------------------------------
// Size-boundary + Price-Cert shape.
// ---------------------------------------------------------------------------

/// A SMALL circulation (6 edges) — inside the FHE Dark envelope, so its
/// most-private honest tier is Tier 0 DARK. The size boundary works both ways.
pub fn small_flow_clearing() -> Product {
    let n = 6;
    Product::infer(
        "circulation-clearing-small",
        ProductBody::FlowClearing {
            nodes: n,
            edges: cycle_edges(n),
        },
    )
}

/// A **Price-Cert derivative** — a state-price / superhedging LP over a small
/// PUBLIC scenario grid. Its shape type-checks (Dark, PriceCert); the dedicated
/// runner is the fhIR-1 lane.
pub fn derivative_price_cert() -> Product {
    // 3 scenarios × 2 calibrated instruments (public payoff grid H).
    let instruments = MatrixData::public(3, 2, vec![1.0, 0.0, 1.0, 0.5, 1.0, 1.0]);
    Product::infer(
        "european-call-price-cert",
        ProductBody::Derivative {
            instruments,
            marks: vec![1.0, 0.6],
            payoff: vec![0.0, 0.2, 0.8],
        },
    )
}

/// Every fhIR-0 example, in demo order.
pub fn all() -> Vec<Product> {
    vec![
        uniform_price_clearing(),
        small_flow_clearing(),
        flow_lp_clearing(),
        portfolio_qp_public(),
        derivative_price_cert(),
        portfolio_qp_private_claiming_dark(),
        all_or_none_claiming_shielded(),
    ]
}

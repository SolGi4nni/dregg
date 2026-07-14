//! The fhIR-0 example products — both polarities of the tier judgment.
//!
//! Three products that COMPILE to their `(program, tier, cert)` and RUN through
//! the engine, plus two REJECTIONS with precise reasons, plus a small-flow /
//! derivative pair that exercise the size boundary and the Price-Cert shape.
//! Each demonstrates the compiler reporting the right tier
//! (`DREGGFI-PRIVACY-TIERS.md` §3 mapping table).

use crate::ast::{BinomialSpec, EdgeSpec, MatrixData, OrderSpec, PoolSpec, Product, ProductBody};
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
/// PUBLIC scenario grid. An INCOMPLETE market (3 scenarios, 2 instruments): a
/// bond `[1,1,1]`@1 and an asset `[0,0.5,1]`@0.6, pricing a call-like payoff
/// `h=[0,0.2,0.8]`. Many consistent state prices exist (a genuine arbitrage-free
/// interval); the runner returns the upper price `0.48` with a tight superhedge
/// `y=(0,0.8)` (gap 0). Compiles Dark/PriceCert and now RUNS end-to-end.
pub fn derivative_price_cert() -> Product {
    // 3 scenarios × 2 calibrated instruments (public payoff grid H, scenario-major).
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

/// An **American put** priced by the Snell-envelope LP over a PUBLIC recombining
/// binomial tree — the early-exercise member of the Price-Cert family. 16 steps
/// ⇒ 153 tree nodes, which EXCEEDS the Dark LP envelope (64), so the honest tier
/// is Shielded: the American "cliff is tree size, not solver class" (R2.1) —
/// exactly the size boundary biting. Optimal stopping is an LP, not mixed-integer;
/// the runner computes the tight envelope by backward induction and certifies it.
/// The SAME Price-Cert discipline as the European.
pub fn american_put_price_cert() -> Product {
    Product::infer(
        "american-put-price-cert",
        ProductBody::American {
            spec: BinomialSpec {
                s0: 100.0,
                strike: 100.0,
                rate: 0.05,
                vol: 0.2,
                expiry: 1.0,
                steps: 16,
                is_put: true,
            },
        },
    )
}

/// **REJECTION (economic) — an ARBITRAGE derivative market.** Two instruments
/// with IDENTICAL payoff `[1,1]` marked at DIFFERENT prices (1 vs 0.5): a
/// textbook arbitrage. No consistent state price `π ≥ 0` with `Hπ = a` exists,
/// so the runner produces NO certificate and REJECTS the market
/// (`NoArbitrageFreePrice`) — the runner's honest negative polarity, distinct
/// from the type-level over-claim rejections. It still type-checks (the SHAPE is
/// a valid state-price LP); the RUN detects the arbitrage.
pub fn arbitrage_derivative_rejected() -> Product {
    // scenario-major 2×2: both instruments pay [1,1]; only the marks differ.
    let instruments = MatrixData::public(2, 2, vec![1.0, 1.0, 1.0, 1.0]);
    Product::infer(
        "arbitrage-derivative-REJECTED",
        ProductBody::Derivative {
            instruments,
            marks: vec![1.0, 0.5],
            payoff: vec![1.0, 0.0],
        },
    )
}

// ---------------------------------------------------------------------------
// The mechanism FAMILY — three more real clearing mechanisms on the one engine.
// ---------------------------------------------------------------------------

/// **Discriminatory / pay-as-bid call auction** — Tier 0 DARK, CertF. The SAME
/// book form as the uniform-price auction, cleared differently: the efficient
/// fill is a gains-from-trade flow-LP (a linear Cert-F winner-determination) and
/// each winner settles at its OWN limit. Small book ⇒ inside the FHE envelope ⇒
/// Dark, with the linear Cert-F certificate.
pub fn discriminatory_clearing() -> Product {
    let orders = vec![
        OrderSpec::bid(100, 8),
        OrderSpec::bid(60, 7),
        OrderSpec::ask(90, 2),
        OrderSpec::ask(50, 3),
    ];
    Product::infer(
        "discriminatory-pay-as-bid-auction",
        ProductBody::Discriminatory { orders, k: 10 },
    )
}

/// **Welfare-max / Fisher-market equilibrium** — Tier 1 SHIELDED, CertEq. The
/// marquee: the Eisenberg–Gale convex program `max Σ bᵢ log Uᵢ s.t. supply`, the
/// general competitive clearing. The `log` objective is concave (entropic prox),
/// outside the FHE v0 affine core, so the honest tier is Shielded — a bilinear
/// equilibrium certificate `(x, prices)`. Uniform-price is the linear-utility,
/// single-good special case of THIS.
pub fn welfare_max_fisher() -> Product {
    // 4 buyers, 3 goods; buyer i favours good (i mod 3) but values all goods.
    let n = 4;
    let g = 3;
    let mut util = vec![0.0f64; n * g];
    for i in 0..n {
        for j in 0..g {
            let base = 1.0 + ((i + 2 * j) % 5) as f64 * 0.5;
            let favour = if j == i % g { 3.0 } else { 0.0 };
            util[i * g + j] = base + favour;
        }
    }
    Product::infer(
        "welfare-max-fisher-equilibrium",
        ProductBody::WelfareMax {
            n_buyers: n,
            n_goods: g,
            budgets: (0..n).map(|i| 1.0 + (i % 3) as f64).collect(),
            supplies: vec![1.0; g],
            util: MatrixData::public(n, g, util),
        },
    )
}

/// **CFMM optimal routing** — Tier 1 SHIELDED, CertRoute. Split a fixed private
/// input across PUBLIC constant-product pool curves to maximise output. The
/// rational-concave output is a nonlinear objective (water-filling on the
/// marginal price), so the honest tier is Shielded — a KKT routing certificate
/// `(δ, λ)`. Public pool curves, private routing.
pub fn cfmm_routing() -> Product {
    let pools = (0..4)
        .map(|i| PoolSpec {
            reserve_in: 1000.0 * (1.0 + i as f64 * 0.5),
            reserve_out: 1000.0 * (1.0 + ((i + 2) % 4) as f64 * 0.4),
            fee: 0.997,
        })
        .collect();
    Product::infer(
        "cfmm-optimal-routing",
        ProductBody::CfmmRouting {
            pools,
            budget: 500.0,
        },
    )
}

/// **REJECTION — welfare-max claiming Tier 0.** The Eisenberg–Gale `log` objective
/// is concave-nonlinear (entropic prox = exp/log), outside the FHE v0 affine
/// core. Claiming Dark over-claims privacy → rejected with `EntropicObjective`.
/// Its honest tier is Shielded (the STARK carries the mirror-descent circuit).
pub fn welfare_max_claiming_dark() -> Product {
    let base = welfare_max_fisher();
    Product::claiming("welfare-max-OVERCLAIM", base.body, Tier::Dark)
}

/// Every fhIR-0 example, in demo order.
pub fn all() -> Vec<Product> {
    vec![
        uniform_price_clearing(),
        small_flow_clearing(),
        flow_lp_clearing(),
        portfolio_qp_public(),
        derivative_price_cert(),
        american_put_price_cert(),
        arbitrage_derivative_rejected(),
        discriminatory_clearing(),
        welfare_max_fisher(),
        cfmm_routing(),
        portfolio_qp_private_claiming_dark(),
        all_or_none_claiming_shielded(),
        welfare_max_claiming_dark(),
    ]
}

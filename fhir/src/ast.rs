//! The fhIR-0 product/order AST — the front-end the compiler type-checks.
//!
//! A [`Product`] is a name, a body (one of the fhIR-0 product forms), and an
//! OPTIONAL tier *claim*. The claim is how a product author states the privacy
//! they promise: `None` means "infer and report the most-private honest tier";
//! `Some(t)` means "I promise tier `t`", and the compiler REJECTS the product if
//! the math does not deliver at least that privacy (`compile::compile`). This is
//! the mechanized honest-labeling discipline of `DREGGFI-PRIVACY-TIERS.md` §2/§3
//! — the type system, not marketing, decides the privacy label.

use crate::types::Visibility;

/// A typed product/order. The unit the compiler consumes.
#[derive(Clone, Debug)]
pub struct Product {
    pub name: String,
    pub body: ProductBody,
    /// The tier the author CLAIMS to run at. `None` = infer (never over-promise);
    /// `Some(t)` = promise `t`, rejected if unachievable.
    pub claim: Option<crate::tier::Tier>,
}

impl Product {
    /// A product with no claim — "report the most-private honest tier".
    pub fn infer(name: impl Into<String>, body: ProductBody) -> Self {
        Product {
            name: name.into(),
            body,
            claim: None,
        }
    }

    /// A product that CLAIMS a tier — rejected if the math delivers less privacy.
    pub fn claiming(name: impl Into<String>, body: ProductBody, claim: crate::tier::Tier) -> Self {
        Product {
            name: name.into(),
            body,
            claim: Some(claim),
        }
    }
}

/// The fhIR-0 product forms. Each maps to a convex program + a certificate.
#[derive(Clone, Debug)]
pub enum ProductBody {
    /// A uniform-price call auction over a PUBLIC `k`-level price grid — the
    /// fhEgg base case (fold + one crossing, `T=1`). The book topology (the price
    /// grid) is public; only the amounts are private.
    UniformPrice { orders: Vec<OrderSpec>, k: usize },

    /// A volume-max circulation clearing over a PUBLIC trade graph — the Cert-F
    /// flow-LP `max wᵀf s.t. Af=0, 0≤f≤c`. The incidence (topology) is always
    /// public; only the flow amounts are private.
    FlowClearing { nodes: usize, edges: Vec<EdgeSpec> },

    /// A mean-variance portfolio QP `min ½xᵀΣx − λμᵀx s.t. 1ᵀx=1, 0≤x≤w_max`.
    /// `cov` carries the visibility of the covariance MATRIX — the cheap-regime
    /// boundary. Public-`Σ` ⇒ maps to CertQp at Tier 1; private-`Σ` ⇒ off the
    /// Tier-0 public-matrix line (`DREGGFI-PRIVACY-TIERS.md` §3).
    Portfolio {
        cov: MatrixData,
        mu: Vec<f64>,
        lambda: f64,
        w_max: f64,
    },

    /// A state-price derivative pricing program (Price-Cert): the no-arbitrage
    /// superhedging LP over a PUBLIC scenario grid. Typed in fhIR-0; the runner
    /// is the fhIR-1 lane.
    Derivative {
        /// Calibrated-instrument payoffs `H` (M scenarios × J instruments),
        /// public scenario topology.
        instruments: MatrixData,
        /// Observed marks `a` (J).
        marks: Vec<f64>,
        /// The new product's scenario payoff `h` (M).
        payoff: Vec<f64>,
    },

    /// An **American / Bermudan** option priced by the Snell-envelope LP over a
    /// PUBLIC recombining binomial tree — the early-exercise member of the
    /// Price-Cert family (`PriceCert.lean` § Snell). Optimal stopping is an LP,
    /// NOT mixed-integer; the tree topology is public.
    American { spec: BinomialSpec },

    /// A **discriminatory / pay-as-bid** call auction over a PUBLIC `k`-level price
    /// grid — a DIFFERENT clearing on the same book form as [`ProductBody::
    /// UniformPrice`]. The efficient fill is a gains-from-trade flow-LP (linear
    /// Cert-F winner-determination); each winner then settles at its OWN limit.
    Discriminatory { orders: Vec<OrderSpec>, k: usize },

    /// A **welfare-max / Fisher-market** clearing — the Eisenberg–Gale convex
    /// program `max Σ bᵢ log Uᵢ s.t. supply`, the general competitive equilibrium
    /// of which uniform-price is the linear-utility special case. The utility
    /// matrix visibility is the type-level fact (public ⇒ everyone sees the
    /// valuations; private ⇒ the solver sees plaintext). The `log` objective is
    /// concave, so the honest tier is Shielded, not the FHE-affine Dark core.
    WelfareMax {
        n_buyers: usize,
        n_goods: usize,
        budgets: Vec<f64>,
        supplies: Vec<f64>,
        /// Utilities `uᵢⱼ`, row-major `n_buyers × n_goods`.
        util: MatrixData,
    },

    /// A **CFMM optimal-routing** clearing — split a fixed private input `budget`
    /// across PUBLIC constant-product pool curves to maximise output
    /// (`max Σ gᵢ(δᵢ) s.t. Σδ≤Δ`). The pool curves are public; the routing is
    /// private. The rational-concave output is a nonlinear objective ⇒ Shielded.
    CfmmRouting { pools: Vec<PoolSpec>, budget: f64 },

    /// A **package / all-or-none combinatorial auction** — the winner-determination
    /// `max Σ vᵢxᵢ s.t. Σ dᵢⱼxᵢ ≤ sⱼ, xᵢ∈{0,1}` over public item supply. Each bid
    /// is a public bundle (`demand`) at a private `value`, filled FULLY or NOT AT
    /// ALL — indivisibility that is NP-hard to optimize exactly. It compiles to a
    /// CERTIFIED-APPROXIMATION clearing (a feasible integral packing + a Lagrangian
    /// dual bound), NOT a rejection. Honest tier: Shielded (the exact optimum stays
    /// NP-hard; the certificate proves feasibility + a near-optimality ratio).
    PackageAuction {
        n_items: usize,
        /// Public supply per item `sⱼ`.
        supply: Vec<f64>,
        bids: Vec<PackageBidSpec>,
    },
}

/// One all-or-none package bid: a private value for a PUBLIC bundle
/// ([`ProductBody::PackageAuction`]). The bundle `demand` (which items, how many
/// units) is public structure; only the `value` is a private amount.
#[derive(Clone, Debug)]
pub struct PackageBidSpec {
    /// The bid value for the WHOLE bundle (private amount).
    pub value: f64,
    /// Units of each item the package demands, length `n_items` (public).
    pub demand: Vec<f64>,
}

impl PackageBidSpec {
    pub fn new(value: f64, demand: Vec<f64>) -> Self {
        PackageBidSpec { value, demand }
    }
}

/// A recombining CRR binomial American/Bermudan option — the PUBLIC scenario
/// tree the Snell-envelope LP prices against ([`ProductBody::American`]). All
/// fields are public model parameters; the state prices / stopping policy stay
/// hidden (only the certified value opens).
#[derive(Clone, Copy, Debug)]
pub struct BinomialSpec {
    /// Spot price `S₀`.
    pub s0: f64,
    /// Strike `K`.
    pub strike: f64,
    /// Risk-free rate `r` (per annum, continuous).
    pub rate: f64,
    /// Volatility `σ` (per annum).
    pub vol: f64,
    /// Expiry `T` in years.
    pub expiry: f64,
    /// Number of binomial steps (tree depth) — the state-size knob.
    pub steps: usize,
    /// `true` = put `(K−S)₊`; `false` = call `(S−K)₊`.
    pub is_put: bool,
}

/// One constant-product pool for a [`ProductBody::CfmmRouting`] — a PUBLIC curve.
#[derive(Clone, Copy, Debug)]
pub struct PoolSpec {
    /// Reserve of the input token `Rᵢ`.
    pub reserve_in: f64,
    /// Reserve of the output token `Qᵢ`.
    pub reserve_out: f64,
    /// Fee factor `γ ∈ (0,1]`.
    pub fee: f64,
}

/// One limit order in a uniform-price auction.
#[derive(Clone, Copy, Debug)]
pub struct OrderSpec {
    pub side: OrderSide,
    /// Quantity — PRIVATE amount (exact integer, no rounding).
    pub qty: u64,
    /// Price-LEVEL index in `[0, k)` — references the public price grid.
    pub limit: u32,
    /// The fill discipline. `Continuous` stays in the cheap regime; `AllOrNone`
    /// is an integer constraint that forces Tier 2 Open (`R2.2`).
    pub fill: FillType,
}

impl OrderSpec {
    pub fn bid(qty: u64, limit: u32) -> Self {
        Self {
            side: OrderSide::Bid,
            qty,
            limit,
            fill: FillType::Continuous,
        }
    }
    pub fn ask(qty: u64, limit: u32) -> Self {
        Self {
            side: OrderSide::Ask,
            qty,
            limit,
            fill: FillType::Continuous,
        }
    }
    /// Mark this order all-or-none (an integer feature).
    pub fn all_or_none(mut self) -> Self {
        self.fill = FillType::AllOrNone;
        self
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OrderSide {
    Bid,
    Ask,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FillType {
    /// Continuous partial fill — the cheap convex regime.
    Continuous,
    /// All-or-none — an integer/disjunctive constraint (`R2.2`).
    AllOrNone,
}

/// One directed edge of a circulation trade graph.
#[derive(Clone, Copy, Debug)]
pub struct EdgeSpec {
    pub tail: u32,
    pub head: u32,
    /// Objective weight (`wᵀf` maximized) — public.
    pub weight: f64,
    /// Capacity (`0 ≤ f ≤ c`) — public bound; the flow amount is private.
    pub cap: f64,
}

/// A dense matrix with its visibility flag — the type-level fact the tier
/// judgment reads. `rows`/`cols` describe the shape; `data` is row-major.
#[derive(Clone, Debug)]
pub struct MatrixData {
    pub rows: usize,
    pub cols: usize,
    pub data: Vec<f64>,
    pub visibility: Visibility,
}

impl MatrixData {
    pub fn public(rows: usize, cols: usize, data: Vec<f64>) -> Self {
        MatrixData {
            rows,
            cols,
            data,
            visibility: Visibility::Public,
        }
    }
    pub fn private(rows: usize, cols: usize, data: Vec<f64>) -> Self {
        MatrixData {
            rows,
            cols,
            data,
            visibility: Visibility::Private,
        }
    }
}

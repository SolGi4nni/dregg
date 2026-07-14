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

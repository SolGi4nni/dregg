//! The DrEX order book → trade-circulation LP mapping, and the ACCURACY BUDGET a
//! Cert-F certificate is claimed against.
//!
//! `fhegg_clear` used to carry both of these inline: the mapping as a loop in `main`,
//! and the budget as the literal `let epsilon = 0.5f64;`. Both are now here, for two
//! different reasons.
//!
//! ## The mapping, because the prover must map the book the SAME way
//!
//! A Cert-F certificate is a certificate *of a public program*. If the clearing CLI and
//! the STARK bridge each derive that program from the order book by their own copy of the
//! mapping, the two copies are free to drift and the certificate stops being about the
//! book. [`map_book`] is the single derivation both sides call.
//!
//! ## The budget, because `0.5` was not a tolerance of anything
//!
//! `gap ≤ ε` is the ε-optimality clause of Cert-F. A literal `0.5` is dimensionless with
//! respect to the book: on a batch quoted in millions it is unreachably tight, on a batch
//! of three unit orders it is so loose that a certificate claims almost nothing. Worse, it
//! is unrelated to the budget the *prover* will grant, so the CLI could report
//! `valid: true` for a solve the STARK refuses — a self-assertion.
//!
//! [`AccuracyBudget`] replaces the literal with a budget that is either
//!
//!   * **derived** from the program itself — a fraction of `Σ_e w_e·c_e`, the program's own
//!     upper bound on `wᵀf`, so the budget scales with the batch; or
//!   * **declared** as the prescriptive integer ε of a registered Lean-emitted Cert-F
//!     program at its fixed-point scale, expressed back in solver units.
//!
//! The second form is the one that makes the STARK wrap reachable: the certificate is then
//! claimed against exactly the budget the registered program grants, not against a number
//! this crate invented. Which registration a live book resolves to is decided downstream by
//! `dregg_circuit_prove::cert_f_air` against the Lean-emitted registry — this crate does not
//! and must not decide admissibility.

use serde::{Deserialize, Serialize};

use crate::pdhg::FlowLp;

/// One revealed order as posted by the web app (the DrEX wire shape).
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct BookOrder {
    pub trader: String,
    #[serde(rename = "offerAsset")]
    pub offer_asset: String,
    #[serde(rename = "offerAmount")]
    pub offer_amount: u64,
    #[serde(rename = "wantAsset")]
    pub want_asset: String,
    #[serde(rename = "wantMin")]
    pub want_min: u64,
    #[serde(default)]
    pub priority: u64,
}

/// The public trade-circulation program a batch maps to: the asset symbols in node order
/// plus the flow LP whose edge `e` is order `e`.
#[derive(Clone, Debug)]
pub struct BookProgram {
    /// Asset symbol per node index, in first-seen order.
    pub assets: Vec<String>,
    /// `max wᵀf s.t. Af = 0, 0 ≤ f ≤ c` — nodes are assets, edges are orders.
    pub lp: FlowLp,
}

/// The objective weight an order contributes. Priority `0` means "unset", which must not
/// zero the order out of the objective — an unprioritised order still wants to clear.
pub fn order_weight(priority: u64) -> f64 {
    if priority == 0 {
        1.0
    } else {
        priority as f64
    }
}

/// The capacity an order contributes. A zero-amount order would be a zero-capacity edge,
/// which is a degenerate column; it rides at capacity 1 exactly as the CLI has always done.
pub fn order_capacity(offer_amount: u64) -> f64 {
    offer_amount.max(1) as f64
}

/// **The single order-book → LP derivation.**
///
/// Nodes are assets (indexed in first-seen order over each order's `(want, offer)` pair),
/// and each order is one capacitated weighted edge. An order OFFERS `offerAsset` to OBTAIN
/// `wantAsset`: value releases at the want node and lands at the offer node as the ring
/// circulates, so the edge runs `wantAsset → offerAsset`. Conservation `Af = 0` at each
/// asset node is exactly DrEX per-asset conservation (what flows out as offers equals what
/// flows in as wants).
pub fn map_book(orders: &[BookOrder]) -> BookProgram {
    let mut assets: Vec<String> = Vec::new();
    let idx_of = |sym: &str, assets: &mut Vec<String>| -> u32 {
        if let Some(i) = assets.iter().position(|a| a == sym) {
            i as u32
        } else {
            let i = assets.len() as u32;
            assets.push(sym.to_string());
            i
        }
    };

    let mut edges: Vec<(u32, u32)> = Vec::with_capacity(orders.len());
    let mut w: Vec<f64> = Vec::with_capacity(orders.len());
    let mut c: Vec<f64> = Vec::with_capacity(orders.len());
    for o in orders {
        let tail = idx_of(&o.want_asset, &mut assets);
        let head = idx_of(&o.offer_asset, &mut assets);
        edges.push((tail, head));
        c.push(order_capacity(o.offer_amount));
        w.push(order_weight(o.priority));
    }

    let n_nodes = assets.len();
    BookProgram {
        assets,
        lp: FlowLp {
            n_nodes,
            edges,
            w,
            c,
        },
    }
}

/// The program's own upper bound on the achievable objective: `Σ_e w_e·c_e ≥ wᵀf` for every
/// box-feasible `f`. This is the natural scale of a circulation program — it is computed
/// from the public `(w, c)` alone, so a budget derived from it reveals nothing about the
/// solution and moves with the batch.
pub fn weighted_capacity_bound(lp: &FlowLp) -> f64 {
    lp.w.iter()
        .zip(&lp.c)
        .map(|(w, c)| w.max(0.0) * c.max(0.0))
        .sum()
}

/// The optimality tolerance a Cert-F certificate is claimed against — derived from the
/// program or declared by a registration, never a literal.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AccuracyBudget {
    /// The prescriptive integer ε of a REGISTERED Lean-emitted Cert-F program, at that
    /// registration's fixed-point `scale`, expressed back in solver (f64) units.
    ///
    /// The bridge to the integer STARK scales `w` and `f` by `scale` each, and `c` and `s`
    /// likewise, so every term of `cᵀs − wᵀf` picks up `scale²`. An integer budget `ε_int`
    /// is therefore the solver-unit budget `ε_int / scale²`.
    Registered { scale: i64, integer_epsilon: i64 },
    /// `relative · Σ_e w_e·c_e`. A certificate claimed against this budget is a real
    /// ε-optimality statement about THIS program at THIS batch size, but it carries no
    /// registration: whether the fixed-point image is a Lean-emitted registered program is
    /// decided downstream, and an unregistered program is refused by the prover.
    RelativeToWeightedCapacity { relative: f64 },
}

impl AccuracyBudget {
    /// The default relative budget: one part in 128 of the program's own weighted-capacity
    /// bound. Named, not tuned — it is the coarsest budget under which the deployed batches
    /// still certify, and it is asserted against a real solve in this module's tests rather
    /// than assumed.
    pub const DEFAULT_RELATIVE: f64 = 1.0 / 128.0;

    /// The default budget for a batch with no declared registration.
    pub fn derived_default() -> Self {
        Self::RelativeToWeightedCapacity {
            relative: Self::DEFAULT_RELATIVE,
        }
    }

    /// The solver-unit tolerance this budget grants for `lp`.
    pub fn epsilon_for(&self, lp: &FlowLp) -> f64 {
        match *self {
            Self::Registered {
                scale,
                integer_epsilon,
            } => {
                let s = scale.max(1) as f64;
                integer_epsilon.max(0) as f64 / (s * s)
            }
            Self::RelativeToWeightedCapacity { relative } => {
                relative.max(0.0) * weighted_capacity_bound(lp)
            }
        }
    }

    /// How this budget was obtained, for the CLI's output. A relying party reading a
    /// certificate must be able to see whether `ε` came from a registration or from a
    /// batch-relative derivation.
    pub fn derivation(&self, lp: &FlowLp) -> String {
        match *self {
            Self::Registered {
                scale,
                integer_epsilon,
            } => format!(
                "declared: registered Lean-emitted program epsilon {integer_epsilon} at fixed-point scale {scale} \
                 => {integer_epsilon}/{scale}^2 in solver units"
            ),
            Self::RelativeToWeightedCapacity { relative } => format!(
                "derived: {relative} * sum_e w_e*c_e = {relative} * {bound}",
                bound = weighted_capacity_bound(lp)
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cert::CertF;
    use crate::pdhg::{restore_feasibility, solve_cpu};

    fn order(trader: &str, offer: &str, amount: u64, want: &str, priority: u64) -> BookOrder {
        BookOrder {
            trader: trader.to_string(),
            offer_asset: offer.to_string(),
            offer_amount: amount,
            want_asset: want.to_string(),
            want_min: 1,
            priority,
        }
    }

    /// The DrEX demo batch: a 3-asset ring plus one bilateral leg. This is the exact book
    /// whose ×100 fixed-point image is the registered Lean-emitted `market4Prog`, so the
    /// mapping pinned here is the one the STARK registry resolves against.
    fn demo_batch() -> Vec<BookOrder> {
        vec![
            order("alice", "B", 5, "A", 1),
            order("bob", "C", 5, "B", 1),
            order("carol", "A", 5, "C", 1),
            order("dave", "A", 3, "B", 3),
        ]
    }

    #[test]
    fn demo_batch_maps_to_the_registered_market4_shape() {
        let program = map_book(&demo_batch());
        assert_eq!(program.assets, vec!["A", "B", "C"]);
        assert_eq!(program.lp.n_nodes, 3);
        assert_eq!(program.lp.edges, vec![(0, 1), (1, 2), (2, 0), (1, 0)]);
        assert_eq!(program.lp.w, vec![1.0, 1.0, 1.0, 3.0]);
        assert_eq!(program.lp.c, vec![5.0, 5.0, 5.0, 3.0]);
    }

    #[test]
    fn weighted_capacity_bounds_the_objective() {
        let program = map_book(&demo_batch());
        let bound = weighted_capacity_bound(&program.lp);
        assert_eq!(bound, 24.0, "1*5 + 1*5 + 1*5 + 3*3");
        let res = solve_cpu(&program.lp, 4000);
        let (f, _) = restore_feasibility(&program.lp, res.f.clone());
        let objective: f64 = program.lp.w.iter().zip(&f).map(|(w, f)| w * f).sum();
        assert!(
            objective <= bound + 1e-9,
            "the derived budget's base must really bound the objective: {objective} > {bound}"
        );
    }

    /// TEST THE STATED LIMIT: the default derived budget must actually admit a real solve of
    /// a real batch. If this goes red the answer is a tighter solve, never a looser budget.
    #[test]
    fn derived_default_budget_admits_a_real_solve() {
        let program = map_book(&demo_batch());
        let budget = AccuracyBudget::derived_default();
        let epsilon = budget.epsilon_for(&program.lp);
        let res = solve_cpu(&program.lp, 4000);
        let (f, _) = restore_feasibility(&program.lp, res.f.clone());
        let cert = CertF::from_solution(&program.lp, &f, &res.y, epsilon);
        let report = cert.check_strict();
        assert!(
            report.valid,
            "the DERIVED budget {epsilon} must admit the real solve (achieved gap {}): {report:?}",
            report.gap
        );
        // ...and the budget must still be a real accuracy CLAIM, not a rubber stamp: at
        // most ~2% of the cleared volume. A budget that admits everything certifies nothing.
        let objective: f64 = program.lp.w.iter().zip(&f).map(|(w, f)| w * f).sum();
        assert!(
            epsilon <= 0.02 * objective,
            "the derived budget {epsilon} must be a real bound on the cleared volume {objective}"
        );
    }

    /// The registered budget is the integer epsilon divided by scale squared: the bridge
    /// scales both factors of every product in `cᵀs − wᵀf`.
    #[test]
    fn registered_budget_is_the_integer_epsilon_in_solver_units() {
        let program = map_book(&demo_batch());
        let budget = AccuracyBudget::Registered {
            scale: 100,
            integer_epsilon: 2000,
        };
        assert_eq!(budget.epsilon_for(&program.lp), 0.2);
    }

    /// A batch quoted a thousand times larger gets a thousand times the budget: the
    /// derivation moves with the book, which is exactly what the literal could not do.
    #[test]
    fn derived_budget_scales_with_the_batch() {
        let small = map_book(&demo_batch());
        let large = map_book(
            &demo_batch()
                .into_iter()
                .map(|mut o| {
                    o.offer_amount *= 1000;
                    o
                })
                .collect::<Vec<_>>(),
        );
        let budget = AccuracyBudget::derived_default();
        let small_eps = budget.epsilon_for(&small.lp);
        let large_eps = budget.epsilon_for(&large.lp);
        assert!(
            (large_eps - 1000.0 * small_eps).abs() < 1e-9,
            "{large_eps} should be 1000x {small_eps}"
        );
    }

    #[test]
    fn unset_priority_still_carries_weight() {
        assert_eq!(order_weight(0), 1.0);
        assert_eq!(order_weight(3), 3.0);
        assert_eq!(order_capacity(0), 1.0);
        assert_eq!(order_capacity(7), 7.0);
    }
}

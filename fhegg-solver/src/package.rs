//! Package / all-or-none combinatorial clearing — CERTIFIED APPROXIMATION.
//!
//! The verify-not-find answer to the NP-hard boundary. Uniform-price
//! ([`crate::clearing`]) and the circulation flow-LP ([`crate::pdhg`]) clear the
//! *continuous* (`[0,1]` divisible) regime; this module clears the INDIVISIBLE
//! one — **all-or-none package bids**, where each bid is a bundle at a price that
//! must be filled FULLY or NOT AT ALL (`x ∈ {0,1}`, never relaxed to a fraction).
//!
//! ## The winner-determination problem (WDP) — the NP-hard object
//!
//! `n` package bids over `m` items with public supply `s ∈ ℝ_{≥0}^m`. Bid `i`
//! demands a bundle `d_i ∈ ℝ_{≥0}^m` (units of each item) at a private value
//! `v_i`. The welfare-maximising clearing is the multi-dimensional 0/1 knapsack /
//! weighted set-packing
//!
//! ```text
//!   maximize   Σ_i v_i x_i
//!   subject to Σ_i d_ij x_i ≤ s_j     ∀ item j   (supply / capacity)
//!              x_i ∈ {0, 1}                       (ALL-OR-NONE — indivisible)
//! ```
//!
//! which is NP-hard. dregg does NOT relax the `{0,1}` to `[0,1]` — that would
//! change the product (a fractional fill of an all-or-none bid is meaningless).
//! The exact optimum stays NP-hard; what we ship is a FEASIBLE integral
//! allocation plus a certificate of a **provable near-optimality bound**.
//!
//! ## The certificate — feasibility + a dual upper bound (verify-not-find)
//!
//! The heart is exactly [`crate::cert::CertF`]'s move: WEAK DUALITY bounds the
//! optimum, and the bound reads only a feasible witness — never the solver's
//! search. Give each item a price `y_j ≥ 0` and set the per-bid slack
//! `u_i = (v_i − d_i·y)₊`. Then for EVERY integral-feasible `x`
//! (`Σ_i d_ij x_i ≤ s_j`, `x_i ∈ {0,1}`):
//!
//! ```text
//!   W(x) = Σ_i v_i x_i
//!        = Σ_i (v_i − d_i·y) x_i + Σ_i (d_i·y) x_i
//!        ≤ Σ_i (v_i − d_i·y)₊ x_i + Σ_j y_j (Σ_i d_ij x_i)   [x_i∈{0,1} ⇒ (v_i−d_i·y)x_i ≤ (·)₊]
//!        ≤ Σ_i u_i + Σ_j y_j s_j                              [x_i≤1, u_i≥0; capacity, y_j≥0]
//!        = UB(y).
//! ```
//!
//! So `UB(y) = Σ_j s_j y_j + Σ_i u_i` is a VALID UPPER BOUND on the integral
//! optimum `W*` — for ANY `y ≥ 0`, independent of how `y` was found (it is the LP
//! dual / Lagrangian bound; the inner 0/1 maximiser is separable, so the
//! Lagrangian bound equals the LP-relaxation bound). The achieved welfare `W` of
//! the emitted integral `x` then satisfies `W ≤ W* ≤ UB(y)`, giving the
//! **certified ratio** `α = W / UB(y) ∈ (0,1]`: the emitted clearing is provably
//! within a factor `α` of optimal —
//!
//! ```text
//!   W ≥ α · UB(y) ≥ α · W*      (achieved welfare ≥ α × the true optimum).
//! ```
//!
//! [`CertPackage::check`] recomputes `u`, `UB`, and `W` from the PUBLIC program +
//! the witness `(x, y)` and validates: `x` integral, capacity respected, `y ≥ 0`,
//! and the weak-duality bound `W ≤ UB`. Tamper any of these — a package
//! half-filled (`x_i = ½`), an item over supply, a negative price — and the check
//! REFUSES.
//!
//! ## Honest scope (the approximation, named)
//!
//! * **Feasibility is ALWAYS proven** — the emitted `x` is a genuine integral
//!   packing (indivisibility preserved), checked from scratch.
//! * **The bound `UB(y)` is ALWAYS valid** (weak duality) — but its TIGHTNESS,
//!   and hence the ratio `α`, depends on the instance and on the quality of the
//!   dual `y` the untrusted search found. On easy instances `α ≈ 1`; adversarial
//!   set-packing instances have a real LP integrality gap and a hard rounding
//!   step, so `α` can be well below 1. The certificate never claims `α = 1`
//!   (exact optimum) — it reports the honest, checked `α`.
//! * The search here is a subgradient descent on the item prices `y` (to tighten
//!   `UB`) plus a multi-ordering greedy rounding (to raise `W`). Both are the
//!   UNTRUSTED half; only the certificate decides.

use serde::Serialize;

/// One all-or-none package bid: a private value for a public bundle.
#[derive(Clone, Debug, Serialize)]
pub struct PackageBid {
    /// The bid value `v_i` for the WHOLE bundle (private amount).
    pub value: f64,
    /// The bundle `d_i` — units of each item the package demands (length `m`,
    /// the public bundle structure; `0` = item not in the bundle).
    pub demand: Vec<f64>,
}

impl PackageBid {
    pub fn new(value: f64, demand: Vec<f64>) -> Self {
        PackageBid { value, demand }
    }
    /// `d_i · y` — the bundle's cost at item prices `y`.
    fn cost(&self, y: &[f64]) -> f64 {
        self.demand.iter().zip(y).map(|(d, p)| d * p).sum()
    }
}

/// A package (combinatorial) auction: public supply + all-or-none bids.
#[derive(Clone, Debug)]
pub struct PackageAuction {
    /// Number of items `m`.
    pub n_items: usize,
    /// Public supply per item `s_j` (length `m`).
    pub supply: Vec<f64>,
    /// The all-or-none bids.
    pub bids: Vec<PackageBid>,
}

impl PackageAuction {
    pub fn n_bids(&self) -> usize {
        self.bids.len()
    }
}

/// The integral clearing: the accept/reject decisions + the achieved welfare.
#[derive(Clone, Debug, Serialize)]
pub struct PackageClearing {
    /// The all-or-none decisions `x_i ∈ {0,1}` (stored `f64` for certificate
    /// uniformity; the integrality is CHECKED, never assumed).
    pub accept: Vec<f64>,
    /// Achieved welfare `W = Σ v_i x_i`.
    pub welfare: f64,
    /// Item usage `Σ_i d_ij x_i` per item (≤ supply by construction).
    pub item_usage: Vec<f64>,
    /// The dual item prices `y ≥ 0` the certificate's bound rides on.
    pub prices: Vec<f64>,
    /// The certified upper bound `UB(y)` on the integral optimum.
    pub upper_bound: f64,
    /// The certified near-optimality ratio `α = W / UB ∈ (0,1]`.
    pub ratio: f64,
}

/// The package-clearing certificate: public program + integral primal `x` + dual
/// prices `y`. The all-or-none analogue of [`crate::cert::CertF`] — a linear
/// (weak-duality) certificate of feasibility + a near-optimality bound.
#[derive(Clone, Debug, Serialize)]
pub struct CertPackage {
    /// Number of items `m`.
    pub n_items: usize,
    /// Public supply `s` (length `m`).
    pub supply: Vec<f64>,
    /// Public bid values `v` (length `n`). (The values are the private amounts;
    /// they are public IN the certificate — the buyer checks the welfare bound.)
    pub values: Vec<f64>,
    /// Public bundles `d`, row-major `n × m`.
    pub demands: Vec<f64>,
    /// Primal witness — the integral accept decisions `x` (length `n`).
    pub accept: Vec<f64>,
    /// Dual witness — the item prices `y ≥ 0` (length `m`).
    pub prices: Vec<f64>,
    /// Achieved welfare `W = Σ v_i x_i` (stored; recomputed by `check`).
    pub welfare: f64,
    /// The upper bound `UB(y)` (stored; recomputed by `check`).
    pub upper_bound: f64,
    /// The feasibility / integrality tolerance the certificate is checked at.
    pub epsilon: f64,
}

/// The result of running the package-clearing checks.
#[derive(Clone, Debug, Serialize)]
pub struct CertPackageReport {
    /// Every `x_i` is within `tol` of `0` or `1` (ALL-OR-NONE preserved).
    pub integral: bool,
    /// `Σ_i d_ij x_i ≤ s_j` for every item (supply respected).
    pub capacity_ok: bool,
    /// `y ≥ 0` (a valid dual / price vector).
    pub prices_nonneg: bool,
    /// The weak-duality bound `W ≤ UB` holds (recomputed) — the near-optimality
    /// certificate is sound.
    pub bound_sound: bool,
    /// Recomputed achieved welfare `W`.
    pub welfare: f64,
    /// Recomputed upper bound `UB(y)`.
    pub upper_bound: f64,
    /// Recomputed certified ratio `α = W / UB ∈ (0,1]` — achieved ≥ `α` × optimum.
    pub ratio: f64,
    /// The tolerance used.
    pub tol: f64,
    /// Conjunction of every check.
    pub valid: bool,
}

impl CertPackage {
    /// Build the certificate from the auction + witness `(x, y)`.
    pub fn new(auction: &PackageAuction, accept: &[f64], prices: &[f64], epsilon: f64) -> Self {
        let n = auction.n_bids();
        let m = auction.n_items;
        let values: Vec<f64> = auction.bids.iter().map(|b| b.value).collect();
        let mut demands = vec![0.0f64; n * m];
        for (i, b) in auction.bids.iter().enumerate() {
            for j in 0..m {
                demands[i * m + j] = b.demand[j];
            }
        }
        let welfare = welfare_of(&values, accept);
        let upper_bound = upper_bound_of(&auction.supply, &values, &demands, m, prices);
        CertPackage {
            n_items: m,
            supply: auction.supply.clone(),
            values,
            demands,
            accept: accept.to_vec(),
            prices: prices.to_vec(),
            welfare,
            upper_bound,
            epsilon,
        }
    }

    /// Run the checks at an explicit tolerance (recomputed from the public program
    /// + witness — the checker trusts nothing stored).
    pub fn check_with(&self, tol: f64) -> CertPackageReport {
        let n = self.values.len();
        let m = self.n_items;

        // Integrality: every x_i within tol of 0 or 1 (all-or-none preserved).
        let integral = self
            .accept
            .iter()
            .all(|&x| x.abs() <= tol || (x - 1.0).abs() <= tol);

        // Capacity: Σ_i d_ij x_i ≤ s_j for every item.
        let mut capacity_ok = true;
        for j in 0..m {
            let mut used = 0.0;
            for i in 0..n {
                used += self.demands[i * m + j] * self.accept[i];
            }
            if used > self.supply[j] + tol {
                capacity_ok = false;
            }
        }

        let prices_nonneg = self.prices.iter().all(|&p| p >= -tol);

        // Recompute W and UB(y) from scratch.
        let welfare = welfare_of(&self.values, &self.accept);
        let upper_bound =
            upper_bound_of(&self.supply, &self.values, &self.demands, m, &self.prices);

        // Weak duality: W ≤ UB. (Always true for a feasible x and y ≥ 0 — this is
        // the theorem; checked here so a checker bug or a forged bound is caught.)
        let bound_sound = welfare <= upper_bound + tol;

        // The certified ratio α = W / UB ∈ (0,1]. If UB ≈ 0 (no positive-value
        // bid), the empty clearing is exactly optimal ⇒ ratio 1.
        let ratio = if upper_bound.abs() <= tol {
            1.0
        } else {
            (welfare / upper_bound).clamp(0.0, 1.0)
        };

        let valid = integral && capacity_ok && prices_nonneg && bound_sound;
        CertPackageReport {
            integral,
            capacity_ok,
            prices_nonneg,
            bound_sound,
            welfare,
            upper_bound,
            ratio,
            tol,
            valid,
        }
    }

    /// `check_with` at a tolerance scaled to the problem magnitude.
    pub fn check(&self) -> CertPackageReport {
        let scale = self
            .values
            .iter()
            .cloned()
            .fold(1.0f64, |m, v| m.max(v.abs()))
            .max(1.0);
        self.check_with(1e-6 * scale)
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

/// `W = Σ v_i x_i`.
fn welfare_of(values: &[f64], accept: &[f64]) -> f64 {
    values.iter().zip(accept).map(|(v, x)| v * x).sum()
}

/// `UB(y) = Σ_j s_j y_j + Σ_i (v_i − d_i·y)₊`. The valid upper bound on the
/// integral optimum for any `y ≥ 0` (weak duality). `demands` is row-major `n×m`.
fn upper_bound_of(supply: &[f64], values: &[f64], demands: &[f64], m: usize, y: &[f64]) -> f64 {
    let supply_term: f64 = supply.iter().zip(y).map(|(s, p)| s * p).sum();
    let n = values.len();
    let mut slack_term = 0.0;
    for i in 0..n {
        let cost: f64 = (0..m).map(|j| demands[i * m + j] * y[j]).sum();
        slack_term += (values[i] - cost).max(0.0);
    }
    supply_term + slack_term
}

// ===========================================================================
// The untrusted search: a Lagrangian dual (subgradient) + greedy rounding.
// ===========================================================================

/// Subgradient descent on the item prices `y ≥ 0` to MINIMISE the upper bound
/// `UB(y)` (tightening the near-optimality certificate). Returns the tightest
/// `(y, UB)` SEEN across all iterations (UB is convex but the subgradient path is
/// non-monotone, so we keep the best). `y = 0` gives the trivial bound `Σ v₊`, so
/// the search only ever improves it.
fn solve_dual(auction: &PackageAuction, iters: usize) -> (Vec<f64>, f64) {
    let m = auction.n_items;
    let n = auction.n_bids();
    let values: Vec<f64> = auction.bids.iter().map(|b| b.value).collect();

    // Step scale from the value/supply magnitudes.
    let vmax = values.iter().cloned().fold(0.0f64, |a, v| a.max(v.abs()));
    let smax = auction.supply.iter().cloned().fold(1.0f64, f64::max);
    let step0 = (vmax / smax).max(1e-6);

    let mut y = vec![0.0f64; m];
    let mut best_y = y.clone();
    // Trivial dual y=0 bound.
    let mut best_ub: f64 = values.iter().map(|&v| v.max(0.0)).sum();

    for t in 0..iters {
        // Tentative acceptance in the Lagrangian inner max: x_i = 1 iff the
        // reduced value v_i − d_i·y > 0. Subgradient g_j = s_j − Σ_{accepted} d_ij.
        let mut g = auction.supply.clone();
        for (i, b) in auction.bids.iter().enumerate() {
            if values[i] - b.cost(&y) > 0.0 {
                for j in 0..m {
                    g[j] -= b.demand[j];
                }
            }
        }
        // Diminishing step; descend UB (minimise) with a nonneg projection.
        let step = step0 / (1.0 + 0.05 * t as f64);
        for j in 0..m {
            y[j] = (y[j] - step * g[j]).max(0.0);
        }
        // Track the tightest bound seen.
        let ub = {
            let supply_term: f64 = auction.supply.iter().zip(&y).map(|(s, p)| s * p).sum();
            let slack_term: f64 = (0..n)
                .map(|i| (values[i] - auction.bids[i].cost(&y)).max(0.0))
                .sum();
            supply_term + slack_term
        };
        if ub < best_ub {
            best_ub = ub;
            best_y.clone_from(&y);
        }
    }
    (best_y, best_ub)
}

/// Greedy rounding under a bid ORDERING: accept each bid if the whole bundle still
/// fits (all-or-none), producing a FEASIBLE integral packing. `order` lists bid
/// indices in the priority they are considered.
fn greedy_pack(auction: &PackageAuction, order: &[usize]) -> (Vec<f64>, f64) {
    let m = auction.n_items;
    let mut remaining = auction.supply.clone();
    let mut accept = vec![0.0f64; auction.n_bids()];
    let mut welfare = 0.0;
    for &i in order {
        let b = &auction.bids[i];
        if b.value <= 0.0 {
            continue; // never accept a non-positive-value bid
        }
        let fits = (0..m).all(|j| b.demand[j] <= remaining[j] + 1e-12);
        if fits {
            accept[i] = 1.0;
            welfare += b.value;
            for j in 0..m {
                remaining[j] -= b.demand[j];
            }
        }
    }
    (accept, welfare)
}

/// Clear a package auction: tighten the dual bound (subgradient), round to a
/// feasible integral packing (best of several greedy orderings), and emit the
/// certificate. `iters` bounds the subgradient search. Returns
/// `(clearing, CertPackage)`.
pub fn clear_package(auction: &PackageAuction, iters: usize) -> (PackageClearing, CertPackage) {
    let m = auction.n_items;
    let n = auction.n_bids();

    // 1. The dual bound (untrusted search) → item prices y + UB.
    let (prices, upper_bound) = solve_dual(auction, iters);

    // 2. Greedy rounding under several orderings; keep the best-welfare packing.
    //    (a) by value; (b) by value / total-demand (unit-weight density);
    //    (c) by value / (d·y) (dual-price-weighted density — LP-guided).
    let values: Vec<f64> = auction.bids.iter().map(|b| b.value).collect();
    let total_demand = |i: usize| -> f64 { auction.bids[i].demand.iter().sum::<f64>().max(1e-12) };
    let dual_cost = |i: usize| -> f64 { auction.bids[i].cost(&prices).max(1e-12) };

    let mut orderings: Vec<Vec<usize>> = Vec::new();
    let push_order = |key: &dyn Fn(usize) -> f64, orderings: &mut Vec<Vec<usize>>| {
        let mut o: Vec<usize> = (0..n).collect();
        o.sort_by(|&a, &b| {
            key(b)
                .partial_cmp(&key(a))
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        orderings.push(o);
    };
    push_order(&|i| values[i], &mut orderings);
    push_order(&|i| values[i] / total_demand(i), &mut orderings);
    push_order(&|i| values[i] / dual_cost(i), &mut orderings);

    let mut best_accept = vec![0.0f64; n];
    let mut best_welfare = 0.0;
    for o in &orderings {
        let (accept, welfare) = greedy_pack(auction, o);
        if welfare > best_welfare {
            best_welfare = welfare;
            best_accept = accept;
        }
    }

    // 3. Item usage + certified ratio.
    let mut item_usage = vec![0.0f64; m];
    for (i, b) in auction.bids.iter().enumerate() {
        for j in 0..m {
            item_usage[j] += b.demand[j] * best_accept[i];
        }
    }
    let ratio = if upper_bound.abs() <= 1e-12 {
        1.0
    } else {
        (best_welfare / upper_bound).clamp(0.0, 1.0)
    };

    // ε: an absolute feasibility/integrality slack scaled to the value magnitude.
    let scale = values.iter().cloned().fold(1.0f64, |a, v| a.max(v.abs()));
    let cert = CertPackage::new(auction, &best_accept, &prices, 1e-6 * scale);

    let clearing = PackageClearing {
        accept: best_accept,
        welfare: best_welfare,
        item_usage,
        prices,
        upper_bound,
        ratio,
    };
    (clearing, cert)
}

// ===========================================================================
// Test-instance builders.
// ===========================================================================

/// The textbook single-unit combinatorial auction: `m` items, one unit each,
/// singleton + pair + grand bundles at the given values. A clean instance with a
/// known optimum for the positive-polarity test.
pub fn sample_auction() -> PackageAuction {
    // 3 items, one unit each.
    let bids = vec![
        PackageBid::new(6.0, vec![1.0, 0.0, 0.0]),  // {0}
        PackageBid::new(5.0, vec![0.0, 1.0, 0.0]),  // {1}
        PackageBid::new(5.0, vec![0.0, 0.0, 1.0]),  // {2}
        PackageBid::new(12.0, vec![1.0, 1.0, 0.0]), // {0,1}
        PackageBid::new(12.0, vec![0.0, 1.0, 1.0]), // {1,2}
        PackageBid::new(17.0, vec![1.0, 1.0, 1.0]), // {0,1,2}
    ];
    // Optimum = {1,2}(12) + {0}(6) = 18.
    PackageAuction {
        n_items: 3,
        supply: vec![1.0, 1.0, 1.0],
        bids,
    }
}

/// A deterministic pseudo-random multi-unit combinatorial auction (for the
/// benchmark): `n_bids` bundles over `n_items`, each bundle touching a few items
/// with small integer demands, capacities a few units each.
pub fn random_auction(n_items: usize, n_bids: usize, seed: u64) -> PackageAuction {
    let mut state = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let bids = (0..n_bids)
        .map(|_| {
            let mut demand = vec![0.0f64; n_items];
            // 1–3 items in the bundle.
            let k = 1 + (next() % 3) as usize;
            let mut touched = 0.0;
            for _ in 0..k {
                let j = (next() as usize) % n_items;
                let units = 1.0 + (next() % 3) as f64; // 1–3 units
                demand[j] += units;
                touched += units;
            }
            // Value ~ proportional to bundle size with noise (super-/sub-additive mix).
            let noise = (next() % 100) as f64 / 100.0;
            let value = touched * (1.0 + noise) + 1.0;
            PackageBid::new(value, demand)
        })
        .collect();
    // Capacity: a few units per item.
    let supply = (0..n_items).map(|_| 3.0 + (next() % 4) as f64).collect();
    PackageAuction {
        n_items,
        supply,
        bids,
    }
}

/// Brute-force the exact integral optimum by enumerating all `2^n` subsets — for
/// SMALL `n` only (the benchmark uses it to report the TRUE ratio the certificate
/// bounds, on instances small enough to know the optimum). Panics past `n = 24`.
pub fn brute_force_optimum(auction: &PackageAuction) -> f64 {
    let n = auction.n_bids();
    assert!(n <= 24, "brute force is 2^n — small instances only");
    let m = auction.n_items;
    let mut best = 0.0f64;
    for mask in 0u32..(1u32 << n) {
        let mut usage = vec![0.0f64; m];
        let mut welfare = 0.0;
        let mut feasible = true;
        for i in 0..n {
            if mask & (1 << i) != 0 {
                welfare += auction.bids[i].value;
                for j in 0..m {
                    usage[j] += auction.bids[i].demand[j];
                    if usage[j] > auction.supply[j] + 1e-9 {
                        feasible = false;
                        break;
                    }
                }
                if !feasible {
                    break;
                }
            }
        }
        if feasible && welfare > best {
            best = welfare;
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample_auction_clears_feasible_and_certifies() {
        let auction = sample_auction();
        let (clr, cert) = clear_package(&auction, 3000);
        let rep = cert.check();
        assert!(
            rep.valid,
            "package clearing certificate must be valid: {rep:?}"
        );
        assert!(rep.integral, "all-or-none: every x ∈ {{0,1}}");
        assert!(rep.capacity_ok, "supply respected");
        assert!(rep.prices_nonneg, "y ≥ 0");
        assert!(rep.bound_sound, "weak duality W ≤ UB");
        // The greedy (density ordering) finds the true optimum 18.
        assert!(
            clr.welfare >= 18.0 - 1e-9,
            "should find optimum 18, got {}",
            clr.welfare
        );
        // The bound is valid and the ratio is meaningful (∈ (0,1]).
        assert!(
            clr.ratio > 0.0 && clr.ratio <= 1.0 + 1e-9,
            "ratio {}",
            clr.ratio
        );
        assert!(
            clr.upper_bound >= clr.welfare - 1e-9,
            "UB {} must bound W {}",
            clr.upper_bound,
            clr.welfare
        );
    }

    #[test]
    fn certified_ratio_bounds_the_true_optimum() {
        // On an instance small enough to brute-force, the certified ratio is a
        // SOUND lower bound: achieved ≥ ratio · optimum, and UB ≥ optimum.
        let auction = sample_auction();
        let (clr, _) = clear_package(&auction, 3000);
        let opt = brute_force_optimum(&auction);
        assert!((opt - 18.0).abs() < 1e-9, "known optimum is 18, got {opt}");
        assert!(
            clr.upper_bound >= opt - 1e-6,
            "UB {} ≥ optimum {}",
            clr.upper_bound,
            opt
        );
        // achieved ≥ ratio · optimum (the certified guarantee).
        assert!(
            clr.welfare >= clr.ratio * opt - 1e-6,
            "achieved {} ≥ ratio {} × opt {}",
            clr.welfare,
            clr.ratio,
            opt
        );
    }

    #[test]
    fn indivisibility_is_preserved_not_relaxed() {
        // Every accepted bid is FULLY filled (x = 1), never a fraction.
        let auction = sample_auction();
        let (clr, _) = clear_package(&auction, 3000);
        for &x in &clr.accept {
            assert!(
                x.abs() < 1e-9 || (x - 1.0).abs() < 1e-9,
                "x must be 0 or 1 (all-or-none), got {x}"
            );
        }
    }

    #[test]
    fn tampered_partial_fill_is_rejected() {
        // Half-fill a package (relax the all-or-none) → integrality REFUSES.
        let auction = sample_auction();
        let (_, mut cert) = clear_package(&auction, 3000);
        // Find a rejected bid and half-accept it.
        let idx = cert.accept.iter().position(|&x| x < 0.5).unwrap();
        cert.accept[idx] = 0.5;
        let rep = cert.check();
        assert!(!rep.integral, "a half-filled package breaks all-or-none");
        assert!(!rep.valid, "partial fill must be rejected");
    }

    #[test]
    fn tampered_over_capacity_is_rejected() {
        // Accept EVERY bid → items go over supply → capacity REFUSES.
        let auction = sample_auction();
        let (_, mut cert) = clear_package(&auction, 3000);
        cert.accept = vec![1.0; cert.values.len()];
        let rep = cert.check();
        assert!(
            !rep.capacity_ok,
            "accepting all bids over-subscribes supply"
        );
        assert!(!rep.valid, "over-capacity allocation must be rejected");
    }

    #[test]
    fn negative_price_is_rejected() {
        // A negative item price is not a valid dual → REFUSED (the bound would be
        // unsound).
        let auction = sample_auction();
        let (_, mut cert) = clear_package(&auction, 3000);
        cert.prices[0] = -1.0;
        let rep = cert.check();
        assert!(!rep.prices_nonneg, "y ≥ 0 required");
        assert!(!rep.valid, "negative price must be rejected");
    }

    #[test]
    fn empty_book_is_trivially_optimal() {
        // No bids: the empty clearing is exactly optimal (W = UB = 0, ratio 1).
        let auction = PackageAuction {
            n_items: 2,
            supply: vec![1.0, 1.0],
            bids: vec![],
        };
        let (clr, cert) = clear_package(&auction, 500);
        let rep = cert.check();
        assert!(rep.valid, "empty clearing certifies");
        assert_eq!(clr.welfare, 0.0);
        assert!(
            (rep.ratio - 1.0).abs() < 1e-9,
            "empty book is exactly optimal"
        );
    }

    #[test]
    fn dual_bound_beats_the_trivial_bound() {
        // The subgradient tightens UB below the trivial Σv₊ bound (some duality is
        // extracted). On the sample instance Σv = 6+5+5+12+12+17 = 57; the dual
        // bound must be far tighter (≤ 25, near the optimum 18).
        let auction = sample_auction();
        let (clr, _) = clear_package(&auction, 3000);
        let sum_v: f64 = auction.bids.iter().map(|b| b.value).sum();
        assert!((sum_v - 57.0).abs() < 1e-9);
        assert!(
            clr.upper_bound < 30.0,
            "dual bound {} should be far below the trivial {}",
            clr.upper_bound,
            sum_v
        );
    }

    #[test]
    fn json_roundtrips_shape() {
        let auction = sample_auction();
        let (_, cert) = clear_package(&auction, 2000);
        let json = cert.to_json();
        assert!(json.contains("\"accept\""));
        assert!(json.contains("\"prices\""));
        assert!(json.contains("\"upper_bound\""));
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["n_items"], 3);
    }

    #[test]
    fn random_instances_always_feasible_and_bounded() {
        // Across many random instances: feasibility + a valid bound ALWAYS hold
        // (the honest invariant), whatever the ratio.
        for seed in 0..40u64 {
            let auction = random_auction(5, 12, seed);
            let (clr, cert) = clear_package(&auction, 2000);
            let rep = cert.check();
            assert!(rep.valid, "seed {seed}: cert must be valid: {rep:?}");
            assert!(rep.integral && rep.capacity_ok && rep.bound_sound);
            // The certified ratio soundly bounds the brute-force optimum.
            let opt = brute_force_optimum(&auction);
            assert!(
                clr.upper_bound >= opt - 1e-6,
                "seed {seed}: UB {} must bound optimum {}",
                clr.upper_bound,
                opt
            );
            assert!(
                clr.welfare >= clr.ratio * opt - 1e-6,
                "seed {seed}: achieved ≥ ratio·opt"
            );
        }
    }
}

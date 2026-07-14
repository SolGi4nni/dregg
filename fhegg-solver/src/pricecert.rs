//! Price-Cert — the derivatives-pricing certificate (the fhIR-1 RUNNER).
//!
//! This is the executable realization of `metatheory/Market/PriceCert.lean`: the
//! state-price LP + superhedging dual that prices the WHOLE LP-expressible
//! derivatives family with ONE certificate relation. It is the Price-Cert sibling
//! of [`crate::cert::CertF`] (circulation) / [`crate::qp::CertQp`] (portfolio) /
//! [`crate::fisher::CertEq`] / [`crate::cfmm::CertRoute`] — an untrusted solve
//! plus a checked certificate (translation validation, verify-not-find).
//!
//! ## The two members of the family (both proved in `PriceCert.lean`)
//!
//! **European / basket / Asian / barrier — the state-price LP.** Over a public
//! scenario grid, calibrated instruments `H` (`H[j][s]` = payoff of instrument
//! `j` in scenario `s`, instrument-major, exactly the Lean `Matrix J S`), observed
//! marks `a`, and a new product's scenario payoff `h`:
//!
//! ```text
//!   upper price  p̄ = max_{π ≥ 0}  hᵀπ   s.t.  H π = a       (consistent state prices)
//!   superhedge   p̄ = min_{y}      aᵀy   s.t.  yᵀH ≥ h       (a dominating portfolio)
//! ```
//!
//! The certificate is `(π, y)` with `π ≥ 0, Hπ = a, yᵀH ≥ h, 0 ≤ aᵀy − hᵀπ ≤ ε`
//! ([`CertPrice`]). By `price_weak_duality` / `price_cert_certifies` a valid
//! certificate proves the arbitrage-free price to within `ε`, INDEPENDENT of how
//! `(π, y)` were found. [`CertPrice::check`] mirrors the Lean clauses exactly
//! (`π ≥ 0`, `Hπ = a`, `yᵀH ≥ h`, `gap ≤ ε`) and tamper-rejects.
//!
//! **American / Bermudan — the Snell-envelope LP.** Early exercise is NOT a
//! mixed-integer problem: it is the optimal-stopping LP on the scenario tree
//! (Haugh–Kogan / Rogers). A candidate value vector `V` is Snell-feasible when it
//! dominates the exercise payoff (`V ≥ g`) and is superharmonic
//! (`V_n ≥ d·Σ P_nm V_m` at every internal node); by `snell_feasible_upper_bound`
//! any feasible `V` UPPER-bounds the true backward-induction value. The runner
//! computes the tight envelope by backward induction ([`SnellTree::backward`]) and
//! emits [`CertSnell`], whose [`CertSnell::check`] validates the LP feasibility.
//!
//! ## Honest scope (matching the Lean's named residuals)
//!
//! * The state-price LP is solved EXACTLY by a two-phase simplex (small dense
//!   instances); the certificate is tight (`gap ≈ 0` at double precision).
//! * The Snell runner evaluates the full recombining tree by backward induction.
//!   The PER-STEP domination lemma is Lean-proved (`snell_feasible_upper_bound`);
//!   the MULTI-LAYER DAG assembly is the Lean's NAMED residual — computed here,
//!   its feasibility checked, but its soundness composition not re-derived.
//! * The **continuous / path-dependent** case (running-max barriers, continuous
//!   monitoring) is the state-size residual named in `PriceCert.lean`: the tree is
//!   a finite PUBLIC grid here.
//! * A proof certifies pricing UNDER A COMMITTED MODEL; it cannot certify the
//!   model is economically correct (the honest floor of R2.1).

use serde::Serialize;

// ===========================================================================
// The two-phase simplex — the untrusted LP search (dense, small instances).
// ===========================================================================

/// The result of a min-form LP solve `min cᵀx s.t. Ax = b, x ≥ 0`.
struct SimplexResult {
    /// Primal optimum `x` (length `n`), a basic feasible solution.
    x: Vec<f64>,
    /// The simplex multipliers `y = c_B B⁻¹` (length `m`) — the LP dual of the
    /// MIN problem (`Aᵀy ≤ c` at optimum).
    y: Vec<f64>,
    /// Whether the LP is feasible (`false` = the constraints admit no `x ≥ 0`).
    feasible: bool,
}

/// One Gauss–Jordan pivot on `(row, col)` of the tableau + rhs.
fn do_pivot(t: &mut [f64], rhs: &mut [f64], m: usize, ncol: usize, prow: usize, pcol: usize) {
    let piv = t[prow * ncol + pcol];
    for j in 0..ncol {
        t[prow * ncol + j] /= piv;
    }
    rhs[prow] /= piv;
    for i in 0..m {
        if i == prow {
            continue;
        }
        let f = t[i * ncol + pcol];
        if f.abs() < 1e-15 {
            continue;
        }
        for j in 0..ncol {
            t[i * ncol + j] -= f * t[prow * ncol + j];
        }
        rhs[i] -= f * rhs[prow];
    }
}

/// Drive the tableau to optimality (min), Bland's rule (anti-cycling). `allow`
/// gates which columns may ENTER the basis (phase 2 forbids the artificials).
fn pivot_to_optimal(
    t: &mut [f64],
    rhs: &mut [f64],
    basis: &mut [usize],
    cost: &[f64],
    m: usize,
    ncol: usize,
    allow: impl Fn(usize) -> bool,
    eps: f64,
) {
    loop {
        // Entering column: the smallest index (Bland) with reduced cost < 0.
        let mut entering = None;
        for j in 0..ncol {
            if !allow(j) || basis.contains(&j) {
                continue;
            }
            let zj: f64 = (0..m).map(|k| cost[basis[k]] * t[k * ncol + j]).sum();
            if cost[j] - zj < -eps {
                entering = Some(j);
                break;
            }
        }
        let Some(e) = entering else { break };

        // Leaving row: min-ratio, Bland tie-break on the smallest basic index.
        let mut leaving: Option<usize> = None;
        let mut best = f64::INFINITY;
        for i in 0..m {
            let aie = t[i * ncol + e];
            if aie > eps {
                let ratio = rhs[i] / aie;
                let take = ratio < best - eps
                    || ((ratio - best).abs() <= eps
                        && leaving.map_or(true, |li| basis[i] < basis[li]));
                if take {
                    best = ratio;
                    leaving = Some(i);
                }
            }
        }
        let Some(l) = leaving else { break }; // unbounded — bail (does not occur here)
        do_pivot(t, rhs, m, ncol, l, e);
        basis[l] = e;
    }
}

/// Solve `min cᵀx s.t. Ax = b, x ≥ 0` (`A` is `m×n` row-major) by two-phase
/// simplex, returning the primal `x`, the dual multipliers `y`, and feasibility.
/// The dual is read from the artificial columns: `t[:, n+i] = B⁻¹ eᵢ`, so
/// `yᵢ = c_B · t[:, n+i] = c_B B⁻¹ eᵢ`.
fn solve_min_lp(a: &[f64], m: usize, n: usize, b: &[f64], c: &[f64]) -> SimplexResult {
    let eps = 1e-9;
    let ncol = n + m;
    let mut t = vec![0.0f64; m * ncol];
    let mut rhs = b.to_vec();
    // Normalise to b ≥ 0 (flip rows) and lay in the artificial identity block.
    for i in 0..m {
        let sign = if rhs[i] < 0.0 { -1.0 } else { 1.0 };
        rhs[i] *= sign;
        for j in 0..n {
            t[i * ncol + j] = sign * a[i * n + j];
        }
        t[i * ncol + (n + i)] = 1.0;
    }
    let mut basis: Vec<usize> = (0..m).map(|i| n + i).collect();

    // Phase 1: minimise the sum of artificials (feasibility).
    let mut cost = vec![0.0f64; ncol];
    for i in 0..m {
        cost[n + i] = 1.0;
    }
    pivot_to_optimal(&mut t, &mut rhs, &mut basis, &cost, m, ncol, |_| true, eps);
    let phase1: f64 = (0..m).filter(|&i| basis[i] >= n).map(|i| rhs[i]).sum();
    if phase1 > 1e-6 {
        // The constraints admit no π ≥ 0 — the market is INCONSISTENT (arbitrage).
        return SimplexResult {
            x: vec![0.0; n],
            y: vec![0.0; m],
            feasible: false,
        };
    }
    // Drive any artificial still basic out (redundant rows are left at value 0).
    for i in 0..m {
        if basis[i] >= n {
            if let Some(j) = (0..n).find(|&j| t[i * ncol + j].abs() > eps) {
                do_pivot(&mut t, &mut rhs, m, ncol, i, j);
                basis[i] = j;
            }
        }
    }

    // Phase 2: minimise the real objective; the artificials stay out of the basis.
    for j in 0..n {
        cost[j] = c[j];
    }
    for i in 0..m {
        cost[n + i] = 0.0;
    }
    pivot_to_optimal(&mut t, &mut rhs, &mut basis, &cost, m, ncol, |j| j < n, eps);

    let mut x = vec![0.0f64; n];
    for i in 0..m {
        if basis[i] < n {
            x[basis[i]] = rhs[i];
        }
    }
    let mut y = vec![0.0f64; m];
    for (i, yi) in y.iter_mut().enumerate() {
        *yi = (0..m).map(|k| cost[basis[k]] * t[k * ncol + (n + i)]).sum();
    }
    SimplexResult {
        x,
        y,
        feasible: true,
    }
}

// ===========================================================================
// The state-price market + the Price-Cert (European / basket / Asian family).
// ===========================================================================

/// A state-price market — the public object every LP-expressible derivative
/// prices against (the Rust mirror of `PriceCert.lean`'s `Market`).
#[derive(Clone, Debug, Serialize)]
pub struct Market {
    /// Number of scenarios `S`.
    pub n_scenarios: usize,
    /// Number of calibrated instruments `J`.
    pub n_instruments: usize,
    /// The instrument-payoff matrix `H`, INSTRUMENT-MAJOR (`J` rows × `S` cols,
    /// `h_mat[j*S + s]` = payoff of instrument `j` in scenario `s`) — exactly the
    /// Lean `H : Matrix J S`.
    pub h_mat: Vec<f64>,
    /// The observed instrument marks `a` (length `J`).
    pub a: Vec<f64>,
    /// The new product's scenario payoff `h` (length `S`).
    pub h: Vec<f64>,
    /// The public accuracy target `ε` (`gap ≤ ε` ⇒ ε-tight arbitrage-free bound).
    pub epsilon: f64,
}

impl Market {
    /// Build a market from a SCENARIO-MAJOR payoff grid (`S` rows × `J` cols,
    /// `data[s*J + j]`), transposing to the instrument-major `H` the Lean uses.
    /// This is the shape `fhir`'s `MatrixData` (scenario rows) hands over.
    pub fn from_scenario_major(
        n_scenarios: usize,
        n_instruments: usize,
        scenario_major: &[f64],
        marks: Vec<f64>,
        payoff: Vec<f64>,
        epsilon: f64,
    ) -> Self {
        assert_eq!(scenario_major.len(), n_scenarios * n_instruments);
        assert_eq!(marks.len(), n_instruments);
        assert_eq!(payoff.len(), n_scenarios);
        let mut h_mat = vec![0.0f64; n_instruments * n_scenarios];
        for s in 0..n_scenarios {
            for j in 0..n_instruments {
                h_mat[j * n_scenarios + s] = scenario_major[s * n_instruments + j];
            }
        }
        Market {
            n_scenarios,
            n_instruments,
            h_mat,
            a: marks,
            h: payoff,
            epsilon,
        }
    }

    /// `(H π)ⱼ = Σ_s H[j][s] π[s]` — the instrument's payoff under the measure π.
    fn h_mulvec(&self, pi: &[f64]) -> Vec<f64> {
        (0..self.n_instruments)
            .map(|j| {
                (0..self.n_scenarios)
                    .map(|s| self.h_mat[j * self.n_scenarios + s] * pi[s])
                    .sum()
            })
            .collect()
    }

    /// `(yᵀH)_s = Σ_j y[j] H[j][s]` — the hedge portfolio's payoff in scenario `s`.
    fn y_vecmul(&self, y: &[f64]) -> Vec<f64> {
        (0..self.n_scenarios)
            .map(|s| {
                (0..self.n_instruments)
                    .map(|j| y[j] * self.h_mat[j * self.n_scenarios + s])
                    .sum()
            })
            .collect()
    }
}

/// A Price-Cert certificate — the state-price / superhedge pair, the ENTIRE
/// object the checker reads (the Rust mirror of `PriceCert.lean`'s
/// `PriceCertified`). `π ≥ 0, Hπ = a, yᵀH ≥ h, aᵀy − hᵀπ ≤ ε`.
#[derive(Clone, Debug, Serialize)]
pub struct CertPrice {
    pub n_scenarios: usize,
    pub n_instruments: usize,
    pub h_mat: Vec<f64>,
    pub a: Vec<f64>,
    pub h: Vec<f64>,
    pub epsilon: f64,
    /// The consistent state price `π` (length `S`).
    pub pi: Vec<f64>,
    /// The superhedge `y` (length `J`).
    pub y: Vec<f64>,
    /// The certified no-arbitrage price `hᵀπ` (the primal upper price).
    pub primal_price: f64,
    /// The superhedge cost `aᵀy` (the dual bound).
    pub dual_cost: f64,
    /// The duality gap `aᵀy − hᵀπ` (≥ 0 by weak duality).
    pub gap: f64,
}

/// The Price-Cert check report (mirrors the four `PriceCert.lean` clauses).
#[derive(Clone, Debug, Serialize)]
pub struct CertPriceReport {
    /// `π ≥ 0` (`ConsistentPrice.1`).
    pub pi_nonneg: bool,
    /// `Hπ = a` within `tol` (`ConsistentPrice.2`) — instrument calibration.
    pub consistent: bool,
    /// `yᵀH ≥ h` within `tol` (`Superhedge`).
    pub superhedge: bool,
    /// `aᵀy − hᵀπ ≤ ε` (the certified gap).
    pub gap_ok: bool,
    /// `‖Hπ − a‖_∞` — the consistency residual.
    pub consistency_residual: f64,
    /// `max_s (h_s − (yᵀH)_s)₊` — the superhedge shortfall.
    pub hedge_shortfall: f64,
    pub gap: f64,
    pub tol: f64,
    /// Conjunction of every clause.
    pub valid: bool,
}

impl CertPrice {
    /// Assemble a certificate from a `(π, y)` pair against `market`.
    pub fn from_solution(market: &Market, pi: Vec<f64>, y: Vec<f64>, epsilon: f64) -> Self {
        let primal_price: f64 = market.h.iter().zip(&pi).map(|(h, p)| h * p).sum();
        let dual_cost: f64 = market.a.iter().zip(&y).map(|(a, y)| a * y).sum();
        CertPrice {
            n_scenarios: market.n_scenarios,
            n_instruments: market.n_instruments,
            h_mat: market.h_mat.clone(),
            a: market.a.clone(),
            h: market.h.clone(),
            epsilon,
            pi,
            y,
            primal_price,
            dual_cost,
            gap: dual_cost - primal_price,
        }
    }

    /// Validate the four Lean clauses at tolerance `tol` (recomputed from
    /// `(π, y)` — a checker never trusts the stored scalars).
    pub fn check_with(&self, tol: f64) -> CertPriceReport {
        let market = Market {
            n_scenarios: self.n_scenarios,
            n_instruments: self.n_instruments,
            h_mat: self.h_mat.clone(),
            a: self.a.clone(),
            h: self.h.clone(),
            epsilon: self.epsilon,
        };
        let pi_nonneg = self.pi.iter().all(|&p| p >= -tol);

        let hpi = market.h_mulvec(&self.pi);
        let consistency_residual = hpi
            .iter()
            .zip(&self.a)
            .fold(0.0f64, |m, (hp, a)| m.max((hp - a).abs()));
        let consistent = consistency_residual <= tol;

        let yh = market.y_vecmul(&self.y);
        let hedge_shortfall = yh
            .iter()
            .zip(&self.h)
            .fold(0.0f64, |m, (yh, h)| m.max((h - yh).max(0.0)));
        let superhedge = hedge_shortfall <= tol;

        let price: f64 = market.h.iter().zip(&self.pi).map(|(h, p)| h * p).sum();
        let cost: f64 = market.a.iter().zip(&self.y).map(|(a, y)| a * y).sum();
        let gap = cost - price;
        let gap_ok = gap <= self.epsilon + tol;

        let valid = pi_nonneg && consistent && superhedge && gap_ok;
        CertPriceReport {
            pi_nonneg,
            consistent,
            superhedge,
            gap_ok,
            consistency_residual,
            hedge_shortfall,
            gap,
            tol,
            valid,
        }
    }

    /// `check_with` at a tolerance scaled to the market magnitude.
    pub fn check(&self) -> CertPriceReport {
        let scale = self
            .a
            .iter()
            .chain(&self.h)
            .fold(1.0f64, |m, v| m.max(v.abs()));
        self.check_with(1e-6 * scale)
    }

    /// Serialize to the JSON wire format the Lean Price-Cert checker ingests.
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

/// The outcome of running the state-price LP.
pub enum PriceOutcome {
    /// A valid arbitrage-free price + its Price-Cert.
    Certified(CertPrice),
    /// The market admits ARBITRAGE — no consistent state price `π ≥ 0` with
    /// `Hπ = a` exists, so there is NO arbitrage-free price and NO certificate.
    /// The honest negative polarity (mirrors `piBad_inconsistent`).
    Arbitrage,
}

/// **The Price-Cert RUNNER (European / basket / Asian family).** Solve the
/// state-price LP `max hᵀπ s.t. Hπ = a, π ≥ 0` (untrusted simplex search) and,
/// on success, emit the tight `(π, y)` certificate — `π` the primal state price,
/// `y = −y'` the superhedging dual (so `yᵀH ≥ h`), gap ≈ 0. If the market is
/// inconsistent (arbitrage), returns [`PriceOutcome::Arbitrage`] — no cert.
pub fn solve_price_cert(market: &Market) -> PriceOutcome {
    let (m, n) = (market.n_instruments, market.n_scenarios);
    // Primal: max hᵀπ s.t. Hπ=a, π≥0  ≡  min (−h)ᵀπ. A = H (instrument-major = m×n).
    let c: Vec<f64> = market.h.iter().map(|&h| -h).collect();
    let res = solve_min_lp(&market.h_mat, m, n, &market.a, &c);
    if !res.feasible {
        return PriceOutcome::Arbitrage;
    }
    // Dual of the MIN gives y' with Hᵀy' ≤ −h; the superhedge is y = −y'
    // (so Hᵀy ≥ h) with cost aᵀy = hᵀπ (gap 0).
    let y: Vec<f64> = res.y.iter().map(|&v| -v).collect();
    PriceOutcome::Certified(CertPrice::from_solution(market, res.x, y, market.epsilon))
}

// ===========================================================================
// The Snell-envelope LP + CertSnell (American / Bermudan family).
// ===========================================================================

/// A scenario tree for the Snell-envelope LP — the American/Bermudan object (the
/// Rust generalization of `PriceCert.lean`'s `SnellTree`, which is the one-step
/// binomial the per-step lemma is proved on). Nodes carry an exercise payoff `g`;
/// `children[n]` lists `(child, transition_weight)` and MUST have index `> n`
/// (reverse-topological, so backward induction is a single reverse sweep). A node
/// with no children is a terminal leaf.
#[derive(Clone, Debug, Serialize)]
pub struct SnellTree {
    pub n_nodes: usize,
    /// Exercise payoff per node.
    pub g: Vec<f64>,
    /// Per-step discount factor `d ≥ 0`.
    pub d: f64,
    /// `children[n] = [(child, weight)]`, `child > n`, weights `≥ 0`.
    pub children: Vec<Vec<(usize, f64)>>,
    /// The root node the option value is read at.
    pub root: usize,
}

impl SnellTree {
    /// Continuation value at node `n` under `V`: `d·Σ P_nm V_m` (the "hold" branch).
    fn continuation(&self, n: usize, v: &[f64]) -> f64 {
        self.d * self.children[n].iter().map(|&(m, p)| p * v[m]).sum::<f64>()
    }

    /// **Backward induction** — the exact Snell envelope. `V_n = g_n` at leaves;
    /// `V_n = max(g_n, continuation)` at internal nodes. The tight LP-feasible
    /// value vector (the runner's untrusted search; its feasibility is checked).
    pub fn backward(&self) -> Vec<f64> {
        let mut v = vec![0.0f64; self.n_nodes];
        for n in (0..self.n_nodes).rev() {
            v[n] = if self.children[n].is_empty() {
                self.g[n]
            } else {
                self.g[n].max(self.continuation(n, &v))
            };
        }
        v
    }
}

/// A Snell certificate — a value vector `V` that dominates exercise and is
/// superharmonic; a valid one UPPER-bounds the true option value at `root`
/// (`snell_feasible_upper_bound`).
#[derive(Clone, Debug, Serialize)]
pub struct CertSnell {
    pub n_nodes: usize,
    pub g: Vec<f64>,
    pub d: f64,
    pub children: Vec<Vec<(usize, f64)>>,
    pub root: usize,
    /// The candidate value vector `V`.
    pub v: Vec<f64>,
    pub epsilon: f64,
    /// The certified option value `V_root`.
    pub root_value: f64,
}

/// The Snell check report (dominance + superharmonicity = LP feasibility).
#[derive(Clone, Debug, Serialize)]
pub struct CertSnellReport {
    /// `V ≥ g` at every node (exercise-dominance).
    pub dominates: bool,
    /// `V_n ≥ d·Σ P V_m` at every internal node (superharmonic).
    pub superharmonic: bool,
    /// `max_n (g_n − V_n)₊` — the dominance shortfall.
    pub dominance_shortfall: f64,
    /// `max_n (continuation_n − V_n)₊` — the superharmonic shortfall.
    pub superharmonic_shortfall: f64,
    pub root_value: f64,
    pub tol: f64,
    pub valid: bool,
}

impl CertSnell {
    /// Assemble a Snell certificate from a value vector `V` against `tree`.
    pub fn from_value(tree: &SnellTree, v: Vec<f64>, epsilon: f64) -> Self {
        let root_value = v[tree.root];
        CertSnell {
            n_nodes: tree.n_nodes,
            g: tree.g.clone(),
            d: tree.d,
            children: tree.children.clone(),
            root: tree.root,
            v,
            epsilon,
            root_value,
        }
    }

    /// Validate LP feasibility (`V ≥ g`, superharmonic) at tolerance `tol`.
    pub fn check_with(&self, tol: f64) -> CertSnellReport {
        let tree = SnellTree {
            n_nodes: self.n_nodes,
            g: self.g.clone(),
            d: self.d,
            children: self.children.clone(),
            root: self.root,
        };
        let dominance_shortfall = self
            .g
            .iter()
            .zip(&self.v)
            .fold(0.0f64, |m, (g, v)| m.max((g - v).max(0.0)));
        let dominates = dominance_shortfall <= tol;

        let mut superharmonic_shortfall = 0.0f64;
        for n in 0..self.n_nodes {
            if !tree.children[n].is_empty() {
                let cont = tree.continuation(n, &self.v);
                superharmonic_shortfall = superharmonic_shortfall.max((cont - self.v[n]).max(0.0));
            }
        }
        let superharmonic = superharmonic_shortfall <= tol;

        CertSnellReport {
            dominates,
            superharmonic,
            dominance_shortfall,
            superharmonic_shortfall,
            root_value: self.v[self.root],
            tol,
            valid: dominates && superharmonic,
        }
    }

    /// `check_with` at a tolerance scaled to the payoff magnitude.
    pub fn check(&self) -> CertSnellReport {
        let scale = self.g.iter().fold(1.0f64, |m, v| m.max(v.abs()));
        self.check_with(1e-9 * scale)
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

/// **The Snell RUNNER (American / Bermudan family).** Compute the tight Snell
/// envelope by backward induction and emit its [`CertSnell`]. The value is the
/// exact early-exercise value; the certificate proves it is a valid upper bound
/// (`snell_feasible_upper_bound`, per-step lemma Lean-proved; multi-layer
/// composition the Lean's named residual).
pub fn solve_snell_cert(tree: &SnellTree, epsilon: f64) -> CertSnell {
    let v = tree.backward();
    CertSnell::from_value(tree, v, epsilon)
}

/// Build a recombining CRR binomial American-option Snell tree. `n_steps` steps,
/// spot `s0`, strike `k`, per-annum rate `r`, volatility `sigma`, expiry `t`
/// (years). `is_put` selects the exercise payoff `(K−S)₊` vs `(S−K)₊`. Node
/// `(i, j)` (step `i`, `j` up-moves) has index `i(i+1)/2 + j`; its children
/// `(i+1, j)` and `(i+1, j+1)` have larger indices — the reverse-topo invariant.
/// A genuine multi-step Snell LP (the "small binomial tree" of R2.1).
pub fn american_put_binomial(
    s0: f64,
    k: f64,
    r: f64,
    sigma: f64,
    t: f64,
    n_steps: usize,
    is_put: bool,
) -> SnellTree {
    let dt = t / n_steps as f64;
    let u = (sigma * dt.sqrt()).exp();
    let dmove = 1.0 / u;
    let disc = (-r * dt).exp();
    let p = ((r * dt).exp() - dmove) / (u - dmove); // risk-neutral up-probability
    let idx = |i: usize, j: usize| i * (i + 1) / 2 + j;
    let n_nodes = idx(n_steps, n_steps) + 1;

    let mut g = vec![0.0f64; n_nodes];
    let mut children = vec![Vec::new(); n_nodes];
    for i in 0..=n_steps {
        for j in 0..=i {
            let price = s0 * u.powi(j as i32) * dmove.powi((i - j) as i32);
            let payoff = if is_put {
                (k - price).max(0.0)
            } else {
                (price - k).max(0.0)
            };
            g[idx(i, j)] = payoff;
            if i < n_steps {
                // down → (i+1, j), up → (i+1, j+1); both index > idx(i,j).
                children[idx(i, j)] = vec![(idx(i + 1, j), 1.0 - p), (idx(i + 1, j + 1), p)];
            }
        }
    }
    SnellTree {
        n_nodes,
        g,
        d: disc,
        children,
        root: 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Lean `mkt2` — a COMPLETE market (bond `(1,1)`@1, stock `(2,0)`@1), the
    /// digital call `h=(1,0)`. Unique state price `(½,½)`; no-arbitrage price ½;
    /// replicating hedge `(0,½)` cost ½ — a TIGHT (gap 0) cert (`mkt2_cert_valid`).
    fn mkt2() -> Market {
        // instrument-major H: bond row (1,1), stock row (2,0).
        Market {
            n_scenarios: 2,
            n_instruments: 2,
            h_mat: vec![1.0, 1.0, 2.0, 0.0],
            a: vec![1.0, 1.0],
            h: vec![1.0, 0.0],
            epsilon: 1e-6,
        }
    }

    #[test]
    fn complete_market_prices_digital_call_at_half() {
        let market = mkt2();
        let PriceOutcome::Certified(cert) = solve_price_cert(&market) else {
            panic!("mkt2 is consistent — must certify");
        };
        // The Lean no-arbitrage price is ½.
        assert!(
            (cert.primal_price - 0.5).abs() < 1e-9,
            "price = {}",
            cert.primal_price
        );
        // Tight: gap ≈ 0 (superhedge cost equals the price).
        assert!(cert.gap.abs() < 1e-9, "gap = {}", cert.gap);
        let rep = cert.check();
        assert!(rep.valid, "mkt2 certificate must validate: {rep:?}");
        assert!(rep.pi_nonneg && rep.consistent && rep.superhedge && rep.gap_ok);
    }

    /// The `fhir` example instance — an INCOMPLETE market (3 scenarios, 2
    /// instruments): bond `[1,1,1]`@1, asset `[0,0.5,1]`@0.6, product
    /// `h=[0,0.2,0.8]`. Hand-solved upper price 0.48 at `π=(0.4,0,0.6)`, tight
    /// superhedge `y=(0,0.8)`. A genuine arbitrage-free INTERVAL (many consistent
    /// measures), the upper price is a real `max`.
    fn incomplete_market() -> Market {
        Market::from_scenario_major(
            3,
            2,
            &[1.0, 0.0, 1.0, 0.5, 1.0, 1.0], // scenario-major (matches fhir MatrixData)
            vec![1.0, 0.6],
            vec![0.0, 0.2, 0.8],
            1e-6,
        )
    }

    #[test]
    fn incomplete_market_upper_price_and_tight_hedge() {
        let market = incomplete_market();
        let PriceOutcome::Certified(cert) = solve_price_cert(&market) else {
            panic!("consistent incomplete market must certify");
        };
        assert!(
            (cert.primal_price - 0.48).abs() < 1e-9,
            "upper price = {} (expected 0.48)",
            cert.primal_price
        );
        assert!(cert.gap.abs() < 1e-9, "tight gap: {}", cert.gap);
        assert!(cert.check().valid, "cert must validate: {:?}", cert.check());
    }

    #[test]
    fn arbitrage_market_is_rejected() {
        // Two instruments with IDENTICAL payoff (1,1) but DIFFERENT marks (1 vs
        // 0.5) — a textbook arbitrage. No π ≥ 0 satisfies both Hπ=a rows, so there
        // is NO arbitrage-free price and NO certificate (mirrors piBad_inconsistent).
        let market = Market {
            n_scenarios: 2,
            n_instruments: 2,
            h_mat: vec![1.0, 1.0, 1.0, 1.0],
            a: vec![1.0, 0.5],
            h: vec![1.0, 0.0],
            epsilon: 1e-6,
        };
        assert!(matches!(solve_price_cert(&market), PriceOutcome::Arbitrage));
    }

    #[test]
    fn tampered_price_cert_is_rejected() {
        // A VALID cert whose π is corrupted (breaks consistency Hπ=a) must fail.
        let market = incomplete_market();
        let PriceOutcome::Certified(mut cert) = solve_price_cert(&market) else {
            panic!("must certify");
        };
        assert!(cert.check().valid);
        cert.pi[0] += 0.5; // break Hπ = a
        let rep = cert.check();
        assert!(!rep.consistent, "tampered π breaks calibration");
        assert!(!rep.valid, "tampered certificate must be rejected");
    }

    #[test]
    fn non_dominating_hedge_is_rejected() {
        // A cheaper "hedge" y=0 does NOT dominate the product payoff h → the
        // superhedge clause fails (mirrors yBad_not_superhedge / no_consistent_overprice).
        let market = incomplete_market();
        let PriceOutcome::Certified(mut cert) = solve_price_cert(&market) else {
            panic!("must certify");
        };
        cert.y = vec![0.0; market.n_instruments]; // empty hedge — pays 0 < h somewhere
        let rep = cert.check();
        assert!(!rep.superhedge, "the empty hedge cannot dominate h");
        assert!(!rep.valid);
    }

    /// The Lean `putTree` — one-step binomial American put, `g=(0,4,0)`, `d=1`,
    /// `pA=pB=½`. Worth 2 by HOLDING (continuation `2 > g₀ = 0`); envelope
    /// `V=(2,4,0)` (`putTree_value`, `putV_feasible`).
    fn put_tree() -> SnellTree {
        SnellTree {
            n_nodes: 3,
            g: vec![0.0, 4.0, 0.0],
            d: 1.0,
            children: vec![vec![(1, 0.5), (2, 0.5)], vec![], vec![]],
            root: 0,
        }
    }

    #[test]
    fn snell_one_step_values_by_holding() {
        let tree = put_tree();
        let cert = solve_snell_cert(&tree, 1e-9);
        assert!(
            (cert.root_value - 2.0).abs() < 1e-12,
            "value = {} (expected 2, by continuation)",
            cert.root_value
        );
        let rep = cert.check();
        assert!(rep.valid, "envelope must be Snell-feasible: {rep:?}");
        assert!(rep.dominates && rep.superharmonic);
    }

    #[test]
    fn snell_undervalue_is_rejected() {
        // A candidate claiming the option is worth 1 at the root fails
        // superharmonicity (continuation 2 > 1) — mirrors underValue_refused.
        let tree = put_tree();
        let cert = CertSnell::from_value(&tree, vec![1.0, 4.0, 0.0], 1e-9);
        let rep = cert.check();
        assert!(!rep.superharmonic, "undervalued root is not superharmonic");
        assert!(!rep.valid);
    }

    #[test]
    fn american_put_dominates_european_early_exercise() {
        // A multi-step recombining binomial American put. The American value is
        // ≥ its intrinsic value and the Snell certificate validates.
        let tree = american_put_binomial(100.0, 100.0, 0.05, 0.2, 1.0, 50, true);
        let cert = solve_snell_cert(&tree, 1e-9);
        let rep = cert.check();
        assert!(rep.valid, "binomial Snell cert must validate: {rep:?}");
        assert!(cert.root_value > 0.0, "at-the-money put has value");
        // Deep in-the-money: early exercise makes the American put worth ≥ intrinsic.
        let itm = american_put_binomial(60.0, 100.0, 0.05, 0.2, 1.0, 50, true);
        let icert = solve_snell_cert(&itm, 1e-9);
        assert!(
            icert.root_value >= 100.0 - 60.0 - 1e-9,
            "deep-ITM American put ≥ intrinsic 40: {}",
            icert.root_value
        );
        assert!(icert.check().valid);
    }
}

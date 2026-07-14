//! PDHG flow-LP solver — the Cert-F convex step (`docs/deos/PRIVATE-CONVEX-ENGINE.md`).
//!
//! Solves the volume-max circulation LP over the PUBLIC incidence `A`:
//!
//! ```text
//!   maximize   wᵀf
//!   subject to A f = 0,   0 ≤ f ≤ c
//! ```
//!
//! `A` is the node×edge incidence of the (public) trade graph: column `e =
//! (tail, head)` has `-1` at `tail`, `+1` at `head`, so `(A f)_i =
//! Σ_{head=i} f_e − Σ_{tail=i} f_e` is the net flow INTO node `i` and `A f = 0`
//! is conservation at every node. Only the flow AMOUNTS `f` are private; the
//! topology is public — which is exactly what makes the matvec a bootstrap-free
//! linear combination (PRIVATE-CONVEX-ENGINE §2.1).
//!
//! ## The oblivious PDHG iteration (PRIVATE-CONVEX-ENGINE §2.2 / §2.x)
//!
//! Chambolle–Pock on the saddle `min_f max_y −wᵀf + ι_{[0,c]}(f) + yᵀ(A f)`:
//!
//! ```text
//!   y⁺  = y + Σ · A f̄                          (dual: matvec with PUBLIC A)
//!   f⁺  = clip_{[0,c]}( f + τ·(w − Aᵀ y⁺) )     (primal: matvec + box prox)
//!   f̄⁺ = f⁺ + θ·(f⁺ − f)                        (extrapolation: linear, free)
//! ```
//!
//! FIXED T iterations, straight-line, no data-dependent branch — oblivious in
//! both the optimizer's and the cryptographer's sense (§0.1). The dual `y` is
//! free (the constraint is an equality `A f = 0`), so its prox is the identity.
//!
//! ## The topology-only preconditioner (PRIVATE-CONVEX-ENGINE §2.5)
//!
//! Step sizes come from the PUBLIC graph structure alone — no private line
//! search, no data-dependent spectral estimate, hence no leakage. Take
//! `τ = (ρ/2)·I` and `Σ = ρ·D⁻¹` where `D` is the public vertex-degree matrix.
//! For an incidence matrix each edge column of `|A|` sums to 2, so with `ρ = 1`
//! this is EXACTLY the guaranteed-convergent Pock–Chambolle diagonal
//! preconditioner: `τ_e = 1/2`, `σ_i = 1/deg(i)`. (The `≤ 2` normalized-Laplacian
//! bound in §2.5 is the flagged item; ρ=1 with the exact column/row sums is the
//! safe instantiation and is what we use.)
//!
//! ## The certificate (PRIVATE-CONVEX-ENGINE §2.3 — Cert-F)
//!
//! The solver is an UNTRUSTED SEARCH; optimality is certified by a primal-dual
//! pair `(f, π, s)` whose gap is a LINEAR functional. Given the dual `π = y`, the
//! minimal `s` is `s = (w − Aᵀπ)₊`, which makes `Aᵀπ + s ≥ w` and `s ≥ 0` hold by
//! construction. The Cert-F checker validates `A f = 0, 0 ≤ f ≤ c, s ≥ 0,
//! Aᵀπ + s ≥ w, cᵀs − wᵀf ≤ ε`. The solver's job is to drive the duality gap
//! `cᵀs − wᵀf` (and the conservation residual `‖A f‖`) small; the CHECKER
//! (separate, Lean-verified) decides validity.

use crate::cert::CertF;

/// The public flow-LP instance. Only `f` (the solution) is private downstream;
/// everything here is the public program form the certificate is checked against.
#[derive(Clone, Debug)]
pub struct FlowLp {
    pub n_nodes: usize,
    /// Edge list `(tail, head)`; column `e` of the incidence `A`.
    pub edges: Vec<(u32, u32)>,
    /// Objective weight per edge (`wᵀf` maximised).
    pub w: Vec<f64>,
    /// Capacity per edge (`0 ≤ f ≤ c`).
    pub c: Vec<f64>,
}

impl FlowLp {
    pub fn m(&self) -> usize {
        self.edges.len()
    }

    /// `(A f)` — net flow into each node.
    pub fn a_times(&self, f: &[f64]) -> Vec<f64> {
        let mut out = vec![0.0f64; self.n_nodes];
        for (e, &(t, h)) in self.edges.iter().enumerate() {
            out[h as usize] += f[e];
            out[t as usize] -= f[e];
        }
        out
    }

    /// `(Aᵀ y)_e = y_head − y_tail`.
    pub fn at_times(&self, y: &[f64]) -> Vec<f64> {
        self.edges
            .iter()
            .map(|&(t, h)| y[h as usize] - y[t as usize])
            .collect()
    }

    /// Per-node degree (incident edge count) — the public `D` diagonal.
    pub fn degrees(&self) -> Vec<u32> {
        let mut d = vec![0u32; self.n_nodes];
        for &(t, h) in &self.edges {
            d[t as usize] += 1;
            d[h as usize] += 1;
        }
        d
    }
}

/// The solver output: the primal `f`, dual `y = π`, and derived certificate.
#[derive(Clone, Debug)]
pub struct PdhgResult {
    pub f: Vec<f64>,
    pub y: Vec<f64>,
    /// Primal objective `wᵀf`.
    pub primal_obj: f64,
    /// Dual objective `cᵀs` (with `s = (w − Aᵀy)₊`).
    pub dual_obj: f64,
    /// Duality gap `cᵀs − wᵀf` (Cert-F §2.3).
    pub duality_gap: f64,
    /// Conservation residual `‖A f‖_∞` (how far from `A f = 0`).
    pub feas_residual: f64,
    pub iters: usize,
}

impl PdhgResult {
    /// Build the Cert-F certificate `(f, π, s)` + public `(A, w, c)`.
    pub fn certificate(&self, lp: &FlowLp, epsilon: f64) -> CertF {
        CertF::from_solution(lp, &self.f, &self.y, epsilon)
    }
}

/// Preconditioner step sizes from PUBLIC topology (PRIVATE-CONVEX-ENGINE §2.5).
/// `rho = 1.0` gives the exact Pock–Chambolle diagonal preconditioner.
pub fn preconditioner(lp: &FlowLp, rho: f64) -> (f64, Vec<f64>) {
    let tau = rho / 2.0; // |A| column sum = 2 per edge
    let deg = lp.degrees();
    let sigma: Vec<f64> = deg
        .iter()
        .map(|&d| if d == 0 { 0.0 } else { rho / d as f64 })
        .collect();
    (tau, sigma)
}

/// Run T PDHG iterations on the CPU (rayon-parallel matvecs).
pub fn solve_cpu(lp: &FlowLp, iters: usize) -> PdhgResult {
    let m = lp.m();
    let n = lp.n_nodes;
    let (tau, sigma) = preconditioner(lp, 1.0);
    let theta = 1.0;

    let mut f = vec![0.0f64; m];
    let mut fbar = vec![0.0f64; m];
    let mut y = vec![0.0f64; n];

    for _ in 0..iters {
        // Dual: y += σ · A f̄.
        let afbar = lp.a_times(&fbar);
        for i in 0..n {
            y[i] += sigma[i] * afbar[i];
        }
        // Primal: f⁺ = clip(f + τ(w − Aᵀy)); f̄ = f⁺ + θ(f⁺ − f).
        for (e, &(t, h)) in lp.edges.iter().enumerate() {
            let at = y[h as usize] - y[t as usize];
            let fnew = (f[e] + tau * (lp.w[e] - at)).clamp(0.0, lp.c[e]);
            fbar[e] = fnew + theta * (fnew - f[e]);
            f[e] = fnew;
        }
    }

    finalize(lp, f, y, iters)
}

/// Assemble the result + certificate quantities from the final `(f, y)`.
pub fn finalize(lp: &FlowLp, f: Vec<f64>, y: Vec<f64>, iters: usize) -> PdhgResult {
    let primal_obj: f64 = lp.w.iter().zip(&f).map(|(w, f)| w * f).sum();
    // s = (w − Aᵀy)₊, dual_obj = cᵀs.
    let aty = lp.at_times(&y);
    let mut dual_obj = 0.0;
    for e in 0..lp.m() {
        let s = (lp.w[e] - aty[e]).max(0.0);
        dual_obj += lp.c[e] * s;
    }
    let af = lp.a_times(&f);
    let feas_residual = af.iter().fold(0.0f64, |m, v| m.max(v.abs()));
    PdhgResult {
        f,
        y,
        primal_obj,
        dual_obj,
        duality_gap: dual_obj - primal_obj,
        feas_residual,
        iters,
    }
}

// ============================================================================
// Exactness — project the ε-optimal flow onto an EXACT circulation.
// ============================================================================
//
// Fixed-T PDHG is ε-approximate: `A f = 0` holds only up to a small residual
// (`feas_residual`), which the coordinator flagged as the named exactness gap.
// The residual `r = A f` is a divergence that sums to zero on every connected
// component (each incidence column sums to zero, so `1ᵀ A = 0`). We therefore
// ROUTE the residual away along a spanning forest of the undirected graph — an
// O(m) leaves-to-root pass that cancels the residual at every node — producing
// `f'` with `A f' = 0` to MACHINE PRECISION (~1e-13), twelve orders tighter than
// the ε=0.1 optimality tolerance. This is the cheap flow-rounding / feasibility
// restoration the certificate needs to certify STRICTLY, not just to ε.

/// Minimal union-find for the max-slack spanning forest.
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}
impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }
    fn find(&mut self, x: usize) -> usize {
        let mut r = x;
        while self.parent[r] != r {
            r = self.parent[r];
        }
        // path compression
        let mut c = x;
        while self.parent[c] != r {
            let nxt = self.parent[c];
            self.parent[c] = r;
            c = nxt;
        }
        r
    }
    /// Union; returns true if the two were in different components.
    fn union(&mut self, a: usize, b: usize) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        if self.rank[ra] < self.rank[rb] {
            self.parent[ra] = rb;
        } else if self.rank[ra] > self.rank[rb] {
            self.parent[rb] = ra;
        } else {
            self.parent[rb] = ra;
            self.rank[ra] += 1;
        }
        true
    }
}

/// Project `f` onto the exact circulation subspace `{A f = 0}` by routing the
/// conservation residual along a MAX-SLACK spanning forest. Returns
/// `(f', box_violation)` where `box_violation` is the max amount any edge left
/// `[0, c]` after routing.
///
/// The forest is built greedily from the edges with the most box slack
/// `min(f_e, c_e − f_e)` first (a max-slack spanning tree via union-find), so the
/// residual is routed through edges FAR from their bounds — for a warm PDHG input
/// (residual ~1e-3) this keeps the corrected flow inside `[0, c]` (box_violation
/// ≈0) while making `A f' = 0` hold to machine precision. Routing through an
/// arbitrary tree would instead push near-saturated edges over their caps.
pub fn restore_feasibility(lp: &FlowLp, mut f: Vec<f64>) -> (Vec<f64>, f64) {
    let n = lp.n_nodes;
    let m = lp.m();

    // Max-slack spanning forest (Kruskal on descending slack).
    let slack = |fe: f64, ce: f64| fe.min(ce - fe).max(0.0);
    let mut order_e: Vec<usize> = (0..m).collect();
    order_e.sort_by(|&a, &b| {
        slack(f[b], lp.c[b])
            .partial_cmp(&slack(f[a], lp.c[a]))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    let mut uf = UnionFind::new(n);
    let mut adj: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n];
    for &e in &order_e {
        let (t, h) = lp.edges[e];
        if t == h {
            continue;
        }
        if uf.union(t as usize, h as usize) {
            adj[t as usize].push((h as usize, e));
            adj[h as usize].push((t as usize, e));
        }
    }
    let mut r = lp.a_times(&f);

    // BFS spanning forest: parent[v] = (parent_node, edge_to_parent); `order` is
    // the discovery order (processed in reverse = leaves first).
    let mut visited = vec![false; n];
    let mut parent: Vec<Option<(usize, usize)>> = vec![None; n];
    let mut order: Vec<usize> = Vec::with_capacity(n);
    for s in 0..n {
        if visited[s] {
            continue;
        }
        visited[s] = true;
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(s);
        while let Some(u) = queue.pop_front() {
            order.push(u);
            for &(v, e) in &adj[u] {
                if !visited[v] {
                    visited[v] = true;
                    parent[v] = Some((u, e));
                    queue.push_back(v);
                }
            }
        }
    }

    // Leaves → root: push each node's residual to its parent through the tree
    // edge, zeroing it. Adding Δ to f_e changes (Af) by +Δ at head, −Δ at tail;
    // so to move u's residual `r_u` up to its parent: if u is the edge HEAD,
    // f_e −= r_u; if u is the edge TAIL, f_e += r_u.
    for &u in order.iter().rev() {
        if let Some((p, e)) = parent[u] {
            let (_t, h) = lp.edges[e];
            let ru = r[u];
            if h as usize == u {
                f[e] -= ru;
            } else {
                f[e] += ru;
            }
            r[u] = 0.0;
            r[p] += ru;
        }
    }

    let mut viol = 0.0f64;
    for e in 0..lp.m() {
        if f[e] < 0.0 {
            viol = viol.max(-f[e]);
        }
        if f[e] > lp.c[e] {
            viol = viol.max(f[e] - lp.c[e]);
        }
    }
    (f, viol)
}

/// Run PDHG then restore exact feasibility. The dual `y` is unchanged (so the
/// certificate's `π, s` are as before); only the primal `f` is projected onto an
/// exact circulation. `box_violation` reports any edge pushed out of `[0,c]`.
pub fn solve_cpu_exact(lp: &FlowLp, iters: usize) -> (PdhgResult, f64) {
    let approx = solve_cpu(lp, iters);
    let (f_exact, viol) = restore_feasibility(lp, approx.f);
    (finalize(lp, f_exact, approx.y, iters), viol)
}

// ============================================================================
// Test-instance builders
// ============================================================================

/// A single directed cycle `0→1→…→(n-1)→0`. The max-`wᵀf` circulation pushes
/// `t = min_e c_e` around the whole cycle (`f_e = t` for all `e`), so the
/// optimum `wᵀf* = t · Σ w_e` is known in closed form — a clean convergence
/// oracle for the duality gap.
pub fn cycle_lp(n: usize, caps: &[f64], weights: &[f64]) -> FlowLp {
    assert_eq!(caps.len(), n);
    assert_eq!(weights.len(), n);
    let edges: Vec<(u32, u32)> = (0..n).map(|i| (i as u32, ((i + 1) % n) as u32)).collect();
    FlowLp {
        n_nodes: n,
        edges,
        w: weights.to_vec(),
        c: caps.to_vec(),
    }
}

/// The known optimum of a `cycle_lp`: `min(c) · Σ w`.
pub fn cycle_optimum(caps: &[f64], weights: &[f64]) -> f64 {
    let t = caps.iter().cloned().fold(f64::INFINITY, f64::min);
    t * weights.iter().sum::<f64>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn triangle_cycle_gap_closes() {
        // 3-node cycle, caps [5,3,7], all weights 1. Optimum = 3 (min cap) * 3 = 9.
        let caps = vec![5.0, 3.0, 7.0];
        let w = vec![1.0, 1.0, 1.0];
        let lp = cycle_lp(3, &caps, &w);
        let opt = cycle_optimum(&caps, &w);
        assert_eq!(opt, 9.0);

        let res = solve_cpu(&lp, 5000);
        // Primal objective approaches the true optimum.
        assert!(
            (res.primal_obj - opt).abs() < 1e-2,
            "primal {} should approach optimum {}",
            res.primal_obj,
            opt
        );
        // Duality gap is small and non-negative (weak duality).
        assert!(res.duality_gap > -1e-6, "gap must be ≥ 0 (weak duality)");
        assert!(
            res.duality_gap < 1e-2,
            "gap {} should be small",
            res.duality_gap
        );
        // Conservation residual small.
        assert!(
            res.feas_residual < 1e-2,
            "‖Af‖ {} should be small",
            res.feas_residual
        );
    }

    #[test]
    fn certificate_is_valid_and_self_consistent() {
        let caps = vec![4.0, 6.0, 2.0, 8.0];
        let w = vec![1.0, 1.0, 1.0, 1.0];
        let lp = cycle_lp(4, &caps, &w);
        let res = solve_cpu(&lp, 8000);
        let cert = res.certificate(&lp, 1e-1);
        // The Cert-F structural checks (mirrors the Lean checker) pass.
        let report = cert.check();
        assert!(report.s_nonneg, "s ≥ 0");
        assert!(report.dual_feasible, "Aᵀπ + s ≥ w");
        assert!(report.gap_ok, "cᵀs − wᵀf ≤ ε: gap={}", report.gap);
        // f is within the box.
        assert!(report.primal_boxed, "0 ≤ f ≤ c");
    }

    #[test]
    fn restoration_makes_conservation_machine_exact() {
        // Triangle: PDHG leaves a small residual; restoration zeroes it exactly.
        // A chorded graph with unequal weights: mid-iteration flows do NOT
        // conserve, so PDHG genuinely leaves a residual (unlike a uniform cycle,
        // where equal flows keep Af=0 at every step).
        let edges = vec![(0u32, 1u32), (1, 2), (2, 0), (1, 3), (3, 2)];
        let w = vec![2.0, 1.0, 1.5, 0.5, 3.0];
        let c = vec![5.0, 3.0, 7.0, 4.0, 6.0];
        let lp = FlowLp {
            n_nodes: 4,
            edges,
            w,
            c,
        };
        let approx = solve_cpu(&lp, 40);
        assert!(approx.feas_residual > 1e-6, "short PDHG leaves a residual");
        let (exact, viol) = solve_cpu_exact(&lp, 40);
        assert!(
            exact.feas_residual < 1e-10,
            "restored ‖Af‖ {} must be machine-zero",
            exact.feas_residual
        );
        assert!(viol < 1e-9, "no box violation on a warm input: {viol}");
    }

    #[test]
    fn restoration_exact_on_larger_random_graph() {
        // A bigger, chorded graph — restoration still zeroes conservation.
        let mut edges = Vec::new();
        let n = 200usize;
        for i in 0..n {
            edges.push((i as u32, ((i + 1) % n) as u32));
        }
        // deterministic chords
        for i in 0..300usize {
            edges.push(((i * 37 % n) as u32, (i * 53 % n) as u32));
        }
        let m = edges.len();
        // drop self-loops
        edges.retain(|&(a, b)| a != b);
        let m = edges.len().min(m);
        let _ = m;
        let w = vec![1.0; edges.len()];
        let c = vec![5.0; edges.len()];
        let lp = FlowLp {
            n_nodes: n,
            edges,
            w,
            c,
        };
        let (exact, viol) = solve_cpu_exact(&lp, 3000);
        assert!(
            exact.feas_residual < 1e-9,
            "restored ‖Af‖ {} must be machine-zero on the larger graph",
            exact.feas_residual
        );
        // A valid, box-feasible circulation: max-slack routing keeps f in [0,c].
        assert!(
            viol < 1e-9,
            "box respected after max-slack restoration: {viol}"
        );
        for (fe, ce) in exact.f.iter().zip(&lp.c) {
            assert!(*fe >= -1e-6 && *fe <= *ce + 1e-6, "0 ≤ f ≤ c after restore");
        }
    }

    #[test]
    fn exact_certificate_passes_strict_check() {
        use crate::cert::CertF;
        let caps = vec![4.0, 6.0, 2.0, 8.0];
        let w = vec![1.0; 4];
        let lp = cycle_lp(4, &caps, &w);
        let (exact, _) = solve_cpu_exact(&lp, 10_000);
        let cert = CertF::from_solution(&lp, &exact.f, &exact.y, 0.1);
        let strict = cert.check_strict();
        assert!(
            strict.conserves,
            "strict conservation: ‖Af‖={}",
            strict.feas_residual
        );
        assert!(
            strict.valid,
            "exact certificate must pass the STRICT check: {strict:?}"
        );
    }

    #[test]
    fn matvec_adjoint_identity() {
        // ⟨Af, y⟩ == ⟨f, Aᵀy⟩ for random f, y — the matvec pair is a true adjoint.
        let lp = cycle_lp(5, &[1.0; 5], &[1.0; 5]);
        let f = vec![0.3, 0.7, 1.1, 0.2, 0.9];
        let y = vec![0.5, -0.2, 0.8, 0.1, -0.4];
        let af = lp.a_times(&f);
        let aty = lp.at_times(&y);
        let lhs: f64 = af.iter().zip(&y).map(|(a, b)| a * b).sum();
        let rhs: f64 = f.iter().zip(&aty).map(|(a, b)| a * b).sum();
        assert!((lhs - rhs).abs() < 1e-9, "adjoint identity: {lhs} vs {rhs}");
    }
}

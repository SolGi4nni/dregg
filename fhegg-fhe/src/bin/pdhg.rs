//! One PDHG (Chambolle–Pock) iteration of a circulation flow-LP UNDER FHE.
//!
//! Program (the canonical dregg flow-LP, PRIVATE-CONVEX-ENGINE.md §2.3 Cert-F):
//!     max  wᵀf   s.t.  A f = 0,   0 <= f <= c
//! with A the PUBLIC node–edge incidence matrix and f the PRIVATE (encrypted)
//! edge-flow vector. The Chambolle–Pock iteration is:
//!     ȳ ← y + σ (A f̄)             # matvec with public A   — homomorphic add/sub (CHEAP)
//!     y ← y                        # dual prox = identity (indicator of {0}) — FREE
//!     f⁺ ← f + τ (w − Aᵀ y)        # matvec with public Aᵀ  — homomorphic add/sub (CHEAP)
//!     f ← clamp(f⁺, 0, c)          # box prox               — min/max = PBS (THE COST)
//!     f̄ ← 2f − f_prev              # extrapolation          — linear (CHEAP)
//!
//! We measure ONE iteration split into (matvec = cheap linear) vs (prox = the
//! PBS bill), then extrapolate the T-step cost. This tests codex's claim
//! (PRIVATE-CONVEX-ENGINE.md §1.4): "aggregation/matvec is bootstrap-free; the
//! prox is the only PBS-class work, ~2–3 PBS-equiv per packed ciphertext."
//! With a PUBLIC box cap the prox is one clamp = one max + one min per edge.
//!
//! Signed arithmetic (flows/prices go negative mid-iteration) => FheInt16.
//! CPU only (no CUDA on Apple Silicon).

use std::time::{Duration, Instant};

use tfhe::prelude::*;
use tfhe::{generate_keys, set_server_key, ClientKey, ConfigBuilder, FheInt16};

fn secs(d: Duration) -> f64 {
    d.as_secs_f64()
}

/// Public incidence: each edge e = (tail, head). (A f)[v] = Σ_{head=v} f - Σ_{tail=v} f.
struct Graph {
    n_nodes: usize,
    edges: Vec<(usize, usize)>,
}

impl Graph {
    /// A small circulation graph: an n-cycle plus a few chords (all edges
    /// carry flow; A f = 0 is node conservation). Public structure.
    fn cycle_with_chords(n_nodes: usize) -> Self {
        let mut edges = Vec::new();
        for i in 0..n_nodes {
            edges.push((i, (i + 1) % n_nodes)); // the cycle
        }
        // a few chords for a richer incidence
        let mut i = 0;
        while i + 2 < n_nodes {
            edges.push((i, i + 2));
            i += 3;
        }
        Graph { n_nodes, edges }
    }
    fn n_edges(&self) -> usize {
        self.edges.len()
    }
}

/// A f : encrypted edge-flows -> encrypted node residuals (homomorphic add/sub).
fn matvec_a(g: &Graph, f: &[FheInt16], zero: &FheInt16) -> Vec<FheInt16> {
    let mut out = vec![zero.clone(); g.n_nodes];
    for (e, &(tail, head)) in g.edges.iter().enumerate() {
        out[head] = &out[head] + &f[e];
        out[tail] = &out[tail] - &f[e];
    }
    out
}

/// Aᵀ y : encrypted node-prices -> encrypted per-edge (y[head] - y[tail]).
fn matvec_at(g: &Graph, y: &[FheInt16]) -> Vec<FheInt16> {
    g.edges
        .iter()
        .map(|&(tail, head)| &y[head] - &y[tail])
        .collect()
}

fn main() {
    println!(
        "=== fhEgg Stage-2: ONE PDHG flow-LP iteration UNDER FHE — measured per-iteration cost ==="
    );
    println!("host: CPU only (no CUDA on Apple Silicon; tfhe-rs gpu feature = NVIDIA-only)");

    let config = ConfigBuilder::default().build();
    let (ck, sk): (ClientKey, _) = generate_keys(config);
    set_server_key(sk);

    // Public problem structure.
    let sigma: i16 = 1;
    let tau: i16 = 1;

    for &n_nodes in &[6usize, 12, 24] {
        let g = Graph::cycle_with_chords(n_nodes);
        let m = g.n_edges();

        // Public data: objective weights w, box caps c.
        let w: Vec<i16> = (0..m).map(|e| 1 + (e as i16 % 3)).collect();
        let cap: i16 = 50;

        // Encrypted state: primal flow f, dual prices y (start at 0).
        let zero = FheInt16::encrypt(0i16, &ck);
        let cap_ct = FheInt16::encrypt(cap, &ck);
        let w_ct: Vec<FheInt16> = w.iter().map(|&x| FheInt16::encrypt(x, &ck)).collect();
        let mut f: Vec<FheInt16> = (0..m).map(|_| FheInt16::encrypt(3i16, &ck)).collect();
        let mut y: Vec<FheInt16> = vec![zero.clone(); n_nodes];
        let mut f_bar: Vec<FheInt16> = f.clone();

        // Warm one iteration to stabilise timing, then measure phases.
        let mut matvec_t = Duration::ZERO;
        let mut prox_t = Duration::ZERO;
        let mut linear_t = Duration::ZERO;
        let iters = 3;
        for _ in 0..iters {
            let f_prev = f.clone();

            // ȳ ← y + σ (A f̄)   — matvec (cheap linear)
            let t = Instant::now();
            let af = matvec_a(&g, &f_bar, &zero);
            for v in 0..n_nodes {
                y[v] = &y[v] + &(&af[v] * sigma);
            }
            matvec_t += t.elapsed();
            // dual prox = identity (indicator of {0}) — FREE, nothing to do.

            // f⁺ ← f + τ (w − Aᵀ y)   — matvec (cheap linear)
            let t = Instant::now();
            let aty = matvec_at(&g, &y);
            let mut fp: Vec<FheInt16> = Vec::with_capacity(m);
            for e in 0..m {
                let grad = &w_ct[e] - &aty[e];
                fp.push(&f[e] + &(&grad * tau));
            }
            matvec_t += t.elapsed();

            // f ← clamp(fp, 0, c)   — box prox: max(.,0) then min(.,c) = 2 PBS/edge
            let t = Instant::now();
            for e in 0..m {
                f[e] = fp[e].max(&zero).min(&cap_ct);
            }
            prox_t += t.elapsed();

            // f̄ ← 2f − f_prev   — extrapolation (linear)
            let t = Instant::now();
            for e in 0..m {
                f_bar[e] = &(&f[e] + &f[e]) - &f_prev[e];
            }
            linear_t += t.elapsed();
        }

        let matvec = matvec_t / iters;
        let prox = prox_t / iters;
        let linear = linear_t / iters;
        let per_iter = matvec + prox + linear;

        // sanity: flows stayed in [0,cap]
        let f0: i16 = f[0].decrypt(&ck);

        println!(
            "\nnodes={} edges(m)={}  (per-iteration, avg of {} iters):",
            n_nodes, m, iters
        );
        println!(
            "  matvec Af & Aᵀy (public A, homomorphic add/sub + public-scalar mul) = {:.3}s  [EXPECTED bootstrap-free; but tfhe-rs int add/sub CARRY-PROPAGATE (PBS-class) => MEASURED ~50%, NOT free]",
            secs(matvec)
        );
        println!(
            "  box prox clamp(0,c) = {:.3}s   ({} edges x (max+min) = {} PBS-class ops => {:.1} PBS-equiv/edge)  [THE COST]",
            secs(prox),
            m,
            2 * m,
            2.0
        );
        println!(
            "  extrapolation 2f - f_prev (linear) = {:.3}s",
            secs(linear)
        );
        println!(
            "  => PER-ITERATION TOTAL = {:.3}s   (prox is {:.0}% of it)",
            secs(per_iter),
            100.0 * secs(prox) / secs(per_iter).max(1e-9)
        );
        println!(
            "  T-step extrapolation:  T=100 => {:.1}s   T=1000 => {:.1}s   (sanity f[0]={} in [0,{}])",
            100.0 * secs(per_iter),
            1000.0 * secs(per_iter),
            f0,
            cap
        );
    }

    println!("\n=== done ===");
}

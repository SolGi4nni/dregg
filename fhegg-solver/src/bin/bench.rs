//! fhEgg Stage-1 benchmark harness — REAL runs, honest numbers.
//!
//! Reports the actual envelope for the two solvers:
//!   - aggregation clearing: N = 100/1000/10⁴ orders, K = 100/1000 levels
//!     (CPU fold+scan+crossing vs wgpu histogram + CPU scan/crossing);
//!   - PDHG flow-LP: m edges × T iterations (CPU vs GPU resident loop), with the
//!     final duality gap for each run.
//!
//! Usage: `cargo run --release --bin fhegg-bench`

use fhegg_solver::cert::CertF;
use fhegg_solver::clearing::{allocate, clear, crossing, scan_curves, Order, Side};
use fhegg_solver::gpu::GpuContext;
use fhegg_solver::pdhg::{
    cycle_lp, cycle_optimum, restore_feasibility, solve_cpu, solve_cpu_exact, FlowLp,
};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::time::Instant;

fn best_of<F: FnMut() -> ()>(reps: u32, mut f: F) -> f64 {
    // warmup
    f();
    let mut best = f64::MAX;
    for _ in 0..reps {
        let t0 = Instant::now();
        f();
        best = best.min(t0.elapsed().as_secs_f64());
    }
    best
}

fn gen_orders(n: usize, k: usize, seed: u64) -> Vec<Order> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..n)
        .map(|_| {
            let side = if rng.gen_bool(0.5) {
                Side::Bid
            } else {
                Side::Ask
            };
            let qty = rng.gen_range(1..100u64);
            // Bids skew to higher limits, asks to lower, so the book clears.
            let limit = match side {
                Side::Bid => rng.gen_range(k / 3..k) as u32,
                Side::Ask => rng.gen_range(0..(2 * k) / 3) as u32,
            };
            Order { side, qty, limit }
        })
        .collect()
}

fn bench_clearing(gpu: &Option<GpuContext>) {
    println!("\n=== AGGREGATION CLEARING (fhEgg T=1) ===");
    println!(
        "{:>8} {:>6} {:>14} {:>14} {:>10} {:>10}",
        "N", "K", "CPU (µs)", "GPU-hist (µs)", "cleared", "price*"
    );
    for &n in &[100usize, 1000, 10_000] {
        for &k in &[100usize, 1000] {
            let orders = gen_orders(n, k, 0xF00D ^ (n as u64) ^ ((k as u64) << 20));

            // CPU: full fold + scan + crossing + allocation.
            let cpu_s = best_of(50, || {
                let c = clear(&orders, k);
                let _ = allocate(&orders, &c);
                std::hint::black_box(&c);
            });

            let c = clear(&orders, k);

            // GPU: histogram the fold on device, scan+cross on CPU.
            let gpu_us = if let Some(g) = gpu {
                let bids: (Vec<u32>, Vec<u32>) = orders
                    .iter()
                    .filter(|o| o.side == Side::Bid)
                    .map(|o| (o.limit, o.qty as u32))
                    .unzip();
                let asks: (Vec<u32>, Vec<u32>) = orders
                    .iter()
                    .filter(|o| o.side == Side::Ask)
                    .map(|o| (o.limit, o.qty as u32))
                    .unzip();
                let gpu_s = best_of(50, || {
                    let bh = g.histogram(&bids.0, &bids.1, k);
                    let ah = g.histogram(&asks.0, &asks.1, k);
                    let bh: Vec<u64> = bh.iter().map(|&x| x as u64).collect();
                    let ah: Vec<u64> = ah.iter().map(|&x| x as u64).collect();
                    let (d, s) = scan_curves(&bh, &ah);
                    let _ = crossing(&d, &s);
                });
                format!("{:>14.2}", gpu_s * 1e6)
            } else {
                format!("{:>14}", "n/a")
            };

            println!(
                "{:>8} {:>6} {:>14.2} {} {:>10} {:>10}",
                n,
                k,
                cpu_s * 1e6,
                gpu_us,
                c.cleared_volume,
                if c.crossed {
                    c.clearing_price as i64
                } else {
                    -1
                },
            );
        }
    }
    println!(
        "  (GPU-hist times INCLUDE dispatch+readback per call; the fold is O(N) \n   \
         additions — cheap enough that CPU wins until N is very large.)"
    );
}

/// A random connected-ish directed graph with a nontrivial circulation:
/// a Hamiltonian cycle (guarantees a feasible circulation) plus random chords.
fn gen_graph(n_nodes: usize, extra_edges: usize, seed: u64) -> FlowLp {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut edges: Vec<(u32, u32)> = Vec::new();
    for i in 0..n_nodes {
        edges.push((i as u32, ((i + 1) % n_nodes) as u32));
    }
    for _ in 0..extra_edges {
        let a = rng.gen_range(0..n_nodes) as u32;
        let mut b = rng.gen_range(0..n_nodes) as u32;
        if a == b {
            b = (b + 1) % n_nodes as u32;
        }
        edges.push((a, b));
    }
    let m = edges.len();
    let w: Vec<f64> = (0..m).map(|_| rng.gen_range(0.5..2.0)).collect();
    let c: Vec<f64> = (0..m).map(|_| rng.gen_range(1.0..10.0)).collect();
    FlowLp {
        n_nodes,
        edges,
        w,
        c,
    }
}

fn bench_pdhg(gpu: &Option<GpuContext>) {
    println!("\n=== PDHG FLOW-LP (Cert-F convex step) ===");
    println!(
        "{:>7} {:>7} {:>7} {:>12} {:>12} {:>12} {:>12}",
        "m", "T", "nodes", "CPU (ms)", "GPU (ms)", "gap (CPU)", "‖Af‖ (CPU)"
    );
    let configs = [
        (64usize, 1000usize, 16usize),
        (256, 2000, 64),
        (1024, 4000, 256),
        (4096, 4000, 1024),
        (16384, 4000, 4096),
    ];
    for &(m, t, n) in &configs {
        let extra = m.saturating_sub(n);
        let lp = gen_graph(n, extra, 0xBEEF ^ (m as u64));

        let cpu_s = best_of(3, || {
            let r = solve_cpu(&lp, t);
            std::hint::black_box(r.primal_obj);
        });
        let cpu_res = solve_cpu(&lp, t);

        let gpu_str = if let Some(g) = gpu {
            let gpu_s = best_of(3, || {
                let r = g.solve_pdhg(&lp, t);
                std::hint::black_box(r.primal_obj);
            });
            format!("{:>12.2}", gpu_s * 1e3)
        } else {
            format!("{:>12}", "n/a")
        };

        println!(
            "{:>7} {:>7} {:>7} {:>12.2} {} {:>12.2e} {:>12.2e}",
            lp.m(),
            t,
            n,
            cpu_s * 1e3,
            gpu_str,
            cpu_res.duality_gap,
            cpu_res.feas_residual,
        );
    }
}

fn bench_exactness() {
    println!("\n=== EXACTNESS: spanning-forest residual restoration ===");
    println!(
        "{:>7} {:>7} {:>16} {:>16} {:>14} {:>12}",
        "m", "nodes", "‖Af‖ before", "‖Af‖ after", "restore (µs)", "box viol"
    );
    for &(m, t, n) in &[
        (256usize, 2000usize, 64usize),
        (4096, 4000, 1024),
        (16384, 4000, 4096),
    ] {
        let extra = m.saturating_sub(n);
        let lp = gen_graph(n, extra, 0xBEEF ^ (m as u64));
        let approx = solve_cpu(&lp, t);
        let before = approx.feas_residual;
        let f = approx.f.clone();
        let restore_s = best_of(20, || {
            let _ = restore_feasibility(&lp, f.clone());
        });
        let (exact, viol) = solve_cpu_exact(&lp, t);
        println!(
            "{:>7} {:>7} {:>16.3e} {:>16.3e} {:>14.2} {:>12.2e}",
            lp.m(),
            n,
            before,
            exact.feas_residual,
            restore_s * 1e6,
            viol,
        );
    }
    println!(
        "  (restoration is O(m), zeroes conservation to machine precision — the\n   \
         primal becomes an EXACT box-feasible circulation, not ε-approximate.)"
    );
}

fn demonstrate_certificate() {
    println!("\n=== Cert-F CERTIFICATE OUTPUT (bridge to the Lean checker) ===");
    // A known-optimum triangle: caps [5,3,7], w=1 → optimum = 3*3 = 9.
    let caps = vec![5.0, 3.0, 7.0];
    let w = vec![1.0, 1.0, 1.0];
    let lp = cycle_lp(3, &caps, &w);
    let opt = cycle_optimum(&caps, &w);
    let (res, viol) = solve_cpu_exact(&lp, 20_000);
    let cert = CertF::from_solution(&lp, &res.f, &res.y, 0.05);
    let report = cert.check_strict();
    println!("  triangle LP (known optimum wᵀf* = {opt}), EXACT-restored:");
    println!("    primal wᵀf = {:.6}", cert.primal_obj);
    println!("    dual   cᵀs = {:.6}", cert.dual_obj);
    println!("    duality gap = {:.3e}", cert.duality_gap);
    println!(
        "    ‖Af‖_∞ (conservation residual) = {:.3e}  (box viol {:.1e})",
        cert.feas_residual, viol
    );
    println!(
        "    Cert-F STRICT checks: conserves={} boxed={} s≥0={} dual_feas={} gap≤ε={} => VALID={}",
        report.conserves,
        report.primal_boxed,
        report.s_nonneg,
        report.dual_feasible,
        report.gap_ok,
        report.valid
    );
    // Emit a compact slice of the JSON wire format.
    let json = cert.to_json();
    let head: String = json.lines().take(14).collect::<Vec<_>>().join("\n");
    println!(
        "  --- Cert-F JSON (head) ---\n{head}\n  ... ({} bytes total)",
        json.len()
    );
}

fn main() {
    println!("fhEgg Stage-1 solver benchmark (real runs)");
    let gpu = GpuContext::new();
    match &gpu {
        Some(g) => println!("GPU: {} [{}]", g.adapter_name, g.backend),
        None => println!("GPU: none (CPU-only run)"),
    }
    bench_clearing(&gpu);
    bench_pdhg(&gpu);
    bench_exactness();
    demonstrate_certificate();
}

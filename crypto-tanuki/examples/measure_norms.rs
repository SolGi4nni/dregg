//! Demonstrates the norm separation that enforces the threshold: an honest
//! `t`-of-`n` signature has a SHORT `(z, h)` (well within the acceptance
//! bounds), while a sub-threshold set — whose wrong Lagrange reconstruction
//! yields `s' ≠ s` — produces `(z, h)` of size `≈ q/2`, rejected by the bounds.
//!
//! Run: `cargo run --release --example measure_norms`

use crypto_tanuki::threshold::{keygen, run_ceremony, Params};

fn main() {
    let keys = keygen(&Params::reference(), b"tanuki-reference-master-seed-0001");
    let p = &keys.params;
    println!(
        "reference params: n={} t={} k={} ell={} rep={} omega={}",
        p.n, p.t, p.k, p.ell, p.rep, p.omega
    );
    println!(
        "acceptance bounds: z_bound={}  h_bound={}  (q/2 ≈ {})\n",
        p.z_bound,
        p.h_bound,
        crypto_tanuki::Q / 2
    );

    for (i, sub) in [[0usize, 1, 2], [0, 2, 4], [1, 3, 4]].iter().enumerate() {
        let (sig, _) = run_ceremony(&keys, sub, b"measure", format!("n{i}").as_bytes());
        println!(
            "honest 3-of-5 set {:?}: |z|inf = {:>6}   |h|inf = {:>6}",
            sub,
            sig.z.norm_inf(),
            sig.h.norm_inf()
        );
    }
    let (sig, _) = run_ceremony(&keys, &[0, 1], b"measure", b"sub");
    println!(
        "SUB-threshold set   [1, 2]: |z|inf = {:>6}   |h|inf = {:>6}  <-- exceeds bounds => REJECTED",
        sig.z.norm_inf(),
        sig.h.norm_inf()
    );
}

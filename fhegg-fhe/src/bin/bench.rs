//! NO-VIEWER FHE uniform-price clearing — the honest measured envelope.
//!
//! Builds real TFHE ciphertexts, clears homomorphically (nobody decrypts an
//! order), checks correctness vs the plaintext reference, and reports the
//! per-phase latency + op counts for N in {32,128,512}, K in {64,256}.
//!
//! CPU only. Apple Silicon has no CUDA, so the tfhe-rs `gpu` feature (which
//! targets NVIDIA/CUDA) does not apply here; the GPU column is reported as
//! N/A-on-this-host with the published Zama H100 speedup cited in the writeup.

use std::time::{Duration, Instant};

use fhegg_fhe::{fhe_clear, reference_clear, FheTiming, Order, Side};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tfhe::prelude::*;
use tfhe::{generate_keys, set_server_key, ClientKey, ConfigBuilder, FheUint16};

/// Per-config time budget. If a config's ESTIMATED full-run time (from the
/// measured per-op costs) exceeds this, we report the extrapolation instead of
/// running it, clearly labelled. Keeps the whole sweep bounded while every
/// number stays grounded in a real measured per-op cost.
const BUDGET_SECS: f64 = 900.0;

fn gen_orders(n: usize, k: usize, rng: &mut StdRng) -> Vec<Order> {
    // Balanced-ish book: half bids, half asks, random limits and small qtys.
    // Small qtys keep the aggregate sums inside u16 (max N*qty < 65535):
    // for N=512 we cap qty at 64 -> <= 32768.
    let qmax: u16 = if n >= 512 { 32 } else { 100 };
    (0..n)
        .map(|i| {
            let side = if i % 2 == 0 { Side::Bid } else { Side::Ask };
            Order {
                side,
                limit: rng.gen_range(0..k),
                qty: rng.gen_range(1..=qmax),
            }
        })
        .collect()
}

/// Measure raw per-op FHE costs once, so every config's numbers are grounded.
struct PerOp {
    encrypt: Duration,
    add: Duration,
    ge: Duration,
    select: Duration,
    decrypt: Duration,
    /// cost to sum 512 ciphertexts via the deferred-carry parallel sum (one
    /// aggregation bucket at N=512). Aggregation per bucket scales ~linearly
    /// in N, so we scale this for other N.
    sum512: Duration,
}

fn measure_per_op(ck: &ClientKey) -> PerOp {
    let reps = 16;
    // encrypt
    let t = Instant::now();
    let mut cts = Vec::new();
    for i in 0..reps {
        cts.push(FheUint16::encrypt((i as u16) * 3 + 1, ck));
    }
    let encrypt = t.elapsed() / reps as u32;

    let a = FheUint16::encrypt(12345u16, ck);
    let b = FheUint16::encrypt(6789u16, ck);
    let one = FheUint16::encrypt(1u16, ck);
    let zero = FheUint16::encrypt(0u16, ck);

    // add
    let t = Instant::now();
    let mut acc = zero.clone();
    for _ in 0..reps {
        acc = &acc + &a;
    }
    let add = t.elapsed() / reps as u32;
    let _ = &acc;

    // ge
    let t = Instant::now();
    let mut lastbool = a.ge(&b);
    for _ in 0..reps {
        lastbool = a.ge(&b);
    }
    let ge = t.elapsed() / reps as u32;

    // select (if_then_else) — the GE-bit -> {0,1} conversion in the crossing
    let t = Instant::now();
    for _ in 0..reps {
        let _s = lastbool.if_then_else(&one, &zero);
    }
    let select = t.elapsed() / reps as u32;

    // decrypt
    let t = Instant::now();
    for _ in 0..reps {
        let _: u16 = a.decrypt(ck);
    }
    let decrypt = t.elapsed() / reps as u32;

    // sum of 512 ciphertexts (one aggregation bucket at N=512) — the cheap
    // additive-aggregation primitive (deferred-carry parallel tree-sum).
    let col: Vec<FheUint16> = (0..512)
        .map(|i| FheUint16::encrypt((i % 30) as u16 + 1, ck))
        .collect();
    let refs: Vec<&FheUint16> = col.iter().collect();
    let t = Instant::now();
    let summed = FheUint16::sum(&refs);
    let sum512 = t.elapsed();
    let chk: u16 = summed.decrypt(ck);
    debug_assert!(chk > 0);

    PerOp {
        encrypt,
        add,
        ge,
        select,
        decrypt,
        sum512,
    }
}

fn secs(d: Duration) -> f64 {
    d.as_secs_f64()
}

fn agg_secs(n: usize, k: usize, po: &PerOp) -> f64 {
    // aggregation = 2*K buckets (demand+supply), each a sum of ~N/2 ciphertexts;
    // sum cost scales ~linearly in the element count vs the measured sum512.
    let per_bucket = secs(po.sum512) * ((n as f64 / 2.0) / 512.0);
    2.0 * k as f64 * per_bucket
}

fn estimate_secs(n: usize, k: usize, po: &PerOp) -> f64 {
    let nk = (n * k) as f64;
    let enc = nk * secs(po.encrypt);
    let agg = agg_secs(n, k, po);
    // crossing = K comparisons (ge) + K selects + a cheap sum of K bits
    let cross = (k as f64) * (secs(po.ge) + secs(po.select));
    enc + agg + cross
}

fn print_timing(tag: &str, t: &FheTiming, reference: &fhegg_fhe::ClearOutcome, ok: bool) {
    let ref_p = reference.p_star.map(|p| p as i64).unwrap_or(-1);
    println!(
        "  [{tag}] N={} K={}  p*_fhe={} p*_ref={} V*_fhe={} V*_ref={}  MATCH={}",
        t.n,
        t.k,
        t.p_star as i64,
        ref_p,
        t.v_star,
        reference.v_star,
        if ok { "YES" } else { "NO !!!" }
    );
    println!(
        "        encrypt(N*K={} cts) = {:.3}s | aggregate(adds={}) = {:.3}s | crossing(ge={}) = {:.3}s | decrypt-result = {:.4}s | TOTAL(clear only) = {:.3}s",
        t.n * t.k,
        secs(t.encrypt),
        t.add_ops,
        secs(t.aggregate),
        t.ge_ops,
        secs(t.crossing),
        secs(t.decrypt_result),
        secs(t.aggregate) + secs(t.crossing) + secs(t.decrypt_result),
    );
}

fn main() {
    println!("=== fhEgg Stage-2: NO-VIEWER FHE uniform-price clearing — measured envelope ===");
    println!(
        "host: CPU only (Apple Silicon has no CUDA; tfhe-rs gpu feature = NVIDIA-only, N/A here)"
    );

    let config = ConfigBuilder::default().build();
    println!(
        "params: tfhe-rs high-level API default (PARAM_MESSAGE_2_CARRY_2, >=128-bit IND-CPA-D)"
    );
    let t = Instant::now();
    let (ck, sk) = generate_keys(config);
    println!("keygen: {:.3}s", secs(t.elapsed()));
    set_server_key(sk);

    let po = measure_per_op(&ck);
    println!("\nper-op FHE costs (FheUint16, CPU, tfhe-rs internal rayon):");
    println!(
        "  encrypt = {:.3}ms | seq add (carry-propagating +) = {:.3}ms | ge(compare) = {:.3}ms | select = {:.3}ms | decrypt = {:.3}ms",
        secs(po.encrypt) * 1e3,
        secs(po.add) * 1e3,
        secs(po.ge) * 1e3,
        secs(po.select) * 1e3,
        secs(po.decrypt) * 1e3,
    );
    println!(
        "  sum of 512 cts (deferred-carry parallel tree-sum, ONE aggregation bucket) = {:.3}s  => effective {:.3}ms per input-add (vs {:.1}ms for the sequential +)",
        secs(po.sum512),
        secs(po.sum512) / 512.0 * 1e3,
        secs(po.add) * 1e3,
    );

    let configs = [
        (32usize, 64usize),
        (32, 256),
        (128, 64),
        (128, 256),
        (512, 64),
        (512, 256),
    ];

    println!("\n--- sweep (each config: full FHE clear + correctness check vs plaintext) ---");
    for &(n, k) in &configs {
        let mut rng = StdRng::seed_from_u64(0xF9E66 ^ ((n as u64) << 20) ^ (k as u64));
        let orders = gen_orders(n, k, &mut rng);
        let reference = reference_clear(&orders, k);

        let est = estimate_secs(n, k, &po);
        if est > BUDGET_SECS {
            // Extrapolate from measured per-op — labelled, not a real run.
            let enc = (n * k) as f64 * secs(po.encrypt);
            let agg = agg_secs(n, k, &po);
            let cross = k as f64 * (secs(po.ge) + secs(po.select));
            println!(
                "  [EXTRAPOLATED from measured per-op — exceeds {:.0}s budget] N={} K={}",
                BUDGET_SECS, n, k
            );
            println!(
                "        encrypt ~ {:.1}s | aggregate(2*K={} deferred-carry sums) ~ {:.1}s | crossing(K={} ge+select) ~ {:.1}s | est TOTAL clear ~ {:.1}s",
                enc,
                2 * k,
                agg,
                k,
                cross,
                agg + cross,
            );
            continue;
        }

        let t = fhe_clear(&orders, k, &ck);
        let ok_p = match reference.p_star {
            Some(p) => t.p_star == p,
            None => t.p_star == usize::MAX,
        };
        let ok = ok_p && t.v_star == reference.v_star;
        print_timing("run", &t, &reference, ok);
        if !ok {
            eprintln!("!!! CORRECTNESS FAILURE at N={} K={}", n, k);
        }
    }

    println!("\n=== done ===");
}

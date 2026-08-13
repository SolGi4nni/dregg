//! Correctness teeth for the WGSL MLE fold and the BFV -> BabyBear fusion seam.
//!
//! Three independent things are checked, because each is blind to the others' failure:
//!
//! 1. **Arithmetic.** The WGSL Montgomery multiply agrees with canonical BabyBear arithmetic on
//!    hostile inputs (0, 1, p-1, and a pseudorandom sweep).
//! 2. **Semantics.** One GPU round equals Plonky3's own `Poly::fix_prefix_var` at the workspace's
//!    pinned rev — an oracle written by someone else, so a shared misunderstanding of "the fold"
//!    between the kernel and this crate's CPU reference cannot pass.
//! 3. **The seam.** A real BFV `fold_resident` output, bridged on-device into a BabyBear table and
//!    folded, equals the same computation routed through a host download and re-upload. If FUSED
//!    and UNFUSED disagree, the fusion measurement is measuring two different computations and the
//!    benchmark's delta means nothing.
//!
//! Headless runners have no adapter; every GPU test prints an explicit SKIP line rather than
//! passing silently.

use fhegg_fhe::bfv_lean::{LeanCiphertext, RnsPoly, FOLD_MODULI};
use fhegg_fhe::gpu_arena::{arena, Arena};
use fhegg_fhe::mle_gpu::{
    assert_montgomery_constants, bridge_lanes_to_babybear, fixture_challenges, fixture_table,
    fold_mle_all, fold_mle_table, table_len_for_lanes, BABYBEAR_P,
};

use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_multilinear_util::poly::Poly;

fn skip(what: &str) -> bool {
    eprintln!("no wgpu adapter — {what} SKIPPED (headless runner)");
    true
}

fn synth_ct(seed: u64, degree: usize) -> LeanCiphertext {
    let mut s = seed;
    let mut next = || {
        s = s
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(17)
            .wrapping_add(1);
        s
    };
    let polys = (0..2)
        .map(|_| RnsPoly {
            rows: FOLD_MODULI
                .iter()
                .map(|&q| (0..degree).map(|_| next() % q).collect())
                .collect(),
        })
        .collect();
    LeanCiphertext {
        moduli: FOLD_MODULI.to_vec(),
        degree,
        level: 0,
        variable_time: false,
        polys,
        plain_bound: 1,
    }
}

fn lanes_of(ct: &LeanCiphertext) -> Vec<u64> {
    ct.polys
        .iter()
        .flat_map(|p| p.rows.iter().flat_map(|r| r.iter().copied()))
        .collect()
}

/// The host constants and the ones compiled into `mle_fold.wgsl` must be the same constants.
/// Independent of any adapter, so it runs headless too.
#[test]
fn montgomery_constants_do_not_drift() {
    assert_montgomery_constants();
}

/// SEMANTICS. One GPU round == Plonky3's `fix_prefix_var` == this crate's CPU reference.
///
/// `fix_prefix_var` splits at the midpoint and computes `r*(a1-a0)+a0` — the object a
/// `VariableOrder::Prefix` sumcheck folds, which is the mode `sumcheck-toy` runs.
#[test]
fn one_round_matches_plonky3_and_cpu_reference() {
    let Some(a) = arena() else {
        assert!(skip("MLE fold semantics"));
        return;
    };
    for log_len in [1usize, 4, 10, 16] {
        let len = 1usize << log_len;
        let evals = fixture_table(len, 0xC0FFEE ^ log_len as u64);
        let r = fixture_challenges(1, log_len as u64)[0];

        let cpu = fold_mle_table(&evals, r);

        let oracle = Poly::new(evals.iter().map(|&v| BabyBear::from_u32(v)).collect())
            .fix_prefix_var(BabyBear::from_u32(r));
        let oracle: Vec<u32> = oracle.iter().map(|v| v.as_canonical_u32()).collect();
        assert_eq!(
            cpu, oracle,
            "CPU reference disagrees with Plonky3 fix_prefix_var at len {len}"
        );

        let mut table = a.upload_table(&evals);
        a.mle_fold_rounds(&mut table, &[r]);
        let gpu = a.download_table(&table);
        assert_eq!(
            gpu, oracle,
            "WGSL MLE fold diverged from Plonky3 fix_prefix_var at len {len}"
        );
    }
}

/// ARITHMETIC. Hostile operands through the kernel's Montgomery path: the fold with `f0 = 0`
/// reduces to `r * f1`, so a length-2 table is a direct multiply oracle.
#[test]
fn montgomery_multiply_is_exact_on_hostile_operands() {
    let Some(a) = arena() else {
        assert!(skip("Montgomery arithmetic"));
        return;
    };
    let p = u64::from(BABYBEAR_P);
    let interesting = [
        0u32,
        1,
        2,
        BABYBEAR_P - 1,
        BABYBEAR_P - 2,
        1 << 15,
        1 << 16,
        (1 << 27) - 1,
        1 << 27,
        (1 << 30) - 1,
        1_000_000_007 % BABYBEAR_P,
        u32::try_from((1u64 << 31) % p).unwrap(),
    ];
    for &r in &interesting {
        // table = [0, v] for each v: f0 = 0, f1 = v, so the fold yields r*v mod p.
        let table: Vec<u32> = interesting.iter().flat_map(|&v| [0u32, v]).collect();
        // Length must be a power of two; `interesting` has 12 entries -> pad to 32 with zeros.
        let mut padded = table.clone();
        padded.resize(32, 0);
        let mut resident = a.upload_table(&padded);
        a.mle_fold_rounds(&mut resident, &[r]);
        let got = a.download_table(&resident);

        // With the fold variable as the HIGH bit, index i pairs with i + 16.
        for i in 0..16 {
            let f0 = u64::from(padded[i]);
            let f1 = u64::from(padded[i + 16]);
            let want = (f0 + u64::from(r) * ((f1 + p - f0) % p)) % p;
            assert_eq!(
                u64::from(got[i]),
                want,
                "Montgomery fold wrong at r={r} i={i} (f0={f0}, f1={f1})"
            );
        }
    }
}

/// A whole sumcheck's worth of folding — every variable bound, one submission — matches the CPU
/// reference applied round by round.
#[test]
fn full_fold_to_a_constant_matches_cpu() {
    let Some(a) = arena() else {
        assert!(skip("full MLE fold"));
        return;
    };
    for log_len in [1usize, 8, 14, 18] {
        let len = 1usize << log_len;
        let evals = fixture_table(len, 0xDEADBEEF ^ log_len as u64);
        let challenges = fixture_challenges(log_len, 0x1234 ^ log_len as u64);

        let cpu = fold_mle_all(&evals, &challenges);

        let mut table = a.upload_table(&evals);
        a.mle_fold_rounds(&mut table, &challenges);
        let gpu = a.download_table(&table);
        assert_eq!(gpu.len(), 1, "a full fold leaves one evaluation");
        assert_eq!(
            gpu[0], cpu,
            "WGSL full fold diverged from the CPU reference at 2^{log_len}"
        );
    }
}

/// THE SEAM, correctness half. The on-device bridge must produce exactly the host-side encoding of
/// the same downloaded ciphertext — otherwise FUSED and UNFUSED are not the same computation and
/// the benchmark compares apples to oranges.
#[test]
fn device_bridge_equals_host_encoding_of_the_same_fold() {
    let Some(a) = arena() else {
        assert!(skip("BFV->BabyBear bridge"));
        return;
    };
    // Small degree keeps the test fast; the encoding is per-lane so shape does not change it.
    let cts: Vec<_> = (0..5).map(|i| synth_ct(i + 1, 256)).collect();
    let uploaded = a.upload(&cts);
    let folded = a.fold_resident(&uploaded);

    let fused_table = a.bridge_to_babybear(&folded);
    let fused = a.download_table(&fused_table);

    let downloaded = a.download(&folded);
    assert_eq!(downloaded.len(), 1);
    let lanes = lanes_of(&downloaded[0]);
    let host = bridge_lanes_to_babybear(&lanes, table_len_for_lanes(lanes.len()));

    assert_eq!(
        fused.len(),
        host.len(),
        "device and host bridges disagree on table length"
    );
    assert_eq!(
        fused, host,
        "on-device bridge diverged from the host encoding of the same ciphertext"
    );
    assert!(
        host.iter().all(|&v| v < BABYBEAR_P),
        "bridge emitted a non-canonical BabyBear element"
    );

    // And the encoding is INJECTIVE: recombining the limbs returns the residue.
    for (i, &x) in lanes.iter().enumerate() {
        let back = u64::from(host[2 * i]) | (u64::from(host[2 * i + 1]) << 30);
        assert_eq!(back, x, "2-limb base-2^30 encoding is not injective at {i}");
    }
}

/// THE SEAM, end-to-end. Fused (never leaves the device) and unfused (download, re-upload) must
/// fold to the same field element.
#[test]
fn fused_and_unfused_pipelines_agree() {
    let Some(a) = arena() else {
        assert!(skip("fused/unfused parity"));
        return;
    };
    let cts: Vec<_> = (0..7).map(|i| synth_ct(i + 100, 512)).collect();
    let uploaded = a.upload(&cts);
    let folded = a.fold_resident(&uploaded);

    let lanes = folded.total_lanes();
    let table_len = table_len_for_lanes(lanes);
    let challenges = fixture_challenges(table_len.trailing_zeros() as usize, 0xFEED);

    // FUSED: bridge on device, fold on device, one readback.
    let mut fused_table = a.bridge_to_babybear(&folded);
    a.mle_fold_rounds(&mut fused_table, &challenges);
    let fused = a.download_table(&fused_table);

    // UNFUSED: the ciphertext comes back to the host, is encoded there, and goes up again.
    let downloaded = a.download(&folded);
    let host_table = bridge_lanes_to_babybear(&lanes_of(&downloaded[0]), table_len);
    let mut unfused_table = a.upload_table(&host_table);
    a.mle_fold_rounds(&mut unfused_table, &challenges);
    let unfused = a.download_table(&unfused_table);

    assert_eq!(fused, unfused, "fused and unfused pipelines disagree");
    assert_eq!(
        fused[0],
        fold_mle_all(&host_table, &challenges),
        "the fused pipeline disagrees with the pure-CPU reference over the same table"
    );
}

/// The arena is multi-pipeline: the BFV fold, the bridge, and the MLE fold all run against ONE
/// device and ONE queue, and the intermediate buffers are shared rather than copied through the
/// host. If a future refactor gives any of them its own device, `bridge_to_babybear` cannot bind a
/// `ResidentHandle`'s buffer at all — this test is the tripwire.
#[test]
fn one_arena_serves_three_pipelines_without_a_host_round_trip() {
    let Some(a) = arena() else {
        assert!(skip("multi-pipeline arena"));
        return;
    };
    let cts: Vec<_> = (0..3).map(|i| synth_ct(i + 7, 128)).collect();
    let folded = a.fold_resident(&a.upload(&cts));
    let mut table = a.bridge_to_babybear(&folded);
    let n_vars = table.len().trailing_zeros() as usize;
    a.mle_fold_rounds(&mut table, &fixture_challenges(n_vars, 9));
    assert_eq!(table.len(), 1);
    let _ = a.download_table(&table);
    // Constant on Arena rather than a free function: it must be reachable from the same type that
    // owns the pipeline compiled against it.
    assert_eq!(Arena::mle_montgomery_mu(), 2_013_265_919);
}

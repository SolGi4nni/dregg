//! The consolidation invariant, as a gate that can go red.
//!
//! This crate had **nine** `wgpu::Device`s in one process — `gpu_arena`, `bfv_gpu`, `bfv_ntt_gpu`,
//! `private_book_bfv_wgpu`, `tfhe_wgpu` (twice), `tfhe_ntt_wgpu`, `tfhe_blind_rotation_wgpu`,
//! `tfhe_blind_rotation_ntt_wgpu` — each behind its own `OnceLock`. Two wgpu devices cannot share a
//! buffer, so every cross-kernel hand-off was unreachable by construction and the measured fusion
//! win (2.7x–7.1x on traffic alone at 2^20–2^22) was unavailable at all nine sites.
//!
//! The property that fixed it is not "the code was edited"; it is **"there is exactly one place in
//! this crate that opens a device."** That is a property a future edit can silently break — a new
//! kernel written the way all nine were written compiles, passes its own tests, and is invisibly
//! unfusable. So it is asserted here rather than documented.

use std::sync::Arc;
use std::thread;

use fhegg_fhe::bfv_lean::{fold, LeanCiphertext, RnsPoly, FOLD_MODULI};
use fhegg_fhe::bfv_ntt_gpu::{transform_odd_rns_cpu, OddNttDirection, RnsNttEngine};
use fhegg_fhe::gpu_arena::arena;

/// The two bench binaries that still open their own device, and why each is not a kernel.
///
/// ⚑ This is a DEBT LEDGER, not a carve-out. It is spelled as an allow-list rather than "skip
/// `src/bin/`" so that a *new* device anywhere — bins included — goes red, and so that the
/// remaining two are visible in the gate itself instead of in a note nobody reads.
const KNOWN_PRIVATE_DEVICES: &[(&str, &str)] = &[
    (
        "bin/gpu_saturate.rs",
        "measures what a COLD device costs for one buffer create+upload ('attribution-scratch'); \
         handing it the warm shared device would change the quantity it exists to report, and it \
         never passes a buffer to anything",
    ),
    (
        "bin/ntt_four_step_bench.rs",
        "standalone four-step-NTT-as-GEMM experiment with its own engine; it hands no buffer to \
         another kernel. If that NTT graduates into a library kernel it must take the shared \
         device with it",
    ),
];

/// THE RATCHET. `wgpu::Adapter::request_device` may be called from exactly one module, plus the
/// named bench binaries above.
///
/// A source-level assertion is the honest shape for this one: the thing being protected is a
/// *structural* property of the crate, and there is no runtime handle that distinguishes "one
/// device shared by nine modules" from "nine devices" without every module exposing its device.
/// This goes red the moment a tenth device appears, which is the only moment that matters.
#[test]
fn only_gpu_device_may_open_a_wgpu_device() {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut offenders = Vec::new();
    let mut found: Vec<String> = Vec::new();
    let mut visited_gpu_device = false;

    let mut stack = vec![src.clone()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).expect("readable source directory") {
            let path = entry.expect("readable directory entry").path();
            if path.is_dir() {
                stack.push(path);
                continue;
            }
            if path.extension().and_then(|e| e.to_str()) != Some("rs") {
                continue;
            }
            let relative = path
                .strip_prefix(&src)
                .expect("source paths live under src/")
                .to_string_lossy()
                .replace('\\', "/");
            let text = std::fs::read_to_string(&path).expect("readable source file");
            // The CALL, not the word. Several migrated modules name `request_device` in a comment
            // explaining what they used to do, and a substring match reports those as offenders —
            // a gate that goes red for documenting its own history teaches people to delete the
            // documentation.
            if !text.contains(".request_device(") {
                continue;
            }
            if relative == "gpu_device.rs" {
                visited_gpu_device = true;
                continue;
            }
            found.push(relative.clone());
            if !KNOWN_PRIVATE_DEVICES
                .iter()
                .any(|(allowed, _)| *allowed == relative)
            {
                offenders.push(relative);
            }
        }
    }

    assert!(
        visited_gpu_device,
        "src/gpu_device.rs no longer calls request_device — the shared device provider is gone, \
         and whatever replaced it is not covered by this ratchet"
    );
    offenders.sort();
    assert!(
        offenders.is_empty(),
        "these modules open their own wgpu::Device again: {offenders:?}\n\
         Two wgpu devices cannot share a buffer, so a kernel with its own device cannot receive a \
         resident hand-off from any other kernel here — the fusion win is unavailable to it BY \
         CONSTRUCTION, not by omission. Take the device from `crate::gpu_device::shared_gpu()` and \
         keep only your own pipelines."
    );

    // Downward ratchet: an allowed entry that has been fixed (or deleted) must leave the ledger,
    // or the list slowly becomes a lie about work that is already done.
    let stale: Vec<_> = KNOWN_PRIVATE_DEVICES
        .iter()
        .map(|(path, _)| *path)
        .filter(|path| !found.iter().any(|f| f == path))
        .collect();
    assert!(
        stale.is_empty(),
        "these entries no longer open a device and must be removed from KNOWN_PRIVATE_DEVICES: \
         {stale:?}"
    );
}

/// The device provider answers once and answers the same thing. A second `arena()` must not stand
/// up a second device — the old `arena()` did exactly that, so two arenas in one process could not
/// exchange a handle either.
#[test]
fn two_arenas_share_one_device() {
    let (Some(first), Some(second)) = (arena(), arena()) else {
        eprintln!("no wgpu adapter — shared-device identity SKIPPED (headless runner)");
        return;
    };
    let shared = fhegg_fhe::gpu_device::shared_gpu().expect("an arena exists, so a device does");
    assert_eq!(
        first.device(),
        second.device(),
        "two arenas hold different devices — a handle from one cannot be bound by the other"
    );
    assert_eq!(
        first.device(),
        &shared.device,
        "the arena's device is not the crate's shared device"
    );
}

fn synth_poly(seed: u64, degree: usize) -> RnsPoly {
    let mut state = seed;
    RnsPoly {
        rows: FOLD_MODULI
            .iter()
            .map(|&q| {
                (0..degree)
                    .map(|i| {
                        state = state
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .rotate_left(17)
                            .wrapping_add(i as u64 + 1);
                        state % q
                    })
                    .collect()
            })
            .collect(),
    }
}

/// A BFV ciphertext is a PAIR of polynomials — `bfv_lean::fold` refuses any other poly count, so a
/// single-poly stand-in would fold fine on the GPU and have no CPU oracle to be checked against.
fn as_ciphertext(polys: [RnsPoly; 2], degree: usize) -> LeanCiphertext {
    LeanCiphertext {
        moduli: FOLD_MODULI.to_vec(),
        degree,
        level: 0,
        variable_time: false,
        polys: polys.to_vec(),
        plain_bound: 1,
    }
}

/// ⚑ THE HAZARD THE CONSOLIDATION INTRODUCED, under load.
///
/// wgpu error scopes are a stack on the *device*. Nine devices meant nine independent stacks; one
/// device means one, so two threads in two different kernels can interleave `push`/`pop` and each
/// pop the other's scope — a real validation error attributed to the wrong kernel while the guilty
/// one sees `None` and proceeds. `gpu_device::ValidationScope` serializes the whole push..pop
/// region and is reentrant per thread.
///
/// This test is the tooth for that: many threads, two different kernels, hammering the one device
/// at once. It fails by **hanging** if the guard is not reentrant (a kernel that nests scopes
/// deadlocks against itself) and by **mismatching** if a scope pop ever ate a sibling's error and
/// let a bad result through. Each thread checks its own answer against a CPU oracle, so a
/// cross-talk failure is a wrong value and not merely a missing diagnostic.
#[test]
fn concurrent_kernels_on_one_device_neither_deadlock_nor_cross_talk() {
    let Some(a) = arena() else {
        eprintln!("no wgpu adapter — concurrent shared-device tooth SKIPPED (headless runner)");
        return;
    };
    let a = Arc::new(a);
    let degree = 256;

    let handles: Vec<_> = (0..8u64)
        .map(|t| {
            let a = Arc::clone(&a);
            thread::spawn(move || {
                let engine = RnsNttEngine::new();
                for round in 0..4u64 {
                    let seed = 0xA11CE ^ (t * 97 + round);
                    if t % 2 == 0 {
                        // Kernel 1: the arena's RNS fold-add.
                        let cts: Vec<_> = (0..4)
                            .map(|i| {
                                as_ciphertext(
                                    [
                                        synth_poly(seed + 2 * i, degree),
                                        synth_poly(seed + 2 * i + 1, degree),
                                    ],
                                    degree,
                                )
                            })
                            .collect();
                        let expected = fold(&cts, 1 << 20).expect("CPU fold oracle");
                        let uploaded = a.upload(&cts);
                        let folded = a.fold_resident(&uploaded);
                        let got = a.download(&folded).pop().expect("one ciphertext");
                        assert_eq!(
                            got, expected,
                            "thread {t} round {round}: fold diverged under concurrent device use"
                        );
                    } else {
                        // Kernel 2: the BFV RNS-NTT, a different module's pipelines on the same
                        // device, opening its own validation scopes in its own hot path.
                        let input = synth_poly(seed, degree);
                        let expected =
                            transform_odd_rns_cpu(&input, &FOLD_MODULI, OddNttDirection::Forward)
                                .expect("CPU transform oracle");
                        let got = engine
                            .forward_odd(&input, &FOLD_MODULI)
                            .expect("forward odd NTT");
                        assert_eq!(
                            got.polynomial, expected,
                            "thread {t} round {round}: NTT diverged under concurrent device use"
                        );
                    }
                }
            })
        })
        .collect();

    for (i, handle) in handles.into_iter().enumerate() {
        handle
            .join()
            .unwrap_or_else(|_| panic!("thread {i} panicked under concurrent shared-device use"));
    }
}

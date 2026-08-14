//! The NTT -> fold seam: teeth for the hand-off the device consolidation made expressible.
//!
//! `bfv_ntt_gpu` and `gpu_arena` each stood up their own `wgpu::Device` until `gpu_device` landed.
//! Two wgpu devices cannot share a buffer, so "fold the NTT's output without bringing it home" was
//! not a missing feature — it was unreachable. These tests are the oracle for the seam that
//! replaced it, and they exist BEFORE any measurement uses it: a fusion benchmark whose two arms
//! compute different things measures nothing, and the way that happens silently is a layout or
//! bookkeeping mismatch at exactly this join.
//!
//! The bar is bit-equality against two independent references, because either alone is blind:
//!
//! 1. The **host round trip** — the same forward NTT through the deployed `forward_odd_batch`
//!    (readback, `LeanCiphertext` reassembly, re-upload), then the same fold. If the resident
//!    buffer's layout disagreed with what `bfv_fold.wgsl` reads, this diverges.
//! 2. The **pure CPU fold** of the CPU transform's output. If the two GPU paths shared a wrong idea
//!    of either the transform or the fold, they would agree with each other forever.

use fhegg_fhe::bfv_lean::{fold, LeanCiphertext, RnsPoly, FOLD_DEGREE, FOLD_MODULI};
use fhegg_fhe::bfv_ntt_gpu::{transform_odd_rns_cpu, OddNttDirection, RnsNttEngine};
use fhegg_fhe::gpu_arena::{arena, Arena};

/// Plaintext modulus for the wrap gate. Every synthetic ciphertext carries `plain_bound = 1`, so a
/// fold of `n` of them has bound `n` — far under this, and the gate stays quiet.
const PLAINTEXT_MODULUS: u64 = 1 << 20;

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
                        // Hostile lanes first: 0, 1, q-1 exercise the fold's conditional subtract.
                        match i {
                            0 => 0,
                            1 => 1,
                            2 => q - 1,
                            _ => state % q,
                        }
                    })
                    .collect()
            })
            .collect(),
    }
}

/// A PAIR of transformed polynomials, dressed as the ciphertext the arena folds.
///
/// A BFV ciphertext is two polynomials and `bfv_lean::fold` refuses any other poly count — so a
/// single-poly stand-in would fold perfectly well on the GPU and have no CPU oracle to be checked
/// against, which is the one thing these tests exist to have. The NTT batch is therefore always an
/// even number of polynomials, consumed two at a time; the buffer layout is unaffected, because
/// `[polynomial][rns row][coefficient]` is contiguous either way.
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

/// The batch's polynomials, paired into ciphertexts in buffer order.
fn pair_up(polys: Vec<RnsPoly>, degree: usize) -> Vec<LeanCiphertext> {
    assert_eq!(polys.len() % 2, 0, "an NTT batch pairs into ciphertexts");
    let mut iter = polys.into_iter();
    std::iter::from_fn(|| {
        let a = iter.next()?;
        let b = iter.next().expect("even batch");
        Some(as_ciphertext([a, b], degree))
    })
    .collect()
}

/// A shape template for `adopt_resident` — only its moduli/degree/poly-count are read.
fn shape_template(degree: usize) -> LeanCiphertext {
    as_ciphertext([synth_poly(1, degree), synth_poly(2, degree)], degree)
}

/// FUSED: the NTT's output buffer is adopted by the arena and folded where it already lies.
fn fused(a: &Arena, engine: &RnsNttEngine, inputs: &[RnsPoly], degree: usize) -> LeanCiphertext {
    let resident = engine
        .forward_odd_batch_resident(inputs, &FOLD_MODULI)
        .expect("resident forward NTT batch");
    let n_cts = inputs.len() / 2;
    let adopted = a.adopt_resident(
        resident.buffer,
        &shape_template(degree),
        n_cts,
        &vec![1u64; n_cts],
        &vec![false; n_cts],
    );
    let folded = a.fold_resident(&adopted);
    a.download(&folded).pop().expect("one folded ciphertext")
}

/// UNFUSED: the deployed path — the NTT reads back to the host, the host rebuilds ciphertexts, and
/// the arena uploads them again.
fn unfused(a: &Arena, engine: &RnsNttEngine, inputs: &[RnsPoly], degree: usize) -> LeanCiphertext {
    let transformed = engine
        .forward_odd_batch(inputs, &FOLD_MODULI)
        .expect("host-round-trip forward NTT batch");
    let cts = pair_up(transformed.polynomials, degree);
    let uploaded = a.upload(&cts);
    let folded = a.fold_resident(&uploaded);
    a.download(&folded).pop().expect("one folded ciphertext")
}

fn skip_without_gpu() -> Option<Arena> {
    match arena() {
        Some(a) => Some(a),
        None => {
            eprintln!("no wgpu adapter — NTT/fold fusion seam SKIPPED (headless runner)");
            None
        }
    }
}

/// THE SEAM TOOTH. A resident NTT output, folded in place, must equal the host round trip
/// bit-for-bit — and both must equal the CPU transform folded on the CPU.
#[test]
fn resident_ntt_output_folds_to_the_same_ciphertext_as_the_host_round_trip() {
    let Some(a) = skip_without_gpu() else { return };
    let engine = RnsNttEngine::new();
    if !engine.has_gpu() {
        eprintln!("no wgpu NTT backend — fusion seam SKIPPED");
        return;
    }

    for (n_polys, degree) in [(2usize, 256usize), (6, 1024), (8, FOLD_DEGREE)] {
        let inputs: Vec<_> = (0..n_polys)
            .map(|i| synth_poly(0x5EED ^ (i as u64 + 1), degree))
            .collect();

        // Reference 2, built first and from nobody's GPU: transform on the CPU, fold on the CPU.
        let cpu_transformed: Vec<_> = inputs
            .iter()
            .map(|p| {
                transform_odd_rns_cpu(p, &FOLD_MODULI, OddNttDirection::Forward)
                    .expect("CPU forward transform oracle")
            })
            .collect();
        let cpu =
            fold(&pair_up(cpu_transformed, degree), PLAINTEXT_MODULUS).expect("CPU fold oracle");

        let host_round_trip = unfused(&a, &engine, &inputs, degree);
        let resident = fused(&a, &engine, &inputs, degree);

        assert_eq!(
            resident, host_round_trip,
            "n={n_polys} degree={degree}: the adopted resident NTT buffer folded to a different \
             ciphertext than the same transform round-tripped through the host — the seam's \
             layout or bookkeeping is wrong, and any fusion measurement over it is meaningless"
        );
        assert_eq!(
            resident, cpu,
            "n={n_polys} degree={degree}: both GPU paths agree with each other and disagree with \
             the CPU transform-then-fold oracle"
        );
        a.clear_pool();
    }
}

/// The plaintext bound the caller hands `adopt_resident` must ride through the fold, so the wrap
/// gate downstream bites on an adopted set exactly as it does on an uploaded one. A seam that
/// dropped the bookkeeping would still fold correct residues and still pass the tooth above.
#[test]
fn adopted_bounds_survive_the_fold_and_still_arm_the_wrap_gate() {
    let Some(a) = skip_without_gpu() else { return };
    let engine = RnsNttEngine::new();
    if !engine.has_gpu() {
        eprintln!("no wgpu NTT backend — adopted-bounds tooth SKIPPED");
        return;
    }
    let degree = 256;
    // Eight polynomials = four ciphertexts.
    let inputs: Vec<_> = (0..8).map(|i| synth_poly(0xB0_0000 + i, degree)).collect();
    let resident = engine
        .forward_odd_batch_resident(&inputs, &FOLD_MODULI)
        .expect("resident forward NTT batch");
    // Four sets, each claiming a quarter of the plaintext budget. Their sum is the whole budget,
    // so the folded output must be refused by the same gate `fold` applies.
    let quarter = PLAINTEXT_MODULUS / 4;
    let adopted = a.adopt_resident(
        resident.buffer,
        &shape_template(degree),
        4,
        &[quarter; 4],
        &[false; 4],
    );
    let folded = a.fold_resident(&adopted);
    let downloaded = a.download(&folded).pop().expect("one folded ciphertext");
    assert_eq!(
        downloaded.plain_bound,
        quarter * 4,
        "the adopted per-set bounds must sum onto the downloaded ciphertext"
    );
    // And the summed bound is exactly the budget, which is what the downstream gate refuses.
    assert!(
        downloaded.plain_bound >= PLAINTEXT_MODULUS,
        "a fold that consumes the whole plaintext budget must be visible to the wrap gate"
    );
    a.clear_pool();
}

/// `adopt_resident` is fail-loud, not fail-quiet. A buffer whose size does not match the declared
/// shape would make the fold read lanes that are not there; the arena refuses instead.
#[test]
fn adopt_refuses_a_buffer_that_does_not_match_the_declared_shape() {
    let Some(a) = skip_without_gpu() else { return };
    let engine = RnsNttEngine::new();
    if !engine.has_gpu() {
        eprintln!("no wgpu NTT backend — adopt refusal tooth SKIPPED");
        return;
    }
    let degree = 256;
    // Six polynomials = three ciphertexts.
    let inputs: Vec<_> = (0..6).map(|i| synth_poly(0xDEAD + i, degree)).collect();
    let resident = engine
        .forward_odd_batch_resident(&inputs, &FOLD_MODULI)
        .expect("resident forward NTT batch");
    let shape = shape_template(degree);

    // The buffer holds 3 ciphertexts; claiming 4 is a size mismatch.
    let buffer = resident.buffer.clone();
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        a.adopt_resident(buffer, &shape, 4, &[1; 4], &[false; 4])
    }));
    assert!(
        refused.is_err(),
        "adopt_resident accepted a buffer of the wrong size — the fold would have read past the \
         lanes the producing kernel actually wrote"
    );

    // And the honest claim is accepted, so the refusal above is about the size and not about
    // adoption failing in general.
    let ok = a.adopt_resident(resident.buffer, &shape, 3, &[1; 3], &[false; 3]);
    assert_eq!(ok.n_ciphertexts(), 3);
    a.clear_pool();
}

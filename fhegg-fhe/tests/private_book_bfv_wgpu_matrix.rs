//! Exact validation matrix for the private-book prover's opt-in wgpu precompute.
//!
//! The kernel has no CPU fallback: production uses the CPU relation unless the
//! operator opts into wgpu, and an unavailable requested adapter fails closed.
//! These tests therefore skip capability-portably in the ordinary lane and bite
//! hard in the ignored hbox tooth.

#![cfg(feature = "amm-input-binding")]

use fhegg_fhe::private_book_bfv_wgpu::{adapter_name, precompute_signed_dots_wgpu, SignedDotShape};

#[derive(Clone, Copy)]
struct XorShift64(u64);

impl XorShift64 {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn sign_words(shape: SignedDotShape) -> usize {
    shape.degree.div_ceil(32)
}

fn sign_rows(shape: SignedDotShape) -> usize {
    shape.modulus_count * shape.sign_rows_per_modulus
}

fn cpu_signed_dots(shape: SignedDotShape, signs: &[u32], messages: &[u64]) -> Vec<i128> {
    let words = sign_words(shape);
    let mut output = Vec::with_capacity(sign_rows(shape) * shape.option_count);
    for row in 0..sign_rows(shape) {
        let modulus = row / shape.sign_rows_per_modulus;
        for option in 0..shape.option_count {
            let mut dot = 0i128;
            for coefficient in 0..shape.degree {
                let positive =
                    signs[row * words + coefficient / 32] & (1 << (coefficient % 32)) != 0;
                let value =
                    messages[(option * shape.modulus_count + modulus) * shape.degree + coefficient];
                dot += if positive {
                    i128::from(value)
                } else {
                    -i128::from(value)
                };
            }
            output.push(dot);
        }
    }
    output
}

fn fixture(shape: SignedDotShape, seed: u64) -> (Vec<u32>, Vec<u64>) {
    let mut rng = XorShift64(seed);
    let signs = (0..sign_rows(shape) * sign_words(shape))
        .map(|index| match index % 5 {
            0 => 0,
            1 => u32::MAX,
            _ => rng.next() as u32,
        })
        .collect();
    let q = 0x1_ffff_e0001u64;
    let messages = (0..shape.option_count * shape.modulus_count * shape.degree)
        .map(|index| match index % 9 {
            0 => 0,
            1 => 1,
            2 => q - 1,
            3 => u64::from(u32::MAX),
            4 => u64::from(u32::MAX) + 1,
            _ => rng.next() % q,
        })
        .collect();
    (signs, messages)
}

fn check_shape(shape: SignedDotShape, seed: u64, require_gpu: bool) {
    let (signs, messages) = fixture(shape, seed);
    let oracle = cpu_signed_dots(shape, &signs, &messages);
    match precompute_signed_dots_wgpu(shape, &signs, &messages) {
        Ok(actual) => assert_eq!(actual, oracle, "signed-dot CPU/wgpu parity"),
        Err(error) if !require_gpu && adapter_name().is_err() => {
            eprintln!("no wgpu adapter — private-book signed-dot parity SKIPPED: {error}")
        }
        Err(error) => panic!("private-book signed-dot wgpu failure: {error}"),
    }
}

#[test]
fn signed_dot_randomized_exact_matrix_or_explicit_capability_skip() {
    for (index, shape) in [
        SignedDotShape {
            degree: 1,
            modulus_count: 1,
            option_count: 1,
            sign_rows_per_modulus: 1,
        },
        SignedDotShape {
            degree: 31,
            modulus_count: 3,
            option_count: 5,
            sign_rows_per_modulus: 3,
        },
        SignedDotShape {
            degree: 32,
            modulus_count: 2,
            option_count: 7,
            sign_rows_per_modulus: 5,
        },
        SignedDotShape {
            degree: 257,
            modulus_count: 3,
            option_count: 11,
            sign_rows_per_modulus: 9,
        },
    ]
    .into_iter()
    .enumerate()
    {
        check_shape(shape, 0x51a7_0000 ^ index as u64, false);
    }
    eprintln!("private signed-dot matrix: 4 exact CPU-parity shapes");
}

#[test]
fn signed_dot_malformed_shapes_fail_before_dispatch() {
    let base = SignedDotShape {
        degree: 32,
        modulus_count: 3,
        option_count: 2,
        sign_rows_per_modulus: 2,
    };
    let (signs, messages) = fixture(base, 7);
    for (shape, signs, messages) in [
        (SignedDotShape { degree: 0, ..base }, vec![], vec![]),
        (
            SignedDotShape {
                modulus_count: 0,
                ..base
            },
            vec![],
            vec![],
        ),
        (base, signs[..signs.len() - 1].to_vec(), messages.clone()),
        (base, signs.clone(), messages[..messages.len() - 1].to_vec()),
    ] {
        let error = precompute_signed_dots_wgpu(shape, &signs, &messages)
            .expect_err("malformed signed-dot shape must fail");
        assert!(
            error.contains("invalid signed-dot shape or buffer length"),
            "unexpected refusal: {error}"
        );
    }
    eprintln!("private signed-dot preflight: 4 adversarial shape/buffer refusals");
}

#[test]
#[ignore = "hbox GPU tooth: requires the private-book signed-dot wgpu kernel"]
fn require_real_wgpu_private_book_signed_dot_residency() {
    let name = adapter_name().expect("no wgpu adapter for private-book signed-dot kernel");
    assert!(!name.is_empty());
    eprintln!(
        "hard private signed-dot backend: adapter={name}; shape=4096x3x128x512; exact_sign_adds=805306368"
    );
    check_shape(
        SignedDotShape {
            degree: 4096,
            modulus_count: 3,
            option_count: 128,
            // 128 transcript rounds x four hidden order rows: the exact
            // N4K4 proof-producer shape, not a reduced smoke fixture.
            sign_rows_per_modulus: 512,
        },
        0xbaaa_5eed,
        true,
    );
}

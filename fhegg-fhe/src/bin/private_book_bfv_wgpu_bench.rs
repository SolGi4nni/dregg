//! Full-shape benchmark and exact parity gate for the private-book BFV/R1CS
//! public message-table precompute.
//!
//! Run on the GPU host:
//! `cargo run --release -p fhegg-fhe --features amm-input-binding --bin private_book_bfv_wgpu_bench`

#[cfg(feature = "amm-input-binding")]
fn main() {
    use std::time::Instant;

    use fhegg_fhe::bfv_lean::FOLD_MODULI;
    use fhegg_fhe::private_book_bfv_wgpu::{
        adapter_name, precompute_signed_dots_wgpu, SignedDotShape,
    };

    const DEGREE: usize = 4096;
    const OPTIONS: usize = 128;
    const ROUNDS: usize = 128;
    const ORDERS: usize = 4;

    let shape = SignedDotShape {
        degree: DEGREE,
        modulus_count: FOLD_MODULI.len(),
        option_count: OPTIONS,
        sign_rows_per_modulus: ROUNDS * ORDERS,
    };
    let sign_words = DEGREE.div_ceil(32);
    let sign_rows = shape.modulus_count * shape.sign_rows_per_modulus;
    let mut state = 0x7261_6465_6d61_6368u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let signs: Vec<u32> = (0..sign_rows * sign_words).map(|_| next() as u32).collect();
    let mut messages = Vec::with_capacity(OPTIONS * FOLD_MODULI.len() * DEGREE);
    for _option in 0..OPTIONS {
        for &modulus in &FOLD_MODULI {
            messages.extend((0..DEGREE).map(|_| next() % modulus));
        }
    }

    let cpu_start = Instant::now();
    let cpu = cpu_dots(shape, &signs, &messages);
    let cpu_elapsed = cpu_start.elapsed();

    let adapter = adapter_name().unwrap_or_else(|error| {
        eprintln!("no usable wgpu adapter: {error}");
        std::process::exit(2);
    });
    let first_start = Instant::now();
    let first = precompute_signed_dots_wgpu(shape, &signs, &messages)
        .unwrap_or_else(|error| panic!("first wgpu precompute failed: {error}"));
    let first_elapsed = first_start.elapsed();
    assert_eq!(first, cpu, "first full-shape GPU result diverged from CPU");

    let warm_start = Instant::now();
    let warm = precompute_signed_dots_wgpu(shape, &signs, &messages)
        .unwrap_or_else(|error| panic!("warm wgpu precompute failed: {error}"));
    let warm_elapsed = warm_start.elapsed();
    assert_eq!(warm, cpu, "warm full-shape GPU result diverged from CPU");

    let operations = sign_rows as u64 * OPTIONS as u64 * DEGREE as u64;
    println!("adapter: {adapter}");
    println!(
        "shape: {sign_rows} sign rows x {OPTIONS} options x {DEGREE} = {operations} exact sign/add operations"
    );
    println!("CPU exact dots:     {:.3} s", cpu_elapsed.as_secs_f64());
    println!("wgpu first batch:   {:.3} s", first_elapsed.as_secs_f64());
    println!("wgpu warm batch:    {:.3} s", warm_elapsed.as_secs_f64());
    println!(
        "warm speedup:       {:.2}x",
        cpu_elapsed.as_secs_f64() / warm_elapsed.as_secs_f64()
    );
    println!("PARITY: all {} i128 dots exact", cpu.len());
}

#[cfg(feature = "amm-input-binding")]
fn cpu_dots(
    shape: fhegg_fhe::private_book_bfv_wgpu::SignedDotShape,
    signs: &[u32],
    messages: &[u64],
) -> Vec<i128> {
    let sign_words = shape.degree.div_ceil(32);
    let sign_rows = shape.modulus_count * shape.sign_rows_per_modulus;
    let mut out = Vec::with_capacity(sign_rows * shape.option_count);
    for row in 0..sign_rows {
        let modulus = row / shape.sign_rows_per_modulus;
        for option in 0..shape.option_count {
            let mut dot = 0i128;
            for coefficient in 0..shape.degree {
                let positive =
                    signs[row * sign_words + coefficient / 32] & (1 << (coefficient % 32)) != 0;
                let value =
                    messages[(option * shape.modulus_count + modulus) * shape.degree + coefficient];
                dot += if positive {
                    i128::from(value)
                } else {
                    -i128::from(value)
                };
            }
            out.push(dot);
        }
    }
    out
}

#[cfg(not(feature = "amm-input-binding"))]
fn main() {
    eprintln!("private_book_bfv_wgpu_bench requires --features amm-input-binding");
    std::process::exit(2);
}

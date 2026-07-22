//! Native no-proof evaluation baseline for the four Boolean skeletons.
//!
//! LLVM is free to optimize these ordinary Boolean expressions.  This is an
//! order-of-magnitude baseline for evaluating the logic after atoms are known,
//! not a source-vs-optimized compiler benchmark.

use std::hint::black_box;
use std::time::Instant;

const ITERATIONS: u64 = 10_000_000;
const SAMPLES: u64 = 25;

#[inline(always)]
fn admission_source(b: &[bool; 12]) -> bool {
    let common = b[0] && b[1] && b[2] && b[5] && b[6] && b[7] && b[8] && b[9] && b[10] && b[11];
    (common && b[3]) || (common && b[4])
}

#[inline(always)]
fn admission_optimized(b: &[bool; 12]) -> bool {
    let common = b[0] && b[1] && b[2] && b[5] && b[6] && b[7] && b[8] && b[9] && b[10] && b[11];
    common && (b[3] || b[4])
}

#[inline(always)]
fn branch_source(b: &[bool; 4]) -> bool {
    ((b[0] && b[1]) && b[2]) || ((b[0] && b[1]) && b[3])
}

#[inline(always)]
fn branch_optimized(b: &[bool; 4]) -> bool {
    b[0] && b[1] && (b[2] || b[3])
}

#[inline(always)]
fn strand(b: &[bool; 3]) -> bool {
    b[0] || b[1] || b[2]
}

fn time(label: &str, mut evaluate: impl FnMut() -> bool) {
    for sample in 0..SAMPLES {
        let start = Instant::now();
        let mut accumulator = false;
        for _ in 0..ITERATIONS {
            accumulator ^= black_box(evaluate());
        }
        let elapsed = start.elapsed().as_nanos();
        black_box(accumulator);
        println!("BASELINE,{label},{sample},{ITERATIONS},{elapsed}");
    }
}

fn main() {
    let admission = black_box([
        true, true, true, true, false, true, true, true, true, true, true, true,
    ]);
    let upgrade = black_box([true, true, false, true]);
    let clearance = black_box([true, true, true, false]);
    let strand_bits = black_box([true, false, false]);
    assert!(admission_source(&admission) && admission_optimized(&admission));
    assert!(branch_source(&upgrade) && branch_optimized(&upgrade));
    assert!(branch_source(&clearance) && branch_optimized(&clearance));
    assert!(strand(&strand_bits));
    println!(
        "META,kind=native_boolean_no_proof,iterations={ITERATIONS},samples={SAMPLES},black_box=true"
    );
    time("admission-source", || {
        admission_source(black_box(&admission))
    });
    time("admission-optimized", || {
        admission_optimized(black_box(&admission))
    });
    time("upgrade-source", || branch_source(black_box(&upgrade)));
    time("upgrade-optimized", || {
        branch_optimized(black_box(&upgrade))
    });
    time("clearance-source", || branch_source(black_box(&clearance)));
    time("clearance-optimized", || {
        branch_optimized(black_box(&clearance))
    });
    time("strand-source", || strand(black_box(&strand_bits)));
    time("strand-optimized", || strand(black_box(&strand_bits)));
}

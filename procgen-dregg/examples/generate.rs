//! Generate + print a dungeon from a committed seed, then re-generate it from the
//! committed seed alone and confirm byte-identity — the provably-fair,
//! reproducible pipeline, end to end.
//!
//!   cargo run -p procgen-dregg --example generate
//!   cargo run -p procgen-dregg --example generate -- 20260711   # a specific day

use attested_dm::{Severity, parse_dungeon, validate};
use procgen_dregg::{daily_seed, generate, regenerate};

fn main() {
    // Treat an optional CLI arg as a "day" — in production this stands in for a
    // committed epoch / beacon output. Here we hash it into a committed value.
    let day: u64 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(20_260_711);

    // A committed epoch value (in production: a public beacon output for the day).
    let mut epoch = [0u8; 32];
    epoch[..8].copy_from_slice(&day.to_le_bytes());
    let seed = daily_seed(&epoch);

    let dungeon = generate(&seed);

    println!("=== procgen-dregg — provably-fair dungeon ===");
    println!("day (epoch)         : {day}");
    println!("committed seed      : {}", hex(seed.as_bytes()));
    println!(
        "request commitment  : {}",
        hex(&dungeon.request_commitment())
    );
    println!(
        "transcript commit   : {}",
        hex(&dungeon.transcript_commitment())
    );
    println!("rooms               : {}", dungeon.room_count);
    println!();
    println!("{}", dungeon.source);

    // It is a first-class dungeon: parse + validate through the real engine.
    let world = parse_dungeon(&dungeon.source).expect("generated dungeon must parse");
    let errors = validate(&world)
        .into_iter()
        .filter(|i| i.severity == Severity::Error)
        .count();
    println!("--- attested-dm: parses OK, {errors} validator errors ---");

    // Reproducibility: re-generate from the committed seed alone.
    let again = regenerate(&seed);
    assert_eq!(
        again, dungeon.source,
        "re-generation must be byte-identical"
    );
    println!("--- re-generated from the committed seed: BYTE-IDENTICAL ---");
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

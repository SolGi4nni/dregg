//! Driving tests for procgen-dregg: the committed-seed pipeline PARSES + VALIDATES
//! through the real `attested_dm` DSL, is byte-identical on re-generation, and is
//! non-vacuous (a different seed yields a different dungeon).

use attested_dm::{Severity, parse_dungeon, validate};
use procgen_dregg::{
    CommittedSeed, DRAW_COUNT, MAX_ROOMS, MIN_ROOMS, daily_seed, dungeon_request, generate,
    regenerate, verify_generation,
};

fn seed(byte: u8) -> CommittedSeed {
    CommittedSeed::from_bytes([byte; 32])
}

/// A generated dungeon PARSES and VALIDATES with zero errors through the shipped
/// attested-dm engine — a first-class, sound, playable dungeon.
#[test]
fn generated_dungeon_parses_and_validates() {
    for b in 0u8..40 {
        let dungeon = generate(&seed(b));
        // fail-closed parse: refuses dangling exits, unreachable objectives, …
        let world = parse_dungeon(&dungeon.source).unwrap_or_else(|e| {
            panic!(
                "seed {b}: generated dungeon failed to parse: {e}\n---\n{}",
                dungeon.source
            )
        });
        // and validate() reports NO errors (belt-and-suspenders over parse_dungeon).
        let issues = validate(&world);
        let errors: Vec<_> = issues
            .iter()
            .filter(|i| i.severity == Severity::Error)
            .collect();
        assert!(
            errors.is_empty(),
            "seed {b}: validator errors: {errors:?}\n---\n{}",
            dungeon.source
        );

        assert!(dungeon.room_count >= MIN_ROOMS && dungeon.room_count <= MAX_ROOMS);
        // The world has at least one gated exit (the DSL keyword `requires`).
        assert!(
            dungeon.source.contains("requires item"),
            "seed {b}: no gated exit emitted"
        );
    }
}

/// Reproducibility: the SAME committed seed yields byte-identical output.
#[test]
fn same_seed_is_byte_identical() {
    for b in [0u8, 7, 42, 200, 255] {
        let a = generate(&seed(b)).source;
        let c = regenerate(&seed(b));
        assert_eq!(a, c, "seed {b}: re-generation diverged");
    }
}

/// Non-vacuity: DIFFERENT seeds yield DIFFERENT dungeons (the generator actually
/// consumes the draw stream). If they were all identical, the reproducibility
/// test above would be meaningless.
#[test]
fn different_seeds_differ() {
    let a = generate(&seed(1)).source;
    let b = generate(&seed(2)).source;
    let c = generate(&seed(99)).source;
    assert_ne!(a, b);
    assert_ne!(a, c);
    assert_ne!(b, c);

    // A broad spread: across many seeds we see genuine variety, not two outputs.
    use std::collections::BTreeSet;
    let distinct: BTreeSet<String> = (0u8..60).map(|x| generate(&seed(x)).source).collect();
    assert!(
        distinct.len() > 20,
        "too little variety: {} distinct of 60",
        distinct.len()
    );
}

/// The seed commitment binds the dungeon: a verifier who holds the committed seed
/// and the evidence re-derives the seed through the pure dregg-dice verifier,
/// re-generates, and confirms byte-identity. A wrong seed is rejected.
#[test]
fn committed_seed_binds_the_dungeon() {
    let s = seed(123);
    let dungeon = generate(&s);
    assert!(
        verify_generation(&s, &dungeon.evidence, &dungeon.source),
        "honest dungeon must verify against its committed seed"
    );
    // A different seed's evidence must NOT verify this source.
    let other = generate(&seed(124));
    assert!(
        !verify_generation(&s, &other.evidence, &dungeon.source) || other.source == dungeon.source,
        "evidence from a different seed must not verify this source"
    );
    // And the honest source is NOT the honest source for a different seed.
    assert!(!verify_generation(
        &seed(124),
        &dungeon.evidence,
        &dungeon.source
    ));
}

/// The request commitment is the receipt-shaped value published BEFORE generation,
/// and it is stable for a given seed and moves for a different one.
#[test]
fn request_commitment_is_stable_and_binding() {
    let c1 = dungeon_request(&seed(5)).commitment();
    let c1b = dungeon_request(&seed(5)).commitment();
    let c2 = dungeon_request(&seed(6)).commitment();
    assert_eq!(c1, c1b);
    assert_ne!(c1, c2);
    // The transcript commitment likewise binds every draw.
    let d = generate(&seed(5));
    assert_eq!(
        d.transcript_commitment(),
        d.evidence.draw_transcript_commitment
    );
}

/// The draw stream is the REAL dregg-dice reject-free unbiased one: the fixed
/// DRAW_COUNT is bound into the request, and every legal index is drawable while
/// an out-of-range index is refused (not silently reused).
#[test]
fn draws_are_the_real_dregg_dice_stream() {
    let s = seed(77);
    let req = dungeon_request(&s);
    assert_eq!(req.draw_count, DRAW_COUNT);

    // Reconstruct the verified stream and exercise the bounded, reject-free draw.
    let (_, _, stream) = procgen_dregg::verified_stream(&s);
    assert_eq!(stream.draw_count(), DRAW_COUNT);
    // Every legal index yields a bounded value; the boundary index is refused.
    for i in 0..DRAW_COUNT {
        let v = stream.draw_bounded(i, 20).expect("legal index");
        assert!(v < 20);
    }
    assert!(
        stream.draw_bounded(DRAW_COUNT, 20).is_err(),
        "out-of-range draw must be refused"
    );
    // A 1-based die is in range.
    let d20 = stream.draw_die(0, 20).unwrap();
    assert!((1..=20).contains(&d20));
}

/// The daily-seed helper: a committed epoch value yields a stable seed, and
/// distinct epochs yield distinct dungeons ("a new fair dungeon every day").
#[test]
fn daily_seed_gives_a_fresh_dungeon_per_epoch() {
    let epoch_a = [0xA5u8; 32];
    let epoch_b = [0xB6u8; 32];
    let s_a = daily_seed(&epoch_a);
    let s_a2 = daily_seed(&epoch_a);
    let s_b = daily_seed(&epoch_b);
    assert_eq!(s_a, s_a2, "same epoch -> same seed");
    assert_ne!(s_a, s_b, "different epoch -> different seed");

    let day_a = generate(&s_a);
    let day_b = generate(&s_b);
    parse_dungeon(&day_a.source).expect("daily dungeon A parses");
    parse_dungeon(&day_b.source).expect("daily dungeon B parses");
    assert_ne!(day_a.source, day_b.source, "a new day is a new dungeon");
    // Reproducible: re-derive the same day's dungeon from the same epoch.
    assert_eq!(day_a.source, generate(&daily_seed(&epoch_a)).source);
}

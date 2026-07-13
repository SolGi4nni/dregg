//! The drand-beacon → daily-seed wire, DRIVEN against a REAL published drand `quicknet`
//! round (genuine interop, not self-consistency).
//!
//! Proves the three properties "today's dungeon everyone plays" needs:
//!   1. a real beacon round VERIFIES, and a forged reveal is REFUSED (unpredictable-until-
//!      revealed: you cannot fabricate a favourable day);
//!   2. the same verified round gives the byte-IDENTICAL dungeon (identical world-wide +
//!      re-derivation check);
//!   3. a DIFFERENT day's beacon gives a DIFFERENT dungeon.

use procgen_dregg::beacon::{DailyBeacon, generate_daily, quicknet_round_for_utc_day};
use procgen_dregg::dregg_dice::{Beacon, BeaconSchedule, HashChainBeacon};

// A REAL, PUBLISHED drand `quicknet` round (the same vector the `dregg-dice` interop test
// pins). Source (drand public API):
//   round: https://api.drand.sh/52db9ba7…c84e971/public/1000000
//     -> signature  = 83ad29e4…88abe72 (G1, 48 bytes)
//     -> randomness = b22aad47…1440af3 (== SHA-256(signature))
const DRAND_QUICKNET_ROUND: u64 = 1_000_000;
const DRAND_QUICKNET_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

fn real_sig() -> Vec<u8> {
    hex::decode(DRAND_QUICKNET_SIG_HEX).expect("the published drand signature decodes")
}

#[test]
fn a_real_drand_round_seeds_todays_dungeon_and_re_derives_identically() {
    // The day's beacon opening from a REAL fetched drand round.
    let today = DailyBeacon::quicknet(DRAND_QUICKNET_ROUND, real_sig());

    // (1) It VERIFIES by the real BLS pairing check against the pinned quicknet group key.
    today
        .verify()
        .expect("a real published drand quicknet round must verify");

    // (2) It seeds today's dungeon; the SAME verified round re-derives the byte-IDENTICAL
    //     dungeon — what makes the day's world identical world-wide + verifiable.
    let seed = today
        .seed()
        .expect("a verified beacon yields the day's seed");
    let d1 = procgen_dregg::generate(&seed);
    let d2 = generate_daily(&today).expect("re-generate from the same verified beacon");
    assert_eq!(
        d1.source, d2.source,
        "the same verified beacon gives the byte-identical dungeon"
    );
    // A third party who re-derives from seed alone reproduces it too.
    assert_eq!(
        procgen_dregg::regenerate(&seed),
        d1.source,
        "re-derivation from the committed seed reproduces the dungeon byte-for-byte"
    );
    // The dungeon is a real, non-empty generated world.
    assert!(
        d1.source.contains("name:") && d1.room_count >= 4,
        "the beacon-seeded dungeon is a real generated world"
    );
}

#[test]
fn a_forged_reveal_is_refused_you_cannot_grind_a_favourable_day() {
    // Flip one bit of the threshold-BLS signature — a "forged reveal".
    let mut sig = real_sig();
    sig[0] ^= 0x01;
    let forged = DailyBeacon::quicknet(DRAND_QUICKNET_ROUND, sig);

    // The pairing check REFUSES it: the threshold group never signed it. So an attacker
    // cannot fabricate a favourable day's beacon output — the reveal is unforgeable.
    assert!(
        forged.verify().is_err(),
        "a forged beacon signature must fail the pairing check"
    );
    assert!(
        forged.seed().is_err(),
        "no seed falls out of an unverifiable beacon (fail-closed)"
    );

    // And picking a WRONG round for the honest signature is refused too (no favourable-round
    // grind): quicknet is unchained, so a different round hashes to a different message.
    let wrong_round = DailyBeacon::quicknet(DRAND_QUICKNET_ROUND + 1, real_sig());
    assert!(
        wrong_round.verify().is_err(),
        "the honest signature at the wrong round must be refused"
    );
}

#[test]
fn a_different_days_beacon_gives_a_different_dungeon() {
    // Two DIFFERENT days → two different beacon rounds → (once fetched + verified) two
    // different outputs → two different seeds → two different dungeons. We drive the
    // output-divergence with two genuinely beacon-VERIFIED openings (hash-chain test
    // beacons at two rounds), so both legs are real verified beacon outputs.
    let make_day = |root: [u8; 32], round: u64| -> DailyBeacon {
        let schedule = BeaconSchedule {
            base_round: 1,
            stride: 1,
        };
        let b = HashChainBeacon::new(root, 128, b"the-descent/daily-test".to_vec(), schedule);
        let output = b.round_output(round);
        let day = DailyBeacon::from_parts(b.params(), round, output, Vec::new());
        day.verify().expect("the hash-chain day verifies");
        day
    };

    let day_a = make_day([0xA1; 32], 30);
    let day_b = make_day([0xA1; 32], 31); // same chain, a later day/round → different output

    let seed_a = day_a.seed().expect("day A seed");
    let seed_b = day_b.seed().expect("day B seed");
    assert_ne!(
        seed_a.as_bytes(),
        seed_b.as_bytes(),
        "different days derive different committed seeds"
    );

    let dungeon_a = procgen_dregg::generate(&seed_a).source;
    let dungeon_b = procgen_dregg::generate(&seed_b).source;
    assert_ne!(
        dungeon_a, dungeon_b,
        "a different day's beacon gives a different dungeon"
    );

    // And the day→round map is a deterministic, un-grindable function of the date: two
    // different UTC days map to two different rounds.
    let r1 = quicknet_round_for_utc_day(19_800); // some day
    let r2 = quicknet_round_for_utc_day(19_801); // the next day
    assert_ne!(r1, r2, "consecutive days map to different beacon rounds");
    assert!(r2 > r1, "later day, later round");
}

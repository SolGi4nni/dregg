//! **THE WEB'S DAILY OPEN IS BEACON-BOUND — driven.**
//!
//! `dreggnet_web::descent::todays_day()` used to return the OFFLINE date-derived day
//! unconditionally, so the web board / `/descent/play` / leaderboard played a pre-computable world
//! while the catalog host it shares a process with minted relics under the verified beacon day —
//! two different worlds under one name. This canary drives the flip: with a verified beacon armed
//! (exactly as `arm_todays_descent_day` arms it), `todays_day()` resolves the BEACON day, and its
//! provenance root is the beacon-derived one — NOT the deploy-seed-derived root. A beacon that does
//! not verify binds NO day (fail-closed: it falls back to the honest offline day, never seeds a run
//! on a forged reveal).
//!
//! This is its own test binary on purpose: `set_web_live_beacon` writes a process-wide cell, so
//! isolating it keeps the offline-default unit tests (a different binary) uncontaminated.

use dreggnet_offerings::native_descent::{NativeDescentOffering, native_descent_run_day_seed};
use dreggnet_offerings::{Offering, SessionConfig};
use procgen_dregg::beacon::{DailyBeacon, current_utc_day, pinned_fallback_beacon};
use procgen_dregg::descent_day::{self, DaySource};

use dreggnet_web::descent::{set_web_live_beacon, todays_day};

/// A REAL published drand `quicknet` reveal with one signature byte flipped — it fails the BLS
/// pairing check, so no day derives from it.
fn forged_beacon() -> DailyBeacon {
    let good = pinned_fallback_beacon();
    let mut signature = good.signature.clone();
    signature[0] ^= 0x01;
    DailyBeacon::quicknet(good.round, signature)
}

/// The raw seed a browser hands the native offering (normalized to `1..=251` by `open`).
const RAW_SEED: u64 = 42;

#[test]
fn the_web_daily_open_is_beacon_bound_and_fails_closed_on_a_forged_reveal() {
    let today = current_utc_day();

    // Nothing armed yet ⇒ the honest offline day (the fail-closed default: a board can still show
    // a real daily rotation, it just is not a fresh reveal).
    let offline = todays_day();
    assert_eq!(
        offline.source,
        DaySource::OfflineDate,
        "with no beacon armed, today is the offline date-derived day"
    );

    // ── ARM A VERIFIED BEACON, exactly as `arm_todays_descent_day` does ───────────────────────
    // The pinned published round is a genuine BLS-verifiable drand reveal (what a live surface
    // serves, labeled, when the transport is down), so it drives the verify path with no egress.
    let beacon = pinned_fallback_beacon();
    let beacon_seed = beacon.seed().expect("the pinned published round verifies");
    set_web_live_beacon(today, beacon.clone());

    let day = todays_day();
    assert!(
        day.source.is_live_beacon(),
        "an armed verified beacon makes today a beacon day, not the offline date day"
    );
    assert_eq!(
        day.source,
        DaySource::Beacon {
            round: beacon.round
        },
        "the day names the very round it was sealed from"
    );
    assert_eq!(
        day.seed.as_bytes(),
        beacon_seed.as_bytes(),
        "the beacon day's seed is the verified beacon's seed"
    );
    assert_ne!(
        day.seed.as_bytes(),
        descent_day::offline_day(today).seed.as_bytes(),
        "the beacon world is NOT the offline world — the flip is a real world change"
    );

    // ⚑ THE PROVENANCE ROOT DIFFERS FROM THE DEPLOY-SEED-DERIVED ONE. A live open through the
    // catalog binding (`on_day`, the seed `todays_day` now resolves) deploys on the beacon day's
    // run day-seed; the old seed-derived open (`new()`) deploys on the pre-computable one.
    let live_session = NativeDescentOffering::on_day(day.seed)
        .open(SessionConfig::with_seed(RAW_SEED))
        .expect("the beacon-bound offering opens");
    let normalized_seed = live_session.export_record().seed;
    assert_eq!(
        live_session.day_seed(),
        &native_descent_run_day_seed(&day.seed, normalized_seed),
        "the live run deploys on the beacon day's run day-seed"
    );
    // The seed-derived open (`new()`, the OLD posture) deploys on the pre-computable
    // deploy-seed-derived root for the same raw seed — a strictly different provenance.
    let seed_derived_session = NativeDescentOffering::new()
        .open(SessionConfig::with_seed(RAW_SEED))
        .expect("the seed-derived offering opens");
    assert_ne!(
        live_session.day_seed().as_bytes(),
        seed_derived_session.day_seed().as_bytes(),
        "a live run must NOT mint under the pre-computable deploy-seed-derived root"
    );
    assert_ne!(
        live_session.root(),
        seed_derived_session.root(),
        "the day-seed is folded into the genesis root, so the whole chain moves with the beacon"
    );

    // ── A FORGED REVEAL BINDS NO DAY ─────────────────────────────────────────────────────────
    // `beacon_day` runs the BLS pairing check first, so a mutated signature yields no day and
    // `todays_day` falls back to the honest offline day — it never seeds a run on a forged reveal.
    set_web_live_beacon(today, forged_beacon());
    assert_eq!(
        todays_day().source,
        DaySource::OfflineDate,
        "a forged armed beacon does not verify, so today degrades to the offline day (fail-closed)"
    );
}

//! ⚑ THE LIVE DAILY OPEN IS BEACON-BOUND — driven through the registration path itself.
//!
//! `dreggnet-offerings` proved that a Descent bound to a verified beacon mints banked relics
//! whose provenance replays to the run (`native_descent_banked_relics.rs`). What it could not
//! prove is that any LIVE surface actually opens that way: web, Telegram and WeChat all register
//! through [`dreggnet_catalog::register_games`], and that registration used to hand the host a
//! plain `NativeDescentOffering::new()` — the reproducible, deploy-seed-derived provenance root,
//! which anyone can compute in advance for every seed. This file drives the seam that changed.
//!
//! Everything here runs against the EXACT objects the frontends mount:
//! [`CatalogConfig::live`] (what `dreggnet_web::web_catalog_config`,
//! `dreggnet_telegram::host::telegram_default_host` and
//! `dreggnet_wechat::host::wechat_default_host` now build), its
//! [`CatalogConfig::native_descent`] (what `register_games` registers), and
//! [`full_catalog_host`] itself.
//!
//! The whole day-binding story is ONE `#[test]`: the published day is process-wide state, so
//! sequencing the "no day yet" and "day published" phases inside one test is what keeps them
//! from racing each other across parallel test threads.

use dreggnet_catalog::{
    CatalogConfig, DescentDayBinding, full_catalog_host, publish_todays_descent_day,
    todays_descent_day,
};
use dreggnet_offerings::native_descent::{NativeDescentOffering, native_descent_run_day_seed};
use dreggnet_offerings::{Offering, SessionConfig};
use dungeon_on_dregg::descent::day_seed_from_deploy_seed;
use procgen_dregg::beacon::{
    DailyBeacon, PINNED_FALLBACK_ROUND, PINNED_FALLBACK_SIG_HEX, current_utc_day,
    pinned_fallback_beacon,
};

/// The raw seed the surfaces hand `SessionConfig` (a channel id / session id); the Offering
/// normalizes it to `1..=251` exactly as it does on every frontend.
const RAW_SEED: u64 = 0xD1_5C_0A_7D;

/// The normalized deploy seed `RAW_SEED` lands on — `(raw % 251) + 1`, the Offering's canonical
/// normalization, restated here so the expected provenance roots are computed the same way the
/// Offering computes them rather than read back off it.
fn normalized_seed() -> u8 {
    ((RAW_SEED % 251) + 1) as u8
}

/// A REAL published drand `quicknet` reveal with one signature byte flipped — it does not pass
/// the BLS pairing check against the pinned group key, so nothing may be derived from it.
fn forged_beacon() -> DailyBeacon {
    let mut signature = hex::decode(PINNED_FALLBACK_SIG_HEX).expect("the pinned signature decodes");
    signature[0] ^= 0x01;
    DailyBeacon::quicknet(PINNED_FALLBACK_ROUND, signature)
}

#[test]
fn the_live_catalog_opens_the_descent_on_the_verified_beacon_day_and_fails_closed_without_one() {
    let seed = normalized_seed();

    // ── 1. The live config declares the live binding, and it is NOT the default ──────────────
    let live = CatalogConfig::live(Vec::new());
    assert!(
        matches!(live.descent_day, DescentDayBinding::Live(_)),
        "CatalogConfig::live must register the Descent against the LIVE day source"
    );
    assert!(
        matches!(
            CatalogConfig::default().descent_day,
            DescentDayBinding::SeedDerived
        ),
        "a config nobody told about a beacon must NOT pretend it has one"
    );
    assert!(
        live.native_descent().is_day_bound(),
        "the offering `register_games` mounts must be day-bound"
    );

    // ── 2. NO DAY PUBLISHED ⇒ THE OPEN IS REFUSED ────────────────────────────────────────────
    // Fail-closed is the whole point: a live surface with no verified day must not quietly serve
    // the pre-computable deploy-seed-derived provenance root just because the beacon fetch has
    // not landed. (The cell starts empty; this runs before anything publishes.)
    assert!(
        todays_descent_day().is_none(),
        "no day may be resolved before one is published"
    );
    // `match`, not `expect_err`: a landed `NativeDescentSession` carries live game state and has no
    // `Debug`, so the test names the error arm directly rather than asking to format the Ok value.
    let refusal = match live
        .native_descent()
        .open(SessionConfig::with_seed(RAW_SEED))
    {
        Ok(_) => panic!("an unresolved live day must refuse to open"),
        Err(refusal) => refusal.to_string(),
    };
    assert!(
        refusal.contains("live daily beacon") && refusal.contains("refusing"),
        "the refusal must SAY it is refusing on the missing day, not fail vaguely: {refusal}"
    );
    let mut host = full_catalog_host(&live);
    assert!(
        host.open("descent").is_err(),
        "the registered host must refuse the same way — the offering it mounts IS this one"
    );

    // ── 3. A FORGED REVEAL PUBLISHES NOTHING ─────────────────────────────────────────────────
    // `DailyBeacon::seed` runs the BLS pairing check before it derives anything, so a mutated
    // signature yields no seed — and `publish_todays_descent_day` therefore installs no day.
    // You cannot install a forged day, and (step 2 having already refused) you cannot fall
    // through to a pre-computable one either.
    assert!(
        publish_todays_descent_day(current_utc_day(), &forged_beacon()).is_err(),
        "a reveal that does not verify must not publish a day"
    );
    assert!(
        todays_descent_day().is_none(),
        "a refused publish must leave NO day installed"
    );
    assert!(
        live.native_descent()
            .open(SessionConfig::with_seed(RAW_SEED))
            .is_err(),
        "a forged reveal leaves the live Descent exactly as closed as it was"
    );

    // ── 4. A VERIFIED REVEAL BINDS THE DAY ───────────────────────────────────────────────────
    // The pinned published round is a genuine BLS-verifiable drand reveal (it is what a live
    // surface serves when the transport is down, labeled as such), so it is the right reveal to
    // drive the verify path with offline.
    let beacon = pinned_fallback_beacon();
    let day = beacon.seed().expect("the pinned published round verifies");
    publish_todays_descent_day(current_utc_day(), &beacon).expect("a verified reveal publishes");
    assert_eq!(
        todays_descent_day(),
        Some(day),
        "the published day is what the live source resolves"
    );

    let session = live
        .native_descent()
        .open(SessionConfig::with_seed(RAW_SEED))
        .expect("a published verified day opens the live Descent");

    // ⚑ THE FLIP, STATED AS AN EQUALITY AND AN INEQUALITY. The run's provenance root — the seed
    // its banked relics' asset ids are content-addressed to — is the beacon-derived one, and is
    // NOT the deploy-seed-derived root the surfaces used to serve.
    assert_eq!(
        session.day_seed(),
        &native_descent_run_day_seed(&day, seed),
        "the live run must deploy on the beacon day's run day-seed"
    );
    assert_ne!(
        session.day_seed(),
        &day_seed_from_deploy_seed(seed),
        "a live run must NOT mint under the pre-computable deploy-seed-derived root"
    );

    // The root is folded into the genesis journal root, so the whole hash chain moves with it —
    // a beacon-bound run is not a seed-derived run wearing a different label.
    let seed_derived = NativeDescentOffering::new()
        .open(SessionConfig::with_seed(RAW_SEED))
        .expect("the seed-derived Descent opens");
    assert_ne!(
        session.root(),
        seed_derived.root(),
        "the day-seed is in the genesis root: the two runs' journals cannot start equal"
    );

    // And a DIFFERENT day is a different provenance root for the same world — which is what
    // "unique per day" means for the relic ids drawn from it.
    let other_day = procgen_dregg::CommittedSeed::from_bytes([0x5A; 32]);
    assert_ne!(
        native_descent_run_day_seed(&other_day, seed),
        native_descent_run_day_seed(&day, seed),
        "two days must not share one provenance root"
    );

    // ── 5. THE REGISTERED HOST OPENS IT TOO ──────────────────────────────────────────────────
    // Not a peer offering: `full_catalog_host` is the builder web/Telegram/WeChat all call, and
    // `descent-campaign` rides the same binding.
    let mut host = full_catalog_host(&live);
    host.open("descent")
        .expect("the live catalog host opens the Descent on the published day");
    host.open("descent-campaign")
        .expect("the campaign over the Descent rides the same day binding");

    // ── 6. THE DAY ROLLS ⇒ CLOSED AGAIN UNTIL THE NEXT REFRESH ───────────────────────────────
    // A published day is only today's. Serving yesterday's provenance root under today's play
    // would hand every relic id to anyone who played yesterday, so a stale day resolves to
    // nothing and the open refuses until the frontend's refresh publishes the new round.
    publish_todays_descent_day(current_utc_day() - 1, &beacon)
        .expect("publishing yesterday still verifies the reveal");
    assert!(
        todays_descent_day().is_none(),
        "a day that has rolled must not resolve"
    );
    assert!(
        live.native_descent()
            .open(SessionConfig::with_seed(RAW_SEED))
            .is_err(),
        "a stale day fails closed, exactly like no day at all"
    );

    // Leave the cell holding today's day so nothing else in this binary inherits a stale one.
    publish_todays_descent_day(current_utc_day(), &beacon).expect("re-arm today");
}

/// The seed-derived binding is still exactly what it was — the fixture/offline path did not move
/// when the live path did, and `Fixed` is the same root as the live source resolving that day.
#[test]
fn the_fixture_binding_is_unchanged_and_a_fixed_day_matches_the_live_one() {
    let seed = normalized_seed();

    let fixture = CatalogConfig::default().native_descent();
    assert!(
        !fixture.is_day_bound(),
        "the default binding names no day, and says so"
    );
    let session = fixture
        .open(SessionConfig::with_seed(RAW_SEED))
        .expect("the seed-derived Descent opens with no beacon at all");
    assert_eq!(
        session.day_seed(),
        &day_seed_from_deploy_seed(seed),
        "the reproducible fixture root is untouched"
    );

    let beacon = pinned_fallback_beacon();
    let day = beacon.seed().expect("the pinned published round verifies");
    let fixed = CatalogConfig::on_beacon(Vec::new(), &beacon).expect("a verified reveal pins");
    assert!(matches!(fixed.descent_day, DescentDayBinding::Fixed(_)));
    let pinned_session = fixed
        .native_descent()
        .open(SessionConfig::with_seed(RAW_SEED))
        .expect("a pinned day opens");
    assert_eq!(
        pinned_session.day_seed(),
        &native_descent_run_day_seed(&day, seed),
        "Fixed(day) and Live-resolving-day are the same provenance root"
    );

    assert!(
        CatalogConfig::on_beacon(Vec::new(), &forged_beacon()).is_err(),
        "a forged reveal pins no day either"
    );
}

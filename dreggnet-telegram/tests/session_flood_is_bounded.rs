//! **T1 DoS FALSIFIER — the deployed Telegram game-session host is BORN BOUNDED.**
//!
//! `dreggnet-telegram`'s `telegram_default_host` (the host every live bot spawns) used to return
//! `full_catalog_host(...)` with `SessionPolicy::is_unbounded()` — so `admit_fresh_open` skipped
//! every gate and ANY Telegram user opening games across chats minted durable sessions (memory AND
//! disk) without limit: PlayerWorlds's deployed sibling, un-armed. The fix arms a bounded
//! [`resolve_telegram_policy`] on it (capacity + idle-TTL + per-opener quota), mirroring
//! `dreggnet_web`'s `resolve_web_policy` / the capped `OfferingHost` path.
//!
//! These are the falsifiers, mirroring `dreggnet_catalog`'s
//! `a_flood_of_distinct_identities_never_grows_past_capacity`:
//! 1. the DEPLOYED construction path is bounded (`telegram_default_host(..).policy()` arms all
//!    three caps — no env required);
//! 2. under a flood of N ≫ cap distinct session ids the live-session map saturates at exactly the
//!    cap and never grows past it (bounded, LRU-evicted) — the anonymous open path (`ensure_open`,
//!    no attribution) the real bot drives.

use dreggnet_catalog::{CatalogConfig, full_catalog_host};
use dreggnet_offerings::{ManualClock, SessionId};
use dreggnet_telegram::host::{
    DEFAULT_TELEGRAM_MAX_SESSIONS, TELEGRAM_MAX_SESSIONS_ENV, resolve_telegram_policy,
    telegram_default_host, telegram_policy_from,
};

/// **The deployed host is never born unbounded.** The default policy (no env set) arms the three
/// caps the fix names — capacity, idle-TTL, and the per-opener quota — so
/// [`dreggnet_offerings::OfferingHost`]'s `admit_fresh_open` runs its gates rather than skipping
/// them. This is the exact property that was FALSE before the fix.
#[test]
fn the_default_telegram_policy_is_bounded_not_unbounded() {
    // Directly: the env-less resolver and the deployed host both carry an armed policy.
    let resolved = telegram_policy_from(|_| None);
    assert!(
        !resolved.is_unbounded(),
        "the default Telegram policy must be bounded, not unbounded: {resolved:?}"
    );
    assert!(
        resolved.max_sessions_per_offering.is_some(),
        "a per-offering capacity cap is armed"
    );
    assert!(
        resolved.idle_ttl_secs.is_some(),
        "an idle-TTL sweep is armed"
    );
    assert!(
        resolved.max_opens_per_actor.is_some(),
        "a per-opener fresh-mint quota is armed"
    );

    // The real process-env resolver (unset env in CI → the same bounded defaults) and the actual
    // deployed host constructor.
    assert!(!resolve_telegram_policy().is_unbounded());
    let host = telegram_default_host(vec![]);
    assert!(
        !host.policy().is_unbounded(),
        "telegram_default_host must arm a bounded policy on the live catalog host: {:?}",
        host.policy()
    );
    assert_eq!(
        host.policy().max_sessions_per_offering,
        Some(DEFAULT_TELEGRAM_MAX_SESSIONS)
    );
}

/// **THE DoS FALSIFIER** — a flood of distinct session ids (the anonymous `(offering, chat)` mint
/// vector: any user opening a game in a fresh chat) never grows the live-session map past the
/// per-offering cap. Built the way `telegram_default_host` builds — the SAME [`full_catalog_host`]
/// + [`telegram_policy_from`] policy — with a small cap injected through the env-shaped getter so
/// the flood is fast and deterministic. Opens go through `ensure_open` (no attribution), exactly
/// the real bot's open path, so it is the capacity cap + LRU eviction that bounds it.
#[test]
fn a_flood_of_distinct_sessions_never_grows_past_capacity() {
    let cap = 8usize;
    let policy =
        telegram_policy_from(|k| (k == TELEGRAM_MAX_SESSIONS_ENV).then(|| cap.to_string()));
    assert_eq!(policy.max_sessions_per_offering, Some(cap));

    // A manual clock keeps eviction deterministic; the catalog host holds the "dungeon" offering
    // (the Warden's Keep, offering #0) — an anonymous single-player surface that opens with no day
    // binding, unlike the descent games.
    let clock = ManualClock::new(1_000);
    let mut host =
        full_catalog_host(&CatalogConfig::live(vec![])).with_policy(policy, clock.clone());

    for n in 0..(cap * 6) {
        // Advance the clock each open so the LRU has a strict order to evict by.
        clock.advance(1);
        let id = SessionId::new(format!("flood-{n}"));
        host.ensure_open("dungeon", &id)
            .expect("an anonymous open lands (evicting the coldest at the cap)");
        assert!(
            host.session_ids("dungeon").len() <= cap,
            "the live-session map is hard-bounded at {cap}; saw {} after {} opens",
            host.session_ids("dungeon").len(),
            n + 1
        );
    }
    assert_eq!(
        host.session_ids("dungeon").len(),
        cap,
        "the map saturates at exactly its capacity, never beyond"
    );
}

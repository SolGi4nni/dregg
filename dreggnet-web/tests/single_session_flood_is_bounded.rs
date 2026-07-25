//! **W2 DoS FALSIFIER — the single-offering `GET /session/{id}` surface is BOUNDED.**
//!
//! `WebState::ensure_open` (the legacy offering-#0 surface, mounted at `GET /session/{id}`) used to
//! insert a full `DungeonSession` into `WebState.sessions` — plus a `presented` slot in the
//! `WebFrontend` — for EVERY arbitrary path `{id}`, with no cap and no eviction: the SAME
//! PlayerWorlds gap the catalog host closed, still open on this map. The fix routes the map through
//! a bounded LRU ([`WebState::with_capacity`], default [`DEFAULT_WEB_SESSION_CAPACITY`]) and tears
//! down an evicted session's frontend slot in lockstep, mirroring `dreggnet_catalog::PlayerWorlds`.
//!
//! These falsifiers mirror `dreggnet_catalog`'s
//! `a_flood_of_distinct_identities_never_grows_past_capacity`: a flood of N ≫ cap distinct ids
//! saturates the map at exactly the cap and never grows past it — and an actively-viewed session is
//! kept hot, so the LRU never evicts a live player out from under a flood.

use dreggnet_offerings::SessionId;
use dreggnet_web::WebState;

/// **THE DoS FALSIFIER** — a flood of distinct `/session/{id}` path ids never grows the live
/// session map (or its paired frontend `presented` map) past the LRU capacity.
#[test]
fn a_flood_of_distinct_session_ids_never_grows_past_capacity() {
    let cap = 8usize;
    let state = WebState::with_capacity(cap);

    for n in 0..(cap * 6) {
        state.ensure_open(&SessionId::new(format!("flood-{n}")));
        assert!(
            state.live_sessions() <= cap,
            "the live-session map is hard-bounded at {cap}; saw {} after {} opens",
            state.live_sessions(),
            n + 1
        );
        assert!(
            state.presented_sessions() <= cap,
            "the frontend `presented` map is bounded in lockstep at {cap}; saw {}",
            state.presented_sessions()
        );
    }
    assert_eq!(
        state.live_sessions(),
        cap,
        "the session map saturates at exactly its capacity, never beyond"
    );
    assert_eq!(
        state.presented_sessions(),
        cap,
        "the presented map saturates at exactly its capacity, never beyond"
    );
}

/// **A capacity of zero is clamped to one** — the surface always holds at least the session being
/// served, so a `GET` can never fail to yield a live session.
#[test]
fn a_zero_capacity_is_clamped_so_a_touch_always_yields_a_session() {
    let state = WebState::with_capacity(0);
    let solo = SessionId::new("solo");
    state.ensure_open(&solo);
    assert!(state.is_open(&solo));
    assert_eq!(state.live_sessions(), 1);
}

/// **An actively-viewed session is never the flood's victim.** Re-touching `hero` (what every
/// render/GET does) keeps it most-recently-used, so a flood of distinct cold ids evicts the cold
/// ones and leaves the live player's session intact.
#[test]
fn a_hot_session_survives_a_flood_of_cold_ids() {
    let cap = 4usize;
    let state = WebState::with_capacity(cap);
    let hero = SessionId::new("hero");
    state.ensure_open(&hero);

    for n in 0..(cap * 8) {
        // The flood of strangers…
        state.ensure_open(&SessionId::new(format!("stranger-{n}")));
        // …while the live player keeps viewing their session (a touch bumps LRU recency).
        state.ensure_open(&hero);
        assert!(state.live_sessions() <= cap);
    }
    assert!(
        state.is_open(&hero),
        "the continuously-touched session was never evicted by the flood"
    );
}

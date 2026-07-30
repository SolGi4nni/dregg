//! Shared setup for this bot's test binaries — the two things a LIVE Telegram bot does at startup
//! and a test binary, which never runs `main`, has to do for itself.
//!
//! # Why a Telegram test has to install anything
//!
//! `src/bin/dreggnet-telegram-bot.rs` performs two arming steps before it builds a host, and both
//! are fail-closed by design, so a process that skips them does not degrade — it REFUSES:
//!
//! 1. **the Descent's day.** The catalog registers the Descent under
//!    [`dreggnet_catalog::DescentDayBinding::Live`], resolved at every open, so a run's banked
//!    relics mint under a provenance root that could not exist before that drand round was
//!    revealed. With no day published, `descent` and `descent-campaign` refuse to OPEN with *"this
//!    offering could not be opened on this server"* — measured 2026-07-29 in
//!    `every_offering_paints` and `runtime_shell`, where two of the three
//!    [`dreggnet_catalog::SHIPPED_KEYS`] were simply unreachable.
//!
//! 2. **the verified distributed gates.** `/market` and the Dark Bazaar settle their award ring
//!    through `dregg_intent::verified_settle`, which the twin-deletion sweep (`e3f0e7b92`) made
//!    authoritative per leg. An unregistered `IntentVerifiedGate` is not a skipped cross-check, it
//!    is a REFUSAL, and `multi_offering_through_telegram` read it verbatim:
//!
//!    ```text
//!    WIRING BUG in this host, not a problem with the auction: no verified executor gate is
//!    installed, so the award was NEVER JUDGED — it was not rejected.
//!    ```
//!
//!    Nothing in this crate's graph registered one, including the bot binary. `dreggnet-market`,
//!    `starbridge-apps/tussle`, `dregg-teasting`, `dregg-wire`, `dreggnet-catalog`, the Discord bot
//!    and `dregg-app-framework` each learned this separately; this is the eighth.
//!
//! # They are the REAL things, and they cannot silently do nothing
//!
//! [`arm_pinned_descent_day`] publishes a genuine BLS-verifiable drand reveal, so the whole verify
//! path runs for real — ⚠ it is a PINNED published round, not today's, which is as pre-computable
//! as any constant, so it establishes that the WIRING is beacon-bound and nothing about
//! unpredictability. A serving process calls `host::arm_todays_descent_day`, never this.
//!
//! [`install_verified_distributed_gates`] installs `dregg-exec-lean`'s Lean-backed implementation,
//! so both poles of a settle are decided by the machine-checked rule over the linked archive: a
//! conserved ring CLEARS and an unaffordable one FAILS CLOSED. The archive-absent case routes
//! through `dregg_lean_ffi::demand_lean`, which PANICS by default naming the missing capability,
//! rather than returning and letting a test print `ok` about a settlement nothing judged.
//!
//! # Once per PROCESS, so once per TEST
//!
//! `cargo nextest` runs one process per test, so a single call at the top of one test does not
//! carry to the next. Both are idempotent (a process-global cell each), so calling them where they
//! are not needed costs nothing.

#![allow(dead_code)]

/// Publish the pinned drand round as the Descent's day for THIS test process, as the bot's startup
/// does with today's live round. Idempotent. PANICS if the pinned reveal does not verify — that is
/// a broken beacon path, not a skippable condition.
pub fn arm_pinned_descent_day() {
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");
}

/// Install the verified-Lean distributed gates for THIS test process, exactly as a native node does
/// at startup (`node/src/lib.rs`) and as `src/bin/dreggnet-telegram-bot.rs` now does. Idempotent.
///
/// Returns `true` when the gates are live. PANICS (rather than skipping) when the linked archive
/// lacks the distributed exports, unless the developer opt-out `DREGG_TEST_ALLOW_MISSING_LEAN=1` is
/// set out loud — in which case it returns `false` after printing that any resulting green is
/// evidence about the Rust half only.
pub fn install_verified_distributed_gates() -> bool {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::distributed_exports_available(),
        "the verified distributed coordination gates (distributed_exports_available()==false): \
         this bot's market settle and Dark Bazaar award both refuse without them",
    ) {
        return false;
    }
    dregg_exec_lean::register_distributed_gates();
    true
}

/// Both arming steps, in the order the bot binary performs them — for a test that drives the whole
/// catalog and therefore meets both.
pub fn arm_like_the_running_bot() {
    arm_pinned_descent_day();
    install_verified_distributed_gates();
}

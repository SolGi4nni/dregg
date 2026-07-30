//! Shared setup for the bot's test binaries — and for the bot's OWN unit tests, which reach this
//! same file through `#[cfg(test)] #[path = "../tests/support/mod.rs"] mod support;` in
//! `src/main.rs`. One file, one installer, no second copy to drift.
//!
//! # Why a bot test has to install something
//!
//! Three of this bot's surfaces end in a decision the verified Lean export owns, routed through a
//! seam that is EMPTY until someone registers it:
//!
//!   * `/market` and the Dark Bazaar settle through `dregg_intent::verified_settle`;
//!   * `/coordinate` folds a pair round through `dregg-coord`'s conservation gate;
//!   * `/handoff` redeems a CapTP certificate through `dregg_captp`'s handoff §6.
//!
//! The twin-deletion sweep (`e3f0e7b92`) made the verified export the AUTHORITY on those paths and
//! deleted the Rust fold from the live path, so an unregistered seam is not a skipped cross-check —
//! it REFUSES. Nothing in this crate's graph registered one. Measured at HEAD on 2026-07-29,
//! `cargo nextest run -p dregg-discord-bot --no-fail-fast --test-threads=4` was 19 of 509 red and
//! **six of those nineteen were this single missing call**, in three unrelated-looking families:
//!
//! ```text
//! WIRING BUG in this host, not a problem with the auction: no verified executor gate is
//! installed, so the award was NEVER JUDGED — it was not rejected.        (3 × market)
//! NotConserving(FfiUnavailable("no verified gate registered"))           (2 × coordinate_flow)
//! Captp(VerifiedGateUnavailable)                                         (1 × handoff_flow)
//! ```
//!
//! …and the market's text was right: `dreggnet_web::install_verified_settlement_gate` and
//! `node/src/lib.rs` call `dregg_exec_lean::register_distributed_gates()` at startup, and this bot
//! now does too (`main.rs`). A test binary never runs `main`, so it has to do the same thing for
//! itself. `dreggnet-market`, `starbridge-apps/tussle`, `dregg-teasting`, `dregg-wire` and
//! `dreggnet-catalog` each learned this separately.
//!
//! ⚑ **AND ONE OF THE SIX WAS A REFUSAL POLE THAT WAS GREEN FOR THE WRONG REASON.**
//! `coordinate_flow::an_unaffordable_round_is_refused_whole` asserted
//! `matches!(err, CoordinationError::NotConserving(_))` — which the MISSING-GATE error satisfies
//! just as well as a real overdraft. It passed throughout, on the wrong evidence, while its honest
//! twin died. That is why the honest pole and the refusal pole are now asserted in the same
//! process against the same installed gate, and why the refusal assertions name the inner cause.
//!
//! # It is the REAL gate, and it cannot silently do nothing
//!
//! [`install_verified_distributed_gates`] installs `dregg-exec-lean`'s Lean-backed implementation,
//! so both poles are decided by the machine-checked rule over the linked archive: a conserved
//! round CLEARS and an unaffordable one FAILS CLOSED. A permissive stand-in would have turned "the
//! bot settles" into "the bot compiles".
//!
//! The archive-absent case routes through `dregg_lean_ffi::demand_lean`, which PANICS by default
//! (`DREGG_TEST_REQUIRE_LEAN` is armed unless explicitly disarmed) naming the missing capability,
//! rather than returning and letting a test print `ok` about a settlement nothing judged.
//!
//! # Once per PROCESS, so once per TEST
//!
//! `cargo nextest` runs one process per test, so a single install at the top of one test does not
//! carry to the next. Call this at the top of every test that settles, folds a coordination round,
//! or redeems a handoff — it is idempotent (the seams are process-global `OnceLock`s), so calling
//! it where it is not needed costs nothing.

/// Install the verified-Lean distributed gates for THIS test process, exactly as `main.rs` does at
/// startup and as a native node does (`node/src/lib.rs`). Idempotent.
///
/// Returns `true` when the gates are live. PANICS (rather than skipping) when the linked archive
/// lacks the distributed exports, unless the developer opt-out `DREGG_TEST_ALLOW_MISSING_LEAN=1` is
/// set out loud — in which case it returns `false` after printing that any resulting green is
/// evidence about the Rust half only.
pub fn install_verified_distributed_gates() -> bool {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::distributed_exports_available(),
        "the verified distributed coordination gates (distributed_exports_available()==false): \
         the bot's market settle, coordination fold and CapTP handoff all refuse without them",
    ) {
        return false;
    }
    dregg_exec_lean::register_distributed_gates();
    true
}

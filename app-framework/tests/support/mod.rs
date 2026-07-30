//! Shared setup for the `dregg-app-framework` test binaries — and for the crate's own lib tests,
//! which reach this same file through `#[cfg(test)] #[path = "../tests/support/mod.rs"] mod
//! support;` in `src/lib.rs`. One file, one installer, no second copy to drift.
//!
//! # Why an app-framework test has to install something
//!
//! Three of this crate's surfaces move value, and all three end in
//! `dregg_intent::verified_settle::settle_ring_wide_verified`:
//!
//!   * `ring_trade::RingCoordinator::coordinate` — the Σδ=0 gate it runs BEFORE touching any app,
//!   * `service_promise::ServicePromiseExchange::{fund,fulfill,refund}` — every escrow leg,
//!   * `agent_coordination::coordinate` — the round's single atomic settle.
//!
//! That fold decides each leg ONLY through the verified Lean export `dregg_record_kernel_step`,
//! routed through `dregg_intent::verified_gate`. The twin-deletion sweep (`e3f0e7b92`) made that
//! export the AUTHORITY and deleted the Rust fold from the live path, so an unregistered gate is
//! not a skipped cross-check — `ffi::settle_leg` returns `FfiUnavailable("no verified gate
//! registered")`, which REFUSES the leg, and a ring is all-or-none.
//!
//! Nothing in this crate's graph registered one. Measured at HEAD on 2026-07-29, `cargo nextest run
//! -p dregg-app-framework --no-fail-fast --test-threads=4` was **15 red, and all 15 were this
//! single missing call** — every happy path that moves value, and also the refusal tests whose
//! refusal is supposed to cite an underfunded leg or a taken one-shot and instead never got as far
//! as funding the escrow.
//!
//! ⚠ The refusal that bites here is INSIDE `dregg-intent`, and it is invisible to that crate's own
//! `cargo test`: `verified_settle::settle_leg_authoritative` has a `#[cfg(test)]` twin that keeps
//! the in-process fold authoritative for dregg-intent's OWN unit tests. Every DOWNSTREAM crate —
//! this one — compiles the `#[cfg(not(test))]` fail-closed sibling. So "dregg-intent is green"
//! carries no information about whether a consumer can settle.
//!
//! `dreggnet_web::install_verified_settlement_gate` and `node/src/lib.rs` call
//! `dregg_exec_lean::register_distributed_gates()` at startup; a test binary that drives the settle
//! path has to do the same thing for itself. `dreggnet-market`, `starbridge-apps/tussle`,
//! `dregg-teasting`, `dregg-wire` and `dreggnet-catalog` each learned this separately.
//!
//! # It is the REAL gate, and it cannot silently do nothing
//!
//! [`install_verified_settlement_gate`] installs `dregg-exec-lean`'s Lean-backed implementation, so
//! both poles are decided by the machine-checked rule over the linked archive: a conserving escrow
//! leg SETTLES and an underfunded one FAILS CLOSED. A permissive stand-in would have turned "the
//! escrow conserves" into "the escrow compiles".
//!
//! The archive-absent case routes through `dregg_lean_ffi::demand_lean`, which PANICS by default
//! (`DREGG_TEST_REQUIRE_LEAN` is armed unless explicitly disarmed) naming the missing capability,
//! rather than returning and letting a test print `ok` about a payment nothing judged.
//!
//! # Once per PROCESS, so once per TEST
//!
//! `cargo nextest` runs one process per test, so a single install at the top of one test does not
//! carry to the next. Call this at the top of every test that funds, fulfills, refunds, coordinates
//! or settles — it is idempotent (`OnceLock`), so calling it where it is not needed costs nothing.

/// Install the verified-Lean settlement gate for THIS test process, exactly as a native node does
/// at startup (`node/src/lib.rs::install_verified_distributed_gates`). Idempotent.
///
/// Returns `true` when the gate is live. PANICS (rather than skipping) when the linked archive
/// lacks the distributed exports, unless the developer opt-out `DREGG_TEST_ALLOW_MISSING_LEAN=1` is
/// set out loud — in which case it returns `false` after printing that any resulting green is
/// evidence about the Rust half only.
pub fn install_verified_settlement_gate() -> bool {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::distributed_exports_available(),
        "the verified app-framework settlement gate (distributed_exports_available()==false)",
    ) {
        return false;
    }
    dregg_exec_lean::register_distributed_gates();
    true
}

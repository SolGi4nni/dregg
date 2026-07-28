//! Shared setup for the `dreggnet-market` test binaries — and for the crate's own lib tests,
//! which reach this same file through `#[cfg(test)] #[path = "../tests/support/mod.rs"] mod
//! support;` in `src/lib.rs`. One file, one installer, no second copy to drift.
//!
//! # Why a market test has to install something
//!
//! Every SETTLE in this crate ends in `dregg_intent::verified_settle::settle_ring_verified`, which
//! decides each ring leg ONLY through the verified Lean export `dregg_record_kernel_step`, routed
//! through `dregg_intent::verified_gate`. The twin-deletion sweep (`e3f0e7b92`) made that export
//! the AUTHORITY and deleted the Rust fold from the live path, so an unregistered gate is not a
//! skipped cross-check — it REFUSES the leg, and a ring is all-or-none.
//!
//! Nothing in this crate's graph registered one. Measured at HEAD on 2026-07-28, `cargo nextest
//! run -p dreggnet-market --no-fail-fast --test-threads=4` was **23 of 52 red, and 22 of those 23
//! were this single missing call** — every happy-path clear, and also every REFUSAL test whose
//! refusal is supposed to cite the reserve or the seal and instead cited the absent gate. The
//! market's own error text has named the fix since `078d68914`:
//!
//! > WIRING BUG in this host, not a problem with the auction: no verified executor gate is
//! > installed, so the award was NEVER JUDGED — it was not rejected.
//!
//! …and it was right. `dreggnet_web::install_verified_settlement_gate` and `node/src/lib.rs` call
//! `dregg_exec_lean::register_distributed_gates()` at startup; a test binary that drives the settle
//! path has to do the same thing for itself. `starbridge-apps/tussle`, `dregg-teasting`,
//! `dregg-wire` and `dreggnet-catalog` each learned this separately.
//!
//! # It is the REAL gate, and it cannot silently do nothing
//!
//! [`install_verified_settlement_gate`] installs `dregg-exec-lean`'s Lean-backed implementation, so
//! both poles are decided by the machine-checked rule over the linked archive: a conserved award
//! CLEARS and a divergent leg FAILS CLOSED. A permissive stand-in would have turned "the market
//! settles" into "the market compiles".
//!
//! The archive-absent case routes through `dregg_lean_ffi::demand_lean`, which PANICS by default
//! (`DREGG_TEST_REQUIRE_LEAN` is armed unless explicitly disarmed) naming the missing capability,
//! rather than returning and letting a test print `ok` about a settlement nothing judged.
//!
//! # Once per PROCESS, so once per TEST
//!
//! `cargo nextest` runs one process per test, so a single install at the top of one test does not
//! carry to the next. Call this at the top of every test that lists, bids, settles or verifies —
//! it is idempotent (`OnceLock`), so calling it where it is not needed costs nothing.

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
        "the verified market settlement gate (distributed_exports_available()==false)",
    ) {
        return false;
    }
    dregg_exec_lean::register_distributed_gates();
    true
}

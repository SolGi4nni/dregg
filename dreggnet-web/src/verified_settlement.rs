//! **Install the verified-Lean settlement gate this surface's market actually needs — at STARTUP.**
//!
//! # What was broken
//!
//! `dreggnet-web` serves a sealed-bid market (`/offerings/market/session/{id}`, and the Dark
//! Bazaar beside it). A settle folds the award ring through
//! [`dregg_intent::verified_settle::settle_ring_verified`], which is FAIL-CLOSED by design: with no
//! [`IntentVerifiedGate`](dregg_intent::verified_gate::IntentVerifiedGate) registered it REFUSES
//! rather than letting an unverified in-process Rust fold decide a settlement. That refusal is
//! correct and stays.
//!
//! What was NOT correct is that nothing in this crate ever registered the gate. Measured on
//! 2026-07-25 against the shipped router, a player could `list`, `bid`, `bid` — three real
//! committed turns — and then the one turn that matters died with:
//!
//! ```text
//! Refused: settlement rejected by the verified executor: award settlement rejected by the
//! verified executor: verified-executor FFI unavailable: no verified gate registered
//! ```
//!
//! `dregg_exec_lean::register_distributed_gates()` had exactly ONE caller in the whole repo (a
//! `dreggnet-catalog` test). So the sealed auction was unreachable in `dreggnet-web-server`: a
//! button that lands two turns and then cannot complete the third.
//!
//! # Why REGISTER rather than hide the affordance
//!
//! `dregg-exec-lean` is **already compiled and linked into this binary** — `spween-dregg` and
//! `dreggnet-telegram` both pull `dregg-sdk`, whose default features include `exec-lean`, and
//! `dregg-automatafl` + `dregg-bridge` already link `dregg-lean-ffi` (the archive) unconditionally.
//! So there was never a link-weight or portability argument for the absence: the verified executor
//! is in the process, and the only thing missing was the four-line call that hands it to the four
//! FFI-free coordination seams. Naming `dregg-exec-lean` as a direct dependency adds ZERO new
//! compilation; it makes an already-present capability reachable.
//!
//! # Fail closed, LOUDLY, at startup
//!
//! Registration alone is not evidence: a registered gate over an ABSENT or STALE Lean archive still
//! refuses at the third click, which is the failure mode this module exists to delete. So
//! [`install_verified_settlement_gate`] registers and then **PROVES the gate decides**, with a
//! two-polarity probe run once at startup:
//!
//!   * a funded, distinct, live-cell leg MUST commit and MUST produce the exact post-column;
//!   * an UNDER-FUNDED leg MUST be rejected.
//!
//! The second pole is what makes this a gate rather than a smoke test: a gate that answered "ok"
//! unconditionally would sail through the first probe. `dreggnet-web-server` runs this before it
//! binds a listener and REFUSES TO BOOT on failure (the same posture
//! `validate_public_shielded_deployment` takes), so an operator learns at second zero, not from a
//! player's third click.

use std::sync::OnceLock;

use dregg_intent::verified_settle::{VerifiedLedger, VerifiedLeg, settle_ring_verified};

/// The probe's asset column — a fixed, meaningless 32-byte id. Nothing else in the process uses it,
/// so the probe cannot collide with a live market's ledger.
const PROBE_ASSET: [u8; 32] = [0x67; 32];
/// The probe's two live cells (the low byte the verified ledger indexes by).
const PROBE_FROM: u8 = 0xA1;
const PROBE_TO: u8 = 0xA2;
/// The probe's funded balance and the amount it moves.
const PROBE_FUNDED: i128 = 7;
const PROBE_AMOUNT: i128 = 5;

/// Cached one-shot result — the gate is a process-global `OnceLock` in `dregg-intent`, so the
/// install is idempotent and the probe is worth running exactly once.
static INSTALLED: OnceLock<Result<(), String>> = OnceLock::new();

/// **Install the verified-Lean settlement gate and PROVE it decides.** Idempotent; the result is
/// computed once per process and returned to every later caller.
///
/// `Ok(())` means a market settle in this process will be decided by the linked verified executor.
/// `Err(reason)` means it will NOT — every settle will refuse — and the caller MUST surface that
/// rather than serve a settle affordance it cannot complete.
pub fn install_verified_settlement_gate() -> Result<(), String> {
    INSTALLED.get_or_init(install_and_probe).clone()
}

/// Whether [`install_verified_settlement_gate`] has already been run AND succeeded. Never triggers
/// the install itself — for a surface that wants to describe the state without changing it.
pub fn verified_settlement_available() -> bool {
    matches!(INSTALLED.get(), Some(Ok(())))
}

fn install_and_probe() -> Result<(), String> {
    // The single documented entry point a native node calls at startup: it installs the Lean-backed
    // impl into all four FFI-free coordination seams (coord / captp / federation / intent). The
    // intent seam is the one a market settle folds through.
    dregg_exec_lean::register_distributed_gates();

    // ── THE DEPLOYED CONSTRAINT ORACLE — the SAME wound, one layer down ────────────────────────
    //
    // Found 2026-07-26 by putting a RELEASE build of `dreggnet-web-server` on a real box. It died
    // at boot, before binding, with:
    //
    // ```text
    // panicked at dreggnet-web/src/lib.rs:5471: today's descent opens: Deploy("world-cell turn
    // refused: … no constraint oracle installed: this native node cannot decide a Lean-subset
    // constraint without the verified dregg_constraint_admits oracle — fail-closed")
    // ```
    //
    // `dregg_cell::program::eval` routes the Lean-evaluated `StateConstraint` subset through the
    // installed oracle and FAILS CLOSED when there is none — but that gate is
    // `#[cfg(all(not(debug_assertions), any(unix, windows)))]`, i.e. **native RELEASE only**.
    // `dregg-cell` is a pervasive dependency and a plain `not(test)` refusal would have refused
    // valid turns across every debug test build in the workspace, so release-gating it is right.
    // The cost is that it is INVISIBLE to `cargo test`: every test in this repo builds debug, takes
    // the Rust guest-path evaluator, and passes. Nothing goes red until a release binary opens a
    // programmed cell on a box.
    //
    // `dregg_exec_lean::register_constraint_oracle()` had exactly ONE caller in the whole repo —
    // `node/src/lib.rs` — so the NODE was armed and the web server was not. Same shape as the
    // finding this module was written for: the capability is compiled in, linked, and simply never
    // handed over. Registering it here rather than in the server bin arms every embedding of
    // `dreggnet-web` (the bin, the tailnet funnel, the catalog tests) from the one place that is
    // already contractually "installed and PROVED before a listener exists".
    let constraint_oracle = dregg_exec_lean::register_constraint_oracle();
    tracing::info!(
        installed = constraint_oracle,
        "constraint oracle: the deployed executor's Lean-subset StateConstraint/HeapAtom admission \
         is decided by the verified `dregg_constraint_admits`"
    );
    // Refuse on the EXACT configuration `eval.rs` fails closed on, and no other. In debug (tests,
    // dev) the guest-path evaluator legitimately decides and this must stay quiet; on a release
    // native build without the oracle every programmed-cell turn is already dead, so booting only
    // moves the discovery to a player.
    #[cfg(all(not(debug_assertions), any(unix, windows)))]
    if !constraint_oracle {
        return Err(
            "the verified deployed-constraint oracle did not register (the linked archive does \
             not export `dregg_constraint_admits`). On a native RELEASE build `dregg-cell` fails \
             CLOSED for the whole Lean-evaluated constraint subset, so every programmed-cell turn \
             — the Descent, the dungeon, the campaign — would refuse"
                .to_string(),
        );
    }

    // ── THE CONSERVATION ORACLE (House Law #1) ────────────────────────────────────────────────
    // Same treatment, opposite failure mode: with no oracle installed the executor does NOT fail
    // closed here — `turn::executor::atomic` falls through to the hand-written Rust
    // `BlockConservation` twin, the asset-blind decision that already drifted into an inflation
    // bug once. `dregg-node` refuses to boot without it (`assert_conservation_oracle_installed`).
    // A server that settles a market must hold the same line.
    let conservation_oracle = dregg_exec_lean::register_conservation_oracle();
    tracing::info!(
        installed = conservation_oracle,
        "conservation oracle: per-asset Σδ=0 is decided by the verified `dregg_cross_cell_conserves`"
    );
    #[cfg(all(not(debug_assertions), any(unix, windows)))]
    if !conservation_oracle {
        return Err(
            "the verified cross-cell conservation oracle did not register (the linked archive \
             does not export `dregg_cross_cell_conserves`). The executor would silently decide \
             per-asset Σδ=0 with the UNVERIFIED Rust twin that already drifted into an inflation \
             bug; refusing to serve a market on it"
                .to_string(),
        );
    }

    // POLE 1 — a leg that MUST commit, with the exact post-column checked.
    let mut ledger = VerifiedLedger::new();
    ledger.add_account(PROBE_FROM);
    ledger.add_account(PROBE_TO);
    ledger.set(PROBE_FROM, &PROBE_ASSET, PROBE_FUNDED);
    ledger.set(PROBE_TO, &PROBE_ASSET, 0);
    let good = VerifiedLeg {
        from: PROBE_FROM,
        to: PROBE_TO,
        asset: PROBE_ASSET,
        amount: PROBE_AMOUNT,
    };
    let post = settle_ring_verified(&ledger, std::slice::from_ref(&good)).map_err(|e| {
        format!(
            "the verified executor could not settle a trivial funded leg: {e} \
             (a market settle in this process will refuse)"
        )
    })?;
    let (want_from, want_to) = (PROBE_FUNDED - PROBE_AMOUNT, PROBE_AMOUNT);
    let (got_from, got_to) = (
        post.get(PROBE_FROM, &PROBE_ASSET),
        post.get(PROBE_TO, &PROBE_ASSET),
    );
    if (got_from, got_to) != (want_from, want_to) {
        return Err(format!(
            "the verified executor settled the probe leg to the WRONG post-column: \
             got ({got_from}, {got_to}), want ({want_from}, {want_to})"
        ));
    }

    // POLE 2 — an UNDER-FUNDED leg that MUST be refused. Without this a gate that answers "ok"
    // unconditionally would pass the install, and the whole point is that the executor DECIDES.
    let overdraft = VerifiedLeg {
        amount: PROBE_FUNDED + 2,
        ..good
    };
    if settle_ring_verified(&ledger, std::slice::from_ref(&overdraft)).is_ok() {
        return Err(
            "the verified executor COMMITTED an under-funded leg — the gate is not deciding, \
             it is rubber-stamping; refusing to treat settlement as verified"
                .to_string(),
        );
    }

    Ok(())
}

/// The operator-facing sentence for a failed install — used by the server bin's startup refusal and
/// by the library's error log, so both say the same thing.
pub fn install_failure_advice(reason: &str) -> String {
    format!(
        "the verified executor is NOT fully armed in this process: {reason}. Depending on which \
         half failed, either the sealed-bid market and the Dark Bazaar cannot settle — a player \
         lands a listing and bids and is then refused — or every programmed-cell turn refuses \
         outright. This almost always means the linked Lean archive (`dregg-lean-ffi`'s \
         libdregg_lean.a) is absent or stale for this build."
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// THE CANARY. The whole finding was "nobody calls `register_distributed_gates()`", so the test
    /// that matters is that the install actually installs — and that its own probe is capable of
    /// failing. Deleting the `register_distributed_gates()` call from `install_and_probe` makes
    /// this red (the probe's first pole refuses with `no verified gate registered`).
    #[test]
    fn the_install_registers_a_gate_that_really_decides() {
        install_verified_settlement_gate()
            .expect("the linked verified executor installs + decides");
        assert!(verified_settlement_available());

        // And a settle in this process is now decided, in BOTH polarities, by that gate.
        let mut ledger = VerifiedLedger::new();
        ledger.add_account(1);
        ledger.add_account(2);
        ledger.set(1, &PROBE_ASSET, 10);
        let leg = |amount| VerifiedLeg {
            from: 1,
            to: 2,
            asset: PROBE_ASSET,
            amount,
        };
        let post = settle_ring_verified(&ledger, &[leg(4)]).expect("a funded leg settles");
        assert_eq!(post.get(1, &PROBE_ASSET), 6);
        assert_eq!(post.get(2, &PROBE_ASSET), 4);
        assert!(
            settle_ring_verified(&ledger, &[leg(11)]).is_err(),
            "an over-draft leg must be REFUSED by the verified executor"
        );
    }
}

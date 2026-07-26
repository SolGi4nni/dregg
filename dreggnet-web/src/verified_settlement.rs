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
        "the verified settlement gate is NOT installed: {reason}. The sealed-bid market and the \
         Dark Bazaar CANNOT settle in this process — a player would land a listing and bids and \
         then be refused. This almost always means the linked Lean archive \
         (`dregg-lean-ffi`'s libdregg_lean.a) is absent or stale for this build."
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

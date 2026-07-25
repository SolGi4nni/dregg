//! Both-directions gate test for the DrEX `drex_clear` clear-book pipeline.
//!
//! # The regression this pins
//!
//! The twin-deletion sweep INVERTED `dregg-intent`'s ring settlement so that, with NO verified gate
//! installed, `settle_ring_verified` FAILS CLOSED (an unverified in-process Rust fold must not decide
//! a settlement — `intent/tests/settle_fail_closed.rs` proves that refusal). The `drex_clear` CLI is
//! an app that settles cleared rings, so it MUST install the gate — but it lived in FFI-free
//! `dregg-intent`, which cannot, so every clearing book (including the demo) was refused. Moving the
//! bin here (`dregg-exec-lean`, the single FFI boundary) lets it install the REAL Lean gate via
//! `register_distributed_gates()` — the same way a native node does.
//!
//! This test asserts BOTH directions THROUGH THE REAL Lean export `dregg_record_kernel_step`:
//!   * ACCEPT — a legitimate, conserving 3-ring clearing book CLEARS (no longer refused);
//!   * REFUSE — an over-debiting ring is still REJECTED (the fail-close the twin-deletion is for).
//!
//! Requires the linked Lean archive (`libdregg_lean.a`); self-skips when absent (CI without it),
//! matching `fulfillment_ffi_verified.rs` + the other `lean_*` producer tests.
//!
//! Run with: `cargo test -p dregg-exec-lean --test drex_clear_gate`

use std::process::{Command, Stdio};

use dregg_intent::verified_settle::{
    VerifiedLeg, VerifiedSettleError, funded_ledger, settle_ring_verified, touched_assets,
};

fn lean_ready() -> bool {
    dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (lean_available)",
    )
}

fn asset(b: u8) -> [u8; 32] {
    let mut a = [0u8; 32];
    a[0] = b;
    a
}

/// The canonical demo book: a GOLD→ART→WINE→GOLD 3-ring that is bilaterally STUCK and clears only as
/// a ring (plus one resting order that matches nobody). This is `drex-web`'s baked-in default book —
/// the exact one the regression refused fail-closed.
const DEMO_BOOK: &str = r#"[
  {"trader":"Ada","offerAsset":"GOLD","offerAmount":100,"wantAsset":"ART","wantMin":10,"priority":3},
  {"trader":"Bram","offerAsset":"ART","offerAmount":50,"wantAsset":"WINE","wantMin":20,"priority":1},
  {"trader":"Cyl","offerAsset":"WINE","offerAmount":80,"wantAsset":"GOLD","wantMin":40,"priority":2},
  {"trader":"Del","offerAsset":"SILVER","offerAmount":30,"wantAsset":"PEARL","wantMin":5,"priority":4}
]"#;

/// ACCEPT direction, end-to-end through the shipped CLI: feed the real demo book to the `drex_clear`
/// binary (which installs the REAL Lean gate in its `main`) and assert it clears.
///
/// A printed `"ok":true` is doubly load-bearing: the bin only emits it when the matched ring SETTLED
/// through the verified gate AND its internal reject-polarity check saw the over-debit REFUSED with a
/// `LegRejected` (not `FfiUnavailable`) — so `ok:true` witnesses BOTH the accept and the refuse
/// through the same real Lean export in one shot. Before the fix the bin printed
/// `{"error":"verified settlement rejected the ring: verified-executor FFI unavailable: no verified
/// gate registered","ok":false}` and exited non-zero.
#[test]
fn drex_clear_bin_clears_the_demo_book() {
    if !lean_ready() {
        return;
    }
    let bin = env!("CARGO_BIN_EXE_drex_clear");
    let out = Command::new(bin)
        .arg(DEMO_BOOK)
        .stdin(Stdio::null())
        .output()
        .expect("spawn drex_clear");

    let stdout = String::from_utf8_lossy(&out.stdout);
    let last = stdout.trim().lines().last().unwrap_or_default();
    let v: serde_json::Value = serde_json::from_str(last)
        .unwrap_or_else(|e| panic!("drex_clear emitted non-JSON: {e}; raw: {stdout}"));

    assert_eq!(
        v["ok"],
        serde_json::Value::Bool(true),
        "the legit demo book must CLEAR through the verified gate (regression: it was refused \
         fail-closed); got: {v}"
    );
    assert!(
        v["ring"].is_object(),
        "a clearing ring must be found for the demo book; got: {v}"
    );
    assert_eq!(
        v["twoCycles"],
        serde_json::json!(0),
        "the clearing must be genuinely multilateral (no bilateral match); got: {v}"
    );
    assert!(
        out.status.success(),
        "drex_clear must exit 0 on the legit book; stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// The regression gate that CANNOT self-skip — it has teeth on a box WITHOUT the Lean archive too,
/// which is where the previous gate went blind.
///
/// `drex_clear_bin_clears_the_demo_book` only fires where `libdregg_lean.a` is linked; on every other
/// box it returns early, so deleting `register_distributed_gates()` from the bin's `main` would sail
/// through. This test never skips. It asserts the CLI's failure MODE, which is registration-sensitive
/// in both environments:
///
///   * archive linked   → the demo book must CLEAR (`ok:true`) — the gate is installed and works;
///   * archive absent   → the CLI must refuse and say the BUILD/ENVIRONMENT has no verified core.
///     Without the registration the refusal instead reads `no verified gate registered` (a WIRING
///     BUG), which this test rejects — so the unregistered path is RED here as well.
///
/// In BOTH directions it forbids the old ring-blaming wording. `"verified settlement rejected the
/// ring: …FFI unavailable…"` is a lie about a legitimate book: nothing judged that ring. The demo
/// book below is CLEARABLE by construction (the GOLD→ART→WINE→GOLD ring), so any message claiming it
/// was *rejected* for want of an FFI is misattribution, and it is what sent the DrEX outage to the
/// matcher instead of to the missing gate.
#[test]
fn drex_clear_blames_the_missing_core_never_the_book() {
    let bin = env!("CARGO_BIN_EXE_drex_clear");
    let out = Command::new(bin)
        .arg(DEMO_BOOK)
        .stdin(Stdio::null())
        .output()
        .expect("spawn drex_clear");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let last = stdout.trim().lines().last().unwrap_or_default();
    let v: serde_json::Value = serde_json::from_str(last)
        .unwrap_or_else(|e| panic!("drex_clear emitted non-JSON: {e}; raw: {stdout}"));
    let err = v["error"].as_str().unwrap_or_default().to_string();

    assert!(
        !err.contains("rejected the ring"),
        "a clearable book must never be reported as REJECTED by the verified settlement — when the \
         core cannot run, the ring was never judged. Say what is missing instead; got: {err}"
    );

    if dregg_lean_ffi::lean_available() {
        assert_eq!(
            v["ok"],
            serde_json::Value::Bool(true),
            "with the Lean archive linked, the bin installs the gate and the demo book CLEARS; \
             got: {v}"
        );
        return;
    }

    // No archive: the ONLY acceptable outcome is a refusal that names the missing verified core.
    assert_eq!(
        v["ok"],
        serde_json::Value::Bool(false),
        "with NO verified core a book must NEVER clear — it would be an unverified Rust \
         settlement; got: {v}"
    );
    assert!(
        !err.contains("no verified gate registered") && !err.contains("WIRING BUG"),
        "the bin must INSTALL the verified gate (`register_distributed_gates()` in `main`); a \
         `no verified gate registered` refusal means that call is gone — the exact regression this \
         test exists to catch; got: {err}"
    );
    assert!(
        err.contains("ENVIRONMENT") && err.contains("NO VERIFIED CORE"),
        "with the gate installed but no linked archive, the refusal must blame the ENVIRONMENT and \
         name the missing verified core; got: {err}"
    );
    // Keep the hard mode honest: a verification lane must not accept this weaker branch as a pass.
    dregg_lean_ffi::demand_lean(false, "Lean archive (drex_clear accept-direction)");
}

/// Both directions at the library level, through the REAL Lean gate (no subprocess): a funded,
/// conserving ring is ACCEPTED and conserves; an over-debiting ring is REFUSED with `LegRejected`
/// (the fail-close preserved — a bad book never settles).
#[test]
fn verified_gate_accepts_a_legit_ring_and_refuses_an_overdebit() {
    if !lean_ready() {
        return;
    }
    // Install the REAL Lean gate exactly the way the bin / a native node does.
    dregg_exec_lean::register_distributed_gates();

    // A closed, conserving 3-ring A->B->C->A, each leg a distinct asset.
    let legs = vec![
        VerifiedLeg {
            from: 1,
            to: 2,
            asset: asset(0xA0),
            amount: 5,
        },
        VerifiedLeg {
            from: 2,
            to: 3,
            asset: asset(0xA1),
            amount: 7,
        },
        VerifiedLeg {
            from: 3,
            to: 1,
            asset: asset(0xA2),
            amount: 9,
        },
    ];

    // ── ACCEPT: the funded ring settles through the real export and conserves per asset. ──
    let k0 = funded_ledger(&legs);
    let k1 = settle_ring_verified(&k0, &legs)
        .expect("a funded, conserving ring must SETTLE through the verified Lean gate");
    for a in touched_assets(&legs) {
        assert_eq!(
            k1.total_asset(&a),
            k0.total_asset(&a),
            "the verified executor must conserve asset {:02x}",
            a[0]
        );
    }

    // ── REFUSE: drain leg-0's sender one short → the gate must REJECT the over-debit (LegRejected),
    //    and the whole ring aborts atomically. This is the twin-deletion's whole point. ──
    let mut starved = funded_ledger(&legs);
    starved.set(legs[0].from, &legs[0].asset, legs[0].amount - 1);
    let refused = settle_ring_verified(&starved, &legs);
    assert!(
        matches!(
            refused,
            Err(VerifiedSettleError::LegRejected { index: 0, .. })
        ),
        "an over-debiting ring MUST be refused by the verified gate (LegRejected), not settled; \
         got {refused:?}"
    );
}

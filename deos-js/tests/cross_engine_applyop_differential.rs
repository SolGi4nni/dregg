//! **Cross-engine `ApplyOp` differential** — the anti-drift guard for the two deos-js
//! engines (backlog 2026-07-24 T2 / #5).
//!
//! deos runs the SAME cell-applet surface on TWO engines: `deos-js` (real SpiderMonkey via
//! `mozjs`) and `deos-js-runtime` (pure-Rust `boa`). They are twins: the same authored
//! applet, fired through either engine, must leave BYTE-IDENTICAL committed state. They
//! were hand-synced twins and DRIFTED — the SM side's `ApplyOp` lacked the boa side's 5th
//! `SetRegisterFromArgs` variant, and each carried its own `pack_u64` + arithmetic copy.
//!
//! Both engines now bind the ONE `deos_js_core::ApplyOp` (the union, all 5 variants, one
//! canonical saturating arithmetic). This test FIRES the same affordance sequence through
//! BOTH engines' real fire drivers — the SM `deos_js::applet::Applet::fire` (which lowers
//! `ApplyOp` via `into_closure` → `apply`) and the boa
//! `deos_js_runtime::applet::CellApplet::fire` (which lowers it via `slot`/`write`) — and
//! asserts the two ledgers agree on every model slot, including the previously-diverging
//! 5th variant's write path. A future edit that drifts one engine's lowering fails HERE.
//!
//! (This test links BOTH engines — `deos-js` already links `mozjs`; `deos-js-runtime` is a
//! dev-dependency pulling `boa` — the only place a genuine cross-engine comparison can run.)

use deos_js_core::{pack_u64, ApplyOp};
use dregg_cell::AuthRequired;

// The two engines derive the applet cell id from these; seeding them identically makes the
// two cells identical, so any divergence is the ApplyOp lowering, nothing else.
const PK: [u8; 32] = [0x11; 32];
const TOK: [u8; 32] = [0x22; 32];

/// One affordance both engines are seeded from: a name and its (shared) `ApplyOp`.
fn specs() -> Vec<(&'static str, ApplyOp)> {
    vec![
        ("inc", ApplyOp::AddToSlot { slot: 0 }),
        ("dec", ApplyOp::SubFromSlot { slot: 0 }),
        ("reset", ApplyOp::SetSlot { slot: 0, value: 0 }),
        ("put", ApplyOp::SetSlotFromArg { slot: 1 }),
        // The 5th variant — the one the SM engine previously LACKED. Through the single-arg
        // `fire` path both engines expose, it writes value 0 to the register named by the
        // arg (a 2-arg register-value write needs a multi-arg fire the SM engine does not
        // yet have — the scoped remainder; the boa multi-arg path is covered by
        // `deos-js-runtime/tests/native_js_kvstore_pure_js.rs`).
        ("putReg", ApplyOp::SetRegisterFromArgs),
    ]
}

/// Seed model: slot 4 starts non-zero so the 5th variant's write (zeroing register 4) is
/// OBSERVABLE, not a no-op both engines happen to agree on.
const SEED_SLOT: usize = 4;
const SEED_VAL: u64 = 99;

/// The fire sequence — `(affordance, arg)`. Single-arg, the contract both engines' `fire`
/// share. Chosen to exercise saturation (over/underflow), literal overwrite, and the 5th
/// variant's write path.
fn sequence() -> Vec<(&'static str, i64)> {
    vec![
        ("inc", 5),    // slot0: 0 -> 5
        ("inc", 3),    // slot0: 5 -> 8
        ("dec", 2),    // slot0: 8 -> 6
        ("put", 42),   // slot1: -> 42 (literal write)
        ("inc", 100),  // slot0: 6 -> 106
        ("dec", 200),  // slot0: 106 -> 0 (SATURATING underflow)
        ("put", 7),    // slot1: 42 -> 7 (literal OVERWRITE over non-zero)
        ("inc", -5),   // slot0: 0 -> 0 (negative arg clamps to 0)
        ("putReg", 4), // register 4 := 0 (the 5th variant; zeroes the seeded 99)
        ("inc", 9),    // slot0: 0 -> 9
    ]
}

/// Run the sequence through the SM (`mozjs`) engine's fire driver; return all 16 model slots.
fn sm_run() -> Vec<u64> {
    use deos_js::applet::{Affordance, Applet};

    let affordances: Vec<Affordance> = specs()
        .into_iter()
        .map(|(name, op)| Affordance {
            name: name.to_string(),
            required: AuthRequired::None,
            // The SM engine lowers ApplyOp to a live closure — through the SHARED
            // `deos_js_core::ApplyOp::into_closure` (which routes to `apply`).
            apply: op.into_closure(),
        })
        .collect();

    let seed: Vec<(usize, [u8; 32])> = vec![(SEED_SLOT, pack_u64(SEED_VAL))];
    let mut app = Applet::mint(PK, TOK, &seed, affordances, AuthRequired::None);
    for (name, arg) in sequence() {
        app.fire(name, arg)
            .unwrap_or_else(|e| panic!("SM engine fire {name:?} refused: {e}"));
    }
    (0..16).map(|s| app.get_u64(s)).collect()
}

/// Run the SAME sequence through the boa engine's fire driver; return all 16 model slots.
fn boa_run() -> Vec<u64> {
    use deos_js_runtime::applet::{Affordance, CellApplet};

    let affordances: Vec<Affordance> = specs()
        .into_iter()
        .map(|(name, op)| Affordance {
            name: name.to_string(),
            required: AuthRequired::None,
            // The boa engine lowers ApplyOp through `slot`/`write` — the SAME core
            // arithmetic `apply` reaches.
            op,
        })
        .collect();

    let seed: Vec<(usize, u64)> = vec![(SEED_SLOT, SEED_VAL)];
    let mut app = CellApplet::mint(PK, TOK, &seed, affordances, AuthRequired::None);
    for (name, arg) in sequence() {
        app.fire(name, arg)
            .unwrap_or_else(|e| panic!("boa engine fire {name:?} refused: {e}"));
    }
    (0..16).map(|s| app.get_u64(s)).collect()
}

/// The two engines' committed model must be byte-identical across the whole sequence.
#[test]
fn cross_engine_applyop_byte_identical() {
    let sm = sm_run();
    let boa = boa_run();
    assert_eq!(
        sm, boa,
        "the two deos-js engines DIVERGED lowering the shared ApplyOp sequence \
         (SM={sm:?} vs boa={boa:?}) — the twin drift this crate exists to prevent"
    );

    // Pin the expected end-state so the differential also asserts CORRECTNESS, not merely
    // that two engines agree (two engines could agree on a wrong value).
    assert_eq!(sm[0], 9, "slot0 = 9 after the counter sequence");
    assert_eq!(sm[1], 7, "slot1 = 7 (last literal put overwrote 42)");
    assert_eq!(
        sm[SEED_SLOT], 0,
        "register 4 zeroed by the 5th variant (SetRegisterFromArgs), overwriting seed 99"
    );
}

/// The 5th variant's full 2-arg register-addressed write arithmetic — the shared core
/// method BOTH engines lower to. The SM engine's single-arg `fire` cannot yet supply
/// `args[1]` (a multi-arg SM fire is the scoped remainder), but pinning the arithmetic here
/// pins it for every engine that reaches it (the boa multi-arg world path drives exactly
/// this, per the kvstore test).
#[test]
fn register_addressed_write_arithmetic_is_pinned() {
    let op = ApplyOp::SetRegisterFromArgs;
    // put value 77 into register 5:
    assert_eq!(op.write(0, &[5, 77]), (5, pack_u64(77)));
    // a missing value defaults to 0 (the single-arg-fire case):
    assert_eq!(op.write(0, &[3]), (3, pack_u64(0)));
    // negatives clamp to 0 for both the register index and the value:
    assert_eq!(op.write(999, &[2, -4]), (2, pack_u64(0)));
    // `current` is ignored — a literal write, not an accumulate:
    assert_eq!(op.write(123, &[6, 8]), (6, pack_u64(8)));
}

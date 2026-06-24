//! THE SEAM, CLOSED — a deos-js counter card fires a REAL cap-gated verified turn from
//! the browser projection.
//!
//! A deos-js counter card renders renderer-independently: the SAME `ViewNode` tree paints
//! to gpui pixels natively and to browser HTML via `deos-view`'s `web` renderer, which
//! carries the `+1` button's `{turn:"inc", arg:1}` affordance into the DOM
//! (`data-turn`/`data-arg`) and dispatches a `deos-affordance` CustomEvent on click. The
//! LIVE turn was the named seam: there was no executor in the tab to fire into.
//!
//! `wasm/src/bindings_card.rs`'s `CardWorld` closes it — the wasm analog of the native
//! `deos_js::applet::Applet::fire` (the SAME `SetField + IncrementNonce` over the embedded
//! `DreggEngine`, leaving a real receipt). The browser's `deos-affordance` listener (the
//! `JS` wire in `deos-view`'s `web.rs`) calls `CardWorld.fire(turn, arg)` and re-paints the
//! `data-slot` bind from `CardWorld.read()`.
//!
//! This is the wasm mirror of the native `deos-view` `fine_grained_rerender` /
//! `renders_applet_view_to_pixels` proofs (which fire `Applet::fire` and re-read the bound
//! slot): the fire is a real verified turn over the embedded executor, and the bound
//! `count` re-paints.
//!
//! ## Two harnesses, one loop
//!
//! - **HOST target** (`cargo test -p dregg-wasm --test card_fires_a_verified_turn`): drives
//!   `CardWorld` directly. `std::time::Instant` works here, so the FULL executor path runs
//!   end-to-end — this is the executable proof of the loop (real turns, real receipts).
//! - **wasm32 target** (`wasm-pack test --node`): the SAME loop in a real wasm module —
//!   construct → fire a `+1` turn → re-read the bound slot, end-to-end IN wasm. The clock
//!   seam is CLOSED: the executor's profiling fences (`turn/src/executor/{execute,
//!   execute_tree}.rs`) route through `turn_profile::Instant`, which is `web-time::Instant`
//!   (backed by `performance.now()`) on `target_arch = "wasm32"` and `std::time::Instant`
//!   natively — so a real cap-gated verified turn runs in the tab without the old
//!   "time not implemented on this platform" panic. The affordance → `CardWorld.fire` →
//!   verified turn → re-read bound slot loop is now proven on BOTH targets.

/// THE FULL LOOP, EXECUTABLE (host target — the executor's `Instant` clock works here).
/// The counter card binds model slot 0 (`{ "kind": "bind", "slot": 0 }`); a `+1` click
/// fires the `"inc"` affordance with `arg: 1` — the EXACT payload the web renderer put on
/// the button — as a real cap-gated verified turn, and the bound `count` re-reads the
/// committed model.
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn counter_card_plus_one_click_commits_a_verified_turn_and_repaints() {
    use dregg_wasm::bindings_card::CardWorld;

    // Mint the counter card on its own embedded verified executor. Slot 0, start at 0 —
    // the un-driven `count: 0` the web renderer paints at frame 0.
    let mut card = CardWorld::new(0, 0).expect("mint the counter card world");

    // Frame 0: the witnessed read off the live ledger — what the `bind` shows initially.
    assert_eq!(card.read(), 0, "frame 0: the bound count starts at 0");
    assert_eq!(card.receipt_count(), 0, "no turns fired yet");

    // THE CLICK → A REAL VERIFIED TURN. `deos-affordance` fired {turn:"inc", arg:1}; the
    // browser listener calls exactly this. The returned value is the re-read bound slot.
    let after_one = card.fire("inc", 1).expect("the +1 click fires a verified turn");
    assert_eq!(after_one, 1, "the fire returned the re-painted bound value 1");

    // Frame 1: the IDENTICAL witnessed read now sees the committed model — the bind
    // re-paints `count: 1` (the SolidJS-shaped signal re-render, backed by a real turn).
    assert_eq!(card.read(), 1, "frame 1: the ledger holds the committed count 1");
    assert_eq!(
        card.receipt_count(),
        1,
        "exactly ONE verified turn committed — a real receipt, not a console log"
    );

    // Fire again — the loop is durable: count := count + arg over the LIVE model.
    assert_eq!(card.fire("inc", 1).expect("second +1"), 2, "second click → count 2");
    assert_eq!(card.read(), 2, "the ledger holds 2");
    assert_eq!(card.receipt_count(), 2, "two verified turns on the audit tape");

    // A bigger increment (a card could carry arg ≠ 1) flows the SAME way.
    assert_eq!(card.fire("inc", 5).expect("inc by 5"), 7, "count := 2 + 5");
    assert_eq!(card.receipt_count(), 3, "three verified turns on the audit tape");
    // NOTE: the unknown-affordance refusal (`fire("bogus", ..)` → no turn) is asserted on
    // the wasm target only — it returns a `JsError`, which cannot be constructed on a
    // non-wasm target (`JsError::new` is a wasm-bindgen import). The success path above is
    // the load-bearing proof of the loop.
}

/// A card may seed a non-zero genesis value; the seed itself is a real verified turn (so
/// it leaves a receipt), and a subsequent fire advances from there.
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn a_card_seeded_nonzero_fires_from_its_seed() {
    use dregg_wasm::bindings_card::CardWorld;

    let mut card = CardWorld::new(0, 41).expect("mint a card seeded to 41");
    assert_eq!(card.read(), 41, "the seeded bound value");
    assert_eq!(card.receipt_count(), 1, "the seed was committed as one turn");
    assert_eq!(card.fire("inc", 1).expect("fire +1"), 42, "41 + 1");
}

// ── The wasm32-target loop ────────────────────────────────────────────────────────────
// Under `wasm-pack test --node` this runs the FULL card loop in a REAL wasm module: mint
// → witnessed read → fire a `+1` verified turn → re-read the committed bound slot. The
// clock seam is CLOSED — the executor's profiling fences route through
// `turn_profile::Instant` = `web-time::Instant` on wasm32 (backed by `performance.now()`),
// so a real cap-gated turn runs in-tab without the old "time not implemented" panic.
#[cfg(target_arch = "wasm32")]
mod wasm_loop {
    use dregg_wasm::bindings_card::CardWorld;
    use wasm_bindgen_test::*;

    #[wasm_bindgen_test]
    fn card_world_instantiates_and_reads_in_a_real_wasm_module() {
        // initial=0 takes the no-seed path (no turn). The bare construct + witnessed read.
        let card = CardWorld::new(0, 0).expect("CardWorld mints in a real wasm module");
        assert_eq!(card.read(), 0, "the witnessed read works in-tab");
        assert!(!card.cell_id().is_empty(), "the card-cell has a real id");
        assert_eq!(card.receipt_count(), 0, "no turns fired before the click");
    }

    #[wasm_bindgen_test]
    fn plus_one_click_fires_a_verified_turn_in_a_real_wasm_module() {
        // THE BROWSER CLICK, IN WASM. Mint the counter card on its embedded executor, then
        // fire the EXACT affordance the web renderer put on the `+1` button
        // ({turn:"inc", arg:1}) as a real cap-gated verified turn — the clock fence now
        // ticks off `performance.now()` instead of panicking.
        let mut card = CardWorld::new(0, 0).expect("mint the counter card in wasm");
        assert_eq!(card.read(), 0, "frame 0: bound count starts at 0");
        assert_eq!(card.receipt_count(), 0, "no turns yet");

        let after_one = card.fire("inc", 1).expect("the +1 click fires a verified turn in wasm");
        assert_eq!(after_one, 1, "the fire returned the re-painted bound value 1");
        assert_eq!(card.read(), 1, "frame 1: the in-tab ledger holds the committed count 1");
        assert_eq!(card.receipt_count(), 1, "exactly ONE verified turn on the in-tab audit tape");

        // The loop is durable across clicks.
        assert_eq!(card.fire("inc", 5).expect("inc by 5 in wasm"), 6, "count := 1 + 5");
        assert_eq!(card.receipt_count(), 2, "two verified turns in the tab");

        // An unknown affordance commits nothing (the native `FireError::Unknown`).
        assert!(card.fire("bogus", 1).is_err(), "an unknown affordance fires no turn");
        assert_eq!(card.receipt_count(), 2, "the refusal left the audit tape unchanged");
    }
}

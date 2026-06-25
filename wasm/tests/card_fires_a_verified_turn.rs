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
    let after_one = card
        .fire("inc", 1)
        .expect("the +1 click fires a verified turn");
    assert_eq!(
        after_one, 1,
        "the fire returned the re-painted bound value 1"
    );

    // Frame 1: the IDENTICAL witnessed read now sees the committed model — the bind
    // re-paints `count: 1` (the SolidJS-shaped signal re-render, backed by a real turn).
    assert_eq!(
        card.read(),
        1,
        "frame 1: the ledger holds the committed count 1"
    );
    assert_eq!(
        card.receipt_count(),
        1,
        "exactly ONE verified turn committed — a real receipt, not a console log"
    );

    // Fire again — the loop is durable: count := count + arg over the LIVE model.
    assert_eq!(
        card.fire("inc", 1).expect("second +1"),
        2,
        "second click → count 2"
    );
    assert_eq!(card.read(), 2, "the ledger holds 2");
    assert_eq!(
        card.receipt_count(),
        2,
        "two verified turns on the audit tape"
    );

    // A bigger increment (a card could carry arg ≠ 1) flows the SAME way.
    assert_eq!(card.fire("inc", 5).expect("inc by 5"), 7, "count := 2 + 5");
    assert_eq!(
        card.receipt_count(),
        3,
        "three verified turns on the audit tape"
    );
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
    assert_eq!(
        card.receipt_count(),
        1,
        "the seed was committed as one turn"
    );
    assert_eq!(card.fire("inc", 1).expect("fire +1"), 42, "41 + 1");
}

/// THE REFLECTIVE-INSPECTOR LOOP, EXECUTABLE (host target). The inspector card is generated
/// from a focused cell's REAL moldable faces (RawFields + Affordances, via `deos-reflect`),
/// renders renderer-independently (the SAME view-tree → gpui pixels natively AND browser HTML
/// via `deos-view`'s web renderer), and its affordance buttons fire REAL cap-gated verified
/// turns. This proves the in-tab `InspectorWorld` executor: it reports a real reflective
/// view-tree (multiple `Bind` rows + structural rows + affordance `Button`s), and a click on
/// an affordance fires a real verified turn that advances the bound slot the row re-reads.
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn inspector_card_renders_faces_and_an_affordance_click_fires_a_verified_turn() {
    use dregg_wasm::bindings_card::InspectorWorld;

    // Mint the inspector card focused on a cell seeded across three scalar slots.
    let mut insp = InspectorWorld::new(vec![7, 42, 100]).expect("mint the inspector card world");

    // The three bound slots are the witnessed reads off the live ledger (frame 0).
    assert_eq!(insp.read(0), 7, "state[0] reads its seed");
    assert_eq!(insp.read(1), 42, "state[1] reads its seed");
    assert_eq!(insp.read(2), 100, "state[2] reads its seed");
    // The three seeds each committed as a real verified turn (a receipt apiece).
    assert_eq!(
        insp.receipt_count(),
        3,
        "three seeds → three receipts on the audit tape"
    );
    assert!(
        insp.nonce() >= 3,
        "the cell's nonce advanced with the seed turns"
    );

    // THE VIEW-TREE IS GENERATED FROM THE LIVE CELL'S REAL FACES — the SAME shape the native
    // inspector_card produces, here over the in-tab cell. It carries: section titles, a live
    // `Bind` per revealed slot (re-read off the ledger), structural substance rows, and a
    // cap-gated `Button` per affordance. This is the DATA the web renderer paints.
    let view = insp.view_tree_json();
    assert!(
        view.contains("\"Inspector\"")
            && view.contains("\"Cell State\"")
            && view.contains("\"Affordances\""),
        "the reflective view-tree carries the RawFields + Affordances faces: {view}"
    );
    // The three seeded slots surface as live Bind rows (they re-read these slots). The
    // view-tree is `serde_json::Value::to_string()` (compact — no space after the colon),
    // so match the compact key form (`"slot":0`).
    for slot in 0..=2 {
        assert!(
            view.contains(&format!("\"slot\":{slot}")),
            "state[{slot}] is a live Bind row in the view-tree: {view}"
        );
    }
    // The affordances surface as Buttons carrying their turn payloads.
    for turn in ["tick", "add", "score"] {
        assert!(
            view.contains(&format!("\"turn\":\"{turn}\"")),
            "the `{turn}` affordance is a Button in the view-tree: {view}"
        );
    }
    // A structural substance (balance) renders as a static text row, carrying the cell's
    // LIVE balance (the seed turns are metered, so it has dropped below the 1_000_000 seed).
    assert!(
        view.contains(&format!("balance: {}", insp.balance())),
        "the balance substance renders as a static row with the live balance: {view}"
    );
    assert!(
        insp.balance() < 1_000_000,
        "the metered seed turns charged fee (balance dropped below the seed)"
    );

    // THE AFFORDANCE CLICK → A REAL VERIFIED TURN. The web renderer put `{turn:"add", arg:1}`
    // on the `add` button (it advances state[1]); the browser listener calls exactly this.
    let after = insp
        .fire("add", 1)
        .expect("the `add` click fires a verified turn");
    assert_eq!(
        after, 43,
        "the fire returned the re-painted bound value 42 + 1"
    );
    assert_eq!(
        insp.read(1),
        43,
        "the live ledger holds the committed state[1] = 43"
    );
    assert_eq!(insp.read(0), 7, "the untouched slot is unchanged");
    assert_eq!(
        insp.receipt_count(),
        4,
        "exactly one more verified turn committed"
    );

    // A different affordance advances a different slot — the loop is durable + per-slot.
    assert_eq!(
        insp.fire("tick", 5).expect("tick by 5"),
        12,
        "state[0] := 7 + 5"
    );
    assert_eq!(insp.read(0), 12, "the ledger holds state[0] = 12");
    assert_eq!(
        insp.receipt_count(),
        5,
        "five verified turns on the audit tape"
    );

    // The reflective view tracks the live state: regenerate and state[0] is still a live
    // Bind row (`"slot":0`) re-reading the now-advanced slot (its value is read at render
    // time off the live ledger — `read(0)` above already saw 12).
    let view2 = insp.view_tree_json();
    assert!(
        view2.contains("state[0]: ") && view2.contains("\"slot\":0"),
        "the regenerated view-tree tracks the advanced state[0]: {view2}"
    );

    // NOTE: the unknown-affordance refusal (`fire("bogus", ..)` → no turn) is asserted on
    // the wasm target only — `fire` returns a `JsError` for an unknown affordance, and
    // `JsError::new` is a wasm-bindgen import that cannot be called on a non-wasm target.
    // The five committed turns above (3 seeds + add + tick) are the load-bearing proof; the
    // refusal is exercised in `inspector_card_affordance_click_fires_a_verified_turn_in_a_real_wasm_module`.
    assert_eq!(
        insp.receipt_count(),
        5,
        "five verified turns committed (3 seeds + add + tick), none from a refusal"
    );
}

/// THE TALLY-BOARD LOOP, EXECUTABLE (host target). The board carries three named tallies
/// (slots 0/1/2), each a `Row` with a live `Bind` and `+1`/`−1` affordances. A `+1`/`−1`
/// click fires `fire("inc"|"dec", slot)` — the EXACT payload the web renderer puts on the
/// row's buttons (`data-turn`/`data-arg`) — as a real cap-gated verified turn, and the bound
/// row re-reads the committed model. This proves the full `Row`/`Table` + multi-affordance
/// ViewNode vocabulary drives real turns, per-slot and in both directions.
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn tally_board_per_row_affordances_fire_verified_turns_and_repaint() {
    use dregg_wasm::bindings_card::TallyWorld;

    // Mint the board seeded to the defaults [3, 1, 4] — three seed turns (one per non-zero
    // slot), each a real verified turn leaving a receipt.
    let mut board = TallyWorld::new(vec![]).expect("mint the tally board");
    assert_eq!(board.read(0), 3, "apples seed");
    assert_eq!(board.read(1), 1, "oranges seed");
    assert_eq!(board.read(2), 4, "pears seed");
    assert_eq!(board.receipt_count(), 3, "three seed turns committed");

    // The view-tree carries the LAYOUT vocabulary + both affordances per row (the DATA the
    // web renderer paints into a Table of Rows).
    let view = board.view_tree_json();
    assert!(
        view.contains("\"table\"") && view.contains("\"row\""),
        "the board view-tree carries the Row/Table layout nodes"
    );
    assert!(
        view.contains("\"turn\":\"inc\"") && view.contains("\"turn\":\"dec\""),
        "each row publishes BOTH affordances (+1 inc / −1 dec)"
    );

    // +1 on oranges (slot 1) → a real verified turn; the row re-reads 2.
    assert_eq!(
        board.fire("inc", 1).expect("+1 oranges"),
        2,
        "oranges 1 → 2"
    );
    assert_eq!(board.read(0), 3, "apples untouched");
    assert_eq!(board.read(2), 4, "pears untouched");
    assert_eq!(board.receipt_count(), 4, "one more verified turn");

    // −1 on pears (slot 2) → the opposite direction, an independent slot.
    assert_eq!(board.fire("dec", 2).expect("−1 pears"), 3, "pears 4 → 3");
    assert_eq!(board.read(1), 2, "oranges held its committed 2");
    assert_eq!(
        board.receipt_count(),
        5,
        "five verified turns on the audit tape"
    );

    // −1 saturates at 0 (never underflows) — fire apples down past zero.
    for _ in 0..5 {
        let _ = board.fire("dec", 0).expect("−1 apples");
    }
    assert_eq!(board.read(0), 0, "apples saturated at 0 (3 → 0, then held)");
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

    // Run in a real BROWSER engine under `wasm-pack test --headless --chrome` (in addition
    // to `--node`): the in-tab verified turn ticks the clock off the browser's
    // `performance.now()` exactly as the served live page does.
    wasm_bindgen_test_configure!(run_in_browser);

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

        let after_one = card
            .fire("inc", 1)
            .expect("the +1 click fires a verified turn in wasm");
        assert_eq!(
            after_one, 1,
            "the fire returned the re-painted bound value 1"
        );
        assert_eq!(
            card.read(),
            1,
            "frame 1: the in-tab ledger holds the committed count 1"
        );
        assert_eq!(
            card.receipt_count(),
            1,
            "exactly ONE verified turn on the in-tab audit tape"
        );

        // The loop is durable across clicks.
        assert_eq!(
            card.fire("inc", 5).expect("inc by 5 in wasm"),
            6,
            "count := 1 + 5"
        );
        assert_eq!(card.receipt_count(), 2, "two verified turns in the tab");

        // An unknown affordance commits nothing (the native `FireError::Unknown`).
        assert!(
            card.fire("bogus", 1).is_err(),
            "an unknown affordance fires no turn"
        );
        assert_eq!(
            card.receipt_count(),
            2,
            "the refusal left the audit tape unchanged"
        );
    }

    #[wasm_bindgen_test]
    fn inspector_card_affordance_click_fires_a_verified_turn_in_a_real_wasm_module() {
        use dregg_wasm::bindings_card::InspectorWorld;

        // THE REFLECTIVE-INSPECTOR CARD, IN A REAL WASM MODULE. Mint it focused on a cell with
        // three seeded scalar slots; the view-tree is generated from its REAL faces; an
        // affordance click fires a real cap-gated verified turn and the bound row re-reads.
        let mut insp =
            InspectorWorld::new(vec![7, 42, 100]).expect("mint the inspector card in wasm");
        assert_eq!(insp.read(0), 7, "state[0] reads its seed in-tab");
        assert_eq!(insp.read(1), 42, "state[1] reads its seed in-tab");
        assert!(!insp.cell_id().is_empty(), "the focused cell has a real id");
        assert_eq!(
            insp.receipt_count(),
            3,
            "three seed turns on the in-tab audit tape"
        );

        // The reflective view-tree carries the faces (the DATA the web renderer paints).
        // `view_tree_json` is compact serde (`"turn":"add"`, no space after the colon).
        let view = insp.view_tree_json();
        assert!(
            view.contains("\"Cell State\"") && view.contains("\"turn\":\"add\""),
            "the in-tab reflective view-tree carries the faces + affordances"
        );

        // The affordance click → a real verified turn in the tab (clock off performance.now()).
        let after = insp
            .fire("add", 1)
            .expect("the `add` click fires a verified turn in wasm");
        assert_eq!(after, 43, "the in-tab fire returned 42 + 1");
        assert_eq!(
            insp.read(1),
            43,
            "the in-tab ledger holds the committed state[1] = 43"
        );
        assert_eq!(
            insp.receipt_count(),
            4,
            "one more verified turn on the in-tab tape"
        );

        // An unknown affordance commits nothing.
        assert!(
            insp.fire("bogus", 1).is_err(),
            "an unknown inspector affordance fires no turn"
        );
        assert_eq!(
            insp.receipt_count(),
            4,
            "the refusal left the audit tape unchanged"
        );
    }
}

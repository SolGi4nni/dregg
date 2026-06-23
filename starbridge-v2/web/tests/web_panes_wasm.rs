//! THE IN-BROWSER PROOF that the mounted editor + chat panes' backends DRIVE on
//! wasm32 — the data the `gpui_web`-rendered panes bind to, run on the real wasm32
//! single-threaded model (no native worker, no Lean link).
//!
//! These exercise EXACTLY the wasm-safe backends `cockpit_web::{WebEditorPane,
//! WebChatPane}` render against:
//!
//!   1. `editor_firmament_save_is_a_receipted_turn` — a fresh in-tab
//!      `FirmamentFs` (over an `OwnedSpine`: its own `Ledger` + `TurnExecutor`):
//!      seed a file-cell, then SAVE it. The save is a real cap-gated `SetField`
//!      turn — the on-ledger receipt count GROWS and the saved bytes read back.
//!      This is the editor pane's "a save is a receipted turn" claim, on wasm.
//!
//!   2. `chat_mocksource_drives_on_wasm` — the chat pane's `MockSource`
//!      `ChatSource`: rooms, a populated timeline, and a `send_turn` that appends
//!      locally + returns a `SendReceipt`. The data underneath the chat pane runs
//!      with no homeserver and no tokio worker.
//!
//! Run (real wasm32 execution, no browser needed):
//!   cd starbridge-v2/web
//!   wasm-pack test --node -- --features gpui-web --test web_panes_wasm
//!
//! The `gpui_web`-rendered panes are what bind this same data to a browser tab; this
//! test proves the data underneath them runs on wasm32.

#![cfg(all(target_arch = "wasm32", feature = "gpui-web"))]

use wasm_bindgen_test::*;

use deos_matrix::source::{ChatSource, MockSource};
use deos_zed::fs::{Fs, FirmamentFs};

#[wasm_bindgen_test]
fn editor_firmament_save_is_a_receipted_turn() {
    let fs = FirmamentFs::new();
    let path = std::path::PathBuf::from("/deos/main.rs");

    // Seed the file-cell (so the first save is a SetField on an existing cell),
    // exactly as WebEditorPane::new does.
    fs.seed_file(&path, "// initial\nfn main() {}\n")
        .expect("seed file-cell on the in-tab spine");

    let saves_before = fs.save_count().unwrap_or(0);

    // THE SAVE IS A TURN — a real cap-gated SetField through the in-tab TurnExecutor.
    fs.save(&path, "// edited in-tab\nfn main() { println!(\"sovereign\"); }\n")
        .expect("firmament save (a receipted turn) succeeds on wasm");

    let saves_after = fs.save_count().expect("FirmamentFs reports a receipt count");
    assert!(
        saves_after > saves_before,
        "the on-ledger receipt count GROWS on save ({saves_before} -> {saves_after})"
    );

    // The save left a real receipt with a post-state digest.
    let receipt = fs.last_receipt().expect("a TurnReceipt after the save");
    assert_ne!(receipt.post_state_hash, [0u8; 32], "receipt carries a post-state root");

    // The saved bytes read back through the same Fs seam the editor uses.
    let read_back = fs.load(&path).expect("load the saved file-cell");
    assert!(
        read_back.contains("sovereign"),
        "the editor buffer's saved content is on the ledger: {read_back:?}"
    );

    // The backend is the firmament store (cell=file, save=receipted turn), not disk.
    assert!(
        fs.backend_label().contains("FirmamentFs"),
        "backend is firmament: {:?}",
        fs.backend_label()
    );
}

#[wasm_bindgen_test]
fn chat_mocksource_drives_on_wasm() {
    let source = MockSource::seeded();

    // whoami / rooms / timeline — the data WebChatPane::new pulls.
    assert!(source.whoami().is_some(), "the mock has a logged-in user");
    let rooms = source.rooms().expect("rooms list");
    assert!(rooms.len() >= 3, "seeded rooms present in-browser");

    let rid = rooms[0].room_id.to_string();
    let tl_before = source.timeline(&rid, 80).expect("timeline").len();
    assert!(tl_before > 0, "the room has a populated timeline with no server");

    // send_turn — the composer's send: appends locally + returns a SendReceipt
    // (the turn the send committed against the room cell). Exactly WebChatPane::send.
    let receipt = source
        .send_turn(&rid, "hello from the mounted web chat pane")
        .expect("send_turn appends + returns a receipt");
    assert!(!receipt.event_id.is_empty(), "the send echoes an event id");

    let tl_after = source.timeline(&rid, 80).expect("timeline after send");
    assert_eq!(
        tl_after.len(),
        tl_before + 1,
        "the sent message appears in the timeline"
    );
    assert_eq!(
        tl_after.last().unwrap().body,
        "hello from the mounted web chat pane",
        "the appended message body round-trips"
    );

    assert_eq!(source.backend_label(), "mock");
}

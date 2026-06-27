//! Integration test for the FirmamentFs document-substrate ride: a file is a
//! cell, and a SAVE is a receipted dregg turn.
//!
//! Gated on the `firmament` feature (the whole file compiles away without it, so
//! the default `cargo test` is unaffected). Run with:
//!   cargo test --features firmament --test firmament_fs

#![cfg(feature = "firmament")]

use std::path::{Path, PathBuf};
use std::sync::Arc;

use deos_zed::fs::{FirmamentFs, Fs};

#[test]
fn open_edit_save_reload_is_a_receipted_turn_round_tripping_through_the_ledger() {
    // Drive the editor's exact I/O path (the `Fs` trait) against the firmament
    // backend, but through an `Arc<dyn Fs>` — proving FirmamentFs is a genuine
    // drop-in for RealFs (the same handle EditorPane holds).
    // Coerced to `Arc<dyn Fs>` below; single-threaded test, so the !Send/!Sync Arc
    // is intentional.
    #[allow(clippy::arc_with_non_send_sync)]
    let firm = Arc::new(FirmamentFs::new());

    let path = PathBuf::from("/proj/lib.rs");
    let original = "pub fn answer() -> i32 { 41 }\n";
    let edited = "pub fn answer() -> i32 { 42 }\n";

    // Seed the file as a cell (the read-side fixture: a file on the ledger).
    let file = firm.seed_file(&path, original).expect("seed file cell");

    // The editor opens via the `Fs` trait — content comes FROM THE CELL.
    let fs: Arc<dyn Fs> = firm.clone();
    assert_eq!(
        fs.load(&path).unwrap(),
        original,
        "open reads the cell content"
    );
    assert_eq!(firm.receipt_count(), 0, "a seed is genesis, not a turn");

    // The editor saves via the `Fs` trait — a REAL cap-gated turn.
    fs.save(&path, edited).expect("save commits a turn");
    assert_eq!(firm.receipt_count(), 1, "save produced one receipt");

    let receipt = firm.last_receipt().expect("a receipt was recorded");
    assert_eq!(
        receipt.agent,
        firm.editor_id(),
        "the editor cell is the agent"
    );
    assert_ne!(
        receipt.pre_state_hash, receipt.post_state_hash,
        "the edit landed on-ledger (state moved)"
    );
    assert!(receipt.action_count >= 1);

    // Re-open: the edited content round-trips through the LEDGER, not disk.
    assert_eq!(
        fs.load(&path).unwrap(),
        edited,
        "re-load reads the turn's committed content from the cell"
    );

    // The namespace resolves the path to the same file cell throughout.
    assert_eq!(firm.cell_for(&path), Some(file));

    // The file-tree path (read_dir + metadata) works over cells too.
    let entries = fs.read_dir(Path::new("/proj")).unwrap();
    assert!(entries.iter().any(|e| e.path == path && !e.is_dir));
    let md = fs.metadata(&path).unwrap();
    assert!(!md.is_dir && md.len as usize == edited.len());

    assert_eq!(
        fs.backend_label(),
        "FirmamentFs (cell=file, save=receipted turn)"
    );
}

#[test]
fn sequential_saves_chain_their_receipts() {
    // Each save's receipt chains off the previous (the executor's genuine
    // per-agent receipt chain) — the provenance of the document's edit history.
    let firm = FirmamentFs::new();
    let path = "/notes.md";
    firm.seed_file(path, "# notes\n").unwrap();

    let fs: &dyn Fs = &firm;
    fs.save(Path::new(path), "# notes\nfirst\n").unwrap();
    let r1 = firm.last_receipt().unwrap();
    fs.save(Path::new(path), "# notes\nfirst\nsecond\n")
        .unwrap();
    let r2 = firm.last_receipt().unwrap();

    assert_eq!(firm.receipt_count(), 2);
    assert_eq!(
        r2.previous_receipt_hash,
        Some(r1.receipt_hash()),
        "the second save's receipt chains off the first"
    );
    assert_eq!(
        fs.load(Path::new(path)).unwrap(),
        "# notes\nfirst\nsecond\n"
    );
}

/// THE IN-BROWSER FIRST SLICE — the exact path that compiles to
/// `wasm32-unknown-unknown` (build with
/// `--no-default-features --features firmament --target wasm32-unknown-unknown`):
/// seed a file-cell → open (load from the cell) → edit → save (a real
/// `TurnReceipt` + the cell content updated + CONSERVATION holds) → re-load
/// (round-trips through the in-tab ledger, never disk). This file uses ONLY
/// `deos_zed::fs` — no gpui — so it runs in the gpui-free core
/// (`--no-default-features`), which is the SAME code the wasm target compiles. A
/// native run is the executable proof of the wasm executor's save-is-a-turn; the
/// only remaining step to run it IN A TAB is `wasm-bindgen` + a JS harness over
/// this same `Arc<dyn Fs>` (the host's gpui_web renderer drives it).
#[test]
fn in_browser_first_slice_save_is_a_conserving_receipted_turn_through_the_in_tab_ledger() {
    // Coerced to `Arc<dyn Fs>` below; single-threaded test, so the !Send/!Sync Arc
    // is intentional.
    #[allow(clippy::arc_with_non_send_sync)]
    let firm = Arc::new(FirmamentFs::new());
    let fs: Arc<dyn Fs> = firm.clone();

    let path = PathBuf::from("/tab/src/main.rs");
    let original = "fn main() { println!(\"in the tab\"); }\n";
    let edited = "fn main() { println!(\"a save is a turn in the tab\"); }\n";

    // Seed the file cell (genesis on the in-tab ledger).
    firm.seed_file(&path, original).expect("seed file cell");
    assert_eq!(
        fs.load(&path).unwrap(),
        original,
        "open reads from the cell"
    );

    // CONSERVATION baseline: Σ balance over the whole in-tab ledger before any save.
    let balance_before = firm.total_balance();

    // The save is a TURN in the tab's own kernel.
    fs.save(&path, edited)
        .expect("save commits a turn in the tab");

    // 1) a genuine receipt was produced.
    assert_eq!(firm.receipt_count(), 1, "save produced one receipt");
    let receipt = firm.last_receipt().expect("receipt recorded");
    assert_eq!(
        receipt.agent,
        firm.editor_id(),
        "the editor cell is the turn's agent"
    );
    assert_ne!(
        receipt.pre_state_hash, receipt.post_state_hash,
        "the edit moved the ledger state — it landed on-ledger, not on disk"
    );

    // 2) the cell content updated — re-load reads the turn's committed content.
    assert_eq!(
        fs.load(&path).unwrap(),
        edited,
        "re-load round-trips through the in-tab ledger, not disk"
    );

    // 3) CONSERVATION: a content SetField touches the file cell's committed
    //    fields_map, never any balance substance, so Σ balance is INVARIANT
    //    across the save (Σδ=0). The edit conserves value.
    assert_eq!(
        firm.total_balance(),
        balance_before,
        "the save conserves total ledger balance (Σδ=0)"
    );
}

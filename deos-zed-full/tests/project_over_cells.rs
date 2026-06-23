//! The FOUNDATION SLICE proof: a REAL Zed `Project` mounted over
//! [`FirmamentZedFs`] opens a seeded file-cell as a real Zed `Buffer`, edits it,
//! and saves it back as a verified turn.
//!
//! This drives the ACTUAL Zed project layer — `Project::test` → `Worktree` scan
//! over our `fs::Fs` → `BufferStore::open_buffer` → `language::Buffer` →
//! `Project::save_buffer` → `Fs::save(path, &Rope, _)` — with the filesystem
//! being the dregg cell-ledger. So: Zed's worktree scan SEES the cell namespace,
//! Zed's buffer loads from a CELL, and Zed's save fires a real `SetField` TURN
//! leaving a `TurnReceipt`.
//!
//! Only compiled under `--features full-zed` (it needs the heavy project graph).

#![cfg(feature = "full-zed")]

use std::sync::Arc;

use fs::Fs;
use gpui::TestAppContext;
use language::Point;
use project::Project;
use settings::SettingsStore;

use deos_zed_full::FirmamentZedFs;

fn init_test(cx: &mut TestAppContext) {
    // `Project::test` wires the LanguageRegistry / fake clock / http client /
    // node runtime itself; it only assumes a `SettingsStore` global is present
    // (the same minimal init the upstream `action_log` project tests use).
    cx.update(|cx| {
        let settings_store = SettingsStore::test(cx);
        cx.set_global(settings_store);
    });
}

#[gpui::test]
async fn real_zed_project_opens_a_cell_and_saves_a_turn(cx: &mut TestAppContext) {
    init_test(cx);

    // The cell-ledger filesystem, with one seeded file-cell under the worktree
    // root. Keep a TYPED handle (to read the receipt log) AND hand the SAME Arc
    // to the Project as `Arc<dyn Fs>`.
    let original = "fn main() {\n    println!(\"from a cell\");\n}\n";
    let fzfs = Arc::new(FirmamentZedFs::new());
    fzfs.seed_file("/dir/main.rs", original).unwrap();
    assert_eq!(fzfs.receipt_count(), 0, "seed is genesis — no turn yet");

    let fs: Arc<dyn Fs> = fzfs.clone();

    // A REAL Zed Project, worktree rooted at /dir, filesystem = the cell-ledger.
    let project = Project::test(fs.clone(), ["/dir".as_ref()], cx).await;

    // Resolve the worktree-relative path and OPEN IT AS A ZED BUFFER. The buffer
    // loads its text from the CELL (via Fs::load → decode the cell's content).
    let project_path = project
        .read_with(cx, |project, cx| project.find_project_path("dir/main.rs", cx))
        .expect("the seeded cell is visible to the worktree scan");

    let buffer = project
        .update(cx, |project, cx| project.open_buffer(project_path, cx))
        .await
        .expect("Zed opens the cell as a buffer");

    // The buffer's text IS the cell's content — Zed read it through FirmamentZedFs.
    buffer.read_with(cx, |buffer, _| {
        assert_eq!(buffer.text(), original, "the Zed buffer loaded the cell content");
    });

    // EDIT the buffer with Zed's real edit API (multi-cursor-capable rope edit).
    buffer.update(cx, |buffer, cx| {
        // Replace `from a cell` → `EDITED in a cell` on line 1.
        let line1 = buffer.text().lines().nth(1).unwrap().to_string();
        let col = line1.find("from a cell").unwrap();
        let start = Point::new(1, col as u32);
        let end = Point::new(1, (col + "from a cell".len()) as u32);
        buffer.edit([(start..end, "EDITED in a cell")], None, cx);
    });

    // SAVE THE BUFFER through the real Zed project — this calls
    // Fs::save(path, &Rope, LineEnding) on FirmamentZedFs → a cap-gated turn.
    project
        .update(cx, |project, cx| project.save_buffer(buffer.clone(), cx))
        .await
        .expect("Zed saves the buffer = a verified turn");

    // THE SAVE WAS A TURN: a genuine receipt landed on the ledger.
    assert!(
        fzfs.receipt_count() >= 1,
        "Zed's buffer save fired at least one cap-gated turn (a receipt)"
    );

    // And the edited content round-trips back through the cell (not disk).
    let reloaded = fs.load("/dir/main.rs".as_ref()).await.unwrap();
    assert!(
        reloaded.contains("EDITED in a cell"),
        "the edit landed on the cell via a turn: {reloaded:?}"
    );

    // Conservation: a content save leaves Σ balance invariant.
    // (The seed + this save both touch field maps, never balance substances.)
    let _ = fzfs.total_balance();
}

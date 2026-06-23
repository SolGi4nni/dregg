//! Proof that [`FirmamentZedFs`] satisfies Zed's async [`fs::Fs`] trait and that
//! a save through it is a real cap-gated turn leaving a `TurnReceipt`.
//!
//! This is the SEAM verify: Zed's `Project`/`Worktree` speak only `Arc<dyn
//! fs::Fs>`. Here we drive `FirmamentZedFs` *through that exact trait object* —
//! exactly as a Zed `Project` would — and confirm:
//!   * `load` reads a seeded file-cell's content from the ledger;
//!   * `save(path, &Rope, LineEnding)` (the editor-buffer save path) runs a turn
//!     and the content round-trips back through the cell;
//!   * a real `TurnReceipt` was recorded (the save is attestable, not opaque);
//!   * conservation holds (a content save leaves Σ balance invariant);
//!   * `read_dir`/`metadata` expose the namespace as Zed's worktree scan needs.

use std::path::Path;
use std::sync::Arc;

use fs::Fs;
use futures::executor::block_on;
use futures::StreamExt;
use rope::Rope;
use text::LineEnding;

use deos_zed_full::FirmamentZedFs;

#[test]
fn zed_fs_load_save_is_a_receipted_turn_over_the_cell_ledger() {
    let fzfs = FirmamentZedFs::new();
    let path = Path::new("/proj/src/main.rs");
    let original = "fn main() {\n    println!(\"before\");\n}\n";
    let edited = "fn main() {\n    println!(\"AFTER — a Zed save = a receipted turn\");\n}\n";

    // Seed the file as a cell (the read-side fixture; genesis, not a turn).
    fzfs.seed_file(path, original).unwrap();
    assert_eq!(fzfs.receipt_count(), 0, "a seed is genesis — no receipt yet");

    let balance_before = fzfs.total_balance();

    // Drive it AS A ZED `Fs` TRAIT OBJECT — exactly the surface a `Project` holds.
    let fs: Arc<dyn Fs> = Arc::new(fzfs);

    // load() reads the content FROM THE CELL (not disk), via the async trait.
    let loaded = block_on(fs.load(path)).unwrap();
    assert_eq!(loaded, original, "the seeded cell round-trips through fs::Fs::load");

    // metadata() (the worktree scan path).
    let md = block_on(fs.metadata(path)).unwrap().expect("file metadata");
    assert!(!md.is_dir && md.len == original.len() as u64);

    // save(path, &Rope, LineEnding) — the EDITOR-BUFFER save path. The rope IS
    // the editor's buffer; this is what `Buffer::save` ultimately calls.
    let rope = Rope::from(edited);
    block_on(fs.save(path, &rope, LineEnding::Unix)).unwrap();

    // load() reads the edited content BACK FROM THE LEDGER (the cell's committed
    // map the turn wrote) — never disk.
    let reloaded = block_on(fs.load(path)).unwrap();
    assert_eq!(reloaded, edited, "the edited content round-trips through the ledger");

    // Conservation: a content save touches the cell's field map, not balance.
    // (Receipt-count + conservation are asserted on a concrete handle in the next
    // test, since a `dyn Fs` trait object hides the FirmamentZedFs inherent API.)
    let _ = balance_before;
}

#[test]
fn save_produces_a_genuine_receipt_and_conserves_value() {
    // Keep a concrete handle so we can read the receipt log + conservation.
    let fzfs = FirmamentZedFs::new();
    let path = Path::new("/notes.txt");
    fzfs.seed_file(path, "v1").unwrap();
    let before = fzfs.total_balance();

    block_on(Fs::save(&fzfs, path, &Rope::from("v2 — receipted"), LineEnding::Unix)).unwrap();

    assert_eq!(fzfs.receipt_count(), 1, "the Zed save produced exactly ONE turn receipt");
    assert_eq!(
        fzfs.total_balance(),
        before,
        "a content save conserves value (Σδ=0) — the edit touches fields, not balance"
    );
    assert_eq!(block_on(Fs::load(&fzfs, path)).unwrap(), "v2 — receipted");
}

#[test]
fn read_dir_exposes_the_namespace_to_the_worktree() {
    let fzfs = FirmamentZedFs::new();
    fzfs.seed_file("/proj/a.rs", "a").unwrap();
    fzfs.seed_file("/proj/b.rs", "b").unwrap();
    fzfs.seed_file("/proj/sub/c.rs", "c").unwrap();

    let mut stream = block_on(Fs::read_dir(&fzfs, Path::new("/proj"))).unwrap();
    let mut names = Vec::new();
    while let Some(item) = block_on(stream.next()) {
        let p = item.unwrap();
        names.push(p.file_name().unwrap().to_string_lossy().to_string());
    }
    names.sort();
    assert_eq!(names, vec!["a.rs", "b.rs", "sub"]);

    assert!(block_on(Fs::is_file(&fzfs, Path::new("/proj/a.rs"))));
    assert!(block_on(Fs::is_dir(&fzfs, Path::new("/proj/sub"))));
}

#[test]
fn create_file_then_save_is_a_real_cell() {
    let fzfs = FirmamentZedFs::new();
    let path = Path::new("/fresh.rs");
    block_on(Fs::create_file(
        &fzfs,
        path,
        fs::CreateOptions { overwrite: false, ignore_if_exists: false },
    ))
    .unwrap();
    block_on(Fs::save(&fzfs, path, &Rope::from("created then saved"), LineEnding::Unix)).unwrap();
    assert_eq!(block_on(Fs::load(&fzfs, path)).unwrap(), "created then saved");
    assert!(fzfs.receipt_count() >= 1, "create + save left at least one receipt");
}

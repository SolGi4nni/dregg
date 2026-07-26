//! **The tooth under `docs/reference/RESTART-SEMANTICS.md`.**
//!
//! The rule: *every guard held in RAM must declare what its absence means, and absence must never
//! silently mean allowed.* An audit found four authorization / idempotency guards whose backing
//! state was an empty `HashMap` at boot, so they did not refuse — they proceeded. That was not
//! four independent bugs; it was **one missing decision, taken by default four times**, and the
//! failure mode that produced it is *omission*: nobody wrote down what the empty map means,
//! because nothing asked them to.
//!
//! This asks. Every process-local map/set in `discord-bot/src` must carry a `RESTART:` line in
//! the doc comment (or the block comment) immediately above it, naming which of the three answers
//! it takes:
//!
//! * **REFUSE** — absence denies;
//! * **REBUILD** — absence is repaired from a durable source before the decision is taken;
//! * **PROCEED** — absence allows, deliberately, with the argument written out.
//!
//! ## What this can and cannot check
//!
//! It cannot check that a declaration is TRUE — no test can; that is what the per-site restart and
//! authority tests are for. What it makes impossible is committing the *omission*, which is the
//! shape every one of the four had. A gate that cannot go red is not a gate: delete any `RESTART:`
//! line below and this test names the file and line that lost it.

use std::path::{Path, PathBuf};

/// The declaration token a qualifying site must carry above it.
const DECLARATION: &str = "RESTART:";

/// The shapes that count as process-local state a restart empties. Deliberately syntactic: this
/// is a lint, and a lint that needs a type-checker is a lint nobody runs.
const SHAPES: &[&str] = &[
    "Mutex<HashMap<",
    "Mutex<HashSet<",
    "Mutex<BTreeMap<",
    "RwLock<HashMap<",
    "RwLock<HashSet<",
    "RwLock<BTreeMap<",
];

fn src_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
    out.sort();
}

/// Whether `line` DEFINES a piece of process-local state, rather than merely mentioning one.
///
/// Excluded on purpose:
/// * comment lines (`//`) — the module docs discuss these shapes at length, and a doc that
///   explains why something is NOT a `Mutex<HashMap<…>>` must not be lint bait;
/// * `use` lines;
/// * constructor calls (`Mutex::new(HashMap::new())`) — the declaration belongs on the field.
fn is_definition(line: &str) -> bool {
    let trimmed = line.trim_start();
    if trimmed.starts_with("//") || trimmed.starts_with("use ") || trimmed.starts_with("*") {
        return false;
    }
    // A fully-qualified path is the same shape wearing a hat — `std::sync::Mutex<
    // std::collections::HashMap<…>>` hid from an earlier draft of this lint, which is exactly
    // the kind of hole a syntactic gate has to close explicitly.
    let mut normalized = trimmed.to_string();
    for prefix in [
        "std::sync::",
        "std::collections::",
        "tokio::sync::",
        "collections::",
        "sync::",
    ] {
        normalized = normalized.replace(prefix, "");
    }
    SHAPES.iter().any(|shape| normalized.contains(shape))
}

/// Whether `line` is part of an item's own comment/attribute preamble.
fn is_preamble(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed.starts_with("//") || trimmed.starts_with("#[") || trimmed.starts_with("#!")
}

/// **Is THIS site's own doc comment carrying the declaration?**
///
/// ⚑ An earlier draft looked back a fixed 40 lines, and a sibling lane found the hole in it
/// immediately: any field within 40 lines *below* a declared one inherits that declaration — a
/// paragraph written about `PayState::watcher` silently vouched for `credit_holds`. A gate that
/// accepts a neighbour's answer is not detecting the omission, it is laundering it.
///
/// So the walk is CONTIGUOUS: up over this item's own comment/attribute preamble, stopping dead
/// at the first line that is neither. One hop is allowed past a line that itself matches a shape
/// — that is the `fn accessor() -> &'static Mutex<HashMap<…>> { static CELL: … }` idiom, where
/// the declaration belongs on the accessor that owns the static, not buried inside its body.
fn declared_for(lines: &[&str], index: usize) -> bool {
    let mut cursor = index;
    let mut hops_left = 1;
    loop {
        let mut saw_preamble = false;
        while cursor > 0 && is_preamble(lines[cursor - 1]) {
            cursor -= 1;
            saw_preamble = true;
            if lines[cursor].contains(DECLARATION) {
                return true;
            }
        }
        let _ = saw_preamble;
        // The one permitted hop: the enclosing accessor that declares the same shape.
        if hops_left > 0 && cursor > 0 && is_definition(lines[cursor - 1]) {
            cursor -= 1;
            hops_left -= 1;
            continue;
        }
        return false;
    }
}

/// Every `#[cfg(test)]` module's line range in a file — a test fixture's in-memory map is not a
/// live guard, and demanding a declaration on one would be noise that teaches people to ignore
/// this test.
fn test_module_start(lines: &[&str]) -> Option<usize> {
    lines
        .iter()
        .position(|line| line.trim_start().starts_with("#[cfg(test)]"))
}

#[test]
fn every_in_ram_map_declares_its_restart_semantics() {
    let mut files = Vec::new();
    rust_files(&src_root(), &mut files);
    assert!(
        files.len() > 20,
        "the scan found only {} source files under {} — the walker is broken, and a lint that \
         scans nothing passes vacuously",
        files.len(),
        src_root().display(),
    );

    let mut undeclared: Vec<String> = Vec::new();
    let mut declared = 0usize;
    for file in &files {
        let text = std::fs::read_to_string(file).expect("read a source file");
        let lines: Vec<&str> = text.lines().collect();
        let cutoff = test_module_start(&lines).unwrap_or(lines.len());
        for (index, line) in lines.iter().enumerate().take(cutoff) {
            if !is_definition(line) {
                continue;
            }
            if declared_for(&lines, index) {
                declared += 1;
            } else {
                undeclared.push(format!(
                    "{}:{}\n      {}",
                    file.display(),
                    index + 1,
                    line.trim()
                ));
            }
        }
    }

    // NON-VACUITY: the scan must actually be finding sites. A refactor that renames every map
    // out of these shapes should fail HERE, loudly, rather than silently turning this into a
    // test of nothing.
    assert!(
        declared >= 8,
        "the scan matched only {declared} declared in-RAM maps — it has stopped seeing them, so \
         it is no longer a gate. Fix `SHAPES` (or this bound) rather than leaving a green \
         vacuity."
    );

    assert!(
        undeclared.is_empty(),
        "\n{} process-local map(s) do not declare their restart semantics.\n\n\
         Every one of these is EMPTY at boot. Say what that means — REFUSE, REBUILD, or a\n\
         deliberate PROCEED with the argument — in a `RESTART:` line in the doc comment above\n\
         it. See docs/reference/RESTART-SEMANTICS.md.\n\n  {}\n",
        undeclared.len(),
        undeclared.join("\n  "),
    );
}

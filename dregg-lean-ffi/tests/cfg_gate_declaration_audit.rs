//! THE CFG-GATE LEDGER AUDIT — a source-level, archive-independent check that every
//! `#[cfg(dregg_*_present)]` gate in this crate is both DECLARED and EMITTED by `build.rs`.
//!
//! ═══ WHY THIS EXISTS WHEN `unexpected_cfgs = "deny"` IS ALREADY ARMED ═══════════════
//!
//! `[lints] workspace = true` was added to this crate's manifest on 2026-07-25, which
//! binds the workspace's `unexpected_cfgs = "deny"`. That lint is the right detector and
//! it is now on. It is also, in THIS crate, blind to most of what it is supposed to see —
//! for two independent reasons, both measured, not guessed:
//!
//!   (1) NESTED CFGS UNDER A FALSE GATE ARE NEVER EVALUATED. rustc strips
//!       `#[cfg(false_thing)] mod m { … }` top-down; the attributes INSIDE `m` are
//!       deleted with the module before the lint ever looks at them. Reproduced:
//!
//!           #[cfg(outer_gate)]                 // not set
//!           mod inner { #[cfg(totally_bogus)] pub fn f() {} }
//!           #[cfg(another_bogus)] pub fn g() {}
//!
//!           $ rustc --check-cfg 'cfg(outer_gate)' -D unexpected_cfgs …
//!           error: unexpected `cfg` condition name: `another_bogus`   ← only the top-level one
//!
//!       Nineteen of this crate's ~28 gate names live ONLY inside
//!       `#[cfg(lean_lib_present)] mod ffi { … }` (src/lib.rs:1018). On any host without
//!       `libdregg_lean.a` — every hosted CI runner, every fresh `pbuild` lane —
//!       `lean_lib_present` is false, `mod ffi` is stripped, and `unexpected_cfgs` sees
//!       exactly none of them. Verified: a deliberate `dregg_handler_present` ->
//!       `dregg_handlr_present` typo inside `mod ffi` compiled CLEAN on an archive-less
//!       host with the lint at `deny`.
//!
//!   (2) `unexpected_cfgs` CANNOT SEE A DROPPED `rustc-cfg=` EMIT AT ALL. It compares a
//!       used name against the `rustc-check-cfg` DECLARATION set. Delete only the
//!       `println!("cargo:rustc-cfg=dregg_foo_present")` and keep the `rustc-check-cfg`
//!       line, and the gate is permanently false, the guarded code compiles to nothing,
//!       and the lint is green — because the name is still declared. That is the actual
//!       failure mode: the gate does not have to become UNKNOWN to go dark, only UNSET.
//!
//! Commit `7ebe7b7d4b` (2026-07-20) removed BOTH lines for `dregg_fri_ledger_present` and
//! `dregg_constraint_admits_present`; both gates went dark for ~5 days. Every use site of
//! both names is inside `mod ffi`, so on an archive-less host the armed lint would still
//! not have caught it. This audit would have, on any host, with no archive, in
//! `cargo test -p dregg-lean-ffi`.
//!
//! ═══ WHAT IT CHECKS ════════════════════════════════════════════════════════════════
//!
//!   USED      every `lean_lib_present` / `dregg_*_present` name appearing in a real
//!             `#[cfg(…)]` / `#[cfg_attr(…)]` / `cfg!(…)` predicate under `src/`,
//!             `tests/`, `benches/` (comment lines excluded).
//!   DECLARED  every `cargo::rustc-check-cfg=cfg(NAME)` literal in `build.rs`.
//!   EMITTED   every `cargo:rustc-cfg=NAME` literal in `build.rs`.
//!
//!   USED ⊆ DECLARED   — the strip-proof `unexpected_cfgs`.
//!   USED ⊆ EMITTED    — the gate-drop detector `unexpected_cfgs` structurally cannot be.
//!   EMITTED ⊆ USED    — an emitted cfg nothing reads is a dead gate.
//!   DECLARED ⊆ EMITTED — a declared-but-unemittable name is a gate that can never open.
//!
//! ═══ IT CANNOT SILENTLY SKIP ═══════════════════════════════════════════════════════
//!
//! There is no precondition, no env var, no archive, no `if !ready() { return; }`. The
//! only inputs are tracked source files reached from `CARGO_MANIFEST_DIR`. A scanner that
//! matches nothing is itself a failure (`FLOOR_*` below): the repo's signature failure is
//! a filter that matches zero and reports green, so the floors are asserted first.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// Scanner floors. If the source is refactored such that these no longer hold, the
/// *scanner* is what broke — fix it rather than lowering the floor. Set well below the
/// 2026-07-25 measurement (28 names / 29 declared / 28 emitted / 148 sites) so ordinary
/// churn does not trip them, but far above zero so a dead scanner cannot pass.
const FLOOR_NAMES: usize = 20;
const FLOOR_SITES: usize = 90;
const FLOOR_DECLARED: usize = 20;
const FLOOR_EMITTED: usize = 20;

fn crate_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// True for the cfg names this crate's build script owns: the archive-presence gate and
/// every per-export symbol probe. Deliberately narrow — `feature = "…"`, `target_os`,
/// `test` and friends are rustc/cargo's business, not this ledger's.
fn is_gate_name(name: &str) -> bool {
    name == "lean_lib_present" || (name.starts_with("dregg_") && name.ends_with("_present"))
}

/// Collect every gate name mentioned inside a real cfg predicate in `src`.
///
/// Line-oriented on purpose: it skips comment lines (this crate's doc comments quote gate
/// names constantly, and a doc mention is not a gate) and then walks `#[cfg`, `#[cfg_attr`
/// and `cfg!` occurrences to their balanced closing paren, tolerating a predicate that
/// wraps across lines. Returns (names, site_count).
fn scan_uses(src: &str) -> (BTreeSet<String>, usize) {
    let mut names = BTreeSet::new();
    let mut sites = 0usize;

    // Drop comment-only lines, keep the rest joined so a multi-line predicate still parses.
    let code: String = src
        .lines()
        .map(|l| {
            let t = l.trim_start();
            if t.starts_with("//") || t.starts_with("*") || t.starts_with("#!") {
                ""
            } else {
                l
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    let bytes = code.as_bytes();
    for pat in ["#[cfg(", "#[cfg_attr(", "cfg!("] {
        let mut from = 0usize;
        while let Some(rel) = code[from..].find(pat) {
            let open = from + rel + pat.len() - 1; // index of the '('
            let mut depth = 0usize;
            let mut end = open;
            for (i, b) in bytes[open..].iter().enumerate() {
                match b {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = open + i;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            if end > open {
                let pred = &code[open + 1..end];
                let mut hit = false;
                for ident in pred.split(|c: char| !(c.is_alphanumeric() || c == '_')) {
                    if is_gate_name(ident) {
                        names.insert(ident.to_string());
                        hit = true;
                    }
                }
                if hit {
                    sites += 1;
                }
                from = end;
            } else {
                from = open + 1;
            }
        }
    }
    (names, sites)
}

/// Every `cargo::rustc-check-cfg=cfg(NAME)` literal in build.rs.
fn scan_declared(build_rs: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for (_, line) in build_rs.lines().enumerate() {
        let Some(pos) = line.find("rustc-check-cfg=cfg(") else {
            continue;
        };
        let rest = &line[pos + "rustc-check-cfg=cfg(".len()..];
        let Some(close) = rest.find(')') else {
            continue;
        };
        let name = rest[..close].trim();
        if is_gate_name(name) {
            out.insert(name.to_string());
        }
    }
    out
}

/// Every `cargo:rustc-cfg=NAME` literal in build.rs (the SET, not the declaration).
fn scan_emitted(build_rs: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for line in build_rs.lines() {
        // `rustc-check-cfg=cfg(` also contains `rustc-c…`; match the emit form exactly.
        for marker in ["cargo:rustc-cfg=", "cargo::rustc-cfg="] {
            let mut from = 0usize;
            while let Some(rel) = line[from..].find(marker) {
                let start = from + rel + marker.len();
                let name: String = line[start..]
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if is_gate_name(&name) {
                    out.insert(name);
                }
                from = start.max(from + rel + 1);
            }
        }
    }
    out
}

fn rust_sources(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for sub in ["src", "tests", "benches"] {
        let dir = root.join(sub);
        let mut stack = vec![dir];
        while let Some(d) = stack.pop() {
            let Ok(rd) = std::fs::read_dir(&d) else {
                continue;
            };
            for e in rd.flatten() {
                let p = e.path();
                if p.is_dir() {
                    stack.push(p);
                } else if p.extension().is_some_and(|x| x == "rs") {
                    // Skip THIS file. Its `scanner_sees_what_unexpected_cfgs_cannot`
                    // fixture holds deliberately-fake gate names inside a raw string; the
                    // scanner is line-oriented and would read them as real use sites and
                    // fail the audit against its own test data.
                    if p.file_name()
                        .is_some_and(|f| f == "cfg_gate_declaration_audit.rs")
                    {
                        continue;
                    }
                    out.push(p);
                }
            }
        }
    }
    out.sort();
    out
}

/// The whole crate's cfg-gate USE ledger: (names, site count, name -> file sites).
fn collect_uses(root: &Path) -> (BTreeSet<String>, usize, Vec<(String, String)>, usize) {
    let files = rust_sources(root);
    let mut used = BTreeSet::new();
    let mut sites = 0usize;
    let mut where_used: Vec<(String, String)> = Vec::new();
    for f in &files {
        let Ok(s) = std::fs::read_to_string(f) else {
            continue;
        };
        let (n, c) = scan_uses(&s);
        sites += c;
        let rel = f.strip_prefix(root).unwrap_or(f).display().to_string();
        for name in n {
            where_used.push((name.clone(), rel.clone()));
            used.insert(name);
        }
    }
    (used, sites, where_used, files.len())
}

#[test]
fn every_cfg_gate_is_declared_and_emitted_by_build_rs() {
    let root = crate_root();
    let build_rs = std::fs::read_to_string(root.join("build.rs"))
        .expect("dregg-lean-ffi/build.rs must be readable — it is the source of every gate");

    let declared = scan_declared(&build_rs);
    let emitted = scan_emitted(&build_rs);

    let (used, sites, where_used, files_len) = collect_uses(&root);
    assert!(
        files_len >= 10,
        "source scan found only {files_len} .rs files under src/tests/benches — the scanner is \
         broken, not the crate"
    );

    // ── FLOORS FIRST: a scanner that matched nothing must not report green. ──────────
    assert!(
        used.len() >= FLOOR_NAMES,
        "cfg-gate scanner found only {} gate names (floor {FLOOR_NAMES}) across {files_len} \
         files / {sites} sites — the SCANNER is broken. Do not lower the floor to make this pass.",
        used.len(),
    );
    assert!(
        sites >= FLOOR_SITES,
        "cfg-gate scanner found only {sites} cfg sites (floor {FLOOR_SITES}) — scanner broken."
    );
    assert!(
        declared.len() >= FLOOR_DECLARED,
        "build.rs declares only {} gate cfgs via rustc-check-cfg (floor {FLOOR_DECLARED})",
        declared.len()
    );
    assert!(
        emitted.len() >= FLOOR_EMITTED,
        "build.rs emits only {} gate cfgs via rustc-cfg (floor {FLOOR_EMITTED})",
        emitted.len()
    );

    // ── 1. USED ⊆ DECLARED — the strip-proof `unexpected_cfgs`. ─────────────────────
    let undeclared: Vec<_> = used.difference(&declared).cloned().collect();
    assert!(
        undeclared.is_empty(),
        "UNDECLARED CFG GATE(S): {undeclared:?}\n\
         These names are read by `#[cfg(…)]` in this crate but build.rs never prints\n\
         `cargo::rustc-check-cfg=cfg(<name>)` for them. Such a cfg is ALWAYS FALSE and the\n\
         code it guards compiles to nothing. `unexpected_cfgs = \"deny\"` catches this only\n\
         where the site is not nested under a false outer cfg — most of this crate is.\n\
         Sites: {:?}",
        where_used
            .iter()
            .filter(|(n, _)| undeclared.contains(n))
            .collect::<Vec<_>>()
    );

    // ── 2. USED ⊆ EMITTED — the gate-drop detector. ─────────────────────────────────
    let never_set: Vec<_> = used.difference(&emitted).cloned().collect();
    assert!(
        never_set.is_empty(),
        "GATE THAT CAN NEVER OPEN: {never_set:?}\n\
         These names are read by `#[cfg(…)]` and DECLARED by build.rs, but build.rs contains\n\
         no `cargo:rustc-cfg=<name>` that could ever set them — so the gated code is dead on\n\
         every host, forever, silently. This is the exact shape of 7ebe7b7d4b\n\
         (dregg_fri_ledger_present, dregg_constraint_admits_present; ~5 days dark each) and\n\
         `unexpected_cfgs` cannot see it: a declared-but-unset cfg is not an unexpected one.\n\
         Sites: {:?}",
        where_used
            .iter()
            .filter(|(n, _)| never_set.contains(n))
            .collect::<Vec<_>>()
    );

    // ── 3. EMITTED ⊆ USED — an emitted gate nothing reads is dead weight. ───────────
    let unread: Vec<_> = emitted.difference(&used).cloned().collect();
    assert!(
        unread.is_empty(),
        "EMITTED BUT UNREAD CFG(S): {unread:?}\n\
         build.rs probes the archive and sets these, but no `#[cfg(…)]` in the crate reads\n\
         them. Either the consumer was deleted (and the probe should go with it) or the\n\
         consumer was renamed (and a gate just went dark under a different name)."
    );

    // ── 4. DECLARED ⊆ EMITTED — a declaration with no emitter is a gate stub. ───────
    let declared_never_set: Vec<_> = declared.difference(&emitted).cloned().collect();
    assert!(
        declared_never_set.is_empty(),
        "DECLARED BUT NEVER EMITTED: {declared_never_set:?}\n\
         build.rs declares these to `--check-cfg` (which SILENCES `unexpected_cfgs` for them)\n\
         but never prints `cargo:rustc-cfg=<name>`. The declaration is doing nothing except\n\
         suppressing the one lint that would have complained."
    );

    eprintln!(
        "cfg-gate ledger OK: {} names, {sites} sites, {files_len} files; declared {}, emitted {}",
        used.len(),
        declared.len(),
        emitted.len()
    );
}

/// MUTATION CANARY for check #2 (`USED ⊆ EMITTED`), the one check `unexpected_cfgs`
/// structurally cannot perform. It replays commit `7ebe7b7d4b` IN MEMORY — deleting the
/// `cargo:rustc-cfg=dregg_fri_ledger_present` emit line from a copy of the REAL build.rs,
/// leaving its `rustc-check-cfg` declaration intact, exactly as a "the gate is declared so
/// the lint is happy" regression looks — and asserts the audit notices.
///
/// Without this, check #2 could be silently vacuous (e.g. if `scan_emitted` ever started
/// matching the declaration form, `used - emitted` would be empty forever and green).
#[test]
fn gate_drop_canary_replays_7ebe7b7d4b_in_memory() {
    const VICTIM: &str = "dregg_fri_ledger_present";
    let root = crate_root();
    let build_rs = std::fs::read_to_string(root.join("build.rs")).expect("build.rs readable");

    let (used, _, _, _) = collect_uses(&root);
    assert!(
        used.contains(VICTIM),
        "canary victim {VICTIM} is no longer read by any #[cfg] — pick a live gate name"
    );

    // Baseline: unmutated build.rs sets it, so the audit is quiet.
    assert!(
        scan_emitted(&build_rs).contains(VICTIM),
        "baseline: build.rs must currently emit {VICTIM}"
    );

    // The mutation: drop ONLY the emit line, keep the declaration.
    let mutated: String = build_rs
        .lines()
        .filter(|l| !(l.contains("rustc-cfg=") && l.contains(VICTIM) && !l.contains("check-cfg")))
        .collect::<Vec<_>>()
        .join("\n");
    assert_ne!(
        mutated, build_rs,
        "the mutation must actually change build.rs"
    );

    let emitted = scan_emitted(&mutated);
    let declared = scan_declared(&mutated);
    assert!(
        declared.contains(VICTIM),
        "the mutation must leave the DECLARATION intact — that is what makes the real \
         regression invisible to `unexpected_cfgs`"
    );
    assert!(
        !emitted.contains(VICTIM),
        "the mutation must remove the EMISSION"
    );
    assert!(
        used.difference(&emitted).any(|n| n == VICTIM),
        "check #2 IS VACUOUS: build.rs no longer sets {VICTIM}, the gate can never open, and \
         `used - emitted` did not flag it"
    );
}

/// The audit's own falsifier: the scanner must actually FIND gate names in a predicate,
/// must ignore them in comments, and must see through a nested/`all(...)` predicate — the
/// exact shape `unexpected_cfgs` is blind to.
#[test]
fn scanner_sees_what_unexpected_cfgs_cannot() {
    let sample = r#"
/// A doc comment naming `dregg_doc_only_present` — MUST NOT be picked up.
// #[cfg(dregg_commented_out_present)] — MUST NOT be picked up.
#[cfg(lean_lib_present)]
mod ffi {
    #[cfg(dregg_nested_present)]
    pub fn a() {}
    #[cfg(all(test, dregg_nested_all_present))]
    pub fn b() {}
    #[cfg(not(dregg_nested_not_present))]
    pub fn c() {}
}
#[cfg(all(lean_lib_present, dregg_toplevel_present))]
pub fn d() {}
"#;
    let (names, sites) = scan_uses(sample);
    let got: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
    assert_eq!(
        got,
        vec![
            "dregg_nested_all_present",
            "dregg_nested_not_present",
            "dregg_nested_present",
            "dregg_toplevel_present",
            "lean_lib_present",
        ],
        "scanner must find nested + all()/not() gate names and must ignore comments"
    );
    assert_eq!(
        sites, 5,
        "one site per cfg predicate mentioning a gate name"
    );

    assert_eq!(
        scan_declared("    println!(\"cargo::rustc-check-cfg=cfg(dregg_x_present)\");"),
        ["dregg_x_present".to_string()].into_iter().collect()
    );
    assert_eq!(
        scan_emitted("        println!(\"cargo:rustc-cfg=dregg_x_present\");"),
        ["dregg_x_present".to_string()].into_iter().collect()
    );
    // The declaration form must NOT be mistaken for an emission — that confusion would
    // make check #2 (USED ⊆ EMITTED) vacuous, which is the whole point of this file.
    assert!(
        scan_emitted("    println!(\"cargo::rustc-check-cfg=cfg(dregg_x_present)\");").is_empty(),
        "a rustc-check-cfg DECLARATION must not count as a rustc-cfg EMISSION"
    );
}

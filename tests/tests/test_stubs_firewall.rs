//! GUARD — the `test-stubs` firewall: `dregg-cell/test-stubs` must never
//! unify into a production build graph.
//!
//! # What it protects
//!
//! `dregg-cell`'s `test-stubs` feature arms the *accept* path of
//! `StubVerifier` (`cell/src/predicate.rs`), which is otherwise FAIL-CLOSED on
//! every proof. A host that selects the stub registry
//! (`WitnessedPredicateRegistry::with_stubs()`) in a build where the feature is
//! armed gets a verifier that accepts any non-empty proof bytes. `test-stubs`
//! is therefore a soundness gate, and `cell/Cargo.toml` states that production
//! builds never set it.
//!
//! **That statement was false as packaged.** `tests/Cargo.toml` listed
//! `dregg-cell = { path = "../cell", features = ["test-stubs"] }` as a normal
//! `[dependencies]` entry, and `dregg-tests` is in the workspace's `members`
//! AND `default-members` — so a root `cargo build --release` built this crate,
//! unified the feature across the graph, and armed the stub accept path inside
//! `dregg-node`, the production node binary. The fix was to move the entry to
//! `[dev-dependencies]`, matching `turn`/`intent`/`exec-lean`, which had it
//! right: under resolver 3 a dev-dependency's features are not unified into a
//! non-test build.
//!
//! This guard is the probe that found the leak, kept as a test so the build
//! graph cannot regress silently. It is defense in depth with
//! `cell/src/predicate.rs`'s `compile_error!` (which fires if `test-stubs` is
//! on in a `debug_assertions`-off build that has not attested it is a test
//! target): the `compile_error!` catches a leak into a *release* build; this
//! catches a leak into the *dev* graph, where `debug_assertions` is on and the
//! `compile_error!` stays quiet.
//!
//! # What this file took on in 2026-07-26
//!
//! The `compile_error!`'s condition used to be `test-stubs && !debug_assertions`
//! alone, which encodes "release ⟹ production". That is FALSE — `dregg-cell` is
//! a *dependency* of its test consumers, so `cfg(test)` is not set for it in
//! either case and a release TEST build is, from inside `predicate.rs`, the same
//! compilation as a release PRODUCTION build. The gate fired on both, which is
//! why `dregg-turn`, `dregg-intent`, `dregg-exec-lean`, `dregg-turn-prover` and
//! `dregg-tests` (this crate) could build their test targets ONLY in `debug`.
//!
//! The fix added `test-stubs-release-test-target`, a pure attestation marker set
//! only by those crates' `[dev-dependencies]` entries. It costs the compiler one
//! case: a `[dependencies]` entry that copies the attestation across as well
//! would no longer trip the `compile_error!`. No Cargo-level opt-in can be made
//! un-copy-pasteable, so THAT case lives here, in
//! `test_stubs_is_never_named_by_a_non_dev_dependency_entry` — a direct scan of
//! every manifest in the workspace, which does not depend on feature resolution
//! at all. Together the two tests below check the property the `compile_error!`
//! only ever approximated: *no non-dev build path enables the stub accept path.*
//!
//! # The falsifiers (both verified by running them RED)
//!
//! * Tree probe: move `dregg-cell`'s entry in `tests/Cargo.toml` back to
//!   `[dependencies]` with `features = ["test-stubs"]`. (That is exactly how it
//!   was verified — the probe printed `dregg-cell feature "test-stubs"` before
//!   the fix and nothing after.)
//! * Manifest scan: add `dregg-cell = { path = "../cell", features =
//!   ["test-stubs"] }` under any crate's `[dependencies]`. The scan names the
//!   file, the section and the line.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Every `dregg-cell` feature that either ARMS the `StubVerifier` accept path
/// or ATTESTS that arming it is acceptable. Both are disqualified from the
/// production graph, and for the same reason: the first is the hazard, the
/// second is the switch that turns off the compiler floor guarding it.
const STUB_FEATURES: [&str; 2] = ["test-stubs", "test-stubs-release-test-target"];

/// Walk up from `CARGO_MANIFEST_DIR` to the directory holding the workspace
/// root `Cargo.toml` (the one that declares `[workspace]`).
fn workspace_root() -> PathBuf {
    let mut dir: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        let manifest = dir.join("Cargo.toml");
        if manifest.exists() {
            let text = std::fs::read_to_string(&manifest).unwrap_or_default();
            if text.contains("[workspace]") {
                return dir;
            }
        }
        assert!(
            dir.pop(),
            "walked past the filesystem root without finding a [workspace] Cargo.toml"
        );
    }
}

fn cargo_tree(root: &Path, args: &[&str]) -> String {
    let out = Command::new(env!("CARGO"))
        .current_dir(root)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("failed to run `cargo {}`: {e}", args.join(" ")));
    assert!(
        out.status.success(),
        "`cargo {}` failed:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("cargo tree emitted non-UTF-8")
}

/// The gate. `-e features,no-dev` resolves exactly what a real (non-test)
/// build resolves: normal dependency edges only. `dregg-node` is the
/// production node binary and `dregg-tests` is the crate that leaked the
/// feature; asking for both together is what forces the unification the leak
/// depended on.
///
/// NOTE the `no-dev`: a bare `cargo tree -e features` includes dev-dependency
/// edges and therefore prints `test-stubs` even when the firewall is intact —
/// it is showing this crate's own (legitimate) dev-dependency. `no-dev` is what
/// makes the probe measure the production graph rather than the test graph.
#[test]
fn test_stubs_does_not_unify_into_the_production_node_graph() {
    let root = workspace_root();

    // ── HONEST POLE FIRST. The probe must actually be looking at a graph that
    // contains dregg-cell — otherwise "test-stubs not found" would be trivially
    // true and this test would be measuring a typo in its own arguments.
    let production = cargo_tree(
        &root,
        &[
            "tree",
            "-p",
            "dregg-node",
            "-p",
            "dregg-tests",
            "-e",
            "features,no-dev",
            "-i",
            "dregg-cell",
        ],
    );
    assert!(
        production.contains("dregg-cell"),
        "the probe did not resolve dregg-cell at all — it is measuring nothing.\n\
         Output:\n{production}"
    );
    assert!(
        production.contains("dregg-node"),
        "the probe did not reach dregg-node — the production binary is not in this graph, \
         so a leak into it could not be detected.\n\
         Output:\n{production}"
    );

    // ── THE GATE. Both features are checked BY NAME. `test-stubs` arms the
    // accept path; `test-stubs-release-test-target` attests that a
    // `debug_assertions`-off build is a test target and so SILENCES the
    // `compile_error!` — in a production graph it is exactly as disqualifying,
    // because its presence there means the compiler floor has been switched
    // off for that build. (A substring search for "test-stubs" happens to catch
    // both today; naming them individually is what keeps a future rename from
    // opening a hole silently.)
    for feature in STUB_FEATURES {
        assert!(
            !production.contains(feature),
            "SOUNDNESS: `dregg-cell/{feature}` unified into the PRODUCTION dependency graph \
             (normal edges only, no dev-dependencies). `test-stubs` arms StubVerifier's \
             accept-anything path inside dregg-node; `test-stubs-release-test-target` \
             disables the `compile_error!` that would otherwise catch it.\n\n\
             Some crate enables it as a normal [dependencies] entry. Move it to \
             [dev-dependencies] — see turn/intent/exec-lean/tests for the correct shape.\n\n\
             cargo tree -p dregg-node -p dregg-tests -e features,no-dev -i dregg-cell:\n{production}"
        );
    }

    // ── AND THE SAME GATE, WIDENED. The resolve above names two packages
    // because those are the two the original leak needed. That makes it a probe
    // for a KNOWN leak, not for the property. This one selects nothing, so
    // Cargo resolves the workspace's default-members — every production binary
    // in the repo at once, which is the graph the claim is actually about.
    let workspace = cargo_tree(
        &root,
        &["tree", "-e", "features,no-dev", "-i", "dregg-cell"],
    );
    assert!(
        workspace.contains("dregg-node"),
        "the workspace-wide probe did not reach dregg-node, so it is not measuring the \
         production graph.\nOutput:\n{workspace}"
    );
    for feature in STUB_FEATURES {
        assert!(
            !workspace.contains(feature),
            "SOUNDNESS: `dregg-cell/{feature}` unified into the production graph of the \
             workspace's default-members (normal edges only).\n\n\
             cargo tree -e features,no-dev -i dregg-cell:\n{workspace}"
        );
    }

    // ── AND the counter-pole: the feature IS still reachable over dev edges,
    // because this crate's own `#[cfg(test)]` modules legitimately use
    // `with_stubs()`. Without this assertion the gate above would also pass if
    // someone "fixed" the leak by deleting the dev-dependency outright — a
    // green that means the tests silently stopped exercising the stub plumbing.
    let with_dev = cargo_tree(
        &root,
        &[
            "tree",
            "-p",
            "dregg-tests",
            "-e",
            "features",
            "-i",
            "dregg-cell",
        ],
    );
    assert!(
        with_dev.contains("test-stubs"),
        "`test-stubs` is not reachable even over DEV edges — dregg-tests' dev-dependency on \
         `dregg-cell` with `features = [\"test-stubs\"]` is gone, so the stub-plumbing tests \
         are no longer testing the accept path they claim to.\n\
         cargo tree -p dregg-tests -e features -i dregg-cell:\n{with_dev}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The manifest scan — the case the `compile_error!` cannot see.
// ─────────────────────────────────────────────────────────────────────────────

/// Strip a TOML line comment, respecting `"` quoting so a `#` inside a string
/// (a URL fragment, say) is not mistaken for the start of a comment.
fn strip_comment(line: &str) -> &str {
    let mut in_string = false;
    for (i, c) in line.char_indices() {
        match c {
            '"' => in_string = !in_string,
            '#' if !in_string => return &line[..i],
            _ => {}
        }
    }
    line
}

/// Net `{`/`[` nesting introduced by a line, ignoring brackets inside strings.
fn bracket_delta(line: &str) -> i32 {
    let mut in_string = false;
    let mut depth = 0;
    for c in line.chars() {
        match c {
            '"' => in_string = !in_string,
            '{' | '[' if !in_string => depth += 1,
            '}' | ']' if !in_string => depth -= 1,
            _ => {}
        }
    }
    depth
}

/// Every path listed in the root manifest's `[workspace] members`, as manifest
/// paths. This is the set whose dependency sections can feature-unify into a
/// workspace build, so it is the set that MUST be covered.
///
/// Parsed textually rather than via `cargo metadata` to keep the scan
/// independent of feature resolution — the point of this probe is to check the
/// manifests themselves, not what Cargo made of them.
fn member_manifests(root: &Path) -> Vec<PathBuf> {
    let text = std::fs::read_to_string(root.join("Cargo.toml")).expect("read workspace Cargo.toml");
    let after = text
        .split_once("\nmembers = [")
        .expect("workspace Cargo.toml has no `members = [` array")
        .1;
    let list = after.split_once(']').expect("unterminated members array").0;
    list.split(',')
        .filter_map(|raw| {
            let m = raw.trim().trim_matches('"');
            (!m.is_empty()).then(|| root.join(m).join("Cargo.toml"))
        })
        .collect()
}

/// Collect `Cargo.toml` files under `root` to a bounded depth, so NON-member
/// manifests (`wasm/`, `discord-bot/` — separate workspaces that still build
/// against this tree) are covered too.
///
/// Bounded and `file_type()`-based on purpose. An unbounded walk that used
/// `path.is_dir()` FOLLOWED SYMLINKS and hung: this repo has
/// `.claude/worktrees/plonky3-recursion` (a symlinked second checkout),
/// `metatheory/.lake/.lake`, and several `node_modules` trees. `file_type()`
/// does not follow symlinks; the depth cap and the skip list do the rest.
/// Every workspace member sits at depth <= 2, and `member_manifests` covers
/// them by name regardless, so nothing load-bearing rests on this walk's reach.
fn walk_manifests(dir: &Path, depth: usize, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let Ok(ft) = entry.file_type() else { continue };
        if ft.is_symlink() {
            continue;
        }
        if ft.is_dir() {
            if depth == 0
                || name.starts_with('.')
                || matches!(name.as_ref(), "target" | "node_modules" | "vendor")
            {
                continue;
            }
            walk_manifests(&entry.path(), depth - 1, out);
        } else if name == "Cargo.toml" {
            out.push(entry.path());
        }
    }
}

/// THE GATE THE COMPILER GAVE UP. `test-stubs-release-test-target` silences the
/// `compile_error!` in `cell/src/predicate.rs`, so a `[dependencies]` entry that
/// copies BOTH features across would reach a production release build without
/// tripping it. That is the only case the compiler floor lost, and this is where
/// it is caught: a textual scan of every manifest, independent of profile,
/// feature resolution and `debug_assertions`.
///
/// The rule is the one `cell/Cargo.toml` states: a `test-stubs*` feature of
/// `dregg-cell` may be named ONLY from a dev-dependency section. Any other
/// dependency section — `[dependencies]`, `[build-dependencies]`,
/// `[target.'cfg(…)'.dependencies]`, `[workspace.dependencies]`, and the
/// `[dependencies.dregg-cell]` table spelling of each — is a leak.
#[test]
fn test_stubs_is_never_named_by_a_non_dev_dependency_entry() {
    let root = workspace_root();
    let members = member_manifests(&root);

    // ── HONEST POLE 1. A `members` parse that returned nothing (or a handful)
    // would make the gate below trivially green.
    assert!(
        members.len() > 100,
        "parsed only {} workspace members out of the root Cargo.toml — the `members` parse \
         is broken, so this scan is not covering the workspace.",
        members.len()
    );

    // ── HONEST POLE 2. Every declared member must actually be on disk and
    // readable, or the scan is silently skipping crates it claims to police.
    let missing: Vec<_> = members.iter().filter(|m| !m.is_file()).collect();
    assert!(
        missing.is_empty(),
        "workspace members whose Cargo.toml the scan could not find: {missing:#?}"
    );

    let mut found = members;
    walk_manifests(&root, 3, &mut found);
    found.push(root.join("Cargo.toml")); // `[workspace.dependencies]` lives here
    found.sort();
    found.dedup();

    let mut violations = Vec::new();
    // The known-good entries, so a scan that stops recognising the CORRECT
    // shape (a rename, a walker that skips the crates that matter) cannot pass
    // by finding nothing anywhere.
    let mut dev_entries = Vec::new();

    for manifest in &found {
        let Ok(text) = std::fs::read_to_string(manifest) else {
            continue;
        };
        let rel = manifest.strip_prefix(&root).unwrap_or(manifest);
        let mut section = String::new();
        // A dependency entry is a LOGICAL line, not a physical one: the correct
        // shape in this repo spans four lines,
        //     dregg-cell = { path = "../cell", features = [
        //         "test-stubs",
        //         "test-stubs-release-test-target",
        //     ] }
        // and a physical-line scan would see `"test-stubs",` with no crate name
        // next to it — i.e. it would MISS exactly the copy-paste of this block
        // into `[dependencies]` that the scan exists to catch. So accumulate
        // until the brackets balance.
        let mut buf = String::new();
        let mut depth: i32 = 0;
        let mut start = 0usize;

        for (lineno, raw) in text.lines().enumerate() {
            let line = strip_comment(raw).trim();
            if line.is_empty() {
                continue;
            }
            if depth == 0 && line.starts_with('[') && line.ends_with(']') && !line.contains('=') {
                section = line.trim_matches(['[', ']']).to_string();
                continue;
            }
            if buf.is_empty() {
                start = lineno + 1;
            } else {
                buf.push(' ');
            }
            buf.push_str(line);
            depth += bracket_delta(line);
            if depth > 0 {
                continue;
            }
            depth = 0;

            let entry = std::mem::take(&mut buf);
            // Only dependency sections can enable a feature of another crate.
            // `[features]` forwarding (`foo = ["dregg-cell/test-stubs"]`) is a
            // different vector, covered by the `cargo tree` probes above, which
            // see the resolved feature set rather than the manifest text.
            if !section.contains("dependencies") {
                continue;
            }
            if !STUB_FEATURES.iter().any(|f| entry.contains(f)) {
                continue;
            }
            // The feature must belong to `dregg-cell` — named inline
            // (`dregg-cell = { … }`) or by the section in the table spelling
            // (`[dependencies.dregg-cell]`). Without this, another crate that
            // one day grows its own `test-stubs` feature reads as a violation.
            if !entry.contains("dregg-cell") && !section.contains("dregg-cell") {
                continue;
            }
            if section.contains("dev-dependencies") {
                dev_entries.push(format!("{}:{start} [{section}]", rel.display()));
            } else {
                violations.push(format!("{}:{start}  [{section}]  {entry}", rel.display()));
            }
        }
    }

    assert!(
        dev_entries.len() >= 5,
        "the scan recognised only {} dev-dependency entry/entries naming a `test-stubs*` \
         feature, but turn, intent, exec-lean, turn-prover, tests and cell itself all carry \
         one. The scan is not seeing the manifests it is supposed to police, so its silence \
         about violations means nothing.\nSaw: {dev_entries:#?}",
        dev_entries.len()
    );

    assert!(
        violations.is_empty(),
        "SOUNDNESS: a `dregg-cell` `test-stubs*` feature is named by a NON-dev dependency \
         section. `test-stubs` arms StubVerifier's accept-anything path; \
         `test-stubs-release-test-target` switches off the `compile_error!` in \
         `cell/src/predicate.rs` that would otherwise catch it in a release build. Either \
         one outside `[dev-dependencies]` puts the pair one copy-paste away from a \
         production node that accepts any non-empty proof bytes.\n\n\
         Move the entry to [dev-dependencies] — see turn/intent/exec-lean/tests for the \
         correct shape.\n\n\
         Offending entries:\n{}",
        violations.join("\n")
    );
}

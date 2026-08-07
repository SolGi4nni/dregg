//! ⚑⚑⚑ **THE GATE THE `dregg-turn` FIREWALL NEVER HAD.**
//!
//! `turn/Cargo.toml:17-25` forbids the `dregg-circuit-prove` edge in a COMMENT, and
//! `docs/reference/TURN-PROVER-CRATE-EXTRACTION-DESIGN.md` §5 (PR1) names the check as its own
//! acceptance criterion — *"`cargo build -p dregg-turn` is now prover-free and has no
//! `dregg-circuit-prove` edge"*. Measured 2026-08-05, at source: **nothing enforced it.** No
//! `deny.toml` (the repo has none at all), no `[bans]`, no `cargo tree`/`cargo metadata` gate
//! naming these crates, and none of `scripts/local-gates.sh`'s ~90 gates. The firewall was true
//! at HEAD and would have stayed green through its own removal.
//!
//! It is enforced here, and the same probe is turned on the new verify-only crate so that
//! `dregg-recursion-verify` cannot quietly become a re-export of the prover.
//!
//! # What each pole is for
//!
//! Templated on `tests/tests/test_stubs_firewall.rs`: every negative assertion is paired with an
//! **honest pole** (the probe reached a graph that could have shown the thing) and, where the
//! obvious wrong fix exists, a **counter-pole** (deleting the edge entirely is not a green).
//!
//! # ⚠ What this gate does NOT claim
//!
//! It does not claim `dregg-turn` is free of the recursion FORK. `p3-circuit` is already in
//! turn's normal graph via `dregg-turn → dregg-circuit → p3-poseidon2-circuit-air → p3-circuit`,
//! and always has been. "Recursion-free by construction" means precisely: **no `p3-recursion`,
//! no `p3-circuit-prover`, no `dregg-circuit-prove`** — the three that carry the prover and the
//! in-circuit verifier builder. Those are the names asserted below; asserting "p3-circuit" would
//! go red immediately and for the wrong reason.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The crates whose ABSENCE from `dregg-turn`'s normal graph is the firewall.
const FORBIDDEN_IN_TURN: &[&str] = &["dregg-circuit-prove", "p3-recursion", "p3-circuit-prover"];

fn workspace_root() -> PathBuf {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        let manifest = dir.join("Cargo.toml");
        if manifest.exists()
            && std::fs::read_to_string(&manifest)
                .map(|s| s.contains("[workspace]"))
                .unwrap_or(false)
        {
            return dir;
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

/// ⚑ **THE FIREWALL, ENFORCED.** `dregg-turn`'s NORMAL dependency graph contains no prover.
///
/// `-e normal` is what makes this the production graph: `dregg-turn` legitimately dev-depends on
/// nothing heavy, but its *consumers* do, and a bare `cargo tree` would show their edges.
#[test]
fn dregg_turn_has_no_recursion_prover_edge() {
    let root = workspace_root();

    // ── HONEST POLE. The probe must be looking at a real, populated graph — otherwise "the
    // prover is not in it" would be true of a typo in the arguments.
    let turn = cargo_tree(&root, &["tree", "-p", "dregg-turn", "-e", "normal"]);
    assert!(
        turn.contains("dregg-turn"),
        "the probe did not resolve dregg-turn at all; it is measuring nothing:\n{turn}"
    );
    assert!(
        turn.contains("dregg-circuit"),
        "the probe did not reach dregg-circuit — turn's VERIFY floor is missing from this graph, \
         so a prover edge could hardly be detected either:\n{turn}"
    );

    for name in FORBIDDEN_IN_TURN {
        assert!(
            !turn.contains(name),
            "FIREWALL BREACH: `{name}` is in `dregg-turn`'s NORMAL dependency graph.\n\n\
             `turn/Cargo.toml` states that core turn is recursion-free by construction, and the \
             turn-prover extraction (docs/reference/TURN-PROVER-CRATE-EXTRACTION-DESIGN.md §0) \
             exists so that proof PRODUCTION lives in a crate that is always compiled as itself \
             rather than behind a cfg. Proof production belongs in `dregg-turn-prover`; \
             recursion VERIFICATION belongs in `dregg-recursion-verify`, which a consumer that \
             wants it depends on directly.\n\n\
             cargo tree -p dregg-turn -e normal:\n{turn}"
        );
    }
}

/// ⚑ **AND THE VERIFY CRATE IS ACTUALLY VERIFY-ONLY.** `dregg-recursion-verify` must not reach
/// `dregg-circuit-prove` — otherwise it is a re-export of the prover wearing a smaller name, and
/// every consumer that took it "because it is the small one" got the tower anyway.
///
/// ⚠ It DOES reach `p3-recursion` / `p3-circuit-prover`, and that is asserted below rather than
/// left implicit: `BatchStarkProver::verify_all_tables` is the verification, and the orphan rule
/// puts `DreggRecursionConfig`'s `FriRecursionConfig` impl in the crate that owns the type. A
/// gate that pretended otherwise would be describing a crate that does not exist.
#[test]
fn dregg_recursion_verify_is_verify_only_and_says_what_it_pulls() {
    let root = workspace_root();
    let rv = cargo_tree(
        &root,
        &["tree", "-p", "dregg-recursion-verify", "-e", "normal"],
    );

    assert!(
        rv.contains("dregg-recursion-verify"),
        "the probe did not resolve the crate:\n{rv}"
    );
    assert!(
        !rv.contains("dregg-circuit-prove"),
        "`dregg-recursion-verify` reaches `dregg-circuit-prove`, so it is not verify-only — it is \
         the prover behind a smaller name.\n\ncargo tree -p dregg-recursion-verify -e normal:\n{rv}"
    );
    // The heavyweights the split is FOR: none of these may appear.
    for name in ["wgpu", "dregg-lean-ffi", "p3-bn254", "dregg-p3-pasta"] {
        assert!(
            !rv.contains(name),
            "`{name}` is in the verify-only crate's graph; the boundary has drifted.\n{rv}"
        );
    }
    // ── AND THE HONEST ADMISSION, as an assertion so it cannot rot into a nicer story.
    for name in ["p3-recursion", "p3-circuit-prover", "p3-circuit"] {
        assert!(
            rv.contains(name),
            "`{name}` is NOT in the verify crate's graph, but this crate's docs say it is. Either \
             the docs are now wrong or verification stopped happening.\n{rv}"
        );
    }
}

/// ⚑ **THE COUNTER-POLE: the capability EXISTS somewhere.** A firewall that passed because
/// nobody can verify a recursion root anywhere would be a green that means the feature was
/// deleted. `dregg-node` must reach `dregg-recursion-verify` over NORMAL edges — that is the
/// operator's design call made structural: the crate that unconditionally verifies, depended on
/// where verification is wanted.
#[test]
fn the_node_takes_the_verify_edge_that_turn_refuses() {
    let root = workspace_root();
    let node = cargo_tree(
        &root,
        &[
            "tree",
            "-p",
            "dregg-node",
            "-e",
            "normal",
            "-i",
            "dregg-recursion-verify",
        ],
    );
    assert!(
        node.contains("dregg-recursion-verify"),
        "the reverse-dependency probe found nothing:\n{node}"
    );
    assert!(
        node.contains("dregg-node"),
        "`dregg-node` does not depend on `dregg-recursion-verify` over normal edges, so no node \
         in this workspace can verify a recursion root and the firewall above is green for the \
         wrong reason.\n\ncargo tree -p dregg-node -e normal -i dregg-recursion-verify:\n{node}"
    );
}

/// ⚑ **NO CARGO FEATURE SNUCK IN.** The operator's design call was explicit: a separate crate
/// that unconditionally has the functionality, not a feature toggling behaviour. This reads the
/// manifest and requires `[features]` to be absent — the same statement `turn-prover/Cargo.toml`
/// makes in prose, made checkable.
#[test]
fn the_verify_crate_declares_no_features() {
    let manifest = workspace_root().join("recursion-verify/Cargo.toml");
    let text = std::fs::read_to_string(&manifest).expect("the verify crate's manifest is readable");

    // ⚑ SECTION HEADERS, NOT A SUBSTRING SEARCH. The manifest's own prose explains why there is
    // no feature section, and a `contains("[features]")` probe fires on that explanation — which
    // is a gate that goes red for saying the right thing. Strip comments, then look at what is
    // actually a table header.
    let sections: Vec<&str> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.starts_with('#'))
        .filter(|l| l.starts_with('[') && l.ends_with(']'))
        .collect();
    assert!(
        !sections.contains(&"[features]"),
        "`recursion-verify/Cargo.toml` declares a `[features]` section. A feature is a hidden \
         boundary: it is on in one resolve and off in another, which is the cfg-brittleness class \
         the turn-prover extraction closed. If some consumer needs a smaller surface, that is \
         another crate, not a flag.\nsections: {sections:?}"
    );
    // ── HONEST POLE, twice over: the parser found real sections (so "no [features]" is not the
    // output of a parser that found nothing), and we read the file we think we did.
    assert!(
        sections.contains(&"[dependencies]"),
        "the section parser found no `[dependencies]`; it is measuring nothing: {sections:?}"
    );
    assert!(
        text.contains("name = \"dregg-recursion-verify\""),
        "read the wrong manifest: {}",
        manifest.display()
    );

    // ── AND `dregg-turn` must not have grown one either. The extraction deleted turn's `prover`
    // feature; a `recursion`/`recursion-verify` feature would be the same mistake re-made under
    // a new name, and it is exactly the shape this task was told not to build.
    let turn_manifest = workspace_root().join("turn/Cargo.toml");
    let turn_text = std::fs::read_to_string(&turn_manifest).expect("turn's manifest is readable");
    for banned in ["prover", "recursion", "recursion-verify"] {
        assert!(
            !turn_text
                .lines()
                .map(str::trim)
                .filter(|l| !l.starts_with('#'))
                .any(|l| l.starts_with(&format!("{banned} ="))),
            "`turn/Cargo.toml` declares a `{banned}` feature. Proof production is \
             `dregg-turn-prover`; recursion VERIFICATION is `dregg-recursion-verify`, injected \
             through `MinaChainRootBackend`. Neither is a flag on `dregg-turn`."
        );
    }
}

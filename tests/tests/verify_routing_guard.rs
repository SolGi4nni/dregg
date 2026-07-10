//! GUARD A — the static routing lint: a CI regression gate for the "the crate leaves the LIVE TCB"
//! design. It is metadata-only (no leanc/FFI link) and load-bearing.
//!
//! # What it protects
//!
//! `dregg_pq::ml_dsa_verify` computes its security-critical accept/reject from the Lean-verified REAL
//! ML-DSA core ONLY in a process that has called `dregg_pq::install_lean_verify_core_real(...)` (the node
//! does this at startup via `dregg_node::install_mldsa_verified_verify_core()`). A process that never
//! installs the core falls back to the `fips204` crate — the crate is then IN that process's verify TCB.
//!
//! FFI-free leaf binaries (demos, thin clients, offline tools, the sel4 no_std verifier, …) deliberately
//! never link the 195 MB Lean archive: they are a STRUCTURAL design choice, not an oversight. This guard
//! makes that choice CONSCIOUS and REGRESSION-SAFE:
//!
//!   * every workspace binary whose runtime dependency closure reaches a VERIFYING crate must EITHER
//!     route the verified core (install call in `src/` + a non-dev, non-optional `dregg-lean-ffi` dep)
//!     OR appear on the `DELEGATES_VERIFY` allowlist below with a justification;
//!   * a NEW verifying binary added without wiring or an allowlist entry turns CI RED — you cannot
//!     silently ship a binary that re-admits the `fips204` crate to the verify authority;
//!   * a crate that is later WIRED should be REMOVED from the allowlist (its `src/` install call makes it
//!     pass the routed branch), so the allowlist only ever shrinks toward "everything routed".
//!
//! Only `dregg-node` is routed today. Everything else is an allowlisted FFI-free leaf. SIGN + KEM are
//! still crate-authoritative in EVERY process (their Lean seams are toy-wired to nothing deployed) — see
//! `dregg-pq/tests/seam_scope_honesty.rs` (GUARD C) for the in-code proof of that.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// Crates whose presence in a binary's runtime dependency closure means that binary participates in the
/// dregg verify stack (its process either installs the Lean-verified verify core or falls back to the
/// `fips204` crate). These are the crates that carry / transitively pull the ML-DSA verify seam.
const VERIFYING: &[&str] = &[
    "dregg-turn",
    "dregg-wire",
    "dregg-captp",
    "dregg-federation",
    "dregg-blocklace",
    "dregg-lightclient",
    "dregg-cell-crypto",
    "dregg-token",
    "dregg-auth",
    "dregg-pq",
];

/// Source tokens that mark a crate as ROUTING the Lean-verified REAL verify core: any of these appearing
/// in a crate's own `src/` means the crate installs the verified core (and must ALSO carry a non-dev,
/// non-optional `dregg-lean-ffi` dep to actually link the archive).
const ROUTE_INSTALL_TOKENS: &[&str] = &[
    "install_lean_verify_core_real(", // the dregg-pq seam, called directly
    "install_mldsa_verified_verify_core(", // the shared node helper that calls the seam
];

/// The DELEGATES_VERIFY allowlist: verifying binaries that DELIBERATELY do not route the verified core.
/// Each entry is `(crate_name, justification)`. Adding a crate here is a CONSCIOUS, reviewed decision that
/// this binary is a structural FFI-free leaf (or a not-yet-wired TODO). When a crate is later wired,
/// REMOVE it from this list — its `src/` install call will then satisfy the routed branch instead.
///
/// Entries that do not correspond to a current root-workspace verifying binary (e.g. the sel4 no_std
/// verifier and the discord bot live in SEPARATE excluded workspaces) are documented here for intent but
/// are inert to this guard, which only enumerates root-workspace members.
const DELEGATES_VERIFY: &[(&str, &str)] = &[
    // ── Audit-seeded entries ───────────────────────────────────────────────────────────────────────
    ("dregg-cli", "thin HTTP/CLI client, no local PQ verify path"),
    (
        "dregg-verifier",
        "structural Lean-freedom by design — the audit anchor for the FFI-free leaf",
    ),
    // sel4 no_std port — lives in the excluded `sel4/dregg-firmament` workspace (pkg `dregg-verifier-pd`),
    // so it is inert to this root-workspace guard; documented for intent.
    (
        "dregg-verifier-pd",
        "no_std sel4 protection-domain verifier, STARK port pending (separate workspace)",
    ),
    // discord bot lives in its own excluded workspace (pkg `dregg-discord-bot`); inert here.
    (
        "dregg-discord-bot",
        "FFI-free leaf, delegates to co-located node / not yet routed — TODO wire (separate workspace)",
    ),
    (
        "dregg-auth",
        "FFI-free leaf, delegates to co-located node / not yet routed — TODO wire",
    ),
    (
        "agent-platform",
        "FFI-free leaf, delegates to co-located node / not yet routed — TODO wire",
    ),
    (
        "dregg-observability",
        "FFI-free leaf, delegates to co-located node / not yet routed — TODO wire",
    ),
    (
        "dregg-userspace-verify",
        "FFI-free leaf, delegates to co-located node / not yet routed — TODO wire",
    ),
    (
        "mud-dregg",
        "FFI-free leaf, delegates to co-located node / not yet routed — TODO wire",
    ),
    (
        "deos-hermes",
        "FFI-free leaf, delegates to co-located node / not yet routed — TODO wire",
    ),
    (
        "dregg-lightclient",
        "lightclient demos/tools — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    // ── starbridge — wiring in flight (per the audit). Remove once install_lean_verify_core_real lands
    //    in starbridge-v2/src. TODO: wiring in flight.
    (
        "starbridge-v2",
        "gpui master interface — TODO: wiring in flight; remove once the install call lands in src",
    ),
    (
        "starbridge-web",
        "web pty/surface host — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    // ── Demos / example apps: FFI-free leaves, delegate to a co-located node. ─────────────────────────
    (
        "deos-core-smoke",
        "mobile core smoke bin — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    (
        "deos-leptos",
        "leptos web-cell demo — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    (
        "deos-zed",
        "zed doc/merge demo — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    (
        "dregg-demo",
        "story/demo binaries — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    (
        "dregg-demo-agent",
        "agent demo — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    (
        "dregg-sdk-consensus-demo",
        "sdk consensus demo — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    (
        "interactive-fiction-demo",
        "IF demo — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    (
        "starbridge-branch-stitch-multiplayer",
        "multiplayer demo — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
    // ── Offline tools / harnesses: no deployed verify path. ─────────────────────────────────────────
    (
        "dregg-analyzer",
        "offline analysis tool — FFI-free leaf, no deployed verify path — TODO wire if it verifies",
    ),
    (
        "dregg-deploy",
        "deploy CLI — FFI-free leaf, no local verify path — TODO wire if it verifies",
    ),
    (
        "dregg-perf",
        "perf/report harness — FFI-free leaf, no deployed verify path",
    ),
    (
        "dregg-preflight",
        "preflight checker — FFI-free leaf, delegates to co-located node — TODO wire",
    ),
];

/// Locate the workspace root Cargo.toml from this test crate's manifest dir (`.../tests`), so
/// `cargo metadata` resolves the ROOT workspace regardless of cwd.
fn workspace_root_manifest() -> PathBuf {
    // CARGO_MANIFEST_DIR at test-compile time is the `tests` package dir; its parent is the workspace root.
    let tests_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    tests_dir
        .parent()
        .expect("tests crate has a parent (the workspace root)")
        .join("Cargo.toml")
}

/// Recursively collect the text of every `.rs` file under `dir` (a crate's `src/`).
fn read_src_recursive(dir: &Path, out: &mut String) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            read_src_recursive(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            if let Ok(text) = std::fs::read_to_string(&path) {
                out.push_str(&text);
                out.push('\n');
            }
        }
    }
}

#[test]
fn every_verifying_binary_is_routed_or_allowlisted() {
    let manifest = workspace_root_manifest();
    let output = Command::new(env!("CARGO"))
        .args(["metadata", "--format-version", "1"])
        .arg("--manifest-path")
        .arg(&manifest)
        .output()
        .expect("run `cargo metadata`");
    assert!(
        output.status.success(),
        "cargo metadata failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let meta: Value = serde_json::from_slice(&output.stdout).expect("parse cargo metadata JSON");

    // ── Index packages by id, and record each package's name, manifest dir, and normal-dep on
    //    dregg-lean-ffi (non-dev, non-optional). ──────────────────────────────────────────────────────
    let packages = meta["packages"].as_array().expect("packages array");
    let mut id_to_name: HashMap<&str, &str> = HashMap::new();
    let mut id_to_manifest_dir: HashMap<&str, PathBuf> = HashMap::new();
    let mut id_to_bins: HashMap<&str, Vec<String>> = HashMap::new();
    let mut id_has_lean_ffi_runtime: HashMap<&str, bool> = HashMap::new();

    for p in packages {
        let id = p["id"].as_str().unwrap();
        let name = p["name"].as_str().unwrap();
        id_to_name.insert(id, name);

        let manifest_path = PathBuf::from(p["manifest_path"].as_str().unwrap());
        let dir = manifest_path.parent().unwrap().to_path_buf();
        id_to_manifest_dir.insert(id, dir);

        let bins: Vec<String> = p["targets"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|t| {
                t["kind"]
                    .as_array()
                    .map(|k| k.iter().any(|x| x == "bin"))
                    .unwrap_or(false)
            })
            .map(|t| t["name"].as_str().unwrap().to_string())
            .collect();
        id_to_bins.insert(id, bins);

        // A non-dev, non-optional dependency named `dregg-lean-ffi` — i.e. this crate actually links the
        // Lean archive at runtime. `kind` is null for a normal dep, "dev"/"build" otherwise.
        let has = p["dependencies"].as_array().unwrap().iter().any(|d| {
            d["name"].as_str() == Some("dregg-lean-ffi")
                && d["kind"].is_null()
                && d["optional"].as_bool() != Some(true)
        });
        id_has_lean_ffi_runtime.insert(id, has);
    }

    // ── Build the runtime (normal-dep-only) reachability graph from the resolve nodes. Dev/build edges
    //    do NOT ship in the binary, so they are excluded from the verify-TCB closure. ─────────────────
    let nodes = meta["resolve"]["nodes"].as_array().expect("resolve nodes");
    let mut normal_edges: HashMap<&str, Vec<&str>> = HashMap::new();
    for n in nodes {
        let id = n["id"].as_str().unwrap();
        let mut edges = Vec::new();
        for d in n["deps"].as_array().unwrap() {
            let is_normal = d["dep_kinds"]
                .as_array()
                .map(|ks| ks.iter().any(|k| k["kind"].is_null()))
                .unwrap_or(false);
            if is_normal {
                edges.push(d["pkg"].as_str().unwrap());
            }
        }
        normal_edges.insert(id, edges);
    }

    let verifying: HashSet<&str> = VERIFYING.iter().copied().collect();
    let closure_hits_verifying = |root: &str| -> bool {
        let mut seen: HashSet<&str> = HashSet::new();
        let mut stack = vec![root];
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(name) = id_to_name.get(cur) {
                if verifying.contains(name) {
                    return true;
                }
            }
            if let Some(edges) = normal_edges.get(cur) {
                for &e in edges {
                    if !seen.contains(e) {
                        stack.push(e);
                    }
                }
            }
        }
        false
    };

    let allowlist: HashSet<&str> = DELEGATES_VERIFY.iter().map(|(n, _)| *n).collect();
    let ws_members: Vec<&str> = meta["workspace_members"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap())
        .collect();

    let mut failures: Vec<String> = Vec::new();
    let mut routed: Vec<&str> = Vec::new();
    let mut delegated: Vec<&str> = Vec::new();

    for id in ws_members {
        let bins = id_to_bins.get(id).cloned().unwrap_or_default();
        if bins.is_empty() {
            continue; // not a binary — nothing to route
        }
        if !closure_hits_verifying(id) {
            continue; // does not touch the verify stack
        }
        let name = *id_to_name.get(id).unwrap();

        // ROUTED: installs the verified core in its own src AND links dregg-lean-ffi at runtime.
        let mut src_text = String::new();
        let src_dir = id_to_manifest_dir.get(id).unwrap().join("src");
        read_src_recursive(&src_dir, &mut src_text);
        let installs = ROUTE_INSTALL_TOKENS.iter().any(|t| src_text.contains(t));
        let links_ffi = *id_has_lean_ffi_runtime.get(id).unwrap_or(&false);
        let is_routed = installs && links_ffi;
        let is_allowlisted = allowlist.contains(name);

        match (is_routed, is_allowlisted) {
            (true, false) => routed.push(name),
            (false, true) => delegated.push(name),
            (true, true) => {
                // A wired crate must be REMOVED from the allowlist — otherwise the allowlist rots and the
                // guard would keep passing a crate whose wiring was later ripped out.
                failures.push(format!(
                    "  `{name}` is BOTH routed (installs the core in src) AND on DELEGATES_VERIFY — \
                     remove it from the allowlist so the routed branch is its single source of truth"
                ));
            }
            (false, false) => {
                let reason = if installs && !links_ffi {
                    "it calls an install token but has no non-dev `dregg-lean-ffi` dep (the archive is not linked)"
                } else {
                    "it neither installs the verified core nor is on the DELEGATES_VERIFY allowlist"
                };
                failures.push(format!(
                    "  `{name}` (bins: {bins:?}) reaches the verify stack but {reason}. \
                     Either wire it (install `install_lean_verify_core_real` + a non-dev `dregg-lean-ffi` dep) \
                     or add it to DELEGATES_VERIFY with a justification."
                ));
            }
        }
    }

    routed.sort();
    delegated.sort();
    eprintln!(
        "verify-routing guard: {} routed {:?}; {} delegated (FFI-free leaves) {:?}",
        routed.len(),
        routed,
        delegated.len(),
        delegated
    );

    assert!(
        failures.is_empty(),
        "verify-routing guard FAILED — a binary reaches the ML-DSA verify stack but is neither routed to \
         the Lean-verified core nor consciously allowlisted:\n{}\n\nThis is the \"a crate silently re-enters \
         the verify TCB\" regression gate. Fix by wiring the binary or adding a reviewed DELEGATES_VERIFY \
         entry.",
        failures.join("\n")
    );
}

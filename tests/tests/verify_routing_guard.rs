//! GUARD A — the static routing lint: a CI regression gate for the "the crate leaves the LIVE TCB"
//! design. It is metadata-only (no leanc/FFI link) and load-bearing.
//!
//! # What it protects
//!
//! `dregg_pq::ml_dsa_verify` computes its security-critical accept/reject from the Lean-verified REAL
//! ML-DSA core ONLY in a process that has installed one (the node does this at startup via
//! `dregg_node::install_mldsa_verified_verify_core()`; every other host calls
//! `dregg_sdk::install_verified_pq_cores()` or `dregg_pq::install_verified_mldsa_verify_core(…)`).
//!
//! ⚑ A process that never installs the core does NOT quietly fall back — `mldsa_verify_disposition`
//! REFUSES (`refuse_unaudited` → `process::abort`, `dregg-pq/src/mldsa.rs:833`) unless the operator
//! declared `DREGG_ALLOW_UNAUDITED_PQ=1`, in which case the `fips204` crate IS that process's verify
//! authority. So an unrouted verifying binary is not "unverified": it is one of `abort` or `fips204`,
//! and this guard is where a binary declares which of the three it is BEFORE a box finds out.
//!
//! FFI-free leaf binaries (demos, thin clients, offline tools, the sel4 no_std verifier, …) deliberately
//! never link the 195 MB Lean archive: they are a STRUCTURAL design choice, not an oversight. This guard
//! makes that choice CONSCIOUS and REGRESSION-SAFE:
//!
//!   * every workspace binary whose runtime dependency closure reaches a VERIFYING crate must EITHER
//!     route the verified core (install call in `src/` + an ENABLED, non-dev dep on an archive carrier)
//!     OR appear on the `DELEGATES_VERIFY` allowlist below with a justification;
//!   * a NEW verifying binary added without wiring or an allowlist entry turns CI RED — you cannot
//!     silently ship a binary that re-admits the `fips204` crate to the verify authority;
//!   * a crate that is later WIRED should be REMOVED from the allowlist (its `src/` install call makes it
//!     pass the routed branch), so the allowlist only ever shrinks toward "everything routed".
//!
//! SIGN + KEM are still crate-authoritative in EVERY process (their Lean seams are toy-wired to nothing
//! deployed) — see `dregg-pq/tests/seam_scope_honesty.rs` (GUARD C) for the in-code proof of that.
//!
//! # ⚑ It is METADATA-only, and metadata lies in BOTH directions (measured 2026-07-30)
//!
//! This guard is a proxy: "the closure links a verifying crate" stands in for "this process can decide
//! an ML-DSA accept". A proxy earns its keep only if it is read correctly, and it was being read wrong
//! twice over — once too wide and once too narrow — which is how six packages arrived at "unrouted"
//! together and made an allowlist entry look like the answer for all six.
//!
//!   * TOO WIDE — `cargo metadata`'s `resolve` is the LOCK graph and carries edges for optional deps
//!     nothing activates. `dregg-mirror` (Ed25519 committee gate, grep-zero for `ml_dsa`) was reported
//!     inside the ML-DSA verify stack through `deos-view`'s `cap` feature, which its own
//!     `default-features = false, features = ["web"]` never turns on. The reach is now cargo's, via
//!     `feature_resolved_reach`.
//!   * TOO NARROW — `ROUTE_INSTALL_TOKENS` could not spell the two installers every non-node host
//!     actually calls, and "links the archive" was read as `optional != true`, which calls a
//!     default-on optional dep unlinked. `starbridge-v2` and `dregg-preflight` had been routing for
//!     some time and this guard could not see either; both entries have been deleted.
//!
//! Neither direction is free: a phantom reach costs an allowlist entry (and this repo has minted
//! "add an entry until it is green" as the fail-open move), while an unseen route rots the allowlist
//! into the actual specification.

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
/// in a crate's own `src/` means the crate installs the verified core (and must ALSO carry a linked
/// [`ARCHIVE_CARRIERS`] dep to actually reach the archive).
///
/// ⚑ THIS LIST WAS A FALSE NEGATIVE, and the shape of the miss is worth keeping written down. It named
/// `dregg-pq`'s LOW-LEVEL seam (`install_lean_verify_core_real`, the raw `fn`-pointer setter) and
/// `dregg-node`'s PRIVATE wrapper (`install_mldsa_verified_verify_core`) — and neither is what a
/// non-node host calls. The two spellings every other host actually uses,
/// `dregg_pq::install_verified_mldsa_verify_core` (`dregg-pq/src/mldsa.rs:135`, whose own header calls
/// it "THE ONE install every deployed, archive-linked process calls") and
/// `dregg_sdk::install_verified_pq_cores` (`sdk/src/runtime.rs:403`, the preferred all-six installer),
/// were absent. So `starbridge-v2/src/main.rs:98` — which installs in EVERY default build — read as
/// unrouted, and its allowlist entry's own closure trigger ("remove once the install call lands in
/// src") could never fire. A routing gate that cannot see the routing API is measuring the allowlist.
///
/// ⚑ THE NEW ENTRIES ARE QUALIFIED (`crate::fn(`) ON PURPOSE. A bare `install_verified_pq_cores(` also
/// matches a local `fn` DEFINITION of that name — `preflight/src/main.rs:78` and
/// `node/src/submit_queue_drainer.rs:563` both define one — so an EMPTY local wrapper of the right name
/// would satisfy the routed branch without installing anything. A `fn` definition cannot contain `::`.
const ROUTE_INSTALL_TOKENS: &[&str] = &[
    "install_lean_verify_core_real(", // the dregg-pq seam, called directly
    "install_mldsa_verified_verify_core(", // the shared node helper that calls the seam
    "dregg_pq::install_verified_mldsa_verify_core(", // dregg-pq's primary documented installer
    "dregg_sdk::install_verified_mldsa_verify_core(", // the SDK's single-direction adapter
    "dregg_sdk::install_verified_pq_cores(", // the SDK's preferred all-six installer
];

/// The crates that CARRY `libdregg_lean.a` into a binary AND expose an ML-DSA verify install over it.
/// A crate whose `src/` contains a [`ROUTE_INSTALL_TOKENS`] call must depend on one of these — non-dev,
/// and actually ENABLED — or the install call it wrote cannot reach the archive at runtime.
///
/// This is the tooth that keeps "I typed the install call" from being the whole test. `dregg-sdk` and
/// `dregg-node` qualify because each carries a NON-OPTIONAL `dregg-lean-ffi` of its own (`sdk/Cargo.toml:34`,
/// and `dregg-node`'s installer is a thin wrapper over the same two symbols), so a host that routes
/// THROUGH them links the archive exactly as one that names `dregg-lean-ffi` directly.
const ARCHIVE_CARRIERS: &[&str] = &["dregg-lean-ffi", "dregg-sdk", "dregg-node"];

/// The DELEGATES_VERIFY allowlist: verifying binaries that DELIBERATELY do not route the verified core.
/// Each entry is `(crate_name, justification)`. Adding a crate here is a CONSCIOUS, reviewed decision that
/// this binary is a structural FFI-free leaf (or a not-yet-wired TODO). When a crate is later wired,
/// REMOVE it from this list — its `src/` install call will then satisfy the routed branch instead.
///
/// Entries that do not correspond to a current root-workspace verifying binary (e.g. the sel4 no_std
/// verifier and the discord bot live in SEPARATE excluded workspaces) are documented here for intent but
/// are inert to this guard, which only enumerates root-workspace members.
const DELEGATES_VERIFY: &[(&str, &str)] = &[
    // ── DEFERRED-WIRING entries (2026-07-17) — these are NOT "no verify path" claims ───────────────
    // HONESTY NOTE: all three link the FULL verify stack (traced with `cargo tree -e normal`:
    // dregg-lightclient + dregg-federation + dregg-blocklace + dregg-cell-crypto + dregg-token +
    // dregg-pq; gateway-ask also dregg-auth). So — unlike `dregg-cli` below — we CANNOT claim they have
    // no local PQ verify path: they link a light client. The truthful statement is the uncomfortable one:
    // **`fips204` is in these binaries' verify TCB**, because they never install the Lean-verified core.
    // WHY DEFERRED, not wired: wiring requires a non-dev `dregg-lean-ffi` dep, i.e. linking
    // `libdregg_lean.a` — **101 MB today** (measured 2026-07-17) — into a gateway/web/demo binary.
    // CLOSURE TRIGGER (do not let this entry outlive it): a separate lane is slimming the Lean archive to
    // ~8 MB; with that + linker GC the cost objection evaporates. WHEN THAT LANDS, WIRE THESE AND DELETE
    // THESE THREE ENTRIES (exemplars: `starbridge-v2/src/main.rs:85`, `node/src/lib.rs:2450`,
    // `sdk/src/runtime.rs:72`). Tracked as `VerifyTcbReentryResidual` in GOAL-STARK-KILL.md.
    (
        "dregg-gateway-ask",
        "DEFERRED WIRING (not a no-verify claim): links the full verify stack incl. dregg-auth, whose \
         credential/pq.rs rides the PQ verify path — so fips204 is in this binary's verify TCB. Wiring \
         deferred only on the 101MB libdregg_lean.a link cost; WIRE + delete this entry when the ~8MB \
         Lean archive lands. This is the strongest of the three: it has a named live PQ path.",
    ),
    (
        "dreggnet-web",
        "DEFERRED WIRING (not a no-verify claim): links the full verify stack incl. dregg-lightclient — \
         fips204 is in this binary's verify TCB. Deferred only on the 101MB link cost; WIRE + delete this \
         entry when the ~8MB Lean archive lands.",
    ),
    (
        "real-dungeon-service",
        "DEFERRED WIRING (not a no-verify claim): links the full verify stack incl. dregg-lightclient — \
         fips204 is in this binary's verify TCB. Deferred only on the 101MB link cost; WIRE + delete this \
         entry when the ~8MB Lean archive lands.",
    ),
    (
        "dregg-exec-lean",
        "The `drex_clear` clear-book matcher/settlement demo CLI (moved here from `dregg-intent` so it \
         could install the verified SETTLEMENT gate — FFI-free `dregg-intent` cannot). It DOES link \
         libdregg_lean.a and installs the Lean settlement gate (`register_distributed_gates()`), but does \
         NOT install the ML-DSA verify core: the clear-book pipeline verifies NO ML-DSA signatures (dummy \
         `Authorization::Signature`), so no real PQ signature-verify rides this binary's path. Reaches the \
         verify stack only through the executor deps. TODO: install the verify core too now that the \
         archive is already linked (the old 101MB link-cost deferral no longer applies).",
    ),
    (
        "dungeon-service",
        "DEFERRED WIRING (not a no-verify claim): links the full verify stack incl. dregg-lightclient — \
         fips204 is in this binary's verify TCB. Deferred only on the 101MB link cost; WIRE + delete this \
         entry when the ~8MB Lean archive lands.",
    ),
    (
        "dregg-doc",
        "OPTIONAL-ONLY reach (traced 2026-07-17): the default build has NO verify-stack dep at all; it \
         reaches the stack solely via `dregg-blocklace = { optional = true }`, which is OFF by default. \
         The guard's reach probe is `--all-features` (fail-CLOSED: a bin's `required-features` must not \
         hide an edge), so this crate is still SEEN — that is deliberate, and this entry is the \
         declaration. IF that feature is enabled the binary gains a PQ verify path and should wire the \
         core then.",
    ),
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
    // ── starbridge-v2 IS WIRED and its entry is GONE (2026-07-30). `starbridge-v2/src/main.rs:98`
    //    calls `dregg_sdk::install_verified_pq_cores()` and its `dregg-sdk` dep is turned on by
    //    `default = ["embedded-executor"]`, so every default build routes. The entry outlived its own
    //    closure trigger only because ROUTE_INSTALL_TOKENS could not spell the call — see that list.
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
    // `dregg-preflight`'s entry is GONE (2026-07-30) for the same reason as starbridge-v2's:
    // `preflight/src/main.rs:79` forwards to `dregg_sdk::install_verified_pq_cores()` before the first
    // check, over a NON-optional `dregg-sdk`. It routes; it is not a leaf.
    //
    // ── OFFLINE PRODUCERS / CHECKERS: they reach the stack through a LIBRARY they use for something
    //    else, and their own binary decides nothing with ML-DSA. Each entry below states the
    //    file:line that was READ, not a shape that was assumed — a "no verify path" claim is only
    //    worth the call sites someone actually opened. ⚑ These are NOT "fips204 is in the TCB"
    //    entries and NOT deferred wiring: with no verified core installed and no declared
    //    `DREGG_ALLOW_UNAUDITED_PQ`, `dregg_pq::ml_dsa_verify` REFUSES (`refuse_unaudited` →
    //    `process::abort`, `dregg-pq/src/mldsa.rs:833`). So if one of these ever GREW an ML-DSA
    //    verify, it would abort rather than quietly hand the verdict to `fips204`. The entry is the
    //    declaration that it does not have one today.
    (
        "dungeon-on-dregg",
        "OFFLINE PRODUCER, no ML-DSA decision. The one bin is `dungeon-private-quest-producer` \
         (`src/bin/private-quest-producer.rs`, `required-features = [\"private-quest\"]`): it builds a \
         `PrivateQuestRaid`, advances it twice and writes two `.fhquest` receipts. Its whole graph is \
         `dregg_turn_prover::private_graph_rewrite_history` — field arithmetic and a HidingFRI \
         producer; `private_quest.rs` has no `Authorization`, no executor and no signature check \
         (grep-zero for `dregg_turn::`). The package reaches `dregg-turn` because the GAME library \
         drives turns, not because this binary verifies one. WIRE IT if a bin is added here that \
         opens a signed turn.",
    ),
    (
        "dregg-attest-check",
        "OFFLINE TDX/DCAP CHECKER — the wrong signature algorithm entirely. `verify_record` \
         (`attest-check/src/lib.rs:435`) runs six checks: sha256 digests, the Chutes `report_data` \
         binding, the measurement registry, the receipt commitment, the pinned Intel SGX Root CA and \
         the ECDSA-P256 DCAP chain. It touches `dungeon-on-dregg` for exactly ONE symbol — \
         `narrator::tee_provenance_commitment` (a hash, `src/lib.rs:46`) — and inherits that crate's \
         `dregg-turn` edge with it. grep-zero for `ml_dsa`/`dregg_pq` in `attest-check/src`.",
    ),
    (
        "dreggnet-market",
        "OFFLINE DARK-AMM OPERATOR CLI, classical transport only. `dark-amm-tool` \
         (`required-features = [\"dark-amm-game\"]`) verifies with `verify_strict` (Ed25519, \
         `src/bin/dark-amm-tool.rs:617`) and `verify_public_decision_transcript` (:1505) over a roster \
         it builds itself at :1237 with `EqualityTransportRoster::new` — which IS \
         `new_classical_compatibility` (`fhegg-fhe/src/mpc_party/transport.rs:348`). The ML-DSA arm of \
         `verify_frame` (transport.rs:4079) sits inside `match roster.profile` under \
         `NativePostQuantum*`, so a classical roster never reaches it, and `native_key()` has nothing \
         to return. The tool has grep-zero `NativePq`. Its other verifier, \
         `fhegg_fhe::attestation::AuthenticatedQuorumVerifier` (:643-830), is the CLASSICAL one — the \
         ML-DSA quorum check lives in the `NativePq` sibling at :1151. WIRE IT the day this tool \
         constructs a native-PQ roster.",
    ),
    (
        "dreggnet-catalog",
        "QUEUE WRITER, not a decider. `dregg-private-bazaar-submit` \
         (`required-features = [\"private-bazaar-live\"]`) reads a sealed book on stdin, parses it \
         (`private_bazaar_submit.rs:267` → `submit_sealed_book`) and appends a durable 0600 record for \
         the serving process to drain; the manifest says it out loud — \"No FFI: submitting writes a \
         durable record; the proving happens in the serving process\". The catalog's OWN verified-core \
         installs (`private_bazaar_live.rs:800-810`) are `#[cfg(test)]` — the SUPERVISOR that drains \
         this queue is the process that must route, and it is `dreggnet-web`/`dregg-drive`, not this \
         binary.",
    ),
    (
        "fhegg-fhe",
        "THE ONE BIN THAT DECIDES IS ALREADY ROUTED — the package is not, and the difference is \
         `required-features`. `fhegg-fhe` has 7 live `dregg_pq::ml_dsa_verify` call sites \
         (`attestation.rs:1192`, `distributed_bfv_correlation.rs:448`, `mpc_party.rs:2097`, \
         `mpc_party/transport.rs:738,1744,4079,4540`) and they are ALL behind the native-PQ roster / \
         native-PQ quorum verifier. Exactly ONE of the 13 bins touches that surface: \
         `threshold-committee-party`, which is `required-features = [\"verified-pq-runtime-tests\"]` = \
         `dep:dregg-lean-ffi`, so cargo CANNOT build it without the archive, and it installs all six \
         verified cores at `src/bin/threshold_committee_party.rs:350` (refusing to serve if any fails, \
         and never touching DREGG_ALLOW_UNAUDITED_PQ). The other 12 — the benches, the gpu tools, \
         `smoke`, and `fhegg-equality-worker`, which builds a `ClassicalCompatibility` roster at \
         `equality_transport_worker.rs:171` — are grep-zero for `NativePq|native_post_quantum|\
         NATIVE_PQ`. This guard is PACKAGE-granular and `dregg-lean-ffi` is optional here, so it \
         cannot see a per-bin route; that granularity gap is what this entry records. CLOSURE: make \
         `dregg-lean-ffi` non-optional and install in every bin's `main`, or teach the guard bins.",
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

/// The set of dependency KEYS (the name a `[dependencies]` entry is written under — the rename when
/// there is one) that this package's OWN `default` feature turns on, via `dep:x` or `x/feat`.
///
/// Needed because "does this crate link the Lean archive" is NOT answered by `optional != true`.
/// `starbridge-v2` writes `dregg-sdk = { optional = true }` and then `default = ["embedded-executor"]`
/// with `embedded-executor = [… "dep:dregg-sdk" …]`: every default build links the archive and runs the
/// install at `src/main.rs:98`, while a raw optional-flag read calls it unlinked and refuses to see the
/// route. Only the package's own feature table is walked — no dependency resolution, no unification
/// with the rest of the workspace.
fn deps_enabled_by_default_features(pkg: &Value) -> HashSet<String> {
    let table = pkg["features"].as_object();
    let mut seen_features: HashSet<String> = HashSet::new();
    let mut deps: HashSet<String> = HashSet::new();
    let mut stack = vec!["default".to_string()];
    while let Some(feature) = stack.pop() {
        if !seen_features.insert(feature.clone()) {
            continue;
        }
        let Some(items) = table
            .and_then(|t| t.get(&feature))
            .and_then(|v| v.as_array())
        else {
            continue;
        };
        for item in items {
            let Some(entry) = item.as_str() else { continue };
            if let Some(dep) = entry.strip_prefix("dep:") {
                deps.insert(dep.to_string());
            } else if let Some((dep, _)) = entry.split_once('/') {
                // `dep/feat` ALSO activates an optional `dep`; the weak form `dep?/feat` does not.
                if !dep.ends_with('?') {
                    deps.insert(dep.to_string());
                }
            } else {
                stack.push(entry.to_string());
            }
        }
    }
    deps
}

/// Whether `pkg` has a non-dev, ENABLED dependency on one of the [`ARCHIVE_CARRIERS`] — i.e. whether an
/// install call written in its `src/` can actually reach `libdregg_lean.a` at runtime.
fn links_lean_archive(pkg: &Value) -> bool {
    let default_deps = deps_enabled_by_default_features(pkg);
    pkg["dependencies"]
        .as_array()
        .map(|deps| {
            deps.iter().any(|d| {
                let Some(name) = d["name"].as_str() else {
                    return false;
                };
                if !ARCHIVE_CARRIERS.contains(&name) || !d["kind"].is_null() {
                    return false;
                }
                let key = d["rename"].as_str().unwrap_or(name);
                d["optional"].as_bool() != Some(true) || default_deps.contains(key)
            })
        })
        .unwrap_or(false)
}

/// ⚑ THE REACH ORACLE: cargo's OWN resolver, with FEATURES APPLIED and this package as the ROOT.
///
/// `cargo metadata`'s `resolve` is the LOCK graph — it carries an edge for an optional dependency even
/// when nothing on earth activates it. That manufactures phantom reach, and a phantom reach costs an
/// allowlist entry, which is the one currency this guard must not print. Measured 2026-07-30:
/// `dregg-mirror` takes `deos-view = { default-features = false, features = ["web"] }` and `dregg-auth`
/// hangs off `deos-view`'s `cap` feature, which `web` does not imply. `dregg-mirror/src` is grep-zero
/// for `ml_dsa` / `dregg_pq` / `dregg_auth` and its only signature check is Ed25519 (`Cargo.toml`: "the
/// committee-anchored quorum gate"). The metadata closure reported it INSIDE the ML-DSA verify stack
/// anyway, and the fix for that is not an entry saying so — it is to ask cargo.
///
/// `--all-features` is deliberate and it is the FAIL-CLOSED direction: a `[[bin]]` with
/// `required-features` must not be able to hide an edge from this probe. It over-approximates (a crate
/// that only reaches under an off-by-default feature is still SEEN, e.g. `dregg-doc`), which costs a
/// declaration and never a miss.
///
/// `Err` is NOT a pass. A probe that cannot run leaves the package reported, with the reason attached.
fn feature_resolved_reach(manifest: &Path, pkg: &str) -> Result<HashSet<String>, String> {
    let out = Command::new(env!("CARGO"))
        .args(["tree", "-e", "normal", "--all-features"])
        .args(["--prefix", "depth", "--format", "{p}"])
        .arg("--manifest-path")
        .arg(manifest)
        .args(["-p", pkg])
        .output()
        .map_err(|e| format!("could not run `cargo tree -p {pkg}`: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "`cargo tree -p {pkg}` failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|line| {
            // `--prefix depth` writes the depth with no separator: `2dregg-pq v0.1.0 (/path)`.
            let name = line.trim_start_matches(|c: char| c.is_ascii_digit());
            name.split_whitespace().next().map(str::to_string)
        })
        .collect())
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

    // ── Index packages by id, and record each package's name, manifest dir, and whether it links the
    //    Lean archive at runtime (a non-dev, ENABLED dep on an ARCHIVE_CARRIERS crate). ───────────────
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

        id_has_lean_ffi_runtime.insert(id, links_lean_archive(p));
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
    // The CHEAP OVER-APPROXIMATION. It counts every optional dep, enabled or not, so a package it
    // clears provably cannot reach the stack under any feature set and can be skipped without asking
    // cargo. Every package it does NOT clear goes to `feature_resolved_reach` for the real answer.
    let closure_may_hit_verifying = |root: &str| -> bool {
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
    let mut phantom: Vec<&str> = Vec::new();

    for id in ws_members {
        let bins = id_to_bins.get(id).cloned().unwrap_or_default();
        if bins.is_empty() {
            continue; // not a binary — nothing to route
        }
        if !closure_may_hit_verifying(id) {
            continue; // cannot touch the verify stack under ANY feature set
        }
        let name = *id_to_name.get(id).unwrap();

        // THE REACH, for real: cargo's feature-resolved graph rooted at this package. A `cargo tree`
        // that cannot run is NOT a pass — the package is reported with the probe's own error.
        match feature_resolved_reach(&manifest, name) {
            Ok(tree) => {
                if !tree.iter().any(|p| verifying.contains(p.as_str())) {
                    // The metadata closure saw an optional dep no feature turns on. Not a reach.
                    phantom.push(name);
                    continue;
                }
            }
            Err(why) => {
                failures.push(format!(
                    "  `{name}` (bins: {bins:?}) may reach the verify stack and the feature-resolved \
                     reach probe COULD NOT RUN, so this guard has no answer for it: {why}"
                ));
                continue;
            }
        }

        // ROUTED: installs the verified core in its own src AND links the Lean archive at runtime.
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
                    "it calls an install token but has no enabled, non-dev dep on an archive carrier \
                     (dregg-lean-ffi / dregg-sdk / dregg-node), so the archive is not linked"
                } else {
                    "it neither installs the verified core nor is on the DELEGATES_VERIFY allowlist"
                };
                failures.push(format!(
                    "  `{name}` (bins: {bins:?}) reaches the verify stack but {reason}. \
                     Either wire it (`dregg_sdk::install_verified_pq_cores()` + a non-dev `dregg-sdk` dep, \
                     or `dregg_pq::install_verified_mldsa_verify_core` + `dregg-lean-ffi`) \
                     or add it to DELEGATES_VERIFY with a justification."
                ));
            }
        }
    }

    routed.sort();
    delegated.sort();
    phantom.sort();
    eprintln!(
        "verify-routing guard: {} routed {:?}; {} delegated (FFI-free leaves) {:?}; \
         {} metadata-only phantoms dropped by the feature-resolved probe {:?}",
        routed.len(),
        routed,
        delegated.len(),
        delegated,
        phantom.len(),
        phantom
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

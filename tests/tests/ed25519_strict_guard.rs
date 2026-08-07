//! TREE-WIDE INVARIANT — every FIRST-PARTY production module that verifies an
//! Ed25519 signature must do so STRICTLY (`VerifyingKey::verify_strict`), not via
//! the cofactored `Verifier::verify`. This gate catches the NEXT drift, not just
//! the sites fixed today.
//!
//! # Why this is load-bearing, proven from execution (not prose)
//!
//! The cofactored `Verifier::verify` accepts SMALL-ORDER public keys. Under a
//! small-order key `A` (e.g. the Ed25519 identity point, compressed `y = 1`), the
//! signature `(R = identity, s = 0)` satisfies `R == s·B + h·A` for EVERY message
//! — so anyone holding NO SECRET forges a signature that verifies. `verify_strict`
//! denies weak keys and small-order `R` (RFC 8032 §5.1.7), closing that door.
//!
//! Wherever the verifying key is ATTACKER-CHOSEN — read out of a wire value rather
//! than pinned to a trusted roster — this is a live universal-forgery vector, not
//! hygiene. Confirmed this session on two such paths, each fixed + mutation-rigged:
//!   * `dregg_blocklace::evidence` — a self-contained equivocation exhibit carries
//!     its own `creator` key; a cofactored verify let a no-secret exhibit certify
//!     and SLASH a bonded strand. (`forged_exhibit_under_a_small_order_creator_refuses`)
//!   * `dregg_agent::receipt::verify_signature` — the co-signer `signer` is carried
//!     in the wire attestation; a cofactored verify forged a quorum co-signature.
//!     (`a_small_order_signer_cannot_forge_a_signature`)
//! Both crates are now strict-only and DO NOT import the non-strict trait, so they
//! are deliberately absent from the allowlist below: a regression that re-admits
//! `Verifier::verify` in them re-introduces the module-top import and turns this
//! gate RED.
//!
//! # The signal (robust, cheap, compiler-grounded)
//!
//! `verify_strict` is an INHERENT method on `VerifyingKey`; the non-strict `verify`
//! is the `signature::Verifier` trait method and therefore REQUIRES the trait to be
//! in scope. A **module-top** (column-0) `use ed25519_dalek::…Verifier` /
//! `use signature::…Verifier` is the necessary condition for a non-strict dalek
//! verify at module scope. Test-module and fn-local imports are indented (inside
//! `mod tests { … }` or a fn body) and so are excluded automatically — the gate
//! keys on column-0 `use` lines only.
//!
//! A first-party production `src/**.rs` with a module-top non-strict `Verifier`
//! import must EITHER not exist (convert its call to `verify_strict` and drop the
//! trait) OR appear on `ALLOWLIST` with a reviewed justification. The allowlist is
//! an HONEST DEBT LEDGER, not a blessing: `GRANDFATHERED` entries are un-audited
//! non-strict sites that still owe an attacker-key-reachability review.

use std::path::{Path, PathBuf};

/// Workspace root = the parent of this `tests` crate's manifest dir.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("tests crate has a parent (the workspace root)")
        .to_path_buf()
}

/// Directory names never descended into: build output, third-party vendored code,
/// scratch, and VCS metadata. Vendored crates (e.g. `starbridge-v2/vendor/*`) are
/// not ours and set their own crypto policy.
const SKIP_DIRS: &[&str] = &[
    "target",
    "vendor",
    ".git",
    "node_modules",
    "scratchpad",
    "tmp",
];

/// A module-top non-strict `Verifier` trait import is allowed ONLY at these
/// repo-relative paths, each with a reviewed reason. Categories:
///   * `EXTERNAL-SCHEME MIRROR` — verifies signatures of an EXTERNAL chain whose
///     own runtime uses cofactored verification; making it strict would DIVERGE
///     from that chain (reject what the chain accepts). Strictness here is a bug.
///   * `CONSENSUS MIRROR` — like EXTERNAL-SCHEME MIRROR, but mirrors a FIRST-PARTY
///     verifier (node's own acceptance check) whose exact accept-set another crate
///     must predict WITHOUT importing it. Diverging (strict here, cofactored in the
///     verifier it mirrors) would mispredict acceptance. Fix belongs in the mirrored
///     verifier, not the mirror.
///   * `PINNED-KEY` — the verifying key is not attacker-chosen: the code refuses
///     unless the wire key EQUALS a caller-pinned anchor/roster entry BEFORE the
///     verify. The small-order forgery needs an attacker-chosen key, so it is out of
///     reach; cofactored verify is defense-in-depth debt, not a live forgery vector.
///   * `TEST MODULE` — the file is `#[cfg(test)]` code compiled under `src/`.
///   * `HELD DIRTY` — another lane holds the file uncommitted this session; not
///     touched (shared-tree rule). Re-audit when it settles.
///   * `ALREADY STRICT` — prod path is `verify_strict`; the module-top import
///     serves an in-crate strictness *control* test.
///   * `GRANDFATHERED` — a non-strict prod site present before this gate, NOT yet
///     audited for attacker-key reachability. OWES a review: convert to
///     `verify_strict`, or justify (pinned/roster key) and re-file under a real
///     category. This is debt, tracked, not endorsed.
const ALLOWLIST: &[(&str, &str)] = &[
    // ── EXTERNAL-SCHEME MIRROR (verified by reading the code) ───────────────────
    (
        "bridge/src/solana_consensus.rs",
        "EXTERNAL-SCHEME MIRROR: verifies Solana validator vote-tx signatures under \
         the vote/account pubkeys carried in the tx. Solana's own runtime uses \
         cofactored ed25519 verification; verify_strict here would reject votes the \
         Solana chain accepts (small-order keys are consensus-valid THERE), diverging \
         the bridge from the chain it tracks. Cofactored is CORRECT for chain parity.",
    ),
    (
        "bridge/src/solana_wire.rs",
        "EXTERNAL-SCHEME MIRROR: parse_verified_vote_tx re-verifies a real serialized \
         Solana transaction's signatures for chain parity. Same rationale as \
         solana_consensus.rs — must match Solana's cofactored verify, not diverge.",
    ),
    // ── TEST MODULE under src/ ──────────────────────────────────────────────────
    (
        "turn/src/tests.rs",
        "TEST MODULE: turn/src/lib.rs includes it as `#[cfg(test)] mod tests;` — the \
         whole file is test code (the non-strict import exercises verify paths).",
    ),
    // ── HELD DIRTY this session (shared-tree rule: not touched) ──────────────────
    (
        "cell-crypto/src/peer_exchange.rs",
        "ALREADY STRICT + HELD DIRTY: verify_transition uses verify_strict (fixed a \
         prior session) and the crate already ships the small-order strictness tooth \
         (`peer_transition...`); the module-top import serves that in-crate control. \
         File is uncommitted by another lane — re-audit when it settles.",
    ),
    // ── PINNED-KEY (audited 2026-07-17: key equals a caller-pinned anchor) ───────
    (
        "deco-prove/src/notary.rs",
        "PINNED-KEY (audited 2026-07-17): verify_notary_attestation builds the vk from \
         att.notary_pubkey, but line ~166 returns WrongNotary unless \
         `att.notary_pubkey == expected_notary` (the caller-pinned anchor) BEFORE the \
         verify — so the verified key is the pinned anchor, never attacker-chosen. The \
         commitment is separately recomputed (line ~169) so malleability cannot re-point \
         a sig at other facts. Small-order forgery is out of reach; cofactored is \
         defense-in-depth debt only. Pin bites: `wrong_notary_anchor_refused`. NOT \
         converted (converting a pinned site is not the exploit fix).",
    ),
    (
        "deco-prove/src/tlsn_attest.rs",
        "PINNED-KEY (audited 2026-07-17): verify_tlsn_presentation returns NotaryMismatch \
         unless `pres.verifying_key == config.expected_notary` (line ~342) BEFORE \
         building the vk from those same bytes — the verified key is the pinned anchor, \
         not wire-chosen. Small-order forgery needs an attacker-chosen key and is out of \
         reach. Pin bites: `wrong_notary_anchor_is_refused`. NOT converted.",
    ),
    // ── CONSENSUS MIRROR (audited 2026-07-17: must match node, do not diverge) ───
    (
        "dregg-doc/src/ci_verdict.rs",
        "CONSENSUS MIRROR (audited 2026-07-17): verify_nullifier_update_signature (line \
         ~450) faithfully mirrors node's post_update_commitment acceptance check so a \
         test can predict node acceptance WITHOUT depending on node. node's real check \
         `verify_ed25519_signature` (node/src/api.rs:6789) uses cofactored \
         `verifying_key.verify(...)` (line 6798). The key IS wire-supplied (cell_id \
         doubles as the ed25519 pubkey), so node ITSELF is a genuine attacker-key \
         non-strict site — but converting THIS mirror to strict would make it mispredict \
         node acceptance (the solana_consensus.rs trap, internal edition). The fix, if \
         any, belongs in node/src/api.rs:6789 (held dirty by another lane this session; \
         reported for the node-side security swarm), and this mirror must follow node.",
    ),
    // ── GRANDFATHERED: un-audited non-strict prod sites (debt, not endorsement) ──
    (
        "dregg-pay/src/otc.rs",
        "GRANDFATHERED: OTC counterpart signature; counterpart key is wire-supplied — \
         a likely convert-to-strict site.",
    ),
    (
        "dregg-pay/src/swap.rs",
        "GRANDFATHERED: swap authority/counterpart signatures; audit key source, likely convert.",
    ),
    (
        "realm-model/src/identity.rs",
        "GRANDFATHERED: identity signature verify. Audit key source.",
    ),
    (
        "sandstorm-bridge/src/bridge.rs",
        "GRANDFATHERED: sandstorm/bitcoin bridge — MAY be an external-scheme mirror \
         (Bitcoin/BIP-340 is a different scheme entirely; any ed25519 leg here needs \
         its own audit). Classify as EXTERNAL-SCHEME MIRROR or convert.",
    ),
    (
        "sandstorm-bridge/src/grain.rs",
        "GRANDFATHERED: sandstorm bridge grain signatures; audit key source / scheme.",
    ),
    (
        "sandstorm-bridge/src/spk.rs",
        "GRANDFATHERED: sandstorm bridge script-pubkey path; audit key source / scheme.",
    ),
    (
        "sdk/src/device_pairing.rs",
        "GRANDFATHERED: device-pairing peer key is wire-supplied (attacker-influenced) \
         — a likely convert-to-strict site.",
    ),
    (
        "starbridge-apps/site-host/src/registry.rs",
        "GRANDFATHERED: site-registry receipt signature verify. Audit key source.",
    ),
    (
        "storage/src/durability_deal.rs",
        "GRANDFATHERED: PoR challenge signature under the placement operator key \
         (bond-pinned at placement, but placement is deal data) — audit reachability.",
    ),
    (
        "webauth-core/src/credext.rs",
        "GRANDFATHERED: credential-extension signature; key is presented — likely convert.",
    ),
    (
        "zkoracle-prove/src/authentic.rs",
        "GRANDFATHERED: zkoracle attestation/presentation signature leg. Audit key source.",
    ),
];

/// The regex-free detector: a line is a module-top non-strict `Verifier` import iff
/// it starts (column 0) with `use ed25519_dalek::` or `use signature::` AND names
/// the `Verifier` trait (the non-strict path's necessary import). `verify_strict`
/// is inherent and needs no trait, so a strict-only module never trips this.
fn is_module_top_verifier_import(line: &str) -> bool {
    // Column 0: no leading whitespace (fn-local / test-mod imports are indented).
    if line.starts_with(char::is_whitespace) {
        return false;
    }
    let l = line.trim_end();
    let is_dalek = l.starts_with("use ed25519_dalek::") || l.starts_with("use signature::");
    if !is_dalek {
        return false;
    }
    // Word-boundary match on the trait name so `VerifyingKey` does not count.
    l.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .any(|tok| tok == "Verifier")
}

/// Recursively collect first-party `src/**.rs`. A file is "first-party production
/// source" iff its path contains a `/src/` segment and none of `SKIP_DIRS`.
fn collect_src_rs(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if SKIP_DIRS.contains(&name.as_ref()) {
                continue;
            }
            collect_src_rs(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

#[test]
fn no_unallowlisted_module_top_nonstrict_ed25519_verify_import() {
    let root = workspace_root();
    let mut files = Vec::new();
    collect_src_rs(&root, &mut files);

    // Only files under a `/src/` directory are first-party production source.
    let allow: std::collections::HashSet<&str> = ALLOWLIST.iter().map(|(p, _)| *p).collect();

    let mut violations: Vec<String> = Vec::new();
    let mut allow_hits: std::collections::HashSet<String> = std::collections::HashSet::new();

    for path in &files {
        let rel = path
            .strip_prefix(&root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        if !rel.contains("/src/") {
            continue; // examples/, benches/, build scripts at crate root, etc.
        }
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let has = text.lines().any(is_module_top_verifier_import);
        if !has {
            continue;
        }
        if allow.contains(rel.as_str()) {
            allow_hits.insert(rel);
        } else {
            violations.push(format!(
                "  {rel} imports the non-strict `Verifier` trait at module scope but is \
                 NOT on the allowlist. Convert its ed25519 verify to `verify_strict` and \
                 drop the trait import, OR add a reviewed ALLOWLIST entry (with the key \
                 source: attacker-chosen => MUST convert; pinned/roster or external-chain \
                 mirror => justify)."
            ));
        }
    }

    // Rot guard: an allowlist entry whose file no longer trips the detector (fixed,
    // renamed, or deleted) is stale and must be removed — otherwise the allowlist
    // silently grows a license for a site that no longer needs it.
    let mut stale: Vec<&str> = ALLOWLIST
        .iter()
        .map(|(p, _)| *p)
        .filter(|p| !allow_hits.contains(*p))
        .collect();
    stale.sort_unstable();

    let mut msg = String::new();
    if !violations.is_empty() {
        violations.sort();
        msg.push_str("UN-ALLOWLISTED non-strict ed25519 verify import(s):\n");
        msg.push_str(&violations.join("\n"));
        msg.push('\n');
    }
    if !stale.is_empty() {
        msg.push_str(
            "\nSTALE allowlist entries (file no longer imports the trait — remove them):\n",
        );
        for s in stale {
            msg.push_str(&format!("  {s}\n"));
        }
    }
    assert!(
        msg.is_empty(),
        "ed25519 strictness guard FAILED.\n{msg}\n\
         This gate enforces the tree-wide invariant that first-party production modules \
         verify Ed25519 strictly (verify_strict), closing the small-order universal-forgery \
         vector on attacker-chosen keys."
    );
}

/// NON-VACUITY: the detector must actually fire on the exact shape it guards, and
/// must NOT fire on the strict-only shape or on indented (test/fn-local) imports.
/// Without this, a detector that silently matched nothing would pass forever.
#[test]
fn detector_is_non_vacuous() {
    // POSITIVE: the module-top non-strict trait import the guard forbids.
    assert!(is_module_top_verifier_import(
        "use ed25519_dalek::{Signature, Verifier, VerifyingKey};"
    ));
    assert!(is_module_top_verifier_import("use signature::Verifier;"));
    assert!(is_module_top_verifier_import(
        "use ed25519_dalek::{Verifier as _, VerifyingKey};"
    ));

    // NEGATIVE: `VerifyingKey` alone (strict-only module) must NOT match.
    assert!(!is_module_top_verifier_import(
        "use ed25519_dalek::{Signature, VerifyingKey};"
    ));
    // NEGATIVE: an INDENTED import (inside `mod tests {}` or a fn) is out of scope.
    assert!(!is_module_top_verifier_import(
        "    use ed25519_dalek::{Signature, Verifier, VerifyingKey};"
    ));
    // NEGATIVE: an unrelated module-level use.
    assert!(!is_module_top_verifier_import(
        "use std::collections::HashMap;"
    ));
}

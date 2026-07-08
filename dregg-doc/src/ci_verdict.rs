//! WORK-BINDING CI — a [`CiVerdict`] and the machinery that binds it INSIDE a
//! signed check-turn receipt, so "CI green" means "the actual work ran against
//! THIS pull request's code", not "a trusted key signed that a cursor advanced".
//!
//! ## Why this exists (the scholar-review hole)
//!
//! The forge's older required-check form
//! ([`crate::check::CheckRequirement::CommittedReceipt`]) proves only that a
//! trusted key signed the turn named `turn_hash`, finalized — a CONTENT-FREE
//! cursor turn. A host can seed a trivial 1-step workflow, sign its "terminal"
//! receipt, and the gate passes with ZERO build done: it never binds the PR's
//! code. `CommittedReceipt` binds AUTHORSHIP, not WORK.
//!
//! [`CiVerdict`] closes that: a verdict is the statement "command_id was run in
//! confinement_id against input_root and produced exit_code + output_digest".
//! The [`crate::check::CheckRequirement::CiRun`] check
//! ([`crate::check::RequiredCheck::ci_run`]) is satisfied only when a
//! committed, executor-signed receipt **commits exactly this verdict** and the
//! verdict is bound to the PR's real post-merge code
//! ([`crate::PullRequest::input_root`]) with `exit_code == 0`.
//!
//! ## How the verdict is bound INSIDE the signed turn (the crux)
//!
//! A verdict is NOT loose data presented alongside a receipt — that would let a
//! host wave a favorable verdict next to any unrelated signed receipt. Instead:
//!
//! 1. The CI run is a real turn on a dedicated **CI-run region cell** (a
//!    genesis [`crate::ExecutorDrivenDoc`], fixed `(editor_seed, region_seed)`).
//!    The one thing that turn commits is [`ci_run_patch`]`(verdict)` — an
//!    `Op::Add` whose atom content is the canonical [`CiVerdict::encoding`]. So
//!    the turn's `SetField` effects (hence its `turn.hash()`) are a pure
//!    function of the verdict.
//! 2. The executor SIGNS the receipt over its canonical message, which covers
//!    `receipt.turn_hash` — so the signature cryptographically binds the turn
//!    hash, and therefore the verdict the turn committed.
//! 3. [`crate::check::RequiredCheck::satisfied_by`] **re-derives** the planned
//!    turn hash from the PRESENTED verdict ([`planned_ci_run_hash`]) and refuses
//!    unless it equals `receipt.turn_hash`.
//!
//! A loose verdict therefore cannot forge satisfaction: to make the re-derived
//! hash equal a signed receipt's `turn_hash`, that receipt's turn must have
//! actually committed *this* verdict (the projection is injective in the
//! verdict's bytes). Swapping any field re-derives a different hash and refuses.
//!
//! ## Anti-replay
//!
//! A signed verdict must not satisfy the same check across multiple lands / PRs.
//! [`ci_nullifier`] keys a consumed-set entry by `(pr base fold, verdict)`;
//! [`crate::PullRequest::land_checked`] consumes it on a successful land so the
//! same verdict presented again is refused. The in-process consumed-set is
//! [`CiNullifierSet`] (see the crate report for the durable cross-node seam).
//!
//! ## What this binds — and what it does NOT (the L2/L3 seam)
//!
//! The verdict is a trusted-executor ATTESTATION bound to the PR's code. It
//! proves "a trusted key asserts running command_id against this exact code
//! gave exit_code + output_digest" — it does NOT by itself prove the host ran
//! the command honestly (a lying host is the executor; it can sign a fabricated
//! but well-formed verdict for the real `input_root`). Catching a lying host is
//! the L3 re-executor's job: re-run command_id against the same `input_root` in
//! a fresh confinement and compare `output_digest`. This gate makes that
//! comparison MEANINGFUL by binding the attestation to (this code, this command,
//! a real signature) — see the crate report.

use std::collections::HashSet;

use crate::atom::{AtomId, Author};
use crate::executor_drive::ExecutorDrivenDoc;
use crate::patch::Patch;
use dregg_turn::{TurnError, TurnReceipt};

/// The fixed author of every CI-run commit patch. The CI-run region cell is
/// dedicated to a single verdict, so the authoring identity is a constant — the
/// verdict's non-forgeability rides the executor signature over the turn, not
/// this label.
const CI_RUN_AUTHOR: Author = Author(0xC1C1_C1C1_C1C1_C1C1);
/// The fixed atom seed for the CI-run commit patch (so the atom id is a
/// deterministic function of the verdict content alone).
const CI_RUN_SEED: u64 = 0xC1_5EED_C1_5EED;
/// Domain tag separating a verdict's canonical encoding from any other bytes.
const VERDICT_DOMAIN: &[u8] = b"dregg-forge/ci-verdict/v1";
/// Domain tag for the anti-replay nullifier preimage.
const NULLIFIER_DOMAIN: &[u8] = b"dregg-forge/ci-nullifier/v1";

/// THE WORK-BINDING CI ATTESTATION: "command_id was run in confinement_id
/// against input_root and produced exit_code + output_digest."
///
/// Every field is load-bearing for the gate:
/// - `input_root` binds the verdict to the exact post-merge code that would land
///   ([`crate::PullRequest::input_root`]) — a verdict for other code is refused;
/// - `command_id` names WHICH required check ran (not some other turn);
/// - `confinement_id` records the confinement the run happened in (the L2
///   runner's sandbox identity — carried for audit / L3 re-execution);
/// - `exit_code` gates pass/fail (`0` = pass);
/// - `output_digest` is what an L3 re-executor re-derives and compares to catch
///   a lying host.
///
/// A verdict is bound INSIDE a signed turn, never presented loose — see the
/// module docs. `encoding` is its canonical, injective serialization.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CiVerdict {
    /// A stable digest of the PR's exact post-merge state
    /// ([`crate::PullRequest::input_root`]) — the code the CI actually ran on.
    pub input_root: [u8; 32],
    /// Which required check this is the result of (the command that ran).
    pub command_id: [u8; 32],
    /// The confinement the command ran in (the L2 runner's sandbox identity).
    pub confinement_id: [u8; 32],
    /// The command's exit code (`0` = pass; anything else fails the check).
    pub exit_code: i32,
    /// A digest of the command's output — what an L3 re-executor re-derives and
    /// compares against a re-run to catch a lying host.
    pub output_digest: [u8; 32],
}

impl CiVerdict {
    /// The canonical, domain-tagged, injective byte encoding of the verdict.
    /// Every field is fixed-width and in a fixed order, so distinct verdicts
    /// encode to distinct bytes — the property the in-turn binding rests on.
    pub fn encoding(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(VERDICT_DOMAIN.len() + 32 * 4 + 4);
        b.extend_from_slice(VERDICT_DOMAIN);
        b.extend_from_slice(&self.input_root);
        b.extend_from_slice(&self.command_id);
        b.extend_from_slice(&self.confinement_id);
        b.extend_from_slice(&self.exit_code.to_le_bytes());
        b.extend_from_slice(&self.output_digest);
        b
    }

    /// The atom content the CI-run turn commits: the hex of [`CiVerdict::encoding`]
    /// (a document atom's content is a UTF-8 `String`, so the raw bytes are
    /// hex-encoded). Injective in the verdict, so the committed leaf — and hence
    /// the turn hash — is a pure function of the verdict.
    pub fn content_atom(&self) -> String {
        hex_encode(&self.encoding())
    }
}

/// The CI-run commit patch: the single `Op::Add` a CI-run turn commits, whose
/// atom content is the canonical [`CiVerdict::content_atom`]. Deterministic in
/// the verdict (fixed author, fixed seed, added after `ROOT`), so both the
/// runner ([`run_ci_verdict`]) and the verifier ([`planned_ci_run_hash`]) build
/// the identical turn.
pub fn ci_run_patch(verdict: &CiVerdict) -> Patch {
    let (_, op) = Patch::add(CI_RUN_SEED, &verdict.content_atom(), AtomId::ROOT);
    Patch::by(CI_RUN_AUTHOR, [op])
}

/// **L2 CONFINED-RUNNER COMMIT PATH** — drive `verdict` as the genesis turn of a
/// fresh CI-run region cell (`(editor_seed, region_seed)`), signed by the
/// executor key `signing_seed`. The returned receipt is the committed,
/// executor-signed witness that [`crate::check::RequiredCheck::ci_run`] verifies.
///
/// The CI-run turn MUST be the genesis of its cell (this drives exactly one
/// edit), so its `turn_hash` equals the fresh-genesis planned hash
/// [`planned_ci_run_hash`] re-derives at verification time.
pub fn run_ci_verdict(
    editor_seed: u8,
    region_seed: u8,
    signing_seed: [u8; 32],
    verdict: &CiVerdict,
) -> Result<TurnReceipt, TurnError> {
    let mut ci = ExecutorDrivenDoc::new(editor_seed, region_seed, /* holds cap */ true);
    ci.set_receipt_signing_key(signing_seed);
    ci.edit(ci_run_patch(verdict))
}

/// Re-derive the CI-run turn hash for `verdict` on a fresh genesis CI-run region
/// cell with identity `(editor_seed, region_seed)` — the pure binding surface
/// [`crate::check::RequiredCheck::satisfied_by`] compares to `receipt.turn_hash`.
/// `None` only if the verdict projects no delta (never, for a real verdict).
///
/// Turn construction is deterministic (agent, nonce 0, effects in the substrate
/// projection's `BTreeMap` order, no chain head, no wall clock), so this equals
/// the `turn_hash` [`run_ci_verdict`] commits for the same verdict + identity.
pub fn planned_ci_run_hash(
    editor_seed: u8,
    region_seed: u8,
    verdict: &CiVerdict,
) -> Option<[u8; 32]> {
    let ci = ExecutorDrivenDoc::new(editor_seed, region_seed, true);
    ci.planned_turn_hash(&ci_run_patch(verdict))
}

/// The anti-replay nullifier for `(pr base fold, verdict)`: a domain-tagged
/// digest of the PR's base-fold commitment and the verdict's canonical encoding.
/// Consumed at [`crate::PullRequest::land_checked`] so one signed verdict cannot
/// satisfy the check twice on the same base lineage.
pub fn ci_nullifier(base_fold_root: [u8; 32], verdict: &CiVerdict) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(NULLIFIER_DOMAIN);
    h.update(&base_fold_root);
    h.update(&verdict.encoding());
    *h.finalize().as_bytes()
}

/// The in-process consumed-nullifier set threaded through
/// [`crate::PullRequest::land_checked`]. Represents the forge's durable
/// nullifier store for one base lineage; a real cross-node deployment replaces
/// this with a committed accumulator (the durable seam — see the crate report).
#[derive(Clone, Debug, Default)]
pub struct CiNullifierSet {
    consumed: HashSet<[u8; 32]>,
}

impl CiNullifierSet {
    /// A fresh, empty consumed-set.
    pub fn new() -> Self {
        CiNullifierSet {
            consumed: HashSet::new(),
        }
    }

    /// Whether `nullifier` has already been consumed.
    pub fn contains(&self, nullifier: &[u8; 32]) -> bool {
        self.consumed.contains(nullifier)
    }

    /// Consume `nullifier`; returns `true` if it was newly consumed, `false` if
    /// it had already been consumed (a replay).
    pub fn consume(&mut self, nullifier: [u8; 32]) -> bool {
        self.consumed.insert(nullifier)
    }
}

/// Lowercase-hex encode (no dependency — the atom content just needs to be a
/// deterministic, injective UTF-8 string over the verdict bytes).
fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

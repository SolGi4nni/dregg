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

use crate::atom::{AtomId, Author};
use crate::executor_drive::ExecutorDrivenDoc;
use crate::patch::Patch;
use dregg_commit::merkle::{MerkleProof, MerkleTree, NonMembershipProof};
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

/// THE COMMITTED anti-replay accumulator for CI-run nullifiers — the durable
/// cross-node seam, closed.
///
/// Each consumed [`ci_nullifier`]`(base fold, verdict)` is a leaf of the
/// production sorted 4-ary Merkle accumulator ([`dregg_commit::MerkleTree`]):
///
/// - [`root`](Self::root) is the committed digest of the WHOLE consumed set —
///   the shareable state a federation commits so a replay is refused mesh-wide,
///   not merely within one process. It is a pure function of the leaf SET, so
///   two nodes that consumed the same nullifiers in ANY order commit the SAME
///   root (the cross-node-shareable property).
/// - [`contains`](Self::contains) is decided by the committed structure itself
///   (the sorted leaf map that defines the root), not a parallel side set.
/// - [`insert`](Self::insert) adds a leaf and advances the committed root.
///
/// A light client / another node that holds only `root()` verifies a nullifier
/// WAS consumed via [`membership_proof`](Self::membership_proof) (checked with
/// [`verify_membership`](Self::verify_membership)) or was NOT yet consumed via
/// [`non_membership_proof`](Self::non_membership_proof) (checked with
/// [`verify_non_membership`](Self::verify_non_membership)) — without holding the
/// whole set. The sorted-Merkle construction offers a genuine NON-membership
/// proof, so "this verdict was never consumed against this root" is client-
/// verifiable, not a named seam.
#[derive(Clone, Debug)]
pub struct CiNullifierAccumulator {
    tree: MerkleTree,
}

impl CiNullifierAccumulator {
    /// A fresh, empty committed accumulator (root = the canonical empty root).
    pub fn new() -> Self {
        CiNullifierAccumulator {
            tree: MerkleTree::new(),
        }
    }

    /// The committed root over the consumed-nullifier set — the cross-node
    /// shareable state. Deterministic in the leaf SET (order-independent).
    pub fn root(&self) -> [u8; 32] {
        self.tree.root_immutable()
    }

    /// Whether `nullifier` has already been consumed — decided by the committed
    /// tree's own leaf set (not a naive side lookup).
    pub fn contains(&self, nullifier: &[u8; 32]) -> bool {
        self.tree.contains_hash(nullifier)
    }

    /// Consume `nullifier`, advancing the committed root. Returns the new root.
    pub fn insert(&mut self, nullifier: [u8; 32]) -> [u8; 32] {
        self.tree.insert_hash(nullifier)
    }

    /// Number of consumed nullifiers.
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Whether no nullifier has been consumed yet.
    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    /// A membership proof a light client verifies against the shared
    /// [`root`](Self::root) to confirm a nullifier WAS consumed, without holding
    /// the whole set. `None` if the nullifier is not present.
    pub fn membership_proof(&self, nullifier: &[u8; 32]) -> Option<MerkleProof> {
        self.tree.membership_proof_hash(nullifier)
    }

    /// A non-membership proof a light client verifies against
    /// [`root`](Self::root) to confirm a nullifier was NOT yet consumed (so a
    /// fresh verdict can safely land). `None` if the nullifier IS present.
    pub fn non_membership_proof(&self, nullifier: &[u8; 32]) -> Option<NonMembershipProof> {
        self.tree.non_membership_proof_hash(nullifier)
    }

    /// Verify a membership proof against a (possibly shared) committed root.
    pub fn verify_membership(root: &[u8; 32], proof: &MerkleProof) -> bool {
        MerkleTree::verify_membership(root, proof)
    }

    /// Verify a non-membership proof against a (possibly shared) committed root.
    pub fn verify_non_membership(root: &[u8; 32], proof: &NonMembershipProof) -> bool {
        MerkleTree::verify_non_membership(root, proof)
    }
}

impl Default for CiNullifierAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

/// The consumed-nullifier store threaded through
/// [`crate::PullRequest::land_checked`]. Now backed by the COMMITTED
/// [`CiNullifierAccumulator`] (was an in-process `HashSet`): the CI-grade land
/// path rides a real shareable root, so a replayed verdict is refused against a
/// committed cross-node state, not merely within one process. The `contains` /
/// `consume` surface `land_checked` uses is unchanged — the migration is
/// transparent to callers, and [`root`](Self::root) exposes the shareable state.
#[derive(Clone, Debug, Default)]
pub struct CiNullifierSet {
    consumed: CiNullifierAccumulator,
}

impl CiNullifierSet {
    /// A fresh, empty consumed-set (an empty committed accumulator).
    pub fn new() -> Self {
        CiNullifierSet {
            consumed: CiNullifierAccumulator::new(),
        }
    }

    /// Whether `nullifier` has already been consumed (committed-structure check).
    pub fn contains(&self, nullifier: &[u8; 32]) -> bool {
        self.consumed.contains(nullifier)
    }

    /// Consume `nullifier`, advancing the committed root; returns `true` if it
    /// was newly consumed, `false` if it had already been consumed (a replay).
    pub fn consume(&mut self, nullifier: [u8; 32]) -> bool {
        let newly = !self.consumed.contains(&nullifier);
        self.consumed.insert(nullifier);
        newly
    }

    /// The committed root over the consumed nullifiers — the cross-node
    /// shareable state (see [`CiNullifierAccumulator`]).
    pub fn root(&self) -> [u8; 32] {
        self.consumed.root()
    }

    /// Borrow the underlying committed accumulator (for membership /
    /// non-membership proofs a light client verifies against [`root`](Self::root)).
    pub fn accumulator(&self) -> &CiNullifierAccumulator {
        &self.consumed
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

#[cfg(test)]
mod committed_nullifier_tests {
    //! THE COMMITTED anti-replay accumulator, four poles: a fresh nullifier
    //! lands and advances the root; a replay is refused with the root unchanged;
    //! two distinct verdicts give two distinct insertable nullifiers; and the
    //! committed root is deterministic in the leaf SET (the cross-node-shareable
    //! property). Plus a membership / non-membership proof round-trip, so a light
    //! client verifies "consumed" / "not consumed" against the shared root alone.
    use super::*;

    /// A verdict distinguished by `command_id` (every field is otherwise fixed);
    /// distinct `tag`s yield distinct canonical encodings, hence distinct nullifiers.
    fn verdict(tag: u8) -> CiVerdict {
        CiVerdict {
            input_root: [0x11; 32],
            command_id: [tag; 32],
            confinement_id: [0x33; 32],
            exit_code: 0,
            output_digest: [0x44; 32],
        }
    }

    const BASE: [u8; 32] = [0x55; 32];

    // POLE (i): a fresh verdict's nullifier — contains==false → insert → after,
    // contains==true and the committed root CHANGED.
    #[test]
    fn fresh_nullifier_lands_and_advances_root() {
        let mut acc = CiNullifierAccumulator::new();
        let nf = ci_nullifier(BASE, &verdict(1));

        assert!(!acc.contains(&nf), "a fresh nullifier is not consumed");
        let root_before = acc.root();

        acc.insert(nf);

        assert!(acc.contains(&nf), "after insert the nullifier is consumed");
        assert_ne!(root_before, acc.root(), "the committed root advanced");
    }

    // POLE (ii): replay the SAME verdict → contains==true → the `consume` path
    // reports it as a replay and the committed root is UNCHANGED by the re-insert.
    #[test]
    fn replay_is_refused_root_unchanged() {
        let mut set = CiNullifierSet::new();
        let nf = ci_nullifier(BASE, &verdict(1));

        assert!(set.consume(nf), "first consume is newly-consumed");
        let root_after_first = set.root();
        assert!(set.contains(&nf), "the nullifier is now consumed");

        // The replay: consume reports NOT-newly-consumed, root does not move.
        assert!(!set.consume(nf), "a replay is reported as already-consumed");
        assert_eq!(
            root_after_first,
            set.root(),
            "re-inserting an existing nullifier leaves the committed root fixed"
        );
    }

    // POLE (iii): two DIFFERENT verdicts → two distinct nullifiers, both
    // insertable, the root advances on EACH (no collision).
    #[test]
    fn two_distinct_verdicts_both_insertable() {
        let nf_a = ci_nullifier(BASE, &verdict(1));
        let nf_b = ci_nullifier(BASE, &verdict(2));
        assert_ne!(nf_a, nf_b, "distinct verdicts give distinct nullifiers");

        let mut acc = CiNullifierAccumulator::new();
        let r0 = acc.root();
        acc.insert(nf_a);
        let r1 = acc.root();
        acc.insert(nf_b);
        let r2 = acc.root();

        assert_ne!(r0, r1, "first insert advanced the root");
        assert_ne!(r1, r2, "second insert advanced the root again");
        assert!(
            acc.contains(&nf_a) && acc.contains(&nf_b),
            "both are consumed"
        );
        assert_eq!(acc.len(), 2, "no collision — two distinct leaves");
    }

    // POLE (iv): the committed root is deterministic — the SAME leaf set commits
    // the SAME root regardless of INSERT ORDER (the cross-node-shareable property:
    // two federation nodes that consumed the same nullifiers agree on the root).
    #[test]
    fn committed_root_is_order_independent() {
        let nf_a = ci_nullifier(BASE, &verdict(1));
        let nf_b = ci_nullifier(BASE, &verdict(2));

        let mut node1 = CiNullifierAccumulator::new();
        node1.insert(nf_a);
        node1.insert(nf_b);

        let mut node2 = CiNullifierAccumulator::new();
        node2.insert(nf_b); // reverse order
        node2.insert(nf_a);

        assert_eq!(
            node1.root(),
            node2.root(),
            "same consumed SET → same committed root, independent of order"
        );
    }

    // A light client holding ONLY the root verifies "consumed" (membership) and
    // "not consumed" (non-membership) without holding the whole set.
    #[test]
    fn client_verifies_membership_and_non_membership_against_root() {
        let mut acc = CiNullifierAccumulator::new();
        let consumed = ci_nullifier(BASE, &verdict(1));
        let fresh = ci_nullifier(BASE, &verdict(2));
        acc.insert(consumed);

        let root = acc.root();

        let mp = acc
            .membership_proof(&consumed)
            .expect("consumed → proof exists");
        assert!(
            CiNullifierAccumulator::verify_membership(&root, &mp),
            "membership proof verifies against the shared root"
        );

        let nmp = acc
            .non_membership_proof(&fresh)
            .expect("fresh → non-membership proof exists");
        assert!(
            CiNullifierAccumulator::verify_non_membership(&root, &nmp),
            "non-membership proof verifies against the shared root"
        );
        // A consumed nullifier has no non-membership proof; a fresh one has no
        // membership proof — the proofs are exclusive.
        assert!(acc.non_membership_proof(&consumed).is_none());
        assert!(acc.membership_proof(&fresh).is_none());
    }
}

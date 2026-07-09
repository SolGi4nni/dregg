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
//! same verdict presented again is refused. The consumed-set is [`CiNullifierSet`],
//! backed by the committed [`CiNullifierAccumulator`].
//!
//! ## Cross-node anti-replay (the last federation seam, closed)
//!
//! Refusing a replay within one process is not enough: a verdict already spent on
//! node A must be refused on node B too. The accumulator's
//! [`root`](CiNullifierAccumulator::root) is a shareable digest of the WHOLE consumed
//! set, so publishing it lets every node share the consumed-verdict set via the
//! ledger, not a private structure. The accumulator lives in a dedicated nullifier
//! CELL whose committed value IS that Merkle root; [`publish_nullifier_root`] is the
//! owner-signed WRITE to node's `/cells/update-commitment`, and
//! [`fetch_nullifier_root`] is the READ back out of a `GET /api/cell/{id}` response.
//! A node given only {fetched shared root, nullifier, membership proof} confirms
//! consumption with the static
//! [`verify_membership`](CiNullifierAccumulator::verify_membership) — refusing an
//! already-spent verdict WITHOUT holding the publisher's full accumulator. The
//! residual seam is the live HTTP transport only; the request, signature, and
//! shared-root verification are real.
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
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

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

// =============================================================================
// THE FEDERATION PUBLISH/FETCH HALF — the last thin cross-node anti-replay seam.
//
// `CiNullifierAccumulator::root()` is a shareable digest of the WHOLE consumed
// set, but nothing PUBLISHED it cross-node, so replay-refusal held only within one
// process. This section closes that: the accumulator lives in a dedicated nullifier
// CELL whose committed value IS its Merkle root. `publish_nullifier_root` produces
// the exact owner-signed body a node POSTs to node's `/cells/update-commitment` at
// each honest checkpoint (the WRITE); `fetch_nullifier_root` reads that root back
// out of a `GET /api/cell/{id}` response (the READ). With the root on the ledger,
// ANY node can check a verdict's `ci_nullifier` against the SHARED root using the
// static `verify_membership` / `verify_non_membership` proofs — so a replay is
// refused mesh-wide, not merely within the process that consumed it.
//
// The pattern MIRRORS `sandstorm-bridge/src/{grain,bridge}.rs` exactly (node is not
// a dregg-doc dependency, so the request/response types are FAITHFULLY MIRRORED, not
// imported; the live wire uses node's own structs, and a body built here
// deserializes into node's struct and passes its signature check unchanged).
// =============================================================================

/// A faithful mirror of node's `UpdateCommitmentRequest` (`node/src/api.rs`) — the
/// JSON body an owner POSTs to `/cells/update-commitment`. node is not a dependency
/// of this crate (it would be a heavy, cyclic dependency), so the type is MIRRORED,
/// not imported; the LIVE wire uses node's own struct. The mirror is field-for-field
/// identical (same JSON names, same hex encodings, same signed message), so a body
/// built here deserializes into node's struct and its signature passes node's
/// `post_update_commitment` check unchanged.
///
/// The signature signs `cell_id ‖ old_commitment ‖ new_commitment` (96 bytes),
/// verified with the `cell_id` bytes AS the ed25519 public key — node's
/// sovereign-cell convention (`verify_ed25519_signature(&cell_id_bytes, …)`). So a
/// nullifier cell whose root is published this way has `cell_id == owner_pubkey`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UpdateCommitmentRequest {
    /// Hex-encoded 32-byte cell id — doubles as the owner's ed25519 public key.
    pub cell_id: String,
    /// Hex-encoded 32-byte previously-committed root (node checks it matches stored).
    pub old_commitment: String,
    /// Hex-encoded 32-byte new committed root — the accumulator's Merkle root now.
    pub new_commitment: String,
    /// Hex-encoded 64-byte ed25519 signature over `cell_id ‖ old_commitment ‖ new_commitment`.
    pub signature: String,
}

/// **The WRITE half: publish the CI nullifier accumulator's committed root to the
/// federation ledger.** The consumed-nullifier set lives in a dedicated **nullifier
/// CELL** whose committed value IS the accumulator's Merkle root
/// ([`CiNullifierAccumulator::root`]). At each honest checkpoint the cell's owner
/// posts that root as the cell's new committed value, OWNER-SIGNED so a real node
/// accepts it. The returned [`UpdateCommitmentRequest`] is the exact body sent to
/// node's `/cells/update-commitment`; only the HTTP transport is out of a unit test.
///
/// `accumulator_cell_id` is the 32-byte sovereign nullifier-cell id, which under
/// node's convention IS the owner's ed25519 public key (the signature is verified
/// against it). `owner_key` must be the signing key for that public key
/// (`owner_key.verifying_key().to_bytes() == *accumulator_cell_id`) — or a real node
/// rejects the signature (the OWNER-SIGNED negative pole). `previous_root` is the
/// last-committed root the ledger stores (node checks `old_commitment` matches); use
/// [`CiNullifierAccumulator::new`]`().root()` (the canonical empty root) for the
/// genesis publish of a freshly-registered accumulator cell.
///
/// The published `new_commitment` is `acc.root()` — the real committed digest of the
/// whole consumed set — hex-encoded exactly as node returns commitments, so the value
/// another node later fetches with [`fetch_nullifier_root`] is byte-identical to the
/// root the accumulator's membership proofs fold to. That WRITE/READ consistency is
/// what closes the cross-node anti-replay seam.
pub fn publish_nullifier_root(
    accumulator_cell_id: &[u8; 32],
    acc: &CiNullifierAccumulator,
    owner_key: &SigningKey,
    previous_root: [u8; 32],
) -> UpdateCommitmentRequest {
    let new_commitment = acc.root();
    // Mirror node's signed message EXACTLY: cell_id ‖ old_commitment ‖ new_commitment.
    let mut message = Vec::with_capacity(96);
    message.extend_from_slice(accumulator_cell_id);
    message.extend_from_slice(&previous_root);
    message.extend_from_slice(&new_commitment);
    let signature = owner_key.sign(&message);
    UpdateCommitmentRequest {
        cell_id: hex_encode(accumulator_cell_id),
        old_commitment: hex_encode(&previous_root),
        new_commitment: hex_encode(&new_commitment),
        signature: hex_encode(&signature.to_bytes()),
    }
}

/// Mirror of node's `post_update_commitment` signature check: the signature must
/// sign `cell_id ‖ old_commitment ‖ new_commitment`, verified with the `cell_id`
/// bytes AS the ed25519 public key. Returns `true` iff a real node would ACCEPT the
/// request's signature. It does NOT run node's stateful `old_commitment`-matches-
/// stored ledger check (that is node-side state); it is the offline half a test uses
/// to assert node-acceptance without a running node. A wrong signing key, or a
/// mutated commitment under a genuine signature, fails here exactly as node's check.
pub fn verify_nullifier_update_signature(req: &UpdateCommitmentRequest) -> bool {
    let (Some(cell_id), Some(old_c), Some(new_c), Some(sig)) = (
        hex_decode(&req.cell_id),
        hex_decode(&req.old_commitment),
        hex_decode(&req.new_commitment),
        hex_decode(&req.signature),
    ) else {
        return false;
    };
    let (Ok(cell_id), Ok(sig)) = (
        <[u8; 32]>::try_from(cell_id.as_slice()),
        <[u8; 64]>::try_from(sig.as_slice()),
    ) else {
        return false;
    };
    if old_c.len() != 32 || new_c.len() != 32 {
        return false;
    }
    let Ok(vk) = VerifyingKey::from_bytes(&cell_id) else {
        return false;
    };
    let mut message = Vec::with_capacity(96);
    message.extend_from_slice(&cell_id);
    message.extend_from_slice(&old_c);
    message.extend_from_slice(&new_c);
    vk.verify(&message, &Signature::from_bytes(&sig)).is_ok()
}

/// A faithful mirror of the subset of node's `GET /api/cell/{id}` response body a
/// fetching node needs. Only the fields the READ path uses are modeled; serde
/// ignores the rest, so a real node's full response deserializes into it unchanged.
/// The LIVE wire uses node's own type; node is not a dependency of this crate.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CellDetailResponse {
    /// Whether the cell was found in the ledger.
    #[serde(default)]
    pub found: bool,
    /// The nullifier cell's committed root, hex-encoded — node's `state_commitment`
    /// field. For the nullifier cell this committed value IS the accumulator's
    /// Merkle root; a fetching node verifies membership / non-membership against it.
    #[serde(default)]
    pub state_commitment: String,
}

/// Why [`fetch_nullifier_root`] could not extract a committed root from a cell-detail
/// response.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NullifierFetchError {
    /// The response body was not valid `CellDetailResponse` JSON.
    Malformed,
    /// The cell was not found in the ledger (`found: false`).
    NotFound,
    /// The cell exists but carries no committed value yet.
    NoCommitment,
    /// The `state_commitment` field was not valid 32-byte hex.
    BadCommitmentHex,
}

impl std::fmt::Display for NullifierFetchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            NullifierFetchError::Malformed => "cell-detail response is not valid JSON",
            NullifierFetchError::NotFound => "nullifier cell not found in the federation ledger",
            NullifierFetchError::NoCommitment => "nullifier cell has no committed value yet",
            NullifierFetchError::BadCommitmentHex => "state_commitment is not valid 32-byte hex",
        })
    }
}

impl std::error::Error for NullifierFetchError {}

/// **The READ half: extract the shared nullifier-accumulator root a node verifies
/// consumption against, from a `GET /api/cell/{id}` response.** Parses the response
/// body (node's [`CellDetailResponse`]) and decodes its `state_commitment` hex field
/// to raw 32 bytes. This is the value the accumulator's owner published with
/// [`publish_nullifier_root`], so
/// `fetch_nullifier_root(response_after(publish_nullifier_root(.., R))) == R`: the
/// fetching node's independent root equals the root the accumulator's membership
/// proofs fold to. Feed the returned bytes as the `root` argument to
/// [`CiNullifierAccumulator::verify_membership`] /
/// [`CiNullifierAccumulator::verify_non_membership`] — so a node that holds NEITHER
/// the publisher's full accumulator NOR its process state can still refuse a replay
/// using only {ledger root, nullifier, proof}.
///
/// The root here is sourced from the FEDERATION response, never a peer's in-process
/// structure — that is what makes cross-node anti-replay real. (The residual seam is
/// the LIVE HTTP transport only: on a stock node `state_commitment` is the whole-cell
/// digest that absorbs this root; a deployment surfaces the nullifier cell's
/// committed value as this root directly — the SCHEME and hex wire already match what
/// [`publish_nullifier_root`] writes.)
pub fn fetch_nullifier_root(cell_detail_json: &str) -> Result<[u8; 32], NullifierFetchError> {
    let detail: CellDetailResponse =
        serde_json::from_str(cell_detail_json).map_err(|_| NullifierFetchError::Malformed)?;
    if !detail.found {
        return Err(NullifierFetchError::NotFound);
    }
    if detail.state_commitment.is_empty() {
        return Err(NullifierFetchError::NoCommitment);
    }
    let bytes =
        hex_decode(&detail.state_commitment).ok_or(NullifierFetchError::BadCommitmentHex)?;
    <[u8; 32]>::try_from(bytes.as_slice()).map_err(|_| NullifierFetchError::BadCommitmentHex)
}

/// Lowercase-hex decode (the inverse of [`hex_encode`]); `None` on any non-hex
/// character or an odd length. No dependency — mirrors the crate's own encoder.
fn hex_decode(s: &str) -> Option<Vec<u8>> {
    let bytes = s.as_bytes();
    if bytes.len() % 2 != 0 {
        return None;
    }
    let nibble = |c: u8| -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    };
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        out.push((nibble(pair[0])? << 4) | nibble(pair[1])?);
    }
    Some(out)
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

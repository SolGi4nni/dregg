//! One application-payload admission predicate — and one admission STAGING RUN —
//! for every `SignedTurn` ingress.
//!
//! Consensus authentication proves which validator carried a payload; it does
//! not authorize the payload's agent, so every ingress runs
//! [`validate_signed_turn`] before the turn can reach the authoritative ledger.
//!
//! # What each ingress actually does — MEASURED, not intended
//!
//! The previous version of this docblock said this module "prevents a new
//! transport from accidentally implementing a weaker subset", named three
//! transports, and claimed validation runs "before any ledger mutation". Every
//! one of those clauses was false at the time it was read (2026-08-06), and the
//! interesting falsehood was not weakness but STRICTNESS — see below. So this
//! block states the arrangement rather than an aspiration, and the arrangement is
//! now enforced by a shared function instead of by this paragraph.
//!
//! **The five production `validate_signed_turn` call sites**, and what surrounds
//! each:
//!
//! | site | what it is | staging run |
//! |---|---|---|
//! | `api::post_submit_turn` | `POST /turn/submit`, node-signed thin ingress | [`stage_signed_turn_admission`] |
//! | `api::submit_signed_turn` | `POST /turns/submit` + `POST /api/poa/signal/{a}/claims` | [`stage_signed_turn_admission`] |
//! | `api::post_faucet` | node-built faucet envelope | its own (pipelined-nonce delta, below) |
//! | `api::post_aggregate_bundle` | `POST /turns/aggregate` | none — proves, never executes |
//! | `blocklace_sync::execute_finalized_turn` | consensus finalization — THE AUTHORITY | its own (isolated clone) |
//! | `submit_queue_drainer::execute_submission` | pg `dregg.submit_queue`, `pg-mirror-live` ONLY | [`stage_signed_turn_admission`] |
//!
//! ⓘ `private_dependent_turns` calls the predicate twice more (arming, and
//! release) as READ-LOCK PRE-CHECKS. They mutate nothing and execute nothing;
//! they exist so a turn is not sealed into custody that the ingress which will
//! actually apply it would refuse. They deliberately use the pure
//! [`claimed_actor_cell`] rather than the mutating claim.
//!
//! ⓘ The drainer is `#![cfg(feature = "pg-mirror-live")]` and `node/Cargo.toml`
//! declares **no `default` feature at all**, so that transport does not exist in
//! a default build. Do not read its row as describing a shipped ingress.
//!
//! ⚠ **The predicate does NOT run before every ledger mutation, and the old
//! docblock's claim that it did was false.** [`claim_signer_actor_cell`] WRITES
//! to the live ledger and must run FIRST on the write-lock ingresses, because the
//! predicate resolves authority against the LIVE agent cell and a fresh or
//! faucet-stubbed client has none that binds its signer. Every such write is
//! inside an armed restore point, so it is O(touched)-reversible and a refused
//! turn leaves the ledger byte-identical — but "recoverable" is not "before any
//! mutation", and stating the stronger thing is how a reader stops checking.
//! Finalization is the one path that genuinely does not write first: it uses the
//! pure [`claimed_actor_cell`] and installs the result on an isolated clone,
//! because a claim in authoritative RAM that no commit record carries is an
//! attested-root split.
//!
//! ⓘ **The boundary of this module's guarantee.** It covers ingresses that STAGE
//! a `SignedTurn` and predict finalization's verdict. Three other places call
//! `executor_setup::execute_via_producer` on a `Turn` and are NOT covered:
//! `api::post_resolve_conditional` (a stored pending conditional, committed
//! locally), `mcp::handlers_act` (the operator's own MCP `act` surface), and
//! `exact_fnsp_v3_execution_authority`. None of them provisions Transfer
//! destinations either, so a conditional or MCP transfer to an unseen cell hits
//! the same executor refusal. They are a different question — they commit rather
//! than stage — and they are named here so this block is not read as covering
//! them.
//!
//! # ⚑ The split this module was reorganised to kill: STRICTER, not weaker
//!
//! `POST /turn/submit` and the pg drainer used to execute their staging run
//! against a ledger that had NOT had [`install_pre_execution_state`] applied —
//! specifically, without `blocklace_sync::provision_transfer_destinations`. A
//! `Transfer` to a destination cell nobody has seen yet is refused by the
//! executor as `transfer destination not found` (`turn/src/executor/apply.rs`),
//! so those two ingresses answered a TERMINAL REFUSAL for a turn that
//! `POST /turns/submit` accepts and that finalization commits — on the same node,
//! at the same instant, for byte-identical effects. The drainer wrote
//! `status='refused'` into `dregg.submit_queue` and never handed the envelope to
//! consensus at all.
//!
//! That is a LIVENESS SPLIT between transports on one chain, and it protected
//! nothing: finalization provisions unconditionally and is the sole authoritative
//! application, so the strict ingresses refused turns the chain then had no
//! objection to. The gate set that is correct is **finalization's**, because
//! finalization is the only run whose verdict is binding; a staging run exists to
//! PREDICT that verdict, and a prediction made against a ledger finalization will
//! never produce is not a stricter check, it is a wrong one.
//!
//! # How parity is held now
//!
//! [`stage_signed_turn_admission`] is the single staging run: claim → predicate →
//! receipt continuity → [`install_pre_execution_state`] → the one executor gate →
//! unconditional rollback. A transport does not get to choose the steps or their
//! order; it chooses only how to render the refusal. [`install_pre_execution_state`]
//! is the SAME function `execute_finalized_turn` calls on its isolated candidate
//! ledger, so "what the ledger must look like before this turn runs" has exactly
//! one definition and staging cannot drift from finalization.
//!
//! The two remaining deltas are deliberate and stated here rather than implied:
//!
//! * **the faucet** builds its own envelope and must reflect a PIPELINED nonce
//!   (`faucet_reserved_nonce`) inside the journal between provisioning and
//!   execution, so it keeps its own sequence. It runs the same predicate and the
//!   same provisioning; it skips the claim, which would be a no-op (the faucet
//!   cell is genesis-minted and already its signer's canonical account).
//! * **finalization** decides the claim with the pure [`claimed_actor_cell`]
//!   BEFORE validation and installs it on an isolated clone, because a finalized
//!   payload can clear this whole perimeter and still be refused afterwards; a
//!   claim written into authoritative RAM would then survive in RAM only and
//!   split the attested root. It applies ~15 further deterministic-rejection
//!   gates no ingress runs (the PoA Signal/galley classifiers, the
//!   faithful-note/nullifier suite, `exact-fnsp-v3-carrier-refused`). Those are
//!   refusals, and an ingress that skips them is merely optimistic: the turn is
//!   admitted, reaches consensus, and is deterministically rejected there. That
//!   direction costs a block, not safety.

use dregg_sdk::SignedTurn;
use dregg_turn::TurnExecutor;
use serde::{Deserialize, Serialize};

/// A strict wire-decoding failure for the outer application envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignedTurnDecodeError {
    Malformed(String),
    TrailingBytes { count: usize },
}

impl SignedTurnDecodeError {
    pub const fn code(&self) -> &'static str {
        match self {
            Self::Malformed(_) => "malformed-signed-turn",
            Self::TrailingBytes { .. } => "trailing-signed-turn-bytes",
        }
    }
}

impl core::fmt::Display for SignedTurnDecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Malformed(error) => write!(f, "malformed SignedTurn bytes: {error}"),
            Self::TrailingBytes { count } => {
                write!(f, "trailing bytes after SignedTurn envelope: {count}")
            }
        }
    }
}

impl std::error::Error for SignedTurnDecodeError {}

/// Decode exactly one `SignedTurn`, consuming the complete transport payload.
/// `postcard::from_bytes` currently accepts a valid prefix and ignores a suffix;
/// every mutation ingress uses this strict wrapper so no transport can disagree
/// about the signed envelope's canonical boundary.
pub fn decode_signed_turn(bytes: &[u8]) -> Result<SignedTurn, SignedTurnDecodeError> {
    let (signed, remainder) = postcard::take_from_bytes(bytes)
        .map_err(|error| SignedTurnDecodeError::Malformed(error.to_string()))?;
    if !remainder.is_empty() {
        return Err(SignedTurnDecodeError::TrailingBytes {
            count: remainder.len(),
        });
    }
    Ok(signed)
}

/// A stable, transport-independent reason a `SignedTurn` failed admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignedTurnValidationError {
    InvalidEd25519Signature,
    AgentSignerMismatch,
    PqSignatureRequired,
    IncompletePqEnvelope,
    PqIdentityNotEnrolled,
    EnrolledPqSignerMismatch,
    LiveAgentSignerMismatch,
    StalePqIdentityEpoch { enrolled: u64, live: u64 },
    SubstitutedPqPublicKey,
    InvalidPqSignature,
}

impl SignedTurnValidationError {
    /// Stable machine code used by durable finalized-payload rejection records.
    pub const fn code(&self) -> &'static str {
        match self {
            Self::InvalidEd25519Signature => "invalid-ed25519-signature",
            Self::AgentSignerMismatch => "agent-signer-mismatch",
            Self::PqSignatureRequired => "pq-signature-required",
            Self::IncompletePqEnvelope => "incomplete-pq-envelope",
            Self::PqIdentityNotEnrolled => "pq-identity-not-enrolled",
            Self::EnrolledPqSignerMismatch => "enrolled-pq-signer-mismatch",
            Self::LiveAgentSignerMismatch => "live-agent-signer-mismatch",
            Self::StalePqIdentityEpoch { .. } => "stale-pq-identity-epoch",
            Self::SubstitutedPqPublicKey => "substituted-pq-public-key",
            Self::InvalidPqSignature => "invalid-pq-signature",
        }
    }
}

impl core::fmt::Display for SignedTurnValidationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidEd25519Signature => f.write_str("invalid turn signature"),
            Self::AgentSignerMismatch => {
                f.write_str("turn agent does not match signer default cell")
            }
            Self::PqSignatureRequired => {
                f.write_str("post-quantum turn signature required but absent")
            }
            Self::IncompletePqEnvelope => {
                f.write_str("post-quantum turn signature and public key must both be present")
            }
            Self::PqIdentityNotEnrolled => {
                f.write_str(
                    "required post-quantum signer identity is neither Cell-committed nor independently enrolled for migration",
                )
            }
            Self::EnrolledPqSignerMismatch => {
                f.write_str("enrolled post-quantum identity does not bind the outer Ed25519 signer")
            }
            Self::LiveAgentSignerMismatch => {
                f.write_str("live agent identity does not bind the outer Ed25519 signer")
            }
            Self::StalePqIdentityEpoch { enrolled, live } => write!(
                f,
                "enrolled post-quantum identity epoch {enrolled} is stale for live agent epoch {live}"
            ),
            Self::SubstitutedPqPublicKey => f.write_str(
                "carried post-quantum signer does not match the canonical or migration identity",
            ),
            Self::InvalidPqSignature => f.write_str("invalid post-quantum turn signature"),
        }
    }
}

impl std::error::Error for SignedTurnValidationError {}

/// Result of complete validation.  Returning the already-computed hash keeps
/// every caller on the exact bytes both signature halves authenticated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedSignedTurn {
    turn_hash: [u8; 32],
}

impl ValidatedSignedTurn {
    /// The exact turn hash whose classical/PQ perimeter passed validation.
    pub const fn turn_hash(self) -> [u8; 32] {
        self.turn_hash
    }

    #[cfg(test)]
    pub(crate) const fn from_turn_hash_for_test(turn_hash: [u8; 32]) -> Self {
        Self { turn_hash }
    }
}

/// Validate the complete outer `SignedTurn` perimeter.
///
/// `live_agent` is independently loaded node state, never reconstructed from
/// the envelope. Required-PQ mode anchors the carried ML-DSA public key in that
/// Cell's persisted identity commitment and fails closed when the cell or anchor
/// is absent. Pre-v10 local/committee cells may use the independently configured
/// host registry as a migration bridge; it is never populated from this wire
/// envelope and never overrides a Cell-owned commitment.
pub fn validate_signed_turn(
    signed: &SignedTurn,
    executor: &TurnExecutor,
    live_agent: Option<&dregg_cell::Cell>,
) -> Result<ValidatedSignedTurn, SignedTurnValidationError> {
    let turn_hash = signed.turn.hash();
    if !signed.signer.verify(&turn_hash, &signed.signature) {
        return Err(SignedTurnValidationError::InvalidEd25519Signature);
    }

    let default_token_id = *blake3::hash(b"default").as_bytes();
    let expected_agent = dregg_cell::CellId::derive_raw(&signed.signer.0, &default_token_id);
    if signed.turn.agent != expected_agent {
        return Err(SignedTurnValidationError::AgentSignerMismatch);
    }

    let has_pq_signature = !signed.pq_signature.is_empty();
    let has_pq_public_key = !signed.pq_signer.is_empty();
    if has_pq_signature != has_pq_public_key {
        return Err(SignedTurnValidationError::IncompletePqEnvelope);
    }
    if !has_pq_signature {
        return if executor.require_pq() {
            Err(SignedTurnValidationError::PqSignatureRequired)
        } else {
            Ok(ValidatedSignedTurn { turn_hash })
        };
    }

    let legacy_enrolled = if live_agent.and_then(|cell| cell.pq_identity()).is_none() {
        executor.enrolled_pq_identity(&expected_agent)
    } else {
        None
    };
    let verification_key: &[u8] = if let Some(cell) = live_agent {
        if *cell.public_key() != signed.signer.0 {
            return Err(SignedTurnValidationError::LiveAgentSignerMismatch);
        }
        if let Some(identity) = cell.pq_identity() {
            let carried_commitment = dregg_cell::ml_dsa_public_key_commitment(&signed.pq_signer)
                .map_err(|_| SignedTurnValidationError::SubstitutedPqPublicKey)?;
            if carried_commitment != identity.ml_dsa_key_commitment {
                return Err(SignedTurnValidationError::SubstitutedPqPublicKey);
            }
            signed.pq_signer.as_slice()
        } else if let Some(enrolled) = legacy_enrolled.as_ref() {
            if enrolled.target_ed25519 != signed.signer.0 {
                return Err(SignedTurnValidationError::EnrolledPqSignerMismatch);
            }
            if enrolled.public_key.as_slice() != signed.pq_signer.as_slice() {
                return Err(SignedTurnValidationError::SubstitutedPqPublicKey);
            }
            enrolled.public_key.as_slice()
        } else {
            return Err(SignedTurnValidationError::PqIdentityNotEnrolled);
        }
    } else if executor.require_pq() {
        return Err(SignedTurnValidationError::PqIdentityNotEnrolled);
    } else {
        // Explicit unaudited compatibility only. A host registry may anchor an
        // old unbound fixture, but native required-PQ admission never reaches
        // this branch.
        if let Some(enrolled) = legacy_enrolled.as_ref() {
            if enrolled.target_ed25519 != signed.signer.0 {
                return Err(SignedTurnValidationError::EnrolledPqSignerMismatch);
            }
            if enrolled.public_key.as_slice() != signed.pq_signer.as_slice() {
                return Err(SignedTurnValidationError::SubstitutedPqPublicKey);
            }
            enrolled.public_key.as_slice()
        } else {
            signed.pq_signer.as_slice()
        }
    };

    if !dregg_turn::pq::ml_dsa_verify(verification_key, &turn_hash, &signed.pq_signature) {
        return Err(SignedTurnValidationError::InvalidPqSignature);
    }

    Ok(ValidatedSignedTurn { turn_hash })
}

/// What [`claim_signer_actor_cell`] did with the signer's own default cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ActorCellClaim {
    /// The cell did not exist and was materialized from the envelope's own
    /// proven identity material.
    Materialized,
    /// A zero-pk landing stub (a faucet grant to a cell nobody had seen) was
    /// upgraded in place to the canonical, identity-bound account. The stub's
    /// balance is carried over verbatim; nothing is minted.
    StubClaimed,
    /// The cell is already the signer's canonical account. Nothing to do — the
    /// hot path for every turn after the first.
    AlreadyOwned,
    /// Nothing was written. Either the envelope does not prove what a claim
    /// needs, or the id is held by someone else. [`validate_signed_turn`] then
    /// refuses the turn with its own specific reason, exactly as before.
    Declined,
}

/// THE FIRST-TURN CLAIM — materialize the signer's own default cell from the
/// identity material the envelope ITSELF proves, before the admission predicate
/// reads that cell.
///
/// # The bug this exists to close
///
/// [`validate_signed_turn`] resolves a turn's authority against the LIVE agent
/// cell. A fresh client has no such cell, and a faucet-funded one has a zero-pk
/// landing stub (`blocklace_sync::provision_transfer_destinations` mints the
/// destination from turn data alone, because the recipient's key is not carried
/// over consensus). So under the deployed required-PQ posture a first turn was
/// refused `pq-identity-not-enrolled` (no cell) or `live-agent-signer-mismatch`
/// (the stub) — on EVERY ingress, and at finalization — while the code that
/// would have fixed either ran strictly LATER, inside the execution clone. A new
/// person could receive coins and then do nothing, forever.
///
/// # Why this is not a weakening of the predicate
///
/// The predicate is untouched: it still refuses everything it refused before, on
/// the state it is handed. What changes is the STATE — and only for a cell id
/// whose owner this very envelope proves, with the same two possession proofs
/// `Effect::CreateHybridCell` demands of anyone else creating an identity-bound
/// cell:
///
/// * `signed.turn.agent == derive_raw(signer, blake3("default"))` — the agent id
///   is a COMMITMENT to the Ed25519 key; and
/// * `signer.verify(turn_hash, signature)` — possession of that Ed25519 key; and
/// * `ml_dsa_verify(pq_signer, turn_hash, pq_signature)` — possession of the
///   ML-DSA-65 key carried in the same envelope, over the same message.
///
/// So the claim writes exactly the account those proofs describe, and it writes
/// it ONLY where no one else has claimed the id:
///
/// * absent → materialize `with_hybrid_balance(signer, pq_signer, default, 0)`;
/// * zero-pk stub in the default asset → upgrade in place, carrying the stub's
///   balance verbatim (nothing minted, the id already commits to `signer`);
/// * anything else — a cell already bound to a DIFFERENT public key, or a stub
///   denominated in another asset — is left alone and the turn is refused.
///
/// # Cross-node uniformity
///
/// Every input is in-block and signature-verified (`SignedTurn.signer`,
/// `SignedTurn.pq_signer`, `turn.hash()`), so every node makes the identical
/// decision and writes the identical bytes. This matters more than the old
/// comments claimed: `dregg_persist::canonical_ledger_root` hashes
/// `postcard(cell)` — the WHOLE cell, public key and `pq_identity` included —
/// not just `cell.state`, so a divergent claim would show up in the attested
/// root rather than hiding under it.
///
/// # The residual, stated plainly
///
/// A cell id commits to the Ed25519 key alone, so the ML-DSA identity of a cell
/// that has never acted is established by its FIRST turn. Between a faucet grant
/// and that first turn, the grant is protected by Ed25519 only. Closing that
/// window needs the funding turn to carry the recipient's ML-DSA key (that is
/// what `Effect::CreateHybridCell` is for) — it is not closable by refusing the
/// first turn, which protects nothing and only freezes the coins.
pub fn claim_signer_actor_cell(
    ledger: &mut dregg_cell::Ledger,
    signed: &SignedTurn,
    require_pq: bool,
) -> ActorCellClaim {
    let existing = ledger.get(&signed.turn.agent);
    let existed = existing.is_some();
    let already_owned = existing.is_some_and(|cell| *cell.public_key() == signed.signer.0);
    let Some(claimed) = claimed_actor_cell(existing, signed, require_pq) else {
        return if already_owned {
            ActorCellClaim::AlreadyOwned
        } else {
            ActorCellClaim::Declined
        };
    };
    if existed {
        let _ = ledger.remove(&signed.turn.agent);
    }
    let _ = ledger.insert_cell(claimed);
    if existed {
        ActorCellClaim::StubClaimed
    } else {
        ActorCellClaim::Materialized
    }
}

/// The cell [`claim_signer_actor_cell`] would write, computed WITHOUT touching
/// the ledger — `None` when nothing changes (already the signer's account, or
/// the envelope does not prove a claim).
///
/// This exists so the admission pre-checks that hold only a READ lock
/// (`private_dependent_turns`) reach the same verdict as the write-lock
/// ingresses. An ingress that is stricter than finalization is how a first turn
/// ends up rejected in one place and accepted in another; there is ONE
/// implementation of the claim, and both shapes call it.
pub fn claimed_actor_cell(
    existing: Option<&dregg_cell::Cell>,
    signed: &SignedTurn,
    require_pq: bool,
) -> Option<dregg_cell::Cell> {
    let default_token_id = *blake3::hash(b"default").as_bytes();
    let actor_id = dregg_cell::CellId::derive_raw(&signed.signer.0, &default_token_id);
    // Never claim on behalf of a turn that is not acting as its signer's own
    // cell: `validate_signed_turn` refuses that as `agent-signer-mismatch`, and
    // fabricating foreign authority is precisely what must not happen here.
    if signed.turn.agent != actor_id {
        return None;
    }

    // Read the id's current occupant FIRST, so the overwhelmingly common case
    // (every turn after the first) costs one lookup and no cryptography.
    let carried_balance = match existing {
        // Already the signer's canonical account. Nothing to do.
        Some(cell) if *cell.public_key() == signed.signer.0 => return None,
        // Held by a different key. Not ours to claim.
        Some(cell) if *cell.public_key() != [0u8; 32] => return None,
        Some(stub) => {
            // A zero-pk landing stub. Claiming re-mints it under the signer's
            // key; re-denominating a balance while doing so would be exactly the
            // cross-asset teleport the executor now refuses, so a stub minted in
            // some other asset is left for a human to look at.
            if *stub.asset().as_bytes() != default_token_id {
                return None;
            }
            stub.state.balance()
        }
        None => 0,
    };

    // Possession of the Ed25519 key whose commitment IS this cell id.
    let turn_hash = signed.turn.hash();
    if !signed.signer.verify(&turn_hash, &signed.signature) {
        return None;
    }

    let has_pq_signature = !signed.pq_signature.is_empty();
    let has_pq_public_key = !signed.pq_signer.is_empty();
    if has_pq_signature != has_pq_public_key {
        return None;
    }

    if has_pq_signature {
        // Possession of the ML-DSA-65 key, over the same message. Only a key the
        // envelope proves possession of may be committed as this cell's anchor.
        if !dregg_turn::pq::ml_dsa_verify(&signed.pq_signer, &turn_hash, &signed.pq_signature) {
            return None;
        }
        // `Err` is a non-canonical ML-DSA key length, which
        // `validate_signed_turn` refuses as `substituted-pq-public-key`.
        dregg_cell::Cell::with_hybrid_balance(
            signed.signer.0,
            &signed.pq_signer,
            default_token_id,
            carried_balance,
        )
        .ok()
    } else if require_pq {
        // No PQ half at all under the deployed posture: the turn is refused
        // `pq-signature-required`, so materializing anything for it would be
        // state written for a rejected turn.
        None
    } else {
        // The explicitly unaudited classical test/development posture.
        Some(dregg_cell::Cell::with_balance(
            signed.signer.0,
            default_token_id,
            carried_balance,
        ))
    }
}

/// THE PRE-EXECUTION LEDGER SHAPE — the writes that must precede EVERY execution
/// of a `SignedTurn`, on every transport, stated once.
///
/// Two things, and the reason they are one function is that they were previously
/// three open-coded copies and two of them were missing the second half:
///
/// 1. **the first-turn claim**, when one was decided. `claimed_actor` is `Some`
///    only where finalization computed it purely and is installing it on its own
///    candidate ledger; the write-lock ingresses have already installed theirs via
///    [`claim_signer_actor_cell`] (which must run BEFORE the predicate reads the
///    cell) and pass `None`.
/// 2. **Transfer destination provisioning.** The executor refuses a `Transfer`
///    whose destination is absent (`TurnError::TransferDestNotFound`), and no node
///    holds the destination's pre-image, so every node materialises a zero-pk stub
///    at the destination id. ⚑ Deterministic in (turn, PRE-STATE), not in the turn
///    alone — the stub's ASSET is read from the Transfer's source cell in the local
///    ledger, because a Transfer is a single-asset move and the turn does not carry
///    the asset. See `blocklace_sync::provision_transfer_destinations` for why that
///    is enough for cross-node uniformity, and for the absent-source skip.
///    Finalization does this unconditionally; a staging run that omits it is not
///    predicting finalization's verdict, it is answering a different question about
///    a ledger that will never exist.
///
/// ⚠ Idempotent, and a pure function of (claimed actor, call forest, pre-state) in
/// both halves, which is what lets the same function serve an authoritative
/// isolated candidate and a rolled-back staging journal.
pub fn install_pre_execution_state(
    ledger: &mut dregg_cell::Ledger,
    claimed_actor: Option<dregg_cell::Cell>,
    call_forest: &dregg_turn::CallForest,
) {
    if let Some(claimed) = claimed_actor {
        let id = claimed.id();
        let _ = ledger.remove(&id);
        let _ = ledger.insert_cell(claimed);
    }
    crate::blocklace_sync::provision_transfer_destinations(ledger, call_forest);
}

/// Why [`stage_signed_turn_admission`] refused before it ever reached the
/// executor. The executor's own verdict is NOT one of these — it comes back in
/// [`StagedAdmission::outcome`], so each transport renders it in its own shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdmissionRefusal {
    /// The shared outer `SignedTurn` perimeter refused the envelope.
    Envelope(SignedTurnValidationError),
    /// The turn's `previous_receipt_hash` is not this agent's current causal
    /// head. Compared as complete `Option`s: `None` is valid only for an agent's
    /// genesis turn, never as an omitted-link reset.
    ReceiptChainMismatch,
}

impl core::fmt::Display for AdmissionRefusal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Envelope(error) => error.fmt(f),
            Self::ReceiptChainMismatch => f.write_str("receipt chain mismatch"),
        }
    }
}

/// A completed admission staging run. The ledger is ALREADY rolled back when
/// this is returned — consensus finalization is the sole authoritative
/// application at every committee size — so `pre_ledger` is the only view of the
/// cells the run touched.
#[derive(Debug)]
pub struct StagedAdmission {
    /// The exact turn hash whose classical/PQ perimeter passed.
    pub validated: ValidatedSignedTurn,
    /// What the one executor gate said. `Committed` means ADMITTED, not applied.
    pub outcome: dregg_turn::TurnResult,
    /// Prior images of exactly the cells the staging run touched, captured from
    /// the undo journal before it was rolled back.
    pub pre_ledger: dregg_cell::Ledger,
}

/// THE ONE ADMISSION STAGING RUN. Every mutating `SignedTurn` ingress calls
/// this and nothing else; the transport chooses how to render a refusal and
/// what to do with an admission, never which checks apply or in what order.
///
/// # Why this is a function and not a paragraph
///
/// The docblock this replaced claimed a shared choke point "prevents a new
/// transport from implementing a weaker subset". Nothing enforced it, and what
/// actually happened was the opposite failure: two ingresses became STRICTER
/// than consensus by omitting [`install_pre_execution_state`], and each returned
/// a terminal refusal for a `Transfer` the chain commits. A name is a claim; this
/// is the mechanism. A new transport that wants to admit a `SignedTurn` has one
/// door, and the steps behind it are not individually reachable in a way that
/// composes wrongly.
///
/// # The sequence, and why each step is where it is
///
/// 1. `begin_restore_point` FIRST, so a refused turn — and an admitted one,
///    which consensus applies authoritatively — leaves the ledger byte-identical.
/// 2. [`claim_signer_actor_cell`] BEFORE the predicate, because the predicate
///    resolves authority against the LIVE agent cell and a fresh or
///    faucet-stubbed client has none that binds its signer. This is an ordering
///    fix, not a weakening: the claim writes only the account this envelope's own
///    two possession proofs describe, and only where nobody else holds the id.
/// 3. [`validate_signed_turn`] under the SAME guard that protects the impending
///    mutation, so an identity rotation cannot race the check.
/// 4. Agent-scoped receipt continuity.
/// 5. [`install_pre_execution_state`] — the same one finalization applies.
/// 6. `execute_via_producer`, THE one executor gate (#171).
/// 7. Capture the journal's prior images, then roll back UNCONDITIONALLY.
///
/// ⚠ The rollback is unconditional in every arm and at every committee size.
/// This run decides admissibility and builds a response artifact; it is not an
/// application. Anything that reads `s.ledger` after this call is reading the
/// pre-turn ledger.
pub fn stage_signed_turn_admission(
    s: &mut crate::state::NodeStateInner,
    signed: &SignedTurn,
) -> Result<StagedAdmission, AdmissionRefusal> {
    let executor = crate::executor_setup::new_submit_executor(s);
    let lean_producer_enabled = s.lean_producer_enabled;

    s.ledger.begin_restore_point();
    claim_signer_actor_cell(&mut s.ledger, signed, executor.require_pq());

    let validated = match validate_signed_turn(signed, &executor, s.ledger.get(&signed.turn.agent))
    {
        Ok(validated) => validated,
        Err(error) => {
            s.ledger.rollback_restore_point();
            return Err(AdmissionRefusal::Envelope(error));
        }
    };

    if signed.turn.previous_receipt_hash != s.cclerk.agent_receipt_head_hash(&signed.turn.agent) {
        s.ledger.rollback_restore_point();
        return Err(AdmissionRefusal::ReceiptChainMismatch);
    }

    // The claim is already installed (step 2), so only the destinations remain.
    install_pre_execution_state(&mut s.ledger, None, &signed.turn.call_forest);
    let outcome = crate::executor_setup::execute_via_producer(
        &executor,
        &signed.turn,
        &mut s.ledger,
        lean_producer_enabled,
    );

    let pre_ledger = s.ledger.pre_turn_touched_ledger();
    s.ledger.rollback_restore_point();
    Ok(StagedAdmission {
        validated,
        outcome,
        pre_ledger,
    })
}

/// Versioned durable record for a consensus-finalized payload that the
/// application predicate refused.  It deliberately contains only deterministic
/// inputs/codes: no wall clock, local error formatting, or validator-local data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalizedPayloadRejectionRecord {
    pub version: u8,
    pub block_id: [u8; 32],
    pub payload_hash: [u8; 32],
    pub turn_hash: Option<[u8; 32]>,
    pub reason_code: String,
}

impl FinalizedPayloadRejectionRecord {
    pub const VERSION: u8 = 1;

    pub fn new(
        block_id: [u8; 32],
        payload: &[u8],
        turn_hash: Option<[u8; 32]>,
        reason_code: impl Into<String>,
    ) -> Self {
        Self {
            version: Self::VERSION,
            block_id,
            payload_hash: *blake3::hash(payload).as_bytes(),
            turn_hash,
            reason_code: reason_code.into(),
        }
    }

    pub fn storage_key(block_id: &[u8; 32]) -> String {
        format!(
            "finalized_payload_rejection:v1:{}",
            dregg_types::hex_encode(block_id)
        )
    }

    pub fn encode(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_stdvec(self)
    }

    /// Decode and authenticate one restart authority row against the immutable
    /// finalized block coordinate.  A config value under the right key is not
    /// sufficient: the version, embedded id, payload digest, and stable reason
    /// must all agree before recovery may suppress execution.
    pub fn decode_authenticated(
        bytes: &[u8],
        block_id: [u8; 32],
        payload: &[u8],
    ) -> Result<Self, &'static str> {
        let record: Self = postcard::from_bytes(bytes).map_err(|_| "malformed rejection row")?;
        if record.version != Self::VERSION {
            return Err("unsupported rejection row version");
        }
        if record.block_id != block_id {
            return Err("rejection row block id mismatch");
        }
        if record.payload_hash != *blake3::hash(payload).as_bytes() {
            return Err("rejection row payload digest mismatch");
        }
        if record.reason_code.is_empty() || record.reason_code.len() > 128 {
            return Err("rejection row reason code is not canonical");
        }
        if !record
            .reason_code
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
        {
            return Err("rejection row reason code is not canonical");
        }
        Ok(record)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::{CallForest, ComputronCosts, Turn};

    fn empty_turn(agent: dregg_cell::CellId) -> Turn {
        Turn {
            agent,
            nonce: 0,
            fee: 0,
            memo: None,
            valid_until: Some(i64::MAX / 2),
            call_forest: CallForest::new(),
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    fn signed_fixture(seed: [u8; 32]) -> (AgentCipherclerk, SignedTurn, dregg_cell::Cell) {
        let clerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(seed));
        let token = *blake3::hash(b"default").as_bytes();
        let pq = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&seed);
        let cell = dregg_cell::Cell::with_hybrid_balance(
            clerk.public_key().0,
            &pq.public_bytes(),
            token,
            1_000_000,
        )
        .expect("valid canonical ML-DSA key");
        let signed = clerk.sign_turn(&empty_turn(cell.id()));
        (clerk, signed, cell)
    }

    fn required_executor() -> TurnExecutor {
        let executor = TurnExecutor::new(ComputronCosts::default());
        executor.set_require_pq(true);
        executor
    }

    #[test]
    fn required_hybrid_accepts_the_cell_committed_outer_identity_without_registry() {
        let seed = [7; 32];
        let (_clerk, signed, cell) = signed_fixture(seed);
        let executor = required_executor();
        assert!(executor.enrolled_pq_identity(&cell.id()).is_none());
        assert!(validate_signed_turn(&signed, &executor, Some(&cell)).is_ok());
    }

    #[test]
    fn hostile_outer_pq_variants_fail_closed() {
        let seed = [8; 32];
        let (_clerk, signed, cell) = signed_fixture(seed);
        let executor = required_executor();

        let mut stripped = signed.clone();
        stripped.pq_signature.clear();
        stripped.pq_signer.clear();
        assert_eq!(
            validate_signed_turn(&stripped, &executor, Some(&cell)),
            Err(SignedTurnValidationError::PqSignatureRequired)
        );

        let mut invalid = signed.clone();
        invalid.pq_signature[0] ^= 0x80;
        assert_eq!(
            validate_signed_turn(&invalid, &executor, Some(&cell)),
            Err(SignedTurnValidationError::InvalidPqSignature)
        );

        let attacker = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&[91; 32]);
        let mut substituted = signed.clone();
        substituted.pq_signer = attacker.public_bytes();
        substituted.pq_signature = attacker
            .sign(&signed.turn.hash())
            .expect("attacker produces a valid signature under its own key");
        assert!(dregg_turn::pq::ml_dsa_verify(
            &substituted.pq_signer,
            &substituted.turn.hash(),
            &substituted.pq_signature
        ));
        assert_eq!(
            validate_signed_turn(&substituted, &executor, Some(&cell)),
            Err(SignedTurnValidationError::SubstitutedPqPublicKey)
        );
    }

    #[test]
    fn victim_agent_substitution_is_rejected_before_pq_and_has_stable_record() {
        let (_attacker, mut signed, _attacker_cell) = signed_fixture([9; 32]);
        let victim = dregg_cell::Cell::with_balance([0x55; 32], [0x66; 32], 99_000);
        let before_balance = victim.state.balance();
        let before_nonce = victim.state.nonce();
        signed.turn.agent = victim.id();
        signed.turn.fee = 50_000;
        signed.turn.nonce = before_nonce;

        // Re-sign after choosing the victim fields: the adversary owns both of
        // its own keys; only the signer→agent authority relation is false.
        let attacker = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([9; 32]));
        signed = attacker.sign_turn(&signed.turn);
        let executor = TurnExecutor::new(ComputronCosts::default());
        executor.set_require_pq(true);
        let err = validate_signed_turn(&signed, &executor, Some(&victim)).unwrap_err();
        assert_eq!(err, SignedTurnValidationError::AgentSignerMismatch);
        assert_eq!(victim.state.balance(), before_balance);
        assert_eq!(victim.state.nonce(), before_nonce);

        let block = [0xAB; 32];
        let bytes = postcard::to_stdvec(&signed).expect("encode hostile turn");
        let a = FinalizedPayloadRejectionRecord::new(
            block,
            &bytes,
            Some(signed.turn.hash()),
            err.code(),
        );
        let b = FinalizedPayloadRejectionRecord::new(
            block,
            &bytes,
            Some(signed.turn.hash()),
            err.code(),
        );
        assert_eq!(a.encode().unwrap(), b.encode().unwrap());
        assert_eq!(
            FinalizedPayloadRejectionRecord::storage_key(&block),
            format!("finalized_payload_rejection:v1:{}", "ab".repeat(32))
        );
    }

    /// A fresh client: an Ed25519 seed no node has ever seen, its own signed
    /// turn, and the default cell id that turn acts as.
    fn fresh_client(seed: [u8; 32]) -> (SignedTurn, dregg_cell::CellId) {
        let clerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(seed));
        let token = *blake3::hash(b"default").as_bytes();
        let actor = dregg_cell::CellId::derive_raw(&clerk.public_key().0, &token);
        (clerk.sign_turn(&empty_turn(actor)), actor)
    }

    /// The zero-pk landing stub `provision_transfer_destinations` mints for a
    /// faucet grant to a cell no node has seen — in the SOURCE's asset, which
    /// for the faucet is `blake3("default")`.
    fn faucet_landing_stub(actor: dregg_cell::CellId, balance: i64) -> dregg_cell::Cell {
        dregg_cell::Cell::remote_stub_with_id_pk_token_balance(
            actor,
            [0u8; 32],
            *blake3::hash(b"default").as_bytes(),
            balance,
        )
    }

    /// THE REGRESSION, at predicate resolution: with no cell and with the faucet
    /// stub, required-PQ admission refused a fresh client's FIRST turn — the two
    /// halves of "onboarding is dead one step past the faucet".
    #[test]
    fn a_first_turn_is_refused_without_the_claim() {
        let (signed, actor) = fresh_client([0xC1; 32]);
        let executor = required_executor();

        assert_eq!(
            validate_signed_turn(&signed, &executor, None),
            Err(SignedTurnValidationError::PqIdentityNotEnrolled),
            "a client that never touched the faucet has nowhere to enrol"
        );

        let stub = faucet_landing_stub(actor, 10_000);
        assert_eq!(
            validate_signed_turn(&signed, &executor, Some(&stub)),
            Err(SignedTurnValidationError::LiveAgentSignerMismatch),
            "and the cell the faucet leaves behind is not the cell the predicate wants"
        );
    }

    /// THE LAW the ingress ordering relies on: if the claim fires, validation
    /// passes. Nothing else may be needed between them, or an ingress that
    /// claims-then-validates could mutate state for a turn it then rejects.
    #[test]
    fn claiming_makes_the_first_turn_admissible_from_nothing_and_from_the_faucet_stub() {
        let executor = required_executor();

        // (a) never-seen client, no cell at all.
        let (signed, actor) = fresh_client([0xC2; 32]);
        let mut ledger = dregg_cell::Ledger::new();
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::Materialized
        );
        let claimed = ledger.get(&actor).expect("the actor cell now exists");
        assert_eq!(*claimed.public_key(), signed.signer.0);
        assert_eq!(claimed.state.balance(), 0);
        assert!(validate_signed_turn(&signed, &executor, Some(claimed)).is_ok());

        // (b) faucet-funded client: the stub is upgraded and the GRANT SURVIVES.
        let (signed, actor) = fresh_client([0xC3; 32]);
        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(faucet_landing_stub(actor, 10_000))
            .expect("insert the landing stub");
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::StubClaimed
        );
        let claimed = ledger.get(&actor).expect("the stub was claimed in place");
        assert_eq!(*claimed.public_key(), signed.signer.0);
        assert_eq!(
            claimed.state.balance(),
            10_000,
            "the claim carries the grant over verbatim — it must mint nothing and burn nothing"
        );
        assert!(validate_signed_turn(&signed, &executor, Some(claimed)).is_ok());

        // (c) the second turn is the hot path: nothing to do, no cryptography.
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::AlreadyOwned
        );
    }

    /// The claim is not a way in. Every one of these writes NOTHING, and the
    /// predicate still refuses the turn on its own terms.
    #[test]
    fn the_claim_refuses_every_envelope_that_does_not_prove_the_account() {
        let default_token = *blake3::hash(b"default").as_bytes();

        // A forged Ed25519 signature over an otherwise well-formed envelope.
        let (mut signed, actor) = fresh_client([0xC4; 32]);
        signed.signature.0[0] ^= 0x80;
        let mut ledger = dregg_cell::Ledger::new();
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::Declined
        );
        assert!(ledger.get(&actor).is_none(), "no cell for a bad signature");

        // A forged ML-DSA half: the Ed25519 half is genuine, so this is exactly
        // the classical-only adversary the deployed posture exists to refuse.
        let (mut signed, actor) = fresh_client([0xC5; 32]);
        signed.pq_signature[0] ^= 0x80;
        let mut ledger = dregg_cell::Ledger::new();
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::Declined
        );
        assert!(
            ledger.get(&actor).is_none(),
            "no cell without PQ possession"
        );

        // A substituted ML-DSA key the envelope does not hold: the carried
        // signature does not verify under it, so it can never be committed.
        let (mut signed, actor) = fresh_client([0xC6; 32]);
        signed.pq_signer =
            dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&[0x9E; 32]).public_bytes();
        let mut ledger = dregg_cell::Ledger::new();
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::Declined
        );
        assert!(ledger.get(&actor).is_none());

        // Someone else's funded account at the same id: NEVER re-keyed.
        let (signed, actor) = fresh_client([0xC7; 32]);
        let mut ledger = dregg_cell::Ledger::new();
        let victim = dregg_cell::Cell::remote_stub_with_id_pk_token_balance(
            actor,
            [0x5A; 32],
            default_token,
            99_000,
        );
        ledger.insert_cell(victim).expect("insert the victim cell");
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::Declined
        );
        let held = ledger.get(&actor).expect("victim still there");
        assert_eq!(*held.public_key(), [0x5A; 32]);
        assert_eq!(held.state.balance(), 99_000);

        // A stub in some OTHER asset: claiming it would re-denominate a balance,
        // which is the cross-asset teleport the executor refuses.
        let (signed, actor) = fresh_client([0xC8; 32]);
        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(dregg_cell::Cell::remote_stub_with_id_pk_token_balance(
                actor, [0u8; 32], [0x77; 32], 500,
            ))
            .expect("insert a foreign-asset stub");
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::Declined
        );
        assert_eq!(*ledger.get(&actor).unwrap().token_id(), [0x77; 32]);

        // A classical-only envelope under the deployed posture: refused, and no
        // cell is left behind for the rejected turn.
        let (mut signed, actor) = fresh_client([0xC9; 32]);
        signed.pq_signature.clear();
        signed.pq_signer.clear();
        let mut ledger = dregg_cell::Ledger::new();
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::Declined
        );
        assert!(ledger.get(&actor).is_none());
        // …and is materialized only in the explicitly unaudited classical mode.
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, false),
            ActorCellClaim::Materialized
        );
    }

    /// The agent-substitution tooth survives the claim: an adversary naming a
    /// victim cell as its agent gets no cell and no authority.
    #[test]
    fn the_claim_never_fabricates_authority_over_a_foreign_agent() {
        let clerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0xCA; 32]));
        let victim = dregg_cell::CellId([0x42; 32]);
        let signed = clerk.sign_turn(&empty_turn(victim));
        let mut ledger = dregg_cell::Ledger::new();
        assert_eq!(
            claim_signer_actor_cell(&mut ledger, &signed, true),
            ActorCellClaim::Declined
        );
        assert!(ledger.get(&victim).is_none());
        assert_eq!(
            ledger.len(),
            0,
            "not the victim's cell, and not the attacker's own either"
        );
    }

    #[test]
    fn strict_decoder_refuses_a_valid_signed_turn_prefix_with_trailing_bytes() {
        let (_clerk, signed, _cell) = signed_fixture([10; 32]);
        let canonical = postcard::to_stdvec(&signed).expect("encode SignedTurn");
        let decoded = decode_signed_turn(&canonical).expect("canonical envelope decodes");
        assert_eq!(decoded.turn.hash(), signed.turn.hash());
        assert_eq!(decoded.signer.0, signed.signer.0);
        assert_eq!(decoded.signature.0, signed.signature.0);
        assert_eq!(decoded.pq_signer, signed.pq_signer);
        assert_eq!(decoded.pq_signature, signed.pq_signature);

        let mut smuggled = canonical;
        smuggled.extend_from_slice(&[0x00, 0xA5]);
        assert!(matches!(
            decode_signed_turn(&smuggled),
            Err(SignedTurnDecodeError::TrailingBytes { count: 2 })
        ));
    }
}

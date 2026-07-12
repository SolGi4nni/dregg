//! # `bonded_slash` — evidence → adjudication → seized bond, on the bonded-operator cell
//!
//! The back half of the economic slash loop. [`crate::bonded_operator`] posts
//! the bond (the front half); the custody referee
//! ([`dregg_captp::custody::adjudicate_from_inbox`]) derives the verdict from
//! the inbox cell's own authenticated state; and the relay-operator cell
//! program ([`crate::relay_operator`]) enforces the slash transition shape
//! (`BoundedBy { bond, dispute }` + `FieldDelta { dispute, +1 }`,
//! default-deny elsewhere). This module WELDS them: a typed two-phase
//! **challenge → adjudicate** flow that, on a slash verdict, produces the
//! REAL slash [`Turn`] — the executor-enforced bond decrement plus a single
//! conserving [`Effect::Transfer`] of the seized amount to a named
//! beneficiary/escrow cell — and, on either verdict, a typed, Ed25519-signed
//! [`AdjudicationRecord`].
//!
//! ## The two-phase dispute route
//!
//! 1. **[`open_challenge`]** — the disputant posts the operator's own signed
//!    [`CustodyReceipt`] (wrapped in [`EvidenceOfDrop`]) against a specific
//!    bonded-operator cell. Admissibility is checked fail-closed (signature,
//!    deadline, operator↔cell binding, bond floor, fault freshness) and a
//!    bounded response window opens. **No value moves**: an open challenge is
//!    a typed object, not a seizure. The window is the operator's chance to
//!    land the delivery/refund witness on the inbox cell — the facts the
//!    referee reads are sticky, so an honest operator's acquittal cannot be
//!    front-run by racing the adjudication.
//! 2. **[`adjudicate`]** — at or after the window close, the referee runs
//!    against the inbox cell's authenticated state. Acquit ⇒ bond untouched,
//!    signed acquittal record. Slash ⇒ the slash turn (bond down by exactly
//!    the seizure, dispute counter +1, seizure Transferred to the
//!    beneficiary) plus a signed slash record, and the fault nullifier is
//!    consumed so the same fault can never be seized twice.
//!
//! A deployment that wants single-shot adjudication sets
//! `ChallengeConfig { response_window: 0 }` — the window closes at the raise
//! height.
//!
//! ## Fail-closed refusals (all typed, all value-inert)
//!
//! Every arm of [`SlashRefusal`] refuses BEFORE any effect is composed: no
//! turn is built, no nullifier is consumed (except by a completed
//! adjudication), nothing moves.
//!
//! - [`SlashRefusal::UnsignedEvidence`] — the receipt signature does not
//!   verify against the operator key it names (forged / tampered).
//! - [`SlashRefusal::PrematureEvidence`] — raised before `accept_by`; the
//!   operator has not defaulted yet.
//! - [`SlashRefusal::OperatorMismatch`] — the evidence convicts a DIFFERENT
//!   operator than the one pinned in the cell's `OPERATOR_PK_HASH_SLOT`; a
//!   conviction can never be re-pointed at an innocent operator's bond.
//! - [`SlashRefusal::BondBelowFloor`] — the cell's bond does not clear its
//!   own floor; the cell is not in a slashable state.
//! - [`SlashRefusal::SeizureExceedsHeadroom`] — the requested seizure would
//!   push the bond below `bond_min`. Refused typed (NOT silently capped);
//!   the caller re-requests within [`max_seizable`]. The nullifier survives
//!   this refusal, so a corrected retry is possible.
//! - [`SlashRefusal::FaultAlreadyAdjudicated`] — the content-addressed fault
//!   nullifier was already consumed: double-slash refused.
//! - [`SlashRefusal::ChallengeWindowStillOpen`] — adjudication attempted
//!   before the response window closed.
//!
//! ## Assurance ledger (which leg is enforced WHERE — load-bearing labels)
//!
//! Following the AssuranceRung style (KernelEnforced / VerifiedSettlement /
//! CommittedCell / HostArchive), stated per leg and never rounded up:
//!
//! - **The slash transition shape** (bond may only decrease while the
//!   dispute counter advances by exactly one; unknown methods default-deny;
//!   replaying the same slash turn refuses because `FieldDelta{dispute,+1}`
//!   no longer holds): **KernelEnforced** — the installed relay-operator
//!   [`dregg_cell::CellProgram`] is evaluated by the executor, which refuses
//!   and rolls back. Demonstrated by the hostile arms in this module's tests
//!   and in `relay_operator`/node intake tests.
//! - **The seizure Transfer** (Σδ = 0: the relay cell debits exactly what
//!   the beneficiary credits; missing destination or insufficient balance
//!   fails the turn): enforced by the substrate's settlement when the turn
//!   commits — **VerifiedSettlement** when the executing runtime routes
//!   through the verified Lean producer (`EmbeddedExecutor::set_lean_producer`
//!   / `DREGG_LEAN_PRODUCER`), executor-enforced (Rust `TurnExecutor`)
//!   otherwise. This module only COMPOSES the effect; it never applies value.
//! - **The referee's inputs** ([`InboxState`]): facts read off the inbox
//!   cell's authenticated state — **CommittedCell**-anchored; the verdict is
//!   a pure function of the operator's own Ed25519 signature and those
//!   facts. The referee itself is host-side code (crypto-sound, not
//!   kernel-enforced).
//! - **The challenge window, operator↔cell binding, floor/headroom gates,
//!   the fault-nullifier set, and the [`AdjudicationRecord`]**: host-library
//!   enforced, fail-closed — **HostArchive** rung. In particular the
//!   double-slash guard is a host-side sticky set ([`SlashNullifierSet`]);
//!   promoting it to KernelEnforced needs a fault-nullifier accumulator slot
//!   in the cell program (a VK-affecting change, deliberately out of scope
//!   here). What the kernel DOES enforce against double-seizure today is the
//!   turn-level tooth: an already-committed slash turn cannot be replayed
//!   (the dispute-counter delta refuses).

use std::collections::BTreeSet;

use dregg_app_framework::{AppCipherclerk, CellId, Effect, Turn};
use dregg_captp::custody::{
    CustodyOutcome, CustodyReceipt, EvidenceOfDrop, InboxState, adjudicate_from_inbox,
};
use dregg_types::{FederationId, PublicKey, Signature, SigningKey, sign};
use serde::{Deserialize, Serialize};

use crate::bonded_operator::BondedOperator;
use crate::relay_operator::build_slash_action;
use crate::u64_field;

// =============================================================================
// Domain tags
// =============================================================================

/// Domain-separation tag for the [`AdjudicationRecord`] signing preimage.
/// Bump on any wire-format change.
pub const ADJUDICATION_RECORD_DOMAIN: &[u8] = b"dregg-bonded-slash-adjudication-v1";

/// Domain-separation tag for the content-addressed fault nullifier.
pub const FAULT_NULLIFIER_DOMAIN: &[u8] = b"dregg-bonded-slash-fault-nullifier-v1";

/// Default response window (heights) between a challenge being raised and
/// adjudication becoming admissible.
pub const DEFAULT_RESPONSE_WINDOW: u64 = 100;

// =============================================================================
// Identity binding + fault addressing
// =============================================================================

/// The canonical `OPERATOR_PK_HASH_SLOT` value for an operator identity —
/// `blake3(operator_pubkey_bytes)`, the same derivation the node relay
/// service pins at registration (`relay_service.rs`:
/// `blake3_field(&config.operator_key)`). A bonded-operator cell whose slot 5
/// equals `operator_pk_hash_of(op)` is slashable exactly by evidence signed
/// by `op` — the binding [`open_challenge`] and [`adjudicate`] check.
pub fn operator_pk_hash_of(operator: &FederationId) -> [u8; 32] {
    *blake3::hash(&operator.0).as_bytes()
}

/// The content-addressed FAULT NULLIFIER: one adjudication per promised
/// custody fault. Binds the operator, the box, the inbox owner, and the
/// deadline — everything the operator's signature covers that identifies the
/// fault — so two convictions for the SAME broken promise collide, while a
/// different box (or a re-promise with a new deadline) is a fresh fault.
pub fn fault_nullifier(receipt: &CustodyReceipt) -> [u8; 32] {
    let mut msg = Vec::with_capacity(FAULT_NULLIFIER_DOMAIN.len() + 32 * 3 + 8);
    msg.extend_from_slice(FAULT_NULLIFIER_DOMAIN);
    msg.extend_from_slice(&receipt.relay.0);
    msg.extend_from_slice(&receipt.content_hash);
    msg.extend_from_slice(&receipt.inbox_owner.0);
    msg.extend_from_slice(&receipt.accept_by.to_le_bytes());
    *blake3::hash(&msg).as_bytes()
}

// =============================================================================
// Typed refusals
// =============================================================================

/// Why a challenge or adjudication was REFUSED. Every variant is fail-closed
/// and value-inert: no turn is composed, nothing is signed, and (except for a
/// completed adjudication) no nullifier is consumed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlashRefusal {
    /// The receipt's Ed25519 signature does not verify against the operator
    /// identity it names — forged, tampered, or wrong-key evidence binds
    /// nobody.
    UnsignedEvidence,
    /// The dispute was raised before the promise's deadline: non-delivery is
    /// still pending custody, not a fault.
    PrematureEvidence {
        /// The height the evidence was raised at.
        at_height: u64,
        /// The receipt's deadline; the challenge is admissible from here.
        accept_by: u64,
    },
    /// The evidence convicts a different operator than the one pinned in the
    /// target cell's `OPERATOR_PK_HASH_SLOT`.
    OperatorMismatch {
        /// The pk-hash pinned in the bonded-operator cell (slot 5).
        cell_operator_pk_hash: [u8; 32],
        /// `operator_pk_hash_of(receipt.relay)` — who the evidence convicts.
        evidence_operator_pk_hash: [u8; 32],
    },
    /// The cell's bond does not clear its own floor — not a slashable state.
    BondBelowFloor {
        /// The bond read off the cell.
        bond: u64,
        /// The floor the bond must clear.
        bond_min: u64,
    },
    /// The requested seizure exceeds the seizable headroom
    /// (`bond - bond_min`). Refused typed, never silently capped; the fault
    /// nullifier survives, so a corrected request can be retried.
    SeizureExceedsHeadroom {
        /// The seizure the caller requested.
        requested: u64,
        /// The maximum seizable right now ([`max_seizable`]).
        headroom: u64,
    },
    /// This fault (content-addressed by [`fault_nullifier`]) was already
    /// adjudicated — double-slash refused.
    FaultAlreadyAdjudicated {
        /// The consumed nullifier.
        nullifier: [u8; 32],
    },
    /// Adjudication attempted before the challenge's response window closed.
    ChallengeWindowStillOpen {
        /// The height adjudication was attempted at.
        at_height: u64,
        /// The height the window closes (adjudication admissible from here).
        window_ends: u64,
    },
}

impl core::fmt::Display for SlashRefusal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SlashRefusal::UnsignedEvidence => {
                write!(f, "evidence refused: receipt signature does not verify")
            }
            SlashRefusal::PrematureEvidence {
                at_height,
                accept_by,
            } => write!(
                f,
                "evidence refused: raised at height {at_height}, before the deadline {accept_by}"
            ),
            SlashRefusal::OperatorMismatch { .. } => write!(
                f,
                "challenge refused: evidence convicts a different operator than the cell pins"
            ),
            SlashRefusal::BondBelowFloor { bond, bond_min } => write!(
                f,
                "challenge refused: bond {bond} is below its floor {bond_min}"
            ),
            SlashRefusal::SeizureExceedsHeadroom {
                requested,
                headroom,
            } => write!(
                f,
                "seizure refused: requested {requested} exceeds seizable headroom {headroom}"
            ),
            SlashRefusal::FaultAlreadyAdjudicated { .. } => {
                write!(f, "refused: this fault was already adjudicated")
            }
            SlashRefusal::ChallengeWindowStillOpen {
                at_height,
                window_ends,
            } => write!(
                f,
                "adjudication refused at height {at_height}: response window open until {window_ends}"
            ),
        }
    }
}

impl std::error::Error for SlashRefusal {}

// =============================================================================
// Fault-nullifier set (double-slash guard; HostArchive rung — see module docs)
// =============================================================================

/// The sticky set of adjudicated fault nullifiers. Host-side state (see the
/// module-docs assurance ledger): a deployment persists it alongside its
/// adjudication records. Consumed by a COMPLETED adjudication (slash or
/// acquit — both derive from sticky cell facts, so both are final); typed
/// refusals never consume.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SlashNullifierSet {
    consumed: BTreeSet<[u8; 32]>,
}

impl SlashNullifierSet {
    /// An empty set — no fault adjudicated yet.
    pub fn new() -> Self {
        Self::default()
    }

    /// Has this fault already been adjudicated?
    pub fn is_consumed(&self, nullifier: &[u8; 32]) -> bool {
        self.consumed.contains(nullifier)
    }

    /// Consume a fault nullifier; refuses typed if already consumed.
    fn consume(&mut self, nullifier: [u8; 32]) -> Result<(), SlashRefusal> {
        if !self.consumed.insert(nullifier) {
            return Err(SlashRefusal::FaultAlreadyAdjudicated { nullifier });
        }
        Ok(())
    }

    /// Number of adjudicated faults.
    pub fn len(&self) -> usize {
        self.consumed.len()
    }

    /// True while no fault has been adjudicated.
    pub fn is_empty(&self) -> bool {
        self.consumed.is_empty()
    }
}

// =============================================================================
// Phase 1 — the typed challenge
// =============================================================================

/// Parameters of the challenge phase.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChallengeConfig {
    /// Heights between the raise and adjudication admissibility — the
    /// operator's bounded chance to land the delivery/refund witness on the
    /// inbox cell. `0` = single-shot (adjudicate at the raise height).
    pub response_window: u64,
}

impl Default for ChallengeConfig {
    fn default() -> Self {
        Self {
            response_window: DEFAULT_RESPONSE_WINDOW,
        }
    }
}

/// An admitted, still-undecided challenge: evidence bound to a specific
/// bonded-operator cell, with its response window. Value-inert — nothing is
/// seized until [`adjudicate`] runs after `window_ends`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenChallenge {
    /// The operator's own signed receipt + the disputant's claim + height.
    pub evidence: EvidenceOfDrop,
    /// The bonded-operator cell whose bond is at stake.
    pub relay_cell: CellId,
    /// The height the challenge was raised (`evidence.at_height`).
    pub raised_at: u64,
    /// Adjudication is admissible at or after this height.
    pub window_ends: u64,
    /// The content-addressed fault nullifier ([`fault_nullifier`]).
    pub nullifier: [u8; 32],
}

/// Read the bonded-operator lens off a live cell state (first 8 slots).
pub fn bonded_view_of_cell_state(state: &dregg_cell::state::CellState) -> BondedOperator {
    let mut slots = [[0u8; 32]; 8];
    slots.copy_from_slice(&state.fields[..8]);
    BondedOperator::from_state(slots)
}

/// The seizable headroom above the bond floor — the most a single
/// adjudication may seize without violating the floor.
pub fn max_seizable(view: &BondedOperator) -> u64 {
    view.bond_amount().saturating_sub(view.bond_min())
}

/// Phase 1: admit a challenge against a bonded-operator cell, fail-closed.
///
/// Checks, in order: the receipt signature ([`SlashRefusal::UnsignedEvidence`]),
/// the deadline ([`SlashRefusal::PrematureEvidence`]), the operator↔cell
/// binding ([`SlashRefusal::OperatorMismatch`]), the bond floor
/// ([`SlashRefusal::BondBelowFloor`]), and fault freshness
/// ([`SlashRefusal::FaultAlreadyAdjudicated`]). On success returns the typed
/// [`OpenChallenge`] with `window_ends = at_height + response_window`.
///
/// `operator_view` must be a FRESH read of the target cell
/// ([`bonded_view_of_cell_state`]); [`adjudicate`] re-checks every gate
/// against a fresh read anyway, so a stale open cannot smuggle a seizure.
pub fn open_challenge(
    evidence: EvidenceOfDrop,
    relay_cell: CellId,
    operator_view: &BondedOperator,
    config: &ChallengeConfig,
    nullifiers: &SlashNullifierSet,
) -> Result<OpenChallenge, SlashRefusal> {
    admissibility_gates(&evidence, operator_view, nullifiers)?;
    let raised_at = evidence.at_height;
    let nullifier = fault_nullifier(&evidence.receipt);
    Ok(OpenChallenge {
        window_ends: raised_at.saturating_add(config.response_window),
        evidence,
        relay_cell,
        raised_at,
        nullifier,
    })
}

/// The shared fail-closed admissibility gates (signature, deadline, operator
/// binding, bond floor, fault freshness). Run at open AND re-run at
/// adjudication against a fresh cell view.
fn admissibility_gates(
    evidence: &EvidenceOfDrop,
    operator_view: &BondedOperator,
    nullifiers: &SlashNullifierSet,
) -> Result<(), SlashRefusal> {
    // Gate 1 — binding: a receipt whose signature does not verify convicts
    // nobody (Ed25519 EUF-CMA; only the operator's key produces this).
    if !evidence.receipt.sig_verifies() {
        return Err(SlashRefusal::UnsignedEvidence);
    }
    // Gate 2 — deadline: before accept_by the operator has not defaulted.
    if evidence.at_height < evidence.receipt.accept_by {
        return Err(SlashRefusal::PrematureEvidence {
            at_height: evidence.at_height,
            accept_by: evidence.receipt.accept_by,
        });
    }
    // Gate 3 — operator↔cell binding: the convicted operator must be the one
    // pinned in the cell. Evidence against operator B never touches A's bond.
    let evidence_pk_hash = operator_pk_hash_of(&evidence.receipt.relay);
    let cell_pk_hash = operator_view.operator_pk_hash();
    if evidence_pk_hash != cell_pk_hash {
        return Err(SlashRefusal::OperatorMismatch {
            cell_operator_pk_hash: cell_pk_hash,
            evidence_operator_pk_hash: evidence_pk_hash,
        });
    }
    // Gate 4 — the bond must clear its own floor to be slashable at all.
    if !operator_view.bond_meets_floor() {
        return Err(SlashRefusal::BondBelowFloor {
            bond: operator_view.bond_amount(),
            bond_min: operator_view.bond_min(),
        });
    }
    // Gate 5 — fault freshness: one adjudication per fault.
    let nullifier = fault_nullifier(&evidence.receipt);
    if nullifiers.is_consumed(&nullifier) {
        return Err(SlashRefusal::FaultAlreadyAdjudicated { nullifier });
    }
    Ok(())
}

// =============================================================================
// Phase 2 — adjudication: the verdict, the record, and (on slash) the turn
// =============================================================================

/// How a slash verdict is settled: how much to seize and where the seized
/// bond goes. The seizure is a SINGLE conserving [`Effect::Transfer`] from
/// the operator cell to `beneficiary` — a deployment-chosen escrow /
/// restitution / treasury cell. (Splitting a seizure into restitution +
/// remainder legs is a payout-policy composition on top of this — see
/// `node::relay_dispute::SlashPayout` for the node's split.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SeizurePolicy {
    /// The exact seizure requested. Must be `<=` [`max_seizable`] at
    /// adjudication time, or the adjudication refuses typed
    /// ([`SlashRefusal::SeizureExceedsHeadroom`]). `0` records the fault
    /// (dispute counter still advances) without moving value.
    pub amount: u64,
    /// The escrow/beneficiary cell the seized bond is Transferred to. Must
    /// be a live cell on the executing ledger — the executor fails the turn
    /// closed otherwise.
    pub beneficiary: CellId,
}

/// Why an acquittal acquitted — derived from the inbox cell's sticky facts,
/// never from the disputant's claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AcquittalGrounds {
    /// The box's delivery is witnessed on the cell (sticky, content-addressed,
    /// overshoot/reorg-robust).
    Delivered,
    /// A refund was recorded before the deadline (the accept-OR-refund-by
    /// other half).
    Refunded,
}

/// The adjudicated verdict, as recorded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AdjudicationVerdict {
    /// The operator defaulted: the bond was seized.
    Slashed {
        /// Computrons seized from the bond (== the Transfer amount).
        seized_amount: u64,
        /// The escrow/beneficiary cell credited by the seizure.
        beneficiary: CellId,
        /// The bond after the slash (`bond - seized_amount`, `>= bond_min`).
        new_bond_amount: u64,
        /// The dispute counter after the slash (`+1`).
        new_dispute_count: u64,
    },
    /// The operator honored the promise: bond untouched.
    Acquitted {
        /// The sticky cell fact that acquitted.
        grounds: AcquittalGrounds,
    },
}

/// A typed, Ed25519-signed adjudication record — the durable artifact of one
/// fault's adjudication (HostArchive rung; the VALUE consequence is the
/// separately-committed turn). Self-describing: names the fault, the cell,
/// the operator, the verdict, and the adjudicator key that signed it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AdjudicationRecord {
    /// The fault's content-addressed nullifier ([`fault_nullifier`]).
    pub nullifier: [u8; 32],
    /// The bonded-operator cell adjudicated against.
    pub relay_cell: CellId,
    /// The convicted/acquitted operator (the receipt's signer).
    pub operator: FederationId,
    /// The dropped/contested box's content address.
    pub content_hash: [u8; 32],
    /// The inbox owner the box was held for.
    pub inbox_owner: FederationId,
    /// The verdict and its consequence.
    pub verdict: AdjudicationVerdict,
    /// The height the adjudication ran at.
    pub adjudicated_at: u64,
    /// The adjudicator's Ed25519 public key.
    pub adjudicator: PublicKey,
    /// The adjudicator's signature over [`Self::signing_preimage`].
    pub signature: Signature,
}

impl AdjudicationRecord {
    /// The canonical, domain-separated preimage the adjudicator signs.
    /// Covers every bound field, so no field can be swapped post-hoc.
    pub fn signing_preimage(
        nullifier: &[u8; 32],
        relay_cell: &CellId,
        operator: &FederationId,
        content_hash: &[u8; 32],
        inbox_owner: &FederationId,
        verdict: &AdjudicationVerdict,
        adjudicated_at: u64,
    ) -> Vec<u8> {
        let mut msg = Vec::with_capacity(ADJUDICATION_RECORD_DOMAIN.len() + 32 * 5 + 8 + 90);
        msg.extend_from_slice(ADJUDICATION_RECORD_DOMAIN);
        msg.extend_from_slice(nullifier);
        msg.extend_from_slice(&relay_cell.0);
        msg.extend_from_slice(&operator.0);
        msg.extend_from_slice(content_hash);
        msg.extend_from_slice(&inbox_owner.0);
        msg.extend_from_slice(&adjudicated_at.to_le_bytes());
        match verdict {
            AdjudicationVerdict::Slashed {
                seized_amount,
                beneficiary,
                new_bond_amount,
                new_dispute_count,
            } => {
                msg.push(0x01);
                msg.extend_from_slice(&seized_amount.to_le_bytes());
                msg.extend_from_slice(&beneficiary.0);
                msg.extend_from_slice(&new_bond_amount.to_le_bytes());
                msg.extend_from_slice(&new_dispute_count.to_le_bytes());
            }
            AdjudicationVerdict::Acquitted { grounds } => {
                msg.push(0x02);
                msg.push(match grounds {
                    AcquittalGrounds::Delivered => 0x01,
                    AcquittalGrounds::Refunded => 0x02,
                });
            }
        }
        msg
    }

    /// Sign a record over its canonical preimage.
    #[allow(clippy::too_many_arguments)]
    fn sign_new(
        adjudicator_key: &SigningKey,
        nullifier: [u8; 32],
        relay_cell: CellId,
        receipt: &CustodyReceipt,
        verdict: AdjudicationVerdict,
        adjudicated_at: u64,
    ) -> Self {
        let preimage = Self::signing_preimage(
            &nullifier,
            &relay_cell,
            &receipt.relay,
            &receipt.content_hash,
            &receipt.inbox_owner,
            &verdict,
            adjudicated_at,
        );
        let signature = sign(adjudicator_key, &preimage);
        Self {
            nullifier,
            relay_cell,
            operator: receipt.relay,
            content_hash: receipt.content_hash,
            inbox_owner: receipt.inbox_owner,
            verdict,
            adjudicated_at,
            adjudicator: adjudicator_key.public_key(),
            signature,
        }
    }

    /// Does the adjudicator's signature verify over this record's bound
    /// fields? Mutating any field invalidates it.
    pub fn verify(&self) -> bool {
        let preimage = Self::signing_preimage(
            &self.nullifier,
            &self.relay_cell,
            &self.operator,
            &self.content_hash,
            &self.inbox_owner,
            &self.verdict,
            self.adjudicated_at,
        );
        self.adjudicator.verify(&preimage, &self.signature)
    }
}

/// The outcome of a completed adjudication.
#[derive(Debug)]
pub enum Adjudication {
    /// Conviction: the signed record plus the REAL slash [`Turn`] — the
    /// executor-enforced bond/dispute transition with the conserving seizure
    /// Transfer composed in. Submit it through the executing runtime
    /// (`EmbeddedExecutor::submit_turn` / the node's `/turns/submit`); the
    /// installed cell program and the settlement are the enforcement.
    Slashed {
        /// The signed adjudication record.
        record: AdjudicationRecord,
        /// The signed, unsubmitted slash turn (nonce set by the submitter).
        turn: Box<Turn>,
    },
    /// Acquittal: bond untouched, no turn — only the signed record.
    Acquitted {
        /// The signed adjudication record.
        record: AdjudicationRecord,
    },
}

impl Adjudication {
    /// The signed record, whichever way the verdict went.
    pub fn record(&self) -> &AdjudicationRecord {
        match self {
            Adjudication::Slashed { record, .. } | Adjudication::Acquitted { record } => record,
        }
    }
}

/// Phase 2: adjudicate an open challenge, fail-closed.
///
/// Refuses typed while the response window is open, then RE-RUNS every
/// admissibility gate against the FRESH `operator_view` (a stale or replayed
/// challenge cannot smuggle a seizure), then runs the real referee
/// ([`adjudicate_from_inbox`]) against the inbox cell's authenticated state:
///
/// - **acquit** ⇒ the fault nullifier is consumed (the acquitting facts are
///   sticky, so the adjudication is final) and a signed
///   [`AdjudicationVerdict::Acquitted`] record is returned. No turn; the
///   bond is untouched.
/// - **slash** ⇒ the requested seizure is checked against the live headroom
///   ([`SlashRefusal::SeizureExceedsHeadroom`] refuses typed, nullifier
///   intact), the nullifier is consumed, and the slash [`Turn`] is composed:
///   [`build_slash_action`]'s `SetField`s (bond `-= amount`, dispute `+= 1`)
///   + `EmitEvent`, plus one conserving [`Effect::Transfer`] of the seizure
///   to `policy.beneficiary`, signed by `cclerk` and wrapped in the
///   canonical single-action turn.
///
/// `inbox` must be the inbox cell's authenticated state AT OR AFTER
/// `window_ends` — reading it after the window is what gives the operator
/// its response chance.
#[allow(clippy::too_many_arguments)]
pub fn adjudicate(
    cclerk: &AppCipherclerk,
    adjudicator_key: &SigningKey,
    challenge: &OpenChallenge,
    inbox: &InboxState,
    operator_view: &BondedOperator,
    at_height: u64,
    policy: &SeizurePolicy,
    nullifiers: &mut SlashNullifierSet,
) -> Result<Adjudication, SlashRefusal> {
    // The window must have closed — the operator's response chance is real.
    if at_height < challenge.window_ends {
        return Err(SlashRefusal::ChallengeWindowStillOpen {
            at_height,
            window_ends: challenge.window_ends,
        });
    }
    // Re-run every gate against the FRESH cell view. A challenge struct is
    // just data; nothing it carries is trusted at settlement time.
    admissibility_gates(&challenge.evidence, operator_view, nullifiers)?;
    let nullifier = fault_nullifier(&challenge.evidence.receipt);
    let receipt = &challenge.evidence.receipt;

    // THE REFEREE — the verdict is derived from the inbox cell's own
    // authenticated state, never from the disputant's claim.
    if !adjudicate_from_inbox(&challenge.evidence, inbox) {
        // Acquit. Gates 1+2 held above, so the true outcome is one of the
        // two honest fates; name which sticky fact acquitted.
        let grounds = match inbox.true_outcome(receipt) {
            CustodyOutcome::Delivered { .. } => AcquittalGrounds::Delivered,
            CustodyOutcome::Refunded => AcquittalGrounds::Refunded,
            // `adjudicate_from_inbox` == well_formed && Dropped, and the
            // gates above re-established well_formed — so an acquittal with
            // a Dropped true-outcome cannot occur (both are pure functions
            // of the same inputs). Loud, not a lying refusal type.
            CustodyOutcome::Dropped => unreachable!(
                "referee acquitted a well-formed dispute whose true outcome is Dropped"
            ),
        };
        nullifiers.consume(nullifier)?;
        let record = AdjudicationRecord::sign_new(
            adjudicator_key,
            nullifier,
            challenge.relay_cell,
            receipt,
            AdjudicationVerdict::Acquitted { grounds },
            at_height,
        );
        return Ok(Adjudication::Acquitted { record });
    }

    // Slash. The seizure must fit the LIVE headroom — refused typed (never
    // silently capped), and the nullifier survives so a corrected request
    // can retry.
    let headroom = max_seizable(operator_view);
    if policy.amount > headroom {
        return Err(SlashRefusal::SeizureExceedsHeadroom {
            requested: policy.amount,
            headroom,
        });
    }
    let new_bond_amount = operator_view.bond_amount() - policy.amount;
    let new_dispute_count = operator_view.dispute_count().saturating_add(1);

    // One adjudication per fault. Consumed BEFORE the turn is composed —
    // the fail-closed order: an interruption here leaves the fault locked
    // with no seizure turn in flight (safe), never a live seizure turn with
    // an unlocked fault (double-slash exposure).
    nullifiers.consume(nullifier)?;

    // The REAL transition: the relay-operator template's slash action
    // (SetField bond + SetField dispute + EmitEvent under the `slash`
    // method symbol — the shape the installed cell program enforces), plus
    // the single conserving seizure Transfer to the beneficiary.
    let mut action = build_slash_action(
        cclerk,
        challenge.relay_cell,
        u64_field(new_bond_amount),
        u64_field(new_dispute_count),
        receipt.content_hash, // the slash names the exact fault
    );
    if policy.amount > 0 {
        action.effects.push(Effect::Transfer {
            from: challenge.relay_cell,
            to: policy.beneficiary,
            amount: policy.amount,
        });
    }
    let turn = cclerk.make_turn(action);

    let verdict = AdjudicationVerdict::Slashed {
        seized_amount: policy.amount,
        beneficiary: policy.beneficiary,
        new_bond_amount,
        new_dispute_count,
    };
    let record = AdjudicationRecord::sign_new(
        adjudicator_key,
        nullifier,
        challenge.relay_cell,
        receipt,
        verdict,
        at_height,
    );
    Ok(Adjudication::Slashed {
        record,
        turn: Box::new(turn),
    })
}

// =============================================================================
// Tests — honest end-to-end, acquittal, and a hostile arm per refusal
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, EmbeddedExecutor};
    use dregg_cell::{AuthRequired, Cell, Permissions};
    use dregg_types::generate_keypair;

    use crate::bonded_operator::open_bonded_operator;
    use crate::relay_operator::{BOND_AMOUNT_SLOT, relay_operator_program};

    const BOND: u64 = 10_000;
    const FLOOR: u64 = 1_000;
    const DEADLINE: u64 = 500;
    const WINDOW: u64 = 10;

    fn operator_identity() -> (FederationId, SigningKey) {
        let (sk, pk) = generate_keypair();
        (FederationId(pk.0), sk)
    }

    fn adjudicator() -> SigningKey {
        generate_keypair().0
    }

    fn beneficiary_cell() -> CellId {
        CellId::from_bytes(*blake3::hash(b"bonded-slash-escrow").as_bytes())
    }

    fn receipt_for(operator: &FederationId, sk: &SigningKey, content: u8) -> CustodyReceipt {
        CustodyReceipt::sign(
            *operator,
            sk,
            [content; 32],            // content_hash
            FederationId([0x03; 32]), // inbox_owner
            [0x64; 32],               // old_root
            [0x8E; 32],               // new_root (promised)
            DEADLINE,
        )
    }

    fn dropped_inbox(receipt: &CustodyReceipt) -> InboxState {
        InboxState::from_dequeue(receipt, &[], [0x64; 32], false)
    }

    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    /// Boot an executor with a REAL bonded-operator cell: the bond posted
    /// through `open_bonded_operator` (the front half), the relay-operator
    /// `CellProgram` installed (the kernel-enforced slash shape), the
    /// operator identity pinned via `operator_pk_hash_of`, and a live
    /// beneficiary escrow cell for the seizure Transfer.
    fn executor_with_bonded_operator(
        operator: &FederationId,
    ) -> (AppCipherclerk, EmbeddedExecutor, CellId) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x42u8; 32]);
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let agent_cell = cclerk.cell_id();

        // The FRONT HALF: post the bond through the bonded-operator opener.
        let bonded = open_bonded_operator(BOND, FLOOR, operator_pk_hash_of(operator))
            .expect("bond clears the floor and the key is pinned");

        // A dedicated relay cell (not the agent cell, so turn fees never
        // touch the balances this test asserts on), funded to back the bond.
        let token_id = *blake3::hash(b"default").as_bytes();
        let mut relay = Cell::with_balance([0x51u8; 32], token_id, 100_000);
        relay.permissions = open_permissions();
        let relay_id = relay.id();
        exec.ensure_cell(relay).expect("relay cell placed");
        exec.install_program(relay_id, relay_operator_program());

        exec.with_ledger_mut(|ledger| {
            let cell = ledger.get_mut(&relay_id).expect("relay cell exists");
            for (i, field) in bonded.initial_state().iter().enumerate() {
                cell.state.set_field(i, *field);
            }
            let agent = ledger.get_mut(&agent_cell).expect("agent cell exists");
            agent
                .capabilities
                .grant(relay_id, AuthRequired::None)
                .expect("grant relay access");
        });

        // The escrow/beneficiary must be a live cell on the executing ledger
        // (the executor fails the turn closed otherwise).
        exec.ensure_cell(Cell::remote_stub_with_id(beneficiary_cell()))
            .expect("escrow cell placed");

        (cclerk, exec, relay_id)
    }

    fn view_of(exec: &EmbeddedExecutor, cell: CellId) -> BondedOperator {
        bonded_view_of_cell_state(&exec.cell_state(cell).expect("cell state"))
    }

    fn balance_of(exec: &EmbeddedExecutor, cell: CellId) -> i64 {
        exec.cell_state(cell).map(|s| s.balance()).unwrap_or(0)
    }

    // ── The honest end-to-end loop ─────────────────────────────────────────

    #[test]
    fn honest_loop_bond_evidence_slash_conserved_seizure_beneficiary_credited() {
        let (operator, op_sk) = operator_identity();
        let (cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let adjudicator_key = adjudicator();
        let mut nullifiers = SlashNullifierSet::new();

        // The operator signed a custody promise and then dropped the box.
        let receipt = receipt_for(&operator, &op_sk, 0xAB);
        let evidence = EvidenceOfDrop::from_receipt(receipt.clone());

        // Phase 1 — the challenge opens at the deadline; nothing moves.
        let relay_balance_0 = balance_of(&exec, relay_id);
        let escrow_balance_0 = balance_of(&exec, beneficiary_cell());
        let challenge = open_challenge(
            evidence,
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig {
                response_window: WINDOW,
            },
            &nullifiers,
        )
        .expect("a well-formed drop challenge opens");
        assert_eq!(challenge.raised_at, DEADLINE);
        assert_eq!(challenge.window_ends, DEADLINE + WINDOW);
        assert_eq!(
            balance_of(&exec, relay_id),
            relay_balance_0,
            "open is value-inert"
        );

        // Adjudicating INSIDE the window refuses typed — the operator's
        // response chance is real.
        let early = adjudicate(
            &cclerk,
            &adjudicator_key,
            &challenge,
            &dropped_inbox(&receipt),
            &view_of(&exec, relay_id),
            DEADLINE + WINDOW - 1,
            &SeizurePolicy {
                amount: 500,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        );
        assert_eq!(
            early.unwrap_err(),
            SlashRefusal::ChallengeWindowStillOpen {
                at_height: DEADLINE + WINDOW - 1,
                window_ends: DEADLINE + WINDOW,
            }
        );
        assert!(nullifiers.is_empty(), "refusal consumed no nullifier");

        // Phase 2 — the window closed, the box is still neither delivered
        // nor refunded: slash.
        let adjudication = adjudicate(
            &cclerk,
            &adjudicator_key,
            &challenge,
            &dropped_inbox(&receipt),
            &view_of(&exec, relay_id),
            DEADLINE + WINDOW,
            &SeizurePolicy {
                amount: 500,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        )
        .expect("a genuine drop adjudicates to a slash");
        let Adjudication::Slashed { record, turn } = adjudication else {
            panic!("expected a slash");
        };

        // The record is typed, signed, and names the fault.
        assert!(record.verify(), "adjudicator signature verifies");
        assert_eq!(record.operator, operator);
        assert_eq!(record.content_hash, [0xAB; 32]);
        assert_eq!(record.relay_cell, relay_id);
        assert_eq!(
            record.verdict,
            AdjudicationVerdict::Slashed {
                seized_amount: 500,
                beneficiary: beneficiary_cell(),
                new_bond_amount: BOND - 500,
                new_dispute_count: 1,
            }
        );

        // THE WELD: the turn commits through the installed relay-operator
        // cell program in the real executor.
        let receipt_committed = exec
            .submit_turn(&turn)
            .expect("the slash turn commits through the installed cell program");
        assert_eq!(receipt_committed.action_count, 1);

        // The slots moved exactly as adjudicated.
        let view = view_of(&exec, relay_id);
        assert_eq!(view.bond_amount(), BOND - 500);
        assert_eq!(view.dispute_count(), 1);
        assert!(!view.is_in_good_standing());
        assert!(view.bond_meets_floor(), "the floor survives the seizure");

        // CONSERVED SEIZURE, asserted through the real settlement: the relay
        // cell debited exactly what the escrow credited — Σδ = 0 across the
        // pair; no hand-rolled balance map anywhere.
        let relay_balance_1 = balance_of(&exec, relay_id);
        let escrow_balance_1 = balance_of(&exec, beneficiary_cell());
        assert_eq!(relay_balance_1, relay_balance_0 - 500);
        assert_eq!(escrow_balance_1, escrow_balance_0 + 500);
        assert_eq!(
            relay_balance_1 + escrow_balance_1,
            relay_balance_0 + escrow_balance_0,
            "the seizure conserves"
        );

        // The fault is spent.
        assert!(nullifiers.is_consumed(&challenge.nullifier));
    }

    #[test]
    fn replayed_slash_turn_refused_by_the_cell_program() {
        // The kernel-enforced double-seizure tooth at the TURN level: the
        // same committed slash turn cannot land twice — after the first
        // commit the dispute counter is 1, and the replay's SetField(1)
        // yields FieldDelta 0 ≠ +1, which the installed program refuses.
        let (operator, op_sk) = operator_identity();
        let (cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let mut nullifiers = SlashNullifierSet::new();
        let receipt = receipt_for(&operator, &op_sk, 0xAB);
        let challenge = open_challenge(
            EvidenceOfDrop::from_receipt(receipt.clone()),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig { response_window: 0 },
            &nullifiers,
        )
        .unwrap();
        let Adjudication::Slashed { turn, .. } = adjudicate(
            &cclerk,
            &adjudicator(),
            &challenge,
            &dropped_inbox(&receipt),
            &view_of(&exec, relay_id),
            DEADLINE,
            &SeizurePolicy {
                amount: 500,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        )
        .unwrap() else {
            panic!("expected slash");
        };

        exec.submit_turn(&turn).expect("first commit");
        let escrow_after_first = balance_of(&exec, beneficiary_cell());
        assert!(
            exec.submit_turn(&turn).is_err(),
            "replaying the committed slash turn must be refused by the cell program"
        );
        assert_eq!(
            balance_of(&exec, beneficiary_cell()),
            escrow_after_first,
            "the refused replay moved nothing"
        );
        assert_eq!(view_of(&exec, relay_id).bond_amount(), BOND - 500);
    }

    // ── The acquit route ───────────────────────────────────────────────────

    #[test]
    fn delivered_box_acquits_bond_untouched() {
        let (operator, op_sk) = operator_identity();
        let (cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let mut nullifiers = SlashNullifierSet::new();
        let receipt = receipt_for(&operator, &op_sk, 0xAB);

        let challenge = open_challenge(
            EvidenceOfDrop::from_receipt(receipt.clone()),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig {
                response_window: WINDOW,
            },
            &nullifiers,
        )
        .expect("the challenge itself is admissible");

        // During the window the delivery witness lands on the inbox cell
        // (sticky, content-addressed — overshoot-robust: the live root has
        // grown PAST the promise and the acquittal still holds).
        let delivered =
            InboxState::from_dequeue(&receipt, &[receipt.content_hash], [0x99; 32], false);

        let relay_balance_0 = balance_of(&exec, relay_id);
        let adjudication = adjudicate(
            &cclerk,
            &adjudicator(),
            &challenge,
            &delivered,
            &view_of(&exec, relay_id),
            DEADLINE + WINDOW,
            &SeizurePolicy {
                amount: 500,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        )
        .expect("an honored promise adjudicates to an acquittal");
        let Adjudication::Acquitted { record } = adjudication else {
            panic!("expected acquittal");
        };
        assert!(record.verify());
        assert_eq!(
            record.verdict,
            AdjudicationVerdict::Acquitted {
                grounds: AcquittalGrounds::Delivered
            }
        );

        // Bond untouched, nothing moved, cell state identical.
        let view = view_of(&exec, relay_id);
        assert_eq!(view.bond_amount(), BOND);
        assert_eq!(view.dispute_count(), 0);
        assert!(view.is_in_good_standing());
        assert_eq!(balance_of(&exec, relay_id), relay_balance_0);
        assert_eq!(balance_of(&exec, beneficiary_cell()), 0);

        // The acquittal is FINAL (its grounds are sticky cell facts): the
        // same fault cannot be re-challenged into a slash later.
        assert!(nullifiers.is_consumed(&challenge.nullifier));
        let again = open_challenge(
            EvidenceOfDrop::from_receipt(receipt),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig::default(),
            &nullifiers,
        );
        assert!(matches!(
            again.unwrap_err(),
            SlashRefusal::FaultAlreadyAdjudicated { .. }
        ));
    }

    #[test]
    fn refunded_box_acquits_with_refund_grounds() {
        let (operator, op_sk) = operator_identity();
        let (cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let mut nullifiers = SlashNullifierSet::new();
        let receipt = receipt_for(&operator, &op_sk, 0xAB);
        let challenge = open_challenge(
            EvidenceOfDrop::from_receipt(receipt.clone()),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig { response_window: 0 },
            &nullifiers,
        )
        .unwrap();
        // Not delivered, but the refund bit is recorded on the cell.
        let refunded = InboxState::from_dequeue(&receipt, &[], [0x64; 32], true);
        let adjudication = adjudicate(
            &cclerk,
            &adjudicator(),
            &challenge,
            &refunded,
            &view_of(&exec, relay_id),
            DEADLINE,
            &SeizurePolicy {
                amount: 500,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        )
        .unwrap();
        assert_eq!(
            adjudication.record().verdict,
            AdjudicationVerdict::Acquitted {
                grounds: AcquittalGrounds::Refunded
            }
        );
        assert_eq!(view_of(&exec, relay_id).bond_amount(), BOND);
    }

    // ── Hostile arms: one per typed refusal, all value-inert ──────────────

    #[test]
    fn forged_evidence_refused_unsigned() {
        let (operator, op_sk) = operator_identity();
        let (_cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let nullifiers = SlashNullifierSet::new();

        // Tamper a bound field after signing — the signature no longer
        // verifies, so the evidence binds nobody.
        let mut forged = receipt_for(&operator, &op_sk, 0xAB);
        forged.content_hash = [0xEE; 32];
        let refused = open_challenge(
            EvidenceOfDrop::from_receipt(forged),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig::default(),
            &nullifiers,
        );
        assert_eq!(refused.unwrap_err(), SlashRefusal::UnsignedEvidence);

        // Signed by an attacker key that is not the named operator.
        let (_att_id, attacker_sk) = operator_identity();
        let honest = receipt_for(&operator, &op_sk, 0xAB);
        let wrong_key = CustodyReceipt {
            signature: sign(
                &attacker_sk,
                &CustodyReceipt::signing_preimage(
                    &honest.relay,
                    &honest.content_hash,
                    &honest.inbox_owner,
                    &honest.old_root,
                    &honest.new_root,
                    honest.accept_by,
                ),
            ),
            ..honest
        };
        let refused = open_challenge(
            EvidenceOfDrop::from_receipt(wrong_key),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig::default(),
            &nullifiers,
        );
        assert_eq!(refused.unwrap_err(), SlashRefusal::UnsignedEvidence);
        assert_eq!(view_of(&exec, relay_id).bond_amount(), BOND, "value-inert");
    }

    #[test]
    fn premature_evidence_refused() {
        let (operator, op_sk) = operator_identity();
        let (_cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let nullifiers = SlashNullifierSet::new();
        let receipt = receipt_for(&operator, &op_sk, 0xAB);
        let mut evidence = EvidenceOfDrop::from_receipt(receipt);
        evidence.at_height = DEADLINE - 1;
        let refused = open_challenge(
            evidence,
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig::default(),
            &nullifiers,
        );
        assert_eq!(
            refused.unwrap_err(),
            SlashRefusal::PrematureEvidence {
                at_height: DEADLINE - 1,
                accept_by: DEADLINE,
            }
        );
    }

    #[test]
    fn evidence_against_a_different_operator_never_touches_this_bond() {
        // Operator A's cell; a perfectly VALID conviction of operator B.
        let (operator_a, _a_sk) = operator_identity();
        let (operator_b, b_sk) = operator_identity();
        let (cclerk, exec, relay_id) = executor_with_bonded_operator(&operator_a);
        let mut nullifiers = SlashNullifierSet::new();

        let receipt_b = receipt_for(&operator_b, &b_sk, 0xAB);
        assert!(receipt_b.sig_verifies(), "the conviction of B is genuine");

        let refused = open_challenge(
            EvidenceOfDrop::from_receipt(receipt_b.clone()),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig::default(),
            &nullifiers,
        );
        assert_eq!(
            refused.unwrap_err(),
            SlashRefusal::OperatorMismatch {
                cell_operator_pk_hash: operator_pk_hash_of(&operator_a),
                evidence_operator_pk_hash: operator_pk_hash_of(&operator_b),
            }
        );

        // Adjudication re-runs the gate too: a hand-forged challenge struct
        // (bypassing open_challenge) still refuses against the fresh view.
        let forged_challenge = OpenChallenge {
            evidence: EvidenceOfDrop::from_receipt(receipt_b.clone()),
            relay_cell: relay_id,
            raised_at: DEADLINE,
            window_ends: DEADLINE,
            nullifier: fault_nullifier(&receipt_b),
        };
        let refused = adjudicate(
            &cclerk,
            &adjudicator(),
            &forged_challenge,
            &dropped_inbox(&receipt_b),
            &view_of(&exec, relay_id),
            DEADLINE,
            &SeizurePolicy {
                amount: 500,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        );
        assert!(matches!(
            refused.unwrap_err(),
            SlashRefusal::OperatorMismatch { .. }
        ));
        assert_eq!(view_of(&exec, relay_id).bond_amount(), BOND, "value-inert");
        assert!(nullifiers.is_empty());
    }

    #[test]
    fn bond_below_floor_refused() {
        let (operator, op_sk) = operator_identity();
        let nullifiers = SlashNullifierSet::new();
        // A cell view whose bond fell below its own floor (not a state the
        // opener mints, but a hostile/degraded read must still refuse).
        let mut state = open_bonded_operator(BOND, FLOOR, operator_pk_hash_of(&operator))
            .unwrap()
            .initial_state();
        state[BOND_AMOUNT_SLOT as usize] = u64_field(FLOOR - 1);
        let broke_view = BondedOperator::from_state(state);

        let receipt = receipt_for(&operator, &op_sk, 0xAB);
        let refused = open_challenge(
            EvidenceOfDrop::from_receipt(receipt),
            CellId::from_bytes([0x11; 32]),
            &broke_view,
            &ChallengeConfig::default(),
            &nullifiers,
        );
        assert_eq!(
            refused.unwrap_err(),
            SlashRefusal::BondBelowFloor {
                bond: FLOOR - 1,
                bond_min: FLOOR,
            }
        );
    }

    #[test]
    fn seizure_exceeding_headroom_refused_typed_and_retryable() {
        let (operator, op_sk) = operator_identity();
        let (cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let mut nullifiers = SlashNullifierSet::new();
        let receipt = receipt_for(&operator, &op_sk, 0xAB);
        let challenge = open_challenge(
            EvidenceOfDrop::from_receipt(receipt.clone()),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig { response_window: 0 },
            &nullifiers,
        )
        .unwrap();

        // BOND - FLOOR = 9_000 is the headroom; ask for more — refused
        // typed, NOT silently capped, and the nullifier survives.
        let refused = adjudicate(
            &cclerk,
            &adjudicator(),
            &challenge,
            &dropped_inbox(&receipt),
            &view_of(&exec, relay_id),
            DEADLINE,
            &SeizurePolicy {
                amount: BOND - FLOOR + 1,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        );
        assert_eq!(
            refused.unwrap_err(),
            SlashRefusal::SeizureExceedsHeadroom {
                requested: BOND - FLOOR + 1,
                headroom: BOND - FLOOR,
            }
        );
        assert!(nullifiers.is_empty(), "the fault is still adjudicable");
        assert_eq!(view_of(&exec, relay_id).bond_amount(), BOND, "value-inert");

        // The corrected request (the full headroom) succeeds and lands the
        // bond exactly on its floor.
        let Adjudication::Slashed { turn, .. } = adjudicate(
            &cclerk,
            &adjudicator(),
            &challenge,
            &dropped_inbox(&receipt),
            &view_of(&exec, relay_id),
            DEADLINE,
            &SeizurePolicy {
                amount: BOND - FLOOR,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        )
        .unwrap() else {
            panic!("expected slash");
        };
        exec.submit_turn(&turn)
            .expect("floor-exact seizure commits");
        let view = view_of(&exec, relay_id);
        assert_eq!(view.bond_amount(), FLOOR, "bond lands exactly on the floor");
        assert_eq!(balance_of(&exec, beneficiary_cell()), (BOND - FLOOR) as i64);
    }

    #[test]
    fn double_slash_refused_by_the_fault_nullifier() {
        let (operator, op_sk) = operator_identity();
        let (cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let mut nullifiers = SlashNullifierSet::new();
        let receipt = receipt_for(&operator, &op_sk, 0xAB);
        let challenge = open_challenge(
            EvidenceOfDrop::from_receipt(receipt.clone()),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig { response_window: 0 },
            &nullifiers,
        )
        .unwrap();
        let policy = SeizurePolicy {
            amount: 500,
            beneficiary: beneficiary_cell(),
        };
        let Adjudication::Slashed { turn, .. } = adjudicate(
            &cclerk,
            &adjudicator(),
            &challenge,
            &dropped_inbox(&receipt),
            &view_of(&exec, relay_id),
            DEADLINE,
            &policy,
            &mut nullifiers,
        )
        .unwrap() else {
            panic!("expected slash");
        };
        exec.submit_turn(&turn).expect("first seizure commits");
        let escrow_after_first = balance_of(&exec, beneficiary_cell());

        // Re-raising the SAME fault refuses at the challenge gate…
        let refused = open_challenge(
            EvidenceOfDrop::from_receipt(receipt.clone()),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig { response_window: 0 },
            &nullifiers,
        );
        assert!(matches!(
            refused.unwrap_err(),
            SlashRefusal::FaultAlreadyAdjudicated { .. }
        ));

        // …and re-adjudicating the retained challenge struct refuses too.
        let refused = adjudicate(
            &cclerk,
            &adjudicator(),
            &challenge,
            &dropped_inbox(&receipt),
            &view_of(&exec, relay_id),
            DEADLINE,
            &policy,
            &mut nullifiers,
        );
        assert!(matches!(
            refused.unwrap_err(),
            SlashRefusal::FaultAlreadyAdjudicated { .. }
        ));
        assert_eq!(
            balance_of(&exec, beneficiary_cell()),
            escrow_after_first,
            "the double-slash moved nothing"
        );

        // A DIFFERENT fault by the same operator is fresh — the nullifier is
        // per-fault, not per-operator.
        let second_fault = receipt_for(&operator, &op_sk, 0xCD);
        assert!(
            open_challenge(
                EvidenceOfDrop::from_receipt(second_fault),
                relay_id,
                &view_of(&exec, relay_id),
                &ChallengeConfig { response_window: 0 },
                &nullifiers,
            )
            .is_ok(),
            "a distinct fault opens a fresh challenge"
        );
    }

    // ── Record integrity ───────────────────────────────────────────────────

    #[test]
    fn adjudication_record_signature_binds_every_field() {
        let (operator, op_sk) = operator_identity();
        let (cclerk, exec, relay_id) = executor_with_bonded_operator(&operator);
        let mut nullifiers = SlashNullifierSet::new();
        let receipt = receipt_for(&operator, &op_sk, 0xAB);
        let challenge = open_challenge(
            EvidenceOfDrop::from_receipt(receipt.clone()),
            relay_id,
            &view_of(&exec, relay_id),
            &ChallengeConfig { response_window: 0 },
            &nullifiers,
        )
        .unwrap();
        let Adjudication::Slashed { record, .. } = adjudicate(
            &cclerk,
            &adjudicator(),
            &challenge,
            &dropped_inbox(&receipt),
            &view_of(&exec, relay_id),
            DEADLINE,
            &SeizurePolicy {
                amount: 500,
                beneficiary: beneficiary_cell(),
            },
            &mut nullifiers,
        )
        .unwrap() else {
            panic!("expected slash");
        };
        assert!(record.verify());

        // Redirecting the seizure in the record invalidates the signature.
        let mut tampered = record.clone();
        tampered.verdict = AdjudicationVerdict::Slashed {
            seized_amount: 500,
            beneficiary: CellId::from_bytes([0x66; 32]),
            new_bond_amount: BOND - 500,
            new_dispute_count: 1,
        };
        assert!(
            !tampered.verify(),
            "a re-pointed beneficiary must not verify"
        );

        // Re-pointing the operator likewise.
        let mut tampered = record.clone();
        tampered.operator = FederationId([0x77; 32]);
        assert!(!tampered.verify(), "a re-pointed operator must not verify");

        // Inflating the seizure likewise.
        let mut tampered = record;
        tampered.verdict = AdjudicationVerdict::Slashed {
            seized_amount: 9_000,
            beneficiary: beneficiary_cell(),
            new_bond_amount: BOND - 500,
            new_dispute_count: 1,
        };
        assert!(!tampered.verify(), "an inflated seizure must not verify");
    }

    #[test]
    fn fault_nullifier_is_content_addressed() {
        let (operator, op_sk) = operator_identity();
        let r1 = receipt_for(&operator, &op_sk, 0xAB);
        let r1_again = receipt_for(&operator, &op_sk, 0xAB);
        let r2 = receipt_for(&operator, &op_sk, 0xCD);
        // Same fault ⇒ same nullifier (signature bytes are NOT part of the
        // address, so re-signing does not mint a fresh fault)…
        assert_eq!(fault_nullifier(&r1), fault_nullifier(&r1_again));
        // …different box ⇒ different fault.
        assert_ne!(fault_nullifier(&r1), fault_nullifier(&r2));
    }
}

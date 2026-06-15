//! # KERI-shaped identity event-log export (the ORGANS identity rider).
//!
//! The identity cell's key history, exported as an **externally verifiable
//! event log** — the KERI KEL shape over dregg's pre-rotation machinery
//! (`starbridge_polis::identity`, kernel semantics
//! `metatheory/Dregg2/Apps/PreRotation.lean`, wired in `2deda033c`):
//!
//! * **Chained** — each event commits the prior event's canonical digest
//!   (KERI `p`), so reordering / dropping / splicing breaks the chain.
//! * **Signed** — events carry the full [`TurnReceipt`] when the exporting
//!   operator authored the turn; the receipt's `executor_signature` is the
//!   Ed25519 attestation over the canonical v3 signed message
//!   ([`TurnReceipt::canonical_executor_signed_message`]).
//! * **Witness-receipted** — federation attestations ride along as DWR1
//!   artifacts ([`WitnessedReceipt::to_artifact_bytes`]), each re-decoded and
//!   re-bound to the event's `receipt_hash` by the verifier.
//! * **Pre-rotation-aware** — a rotation event's installed key-set
//!   commitment IS the exhibited preimage of the *previous* event's
//!   `next_keys_digest` register (`blake3(K) == prior n`, the
//!   `rotate_exhibits_preimage` shape), and the same event publishes the
//!   fresh next commitment — so an external verifier replays the whole key
//!   history from inception: `rotChain_pinned_by_commitments`'s deployed
//!   half.
//!
//! ## Where the history comes from
//!
//! The persisted commit log ([`dregg_persist`] `commit_log`) is the
//! authoritative, crash-consistent record of every finalized turn this node
//! applied; each [`CommitRecord`](dregg_persist::commit_log::CommitRecord)
//! carries post-state snapshots of every cell the turn touched. The
//! extractor walks the log, keeps the records that touched the identity
//! cell, and reads the five identity registers
//! (`starbridge_polis::identity` slots 0–4, re-exported through
//! `dregg_sdk::identity`) out of each snapshot. Receipts are joined back in
//! from the cipherclerk's receipt chain by `receipt_hash` (the receipt
//! index), and federation witness artifacts from the node's witnessed-
//! receipt store.
//!
//! ## The portable verifier
//!
//! [`verify_export`] needs **no node**: it takes the JSON artifact (plus an
//! out-of-band executor public key to pin signatures against, if you have
//! one) and re-derives everything — the digest chain, the inception shape,
//! every rotation's preimage link, key-state immutability outside
//! rotations, receipt-hash recomputation, executor signatures, and witness
//! artifact binding.
//!
//! ### Honest limits (what the artifact does NOT prove)
//!
//! * The binding "this post-state snapshot belongs to THIS turn's commit"
//!   rests on the exporting node's commit log; a stronger export would
//!   carry per-cell state-commitment openings against `ledger_root` (the
//!   anchors are already in the event for that upgrade).
//! * The cooling window is charter data (not in cell state), so the
//!   verifier checks the rotation *stamp* (`last_rotated_at == height`) but
//!   not the window length itself.
//! * Cleartext key MATERIAL never appears — KERI `k` is carried as the
//!   installed 32-byte key-set commitment (that is dregg's design: the
//!   ledger holds commitments, the gate checks the preimage relation).

use std::collections::HashMap;

use axum::Json;
use axum::extract::{Path as AxumPath, State};
use axum::http::StatusCode;
use serde::{Deserialize, Serialize};

use dregg_cell::CellId;
use dregg_cell::state::FieldElement;
use dregg_sdk::identity::{
    COUNCIL_COMMIT_SLOT, CURRENT_KEYS_COMMIT_SLOT, LAST_ROTATED_AT_SLOT, NEXT_KEYS_DIGEST_SLOT,
    STATE_ACTIVE, STATE_RETIRED, STATE_SLOT,
};
use dregg_turn::{TurnReceipt, WitnessedReceipt};

use crate::state::{NodeState, NodeStateInner};

/// Format tag carried in every export (reject-on-unknown for readers).
pub const KEL_FORMAT_VERSION: &str = "dregg-kel/1";

/// Domain string for the canonical per-event digest.
const EVENT_DIGEST_DOMAIN: &str = "dregg:identity-kel-event v1";

// =============================================================================
// The export format
// =============================================================================

/// Event kind, KERI-inspired (`icp` / `rot` / `ixn`, plus dregg's terminal
/// `rtd` — KERI has no retire verb; dregg's lifecycle does).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IdentityEventType {
    /// Inception (KERI `icp`): UNINIT → ACTIVE, both key registers
    /// installed in one turn, council commitment pinned. No preimage —
    /// nothing was committed yet.
    #[serde(rename = "icp")]
    Inception,
    /// Rotation (KERI `rot`): the installed commitment changed. The gate
    /// admitted it only by exhibiting the preimage of the prior
    /// `next_keys_digest` and re-committing fresh in the same turn.
    #[serde(rename = "rot")]
    Rotation,
    /// Interaction (KERI `ixn`): the cell was touched without moving the
    /// key state (factory birth, funding, reserved-slot churn, …).
    #[serde(rename = "ixn")]
    Interaction,
    /// Retirement (dregg `rtd`): ACTIVE → RETIRED, terminal and inert.
    #[serde(rename = "rtd")]
    Retirement,
}

impl IdentityEventType {
    /// Stable byte for the canonical digest encoding.
    fn digest_byte(self) -> u8 {
        match self {
            IdentityEventType::Inception => 1,
            IdentityEventType::Rotation => 2,
            IdentityEventType::Interaction => 3,
            IdentityEventType::Retirement => 4,
        }
    }
}

/// One key-state event. All 32-byte values are lowercase hex.
///
/// The canonical digest covers `seq`, the type byte, `prior_event_digest`,
/// the cell id, the full post-event key state, and the consensus anchors.
/// The attestation attachments (`receipt`, `witness_artifacts`) are NOT
/// digested — they attest *to* the event (each is independently re-bound to
/// `receipt_hash` by the verifier); attaching or shedding them must not
/// change the event's identity.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IdentityEvent {
    /// Dense position in this cell's event history (KERI `s`).
    pub seq: u64,
    /// KERI-inspired event kind (`icp` / `rot` / `ixn` / `rtd`).
    pub event_type: IdentityEventType,
    /// Canonical digest of the previous event (KERI `p`); `None` only at
    /// `seq == 0`.
    pub prior_event_digest: Option<String>,
    /// This event's canonical digest (recomputed by the verifier).
    pub event_digest: String,

    // ── post-event key state (the five identity registers) ──
    /// Lifecycle register (slot 0): 0 UNINIT / 1 ACTIVE / 2 RETIRED.
    pub lifecycle_state: u64,
    /// Installed key-set commitment (slot 2; KERI `k`, as its commitment).
    pub current_keys_commit: String,
    /// Pre-commitment to the NEXT, unexposed key set (slot 1; KERI `n`).
    pub next_keys_digest: String,
    /// Height of the last rotation (slot 3; the cooling anchor).
    pub last_rotated_at: u64,
    /// The pinned council membership commitment (slot 4).
    pub council_commit: String,
    /// Rotation only: the exhibited `Preimage32` — equal to
    /// `current_keys_commit`; `blake3(it)` must equal the PREVIOUS event's
    /// `next_keys_digest`. Carried explicitly for legibility.
    pub exhibited_preimage: Option<String>,

    // ── consensus anchors (from the commit log) ──
    /// Node-assigned commit height of the turn.
    pub height: u64,
    /// Commit-log ordinal (dense, gap-free applied order).
    pub ordinal: u64,
    /// Blocklace block id that carried the turn.
    pub block_id: String,
    /// The turn hash.
    pub turn_hash: String,
    /// The receipt hash produced by applying the turn.
    pub receipt_hash: String,
    /// Canonical ledger root AFTER the turn.
    pub ledger_root: String,

    // ── attestation attachments (not digested; re-bound by the verifier) ──
    /// Full receipt, when the exporting operator's chain holds it. The
    /// verifier recomputes `receipt_hash()` and checks the executor
    /// signature (canonical v3 message).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub receipt: Option<TurnReceipt>,
    /// Federation witness attestations, hex-encoded DWR1 artifacts
    /// ([`WitnessedReceipt::to_artifact_bytes`]).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub witness_artifacts: Vec<String>,
}

/// The exported identity event log — the portable artifact.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IdentityEventLog {
    /// [`KEL_FORMAT_VERSION`].
    pub format: String,
    /// The identity cell id (hex).
    pub cell: String,
    /// The exporting node's federation id (hex) — receipts bind it.
    pub federation_id: String,
    /// The exporting operator's Ed25519 public key (hex). Self-declared:
    /// pin it out-of-band and pass it to [`verify_export`] when you can.
    pub executor_public_key: String,
    /// The chained events, seq-ordered.
    pub events: Vec<IdentityEvent>,
}

// =============================================================================
// Canonical digest
// =============================================================================

/// The raw (decoded) form of one event's digested surface.
struct DigestSurface {
    cell: [u8; 32],
    seq: u64,
    type_byte: u8,
    prior: Option<[u8; 32]>,
    lifecycle_state: u64,
    current_keys_commit: [u8; 32],
    next_keys_digest: [u8; 32],
    last_rotated_at: u64,
    council_commit: [u8; 32],
    height: u64,
    ordinal: u64,
    block_id: [u8; 32],
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    ledger_root: [u8; 32],
}

impl DigestSurface {
    /// Canonical, domain-separated event digest. Fixed field order; the
    /// `Option` is tag-prefixed — there is exactly one byte string per
    /// logical event.
    fn digest(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key(EVENT_DIGEST_DOMAIN);
        h.update(&self.cell);
        h.update(&self.seq.to_be_bytes());
        h.update(&[self.type_byte]);
        match &self.prior {
            Some(p) => {
                h.update(&[1u8]);
                h.update(p);
            }
            None => {
                h.update(&[0u8]);
            }
        }
        h.update(&self.lifecycle_state.to_be_bytes());
        h.update(&self.current_keys_commit);
        h.update(&self.next_keys_digest);
        h.update(&self.last_rotated_at.to_be_bytes());
        h.update(&self.council_commit);
        h.update(&self.height.to_be_bytes());
        h.update(&self.ordinal.to_be_bytes());
        h.update(&self.block_id);
        h.update(&self.turn_hash);
        h.update(&self.receipt_hash);
        h.update(&self.ledger_root);
        *h.finalize().as_bytes()
    }
}

// =============================================================================
// Hex helpers (module-local; api.rs keeps its own private ones)
// =============================================================================

fn hex32(bytes: &[u8; 32]) -> String {
    hex_var(bytes)
}

fn hex_var(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

fn unhex32(s: &str) -> Result<[u8; 32], String> {
    let v = unhex_var(s)?;
    v.try_into()
        .map_err(|_| format!("expected 32 bytes of hex, got {}", s.len() / 2))
}

fn unhex_var(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("odd-length hex".into());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| format!("bad hex: {e}")))
        .collect()
}

/// Decode the u64 tail of a register written by `field_from_u64`
/// (big-endian in bytes 24..32 — the `inspect_identity` convention).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

const FIELD_ZERO: FieldElement = [0u8; 32];

// =============================================================================
// The extractor — commit log → event log
// =============================================================================

/// Why an export could not be produced.
#[derive(Debug)]
pub enum ExportError {
    /// The persistent store failed underneath us.
    Store(String),
    /// The commit log holds no turn touching this cell.
    NoHistory,
}

/// Consensus anchors for one event, lifted from a
/// [`CommitRecord`](dregg_persist::commit_log::CommitRecord).
#[derive(Clone, Copy, Debug)]
pub struct EventAnchor {
    pub height: u64,
    pub ordinal: u64,
    pub block_id: [u8; 32],
    pub turn_hash: [u8; 32],
    pub receipt_hash: [u8; 32],
    pub ledger_root: [u8; 32],
}

/// Decoded identity registers of one post-state snapshot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct KeyState {
    lifecycle_state: u64,
    current_keys_commit: FieldElement,
    next_keys_digest: FieldElement,
    last_rotated_at: u64,
    council_commit: FieldElement,
}

impl KeyState {
    fn from_fields(fields: &[FieldElement; 16]) -> Self {
        KeyState {
            lifecycle_state: field_to_u64(&fields[STATE_SLOT as usize]),
            current_keys_commit: fields[CURRENT_KEYS_COMMIT_SLOT as usize],
            next_keys_digest: fields[NEXT_KEYS_DIGEST_SLOT as usize],
            last_rotated_at: field_to_u64(&fields[LAST_ROTATED_AT_SLOT as usize]),
            council_commit: fields[COUNCIL_COMMIT_SLOT as usize],
        }
    }
}

/// Classify one snapshot transition. Mirrors the program's shape: the key
/// registers move ONLY at inception (zero → installed, UNINIT → ACTIVE)
/// and rotation (`KeyRotationGate`); everything else is an interaction,
/// except the terminal ACTIVE → RETIRED step.
fn classify(prev: Option<&KeyState>, ks: &KeyState) -> IdentityEventType {
    let prev_commit = prev.map(|p| p.current_keys_commit).unwrap_or(FIELD_ZERO);
    let prev_state = prev.map(|p| p.lifecycle_state).unwrap_or(0);
    if prev_commit == FIELD_ZERO
        && ks.current_keys_commit != FIELD_ZERO
        && ks.lifecycle_state == STATE_ACTIVE
    {
        IdentityEventType::Inception
    } else if ks.current_keys_commit != prev_commit {
        IdentityEventType::Rotation
    } else if ks.lifecycle_state == STATE_RETIRED && prev_state != STATE_RETIRED {
        IdentityEventType::Retirement
    } else {
        IdentityEventType::Interaction
    }
}

/// Build the chained event sequence from `(anchor, post-state fields)` rows
/// in commit order. Pure — the testable core of the extractor; receipts and
/// witness artifacts are joined in afterwards by [`extract_identity_log`].
pub fn events_from_snapshots(
    cell: &CellId,
    rows: &[(EventAnchor, [FieldElement; 16])],
) -> Vec<IdentityEvent> {
    let mut events = Vec::with_capacity(rows.len());
    let mut prev_ks: Option<KeyState> = None;
    let mut prior_digest: Option<[u8; 32]> = None;
    for (seq, (anchor, fields)) in rows.iter().enumerate() {
        let ks = KeyState::from_fields(fields);
        let event_type = classify(prev_ks.as_ref(), &ks);
        let surface = DigestSurface {
            cell: cell.0,
            seq: seq as u64,
            type_byte: event_type.digest_byte(),
            prior: prior_digest,
            lifecycle_state: ks.lifecycle_state,
            current_keys_commit: ks.current_keys_commit,
            next_keys_digest: ks.next_keys_digest,
            last_rotated_at: ks.last_rotated_at,
            council_commit: ks.council_commit,
            height: anchor.height,
            ordinal: anchor.ordinal,
            block_id: anchor.block_id,
            turn_hash: anchor.turn_hash,
            receipt_hash: anchor.receipt_hash,
            ledger_root: anchor.ledger_root,
        };
        let digest = surface.digest();
        events.push(IdentityEvent {
            seq: seq as u64,
            event_type,
            prior_event_digest: prior_digest.as_ref().map(|d| hex32(d)),
            event_digest: hex32(&digest),
            lifecycle_state: ks.lifecycle_state,
            current_keys_commit: hex32(&ks.current_keys_commit),
            next_keys_digest: hex32(&ks.next_keys_digest),
            last_rotated_at: ks.last_rotated_at,
            council_commit: hex32(&ks.council_commit),
            exhibited_preimage: (event_type == IdentityEventType::Rotation)
                .then(|| hex32(&ks.current_keys_commit)),
            height: anchor.height,
            ordinal: anchor.ordinal,
            block_id: hex32(&anchor.block_id),
            turn_hash: hex32(&anchor.turn_hash),
            receipt_hash: hex32(&anchor.receipt_hash),
            ledger_root: hex32(&anchor.ledger_root),
            receipt: None,
            witness_artifacts: Vec::new(),
        });
        prev_ks = Some(ks);
        prior_digest = Some(digest);
    }
    events
}

/// Walk the persisted commit log and assemble the cell's full event log,
/// joining in operator receipts (by `receipt_hash`, from the cipherclerk
/// chain) and federation witness artifacts (from the witnessed-receipt
/// store).
pub fn extract_identity_log(
    s: &NodeStateInner,
    cell: &CellId,
) -> Result<IdentityEventLog, ExportError> {
    let records = s
        .store
        .commit_records_from(0)
        .map_err(|e| ExportError::Store(format!("{e:?}")))?;

    let rows: Vec<(EventAnchor, [FieldElement; 16])> = records
        .iter()
        .filter_map(|r| {
            r.touched_cells.iter().find(|c| c.id() == *cell).map(|c| {
                (
                    EventAnchor {
                        height: r.height,
                        ordinal: r.ordinal,
                        block_id: r.block_id,
                        turn_hash: r.turn_hash,
                        receipt_hash: r.receipt_hash,
                        ledger_root: r.ledger_root,
                    },
                    c.state.fields,
                )
            })
        })
        .collect();
    if rows.is_empty() {
        return Err(ExportError::NoHistory);
    }

    let mut events = events_from_snapshots(cell, &rows);

    // The receipt index: join full receipts back in by hash.
    let receipts_by_hash: HashMap<[u8; 32], &TurnReceipt> = s
        .cclerk
        .receipt_chain()
        .iter()
        .map(|r| (r.receipt_hash(), r))
        .collect();
    for (ev, (anchor, _)) in events.iter_mut().zip(rows.iter()) {
        if let Some(r) = receipts_by_hash.get(&anchor.receipt_hash) {
            ev.receipt = Some((*r).clone());
        }
        if let Some(witnesses) = s.witnessed_receipts.get(&anchor.receipt_hash) {
            ev.witness_artifacts = witnesses
                .iter()
                .filter_map(|w| w.to_artifact_bytes().ok())
                .map(|bytes| hex_var(&bytes))
                .collect();
        }
    }

    Ok(IdentityEventLog {
        format: KEL_FORMAT_VERSION.to_string(),
        cell: hex32(&cell.0),
        federation_id: hex32(&s.federation_id),
        executor_public_key: hex32(&s.cclerk.public_key().0),
        events,
    })
}

// =============================================================================
// The portable verifier — no node required
// =============================================================================

/// One refusal. Every variant names the failing seq where applicable.
#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    UnknownFormat(String),
    Empty,
    BadHex {
        seq: u64,
        field: &'static str,
        detail: String,
    },
    BadField(String),
    SeqGap {
        expected: u64,
        got: u64,
    },
    /// Stated `event_digest` does not match the recomputed canonical digest.
    EventDigestMismatch {
        seq: u64,
    },
    /// `prior_event_digest` does not match the previous event's digest.
    ChainBroken {
        seq: u64,
    },
    /// Event 0 must carry no prior; later events must carry one.
    PriorPresenceWrong {
        seq: u64,
    },
    /// More than one inception, an inception after the first install, or a
    /// rotation before any inception.
    InceptionShape {
        seq: u64,
        detail: String,
    },
    /// `blake3(exhibited preimage)` does not equal the previous event's
    /// `next_keys_digest` — the rotation chain does not replay.
    RotationPreimage {
        seq: u64,
    },
    /// A rotation's structural fields are wrong (zero registers, stamp
    /// mismatch, missing/mismatched exhibited preimage).
    RotationShape {
        seq: u64,
        detail: String,
    },
    /// Key state (or the pinned council commitment) moved outside a
    /// rotation/inception event.
    KeyStateMoved {
        seq: u64,
        detail: String,
    },
    /// An event follows the terminal RETIRED state.
    AfterRetirement {
        seq: u64,
    },
    /// An attached receipt's recomputed `receipt_hash()` differs from the
    /// event's `receipt_hash`.
    ReceiptHashMismatch {
        seq: u64,
    },
    /// An attached receipt's executor signature failed Ed25519
    /// verification against the pinned key.
    BadExecutorSignature {
        seq: u64,
        detail: String,
    },
    /// A witness artifact failed to decode, or its embedded receipt is not
    /// bound to this event's `receipt_hash`.
    BadWitnessArtifact {
        seq: u64,
        detail: String,
    },
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

/// What the verifier checked (counts; all checks are mandatory where the
/// material is present — these report coverage, not pass/fail).
#[derive(Debug, Default, PartialEq, Eq)]
pub struct VerifyReport {
    pub events: usize,
    pub inceptions: usize,
    pub rotations: usize,
    pub receipts_checked: usize,
    pub signatures_checked: usize,
    pub witness_artifacts_checked: usize,
}

/// Decoded event surface + attachments, ready for checking.
struct DecodedEvent {
    surface: DigestSurface,
    stated_digest: [u8; 32],
    event_type: IdentityEventType,
    exhibited_preimage: Option<[u8; 32]>,
}

fn decode_event(cell: &[u8; 32], ev: &IdentityEvent) -> Result<DecodedEvent, VerifyError> {
    let seq = ev.seq;
    let bad = |field: &'static str, detail: String| VerifyError::BadHex { seq, field, detail };
    let prior = match &ev.prior_event_digest {
        Some(p) => Some(unhex32(p).map_err(|e| bad("prior_event_digest", e))?),
        None => None,
    };
    Ok(DecodedEvent {
        surface: DigestSurface {
            cell: *cell,
            seq,
            type_byte: ev.event_type.digest_byte(),
            prior,
            lifecycle_state: ev.lifecycle_state,
            current_keys_commit: unhex32(&ev.current_keys_commit)
                .map_err(|e| bad("current_keys_commit", e))?,
            next_keys_digest: unhex32(&ev.next_keys_digest)
                .map_err(|e| bad("next_keys_digest", e))?,
            last_rotated_at: ev.last_rotated_at,
            council_commit: unhex32(&ev.council_commit).map_err(|e| bad("council_commit", e))?,
            height: ev.height,
            ordinal: ev.ordinal,
            block_id: unhex32(&ev.block_id).map_err(|e| bad("block_id", e))?,
            turn_hash: unhex32(&ev.turn_hash).map_err(|e| bad("turn_hash", e))?,
            receipt_hash: unhex32(&ev.receipt_hash).map_err(|e| bad("receipt_hash", e))?,
            ledger_root: unhex32(&ev.ledger_root).map_err(|e| bad("ledger_root", e))?,
        },
        stated_digest: unhex32(&ev.event_digest).map_err(|e| bad("event_digest", e))?,
        event_type: ev.event_type,
        exhibited_preimage: match &ev.exhibited_preimage {
            Some(p) => Some(unhex32(p).map_err(|e| bad("exhibited_preimage", e))?),
            None => None,
        },
    })
}

/// Independently verify an exported identity event log. **No node needed**
/// — only the artifact (and, ideally, an out-of-band pinned executor
/// public key; pass `None` to fall back to the artifact's self-declared
/// key).
///
/// Refuses (fail-closed) on: format/hex malformation, seq gaps, any digest
/// chain break, inception-shape violations, any rotation whose exhibited
/// preimage does not hash to the prior pre-commitment, key state moving
/// outside rotation/inception, events after retirement, receipt-hash
/// mismatches, bad executor signatures, and unbound witness artifacts.
pub fn verify_export(
    log: &IdentityEventLog,
    pinned_executor_key: Option<&[u8; 32]>,
) -> Result<VerifyReport, VerifyError> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};

    if log.format != KEL_FORMAT_VERSION {
        return Err(VerifyError::UnknownFormat(log.format.clone()));
    }
    if log.events.is_empty() {
        return Err(VerifyError::Empty);
    }
    let cell = unhex32(&log.cell).map_err(|e| VerifyError::BadField(format!("cell: {e}")))?;
    let declared_key = unhex32(&log.executor_public_key)
        .map_err(|e| VerifyError::BadField(format!("executor_public_key: {e}")))?;
    let executor_key: [u8; 32] = pinned_executor_key.copied().unwrap_or(declared_key);
    let verifying_key = VerifyingKey::from_bytes(&executor_key).ok();

    let mut report = VerifyReport {
        events: log.events.len(),
        ..VerifyReport::default()
    };

    let mut prev: Option<DecodedEvent> = None;
    let mut incepted = false;
    let mut retired = false;

    for (i, ev) in log.events.iter().enumerate() {
        let expected_seq = i as u64;
        if ev.seq != expected_seq {
            return Err(VerifyError::SeqGap {
                expected: expected_seq,
                got: ev.seq,
            });
        }
        let dec = decode_event(&cell, ev)?;
        let seq = dec.surface.seq;

        // ── the digest chain ──
        if (seq == 0) != dec.surface.prior.is_none() {
            return Err(VerifyError::PriorPresenceWrong { seq });
        }
        if dec.surface.digest() != dec.stated_digest {
            return Err(VerifyError::EventDigestMismatch { seq });
        }
        if let Some(p) = &prev {
            if dec.surface.prior != Some(p.stated_digest) {
                return Err(VerifyError::ChainBroken { seq });
            }
        }

        // ── terminal retirement ──
        if retired {
            return Err(VerifyError::AfterRetirement { seq });
        }

        // ── per-type key-state rules ──
        match dec.event_type {
            IdentityEventType::Inception => {
                if incepted {
                    return Err(VerifyError::InceptionShape {
                        seq,
                        detail: "second inception".into(),
                    });
                }
                if dec.surface.lifecycle_state != STATE_ACTIVE
                    || dec.surface.current_keys_commit == FIELD_ZERO
                    || dec.surface.next_keys_digest == FIELD_ZERO
                {
                    return Err(VerifyError::InceptionShape {
                        seq,
                        detail: "inception must install both key registers and step to ACTIVE"
                            .into(),
                    });
                }
                incepted = true;
                report.inceptions += 1;
            }
            IdentityEventType::Rotation => {
                let Some(p) = &prev else {
                    return Err(VerifyError::InceptionShape {
                        seq,
                        detail: "rotation with no prior event".into(),
                    });
                };
                if !incepted {
                    return Err(VerifyError::InceptionShape {
                        seq,
                        detail: "rotation before inception".into(),
                    });
                }
                // Structural shape: nonzero registers, fresh re-commit,
                // the height stamp, the explicit exhibit.
                if dec.surface.current_keys_commit == FIELD_ZERO
                    || dec.surface.next_keys_digest == FIELD_ZERO
                {
                    return Err(VerifyError::RotationShape {
                        seq,
                        detail: "rotation nulled a key register".into(),
                    });
                }
                if dec.surface.last_rotated_at != dec.surface.height {
                    return Err(VerifyError::RotationShape {
                        seq,
                        detail: format!(
                            "rotation stamp {} != commit height {}",
                            dec.surface.last_rotated_at, dec.surface.height
                        ),
                    });
                }
                if dec.exhibited_preimage != Some(dec.surface.current_keys_commit) {
                    return Err(VerifyError::RotationShape {
                        seq,
                        detail: "exhibited preimage must equal the installed commitment".into(),
                    });
                }
                // THE TOOTH — the pre-rotation chain replays:
                // blake3(exhibited) == prior event's next_keys_digest
                // (`rotate_exhibits_preimage` / the gate's HashKind::Blake3).
                let digest_of_exhibit = *blake3::hash(&dec.surface.current_keys_commit).as_bytes();
                if digest_of_exhibit != p.surface.next_keys_digest {
                    return Err(VerifyError::RotationPreimage { seq });
                }
                report.rotations += 1;
            }
            IdentityEventType::Interaction | IdentityEventType::Retirement => {
                // Key state and the pinned council commitment must not move.
                if let Some(p) = &prev {
                    if dec.surface.current_keys_commit != p.surface.current_keys_commit
                        || dec.surface.next_keys_digest != p.surface.next_keys_digest
                    {
                        return Err(VerifyError::KeyStateMoved {
                            seq,
                            detail: "key registers moved outside a rotation/inception".into(),
                        });
                    }
                    if p.surface.council_commit != FIELD_ZERO
                        && dec.surface.council_commit != p.surface.council_commit
                    {
                        return Err(VerifyError::KeyStateMoved {
                            seq,
                            detail: "pinned council commitment moved".into(),
                        });
                    }
                }
            }
        }
        if dec.surface.lifecycle_state == STATE_RETIRED {
            retired = true;
        }

        // ── attached receipt: recompute the hash, check the signature ──
        if let Some(receipt) = &ev.receipt {
            if receipt.receipt_hash() != dec.surface.receipt_hash {
                return Err(VerifyError::ReceiptHashMismatch { seq });
            }
            report.receipts_checked += 1;
            if let Some(sig_bytes) = &receipt.executor_signature {
                let Some(vk) = &verifying_key else {
                    return Err(VerifyError::BadExecutorSignature {
                        seq,
                        detail: "invalid executor public key".into(),
                    });
                };
                let sig = Signature::from_slice(sig_bytes).map_err(|e| {
                    VerifyError::BadExecutorSignature {
                        seq,
                        detail: format!("malformed signature: {e}"),
                    }
                })?;
                vk.verify(&receipt.canonical_executor_signed_message(), &sig)
                    .map_err(|e| VerifyError::BadExecutorSignature {
                        seq,
                        detail: format!("signature did not verify: {e}"),
                    })?;
                report.signatures_checked += 1;
            }
        }

        // ── witness artifacts: decode + re-bind to this event's receipt ──
        for (wi, artifact_hex) in ev.witness_artifacts.iter().enumerate() {
            let bytes = unhex_var(artifact_hex).map_err(|e| VerifyError::BadWitnessArtifact {
                seq,
                detail: format!("artifact {wi}: {e}"),
            })?;
            let witnessed = WitnessedReceipt::from_artifact_bytes(&bytes).map_err(|e| {
                VerifyError::BadWitnessArtifact {
                    seq,
                    detail: format!("artifact {wi}: {e}"),
                }
            })?;
            if witnessed.receipt.receipt_hash() != dec.surface.receipt_hash {
                return Err(VerifyError::BadWitnessArtifact {
                    seq,
                    detail: format!("artifact {wi}: embedded receipt not bound to this event"),
                });
            }
            report.witness_artifacts_checked += 1;
        }

        prev = Some(dec);
    }

    Ok(report)
}

// =============================================================================
// The route — GET /identity/export/{cell}
// =============================================================================

/// `GET /identity/export/{cell}` — the cell's KERI-shaped key-event log as
/// a portable JSON artifact. 400 on a malformed cell id, 404 when the
/// commit log holds no history for the cell.
pub async fn get_identity_export(
    AxumPath(cell): AxumPath<String>,
    State(state): State<NodeState>,
) -> Result<Json<IdentityEventLog>, StatusCode> {
    let bytes = unhex32(cell.trim()).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = CellId(bytes);
    let s = state.read().await;
    match extract_identity_log(&s, &cell_id) {
        Ok(log) => Ok(Json(log)),
        Err(ExportError::NoHistory) => Err(StatusCode::NOT_FOUND),
        Err(ExportError::Store(e)) => {
            tracing::warn!("identity export store failure for {cell}: {e}");
            Err(StatusCode::INTERNAL_SERVER_ERROR)
        }
    }
}

// =============================================================================
// Tests — chain tamper refuses; the rotation preimage replays
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::field_from_u64;
    use ed25519_dalek::{Signer, SigningKey};

    const STATE_UNINIT_U64: u64 = 0;

    fn anchor(seq: u64, height: u64) -> EventAnchor {
        EventAnchor {
            height,
            ordinal: seq,
            block_id: *blake3::hash(format!("block-{seq}").as_bytes()).as_bytes(),
            turn_hash: *blake3::hash(format!("turn-{seq}").as_bytes()).as_bytes(),
            receipt_hash: *blake3::hash(format!("receipt-{seq}").as_bytes()).as_bytes(),
            ledger_root: *blake3::hash(format!("root-{seq}").as_bytes()).as_bytes(),
        }
    }

    fn fields(
        state: u64,
        next: FieldElement,
        cur: FieldElement,
        last_rot: u64,
        council: FieldElement,
    ) -> [FieldElement; 16] {
        let mut f = [[0u8; 32]; 16];
        f[STATE_SLOT as usize] = field_from_u64(state);
        f[NEXT_KEYS_DIGEST_SLOT as usize] = next;
        f[CURRENT_KEYS_COMMIT_SLOT as usize] = cur;
        f[LAST_ROTATED_AT_SLOT as usize] = field_from_u64(last_rot);
        f[COUNCIL_COMMIT_SLOT as usize] = council;
        f
    }

    /// Birth (ixn, zero registers) → inception → rotation → interaction.
    /// The rotation installs K1 whose blake3 was pre-committed at
    /// inception — the deployed `rotChain_pinned_by_commitments` shape.
    fn well_formed_log() -> (IdentityEventLog, CellId) {
        let cell = CellId([0xAA; 32]);
        let council = *blake3::hash(b"council").as_bytes();
        let k0 = *blake3::hash(b"keyset-0-commitment").as_bytes();
        let k1 = *blake3::hash(b"keyset-1-commitment").as_bytes();
        let k2 = *blake3::hash(b"keyset-2-commitment").as_bytes();
        let n1 = *blake3::hash(&k1).as_bytes(); // pre-commitment to K1
        let n2 = *blake3::hash(&k2).as_bytes(); // pre-commitment to K2

        let rows = vec![
            // factory birth: all-zero registers, UNINIT
            (
                anchor(0, 10),
                fields(STATE_UNINIT_U64, FIELD_ZERO, FIELD_ZERO, 0, FIELD_ZERO),
            ),
            // inception: install K0 + pre-commit blake3(K1), pin council
            (anchor(1, 11), fields(STATE_ACTIVE, n1, k0, 0, council)),
            // rotation at height 20: exhibit K1, pre-commit blake3(K2), stamp
            (anchor(2, 20), fields(STATE_ACTIVE, n2, k1, 20, council)),
            // interaction: key state untouched
            (anchor(3, 21), fields(STATE_ACTIVE, n2, k1, 20, council)),
        ];
        let events = events_from_snapshots(&cell, &rows);
        let log = IdentityEventLog {
            format: KEL_FORMAT_VERSION.to_string(),
            cell: hex32(&cell.0),
            federation_id: hex32(&[0u8; 32]),
            executor_public_key: hex32(&[0u8; 32]),
            events,
        };
        (log, cell)
    }

    #[test]
    fn well_formed_log_verifies_and_classifies() {
        let (log, _) = well_formed_log();
        assert_eq!(log.events[0].event_type, IdentityEventType::Interaction);
        assert_eq!(log.events[1].event_type, IdentityEventType::Inception);
        assert_eq!(log.events[2].event_type, IdentityEventType::Rotation);
        assert_eq!(log.events[3].event_type, IdentityEventType::Interaction);
        let report = verify_export(&log, None).expect("well-formed log must verify");
        assert_eq!(report.events, 4);
        assert_eq!(report.inceptions, 1);
        assert_eq!(report.rotations, 1);
    }

    #[test]
    fn export_round_trips_through_json() {
        let (log, _) = well_formed_log();
        let json = serde_json::to_string(&log).expect("serialize");
        let back: IdentityEventLog = serde_json::from_str(&json).expect("deserialize");
        verify_export(&back, None).expect("round-tripped log must verify");
    }

    #[test]
    fn chain_tamper_refuses() {
        // Tamper a digested field: the event's own digest no longer matches.
        let (mut log, _) = well_formed_log();
        log.events[2].turn_hash = hex32(&[0xEE; 32]);
        assert_eq!(
            verify_export(&log, None),
            Err(VerifyError::EventDigestMismatch { seq: 2 })
        );

        // Re-state the digest to "fix" event 2: now the NEXT event's prior
        // link refuses — splicing cannot be hidden.
        let (mut log, _) = well_formed_log();
        log.events[2].turn_hash = hex32(&[0xEE; 32]);
        let dec = decode_event(&unhex32(&log.cell).unwrap(), &log.events[2]).unwrap();
        log.events[2].event_digest = hex32(&dec.surface.digest());
        assert_eq!(
            verify_export(&log, None),
            Err(VerifyError::ChainBroken { seq: 3 })
        );

        // Dropping an event breaks the dense seq.
        let (mut log, _) = well_formed_log();
        log.events.remove(1);
        assert_eq!(
            verify_export(&log, None),
            Err(VerifyError::SeqGap {
                expected: 1,
                got: 2
            })
        );
    }

    #[test]
    fn rotation_preimage_verifies_and_forgery_refuses() {
        let cell = CellId([0xBB; 32]);
        let council = *blake3::hash(b"council").as_bytes();
        let k0 = *blake3::hash(b"k0").as_bytes();
        let k1 = *blake3::hash(b"k1").as_bytes();
        let k_evil = *blake3::hash(b"thief").as_bytes(); // NOT pre-committed
        let n1 = *blake3::hash(&k1).as_bytes();
        let n_evil = *blake3::hash(&k_evil).as_bytes();

        // Forged rotation: installs a commitment whose digest was never
        // pre-committed. The builder still emits it (it serializes what
        // the log says happened) — the VERIFIER is the tooth.
        let rows = vec![
            (anchor(0, 11), fields(STATE_ACTIVE, n1, k0, 0, council)),
            (
                anchor(1, 20),
                fields(STATE_ACTIVE, n_evil, k_evil, 20, council),
            ),
        ];
        let events = events_from_snapshots(&cell, &rows);
        let log = IdentityEventLog {
            format: KEL_FORMAT_VERSION.to_string(),
            cell: hex32(&cell.0),
            federation_id: hex32(&[0u8; 32]),
            executor_public_key: hex32(&[0u8; 32]),
            events,
        };
        assert_eq!(
            verify_export(&log, None),
            Err(VerifyError::RotationPreimage { seq: 1 })
        );

        // The honest rotation (k1, pre-committed as n1) verifies.
        let rows = vec![
            (anchor(0, 11), fields(STATE_ACTIVE, n1, k0, 0, council)),
            (anchor(1, 20), fields(STATE_ACTIVE, n_evil, k1, 20, council)),
        ];
        let events = events_from_snapshots(&cell, &rows);
        let log = IdentityEventLog {
            format: KEL_FORMAT_VERSION.to_string(),
            cell: hex32(&cell.0),
            federation_id: hex32(&[0u8; 32]),
            executor_public_key: hex32(&[0u8; 32]),
            events,
        };
        let report = verify_export(&log, None).expect("honest rotation must verify");
        assert_eq!(report.rotations, 1);
    }

    #[test]
    fn key_state_cannot_move_outside_rotation() {
        // An "interaction" that silently swaps the next_keys_digest is
        // refused: the registers are immutable outside rot/icp.
        let cell = CellId([0xCC; 32]);
        let council = *blake3::hash(b"council").as_bytes();
        let k0 = *blake3::hash(b"k0").as_bytes();
        let n1 = *blake3::hash(b"n1").as_bytes();
        let n_swapped = *blake3::hash(b"swapped").as_bytes();
        let rows = vec![
            (anchor(0, 11), fields(STATE_ACTIVE, n1, k0, 0, council)),
            (
                anchor(1, 12),
                fields(STATE_ACTIVE, n_swapped, k0, 0, council),
            ),
        ];
        let events = events_from_snapshots(&cell, &rows);
        // Same current commit ⇒ classified Interaction; the verifier
        // refuses the moved register.
        assert_eq!(events[1].event_type, IdentityEventType::Interaction);
        let log = IdentityEventLog {
            format: KEL_FORMAT_VERSION.to_string(),
            cell: hex32(&cell.0),
            federation_id: hex32(&[0u8; 32]),
            executor_public_key: hex32(&[0u8; 32]),
            events,
        };
        assert!(matches!(
            verify_export(&log, None),
            Err(VerifyError::KeyStateMoved { seq: 1, .. })
        ));
    }

    #[test]
    fn executor_signature_checks() {
        let signing = SigningKey::from_bytes(&[7u8; 32]);
        let pubkey = signing.verifying_key().to_bytes();

        let (mut log, _) = well_formed_log();
        // Attach a receipt to event 3 whose hash the anchor must carry.
        let mut receipt = TurnReceipt {
            turn_hash: unhex32(&log.events[3].turn_hash).unwrap(),
            agent: CellId([0x01; 32]),
            ..TurnReceipt::default()
        };
        let sig = signing.sign(&receipt.canonical_executor_signed_message());
        receipt.executor_signature = Some(sig.to_bytes().to_vec());

        // Rebind event 3's receipt_hash to this receipt and re-chain
        // digests for events 3.. (the anchor changed).
        log.events[3].receipt_hash = hex32(&receipt.receipt_hash());
        let cell = unhex32(&log.cell).unwrap();
        let dec = decode_event(&cell, &log.events[3]).unwrap();
        log.events[3].event_digest = hex32(&dec.surface.digest());
        log.events[3].receipt = Some(receipt.clone());

        let report = verify_export(&log, Some(&pubkey)).expect("signed receipt must verify");
        assert_eq!(report.receipts_checked, 1);
        assert_eq!(report.signatures_checked, 1);

        // Wrong pinned key refuses.
        let wrong = SigningKey::from_bytes(&[8u8; 32])
            .verifying_key()
            .to_bytes();
        assert!(matches!(
            verify_export(&log, Some(&wrong)),
            Err(VerifyError::BadExecutorSignature { seq: 3, .. })
        ));

        // A tampered receipt (hash no longer matches the event) refuses.
        let mut tampered = log.clone();
        if let Some(r) = &mut tampered.events[3].receipt {
            r.computrons_used += 1;
        }
        assert_eq!(
            verify_export(&tampered, Some(&pubkey)),
            Err(VerifyError::ReceiptHashMismatch { seq: 3 })
        );
    }
}

//! # MailboxCrank — drain a hosted inbox and feed its messages to the owner's
//! executor as deferred turns (docs/ORGANS.md §2, the mailbox organ).
//!
//! This is a WELD of existing machinery, not a new protocol:
//!
//! * **Sealing** rides the captp store-and-forward box
//!   ([`dregg_captp::store_forward`]): X25519 → HKDF-SHA256 →
//!   ChaCha20-Poly1305, wrapped in the existing [`BlocklaceEnvelope`] wire
//!   shape. The relay sees only ciphertext.
//! * **Transport** is the `dregg-node relay` hosted-inbox service
//!   (subscribe / send / drain / proof routes) — [`RelayHttpTransport`]
//!   speaks exactly those routes, signing drains with the owner's Ed25519
//!   key the relay already verifies (`dregg-relay-drain-v1`).
//! * **Custody** is the relay's existing dequeue proofs: every drained
//!   message arrives with the FULL `dregg_storage::queue::DequeueProof`
//!   (entry + roots + remaining leaves), and the crank VERIFIES it with the
//!   queue's own verifier — [`verify_dequeue_proof`] for the head of a
//!   drain batch, then [`verify_dequeue_proof_against`] chained on the
//!   tracked live root (`proof[i+1].old_root == proof[i].new_root`), which
//!   refuses replayed/stale proofs inside the batch. The entry's
//!   `content_hash` — recomputed from the delivered body — binds the
//!   ciphertext to the proof-covered leaf. The [`CustodyReceipt`] records
//!   exactly that material (no new receipt type). (Cross-crank root pinning
//!   is not possible from dequeue proofs alone: enqueues that happen while
//!   the crank sleeps legitimately move the root.)
//! * **Execution** rides the owner runtime's ONE public turn shape:
//!   [`AgentRuntime::turn()`](crate::AgentRuntime::turn) →
//!   `sign()` → `submit()`. No new executor entry.
//!
//! ## Authorization (fail-closed)
//!
//! The authorized-sender set is CELL STATE: the owner's inbox cell (born
//! from the storage-template CapInbox factory, seeded at node boot) holds
//! the sender-set commitment in slot 5 (`SENDER_SET_ROOT_SLOT`). Every
//! mutation of that set is an executor-admitted turn (the cell's installed
//! program + the owner-signature/parent-capability gates decide), submitted
//! via [`MailboxCrank::grant_sender`]. The crank's accept gate then anchors
//! to the ON-CELL root: a drained message executes only if
//!
//! 1. the delivered body re-hashes to the proof-covered `content_hash`
//!    (custody binding),
//! 2. the inbox cell's live slot-5 root is non-zero AND equals the
//!    commitment over the crank's openable sender set (a stale or foreign
//!    opening fails closed), and
//! 3. the message's claimed sender is a member of that set.
//!
//! Anything else — missing inbox cell, zero root, root mismatch, unknown
//! sender, broken seal, malformed intent — is REFUSED and recorded; it
//! never reaches the executor. (The deeper per-`send` membership STARK —
//! `StateConstraint::SenderAuthorized` with the
//! `MerkleMembershipStarkVerifier` — is the circuit-side tooth of the same
//! design, exercised in `turn/tests/integration_sender_authorized_air.rs`.)

use std::collections::BTreeSet;
use std::sync::{Arc, RwLock};

use serde::{Deserialize, Serialize};

use dregg_captp::FederationId;
use dregg_captp::store_forward::{self, BlocklaceEnvelope};
use dregg_cell::state::FieldElement;
use dregg_cell::CellId;
use dregg_storage::queue::{
    DequeueProof, QueueEntry, verify_dequeue_proof, verify_dequeue_proof_against,
};
use dregg_turn::Effect;

use crate::cipherclerk::AgentCipherclerk;
use crate::error::SdkError;
use crate::receipt::Receipt;
use crate::runtime::AgentRuntime;

/// Slot index of the sender-set commitment on a CapInbox cell. Mirrors
/// `dregg_storage_templates::cap_inbox::SENDER_SET_ROOT_SLOT` (the published
/// template's slot layout — see `STORAGE-AS-CELL-PROGRAMS.md` §3.1).
pub const SENDER_SET_ROOT_SLOT: usize = 5;

/// Domain tag for the openable sender-set commitment written to slot 5 by
/// [`MailboxCrank::grant_sender`] and re-derived by the accept gate.
const SENDER_SET_DOMAIN: &[u8] = b"dregg-mailbox-sender-set-v1";

// =============================================================================
// Turn-intent wire shape
// =============================================================================

/// A deferred turn-intent: the message body a sender seals into the mailbox.
///
/// Decoded by the recipient's crank and submitted through the owner's normal
/// `.turn()` path — the OWNER's signature authorizes the resulting turn, so
/// an intent can only do what the owner could do themselves (the executor's
/// ordinary gates apply unchanged). The `effects` reuse the existing
/// [`dregg_turn::Effect`] codec (serde/postcard); nothing new on the wire.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MailboxTurnIntent {
    /// The cell the action targets (the owner's cell, or one it administers).
    pub target: CellId,
    /// The action's method verb (e.g. `"execute"`).
    pub method: String,
    /// The effects to run.
    pub effects: Vec<Effect>,
}

impl MailboxTurnIntent {
    /// Canonical wire encoding (postcard, same codec the executor's
    /// CapTP-delivered signing message uses for effects).
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("intent serialization never fails")
    }

    /// Decode from wire bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, SdkError> {
        postcard::from_bytes(bytes)
            .map_err(|e| SdkError::Wire(format!("malformed mailbox turn-intent: {e}")))
    }
}

/// Seal a turn-intent for `recipient`: encrypt to the recipient's X25519
/// public key and wrap in the existing [`BlocklaceEnvelope`] store-and-forward
/// wire shape. The returned bytes are the relay `send` payload.
pub fn seal_intent(
    intent: &MailboxTurnIntent,
    recipient: FederationId,
    recipient_x25519_pk: &[u8; 32],
    sender_x25519_secret: &[u8; 32],
    causal_sequence: u64,
) -> Vec<u8> {
    store_forward::queue_via_blocklace(
        recipient,
        &intent.to_bytes(),
        recipient_x25519_pk,
        sender_x25519_secret,
        causal_sequence,
    )
}

// =============================================================================
// Custody material (wiring what the relay's dequeue proofs already provide)
// =============================================================================

/// Recompute the relay's content hash for a delivered `Encrypted` body.
///
/// MUST match the relay's `inbox_message_content_hash` /
/// `dregg_storage::inbox::InboxMessage::content_hash` framing for
/// `InboxMessage::Encrypted` (`0x03 || sender || ciphertext`): the dequeue
/// proof's roots cover this hash, so re-deriving it from the delivered body
/// is what makes the custody receipt checkable end-to-end.
pub fn encrypted_content_hash(sender: &[u8; 32], ciphertext: &[u8]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(1 + 32 + ciphertext.len());
    buf.push(0x03);
    buf.extend_from_slice(sender);
    buf.extend_from_slice(ciphertext);
    *blake3::hash(&buf).as_bytes()
}

/// A message delivered by a mailbox transport (one drained relay entry),
/// carrying the FULL dequeue proof so the crank can verify custody itself.
#[derive(Debug, Clone)]
pub struct DeliveredMessage {
    /// The proof-covered content hash of this entry.
    pub content_hash: [u8; 32],
    /// The claimed sender public key.
    pub sender: [u8; 32],
    /// The anti-spam deposit the sender posted.
    pub deposit: u64,
    /// Block height the relay enqueued the message at.
    pub enqueued_at: u64,
    /// Entry size in bytes (part of the proof-covered `QueueEntry` leaf).
    pub size: usize,
    /// The delivered ciphertext body (a sealed [`BlocklaceEnvelope`]).
    pub payload: Vec<u8>,
    /// Dequeue proof: the queue root before this dequeue.
    pub proof_old_root: [u8; 32],
    /// Dequeue proof: the queue root after this dequeue.
    pub proof_new_root: [u8; 32],
    /// Dequeue proof: absolute head index (metadata, not root-bound).
    pub proof_position: usize,
    /// Dequeue proof: leaf hashes remaining after this dequeue, FIFO.
    pub proof_remaining_leaves: Vec<[u8; 32]>,
}

impl DeliveredMessage {
    /// Reassemble the relay's [`DequeueProof`] for verification. The entry
    /// fields come from the same wire message, so a relay that lies about
    /// any of them (sender, deposit, size, …) breaks `hash_entry` and the
    /// proof fails structurally.
    pub fn dequeue_proof(&self) -> DequeueProof {
        DequeueProof {
            entry: QueueEntry {
                content_hash: self.content_hash,
                sender: self.sender,
                deposit: self.deposit,
                enqueued_at: self.enqueued_at,
                size: self.size,
            },
            old_root: self.proof_old_root,
            new_root: self.proof_new_root,
            position: self.proof_position,
            remaining_leaves: self.proof_remaining_leaves.clone(),
        }
    }
}

/// The custody receipt for one delivered message — exactly the material the
/// relay's dequeue proofs already provide, plus the binding check result and
/// (on execution) the committed turn's receipt hash.
#[derive(Debug, Clone)]
pub struct CustodyReceipt {
    pub content_hash: [u8; 32],
    pub sender: [u8; 32],
    pub deposit: u64,
    pub enqueued_at: u64,
    /// `MerkleQueue::dequeue` proof roots from the relay.
    pub proof_old_root: [u8; 32],
    pub proof_new_root: [u8; 32],
    /// Whether the dequeue proof verified (`verify_dequeue_proof` for the
    /// batch head, `verify_dequeue_proof_against` the tracked root after).
    pub proof_ok: bool,
    /// Whether the delivered body re-hashed to `content_hash`.
    pub payload_binding_ok: bool,
    /// The committed turn's receipt hash, when the intent executed.
    pub executed_turn_receipt: Option<[u8; 32]>,
}

/// Why the crank refused to execute a delivered message (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefusalReason {
    /// The dequeue proof failed verification: structurally malformed, or
    /// (within a drain batch) replayed/stale against the tracked live root.
    CustodyProofInvalid,
    /// Delivered body does not re-hash to the proof-covered content hash.
    BindingMismatch,
    /// The owner's inbox cell is not present in the runtime ledger.
    InboxCellMissing,
    /// The inbox cell's slot-5 root is zero (nobody authorized) or does not
    /// match the crank's openable sender set.
    SenderSetRootMismatch,
    /// The claimed sender is not in the executor-anchored authorized set.
    UnauthorizedSender,
    /// The sealed envelope failed to parse or decrypt.
    SealInvalid(String),
    /// The decrypted plaintext is not a valid turn-intent.
    MalformedIntent(String),
    /// The executor rejected the submitted turn.
    SubmitRejected(String),
}

/// Disposition of one delivered message after a crank pass.
#[derive(Debug, Clone)]
pub enum CrankDisposition {
    /// The intent executed; `CustodyReceipt::executed_turn_receipt` is set.
    Executed,
    /// The message was refused (custody is still recorded).
    Refused(RefusalReason),
}

/// One delivered message's outcome.
#[derive(Debug, Clone)]
pub struct CrankOutcome {
    pub receipt: CustodyReceipt,
    pub disposition: CrankDisposition,
}

/// Result of one crank pass.
#[derive(Debug, Clone, Default)]
pub struct CrankReport {
    pub outcomes: Vec<CrankOutcome>,
}

impl CrankReport {
    pub fn executed(&self) -> usize {
        self.outcomes
            .iter()
            .filter(|o| matches!(o.disposition, CrankDisposition::Executed))
            .count()
    }

    pub fn refused(&self) -> usize {
        self.outcomes.len() - self.executed()
    }
}

// =============================================================================
// Transport
// =============================================================================

/// A mailbox drain transport. The production impl is [`RelayHttpTransport`]
/// (the node relay's drain route); tests may drain in-process.
pub trait MailboxTransport {
    /// Drain up to `max` pending messages from the owner's inbox.
    fn drain(&mut self, max: usize) -> Result<Vec<DeliveredMessage>, SdkError>;
}

// =============================================================================
// The crank
// =============================================================================

/// Drains a mailbox and feeds its messages to the owner's executor as
/// deferred turns. See the module docs for the authorization model.
pub struct MailboxCrank<'rt, T: MailboxTransport> {
    runtime: &'rt AgentRuntime,
    transport: T,
    /// The owner's inbox cell (CapInbox-template; slot 5 = sender-set root).
    inbox_cell: CellId,
    /// The owner's X25519 secret for unsealing store-and-forward boxes.
    x25519_secret: [u8; 32],
    /// The openable authorized-sender set. Must re-commit to the inbox
    /// cell's live slot-5 root or the crank fails closed.
    senders: BTreeSet<[u8; 32]>,
    /// Custody receipts accumulated across crank passes.
    receipts: Vec<CustodyReceipt>,
}

/// Canonical openable commitment over an authorized-sender set: a
/// domain-tagged blake3 fold over the sorted member keys. The empty set
/// commits to all-zeros — and a zero on-cell root always fails closed.
pub fn sender_set_commitment(senders: &BTreeSet<[u8; 32]>) -> FieldElement {
    if senders.is_empty() {
        return [0u8; 32];
    }
    let mut hasher = blake3::Hasher::new();
    hasher.update(SENDER_SET_DOMAIN);
    for sender in senders {
        hasher.update(sender);
    }
    *hasher.finalize().as_bytes()
}

impl<'rt, T: MailboxTransport> MailboxCrank<'rt, T> {
    /// Build a crank over the owner's runtime + inbox cell.
    pub fn new(
        runtime: &'rt AgentRuntime,
        inbox_cell: CellId,
        x25519_secret: [u8; 32],
        transport: T,
    ) -> Self {
        MailboxCrank {
            runtime,
            transport,
            inbox_cell,
            x25519_secret,
            senders: BTreeSet::new(),
            receipts: Vec::new(),
        }
    }

    /// The custody receipts accumulated so far (every drained message,
    /// executed or refused, leaves one).
    pub fn receipts(&self) -> &[CustodyReceipt] {
        &self.receipts
    }

    /// The current openable authorized-sender set.
    pub fn senders(&self) -> &BTreeSet<[u8; 32]> {
        &self.senders
    }

    /// Authorize `sender` by writing the updated set commitment to the inbox
    /// cell's slot 5 THROUGH THE EXECUTOR (the owner's `.turn()` path with
    /// the template's `grant_sender` verb). The turn only commits if the
    /// owner's signature verifies against the inbox cell, the agent holds a
    /// c-list capability on it (the factory adopt bootstrap), and the cell's
    /// installed program admits the write — that admission is what anchors
    /// the crank's accept gate.
    pub fn grant_sender(&mut self, sender: [u8; 32]) -> Result<Receipt, SdkError> {
        let mut next = self.senders.clone();
        next.insert(sender);
        let root = sender_set_commitment(&next);
        let receipt = self
            .runtime
            .turn()
            .on(self.inbox_cell)
            .method("grant_sender")
            .write(SENDER_SET_ROOT_SLOT, root)
            .sign()?
            .submit()?;
        // Only adopt the opening once the executor committed the root.
        self.senders = next;
        Ok(receipt)
    }

    /// Read the inbox cell's LIVE sender-set root from the runtime ledger.
    fn on_cell_sender_root(&self) -> Option<FieldElement> {
        let ledger = self.runtime.ledger().lock().unwrap();
        ledger
            .get(&self.inbox_cell)
            .map(|cell| cell.state.fields[SENDER_SET_ROOT_SLOT])
    }

    /// Fail-closed sender-authorization gate (see module docs).
    fn sender_authorized(&self, sender: &[u8; 32]) -> Result<(), RefusalReason> {
        let Some(on_cell_root) = self.on_cell_sender_root() else {
            return Err(RefusalReason::InboxCellMissing);
        };
        if on_cell_root == [0u8; 32] {
            // Nobody authorized — an empty inbox admits no one.
            return Err(RefusalReason::SenderSetRootMismatch);
        }
        if on_cell_root != sender_set_commitment(&self.senders) {
            // The crank's opening is stale or foreign: refuse everything
            // rather than trust an unanchored local list.
            return Err(RefusalReason::SenderSetRootMismatch);
        }
        if !self.senders.contains(sender) {
            return Err(RefusalReason::UnauthorizedSender);
        }
        Ok(())
    }

    /// Unseal a delivered body: parse the [`BlocklaceEnvelope`] and decrypt
    /// with the owner's X25519 secret.
    fn unseal(&self, payload: &[u8]) -> Result<Vec<u8>, RefusalReason> {
        let envelope = BlocklaceEnvelope::from_payload(payload)
            .ok_or_else(|| RefusalReason::SealInvalid("not a store-forward envelope".into()))?;
        envelope
            .decrypt(&self.x25519_secret)
            .map_err(|e| RefusalReason::SealInvalid(e.to_string()))
    }

    /// Submit a decoded intent through the owner's normal `.turn()` path.
    fn submit_intent(&self, intent: &MailboxTurnIntent) -> Result<Receipt, SdkError> {
        self.runtime
            .turn()
            .on(intent.target)
            .method(&intent.method)
            .effects(intent.effects.iter().cloned())
            .sign()?
            .submit()
    }

    /// One crank pass: drain up to `max` messages and process each through
    /// the fail-closed gate chain (custody proof → binding → sender-auth →
    /// unseal → decode → submit). Every drained message — executed or
    /// refused — leaves a [`CustodyReceipt`].
    pub fn crank_once(&mut self, max: usize) -> Result<CrankReport, SdkError> {
        let delivered = self.transport.drain(max)?;
        let mut report = CrankReport::default();

        // The live root tracked THROUGH the drain batch: the head proof is
        // verified structurally and adopted; every later proof must verify
        // AGAINST the previous proof's `new_root` (the `_against` form —
        // refuses replayed/stale proofs). A failed proof does NOT advance
        // the root, so everything after a break in the chain also refuses.
        let mut tracked_root: Option<[u8; 32]> = None;

        for msg in delivered {
            let mut receipt = CustodyReceipt {
                content_hash: msg.content_hash,
                sender: msg.sender,
                deposit: msg.deposit,
                enqueued_at: msg.enqueued_at,
                proof_old_root: msg.proof_old_root,
                proof_new_root: msg.proof_new_root,
                proof_ok: false,
                payload_binding_ok: false,
                executed_turn_receipt: None,
            };

            let disposition = (|| {
                // 0. Custody proof: the relay's dequeue proof must verify —
                //    head-binding + exact post-root, and (after the batch
                //    head) pinned to the tracked live root.
                let proof = msg.dequeue_proof();
                let proof_ok = match &tracked_root {
                    Some(root) => verify_dequeue_proof_against(&proof, root),
                    None => verify_dequeue_proof(&proof),
                };
                if !proof_ok {
                    return CrankDisposition::Refused(RefusalReason::CustodyProofInvalid);
                }
                receipt.proof_ok = true;
                tracked_root = Some(proof.new_root);

                // 1. Custody binding: the delivered body must re-hash to the
                //    proof-covered content hash.
                if encrypted_content_hash(&msg.sender, &msg.payload) != msg.content_hash {
                    return CrankDisposition::Refused(RefusalReason::BindingMismatch);
                }
                receipt.payload_binding_ok = true;

                // 2. Fail-closed sender authorization (executor-anchored).
                if let Err(reason) = self.sender_authorized(&msg.sender) {
                    return CrankDisposition::Refused(reason);
                }

                // 3. Unseal.
                let plaintext = match self.unseal(&msg.payload) {
                    Ok(p) => p,
                    Err(reason) => return CrankDisposition::Refused(reason),
                };

                // 4. Decode the turn-intent.
                let intent = match MailboxTurnIntent::from_bytes(&plaintext) {
                    Ok(i) => i,
                    Err(e) => {
                        return CrankDisposition::Refused(RefusalReason::MalformedIntent(
                            e.to_string(),
                        ));
                    }
                };

                // 5. Execute as a deferred turn on the owner's normal path —
                //    the executor's gates decide commit/reject.
                match self.submit_intent(&intent) {
                    Ok(turn_receipt) => {
                        receipt.executed_turn_receipt =
                            Some(turn_receipt.as_turn_receipt().receipt_hash());
                        CrankDisposition::Executed
                    }
                    Err(e) => CrankDisposition::Refused(RefusalReason::SubmitRejected(
                        e.to_string(),
                    )),
                }
            })();

            self.receipts.push(receipt.clone());
            report.outcomes.push(CrankOutcome {
                receipt,
                disposition,
            });
        }

        Ok(report)
    }
}

// =============================================================================
// Relay HTTP transport (the node relay's existing routes)
// =============================================================================

/// HTTP client for the `dregg-node relay` hosted-inbox routes, signing
/// owner-authenticated requests with the agent's Ed25519 key exactly as the
/// relay's `verify_owner_signature` expects (F-P1-1 domains).
#[cfg(all(feature = "federation-client", feature = "network"))]
pub struct RelayHttpTransport {
    base_url: String,
    owner_pk: [u8; 32],
    cipherclerk: Arc<RwLock<AgentCipherclerk>>,
    rt: tokio::runtime::Runtime,
    client: reqwest::Client,
}

#[cfg(all(feature = "federation-client", feature = "network"))]
pub use relay_http::ProofResponseWire;

#[cfg(all(feature = "federation-client", feature = "network"))]
mod relay_http {
    use super::*;
    use base64::Engine;

    #[derive(Deserialize)]
    struct DrainResponseWire {
        messages: Vec<DrainedMessageWire>,
    }

    #[derive(Deserialize)]
    struct DrainedMessageWire {
        content_hash: String,
        sender: String,
        deposit: u64,
        enqueued_at: u64,
        #[serde(default)]
        size: usize,
        proof_old_root: String,
        proof_new_root: String,
        #[serde(default)]
        proof_position: usize,
        #[serde(default)]
        proof_remaining_leaves: Vec<String>,
        #[serde(default)]
        payload: String,
    }

    #[derive(Deserialize)]
    pub struct ProofResponseWire {
        pub old_root: String,
        pub new_root: String,
        pub found: bool,
    }

    fn hex_encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn hex_decode_32(s: &str) -> Result<[u8; 32], SdkError> {
        if s.len() != 64 {
            return Err(SdkError::Wire(format!(
                "expected 64 hex chars, got {}",
                s.len()
            )));
        }
        let mut bytes = [0u8; 32];
        for (i, byte) in bytes.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16)
                .map_err(|e| SdkError::Wire(format!("bad hex: {e}")))?;
        }
        Ok(bytes)
    }

    impl RelayHttpTransport {
        /// Build a transport for `base_url` (e.g. `http://127.0.0.1:3100`),
        /// authenticating as the cipherclerk's identity.
        pub fn new(
            base_url: impl Into<String>,
            cipherclerk: Arc<RwLock<AgentCipherclerk>>,
        ) -> Result<Self, SdkError> {
            let owner_pk = cipherclerk
                .read()
                .unwrap_or_else(|e| e.into_inner())
                .public_key()
                .0;
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .map_err(|e| SdkError::Wire(format!("tokio runtime: {e}")))?;
            Ok(RelayHttpTransport {
                base_url: base_url.into(),
                owner_pk,
                cipherclerk,
                rt,
                client: reqwest::Client::new(),
            })
        }

        /// The identity this transport authenticates as.
        pub fn owner_pk(&self) -> [u8; 32] {
            self.owner_pk
        }

        fn sign(&self, domain: &[u8], payload: &[u8]) -> String {
            let mut msg = Vec::with_capacity(domain.len() + payload.len());
            msg.extend_from_slice(domain);
            msg.extend_from_slice(payload);
            let sig = self
                .cipherclerk
                .read()
                .unwrap_or_else(|e| e.into_inner())
                .sign_bytes(&msg);
            hex_encode(&sig.0)
        }

        fn fresh_nonce() -> [u8; 8] {
            let mut nonce = [0u8; 8];
            getrandom::fill(&mut nonce).expect("getrandom failed");
            nonce
        }

        /// `POST /relay/subscribe` — create this owner's hosted inbox.
        pub fn subscribe(
            &self,
            capacity: Option<usize>,
            min_deposit: Option<u64>,
        ) -> Result<(), SdkError> {
            let nonce = Self::fresh_nonce();
            let mut payload = Vec::with_capacity(40);
            payload.extend_from_slice(&self.owner_pk);
            payload.extend_from_slice(&nonce);
            let signature = self.sign(b"dregg-relay-subscribe-v1", &payload);
            let body = serde_json::json!({
                "owner": hex_encode(&self.owner_pk),
                "capacity": capacity,
                "min_deposit": min_deposit,
                "nonce": hex_encode(&nonce),
                "signature": signature,
            });
            let url = format!("{}/relay/subscribe", self.base_url);
            self.rt.block_on(async {
                let resp = self
                    .client
                    .post(&url)
                    .json(&body)
                    .send()
                    .await
                    .map_err(|e| SdkError::Wire(format!("relay subscribe: {e}")))?;
                if !resp.status().is_success() {
                    let status = resp.status();
                    let text = resp.text().await.unwrap_or_default();
                    return Err(SdkError::Wire(format!(
                        "relay subscribe rejected ({status}): {text}"
                    )));
                }
                Ok(())
            })
        }

        /// `POST /relay/send/:dest` — enqueue a sealed payload for `dest`.
        /// Unauthenticated at the relay (sender authorization is enforced at
        /// the recipient's executor-anchored gate); `deposit` is the
        /// anti-spam stake.
        pub fn send(
            &self,
            dest: &[u8; 32],
            sender: &[u8; 32],
            payload: &[u8],
            deposit: u64,
        ) -> Result<(), SdkError> {
            let body = serde_json::json!({
                "sender": hex_encode(sender),
                "payload": base64::engine::general_purpose::STANDARD.encode(payload),
                "deposit": deposit,
            });
            let url = format!("{}/relay/send/{}", self.base_url, hex_encode(dest));
            self.rt.block_on(async {
                let resp = self
                    .client
                    .post(&url)
                    .json(&body)
                    .send()
                    .await
                    .map_err(|e| SdkError::Wire(format!("relay send: {e}")))?;
                if !resp.status().is_success() {
                    let status = resp.status();
                    let text = resp.text().await.unwrap_or_default();
                    return Err(SdkError::Wire(format!(
                        "relay send rejected ({status}): {text}"
                    )));
                }
                Ok(())
            })
        }

        /// `GET /relay/proof/:msg_id` — fetch the cached dequeue proof for a
        /// delivered message (custody-receipt checkability).
        pub fn proof(&self, content_hash: &[u8; 32]) -> Result<ProofResponseWire, SdkError> {
            let url = format!("{}/relay/proof/{}", self.base_url, hex_encode(content_hash));
            self.rt.block_on(async {
                self.client
                    .get(&url)
                    .send()
                    .await
                    .map_err(|e| SdkError::Wire(format!("relay proof: {e}")))?
                    .json::<ProofResponseWire>()
                    .await
                    .map_err(|e| SdkError::Wire(format!("relay proof decode: {e}")))
            })
        }
    }

    impl MailboxTransport for RelayHttpTransport {
        fn drain(&mut self, max: usize) -> Result<Vec<DeliveredMessage>, SdkError> {
            let nonce = Self::fresh_nonce();
            let mut payload = Vec::with_capacity(48);
            payload.extend_from_slice(&self.owner_pk);
            payload.extend_from_slice(&nonce);
            payload.extend_from_slice(&(max as u64).to_le_bytes());
            let signature = self.sign(b"dregg-relay-drain-v1", &payload);

            let url = format!(
                "{}/relay/drain?owner={}&max={}&nonce={}&signature={}",
                self.base_url,
                hex_encode(&self.owner_pk),
                max,
                hex_encode(&nonce),
                signature,
            );
            let wire: DrainResponseWire = self.rt.block_on(async {
                let resp = self
                    .client
                    .get(&url)
                    .send()
                    .await
                    .map_err(|e| SdkError::Wire(format!("relay drain: {e}")))?;
                if !resp.status().is_success() {
                    let status = resp.status();
                    let text = resp.text().await.unwrap_or_default();
                    return Err(SdkError::Wire(format!(
                        "relay drain rejected ({status}): {text}"
                    )));
                }
                resp.json::<DrainResponseWire>()
                    .await
                    .map_err(|e| SdkError::Wire(format!("relay drain decode: {e}")))
            })?;

            wire.messages
                .into_iter()
                .map(|m| {
                    Ok(DeliveredMessage {
                        content_hash: hex_decode_32(&m.content_hash)?,
                        sender: hex_decode_32(&m.sender)?,
                        deposit: m.deposit,
                        enqueued_at: m.enqueued_at,
                        size: m.size,
                        payload: base64::engine::general_purpose::STANDARD
                            .decode(&m.payload)
                            .map_err(|e| SdkError::Wire(format!("payload base64: {e}")))?,
                        proof_old_root: hex_decode_32(&m.proof_old_root)?,
                        proof_new_root: hex_decode_32(&m.proof_new_root)?,
                        proof_position: m.proof_position,
                        proof_remaining_leaves: m
                            .proof_remaining_leaves
                            .iter()
                            .map(|leaf| hex_decode_32(leaf))
                            .collect::<Result<Vec<_>, _>>()?,
                    })
                })
                .collect()
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_captp::store_forward::generate_x25519_keypair;
    use dregg_cell::Cell;

    /// In-memory transport: a pre-loaded queue of delivered messages.
    struct MemTransport {
        pending: Vec<DeliveredMessage>,
    }

    impl MailboxTransport for MemTransport {
        fn drain(&mut self, max: usize) -> Result<Vec<DeliveredMessage>, SdkError> {
            let n = max.min(self.pending.len());
            Ok(self.pending.drain(..n).collect())
        }
    }

    fn test_runtime(label: &str) -> AgentRuntime {
        let cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
            *blake3::hash(format!("mailbox-test:{label}").as_bytes()).as_bytes(),
        ));
        AgentRuntime::new_simple(cclerk, "mailbox-test")
    }

    /// Insert a CapInbox-shaped cell (owned by the runtime's key) directly
    /// into the runtime ledger with the given slot-5 root, plus a c-list
    /// capability so `.turn().on(inbox)` passes the parent gate. (The node
    /// e2e exercises the full factory-birth path; these unit tests focus the
    /// crank's gate chain.)
    fn install_inbox(runtime: &AgentRuntime, root: FieldElement) -> CellId {
        let owner_pk = runtime
            .cipherclerk()
            .read()
            .unwrap()
            .public_key()
            .0;
        let token = *blake3::hash(b"mailbox-test-inbox").as_bytes();
        let mut inbox = Cell::with_balance(owner_pk, token, 10_000);
        inbox.state.fields[SENDER_SET_ROOT_SLOT] = root;
        let inbox_id = inbox.id();
        let mut ledger = runtime.ledger().lock().unwrap();
        let _ = ledger.insert_cell(inbox);
        if let Some(agent) = ledger.get_mut(&runtime.cell_id()) {
            agent
                .capabilities
                .grant(inbox_id, dregg_cell::AuthRequired::None);
        }
        inbox_id
    }

    /// Run `msgs` through a REAL `MerkleQueue` (enqueue all, dequeue all) so
    /// every `DeliveredMessage` carries a genuine, chained dequeue proof —
    /// exactly what the relay's drain produces.
    fn deliver_all(msgs: Vec<([u8; 32], Vec<u8>)>) -> Vec<DeliveredMessage> {
        let mut queue = dregg_storage::queue::MerkleQueue::new(msgs.len().max(1));
        for (sender, payload) in &msgs {
            queue
                .enqueue(QueueEntry {
                    content_hash: encrypted_content_hash(sender, payload),
                    sender: *sender,
                    deposit: 100,
                    enqueued_at: 1,
                    size: payload.len(),
                })
                .expect("test queue enqueue");
        }
        msgs.into_iter()
            .map(|(_, payload)| {
                let (entry, proof) = queue.dequeue().expect("test queue dequeue");
                DeliveredMessage {
                    content_hash: entry.content_hash,
                    sender: entry.sender,
                    deposit: entry.deposit,
                    enqueued_at: entry.enqueued_at,
                    size: entry.size,
                    payload,
                    proof_old_root: proof.old_root,
                    proof_new_root: proof.new_root,
                    proof_position: proof.position,
                    proof_remaining_leaves: proof.remaining_leaves,
                }
            })
            .collect()
    }

    fn delivered(sender: [u8; 32], payload: Vec<u8>) -> DeliveredMessage {
        deliver_all(vec![(sender, payload)]).remove(0)
    }

    #[test]
    fn intent_codec_round_trips() {
        let intent = MailboxTurnIntent {
            target: CellId::from_bytes([7u8; 32]),
            method: "execute".into(),
            effects: vec![Effect::IncrementNonce {
                cell: CellId::from_bytes([7u8; 32]),
            }],
        };
        let decoded = MailboxTurnIntent::from_bytes(&intent.to_bytes()).unwrap();
        assert_eq!(decoded.to_bytes(), intent.to_bytes());
        assert_eq!(decoded.target, intent.target);
        assert_eq!(decoded.method, intent.method);
        assert_eq!(decoded.effects.len(), intent.effects.len());
    }

    #[test]
    fn seal_unseal_round_trips() {
        let (b_secret, b_public) = generate_x25519_keypair();
        let (a_secret, _) = generate_x25519_keypair();
        let intent = MailboxTurnIntent {
            target: CellId::from_bytes([9u8; 32]),
            method: "execute".into(),
            effects: vec![],
        };
        let sealed = seal_intent(&intent, FederationId([0xBB; 32]), &b_public, &a_secret, 0);
        let envelope = BlocklaceEnvelope::from_payload(&sealed).expect("envelope parses");
        let plain = envelope.decrypt(&b_secret).expect("decrypts");
        assert_eq!(plain, intent.to_bytes());
    }

    #[test]
    fn authorized_sealed_intent_executes_as_turn() {
        let runtime = test_runtime("authorized");
        let (b_secret, b_public) = generate_x25519_keypair();
        let (a_secret, _) = generate_x25519_keypair();
        let a_pk = [0xA1; 32];

        // Recipient cell for the intent's transfer.
        let dest = {
            let cell = Cell::with_balance([0xC1; 32], [0u8; 32], 0);
            let id = cell.id();
            runtime.ledger().lock().unwrap().insert_cell(cell).unwrap();
            id
        };

        let mut set = BTreeSet::new();
        set.insert(a_pk);
        let inbox = install_inbox(&runtime, sender_set_commitment(&set));

        let intent = MailboxTurnIntent {
            target: runtime.cell_id(),
            method: "execute".into(),
            effects: vec![Effect::Transfer {
                from: runtime.cell_id(),
                to: dest,
                amount: 7,
            }],
        };
        let sealed = seal_intent(&intent, FederationId(a_pk), &b_public, &a_secret, 0);

        let transport = MemTransport {
            pending: vec![delivered(a_pk, sealed)],
        };
        let mut crank = MailboxCrank::new(&runtime, inbox, b_secret, transport);
        crank.senders.insert(a_pk);

        let report = crank.crank_once(10).unwrap();
        assert_eq!(report.executed(), 1, "report: {report:?}");
        assert_eq!(report.refused(), 0);
        assert!(crank.receipts()[0].payload_binding_ok);
        assert!(crank.receipts()[0].executed_turn_receipt.is_some());

        let ledger = runtime.ledger().lock().unwrap();
        assert_eq!(ledger.get(&dest).unwrap().state.balance(), 7);
    }

    #[test]
    fn unauthorized_sender_is_refused_fail_closed() {
        let runtime = test_runtime("unauthorized");
        let (b_secret, b_public) = generate_x25519_keypair();
        let (e_secret, _) = generate_x25519_keypair();
        let a_pk = [0xA1; 32];
        let e_pk = [0xE1; 32]; // never granted

        let mut set = BTreeSet::new();
        set.insert(a_pk);
        let inbox = install_inbox(&runtime, sender_set_commitment(&set));

        let intent = MailboxTurnIntent {
            target: runtime.cell_id(),
            method: "execute".into(),
            effects: vec![Effect::IncrementNonce {
                cell: runtime.cell_id(),
            }],
        };
        let sealed = seal_intent(&intent, FederationId(e_pk), &b_public, &e_secret, 0);

        let transport = MemTransport {
            pending: vec![delivered(e_pk, sealed)],
        };
        let mut crank = MailboxCrank::new(&runtime, inbox, b_secret, transport);
        crank.senders.insert(a_pk);

        let nonce_before = runtime.nonce();
        let report = crank.crank_once(10).unwrap();
        assert_eq!(report.executed(), 0);
        assert!(matches!(
            report.outcomes[0].disposition,
            CrankDisposition::Refused(RefusalReason::UnauthorizedSender)
        ));
        // Nothing reached the executor.
        assert_eq!(runtime.nonce(), nonce_before);
        // Custody is still recorded for the refused message.
        assert_eq!(crank.receipts().len(), 1);
        assert!(crank.receipts()[0].executed_turn_receipt.is_none());
    }

    #[test]
    fn zero_or_stale_root_refuses_everything() {
        let runtime = test_runtime("stale-root");
        let (b_secret, b_public) = generate_x25519_keypair();
        let (a_secret, _) = generate_x25519_keypair();
        let a_pk = [0xA1; 32];

        // On-cell root is ZERO (nobody ever granted) — even a sender in the
        // crank's local list must be refused.
        let inbox = install_inbox(&runtime, [0u8; 32]);

        let intent = MailboxTurnIntent {
            target: runtime.cell_id(),
            method: "execute".into(),
            effects: vec![],
        };
        let sealed = seal_intent(&intent, FederationId(a_pk), &b_public, &a_secret, 0);
        let transport = MemTransport {
            pending: vec![delivered(a_pk, sealed.clone())],
        };
        let mut crank = MailboxCrank::new(&runtime, inbox, b_secret, transport);
        crank.senders.insert(a_pk); // unanchored local opening

        let report = crank.crank_once(10).unwrap();
        assert!(matches!(
            report.outcomes[0].disposition,
            CrankDisposition::Refused(RefusalReason::SenderSetRootMismatch)
        ));

        // A non-zero on-cell root that does NOT match the opening also fails.
        let runtime2 = test_runtime("stale-root-2");
        let inbox2 = install_inbox(&runtime2, [0x44; 32]);
        let transport2 = MemTransport {
            pending: vec![delivered(a_pk, sealed)],
        };
        let mut crank2 = MailboxCrank::new(&runtime2, inbox2, b_secret, transport2);
        crank2.senders.insert(a_pk);
        let report2 = crank2.crank_once(10).unwrap();
        assert!(matches!(
            report2.outcomes[0].disposition,
            CrankDisposition::Refused(RefusalReason::SenderSetRootMismatch)
        ));
    }

    #[test]
    fn tampered_payload_is_refused_at_binding() {
        let runtime = test_runtime("tampered");
        let (b_secret, b_public) = generate_x25519_keypair();
        let (a_secret, _) = generate_x25519_keypair();
        let a_pk = [0xA1; 32];

        let mut set = BTreeSet::new();
        set.insert(a_pk);
        let inbox = install_inbox(&runtime, sender_set_commitment(&set));

        let intent = MailboxTurnIntent {
            target: runtime.cell_id(),
            method: "execute".into(),
            effects: vec![],
        };
        let sealed = seal_intent(&intent, FederationId(a_pk), &b_public, &a_secret, 0);
        let mut msg = delivered(a_pk, sealed);
        // Tamper with the body AFTER the content hash was fixed.
        msg.payload[0] ^= 0xFF;

        let transport = MemTransport { pending: vec![msg] };
        let mut crank = MailboxCrank::new(&runtime, inbox, b_secret, transport);
        crank.senders.insert(a_pk);

        let report = crank.crank_once(10).unwrap();
        assert!(matches!(
            report.outcomes[0].disposition,
            CrankDisposition::Refused(RefusalReason::BindingMismatch)
        ));
        // The relay's proof itself was genuine (it covers the content hash,
        // not the body) — the BODY failed to re-hash.
        assert!(crank.receipts()[0].proof_ok);
        assert!(!crank.receipts()[0].payload_binding_ok);
    }

    #[test]
    fn tampered_or_replayed_dequeue_proof_is_refused() {
        let (b_secret, b_public) = generate_x25519_keypair();
        let (a_secret, _) = generate_x25519_keypair();
        let a_pk = [0xA1; 32];

        let intent = |n: u8| MailboxTurnIntent {
            target: CellId::from_bytes([n; 32]),
            method: "execute".into(),
            effects: vec![],
        };
        let seal = |i: &MailboxTurnIntent| {
            seal_intent(i, FederationId(a_pk), &b_public, &a_secret, 0)
        };

        // Tampered post-root → fails the structural verifier.
        let runtime = test_runtime("bad-proof");
        let mut set = BTreeSet::new();
        set.insert(a_pk);
        let inbox = install_inbox(&runtime, sender_set_commitment(&set));
        let mut msg = delivered(a_pk, seal(&intent(1)));
        msg.proof_new_root[0] ^= 0xFF;
        let transport = MemTransport { pending: vec![msg] };
        let mut crank = MailboxCrank::new(&runtime, inbox, b_secret, transport);
        crank.senders.insert(a_pk);
        let report = crank.crank_once(10).unwrap();
        assert!(matches!(
            report.outcomes[0].disposition,
            CrankDisposition::Refused(RefusalReason::CustodyProofInvalid)
        ));
        assert!(!crank.receipts()[0].proof_ok);

        // A chained 2-message batch verifies end-to-end; REPLAYING the first
        // proof as the second fails the `_against` form (stale pre-root) —
        // and the break in the chain refuses everything after it too.
        let runtime2 = test_runtime("replay-proof");
        let inbox2 = install_inbox(&runtime2, sender_set_commitment(&set));
        let batch = deliver_all(vec![
            (a_pk, seal(&intent(2))),
            (a_pk, seal(&intent(3))),
        ]);
        let replayed = batch[0].clone();
        let genuine_second = batch[1].clone();
        let transport2 = MemTransport {
            pending: vec![batch[0].clone(), replayed, genuine_second],
        };
        let mut crank2 = MailboxCrank::new(&runtime2, inbox2, b_secret, transport2);
        crank2.senders.insert(a_pk);
        let report2 = crank2.crank_once(10).unwrap();
        assert!(crank2.receipts()[0].proof_ok, "head proof verifies");
        assert!(matches!(
            report2.outcomes[1].disposition,
            CrankDisposition::Refused(RefusalReason::CustodyProofInvalid)
        ));
        // The genuine second message DOES chain on the (unadvanced) tracked
        // root, so it still verifies after the refused replay.
        assert!(crank2.receipts()[2].proof_ok, "chain resumes on the true successor");
    }

    #[test]
    fn grant_sender_writes_executor_committed_root() {
        let runtime = test_runtime("grant");
        let inbox = install_inbox(&runtime, [0u8; 32]);
        let (b_secret, _) = generate_x25519_keypair();

        let transport = MemTransport { pending: vec![] };
        let mut crank = MailboxCrank::new(&runtime, inbox, b_secret, transport);

        let a_pk = [0xA1; 32];
        crank.grant_sender(a_pk).expect("grant_sender commits");

        let expected = sender_set_commitment(&crank.senders);
        assert_ne!(expected, [0u8; 32]);
        let ledger = runtime.ledger().lock().unwrap();
        assert_eq!(
            ledger.get(&inbox).unwrap().state.fields[SENDER_SET_ROOT_SLOT],
            expected,
            "the executor-committed slot-5 root must equal the crank's opening"
        );
    }
}

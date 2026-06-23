//! The dregg DATA PLANE: a userspace comms API app authors build on.
//!
//! `dregg` is usually described as a *control / auth plane* — caps, attenuation,
//! verified turns, receipts. This module turns that same substrate into a
//! **data plane**: the bus a deos app (or Hermes, or the harness) actually moves
//! work across. It buffs the captp queue / custody / session primitives into one
//! coherent surface:
//!
//!   * **ENQUEUE** a message to a cell's INBOX (the per-recipient
//!     [`crate::store_forward`] `MessageRelay` queue) and get back a signed
//!     **delivery receipt** — the relay's [`crate::custody::CustodyReceipt`].
//!   * be **WOKEN by name** when an inbox advances ([`Waker`] /
//!     [`Bus::poll_wakes`]) — the bb engine's wake/event-notify, but a wake is a
//!     *fact about the queue* (cursor moved), never a forgeable signal.
//!   * **SUBSCRIBE** to an event stream / **TOPIC** and receive fan-out
//!     deliveries ([`Bus::publish`] → every subscriber's inbox), each a real
//!     enqueue with its own receipt.
//!   * **DRAIN** an inbox, which **WITNESSES delivery**: the drain emits the
//!     content hashes that left the queue, and those are exactly what
//!     [`crate::custody::InboxState::from_dequeue`] reads to ACQUIT a relay /
//!     resolve the receipt. So "queued-but-undelivered" is structurally
//!     distinguishable from "drained" — the bb engine's receipt-identity lesson,
//!     made unforgeable. [`Bus::drain_one`] witnesses a SINGLE box (FIFO) so a
//!     delivery path that hands boxes to a consumer one at a time drains the spool
//!     IN LOCKSTEP with delivery — the witness flips as the box reaches the wire,
//!     and the inbox never accumulates a parallel, never-drained backlog.
//!
//! # The north star: buildr's "bb engine", matched and exceeded
//!
//! buildr's fleet voted unanimously to keep one asset: an append-only shared log
//! + wake/spool/event-notify + receipt-identity. dregg has each piece already, in
//! verified form:
//!
//! | bb engine            | dregg substrate                                      |
//! |----------------------|------------------------------------------------------|
//! | append-only log      | the blocklace (`blocklace/`) — the log of record     |
//! | spool / mailbox      | `MessageRelay` per-recipient queue (the inbox)       |
//! | wake / event-notify  | [`Waker`] — cursor-advance is the wake               |
//! | receipt-identity     | `CustodyReceipt` + drain-witness ([`Delivery`])      |
//!
//! Where dregg **exceeds** a plain bb engine — each delivery is a *cap-gated,
//! conserved, verifiable turn*:
//!
//!   1. **You cannot forge a wake.** A wake is minted only when a real enqueue
//!      advanced the cursor; a subscriber cannot fabricate one (it is derived
//!      from the monotone queue depth, not a flag anyone can set).
//!   2. **A receipt is unforgeable.** Only the relay's Ed25519 key produces a
//!      verifying [`CustodyReceipt`]; a dropped delivery is *convictable* and an
//!      honest one *acquitted* (the custody calculus).
//!   3. **Revocation / attenuation apply to channels.** A send capability into an
//!      inbox or topic is an [`AuthRequired`]; an over-attenuated or unauthorized
//!      enqueue is **refused at the seam**, before anything is queued (no receipt
//!      is minted for a refused send — so the ledger never shows phantom work).
//!   4. **No claimed-but-undelivered ambiguity.** The bb engine's hardest-won
//!      lesson: a thing on the spool is NOT a thing handled. Here, "handled" has a
//!      cryptographic witness (the drain-emitted content hash) that is a *separate
//!      object* from "enqueued" (the receipt's promise). [`Delivery::is_handled`]
//!      reads the witness, never the promise.
//!
//! # How it grounds Houyhnhnm IPC
//!
//! This is the realization of the Houyhnhnm "typed channels / implicit + explicit
//! comms / protocols-as-meta-level" chapter: a [`Channel`] is a typed, named,
//! cap-bearing edge; a [`Topic`] is the multi-cast meta-level; the protocol (who
//! may send, with what attenuation, leaving what receipt) is itself first-class
//! data, not convention. See `docs/deos/DREGG-DATA-PLANE.md`.

use std::collections::{BTreeMap, HashMap};

use dregg_cell::AuthRequired;
use dregg_types::SigningKey;
use serde::{Deserialize, Serialize};

use crate::FederationId;
use crate::custody::{CustodyReceipt, InboxState};
use crate::store_forward::{MessageRelay, QueuedMessage};

// =============================================================================
// §1 — Names and channels: the typed, cap-bearing edges of the data plane
// =============================================================================

/// A **channel name** — a stable, human-meaningful handle for a comms edge.
///
/// In bb-engine terms this is the "wake-by-name" key; in Houyhnhnm terms it is
/// the typed-channel label. A name is just bytes (so apps choose their own
/// namespace, e.g. `b"hermes/inbox"`), content-addressed only for the wake table.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ChannelName(pub Vec<u8>);

impl ChannelName {
    /// Construct a name from any byte-ish handle.
    pub fn new(name: impl Into<Vec<u8>>) -> Self {
        ChannelName(name.into())
    }

    /// A short stable key for wake-table indexing (BLAKE3 of the name bytes).
    pub fn key(&self) -> [u8; 32] {
        *blake3::hash(&self.0).as_bytes()
    }
}

/// A **topic name** — the multi-cast meta-level. Publishing to a topic fans the
/// payload out to every [`Bus::subscribe`]r's own inbox (each a real enqueue).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TopicName(pub Vec<u8>);

impl TopicName {
    /// Construct a topic from any byte-ish handle.
    pub fn new(name: impl Into<Vec<u8>>) -> Self {
        TopicName(name.into())
    }
}

/// A **send capability** into a named channel/inbox: the cap-gated edge.
///
/// Holding a `SendCap` is the authority to enqueue to `recipient`'s inbox under
/// channel `name`, at most as broad as `grant`. The data plane checks an offered
/// send against this on every enqueue ([`Bus::enqueue`]); an over-attenuated or
/// mismatched offer is REFUSED before anything is queued — the channel-level
/// realization of dregg attenuation/revocation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SendCap {
    /// The inbox owner this cap can enqueue toward.
    pub recipient: FederationId,
    /// The channel name this cap is scoped to.
    pub name: ChannelName,
    /// The authority level granted to a holder of this cap. An offered send must
    /// be *narrower-or-equal* to this to be admitted.
    pub grant: AuthRequired,
    /// If `true`, the cap has been REVOKED and no send through it is admitted
    /// (the channel-level revocation switch).
    pub revoked: bool,
}

impl SendCap {
    /// Mint a fresh, non-revoked send capability.
    pub fn grant(recipient: FederationId, name: ChannelName, grant: AuthRequired) -> Self {
        Self {
            recipient,
            name,
            grant,
            revoked: false,
        }
    }

    /// **Attenuate** this cap to a narrower authority, producing a new cap. Returns
    /// `None` if `narrower` is not actually narrower-or-equal to this cap's grant
    /// (you cannot *amplify* by calling attenuate — the non-amplification tooth).
    pub fn attenuate(&self, narrower: AuthRequired) -> Option<SendCap> {
        if narrower.is_narrower_or_equal(&self.grant) {
            Some(SendCap {
                recipient: self.recipient,
                name: self.name.clone(),
                grant: narrower,
                revoked: self.revoked,
            })
        } else {
            None
        }
    }

    /// Revoke this cap (idempotent). After revocation no send through it is admitted.
    pub fn revoke(&mut self) {
        self.revoked = true;
    }

    /// Does an `offered` authority pass the gate of this cap for this `(recipient,
    /// name)`? The send is admitted IFF the cap is live, addresses the right
    /// recipient+channel, and the offered authority is narrower-or-equal to the
    /// grant. This is the single seam an enqueue must pass.
    pub fn admits(
        &self,
        recipient: &FederationId,
        name: &ChannelName,
        offered: &AuthRequired,
    ) -> bool {
        !self.revoked
            && self.recipient == *recipient
            && self.name == *name
            && offered.is_narrower_or_equal(&self.grant)
    }
}

// =============================================================================
// §2 — Errors
// =============================================================================

/// Why a data-plane operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DataPlaneError {
    /// The offered send was not admitted by the cap (revoked, wrong
    /// recipient/channel, or over-broad authority). No message was queued and NO
    /// receipt was minted — a refused send leaves no phantom work.
    Unauthorized {
        /// The recipient the refused send targeted.
        recipient: FederationId,
    },
    /// The underlying relay refused the enqueue (queue/storage full, bad TTL).
    Relay(crate::store_forward::RelayError),
    /// No such topic is registered (publish/subscribe to an unknown topic).
    NoSuchTopic(TopicName),
    /// No inbox exists for this recipient yet (drain/wake on an empty name).
    NoSuchInbox(FederationId),
}

impl std::fmt::Display for DataPlaneError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DataPlaneError::Unauthorized { recipient } => {
                write!(f, "send refused: cap does not admit enqueue to {recipient}")
            }
            DataPlaneError::Relay(e) => write!(f, "relay refused enqueue: {e}"),
            DataPlaneError::NoSuchTopic(t) => write!(f, "no such topic: {t:?}"),
            DataPlaneError::NoSuchInbox(r) => write!(f, "no inbox for {r}"),
        }
    }
}

impl std::error::Error for DataPlaneError {}

// =============================================================================
// §3 — Delivery: the receipt-identity object (the bb engine's lesson, unforgeable)
// =============================================================================

/// A **delivery handle** — the object that distinguishes "queued" from "handled".
///
/// An [`Bus::enqueue`] returns a `Delivery` carrying:
///   * `receipt` — the relay's signed *promise* ([`CustodyReceipt`]) that this box
///     (by `content_hash`) is in the inbox and will be delivered or refunded.
///   * `content_hash` — the content-address of the enqueued box (the identity the
///     drain will later witness).
///
/// Crucially the *promise* (receipt) and the *witness* (a later drain that emits
/// `content_hash`) are SEPARATE objects. [`Delivery::is_handled`] consults the
/// witness, never the promise: a thing on the spool is not a thing handled — the
/// bb-engine receipt-identity invariant, here cryptographic.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Delivery {
    /// The relay's signed delivery promise for this enqueue.
    pub receipt: CustodyReceipt,
    /// The content-address of the enqueued box (what a drain witnesses).
    pub content_hash: [u8; 32],
}

impl Delivery {
    /// **Is this delivery actually handled?** Reads the drain-witness, NOT the
    /// promise. `delivered_content_hashes` is the inbox cell's authenticated record
    /// of boxes that left the queue toward the recipient (each drain appends to it
    /// — see [`Bus::drain`]). Returns `true` IFF THIS box's `content_hash` is among
    /// them. This is the structural separation of "queued" from "handled":
    /// possessing the receipt does NOT make `is_handled` true.
    pub fn is_handled(&self, delivered_content_hashes: &[[u8; 32]]) -> bool {
        delivered_content_hashes.contains(&self.content_hash)
    }

    /// The inbox state THIS delivery would adjudicate against, built
    /// content-address-honestly from the cell's delivered-hash log. The drop /
    /// acquit verdict for this receipt is then [`crate::custody::adjudicate_from_inbox`].
    pub fn inbox_state(
        &self,
        delivered_content_hashes: &[[u8; 32]],
        root: [u8; 32],
        refund_recorded: bool,
    ) -> InboxState {
        InboxState::from_dequeue(&self.receipt, delivered_content_hashes, root, refund_recorded)
    }
}

// =============================================================================
// §4 — Waker: wake-by-name, where a wake is a FACT about the queue
// =============================================================================

/// A **wake** — the event-notify signal that a named inbox advanced.
///
/// A wake is *derived*, never *asserted*: it is minted only when an enqueue moved
/// the inbox's monotone cursor forward. A subscriber cannot forge one (there is no
/// public setter; [`Bus`] mints it from the real depth change). This is the
/// bb-engine wake/event-notify, hardened: the cursor is the truth.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Wake {
    /// The cursor value the inbox advanced TO (monotone; the count of boxes ever
    /// enqueued to this name). A waiter that last saw `cursor = n` is woken whenever
    /// the live cursor exceeds `n`.
    pub cursor: u64,
}

/// The wake table: per-channel monotone cursors + per-waiter last-seen marks.
///
/// `cursors[name]` only ever increases (one tick per admitted enqueue). A
/// registered waiter is "pending" exactly when the live cursor exceeds its
/// last-seen mark — so a wake cannot be faked (no enqueue ⇒ no cursor move ⇒ no
/// wake) and cannot be lost (the mark persists until the waiter acknowledges).
#[derive(Clone, Debug, Default)]
pub struct Waker {
    /// Monotone enqueue cursor per channel key.
    cursors: HashMap<[u8; 32], u64>,
    /// Per-waiter (keyed by `(channel key, waiter id)`) last-acknowledged cursor.
    marks: HashMap<([u8; 32], FederationId), u64>,
}

impl Waker {
    /// Fresh wake table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Tick the cursor for a channel (called by [`Bus`] on an admitted enqueue).
    /// Returns the new cursor value. This is the ONLY way a cursor advances —
    /// there is no setter that fakes one.
    fn tick(&mut self, key: [u8; 32]) -> u64 {
        let c = self.cursors.entry(key).or_insert(0);
        *c += 1;
        *c
    }

    /// The live cursor for a channel (0 if never enqueued).
    pub fn cursor(&self, name: &ChannelName) -> u64 {
        self.cursors.get(&name.key()).copied().unwrap_or(0)
    }

    /// Register a waiter on a channel: it will be woken when the cursor advances
    /// past the current value. Marks its last-seen at the current cursor.
    pub fn wait(&mut self, name: &ChannelName, waiter: FederationId) {
        let key = name.key();
        let cur = self.cursors.get(&key).copied().unwrap_or(0);
        self.marks.insert((key, waiter), cur);
    }

    /// Poll a waiter: returns `Some(Wake)` if the channel cursor advanced past the
    /// waiter's last-seen mark, else `None`. Does NOT consume the wake (idempotent
    /// read); call [`Self::acknowledge`] after handling to advance the mark.
    pub fn poll(&self, name: &ChannelName, waiter: &FederationId) -> Option<Wake> {
        let key = name.key();
        let cur = self.cursors.get(&key).copied().unwrap_or(0);
        let seen = self.marks.get(&(key, *waiter)).copied().unwrap_or(0);
        if cur > seen {
            Some(Wake { cursor: cur })
        } else {
            None
        }
    }

    /// Acknowledge wakes up to `cursor` for a waiter (advance its mark). After
    /// this, [`Self::poll`] returns `None` until the cursor advances again.
    pub fn acknowledge(&mut self, name: &ChannelName, waiter: FederationId, cursor: u64) {
        let key = name.key();
        let mark = self.marks.entry((key, waiter)).or_insert(0);
        if cursor > *mark {
            *mark = cursor;
        }
    }
}

// =============================================================================
// §5 — Bus: the userspace data-plane API a deos app holds
// =============================================================================

/// The **data-plane bus** — the one object an app (deos surface, Hermes, the
/// harness) uses to move work. It owns:
///   * a [`MessageRelay`] (the per-recipient inboxes / spool),
///   * a [`Waker`] (wake-by-name / event-notify),
///   * the topic→subscriber table (pub/sub fan-out),
///   * per-inbox delivery-witness logs (the receipt-identity ledger).
///
/// Every op is cap-gated ([`SendCap`]) and receipted ([`Delivery`]). The relay's
/// signing identity (`relay_id` / `relay_key`) signs custody receipts so a drop is
/// convictable and an honest delivery acquitted.
#[derive(Clone, Debug)]
pub struct Bus {
    /// The relay holding per-recipient inbox queues (the spool).
    relay: MessageRelay,
    /// The relay's accountable identity (its `FederationId` IS its pubkey).
    relay_id: FederationId,
    /// The relay's Ed25519 signing key (signs custody receipts).
    relay_key: SigningKey,
    /// Wake-by-name table.
    waker: Waker,
    /// topic → set of subscriber inboxes (pub/sub fan-out).
    topics: BTreeMap<TopicName, Vec<FederationId>>,
    /// Per-recipient append-only log of delivered (drained) content hashes — the
    /// authenticated witness the custody adjudicator reads. "Handled" lives here;
    /// "queued" lives in the relay. Their separation IS receipt-identity.
    delivered: HashMap<FederationId, Vec<[u8; 32]>>,
    /// Per-recipient monotone inbox root (advances on enqueue; carried in receipts).
    roots: HashMap<FederationId, [u8; 32]>,
    /// Default TTL (in blocks) applied to enqueued boxes.
    default_ttl: u64,
    /// Default deadline horizon (blocks past `now`) for custody `accept_by`.
    default_deadline: u64,
}

impl Bus {
    /// Create a bus with the relay's accountable identity + signing key and the
    /// relay storage limits. `relay_id` MUST be the pubkey matching `relay_key`
    /// (else minted receipts will not verify — the custody binding).
    pub fn new(
        relay_id: FederationId,
        relay_key: SigningKey,
        max_queue_depth: usize,
        max_total_messages: usize,
    ) -> Self {
        Self {
            relay: MessageRelay::new(max_queue_depth, max_total_messages),
            relay_id,
            relay_key,
            waker: Waker::new(),
            topics: BTreeMap::new(),
            delivered: HashMap::new(),
            roots: HashMap::new(),
            default_ttl: 1_000,
            default_deadline: 100,
        }
    }

    /// Set the default TTL (blocks) for enqueued boxes (builder-style).
    pub fn with_default_ttl(mut self, ttl: u64) -> Self {
        self.default_ttl = ttl;
        self
    }

    /// Set the default custody deadline horizon (blocks past `now`).
    pub fn with_default_deadline(mut self, deadline: u64) -> Self {
        self.default_deadline = deadline;
        self
    }

    /// The current monotone inbox root for a recipient (zero if never enqueued).
    fn root_of(&self, recipient: &FederationId) -> [u8; 32] {
        self.roots.get(recipient).copied().unwrap_or([0u8; 32])
    }

    /// Advance a recipient's monotone inbox root by folding in a content hash. The
    /// root is `H(old_root || content_hash)` — strictly monotone (a fresh hash each
    /// enqueue) so it never retreats, matching the custody adjudicator's assumption.
    fn advance_root(&mut self, recipient: FederationId, content_hash: &[u8; 32]) -> [u8; 32] {
        let old = self.root_of(&recipient);
        let mut h = blake3::Hasher::new();
        h.update(&old);
        h.update(content_hash);
        let new = *h.finalize().as_bytes();
        self.roots.insert(recipient, new);
        new
    }

    // -------------------------------------------------------------------------
    // (a) ENQUEUE — put work into a cell's inbox, with a delivery RECEIPT
    // -------------------------------------------------------------------------

    /// **ENQUEUE** a payload to `recipient`'s inbox under channel `name`, gated by
    /// `cap` at authority `offered`, returning a signed [`Delivery`].
    ///
    /// The seam: the send is admitted only if `cap.admits(recipient, name, offered)`
    /// — live cap, right recipient+channel, offered authority narrower-or-equal to
    /// the grant. If refused, [`DataPlaneError::Unauthorized`] is returned and
    /// **nothing is queued and no receipt is minted** (a refused send leaves no
    /// phantom work — the receipt-identity ledger never shows it).
    ///
    /// On admission: the box is enqueued on the relay, the inbox root advances, the
    /// relay SIGNS a [`CustodyReceipt`] over `(content_hash, recipient, old→new
    /// root, accept_by)`, and the channel's wake cursor ticks (so waiters are
    /// woken). The returned `Delivery` is the *promise*; handling is later
    /// witnessed by [`Self::drain`].
    pub fn enqueue(
        &mut self,
        cap: &SendCap,
        recipient: FederationId,
        name: &ChannelName,
        offered: AuthRequired,
        payload: Vec<u8>,
        now: u64,
    ) -> Result<Delivery, DataPlaneError> {
        // THE GATE: refuse over-attenuated / forged / revoked sends BEFORE queuing.
        if !cap.admits(&recipient, name, &offered) {
            return Err(DataPlaneError::Unauthorized { recipient });
        }

        // Content-address the box exactly as the relay/receipt commit to it.
        let content_hash = *blake3::hash(&payload).as_bytes();

        let old_root = self.root_of(&recipient);
        let accept_by = now.saturating_add(self.default_deadline);

        // The causal sequence of THIS box is the cursor value it ticks the
        // channel TO — the post-tick value, so the queued message's sequence and
        // the wake cursor a waiter observes for it agree (the first admitted
        // enqueue is causal_sequence 1, matching `cursor == 1`). Reading the
        // pre-tick cursor here desynchronized the two by one.
        let causal_sequence = self.waker.cursor(name).saturating_add(1);
        let msg = QueuedMessage {
            destination: recipient,
            encrypted_payload: payload,
            sender_ephemeral_pk: [0u8; 32],
            causal_sequence,
            queued_at: now,
            ttl_blocks: self.default_ttl,
            priority: crate::store_forward::MessagePriority::Normal,
        };

        // Enqueue first; only mint a receipt + tick the cursor if custody was taken.
        self.relay.enqueue(msg).map_err(DataPlaneError::Relay)?;

        let new_root = self.advance_root(recipient, &content_hash);
        let receipt = CustodyReceipt::sign(
            self.relay_id,
            &self.relay_key,
            content_hash,
            recipient,
            old_root,
            new_root,
            accept_by,
        );

        // Wake-by-name: the cursor advances exactly once per admitted enqueue, to
        // the value `causal_sequence` recorded above.
        let ticked = self.waker.tick(name.key());
        debug_assert_eq!(
            ticked, causal_sequence,
            "the queued box's causal_sequence must equal the cursor it ticked to"
        );

        Ok(Delivery {
            receipt,
            content_hash,
        })
    }

    // -------------------------------------------------------------------------
    // (b) WAKE — be woken by name when an inbox advances
    // -------------------------------------------------------------------------

    /// **WAIT** to be woken on a channel: registers `waiter` so a future enqueue to
    /// `name` produces a pending wake ([`Self::poll_wake`]).
    pub fn wait(&mut self, name: &ChannelName, waiter: FederationId) {
        self.waker.wait(name, waiter);
    }

    /// **POLL** for a wake on a channel: `Some(Wake)` if the cursor advanced past
    /// the waiter's last-seen mark. The wake is a fact (cursor moved), unforgeable.
    pub fn poll_wake(&self, name: &ChannelName, waiter: &FederationId) -> Option<Wake> {
        self.waker.poll(name, waiter)
    }

    /// Acknowledge wakes up to `cursor` (advance the waiter's mark).
    pub fn acknowledge_wake(&mut self, name: &ChannelName, waiter: FederationId, cursor: u64) {
        self.waker.acknowledge(name, waiter, cursor);
    }

    /// The live wake cursor for a channel (count of admitted enqueues).
    pub fn cursor(&self, name: &ChannelName) -> u64 {
        self.waker.cursor(name)
    }

    // -------------------------------------------------------------------------
    // (c) SUBSCRIBE / PUBLISH — pub/sub topic fan-out
    // -------------------------------------------------------------------------

    /// Register a topic (idempotent). Apps may publish to it once registered.
    pub fn register_topic(&mut self, topic: TopicName) {
        self.topics.entry(topic).or_default();
    }

    /// **SUBSCRIBE** `subscriber`'s inbox to a topic (auto-registers the topic).
    /// A subsequent [`Self::publish`] fans the payload out to this subscriber's
    /// inbox as a real enqueue with its own receipt.
    pub fn subscribe(&mut self, topic: TopicName, subscriber: FederationId) {
        let subs = self.topics.entry(topic).or_default();
        if !subs.contains(&subscriber) {
            subs.push(subscriber);
        }
    }

    /// Unsubscribe a subscriber from a topic.
    pub fn unsubscribe(&mut self, topic: &TopicName, subscriber: &FederationId) {
        if let Some(subs) = self.topics.get_mut(topic) {
            subs.retain(|s| s != subscriber);
        }
    }

    /// **PUBLISH** a payload to a topic: fan it out to EVERY subscriber's inbox,
    /// one real cap-gated enqueue + receipt per subscriber, woken by name.
    ///
    /// The publisher presents a `cap` whose `name` is the per-subscriber channel
    /// used for the fan-out (so the same attenuation/revocation discipline governs
    /// a broadcast as a unicast). The channel name for each subscriber's delivery
    /// is the topic-scoped name `cap.name`; a subscriber waits on that name to be
    /// woken on publish. Returns one [`Delivery`] per subscriber that admitted the
    /// send. Subscribers the cap does not admit are silently skipped (the cap may
    /// be scoped to a subset; an unauthorized fan-out target is simply not served).
    pub fn publish(
        &mut self,
        topic: &TopicName,
        cap: &SendCap,
        offered: AuthRequired,
        payload: Vec<u8>,
        now: u64,
    ) -> Result<Vec<(FederationId, Delivery)>, DataPlaneError> {
        let subs = self
            .topics
            .get(topic)
            .ok_or_else(|| DataPlaneError::NoSuchTopic(topic.clone()))?
            .clone();

        let name = cap.name.clone();
        let mut out = Vec::with_capacity(subs.len());
        for sub in subs {
            // Per-subscriber cap: same grant, re-pointed at this subscriber. The
            // publisher's cap must admit this (sub) under the topic channel name.
            let sub_cap = SendCap {
                recipient: sub,
                name: name.clone(),
                grant: cap.grant.clone(),
                revoked: cap.revoked,
            };
            match self.enqueue(&sub_cap, sub, &name, offered.clone(), payload.clone(), now) {
                Ok(d) => out.push((sub, d)),
                Err(DataPlaneError::Unauthorized { .. }) => { /* skip unauthorized target */ }
                Err(e) => return Err(e),
            }
        }
        Ok(out)
    }

    /// Current subscribers of a topic (empty if unregistered).
    pub fn subscribers(&self, topic: &TopicName) -> &[FederationId] {
        self.topics.get(topic).map_or(&[], |v| v.as_slice())
    }

    // -------------------------------------------------------------------------
    // (d) DRAIN — drain the inbox, WITNESSING delivery (the custody receipt resolves)
    // -------------------------------------------------------------------------

    /// **DRAIN** `recipient`'s inbox: return the queued boxes (FIFO) AND record
    /// their content hashes in the recipient's authenticated delivery-witness log.
    ///
    /// THIS is where "queued" becomes "handled": each drained box's `content_hash`
    /// is appended to [`Self::delivered_hashes`], the sticky, content-addressed
    /// witness the custody adjudicator reads. After a drain, the matching
    /// [`Delivery::is_handled`] flips to `true` and the relay is ACQUITTED for that
    /// box; a box that was never drained leaves the witness unset (its relay
    /// convictable past the deadline). The separation is the receipt-identity teeth.
    pub fn drain(&mut self, recipient: &FederationId) -> Vec<QueuedMessage> {
        let drained = self.relay.drain(recipient);
        if !drained.is_empty() {
            let log = self.delivered.entry(*recipient).or_default();
            for m in &drained {
                let ch = *blake3::hash(&m.encrypted_payload).as_bytes();
                log.push(ch);
            }
        }
        drained
    }

    /// **DRAIN ONE** box (FIFO) from `recipient`'s inbox, WITNESSING that single
    /// delivery: the popped box's content hash is appended to the delivery-witness
    /// log exactly as [`Self::drain`] would, so the matching [`Delivery::is_handled`]
    /// flips to `true`. `None` if the inbox is empty.
    ///
    /// This is the lockstep companion to a delivery path that hands boxes to a
    /// consumer one at a time (e.g. an SSE stream): each delivered box witnesses
    /// its own drain, so the spool drains AS it delivers — it never accumulates a
    /// parallel, never-drained backlog. "Delivered on the wire" == "drained-witnessed
    /// on the Bus", box for box.
    pub fn drain_one(&mut self, recipient: &FederationId) -> Option<QueuedMessage> {
        let msg = self.relay.drain_one(recipient)?;
        let ch = *blake3::hash(&msg.encrypted_payload).as_bytes();
        self.delivered.entry(*recipient).or_default().push(ch);
        Some(msg)
    }

    /// The recipient's authenticated log of delivered (drained) content hashes —
    /// the witness `Delivery::is_handled` / the custody adjudicator reads. Append
    /// only; sticky once a box is drained.
    pub fn delivered_hashes(&self, recipient: &FederationId) -> &[[u8; 32]] {
        self.delivered.get(recipient).map_or(&[], |v| v.as_slice())
    }

    /// How many boxes are pending (queued, not yet drained) for a recipient.
    pub fn pending_count(&self, recipient: &FederationId) -> usize {
        self.relay.pending_count(recipient)
    }

    /// The recipient's monotone inbox root (carried in receipts; for adjudication).
    pub fn inbox_root(&self, recipient: &FederationId) -> [u8; 32] {
        self.root_of(recipient)
    }
}

// =============================================================================
// §6 — Tests: the bb-engine parity teeth + the receipt-identity proof
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::custody::adjudicate_from_inbox;
    use crate::custody::{CustodyOutcome, EvidenceOfDrop};
    use dregg_types::generate_keypair;

    /// A relay identity whose FederationId IS its Ed25519 pubkey (custody binding).
    fn relay_identity() -> (FederationId, SigningKey) {
        let (sk, pk) = generate_keypair();
        (FederationId(pk.0), sk)
    }

    fn app_b() -> FederationId {
        FederationId([0xBB; 32])
    }

    fn fresh_bus() -> (Bus, FederationId) {
        let (relay_id, relay_key) = relay_identity();
        (Bus::new(relay_id, relay_key, 1024, 65536), relay_id)
    }

    fn inbox_cap(recipient: FederationId, name: &ChannelName) -> SendCap {
        SendCap::grant(recipient, name.clone(), AuthRequired::Signature)
    }

    // ── (1) THE HEADLINE: A enqueues → B woken → B drains → receipt witnesses ──
    #[test]
    fn enqueue_wake_drain_witness_lifecycle() {
        let (mut bus, _relay) = fresh_bus();
        let b = app_b();
        let name = ChannelName::new(b"app-b/inbox");
        let cap = inbox_cap(b, &name);

        // B registers to be woken by name.
        bus.wait(&name, b);
        assert!(bus.poll_wake(&name, &b).is_none(), "no wake before any enqueue");

        // A enqueues work to B's inbox; gets a signed delivery promise.
        let delivery = bus
            .enqueue(&cap, b, &name, AuthRequired::Signature, b"do-the-thing".to_vec(), 10)
            .expect("authorized enqueue admitted");
        assert!(delivery.receipt.sig_verifies(), "receipt is a real signature");

        // B is WOKEN by name (the cursor advanced — an unforgeable fact).
        let wake = bus.poll_wake(&name, &b).expect("B is woken on enqueue");
        assert_eq!(wake.cursor, 1);

        // RECEIPT-IDENTITY, before drain: queued is NOT handled.
        assert_eq!(bus.pending_count(&b), 1);
        assert!(
            !delivery.is_handled(bus.delivered_hashes(&b)),
            "a thing on the spool is NOT a thing handled"
        );

        // B drains → delivery is WITNESSED.
        let drained = bus.drain(&b);
        assert_eq!(drained.len(), 1);
        assert_eq!(drained[0].encrypted_payload, b"do-the-thing");
        assert_eq!(bus.pending_count(&b), 0);

        // RECEIPT-IDENTITY, after drain: handled is now true, and distinguishable
        // from the pre-drain state (the whole bb-engine lesson).
        assert!(
            delivery.is_handled(bus.delivered_hashes(&b)),
            "drained ⇒ handled (the witness, not the promise)"
        );

        // The custody adjudicator AGREES: a delivered box ACQUITS the relay.
        let inbox = delivery.inbox_state(bus.delivered_hashes(&b), bus.inbox_root(&b), false);
        let dispute = EvidenceOfDrop::from_receipt(delivery.receipt.clone());
        assert!(
            !adjudicate_from_inbox(&dispute, &inbox),
            "a witnessed delivery is provably acquitted"
        );
        assert!(matches!(
            inbox.true_outcome(&delivery.receipt),
            CustodyOutcome::Delivered { .. }
        ));

        // B acknowledges the wake; no further wake until the next enqueue.
        bus.acknowledge_wake(&name, b, wake.cursor);
        assert!(bus.poll_wake(&name, &b).is_none(), "wake consumed after ack");
    }

    // ── (2) RECEIPT-IDENTITY, the convict polarity: never drained ⇒ convictable ──
    #[test]
    fn undrained_is_distinguishable_and_convictable() {
        let (mut bus, _relay) = fresh_bus();
        let b = app_b();
        let name = ChannelName::new(b"app-b/inbox");
        let cap = inbox_cap(b, &name);

        let delivery = bus
            .enqueue(&cap, b, &name, AuthRequired::Signature, b"unhandled-work".to_vec(), 10)
            .unwrap();

        // Never drained: NOT handled, and past the deadline the relay is CONVICTABLE
        // — the unambiguous "queued-but-undelivered" state the bb engine demands be
        // distinct from "handled".
        assert!(!delivery.is_handled(bus.delivered_hashes(&b)));
        let inbox = delivery.inbox_state(bus.delivered_hashes(&b), bus.inbox_root(&b), false);
        assert_eq!(
            inbox.true_outcome(&delivery.receipt),
            CustodyOutcome::Dropped
        );
        let dispute = EvidenceOfDrop::from_receipt(delivery.receipt.clone());
        assert!(dispute.well_formed());
        assert!(
            adjudicate_from_inbox(&dispute, &inbox),
            "queued-but-never-drained is provably a drop (no false 'handled')"
        );

        // Now drain: the SAME delivery flips to handled + acquitted. The two states
        // are genuinely distinct objects, never confused.
        bus.drain(&b);
        let inbox2 = delivery.inbox_state(bus.delivered_hashes(&b), bus.inbox_root(&b), false);
        assert!(delivery.is_handled(bus.delivered_hashes(&b)));
        assert!(!adjudicate_from_inbox(&dispute, &inbox2));
    }

    // ── (3) PUB/SUB: a publish fans a delivery to N subscribers ──────────────────
    #[test]
    fn pubsub_fans_to_n_subscribers() {
        let (mut bus, _relay) = fresh_bus();
        let topic = TopicName::new(b"weather");
        let name = ChannelName::new(b"weather/feed");

        let subs: Vec<FederationId> = (0..5u8).map(|i| FederationId([i; 32])).collect();
        for s in &subs {
            bus.subscribe(topic.clone(), *s);
            bus.wait(&name, *s);
        }
        assert_eq!(bus.subscribers(&topic).len(), 5);

        // Publish once → fans to all 5, each a real enqueue + receipt.
        let cap = SendCap::grant(subs[0], name.clone(), AuthRequired::Signature);
        let deliveries = bus
            .publish(&topic, &cap, AuthRequired::Signature, b"storm-incoming".to_vec(), 7)
            .unwrap();
        assert_eq!(deliveries.len(), 5, "fan-out reached every subscriber");

        // Every subscriber is woken and can drain a real copy, each receipt verifies.
        for (sub, delivery) in &deliveries {
            assert!(delivery.receipt.sig_verifies());
            assert!(bus.poll_wake(&name, sub).is_some(), "subscriber woken on publish");
            assert_eq!(bus.pending_count(sub), 1);
            let drained = bus.drain(sub);
            assert_eq!(drained.len(), 1);
            assert_eq!(drained[0].encrypted_payload, b"storm-incoming");
            assert!(
                delivery.is_handled(bus.delivered_hashes(sub)),
                "each fan-out delivery is independently witnessed"
            );
        }
    }

    // ── (4) NON-AMP: an over-attenuated / unauthorized enqueue is REFUSED ────────
    #[test]
    fn over_attenuated_enqueue_refused_no_phantom_work() {
        let (mut bus, _relay) = fresh_bus();
        let b = app_b();
        let name = ChannelName::new(b"app-b/inbox");

        // The cap grants only Signature-level authority into this channel.
        let cap = SendCap::grant(b, name.clone(), AuthRequired::Signature);

        // Offering a BROADER authority (None ⊋ Signature) is refused at the seam.
        let refused = bus.enqueue(&cap, b, &name, AuthRequired::None, b"forge".to_vec(), 1);
        assert!(
            matches!(refused, Err(DataPlaneError::Unauthorized { .. })),
            "an over-broad (under-attenuated) send is refused"
        );

        // RECEIPT-IDENTITY: a refused send leaves NO phantom work — nothing queued,
        // no cursor tick, no receipt.
        assert_eq!(bus.pending_count(&b), 0, "nothing queued for a refused send");
        assert_eq!(bus.cursor(&name), 0, "no wake cursor tick for a refused send");

        // Wrong channel name is also refused.
        let other = ChannelName::new(b"someone-else/inbox");
        let wrong_chan = bus.enqueue(&cap, b, &other, AuthRequired::Signature, b"x".to_vec(), 1);
        assert!(matches!(wrong_chan, Err(DataPlaneError::Unauthorized { .. })));

        // A REVOKED cap admits nothing (channel-level revocation).
        let mut revoked = cap.clone();
        revoked.revoke();
        let after_revoke =
            bus.enqueue(&revoked, b, &name, AuthRequired::Signature, b"y".to_vec(), 1);
        assert!(matches!(after_revoke, Err(DataPlaneError::Unauthorized { .. })));
        assert_eq!(bus.pending_count(&b), 0);

        // A correctly-attenuated (narrower) send IS admitted: the attenuate path is
        // not vacuously closed.
        let narrower = SendCap::grant(b, name.clone(), AuthRequired::Either);
        // Either grant admits a narrower Signature offer.
        let ok = bus.enqueue(&narrower, b, &name, AuthRequired::Signature, b"ok".to_vec(), 1);
        assert!(ok.is_ok(), "a within-grant send is admitted (gate not vacuous)");
        assert_eq!(bus.cursor(&name), 1);
    }

    // ── (5) ATTENUATE: the cap algebra is non-amplifying ─────────────────────────
    #[test]
    fn cap_attenuation_cannot_amplify() {
        let b = app_b();
        let name = ChannelName::new(b"c");
        let either = SendCap::grant(b, name.clone(), AuthRequired::Either);

        // Narrowing Either → Signature succeeds.
        let narrowed = either.attenuate(AuthRequired::Signature).expect("narrowing allowed");
        assert_eq!(narrowed.grant, AuthRequired::Signature);

        // Trying to widen Signature → Either (or None) FAILS (no amplification).
        assert!(narrowed.attenuate(AuthRequired::Either).is_none(), "cannot widen back");
        assert!(narrowed.attenuate(AuthRequired::None).is_none(), "cannot widen to None");

        // An attenuated cap still admits within its narrowed grant.
        assert!(narrowed.admits(&b, &name, &AuthRequired::Signature));
        // …but not a broader offer than its narrowed grant.
        assert!(!narrowed.admits(&b, &name, &AuthRequired::None));
    }

    // ── (6) WAKE is a FACT: no enqueue ⇒ no wake; only the cursor speaks ──────────
    #[test]
    fn wake_cannot_be_forged() {
        let (mut bus, _relay) = fresh_bus();
        let b = app_b();
        let name = ChannelName::new(b"n");
        bus.wait(&name, b);

        // No enqueue has happened: there is no pending wake, and there is no API to
        // assert one (a wake is derived from the monotone cursor only).
        assert!(bus.poll_wake(&name, &b).is_none());
        assert_eq!(bus.cursor(&name), 0);

        // An enqueue (the ONLY way the cursor moves) produces exactly one wake step.
        let cap = inbox_cap(b, &name);
        bus.enqueue(&cap, b, &name, AuthRequired::Signature, b"m".to_vec(), 1).unwrap();
        assert_eq!(bus.cursor(&name), 1);
        assert_eq!(bus.poll_wake(&name, &b).unwrap().cursor, 1);
    }

    // ── (7b) The queued box's causal_sequence == the wake cursor it ticked to ────
    #[test]
    fn queued_sequence_matches_wake_cursor() {
        let (mut bus, _relay) = fresh_bus();
        let b = app_b();
        let name = ChannelName::new(b"app-b/inbox");
        let cap = inbox_cap(b, &name);
        bus.wait(&name, b);

        // First enqueue: the box's causal_sequence and the cursor a waiter sees
        // are BOTH 1 (no off-by-one between the queued sequence and the wake).
        bus.enqueue(&cap, b, &name, AuthRequired::Signature, b"first".to_vec(), 1)
            .unwrap();
        assert_eq!(bus.cursor(&name), 1, "the wake cursor is 1 after one enqueue");
        let wake = bus.poll_wake(&name, &b).expect("woken");
        assert_eq!(wake.cursor, 1);

        // Enqueue twice more, then drain and read the queued sequences directly:
        // they must be exactly 1,2,3 — the same numbers the cursor reports.
        bus.enqueue(&cap, b, &name, AuthRequired::Signature, b"second".to_vec(), 1)
            .unwrap();
        bus.enqueue(&cap, b, &name, AuthRequired::Signature, b"third".to_vec(), 1)
            .unwrap();
        assert_eq!(bus.cursor(&name), 3);
        let drained = bus.drain(&b);
        let seqs: Vec<u64> = drained.iter().map(|m| m.causal_sequence).collect();
        assert_eq!(
            seqs,
            vec![1, 2, 3],
            "queued causal_sequence agrees with the wake cursor (no off-by-one)"
        );
    }

    // ── (7) Many enqueues, one waiter: wakes coalesce to the live cursor ─────────
    #[test]
    fn multiple_enqueues_coalesce_wake_to_cursor() {
        let (mut bus, _relay) = fresh_bus();
        let b = app_b();
        let name = ChannelName::new(b"busy");
        let cap = inbox_cap(b, &name);
        bus.wait(&name, b);

        for i in 0..3 {
            bus.enqueue(&cap, b, &name, AuthRequired::Signature, vec![i], 1).unwrap();
        }
        // A single poll reflects the live cursor (3), not three separate signals —
        // the waiter drains all pending work in one wake (spool semantics).
        assert_eq!(bus.poll_wake(&name, &b).unwrap().cursor, 3);
        assert_eq!(bus.pending_count(&b), 3);

        // After ack at 3, no further wake until a new enqueue.
        bus.acknowledge_wake(&name, b, 3);
        assert!(bus.poll_wake(&name, &b).is_none());
        bus.enqueue(&cap, b, &name, AuthRequired::Signature, vec![9], 1).unwrap();
        assert_eq!(bus.poll_wake(&name, &b).unwrap().cursor, 4);
    }

    // ── (8) THE SPINE: a real multi-party flow rides the Bus end to end ──────────
    //
    // One producer, TWO subscribers, ONE unauthorized send refused, three ordered
    // publishes — and the four spine properties asserted with REAL receipts:
    //
    //   (a) receipt-identity: each admitted enqueue leaves a verifying CustodyReceipt
    //       AND the chain is tamper-evident (mutating any committed field breaks the
    //       signature) AND the inbox root chains old→new across the run;
    //   (b) cap-gated enqueue: an over-authorized publish target is refused at the
    //       `admits` seam — no box, no cursor tick, no receipt (no phantom work);
    //   (c) ordered pub-sub delivery: each of the two subscribers receives every
    //       payload, in causal (FIFO publish) order, by name;
    //   (d) drain lockstep: lockstep `drain_one` hands boxes out one at a time with
    //       no off-by-one and no double-delivery; a re-drain past empty yields none.
    #[test]
    fn bus_is_the_spine_multiparty_flow_with_four_properties() {
        let (mut bus, _relay) = fresh_bus();
        let topic = TopicName::new(b"orders");
        let name = ChannelName::new(b"orders/feed");

        // Two subscribers ride the Bus; each waits by name.
        let sub_a = FederationId([0xA1; 32]);
        let sub_b = FederationId([0xB2; 32]);
        for s in [sub_a, sub_b] {
            bus.subscribe(topic.clone(), s);
            bus.wait(&name, s);
        }
        assert_eq!(bus.subscribers(&topic).len(), 2);
        assert!(bus.poll_wake(&name, &sub_a).is_none(), "no wake before any publish");

        // The producer holds a Signature-grant publish cap into this topic channel.
        let cap = SendCap::grant(sub_a, name.clone(), AuthRequired::Signature);

        // ── (b) CAP-GATED: an over-broad enqueue to a subscriber inbox is refused.
        // We exercise the same `admits` seam `publish` rides, directly, to prove the
        // refusal polarity is not vacuous and leaves NO phantom work.
        let before = bus.pending_count(&sub_a);
        let cursor_before = bus.cursor(&name);
        let refused = bus.enqueue(&cap, sub_a, &name, AuthRequired::None, b"forge".to_vec(), 0);
        assert!(
            matches!(refused, Err(DataPlaneError::Unauthorized { .. })),
            "(b) an over-authorized (None ⊋ Signature) send is refused at the seam"
        );
        assert_eq!(bus.pending_count(&sub_a), before, "(b) nothing queued for a refused send");
        assert_eq!(bus.cursor(&name), cursor_before, "(b) no cursor tick for a refused send");

        // ── PRODUCE: three ordered publishes fan to BOTH subscribers (6 deliveries).
        // Keep each subscriber's receipts in publish order to check causal sequence.
        let payloads: [&[u8]; 3] = [b"order-1", b"order-2", b"order-3"];
        let mut recv: HashMap<FederationId, Vec<Delivery>> = HashMap::new();
        for (i, p) in payloads.iter().enumerate() {
            let deliveries = bus
                .publish(&topic, &cap, AuthRequired::Signature, p.to_vec(), 100 + i as u64)
                .expect("authorized publish fans out");
            assert_eq!(deliveries.len(), 2, "each publish reaches both subscribers");
            for (sub, d) in deliveries {
                // ── (a) RECEIPT-IDENTITY: every receipt is a real, verifying signature.
                assert!(d.receipt.sig_verifies(), "(a) the custody receipt VERIFIES");
                recv.entry(sub).or_default().push(d);
            }
        }

        // ── (a) TAMPER-EVIDENCE: mutate a committed field of a held receipt — its
        // signature must STOP verifying (the chain is tamper-evident, not decorative).
        {
            let mut forged = recv[&sub_a][0].receipt.clone();
            assert!(forged.sig_verifies(), "the pristine receipt verifies");
            forged.content_hash[0] ^= 0xFF;
            assert!(!forged.sig_verifies(), "(a) a tampered content_hash breaks the signature");
            let mut forged_root = recv[&sub_a][0].receipt.clone();
            forged_root.new_root[0] ^= 0xFF;
            assert!(!forged_root.sig_verifies(), "(a) a tampered root breaks the signature");
        }

        // ── (a) ROOT-CHAINING: each subscriber's receipts chain old_root→new_root
        // across the run (a monotone custody chain, never retreating).
        for sub in [sub_a, sub_b] {
            let chain = &recv[&sub];
            assert_eq!(chain.len(), 3, "three deliveries to {sub:?}");
            for w in chain.windows(2) {
                assert_eq!(
                    w[0].receipt.new_root, w[1].receipt.old_root,
                    "(a) the custody chain links: each enqueue's new_root is the next's old_root"
                );
                assert_ne!(w[0].receipt.new_root, w[1].receipt.new_root, "(a) the root advances");
            }
            assert_eq!(
                chain.last().unwrap().receipt.new_root,
                bus.inbox_root(&sub),
                "(a) the live inbox root is the head of the receipt chain"
            );
        }

        // ── (c) ORDERED PUB-SUB: each subscriber is woken by name, and the boxes in
        // its inbox carry causal_sequence 1,2,3 in publish order (FIFO, no reorder).
        for sub in [sub_a, sub_b] {
            assert_eq!(
                bus.poll_wake(&name, &sub).expect("woken by name").cursor,
                6,
                "(c) the cursor reflects all 6 admitted enqueues (3 publishes × 2 subs)"
            );
            assert_eq!(bus.pending_count(&sub), 3, "(c) three boxes queued for {sub:?}");
        }

        // ── (d) DRAIN LOCKSTEP: hand boxes out ONE at a time. The order is FIFO
        // publish order, no off-by-one, and the witness flips box-for-box.
        for sub in [sub_a, sub_b] {
            let mut got: Vec<Vec<u8>> = Vec::new();
            for expected_pending in (0..3).rev() {
                let m = bus.drain_one(&sub).expect("(d) a box is handed out");
                got.push(m.encrypted_payload.clone());
                assert_eq!(
                    bus.pending_count(&sub),
                    expected_pending,
                    "(d) lockstep: pending drops by exactly one per drained box"
                );
            }
            assert_eq!(
                got,
                payloads.iter().map(|p| p.to_vec()).collect::<Vec<_>>(),
                "(d) delivery order is FIFO publish order (no reorder, no off-by-one)"
            );
            // (d) NO DOUBLE-DELIVERY: the inbox is empty; a re-drain yields nothing,
            // and the witness log holds exactly the three distinct boxes once each.
            assert!(bus.drain_one(&sub).is_none(), "(d) no double-delivery past empty");
            let witnessed = bus.delivered_hashes(&sub);
            assert_eq!(witnessed.len(), 3, "(d) exactly three boxes witnessed (no dup)");
            // Every held receipt is now handled (the witness, not the promise).
            for d in &recv[&sub] {
                assert!(
                    d.is_handled(witnessed),
                    "(a/d) the held delivery is WITNESSED after its box drained"
                );
            }
        }
    }
}

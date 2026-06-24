//! # Netlayer — the OCapN transport abstraction for dregg CapTP.
//!
//! This module adopts the netlayer design from Spritely Goblins / OCapN:
//! a **netlayer** is *how sessions dial, listen, and identify peers* —
//! deliberately independent of the CapTP session semantics layered on top
//! (import/export tables, promises, GC, handoff — all of which live in
//! [`crate::session`], [`crate::gc`], [`crate::handoff`] and are untouched
//! here). Swapping the netlayer swaps the wire; the capability semantics
//! do not move.
//!
//! ## What a netlayer provides
//!
//! - **Identity**: a stable self id ([`PeerId`], 32 bytes — a strand /
//!   federation-node identity in the unified lace model) and a shareable
//!   [`ocapn_uri::OcapnLocation`] (`ocapn://<id-b58>.<netlayer-hint>`)
//!   telling others how to reach us.
//! - **Dial**: [`Netlayer::dial`] turns an address into a live
//!   [`NetSession`] — a byte-frame connection ([`NetConnection`]) paired
//!   with a fresh, epoch-correct [`CapSession`] for the peer. Re-dialing
//!   the same peer mints a *higher epoch* (stale-message rejection rides
//!   the existing `CapSession::epoch` semantics).
//! - **Listen**: [`Netlayer::accept`] yields inbound sessions initiated by
//!   remote dialers.
//!
//! Frames are opaque `Vec<u8>`; the intended payload is the existing
//! postcard-encoded `dregg_wire::WireMessage` (the same codec the silo TCP
//! framing uses), but the netlayer does not inspect it.
//!
//! ## How dregg's EXISTING transports map onto the trait
//!
//! dregg already moves CapTP bytes three ways; the first two are
//! implemented here as the inaugural instances, the third is documented as
//! the same shape:
//!
//! 1. **In-process** ([`InProcessNetlayer`], hint `inproc`): the
//!    test/single-machine transport. Peers join a shared
//!    [`InProcessFabric`]; dialing creates a paired duplex frame queue.
//!    This is the netlayer equivalent of the SDK's `enliven_local` /
//!    shared-`SwissTable` path used throughout the test suite.
//! 2. **Relay store-and-forward** ([`RelayNetlayer`], hint `relay`): an
//!    adapter *around* (not a rewrite of) [`crate::store_forward`]. A
//!    session's `send` is exactly `StoreForwardClient::prepare_message`
//!    (X25519 → HKDF-SHA256 → ChaCha20-Poly1305, fresh ephemeral per
//!    frame) followed by `MessageRelay::enqueue`; `recv` is
//!    `MessageRelay::drain` + `decrypt_from_sender`, in causal order. The
//!    relay holds only ciphertext. The production hosted-inbox HTTP shape
//!    (`dregg-node relay` routes; `dregg_sdk::mailbox::RelayHttpTransport`
//!    with its Ed25519-signed drains and dequeue-proof custody) is this
//!    same netlayer spoken over HTTP — the in-memory `MessageRelay` here
//!    stands in for that service behind the identical session interface.
//! 3. **Silo TCP** (not instantiated here): `dregg_wire`'s
//!    length-prefixed postcard `WireMessage` framing between silos is
//!    already frame-shaped; a `TcpNetlayer` is a mechanical instance
//!    (dial = connect + frame codec) and is left to the node crate, which
//!    owns the sockets.
//!
//! ## The Goblins-interop adapter (the 2–4 week artifact; NOT this module)
//!
//! This trait is the *enabling move* on the ORGANS interop ladder; the
//! bounded follow-up artifact is **a Goblins peer holding and exercising a
//! dregg sturdy ref**. Concretely, an `OcapnGoblinsNetlayer` adapter would
//! add, on top of this trait:
//!
//! - **A shared concrete wire**: OCapN netlayers Goblins actually speaks —
//!   tcp+tls (testing-grade in Goblins), Tor onion, or libp2p — as the
//!   `NetConnection` instance.
//! - **The Syrup codec**: OCapN messages are Syrup-encoded records, not
//!   postcard; the adapter translates frame payloads.
//! - **The OCapN session handshake**: `op:start-session` with captp
//!   version, public-key cross-certification of the netlayer location
//!   (their analogue of our `CapSession::epoch` freshness story), and
//!   `op:abort` teardown.
//! - **Descriptor translation**: `desc:export` / `desc:import-object` /
//!   `desc:import-promise` / `desc:answer` mapped onto our
//!   `CapSession::{exports,imports,promises}` tables, with `op:deliver` /
//!   `op:deliver-only` carrying method invocations (our
//!   `pipeline::PipelinedAction`) and `op:gc-export` / `op:gc-answer`
//!   driving the existing [`crate::gc`] managers.
//! - **Sturdy-ref enliven**: the Goblins peer fetches
//!   `ocapn://<node>.<hint>/s/<swiss>` via the bootstrap object's `fetch`;
//!   on our side that lands in the existing `SwissTable::enliven` — the
//!   swiss-number bearer model is already aligned (Goblins inherited it
//!   from the same E lineage we did). [`ocapn_uri`] below already speaks
//!   the locator format both directions.
//! - **Third-party handoff**: OCapN `desc:handoff-give/receive`
//!   certificates mapped onto our [`crate::handoff::HandoffCertificate`]
//!   (both are signed introducer certificates; the translation is field
//!   renaming plus signature-scheme bridging).
//!
//! None of that requires changing this trait: the adapter is one more
//! `impl Netlayer` plus a codec/descriptor shim above it.
//!
//! ## Async model
//!
//! Trait methods are native `async fn` (no runtime dependency in this
//! crate). The two in-memory instances complete immediately and their
//! `recv` is poll-shaped (`Ok(None)` = nothing pending); socket-backed
//! instances in the node crate may pend for real. Executors are expected
//! to be local; `Send`-bound futures (for work-stealing runtimes) can be
//! layered in the Goblins-adapter artifact if needed.

// Public async-trait note: we deliberately accept the auto-trait-bound
// flexibility caveat; see "Async model" in the module docs.
#![allow(async_fn_in_trait)]

use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::sync::{Arc, Mutex};

use crate::session::CapSession;
use crate::store_forward::{
    MessagePriority, MessageRelay, QueuedMessage, RelayError, StoreForwardClient,
    decrypt_from_sender,
};
use crate::{FederationId, StrandId};

// =============================================================================
// Identity + errors
// =============================================================================

/// A peer identity at the netlayer: 32 bytes, the strand / federation-node
/// id (same keyspace as [`CapSession::peer_id`] and [`StrandId`]).
pub type PeerId = StrandId;

/// Errors surfaced by netlayer operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NetlayerError {
    /// The dialed peer is not reachable on this netlayer (not joined /
    /// not listening / unknown address).
    PeerUnreachable { peer: PeerId },
    /// The connection (or the listener) has been closed.
    Closed,
    /// A frame could not be sent.
    SendFailed { reason: String },
    /// A received frame could not be decoded/decrypted.
    RecvFailed { reason: String },
}

impl fmt::Display for NetlayerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NetlayerError::PeerUnreachable { peer } => {
                write!(f, "peer unreachable: {}", bs58::encode(peer).into_string())
            }
            NetlayerError::Closed => write!(f, "connection closed"),
            NetlayerError::SendFailed { reason } => write!(f, "send failed: {reason}"),
            NetlayerError::RecvFailed { reason } => write!(f, "recv failed: {reason}"),
        }
    }
}

impl std::error::Error for NetlayerError {}

impl From<RelayError> for NetlayerError {
    fn from(e: RelayError) -> Self {
        NetlayerError::SendFailed {
            reason: e.to_string(),
        }
    }
}

// =============================================================================
// The traits
// =============================================================================

/// A live byte-frame connection to one peer, as vended by a [`Netlayer`].
///
/// Frames are opaque; CapTP layers its postcard-encoded messages on top.
pub trait NetConnection {
    /// The peer on the other end of this connection.
    fn peer(&self) -> PeerId;

    /// Send one frame to the peer.
    async fn send(&self, frame: Vec<u8>) -> Result<(), NetlayerError>;

    /// Receive one frame, if one is pending.
    ///
    /// `Ok(Some(frame))` — a frame arrived; `Ok(None)` — nothing pending
    /// right now (poll again); `Err(Closed)` — the connection is closed
    /// and fully drained.
    async fn recv(&self) -> Result<Option<Vec<u8>>, NetlayerError>;

    /// Close this side of the connection. Frames already in flight remain
    /// receivable by the peer; subsequent `send`s fail.
    fn close(&self);
}

/// A dialed/accepted session: the transport leg paired with the CapTP
/// semantic state for the peer.
///
/// The netlayer mints the [`CapSession`] (with the correct strand identity
/// and a fresh epoch); everything CapTP-semantic — exports, imports,
/// promises, GC — happens on `captp` exactly as before this module existed.
pub struct NetSession<C: NetConnection> {
    /// CapTP session state (import/export/promise tables, epoch).
    pub captp: CapSession,
    /// The byte-frame transport to the peer.
    pub conn: C,
}

impl<C: NetConnection> NetSession<C> {
    /// The peer this session talks to.
    pub fn peer(&self) -> PeerId {
        self.conn.peer()
    }
}

/// The OCapN netlayer abstraction: how sessions dial, listen, and identify
/// peers — independent of CapTP session semantics.
///
/// See the module docs for the design provenance (Spritely Goblins) and
/// the instances implemented here.
pub trait Netlayer {
    /// Address type understood by this netlayer (a peer id, a relay
    /// coordinate, a host:port, an onion address, ...).
    type Addr: Clone + fmt::Debug;

    /// The connection type this netlayer vends.
    type Conn: NetConnection;

    /// The netlayer hint used in `ocapn://<id>.<hint>` location strings
    /// (e.g. `"inproc"`, `"relay"`, `"tcp"`, `"onion"`).
    fn hint(&self) -> &'static str;

    /// Our own identity on this netlayer.
    fn self_id(&self) -> PeerId;

    /// Our shareable location: `ocapn://<self-id-b58>.<hint>`.
    ///
    /// Instances with extra reachability information (host, port, relay
    /// coordinates) should override this and attach it as hints.
    fn self_location(&self) -> ocapn_uri::OcapnLocation {
        ocapn_uri::OcapnLocation::new(bs58::encode(self.self_id()).into_string(), self.hint())
    }

    /// Dial a peer: establish a connection and mint a fresh epoch-correct
    /// [`CapSession`] for it.
    async fn dial(&self, addr: &Self::Addr) -> Result<NetSession<Self::Conn>, NetlayerError>;

    /// Accept one pending inbound session, if any.
    ///
    /// `Ok(Some(session))` — a remote dialed us; `Ok(None)` — nothing
    /// pending; `Err(Closed)` — this netlayer has shut down.
    async fn accept(&self) -> Result<Option<NetSession<Self::Conn>>, NetlayerError>;
}

// =============================================================================
// Epoch minting (shared by instances)
// =============================================================================

/// Per-peer session-epoch counters: each (re)dial of the same peer mints a
/// strictly higher epoch, so the existing `CapSession::epoch` stale-message
/// rejection works across reconnects. Shared by netlayer instances.
#[derive(Clone, Debug, Default)]
pub struct EpochMinter {
    next: Arc<Mutex<HashMap<PeerId, u64>>>,
}

impl EpochMinter {
    /// Create a minter with all peers at epoch 0.
    pub fn new() -> Self {
        Self::default()
    }

    /// Mint the next epoch for `peer` (0 on first contact, then 1, 2, ...).
    pub fn mint(&self, peer: PeerId) -> u64 {
        let mut map = self.next.lock().unwrap_or_else(|e| e.into_inner());
        let slot = map.entry(peer).or_insert(0);
        let epoch = *slot;
        *slot += 1;
        epoch
    }
}

// =============================================================================
// Instance 1: InProcessNetlayer (hint "inproc")
// =============================================================================

/// One direction of an in-process duplex pipe.
type FrameQueue = Arc<Mutex<Option<VecDeque<Vec<u8>>>>>; // None = closed

fn new_frame_queue() -> FrameQueue {
    Arc::new(Mutex::new(Some(VecDeque::new())))
}

/// An in-process frame connection (paired queues).
pub struct InProcessConn {
    peer: PeerId,
    /// Frames we send (the peer's rx).
    tx: FrameQueue,
    /// Frames we receive (the peer's tx).
    rx: FrameQueue,
}

impl NetConnection for InProcessConn {
    fn peer(&self) -> PeerId {
        self.peer
    }

    async fn send(&self, frame: Vec<u8>) -> Result<(), NetlayerError> {
        let mut guard = self.tx.lock().unwrap_or_else(|e| e.into_inner());
        match guard.as_mut() {
            Some(q) => {
                q.push_back(frame);
                Ok(())
            }
            None => Err(NetlayerError::Closed),
        }
    }

    async fn recv(&self) -> Result<Option<Vec<u8>>, NetlayerError> {
        let mut guard = self.rx.lock().unwrap_or_else(|e| e.into_inner());
        match guard.as_mut() {
            Some(q) => Ok(q.pop_front()),
            None => Err(NetlayerError::Closed),
        }
    }

    fn close(&self) {
        // Closing our send side: the peer sees Closed once drained is
        // modeled by simply dropping the queue contents' container.
        *self.tx.lock().unwrap_or_else(|e| e.into_inner()) = None;
    }
}

/// A pending inbound dial parked at a listener.
struct PendingInbound {
    dialer: PeerId,
    conn: InProcessConn,
}

#[derive(Default)]
struct FabricState {
    /// Joined peers and their pending-inbound queues.
    listeners: HashMap<PeerId, VecDeque<PendingInbound>>,
}

/// A shared in-process "network": peers [`join`](InProcessFabric::join) it
/// and can then dial each other by [`PeerId`]. The single-machine /
/// test-suite netlayer.
#[derive(Clone, Default)]
pub struct InProcessFabric {
    state: Arc<Mutex<FabricState>>,
}

impl InProcessFabric {
    /// Create an empty fabric.
    pub fn new() -> Self {
        Self::default()
    }

    /// Join the fabric as `self_id`, becoming dialable and able to dial.
    pub fn join(&self, self_id: PeerId) -> InProcessNetlayer {
        self.state
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .listeners
            .entry(self_id)
            .or_default();
        InProcessNetlayer {
            fabric: self.clone(),
            self_id,
            epochs: EpochMinter::new(),
        }
    }
}

/// The in-process netlayer instance. See [`InProcessFabric`].
pub struct InProcessNetlayer {
    fabric: InProcessFabric,
    self_id: PeerId,
    epochs: EpochMinter,
}

impl Netlayer for InProcessNetlayer {
    /// In-process addresses are just peer ids.
    type Addr = PeerId;
    type Conn = InProcessConn;

    fn hint(&self) -> &'static str {
        "inproc"
    }

    fn self_id(&self) -> PeerId {
        self.self_id
    }

    async fn dial(&self, addr: &PeerId) -> Result<NetSession<InProcessConn>, NetlayerError> {
        let a_to_b = new_frame_queue();
        let b_to_a = new_frame_queue();

        // Park the accept-half at the peer's listener.
        {
            let mut state = self.fabric.state.lock().unwrap_or_else(|e| e.into_inner());
            let inbox = state
                .listeners
                .get_mut(addr)
                .ok_or(NetlayerError::PeerUnreachable { peer: *addr })?;
            inbox.push_back(PendingInbound {
                dialer: self.self_id,
                conn: InProcessConn {
                    peer: self.self_id,
                    tx: b_to_a.clone(),
                    rx: a_to_b.clone(),
                },
            });
        }

        let epoch = self.epochs.mint(*addr);
        Ok(NetSession {
            captp: CapSession::with_strand(*addr, epoch),
            conn: InProcessConn {
                peer: *addr,
                tx: a_to_b,
                rx: b_to_a,
            },
        })
    }

    async fn accept(&self) -> Result<Option<NetSession<InProcessConn>>, NetlayerError> {
        let pending = {
            let mut state = self.fabric.state.lock().unwrap_or_else(|e| e.into_inner());
            match state.listeners.get_mut(&self.self_id) {
                Some(inbox) => inbox.pop_front(),
                None => return Err(NetlayerError::Closed),
            }
        };
        Ok(pending.map(|p| {
            let epoch = self.epochs.mint(p.dialer);
            NetSession {
                captp: CapSession::with_strand(p.dialer, epoch),
                conn: p.conn,
            }
        }))
    }
}

// =============================================================================
// Instance 2: RelayNetlayer (hint "relay") — adapts crate::store_forward
// =============================================================================

/// Address of a peer reachable via store-and-forward: their id plus the
/// X25519 public key frames must be sealed to.
///
/// (In production the key comes from the peer's identity cell / published
/// `RelayInfo`; at this layer it is part of the address.)
#[derive(Clone, Debug)]
pub struct RelayAddr {
    /// The destination peer/federation id (the relay queue key).
    pub peer: FederationId,
    /// The destination's X25519 public key (seals each frame).
    pub dest_x25519_pk: [u8; 32],
}

/// Shared handle to a relay's message store.
///
/// Stands in for the hosted-inbox service: the in-memory
/// [`MessageRelay`] from [`crate::store_forward`] here; the `dregg-node
/// relay` HTTP routes (`dregg_sdk::mailbox::RelayHttpTransport`) in
/// production — same queue semantics, same envelope.
pub type SharedRelay = Arc<Mutex<MessageRelay>>;

/// The store-and-forward netlayer: sessions whose frames are sealed
/// end-to-end ([`crate::store_forward`]'s X25519 → HKDF-SHA256 →
/// ChaCha20-Poly1305 box) and queued on a relay that sees only ciphertext.
///
/// This is an ADAPTER over the existing transport, not a reimplementation:
/// `send` = `StoreForwardClient::prepare_message` + `MessageRelay::enqueue`;
/// `recv` = `MessageRelay::drain` + `decrypt_from_sender`, causal order
/// preserved.
///
/// Store-and-forward has no in-band dial handshake (delivery is the
/// introduction), so `accept` surfaces a session for each *new sender*
/// found in our drained queue.
pub struct RelayNetlayer {
    relay: SharedRelay,
    self_id: FederationId,
    /// Our X25519 secret (unseals incoming frames).
    x25519_secret: [u8; 32],
    /// The shared store-and-forward client (sequencing + encryption).
    client: Arc<Mutex<StoreForwardClient>>,
    /// Current block height (for queued_at; advance via `set_height`).
    height: Arc<Mutex<u64>>,
    /// TTL applied to outgoing frames, in blocks.
    ttl_blocks: u64,
    /// Frames drained from the relay but not yet claimed by a session,
    /// keyed by sender. (`MessageRelay::drain` returns everything queued
    /// for us; sessions are per-peer.)
    inbound: Arc<Mutex<HashMap<FederationId, VecDeque<QueuedMessage>>>>,
    /// Senders drained but not yet surfaced via `accept`.
    unclaimed_senders: Arc<Mutex<VecDeque<FederationId>>>,
    /// Senders already claimed (dialed or accepted).
    claimed: Arc<Mutex<std::collections::HashSet<FederationId>>>,
    epochs: EpochMinter,
}

impl RelayNetlayer {
    /// Join a relay as `self_id`, unsealing with `x25519_secret`.
    pub fn new(
        relay: SharedRelay,
        self_id: FederationId,
        x25519_secret: [u8; 32],
        ttl_blocks: u64,
    ) -> Self {
        RelayNetlayer {
            relay,
            self_id,
            x25519_secret,
            client: Arc::new(Mutex::new(StoreForwardClient::new(self_id, Vec::new()))),
            height: Arc::new(Mutex::new(0)),
            ttl_blocks,
            inbound: Arc::new(Mutex::new(HashMap::new())),
            unclaimed_senders: Arc::new(Mutex::new(VecDeque::new())),
            claimed: Arc::new(Mutex::new(std::collections::HashSet::new())),
            epochs: EpochMinter::new(),
        }
    }

    /// Advance the height used for `queued_at` stamps (TTL anchoring).
    pub fn set_height(&self, height: u64) {
        *self.height.lock().unwrap_or_else(|e| e.into_inner()) = height;
    }

    /// Drain our queue on the relay into the per-sender inbound buffers.
    ///
    /// Senders are attributed by the envelope's declared origin. NOTE
    /// (unverified-by-crypto at this layer): the store-and-forward box is
    /// sender-ANONYMOUS by design (fresh ephemeral key per frame), so the
    /// sender id here is a routing claim, not an authentication; payloads
    /// needing sender authenticity carry their own signatures (as the
    /// mailbox organ's sender-set gate does).
    fn pump(&self) {
        let drained = {
            let mut relay = self.relay.lock().unwrap_or_else(|e| e.into_inner());
            relay.drain(&self.self_id)
        };
        if drained.is_empty() {
            return;
        }
        let mut inbound = self.inbound.lock().unwrap_or_else(|e| e.into_inner());
        let claimed = self.claimed.lock().unwrap_or_else(|e| e.into_inner());
        let mut unclaimed = self
            .unclaimed_senders
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for msg in drained {
            // `destination` on a drained message is us; the sender rides in
            // the envelope payload prefix written by RelayConn::send.
            if let Some(sender) = parse_sender_prefix(&msg.encrypted_payload) {
                if !claimed.contains(&sender) && !unclaimed.contains(&sender) {
                    unclaimed.push_back(sender);
                }
                inbound.entry(sender).or_default().push_back(msg);
            }
            // Frames without a parseable prefix are dropped (malformed).
        }
    }

    fn make_conn(&self, peer: FederationId, dest_pk: Option<[u8; 32]>) -> RelayConn {
        RelayConn {
            self_id: self.self_id,
            peer,
            dest_pk,
            x25519_secret: self.x25519_secret,
            relay: self.relay.clone(),
            client: self.client.clone(),
            height: self.height.clone(),
            ttl_blocks: self.ttl_blocks,
            inbound: self.inbound.clone(),
            closed: Arc::new(Mutex::new(false)),
        }
    }
}

/// Outgoing frames carry a cleartext 32-byte sender-id prefix BEFORE the
/// sealed box, so the recipient can route frames to per-sender sessions
/// without trial decryption. The relay learns sender/recipient pairing —
/// which it already knows from queue keys — and nothing else.
fn join_sender_prefix(sender: &FederationId, sealed: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(32 + sealed.len());
    out.extend_from_slice(&sender.0);
    out.extend_from_slice(sealed);
    out
}

fn split_sender_prefix(payload: &[u8]) -> Option<(FederationId, Vec<u8>)> {
    let sender = parse_sender_prefix(payload)?;
    Some((sender, payload[32..].to_vec()))
}

/// Read only the sender id from an envelope prefix, without allocating the
/// trailing sealed body — for paths that route on the sender and keep the
/// original message (the drain/sort loop).
fn parse_sender_prefix(payload: &[u8]) -> Option<FederationId> {
    if payload.len() < 32 {
        return None;
    }
    let mut id = [0u8; 32];
    id.copy_from_slice(&payload[..32]);
    Some(FederationId(id))
}

/// A store-and-forward session leg to one peer.
pub struct RelayConn {
    self_id: FederationId,
    peer: FederationId,
    /// The peer's X25519 public key. `None` for accepted (inbound-only)
    /// sessions until the peer's key is learned out-of-band — `send`
    /// fails until then (fail-closed; we never send unsealed).
    dest_pk: Option<[u8; 32]>,
    x25519_secret: [u8; 32],
    relay: SharedRelay,
    client: Arc<Mutex<StoreForwardClient>>,
    height: Arc<Mutex<u64>>,
    ttl_blocks: u64,
    inbound: Arc<Mutex<HashMap<FederationId, VecDeque<QueuedMessage>>>>,
    closed: Arc<Mutex<bool>>,
}

impl NetConnection for RelayConn {
    fn peer(&self) -> PeerId {
        self.peer.0
    }

    async fn send(&self, frame: Vec<u8>) -> Result<(), NetlayerError> {
        if *self.closed.lock().unwrap_or_else(|e| e.into_inner()) {
            return Err(NetlayerError::Closed);
        }
        let dest_pk = self.dest_pk.ok_or_else(|| NetlayerError::SendFailed {
            reason: "peer X25519 key unknown (inbound-only session)".into(),
        })?;
        let height = *self.height.lock().unwrap_or_else(|e| e.into_inner());

        // EXISTING transport, verbatim: seal + sequence via the
        // StoreForwardClient, then queue on the relay.
        let mut msg = {
            let mut client = self.client.lock().unwrap_or_else(|e| e.into_inner());
            client.prepare_message(
                self.peer,
                &frame,
                &dest_pk,
                &self.x25519_secret,
                MessagePriority::Normal,
                self.ttl_blocks,
                height,
            )
        };
        // Routing prefix so the recipient can demux per-sender sessions.
        msg.encrypted_payload = join_sender_prefix(&self.self_id, &msg.encrypted_payload);

        let mut relay = self.relay.lock().unwrap_or_else(|e| e.into_inner());
        relay.enqueue(msg).map_err(NetlayerError::from)
    }

    async fn recv(&self) -> Result<Option<Vec<u8>>, NetlayerError> {
        let next = {
            let mut inbound = self.inbound.lock().unwrap_or_else(|e| e.into_inner());
            inbound.get_mut(&self.peer).and_then(|q| q.pop_front())
        };
        let Some(msg) = next else {
            return if *self.closed.lock().unwrap_or_else(|e| e.into_inner()) {
                Err(NetlayerError::Closed)
            } else {
                Ok(None)
            };
        };
        let (_, sealed) =
            split_sender_prefix(&msg.encrypted_payload).ok_or(NetlayerError::RecvFailed {
                reason: "malformed frame (missing sender prefix)".into(),
            })?;
        decrypt_from_sender(&sealed, &msg.sender_ephemeral_pk, &self.x25519_secret)
            .map(Some)
            .map_err(|e| NetlayerError::RecvFailed {
                reason: e.to_string(),
            })
    }

    fn close(&self) {
        *self.closed.lock().unwrap_or_else(|e| e.into_inner()) = true;
    }
}

impl Netlayer for RelayNetlayer {
    type Addr = RelayAddr;
    type Conn = RelayConn;

    fn hint(&self) -> &'static str {
        "relay"
    }

    fn self_id(&self) -> PeerId {
        self.self_id.0
    }

    async fn dial(&self, addr: &RelayAddr) -> Result<NetSession<RelayConn>, NetlayerError> {
        // Store-and-forward dialing is connectionless: minting the session
        // is local; the first `send` introduces us to the peer.
        //
        // Dialing deliberately does NOT mark the peer `claimed`: `claimed`
        // exists only to dedup inbound `accept` surfacing, and an outbound
        // dial does not consume that slot. A peer we dialed can still later
        // arrive as an inbound sender (its reply) needing its own accept
        // session — exactly the round-trip the relay round-trip test drives.
        let epoch = self.epochs.mint(addr.peer.0);
        Ok(NetSession {
            captp: CapSession::with_strand(addr.peer.0, epoch),
            conn: self.make_conn(addr.peer, Some(addr.dest_x25519_pk)),
        })
    }

    async fn accept(&self) -> Result<Option<NetSession<RelayConn>>, NetlayerError> {
        self.pump();
        let sender = {
            let mut unclaimed = self
                .unclaimed_senders
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            unclaimed.pop_front()
        };
        Ok(sender.map(|peer| {
            self.claimed
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(peer);
            let epoch = self.epochs.mint(peer.0);
            NetSession {
                captp: CapSession::with_strand(peer.0, epoch),
                // Inbound-only until the peer's X25519 key is learned:
                // recv works, send fails closed.
                conn: self.make_conn(peer, None),
            }
        }))
    }
}

// =============================================================================
// ocapn:// location strings
// =============================================================================

pub mod ocapn_uri {
    //! OCapN locator strings: `ocapn://<designator>.<netlayer-hint>`.
    //!
    //! Two shapes, following the OCapN locators draft (the format Goblins
    //! speaks):
    //!
    //! - **Machine locator** — where a node lives:
    //!   `ocapn://<designator>.<hint>[?key=value&key=value]`
    //!   (e.g. `ocapn://4t1teuu…2pl4.tcpip?host=example.com&port=30022`)
    //! - **Sturdy ref** — a swiss-num capability at a node:
    //!   `ocapn://<designator>.<hint>/s/<swiss>[?…]`
    //!
    //! The designator identifies the node within its netlayer (for dregg:
    //! the base58 [`PeerId`](super::PeerId)); the hint names the netlayer
    //! (`inproc`, `relay`, `tcpip`, `onion`, …); hints/params carry extra
    //! reachability data.
    //!
    //! [`OcapnSturdyRef::from_dregg`] / [`OcapnSturdyRef::to_dregg`]
    //! bridge to the existing [`DreggUri`](crate::uri::DreggUri) sturdy
    //! shape: the dregg `(cell_id, swiss)` pair packs into the single
    //! OCapN swiss segment as base58 of the 64-byte concatenation.

    use std::fmt;

    use crate::uri::DreggUri;

    /// Errors parsing `ocapn://` strings.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum OcapnUriError {
        /// Missing the `ocapn://` scheme prefix.
        InvalidScheme,
        /// The authority is not `<designator>.<hint>`.
        MalformedAuthority,
        /// A designator/hint/param contains a forbidden character.
        ForbiddenCharacter { component: &'static str },
        /// The path is not empty and not `/s/<swiss>`.
        MalformedPath,
        /// A query parameter is not `key=value`.
        MalformedParam,
        /// A base58 segment failed to decode (bridging to dregg).
        Base58 { message: String },
        /// The packed dregg swiss segment is not 64 bytes.
        WrongSwissLength { found: usize },
    }

    impl fmt::Display for OcapnUriError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                OcapnUriError::InvalidScheme => write!(f, "URI must start with 'ocapn://'"),
                OcapnUriError::MalformedAuthority => {
                    write!(f, "authority must be '<designator>.<netlayer-hint>'")
                }
                OcapnUriError::ForbiddenCharacter { component } => {
                    write!(f, "forbidden character in {component}")
                }
                OcapnUriError::MalformedPath => {
                    write!(f, "path must be empty or '/s/<swiss>'")
                }
                OcapnUriError::MalformedParam => write!(f, "params must be 'key=value'"),
                OcapnUriError::Base58 { message } => write!(f, "base58: {message}"),
                OcapnUriError::WrongSwissLength { found } => {
                    write!(f, "packed dregg swiss must be 64 bytes, got {found}")
                }
            }
        }
    }

    impl std::error::Error for OcapnUriError {}

    /// Characters allowed in designators, hints, swiss segments, and param
    /// keys/values. Deliberately conservative: base58 and friendly token
    /// charsets pass; URI metacharacters do not, so formatting always
    /// round-trips through parsing.
    fn token_ok(s: &str) -> bool {
        !s.is_empty()
            && s.chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | ':'))
    }

    /// A machine locator: where a node lives on some netlayer.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct OcapnLocation {
        /// Node designator within the netlayer (dregg: base58 peer id).
        pub designator: String,
        /// The netlayer hint (`inproc`, `relay`, `tcpip`, `onion`, …).
        pub hint: String,
        /// Reachability hints (`host`, `port`, relay coordinates, …).
        pub params: Vec<(String, String)>,
    }

    impl OcapnLocation {
        /// Build a locator with no params.
        pub fn new(designator: impl Into<String>, hint: impl Into<String>) -> Self {
            OcapnLocation {
                designator: designator.into(),
                hint: hint.into(),
                params: Vec::new(),
            }
        }

        /// Attach a reachability param.
        pub fn with_param(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
            self.params.push((key.into(), value.into()));
            self
        }

        /// Parse `ocapn://<designator>.<hint>[?k=v&…]`.
        pub fn parse(s: &str) -> Result<Self, OcapnUriError> {
            let (loc, path) = parse_parts(s)?;
            if !path.is_empty() {
                return Err(OcapnUriError::MalformedPath);
            }
            Ok(loc)
        }

        /// Format as an `ocapn://` string.
        pub fn to_uri_string(&self) -> String {
            format_parts(self, None)
        }
    }

    impl fmt::Display for OcapnLocation {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.to_uri_string())
        }
    }

    /// A sturdy reference: a swiss-num capability at a machine locator.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct OcapnSturdyRef {
        /// Where the hosting node lives.
        pub location: OcapnLocation,
        /// The swiss segment (bearer secret), as it appears in the URI.
        pub swiss: String,
    }

    impl OcapnSturdyRef {
        /// Parse `ocapn://<designator>.<hint>/s/<swiss>[?k=v&…]`.
        pub fn parse(s: &str) -> Result<Self, OcapnUriError> {
            let (location, path) = parse_parts(s)?;
            match path.as_slice() {
                ["s", swiss] if token_ok(swiss) => Ok(OcapnSturdyRef {
                    location,
                    swiss: (*swiss).to_string(),
                }),
                _ => Err(OcapnUriError::MalformedPath),
            }
        }

        /// Format as an `ocapn://` string.
        pub fn to_uri_string(&self) -> String {
            format_parts(&self.location, Some(&self.swiss))
        }

        /// Bridge FROM the dregg sturdy shape: the federation id becomes
        /// the designator, `(cell_id, swiss)` packs into one 64-byte swiss
        /// segment (base58).
        pub fn from_dregg(uri: &DreggUri, hint: impl Into<String>) -> Self {
            let mut packed = [0u8; 64];
            packed[..32].copy_from_slice(&uri.cell_id);
            packed[32..].copy_from_slice(&uri.swiss);
            OcapnSturdyRef {
                location: OcapnLocation::new(bs58::encode(&uri.federation_id).into_string(), hint),
                swiss: bs58::encode(&packed).into_string(),
            }
        }

        /// Bridge TO the dregg sturdy shape (inverse of
        /// [`from_dregg`](Self::from_dregg)).
        pub fn to_dregg(&self) -> Result<DreggUri, OcapnUriError> {
            let federation_id = decode_b58_32(&self.location.designator)?;
            let packed =
                bs58::decode(&self.swiss)
                    .into_vec()
                    .map_err(|e| OcapnUriError::Base58 {
                        message: e.to_string(),
                    })?;
            if packed.len() != 64 {
                return Err(OcapnUriError::WrongSwissLength {
                    found: packed.len(),
                });
            }
            let mut cell_id = [0u8; 32];
            let mut swiss = [0u8; 32];
            cell_id.copy_from_slice(&packed[..32]);
            swiss.copy_from_slice(&packed[32..]);
            Ok(DreggUri {
                federation_id,
                cell_id,
                swiss,
            })
        }
    }

    impl fmt::Display for OcapnSturdyRef {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.to_uri_string())
        }
    }

    fn decode_b58_32(s: &str) -> Result<[u8; 32], OcapnUriError> {
        let bytes = bs58::decode(s)
            .into_vec()
            .map_err(|e| OcapnUriError::Base58 {
                message: e.to_string(),
            })?;
        if bytes.len() != 32 {
            return Err(OcapnUriError::Base58 {
                message: format!("expected 32 bytes, got {}", bytes.len()),
            });
        }
        let mut arr = [0u8; 32];
        arr.copy_from_slice(&bytes);
        Ok(arr)
    }

    /// Shared parser: returns the location plus the path segments.
    fn parse_parts(s: &str) -> Result<(OcapnLocation, Vec<&str>), OcapnUriError> {
        let rest = s
            .strip_prefix("ocapn://")
            .ok_or(OcapnUriError::InvalidScheme)?;

        // Split off ?query.
        let (body, query) = match rest.split_once('?') {
            Some((b, q)) => (b, Some(q)),
            None => (rest, None),
        };

        // First path-split: authority / path…
        let mut segments = body.split('/');
        let authority = segments.next().ok_or(OcapnUriError::MalformedAuthority)?;
        let path: Vec<&str> = segments.collect();

        // authority = <designator>.<hint>, split at the LAST dot (base58
        // designators contain no dots; future designators stay safe).
        let (designator, hint) = authority
            .rsplit_once('.')
            .ok_or(OcapnUriError::MalformedAuthority)?;
        if !token_ok(designator) {
            return Err(OcapnUriError::ForbiddenCharacter {
                component: "designator",
            });
        }
        if !token_ok(hint) {
            return Err(OcapnUriError::ForbiddenCharacter { component: "hint" });
        }

        let mut params = Vec::new();
        if let Some(q) = query {
            for pair in q.split('&') {
                let (k, v) = pair.split_once('=').ok_or(OcapnUriError::MalformedParam)?;
                if !token_ok(k) || !token_ok(v) {
                    return Err(OcapnUriError::ForbiddenCharacter { component: "param" });
                }
                params.push((k.to_string(), v.to_string()));
            }
        }

        Ok((
            OcapnLocation {
                designator: designator.to_string(),
                hint: hint.to_string(),
                params,
            },
            path,
        ))
    }

    fn format_parts(loc: &OcapnLocation, swiss: Option<&str>) -> String {
        let mut out = format!("ocapn://{}.{}", loc.designator, loc.hint);
        if let Some(swiss) = swiss {
            out.push_str("/s/");
            out.push_str(swiss);
        }
        for (i, (k, v)) in loc.params.iter().enumerate() {
            out.push(if i == 0 { '?' } else { '&' });
            out.push_str(k);
            out.push('=');
            out.push_str(v);
        }
        out
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::ocapn_uri::{OcapnLocation, OcapnSturdyRef, OcapnUriError};
    use super::*;
    use crate::store_forward::generate_x25519_keypair;
    use crate::uri::DreggUri;

    /// Minimal single-future executor for the in-memory netlayers (their
    /// futures never pend on external wakeups; a no-op waker suffices).
    fn block_on<F: std::future::Future>(fut: F) -> F::Output {
        use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

        fn raw() -> RawWaker {
            fn no_op(_: *const ()) {}
            fn clone(_: *const ()) -> RawWaker {
                raw()
            }
            RawWaker::new(
                std::ptr::null(),
                &RawWakerVTable::new(clone, no_op, no_op, no_op),
            )
        }

        let waker = unsafe { Waker::from_raw(raw()) };
        let mut cx = Context::from_waker(&waker);
        let mut fut = std::pin::pin!(fut);
        loop {
            match fut.as_mut().poll(&mut cx) {
                Poll::Ready(out) => return out,
                Poll::Pending => std::thread::yield_now(),
            }
        }
    }

    // -------------------------------------------------------------------
    // ocapn_uri
    // -------------------------------------------------------------------

    #[test]
    fn ocapn_location_roundtrip() {
        let loc = OcapnLocation::new(bs58::encode([0xab; 32]).into_string(), "inproc");
        let s = loc.to_uri_string();
        assert!(s.starts_with("ocapn://"));
        assert!(s.ends_with(".inproc"));
        assert_eq!(OcapnLocation::parse(&s).unwrap(), loc);
    }

    #[test]
    fn ocapn_location_roundtrip_with_params() {
        let loc = OcapnLocation::new("4t1tcdjk", "tcpip")
            .with_param("host", "example-node")
            .with_param("port", "30022");
        let s = loc.to_uri_string();
        assert_eq!(s, "ocapn://4t1tcdjk.tcpip?host=example-node&port=30022");
        assert_eq!(OcapnLocation::parse(&s).unwrap(), loc);
    }

    #[test]
    fn ocapn_sturdy_roundtrip() {
        let sr = OcapnSturdyRef {
            location: OcapnLocation::new("nodeid", "relay"),
            swiss: "abc123".into(),
        };
        let s = sr.to_uri_string();
        assert_eq!(s, "ocapn://nodeid.relay/s/abc123");
        assert_eq!(OcapnSturdyRef::parse(&s).unwrap(), sr);
    }

    #[test]
    fn ocapn_parse_errors() {
        assert_eq!(
            OcapnLocation::parse("dregg://x.y").unwrap_err(),
            OcapnUriError::InvalidScheme
        );
        assert_eq!(
            OcapnLocation::parse("ocapn://nodots").unwrap_err(),
            OcapnUriError::MalformedAuthority
        );
        // A sturdy path is not a bare location.
        assert_eq!(
            OcapnLocation::parse("ocapn://a.b/s/swiss").unwrap_err(),
            OcapnUriError::MalformedPath
        );
        // A bare location is not a sturdy ref.
        assert_eq!(
            OcapnSturdyRef::parse("ocapn://a.b").unwrap_err(),
            OcapnUriError::MalformedPath
        );
        // Bad path verb.
        assert_eq!(
            OcapnSturdyRef::parse("ocapn://a.b/x/swiss").unwrap_err(),
            OcapnUriError::MalformedPath
        );
        // Malformed param.
        assert_eq!(
            OcapnLocation::parse("ocapn://a.b?noequals").unwrap_err(),
            OcapnUriError::MalformedParam
        );
        // A slash inside what should be the authority truncates it before
        // the `.hint`: here the authority parses as bare `a` (no dot), so the
        // `<designator>.<hint>` shape is rejected. (The dot-bearing `b.c`
        // landed in the path, never reaching authority parsing.)
        assert_eq!(
            OcapnLocation::parse("ocapn://a/b.c").unwrap_err(),
            OcapnUriError::MalformedAuthority
        );
        // A genuinely forbidden character in an otherwise well-formed
        // authority is rejected (this would break round-tripping).
        assert!(matches!(
            OcapnLocation::parse("ocapn://desig nator.hint").unwrap_err(),
            OcapnUriError::ForbiddenCharacter { .. }
        ));
    }

    #[test]
    fn ocapn_dregg_bridge_roundtrip() {
        let dregg = DreggUri {
            federation_id: [0x11; 32],
            cell_id: [0x22; 32],
            swiss: [0x33; 32],
        };
        let ocapn = OcapnSturdyRef::from_dregg(&dregg, "relay");
        assert_eq!(ocapn.location.hint, "relay");
        // String roundtrip…
        let reparsed = OcapnSturdyRef::parse(&ocapn.to_uri_string()).unwrap();
        assert_eq!(reparsed, ocapn);
        // …and the bridge inverts.
        assert_eq!(reparsed.to_dregg().unwrap(), dregg);
    }

    #[test]
    fn ocapn_dregg_bridge_rejects_short_swiss() {
        let sr = OcapnSturdyRef {
            location: OcapnLocation::new(bs58::encode([0u8; 32]).into_string(), "relay"),
            swiss: bs58::encode([0u8; 16]).into_string(),
        };
        assert!(matches!(
            sr.to_dregg().unwrap_err(),
            OcapnUriError::WrongSwissLength { found: 16 }
        ));
    }

    // -------------------------------------------------------------------
    // InProcessNetlayer
    // -------------------------------------------------------------------

    #[test]
    fn inproc_dial_accept_send_recv() {
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let bob = fabric.join([0xb0; 32]);

        // Dial: alice -> bob.
        let a_sess = block_on(alice.dial(&[0xb0; 32])).unwrap();
        assert_eq!(a_sess.peer(), [0xb0; 32]);
        assert_eq!(a_sess.captp.peer_strand, Some([0xb0; 32]));
        assert_eq!(a_sess.captp.epoch, 0);

        // Accept on bob's side.
        let b_sess = block_on(bob.accept()).unwrap().expect("pending inbound");
        assert_eq!(b_sess.peer(), [0xa1; 32]);
        // Nothing else pending.
        assert!(block_on(bob.accept()).unwrap().is_none());

        // Bidirectional frames.
        block_on(a_sess.conn.send(b"hello bob".to_vec())).unwrap();
        assert_eq!(
            block_on(b_sess.conn.recv()).unwrap(),
            Some(b"hello bob".to_vec())
        );
        block_on(b_sess.conn.send(b"hello alice".to_vec())).unwrap();
        assert_eq!(
            block_on(a_sess.conn.recv()).unwrap(),
            Some(b"hello alice".to_vec())
        );
        // Drained: poll-shaped None.
        assert_eq!(block_on(a_sess.conn.recv()).unwrap(), None);
    }

    #[test]
    fn inproc_redial_mints_higher_epoch() {
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let _bob = fabric.join([0xb0; 32]);

        let s0 = block_on(alice.dial(&[0xb0; 32])).unwrap();
        let s1 = block_on(alice.dial(&[0xb0; 32])).unwrap();
        assert_eq!(s0.captp.epoch, 0);
        assert_eq!(s1.captp.epoch, 1);
    }

    #[test]
    fn inproc_dial_unknown_peer_fails() {
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let Err(err) = block_on(alice.dial(&[0xee; 32])) else {
            panic!("dialing an unjoined peer must fail");
        };
        assert_eq!(err, NetlayerError::PeerUnreachable { peer: [0xee; 32] });
    }

    #[test]
    fn inproc_close_semantics() {
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let bob = fabric.join([0xb0; 32]);

        let a_sess = block_on(alice.dial(&[0xb0; 32])).unwrap();
        let b_sess = block_on(bob.accept()).unwrap().unwrap();

        a_sess.conn.close();
        assert_eq!(
            block_on(a_sess.conn.send(b"after close".to_vec())).unwrap_err(),
            NetlayerError::Closed
        );
        // Peer's recv on the closed direction reports Closed.
        assert_eq!(
            block_on(b_sess.conn.recv()).unwrap_err(),
            NetlayerError::Closed
        );
    }

    #[test]
    fn inproc_self_location() {
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let loc = alice.self_location();
        assert_eq!(loc.hint, "inproc");
        assert_eq!(loc.designator, bs58::encode([0xa1; 32]).into_string());
        // The location string parses back.
        assert_eq!(OcapnLocation::parse(&loc.to_uri_string()).unwrap(), loc);
    }

    // -------------------------------------------------------------------
    // RelayNetlayer
    // -------------------------------------------------------------------

    fn relay_pair() -> (RelayNetlayer, RelayNetlayer, RelayAddr, RelayAddr) {
        let relay: SharedRelay = Arc::new(Mutex::new(MessageRelay::new(16, 64)));
        let (alice_sk, alice_pk) = generate_x25519_keypair();
        let (bob_sk, bob_pk) = generate_x25519_keypair();
        let alice_id = FederationId([0xa1; 32]);
        let bob_id = FederationId([0xb0; 32]);

        let alice = RelayNetlayer::new(relay.clone(), alice_id, alice_sk, 100);
        let bob = RelayNetlayer::new(relay, bob_id, bob_sk, 100);
        let to_bob = RelayAddr {
            peer: bob_id,
            dest_x25519_pk: bob_pk,
        };
        let to_alice = RelayAddr {
            peer: alice_id,
            dest_x25519_pk: alice_pk,
        };
        (alice, bob, to_bob, to_alice)
    }

    #[test]
    fn relay_send_recv_via_store_forward() {
        let (alice, bob, to_bob, to_alice) = relay_pair();

        // Alice dials bob (connectionless: local mint) and sends.
        let a_sess = block_on(alice.dial(&to_bob)).unwrap();
        assert_eq!(a_sess.captp.epoch, 0);
        block_on(a_sess.conn.send(b"sealed greeting".to_vec())).unwrap();

        // Bob accepts: drain surfaces the new sender as an inbound session.
        let b_sess = block_on(bob.accept()).unwrap().expect("inbound session");
        assert_eq!(b_sess.peer(), [0xa1; 32]);
        assert_eq!(
            block_on(b_sess.conn.recv()).unwrap(),
            Some(b"sealed greeting".to_vec())
        );
        // No second sender.
        assert!(block_on(bob.accept()).unwrap().is_none());

        // The accepted session is inbound-only (no key): send fails closed.
        assert!(matches!(
            block_on(b_sess.conn.send(b"reply".to_vec())).unwrap_err(),
            NetlayerError::SendFailed { .. }
        ));

        // Bob dials back with alice's key to reply.
        let b_dial = block_on(bob.dial(&to_alice)).unwrap();
        block_on(b_dial.conn.send(b"sealed reply".to_vec())).unwrap();
        let a_inbound = block_on(alice.accept()).unwrap().expect("reply session");
        assert_eq!(a_inbound.peer(), [0xb0; 32]);
        assert_eq!(
            block_on(a_inbound.conn.recv()).unwrap(),
            Some(b"sealed reply".to_vec())
        );
    }

    #[test]
    fn relay_sees_only_ciphertext() {
        let (alice, _bob, to_bob, _) = relay_pair();
        let relay = alice.relay.clone();

        let a_sess = block_on(alice.dial(&to_bob)).unwrap();
        block_on(a_sess.conn.send(b"top secret plaintext".to_vec())).unwrap();

        // Inspect the queued message as the relay operator would.
        let queued = {
            let mut r = relay.lock().unwrap();
            r.drain(&FederationId([0xb0; 32]))
        };
        assert_eq!(queued.len(), 1);
        let (_, sealed) = split_sender_prefix(&queued[0].encrypted_payload).unwrap();
        // The sealed box never contains the plaintext.
        assert!(
            !sealed
                .windows(b"top secret plaintext".len())
                .any(|w| w == b"top secret plaintext")
        );
    }

    #[test]
    fn relay_preserves_causal_order() {
        let (alice, bob, to_bob, _) = relay_pair();

        let a_sess = block_on(alice.dial(&to_bob)).unwrap();
        for i in 0u8..5 {
            block_on(a_sess.conn.send(vec![i])).unwrap();
        }

        let b_sess = block_on(bob.accept()).unwrap().unwrap();
        for i in 0u8..5 {
            assert_eq!(block_on(b_sess.conn.recv()).unwrap(), Some(vec![i]));
        }
        assert_eq!(block_on(b_sess.conn.recv()).unwrap(), None);
    }

    #[test]
    fn relay_self_location() {
        let (alice, ..) = relay_pair();
        let loc = alice.self_location();
        assert_eq!(loc.hint, "relay");
        assert_eq!(loc.designator, bs58::encode([0xa1; 32]).into_string());
    }
}

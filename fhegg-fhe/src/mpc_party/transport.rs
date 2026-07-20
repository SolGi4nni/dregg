//! Authenticated process transport for scalar PartyMPC equality.
//!
//! This module adapts the existing semi-honest equality runtime without
//! changing its arithmetic. A party process owns its local mod-t operands,
//! Boolean ingress randomness, Beaver row, and `PartyChannels`; the router sees
//! bounded signed frames and their public route only. Peer-ingress payloads are
//! addressed directly to one party and must never be delivered to the
//! coordinator. Gate shares are addressed only to the coordinator; opened
//! Beaver masks are addressed back to one party. The only reconstructed output
//! remains the equality bit in `DecisionTranscript`.
//!
//! Ed25519 authenticates the exact session/sender/recipient/sequence/message
//! bytes and the receiver enforces strict in-order delivery. This closes
//! transport spoofing, cross-session, duplicate, reorder, and misrouting seams.
//! It does **not** prove that a malicious party formed honest input shares,
//! Beaver shares, or gate messages. The arithmetic claim remains the parent
//! module's semi-honest/trusted-preprocessing claim.

use std::collections::HashSet;
use std::fmt;
use std::sync::mpsc::{self, Receiver, Sender, TryRecvError};
use std::thread;

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use sha2::{Digest, Sha256};

use super::{
    run_party_equality, CircuitKind, CoordinatorChannels, CoordinatorMessage, CurveKind,
    DistributedDecisionRun, PartyChannels, PartyEqualityInput, PartyMessage, PartyMpcError,
    PartyMpcSession, PartyReport, PeerInputMessage, TripleMaterial,
};

const FRAME_MAGIC: &[u8; 8] = b"FHEQv001";
const FRAME_SIGNATURE_DOMAIN: &[u8] = b"fhegg/party-mpc-equality-frame-signature/v1";
const FRAME_CHECKSUM_DOMAIN: &[u8] = b"fhegg/party-mpc-equality-frame-checksum/v1";
const SESSION_DOMAIN: &[u8] = b"fhegg/party-mpc-equality-transport-session/v1";
const MAX_FRAME_BYTES: usize = 64 * 1024;
const MAX_PAYLOAD_BYTES: usize = 16 * 1024;
const FIXED_CONTENT_BYTES: usize = 8 + 32 + 4 + 4 + 8 + 1 + 4;
const TRAILER_BYTES: usize = 64 + 32;

const KIND_PEER_INGRESS: u8 = 1;
const KIND_GATE_SHARE: u8 = 2;
const KIND_GATE_OPENED: u8 = 3;
const KIND_DECISION_SHARE: u8 = 4;

/// Stable fail-closed surface for the authenticated equality transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EqualityTransportError {
    InvalidConfiguration(&'static str),
    MalformedFrame(&'static str),
    SessionMismatch,
    SenderMismatch,
    RecipientMismatch,
    SequenceMismatch { sender: usize, have: u64, need: u64 },
    AuthenticationFailed,
    ChannelClosed,
    WorkerPanicked,
    Mpc(PartyMpcError),
}

impl fmt::Display for EqualityTransportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidConfiguration(reason) => {
                write!(f, "invalid equality transport configuration: {reason}")
            }
            Self::MalformedFrame(reason) => write!(f, "malformed equality frame: {reason}"),
            Self::SessionMismatch => write!(f, "equality frame names a different session"),
            Self::SenderMismatch => write!(f, "equality frame names an invalid sender"),
            Self::RecipientMismatch => write!(f, "equality frame is routed to the wrong recipient"),
            Self::SequenceMismatch { sender, have, need } => write!(
                f,
                "equality frame from sender {sender} has sequence {have}, expected {need}"
            ),
            Self::AuthenticationFailed => write!(f, "equality frame authentication failed"),
            Self::ChannelClosed => write!(f, "equality transport channel closed"),
            Self::WorkerPanicked => write!(f, "equality transport worker panicked"),
            Self::Mpc(error) => write!(f, "equality runtime refused: {error}"),
        }
    }
}

impl std::error::Error for EqualityTransportError {}

impl From<PartyMpcError> for EqualityTransportError {
    fn from(error: PartyMpcError) -> Self {
        Self::Mpc(error)
    }
}

type Result<T> = std::result::Result<T, EqualityTransportError>;

/// Ordered transport identities for one equality session.
///
/// Party indices are `0..n`; the coordinator's wire sender id is exactly `n`.
#[derive(Clone)]
pub struct EqualityTransportRoster {
    party_keys: Vec<[u8; 32]>,
    coordinator_key: [u8; 32],
}

impl EqualityTransportRoster {
    pub fn new(party_keys: Vec<[u8; 32]>, coordinator_key: [u8; 32]) -> Result<Self> {
        if party_keys.len() < 2 || party_keys.len() > u32::MAX as usize {
            return Err(EqualityTransportError::InvalidConfiguration(
                "transport requires 2..=u32::MAX parties",
            ));
        }
        let mut seen = HashSet::with_capacity(party_keys.len() + 1);
        for key in party_keys.iter().chain(std::iter::once(&coordinator_key)) {
            let verifying = VerifyingKey::from_bytes(key).map_err(|_| {
                EqualityTransportError::InvalidConfiguration("invalid Ed25519 transport key")
            })?;
            if verifying.is_weak() || !seen.insert(*key) {
                return Err(EqualityTransportError::InvalidConfiguration(
                    "transport keys must be strong and distinct",
                ));
            }
        }
        Ok(Self {
            party_keys,
            coordinator_key,
        })
    }

    pub fn n_parties(&self) -> usize {
        self.party_keys.len()
    }

    pub fn coordinator(&self) -> usize {
        self.party_keys.len()
    }

    fn key(&self, sender: usize) -> Option<[u8; 32]> {
        if sender == self.coordinator() {
            Some(self.coordinator_key)
        } else {
            self.party_keys.get(sender).copied()
        }
    }
}

/// One bounded authenticated wire frame. It intentionally has no `Debug` or
/// `Clone`: peer-ingress payloads contain private Boolean shares. A router may
/// inspect only the public sender/recipient/sequence and forward the bytes.
pub struct AuthenticatedEqualityFrame {
    sender: usize,
    recipient: usize,
    sequence: u64,
    wire: Vec<u8>,
}

impl AuthenticatedEqualityFrame {
    pub fn sender(&self) -> usize {
        self.sender
    }

    pub fn recipient(&self) -> usize {
        self.recipient
    }

    pub fn sequence(&self) -> u64 {
        self.sequence
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.wire
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.wire
    }
}

enum RawOutbound {
    Peer(PeerInputMessage),
    Party(PartyMessage),
    Coordinator {
        recipient: usize,
        message: CoordinatorMessage,
    },
}

/// Party-side adapter. Construct this inside the party process after deriving
/// its local mod-t operands; no operand/share accessor is exposed.
pub struct EqualityPartyMachine {
    session: PartyMpcSession,
    session_digest: [u8; 32],
    roster: EqualityTransportRoster,
    party: usize,
    signing_key: SigningKey,
    outbound: Receiver<RawOutbound>,
    peer_in: Sender<PeerInputMessage>,
    coordinator_in: Sender<CoordinatorMessage>,
    result: Receiver<std::result::Result<PartyReport, PartyMpcError>>,
    outbound_sequences: Vec<u64>,
    inbound_sequences: Vec<u64>,
}

impl EqualityPartyMachine {
    pub fn new(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        party: usize,
        signing_key: SigningKey,
        input: PartyEqualityInput,
        preprocessing: TripleMaterial,
    ) -> Result<Self> {
        validate_transport_session(&session, &roster)?;
        if party >= roster.n_parties()
            || signing_key.verifying_key().to_bytes() != roster.party_keys[party]
        {
            return Err(EqualityTransportError::InvalidConfiguration(
                "party signing key does not match its roster slot",
            ));
        }

        let (party_out_tx, party_out_rx) = mpsc::channel();
        let (peer_out_tx, peer_out_rx) = mpsc::channel();
        let (peer_in_tx, peer_in_rx) = mpsc::channel();
        let (coordinator_in_tx, coordinator_in_rx) = mpsc::channel();
        let channels = PartyChannels {
            party,
            to_coordinator: party_out_tx,
            from_coordinator: coordinator_in_rx,
            to_peers: vec![peer_out_tx; roster.n_parties()],
            from_peers: peer_in_rx,
        };
        let (outbound_tx, outbound_rx) = mpsc::channel();
        let peer_forward = outbound_tx.clone();
        drop(thread::spawn(move || {
            while let Ok(message) = peer_out_rx.recv() {
                if peer_forward.send(RawOutbound::Peer(message)).is_err() {
                    break;
                }
            }
        }));
        let party_forward = outbound_tx;
        drop(thread::spawn(move || {
            while let Ok(message) = party_out_rx.recv() {
                if party_forward.send(RawOutbound::Party(message)).is_err() {
                    break;
                }
            }
        }));
        let (result_tx, result_rx) = mpsc::channel();
        drop(thread::spawn(move || {
            let _ = result_tx.send(run_party_equality(input, preprocessing, channels));
        }));

        Ok(Self {
            session_digest: equality_session_digest(&session, &roster)?,
            session,
            roster: roster.clone(),
            party,
            signing_key,
            outbound: outbound_rx,
            peer_in: peer_in_tx,
            coordinator_in: coordinator_in_tx,
            result: result_rx,
            outbound_sequences: vec![0; roster.n_parties() + 1],
            inbound_sequences: vec![0; roster.n_parties() + 1],
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn try_next_frame(&mut self) -> Result<Option<AuthenticatedEqualityFrame>> {
        match self.outbound.try_recv() {
            Ok(raw) => {
                let (recipient, payload) = encode_party_outbound(&self.session, self.party, raw)?;
                let sequence = self.outbound_sequences[recipient];
                self.outbound_sequences[recipient] =
                    sequence
                        .checked_add(1)
                        .ok_or(EqualityTransportError::MalformedFrame(
                            "outbound sequence exhausted",
                        ))?;
                Ok(Some(sign_frame(
                    self.session_digest,
                    self.party,
                    recipient,
                    sequence,
                    payload,
                    &self.signing_key,
                )?))
            }
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => Ok(None),
        }
    }

    pub fn accept_frame(&mut self, bytes: &[u8]) -> Result<()> {
        let decoded = verify_frame(bytes, self.session_digest, self.party, &self.roster)?;
        let expected = self
            .inbound_sequences
            .get(decoded.sender)
            .copied()
            .ok_or(EqualityTransportError::SenderMismatch)?;
        if decoded.sequence != expected {
            return Err(EqualityTransportError::SequenceMismatch {
                sender: decoded.sender,
                have: decoded.sequence,
                need: expected,
            });
        }
        let sender = decoded.sender;
        match decode_party_inbound(&self.session, self.party, decoded)? {
            PartyInbound::Peer(message) => self
                .peer_in
                .send(message)
                .map_err(|_| EqualityTransportError::ChannelClosed)?,
            PartyInbound::Coordinator(message) => self
                .coordinator_in
                .send(message)
                .map_err(|_| EqualityTransportError::ChannelClosed)?,
        }
        self.inbound_sequences[sender] = expected + 1;
        Ok(())
    }

    pub fn try_result(&mut self) -> Result<Option<PartyReport>> {
        match self.result.try_recv() {
            Ok(result) => result.map(Some).map_err(Into::into),
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => Err(EqualityTransportError::WorkerPanicked),
        }
    }
}

/// Coordinator-side adapter. It receives only gate/final shares and therefore
/// has no endpoint capable of accepting peer-ingress or raw mod-t operands.
pub struct EqualityCoordinatorMachine {
    session: PartyMpcSession,
    session_digest: [u8; 32],
    roster: EqualityTransportRoster,
    signing_key: SigningKey,
    party_in: Sender<PartyMessage>,
    outbound: Receiver<RawOutbound>,
    result: Receiver<std::result::Result<DistributedDecisionRun, PartyMpcError>>,
    outbound_sequences: Vec<u64>,
    inbound_sequences: Vec<u64>,
}

impl EqualityCoordinatorMachine {
    pub fn new(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        signing_key: SigningKey,
    ) -> Result<Self> {
        validate_transport_session(&session, &roster)?;
        if signing_key.verifying_key().to_bytes() != roster.coordinator_key {
            return Err(EqualityTransportError::InvalidConfiguration(
                "coordinator signing key does not match the roster",
            ));
        }
        let (party_in_tx, party_in_rx) = mpsc::channel();
        let (outbound_tx, outbound_rx) = mpsc::channel();
        let mut to_parties = Vec::with_capacity(roster.n_parties());
        for recipient in 0..roster.n_parties() {
            let (tx, rx) = mpsc::channel();
            to_parties.push(tx);
            let forward = outbound_tx.clone();
            drop(thread::spawn(move || {
                while let Ok(message) = rx.recv() {
                    if forward
                        .send(RawOutbound::Coordinator { recipient, message })
                        .is_err()
                    {
                        break;
                    }
                }
            }));
        }
        drop(outbound_tx);
        let channels = CoordinatorChannels {
            from_parties: party_in_rx,
            to_parties,
        };
        let result_session = session.clone();
        let (result_tx, result_rx) = mpsc::channel();
        drop(thread::spawn(move || {
            let _ = result_tx.send(channels.coordinate_equality(&result_session));
        }));
        Ok(Self {
            session_digest: equality_session_digest(&session, &roster)?,
            session,
            roster: roster.clone(),
            signing_key,
            party_in: party_in_tx,
            outbound: outbound_rx,
            result: result_rx,
            outbound_sequences: vec![0; roster.n_parties()],
            inbound_sequences: vec![0; roster.n_parties()],
        })
    }

    pub fn try_next_frame(&mut self) -> Result<Option<AuthenticatedEqualityFrame>> {
        match self.outbound.try_recv() {
            Ok(RawOutbound::Coordinator { recipient, message }) => {
                let payload = encode_coordinator_outbound(&self.session, message)?;
                let sequence = self.outbound_sequences[recipient];
                self.outbound_sequences[recipient] =
                    sequence
                        .checked_add(1)
                        .ok_or(EqualityTransportError::MalformedFrame(
                            "outbound sequence exhausted",
                        ))?;
                Ok(Some(sign_frame(
                    self.session_digest,
                    self.roster.coordinator(),
                    recipient,
                    sequence,
                    payload,
                    &self.signing_key,
                )?))
            }
            Ok(_) => Err(EqualityTransportError::MalformedFrame(
                "coordinator emitted a party message",
            )),
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => Ok(None),
        }
    }

    pub fn accept_frame(&mut self, bytes: &[u8]) -> Result<()> {
        let decoded = verify_frame(
            bytes,
            self.session_digest,
            self.roster.coordinator(),
            &self.roster,
        )?;
        if decoded.sender >= self.roster.n_parties() {
            return Err(EqualityTransportError::SenderMismatch);
        }
        let expected = self.inbound_sequences[decoded.sender];
        if decoded.sequence != expected {
            return Err(EqualityTransportError::SequenceMismatch {
                sender: decoded.sender,
                have: decoded.sequence,
                need: expected,
            });
        }
        let sender = decoded.sender;
        let message = decode_coordinator_inbound(&self.session, decoded)?;
        self.party_in
            .send(message)
            .map_err(|_| EqualityTransportError::ChannelClosed)?;
        self.inbound_sequences[sender] = expected + 1;
        Ok(())
    }

    pub fn try_result(&mut self) -> Result<Option<DistributedDecisionRun>> {
        match self.result.try_recv() {
            Ok(result) => result.map(Some).map_err(Into::into),
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => Err(EqualityTransportError::WorkerPanicked),
        }
    }
}

fn validate_transport_session(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
) -> Result<()> {
    if session.circuit != CircuitKind::Equality {
        return Err(EqualityTransportError::InvalidConfiguration(
            "transport supports equality sessions only",
        ));
    }
    if session.n_parties != roster.n_parties() {
        return Err(EqualityTransportError::InvalidConfiguration(
            "session and transport roster sizes differ",
        ));
    }
    Ok(())
}

struct EncodedPayload {
    kind: u8,
    bytes: Vec<u8>,
}

fn encode_party_outbound(
    session: &PartyMpcSession,
    party: usize,
    raw: RawOutbound,
) -> Result<(usize, EncodedPayload)> {
    match raw {
        RawOutbound::Peer(message) => {
            if message.session != session.binding() || message.from != party {
                return Err(EqualityTransportError::SessionMismatch);
            }
            let mut payload = Vec::with_capacity(16 + message.bits.len());
            payload.push(match message.curve {
                CurveKind::Demand => 0,
                CurveKind::Supply => 1,
            });
            put_u64(&mut payload, message.bucket)?;
            put_u32(&mut payload, message.bits.len())?;
            payload.extend_from_slice(&message.bits);
            Ok((
                message.to,
                EncodedPayload {
                    kind: KIND_PEER_INGRESS,
                    bytes: payload,
                },
            ))
        }
        RawOutbound::Party(PartyMessage::GateShare {
            session: binding,
            party: message_party,
            gate,
            d,
            e,
        }) => {
            if binding != session.binding() || message_party != party || d > 1 || e > 1 {
                return Err(EqualityTransportError::SessionMismatch);
            }
            let mut payload = Vec::with_capacity(10);
            put_u64(&mut payload, gate)?;
            payload.extend_from_slice(&[d, e]);
            Ok((
                session.n_parties,
                EncodedPayload {
                    kind: KIND_GATE_SHARE,
                    bytes: payload,
                },
            ))
        }
        RawOutbound::Party(PartyMessage::DecisionShare {
            session: binding,
            party: message_party,
            equal,
        }) => {
            if binding != session.binding() || message_party != party || equal > 1 {
                return Err(EqualityTransportError::SessionMismatch);
            }
            Ok((
                session.n_parties,
                EncodedPayload {
                    kind: KIND_DECISION_SHARE,
                    bytes: vec![equal],
                },
            ))
        }
        _ => Err(EqualityTransportError::MalformedFrame(
            "non-equality party message",
        )),
    }
}

fn encode_coordinator_outbound(
    session: &PartyMpcSession,
    message: CoordinatorMessage,
) -> Result<EncodedPayload> {
    match message {
        CoordinatorMessage::GateOpened {
            session: binding,
            gate,
            d,
            e,
        } => {
            if binding != session.binding() || d > 1 || e > 1 {
                return Err(EqualityTransportError::SessionMismatch);
            }
            let mut bytes = Vec::with_capacity(10);
            put_u64(&mut bytes, gate)?;
            bytes.extend_from_slice(&[d, e]);
            Ok(EncodedPayload {
                kind: KIND_GATE_OPENED,
                bytes,
            })
        }
    }
}

enum PartyInbound {
    Peer(PeerInputMessage),
    Coordinator(CoordinatorMessage),
}

struct DecodedFrame<'a> {
    sender: usize,
    recipient: usize,
    sequence: u64,
    kind: u8,
    payload: &'a [u8],
}

fn decode_party_inbound(
    session: &PartyMpcSession,
    party: usize,
    frame: DecodedFrame<'_>,
) -> Result<PartyInbound> {
    match frame.kind {
        KIND_PEER_INGRESS => {
            if frame.sender >= session.n_parties || frame.recipient != party {
                return Err(EqualityTransportError::RecipientMismatch);
            }
            let mut input = Reader::new(frame.payload);
            let curve = match input.byte()? {
                0 => CurveKind::Demand,
                1 => CurveKind::Supply,
                _ => return Err(EqualityTransportError::MalformedFrame("invalid curve tag")),
            };
            let bucket = input.usize()?;
            let bits = input.bytes(MAX_PAYLOAD_BYTES)?.to_vec();
            input.finish()?;
            if bucket >= session.buckets
                || bits.len() != session.ingress_bits()
                || bits.iter().any(|bit| *bit > 1)
            {
                return Err(EqualityTransportError::MalformedFrame(
                    "peer ingress shape mismatch",
                ));
            }
            Ok(PartyInbound::Peer(PeerInputMessage {
                session: session.binding(),
                from: frame.sender,
                to: party,
                curve,
                bucket,
                bits,
            }))
        }
        KIND_GATE_OPENED => {
            if frame.sender != session.n_parties || frame.recipient != party {
                return Err(EqualityTransportError::SenderMismatch);
            }
            let (gate, d, e) = decode_gate(frame.payload)?;
            Ok(PartyInbound::Coordinator(CoordinatorMessage::GateOpened {
                session: session.binding(),
                gate,
                d,
                e,
            }))
        }
        _ => Err(EqualityTransportError::MalformedFrame(
            "message kind is not party-addressed",
        )),
    }
}

fn decode_coordinator_inbound(
    session: &PartyMpcSession,
    frame: DecodedFrame<'_>,
) -> Result<PartyMessage> {
    if frame.sender >= session.n_parties || frame.recipient != session.n_parties {
        return Err(EqualityTransportError::RecipientMismatch);
    }
    match frame.kind {
        KIND_GATE_SHARE => {
            let (gate, d, e) = decode_gate(frame.payload)?;
            Ok(PartyMessage::GateShare {
                session: session.binding(),
                party: frame.sender,
                gate,
                d,
                e,
            })
        }
        KIND_DECISION_SHARE => {
            if frame.payload.len() != 1 || frame.payload[0] > 1 {
                return Err(EqualityTransportError::MalformedFrame(
                    "invalid decision share",
                ));
            }
            Ok(PartyMessage::DecisionShare {
                session: session.binding(),
                party: frame.sender,
                equal: frame.payload[0],
            })
        }
        _ => Err(EqualityTransportError::MalformedFrame(
            "message kind is not coordinator-addressed",
        )),
    }
}

fn decode_gate(payload: &[u8]) -> Result<(usize, u8, u8)> {
    if payload.len() != 10 || payload[8] > 1 || payload[9] > 1 {
        return Err(EqualityTransportError::MalformedFrame(
            "invalid gate payload",
        ));
    }
    let gate =
        usize::try_from(u64::from_be_bytes(payload[..8].try_into().map_err(
            |_| EqualityTransportError::MalformedFrame("invalid gate index"),
        )?))
        .map_err(|_| EqualityTransportError::MalformedFrame("gate index does not fit usize"))?;
    Ok((gate, payload[8], payload[9]))
}

fn sign_frame(
    session_digest: [u8; 32],
    sender: usize,
    recipient: usize,
    sequence: u64,
    payload: EncodedPayload,
    signing_key: &SigningKey,
) -> Result<AuthenticatedEqualityFrame> {
    if payload.bytes.len() > MAX_PAYLOAD_BYTES {
        return Err(EqualityTransportError::MalformedFrame(
            "payload exceeds its allocation limit",
        ));
    }
    let sender_u32 = u32::try_from(sender)
        .map_err(|_| EqualityTransportError::MalformedFrame("sender does not fit u32"))?;
    let recipient_u32 = u32::try_from(recipient)
        .map_err(|_| EqualityTransportError::MalformedFrame("recipient does not fit u32"))?;
    let payload_len = u32::try_from(payload.bytes.len())
        .map_err(|_| EqualityTransportError::MalformedFrame("payload length does not fit u32"))?;
    let mut wire = Vec::with_capacity(FIXED_CONTENT_BYTES + payload.bytes.len() + TRAILER_BYTES);
    wire.extend_from_slice(FRAME_MAGIC);
    wire.extend_from_slice(&session_digest);
    wire.extend_from_slice(&sender_u32.to_be_bytes());
    wire.extend_from_slice(&recipient_u32.to_be_bytes());
    wire.extend_from_slice(&sequence.to_be_bytes());
    wire.push(payload.kind);
    wire.extend_from_slice(&payload_len.to_be_bytes());
    wire.extend_from_slice(&payload.bytes);
    let signature = signing_key.sign(&frame_signing_message(&wire));
    wire.extend_from_slice(&signature.to_bytes());
    wire.extend_from_slice(&frame_checksum(&wire));
    if wire.len() > MAX_FRAME_BYTES {
        return Err(EqualityTransportError::MalformedFrame(
            "frame exceeds its allocation limit",
        ));
    }
    Ok(AuthenticatedEqualityFrame {
        sender,
        recipient,
        sequence,
        wire,
    })
}

fn verify_frame<'a>(
    bytes: &'a [u8],
    expected_session: [u8; 32],
    expected_recipient: usize,
    roster: &EqualityTransportRoster,
) -> Result<DecodedFrame<'a>> {
    if bytes.len() < FIXED_CONTENT_BYTES + TRAILER_BYTES || bytes.len() > MAX_FRAME_BYTES {
        return Err(EqualityTransportError::MalformedFrame(
            "frame length is outside its bounds",
        ));
    }
    let checksum_start = bytes.len() - 32;
    if bytes[checksum_start..] != frame_checksum(&bytes[..checksum_start]) {
        return Err(EqualityTransportError::MalformedFrame(
            "frame checksum mismatch",
        ));
    }
    let signature_start = checksum_start - 64;
    let content = &bytes[..signature_start];
    let mut input = Reader::new(content);
    if input.array::<8>()? != *FRAME_MAGIC {
        return Err(EqualityTransportError::MalformedFrame(
            "wrong frame version",
        ));
    }
    if input.array::<32>()? != expected_session {
        return Err(EqualityTransportError::SessionMismatch);
    }
    let sender = input.u32()? as usize;
    let recipient = input.u32()? as usize;
    let sequence = input.u64()?;
    let kind = input.byte()?;
    let payload = input.bytes(MAX_PAYLOAD_BYTES)?;
    input.finish()?;
    if recipient != expected_recipient {
        return Err(EqualityTransportError::RecipientMismatch);
    }
    let public_key = roster
        .key(sender)
        .ok_or(EqualityTransportError::SenderMismatch)?;
    let verifying = VerifyingKey::from_bytes(&public_key)
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
    let signature_bytes: [u8; 64] = bytes[signature_start..checksum_start]
        .try_into()
        .map_err(|_| EqualityTransportError::MalformedFrame("invalid signature length"))?;
    verifying
        .verify_strict(
            &frame_signing_message(content),
            &Signature::from_bytes(&signature_bytes),
        )
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
    Ok(DecodedFrame {
        sender,
        recipient,
        sequence,
        kind,
        payload,
    })
}

fn equality_session_digest(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
) -> Result<[u8; 32]> {
    if session.circuit != CircuitKind::Equality {
        return Err(EqualityTransportError::InvalidConfiguration(
            "transport session is not equality",
        ));
    }
    let mut hash = Sha256::new();
    hash.update((SESSION_DOMAIN.len() as u64).to_be_bytes());
    hash.update(SESSION_DOMAIN);
    hash.update(session.nonce);
    hash.update((session.n_parties as u64).to_be_bytes());
    hash.update((session.buckets as u64).to_be_bytes());
    hash.update((session.value_bits as u64).to_be_bytes());
    hash.update(session.plaintext_modulus.to_be_bytes());
    hash.update(session.quorum_timeout.as_secs().to_be_bytes());
    hash.update(session.quorum_timeout.subsec_nanos().to_be_bytes());
    hash.update([1u8]);
    hash.update((roster.party_keys.len() as u64).to_be_bytes());
    for key in &roster.party_keys {
        hash.update(key);
    }
    hash.update(roster.coordinator_key);
    Ok(hash.finalize().into())
}

fn frame_signing_message(content: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((FRAME_SIGNATURE_DOMAIN.len() as u64).to_be_bytes());
    hash.update(FRAME_SIGNATURE_DOMAIN);
    hash.update((content.len() as u64).to_be_bytes());
    hash.update(content);
    hash.finalize().into()
}

fn frame_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((FRAME_CHECKSUM_DOMAIN.len() as u64).to_be_bytes());
    hash.update(FRAME_CHECKSUM_DOMAIN);
    hash.update((content.len() as u64).to_be_bytes());
    hash.update(content);
    hash.finalize().into()
}

fn put_u64(out: &mut Vec<u8>, value: usize) -> Result<()> {
    let value = u64::try_from(value)
        .map_err(|_| EqualityTransportError::MalformedFrame("value does not fit u64"))?;
    out.extend_from_slice(&value.to_be_bytes());
    Ok(())
}

fn put_u32(out: &mut Vec<u8>, value: usize) -> Result<()> {
    let value = u32::try_from(value)
        .map_err(|_| EqualityTransportError::MalformedFrame("value does not fit u32"))?;
    out.extend_from_slice(&value.to_be_bytes());
    Ok(())
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(EqualityTransportError::MalformedFrame("truncated field"))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.take(N)?
            .try_into()
            .map_err(|_| EqualityTransportError::MalformedFrame("invalid fixed-width field"))
    }

    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_be_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_be_bytes(self.array()?))
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(self.u64()?)
            .map_err(|_| EqualityTransportError::MalformedFrame("value does not fit usize"))
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8]> {
        let len = self.u32()? as usize;
        if len > max {
            return Err(EqualityTransportError::MalformedFrame(
                "length-delimited field exceeds its limit",
            ));
        }
        self.take(len)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(EqualityTransportError::MalformedFrame("trailing bytes"))
        }
    }
}

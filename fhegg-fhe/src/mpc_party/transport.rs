//! Authenticated process transport for PartyMPC equality and crossing.
//!
//! This module adapts the existing semi-honest runtimes without changing their
//! arithmetic. A party process owns its local mod-t operands, Boolean ingress
//! randomness, Beaver row, and `PartyChannels`; the router sees bounded signed
//! frames and their public route only. Peer-ingress payloads are end-to-end
//! encrypted between their two party processes, so an untrusted router can
//! forward every frame without reconstructing the Boolean ingress. Gate shares
//! are addressed only to the coordinator; opened Beaver masks are addressed
//! back to one party. The only reconstructed result is either the equality bit
//! in `DecisionTranscript` or `(p*, V*)` in `DistributedTranscript`.
//!
//! [`TransportSecurityProfile::NativePostQuantum`] authenticates every exact
//! session/sender/recipient/sequence/role/ciphertext frame with both Ed25519 and
//! roster-pinned ML-DSA-65. Each peer-ingress frame performs a fresh ML-KEM-768
//! encapsulation to the named roster key and combines that secret with the
//! existing X25519 shared secret using dregg's canonical hybrid combiner before
//! XChaCha20-Poly1305. The receiver authenticates and key-confirms before parsing
//! plaintext, then enforces strict in-order delivery. A different roster key or
//! security profile changes the session digest, so key substitution, downgrade,
//! cross-session replay, duplicate/reorder, and misrouting fail closed.
//!
//! [`TransportSecurityProfile::ClassicalCompatibility`] retains Ed25519 plus
//! static converted-X25519 as an explicitly named compatibility profile.
//! Neither profile claims forward secrecy: both use long-lived identity DH
//! material, and native-PQ uses a long-lived recipient ML-KEM key even though
//! each frame has a fresh encapsulation.
//! It does **not** prove that a malicious party formed honest input shares,
//! Beaver shares, or gate messages. The arithmetic claim remains the parent
//! module's semi-honest/trusted-preprocessing claim.

use std::collections::HashSet;
use std::fmt;
use std::sync::mpsc::{self, Receiver, Sender, TryRecvError};
use std::thread;

use chacha20poly1305::aead::{Aead, KeyInit, Payload};
use chacha20poly1305::{XChaCha20Poly1305, XNonce};
use curve25519_dalek::edwards::CompressedEdwardsY;
use dregg_pq::hybrid_kem::combine as combine_hybrid_kem;
use dregg_pq::{
    ml_dsa_verify, ml_kem768_decaps, ml_kem768_encaps, ml_kem768_keygen, MlDsaKey, ML_DSA_PK_LEN,
    ML_DSA_SIG_LEN,
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use hkdf::Hkdf;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore};
use sha2::{Digest, Sha256, Sha512};

use super::{
    run_party, run_party_equality, CircuitKind, CoordinatorChannels, CoordinatorMessage, CurveKind,
    DecisionTranscript, DistributedDecisionRun, DistributedRun, DistributedTranscript,
    PartyArithmeticInput, PartyChannels, PartyEqualityInput, PartyMessage, PartyMpcError,
    PartyMpcSession, PartyReport, PeerInputMessage, TripleMaterial,
};
use crate::mpc::{index_bits, Crossing};

const FRAME_MAGIC: &[u8; 8] = b"FHEQv004";
const FRAME_SIGNATURE_DOMAIN: &[u8] = b"fhegg/party-mpc-frame-signature/v4";
const FRAME_ML_DSA_CONTEXT: &[u8] = b"fhegg/party-mpc/frame/v4";
const FRAME_CHECKSUM_DOMAIN: &[u8] = b"fhegg/party-mpc-frame-checksum/v4";
const SESSION_DOMAIN: &[u8] = b"fhegg/party-mpc-transport-session/v4";
const PEER_KEY_DOMAIN: &[u8] = b"fhegg/party-mpc-peer-key/classical-compat/v4";
const PEER_HYBRID_TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/party-mpc-peer-hybrid-kem/v4";
const PEER_AAD_DOMAIN: &[u8] = b"fhegg/party-mpc-peer-aead/v4";
const PREPROCESSING_SEED_DOMAIN: &[u8] = b"fhegg/party-mpc-equality-fresh-preprocessing/v1";
const CROSSING_PREPROCESSING_SEED_DOMAIN: &[u8] =
    b"fhegg/party-mpc-crossing-fresh-preprocessing/v1";
const MAX_FRAME_BYTES: usize = 64 * 1024;
const MAX_PAYLOAD_BYTES: usize = 16 * 1024;
const PEER_NONCE_BYTES: usize = 24;
const PEER_AEAD_TAG_BYTES: usize = 16;
const FIXED_CONTENT_BYTES: usize = 8 + 1 + 64 + 4 + 4 + 8 + 1 + 4;
const CLASSICAL_TRAILER_BYTES: usize = 64 + 32;
const NATIVE_PQ_TRAILER_BYTES: usize = 64 + ML_DSA_SIG_LEN + 32;
const ML_KEM_768_EK_BYTES: usize = 1_184;
const ML_KEM_768_DK_BYTES: usize = 2_400;
const ML_KEM_768_CT_BYTES: usize = 1_088;

type TransportSessionDigest = [u8; 64];

const KIND_PEER_INGRESS: u8 = 1;
const KIND_GATE_SHARE: u8 = 2;
const KIND_GATE_OPENED: u8 = 3;
const KIND_DECISION_SHARE: u8 = 4;
const KIND_OUTPUT_SHARE: u8 = 5;

/// Stable fail-closed surface for the authenticated PartyMPC transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EqualityTransportError {
    InvalidConfiguration(&'static str),
    MalformedFrame(&'static str),
    SessionMismatch,
    SenderMismatch,
    RecipientMismatch,
    SequenceMismatch { sender: usize, have: u64, need: u64 },
    AuthenticationFailed,
    ConfidentialityFailed,
    EntropyUnavailable,
    ChannelClosed,
    WorkerPanicked,
    Mpc(PartyMpcError),
}

impl fmt::Display for EqualityTransportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidConfiguration(reason) => {
                write!(f, "invalid PartyMPC transport configuration: {reason}")
            }
            Self::MalformedFrame(reason) => write!(f, "malformed PartyMPC frame: {reason}"),
            Self::SessionMismatch => write!(f, "PartyMPC frame names a different session"),
            Self::SenderMismatch => write!(f, "PartyMPC frame names an invalid sender"),
            Self::RecipientMismatch => {
                write!(f, "PartyMPC frame is routed to the wrong recipient")
            }
            Self::SequenceMismatch { sender, have, need } => write!(
                f,
                "PartyMPC frame from sender {sender} has sequence {have}, expected {need}"
            ),
            Self::AuthenticationFailed => write!(f, "PartyMPC frame authentication failed"),
            Self::ConfidentialityFailed => {
                write!(f, "PartyMPC peer-ingress confidentiality check failed")
            }
            Self::EntropyUnavailable => {
                write!(f, "PartyMPC transport could not obtain fresh OS entropy")
            }
            Self::ChannelClosed => write!(f, "PartyMPC transport channel closed"),
            Self::WorkerPanicked => write!(f, "PartyMPC transport worker panicked"),
            Self::Mpc(error) => write!(f, "PartyMPC runtime refused: {error}"),
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

/// Cryptographic envelope selected for an entire ordered PartyMPC roster.
///
/// This tag is hashed into the transport session and encoded in every frame;
/// it is not a negotiable per-connection preference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransportSecurityProfile {
    /// Ed25519 authentication plus static converted-X25519 confidentiality.
    ClassicalCompatibility,
    /// Mandatory Ed25519 + ML-DSA-65 authentication and X25519 + ML-KEM-768
    /// hybrid peer confidentiality.
    NativePostQuantum,
}

impl TransportSecurityProfile {
    fn wire_tag(self) -> u8 {
        match self {
            Self::ClassicalCompatibility => 0,
            Self::NativePostQuantum => 1,
        }
    }

    fn trailer_bytes(self) -> usize {
        match self {
            Self::ClassicalCompatibility => CLASSICAL_TRAILER_BYTES,
            Self::NativePostQuantum => NATIVE_PQ_TRAILER_BYTES,
        }
    }
}

/// Roster-pinned public half of one native-PQ transport identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePqTransportPublicIdentity {
    ed25519: [u8; 32],
    ml_dsa: Vec<u8>,
    ml_kem_ek: Vec<u8>,
}

impl NativePqTransportPublicIdentity {
    /// Construct an enrollment record from externally persisted public bytes.
    /// Cryptographic decoding remains fail-closed at signature/KEM use; this
    /// boundary rejects wrong deployed lengths before a roster can be formed.
    pub fn from_parts(ed25519: [u8; 32], ml_dsa: Vec<u8>, ml_kem_ek: Vec<u8>) -> Result<Self> {
        if ml_dsa.len() != ML_DSA_PK_LEN || ml_kem_ek.len() != ML_KEM_768_EK_BYTES {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ public identity has malformed deployed key material",
            ));
        }
        Ok(Self {
            ed25519,
            ml_dsa,
            ml_kem_ek,
        })
    }

    pub fn ed25519(&self) -> [u8; 32] {
        self.ed25519
    }

    pub fn ml_dsa(&self) -> &[u8] {
        &self.ml_dsa
    }

    pub fn ml_kem_encapsulation_key(&self) -> &[u8] {
        &self.ml_kem_ek
    }
}

/// Secret endpoint material for one native-PQ roster slot.
///
/// The X25519 and ML-DSA identities are deterministically bound to the same
/// Ed25519 seed. The ML-KEM recipient key is independently generated and must
/// be persisted with the roster enrollment. Long-lived material means this is
/// harvest-now resistant under ML-KEM, but it does not provide forward secrecy.
#[derive(Clone)]
pub struct NativePqTransportIdentity {
    signing_key: SigningKey,
    ml_dsa: MlDsaKey,
    ml_kem_ek: Vec<u8>,
    ml_kem_dk: Vec<u8>,
}

impl fmt::Debug for NativePqTransportIdentity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("NativePqTransportIdentity(..)")
    }
}

impl NativePqTransportIdentity {
    /// Generate a fresh ML-KEM-768 recipient key and derive the ML-DSA-65 key
    /// from this endpoint's enrolled Ed25519 seed.
    pub fn generate(signing_key: SigningKey) -> Self {
        let ml_dsa = MlDsaKey::from_ed25519_seed(&signing_key.to_bytes());
        let (ml_kem_ek, ml_kem_dk) = ml_kem768_keygen();
        Self {
            signing_key,
            ml_dsa,
            ml_kem_ek,
            ml_kem_dk,
        }
    }

    /// Restore persisted endpoint material. Exact deployed ML-KEM lengths are
    /// checked here; possession/correspondence is key-confirmed by AEAD on use.
    pub fn from_material(
        signing_key: SigningKey,
        ml_kem_ek: Vec<u8>,
        ml_kem_dk: Vec<u8>,
    ) -> Result<Self> {
        if ml_kem_ek.len() != ML_KEM_768_EK_BYTES || ml_kem_dk.len() != ML_KEM_768_DK_BYTES {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ identity has malformed ML-KEM-768 material",
            ));
        }
        let ml_dsa = MlDsaKey::from_ed25519_seed(&signing_key.to_bytes());
        Ok(Self {
            signing_key,
            ml_dsa,
            ml_kem_ek,
            ml_kem_dk,
        })
    }

    pub fn public_identity(&self) -> NativePqTransportPublicIdentity {
        NativePqTransportPublicIdentity {
            ed25519: self.signing_key.verifying_key().to_bytes(),
            ml_dsa: self.ml_dsa.public_bytes(),
            ml_kem_ek: self.ml_kem_ek.clone(),
        }
    }
}

/// Ordered transport identities for one PartyMPC session.
///
/// Party indices are `0..n`; the coordinator's wire sender id is exactly `n`.
#[derive(Clone)]
pub struct EqualityTransportRoster {
    party_keys: Vec<[u8; 32]>,
    coordinator_key: [u8; 32],
    profile: TransportSecurityProfile,
    native_party_keys: Vec<NativePqTransportPublicIdentity>,
    native_coordinator_key: Option<NativePqTransportPublicIdentity>,
}

impl EqualityTransportRoster {
    /// Legacy spelling retained for source compatibility. The resulting roster
    /// is explicitly tagged classical on the wire and in the session digest.
    pub fn new(party_keys: Vec<[u8; 32]>, coordinator_key: [u8; 32]) -> Result<Self> {
        Self::new_classical_compatibility(party_keys, coordinator_key)
    }

    pub fn new_classical_compatibility(
        party_keys: Vec<[u8; 32]>,
        coordinator_key: [u8; 32],
    ) -> Result<Self> {
        Self::validate_ed25519_roster(&party_keys, coordinator_key)?;
        Ok(Self {
            party_keys,
            coordinator_key,
            profile: TransportSecurityProfile::ClassicalCompatibility,
            native_party_keys: Vec::new(),
            native_coordinator_key: None,
        })
    }

    pub fn new_native_post_quantum(
        party_keys: Vec<NativePqTransportPublicIdentity>,
        coordinator_key: NativePqTransportPublicIdentity,
    ) -> Result<Self> {
        let ed25519_party_keys: Vec<_> = party_keys.iter().map(|key| key.ed25519).collect();
        Self::validate_ed25519_roster(&ed25519_party_keys, coordinator_key.ed25519)?;
        let mut seen_ml_dsa = HashSet::with_capacity(party_keys.len() + 1);
        let mut seen_ml_kem = HashSet::with_capacity(party_keys.len() + 1);
        for key in party_keys.iter().chain(std::iter::once(&coordinator_key)) {
            if key.ml_dsa.len() != ML_DSA_PK_LEN
                || key.ml_kem_ek.len() != ML_KEM_768_EK_BYTES
                || !seen_ml_dsa.insert(key.ml_dsa.clone())
                || !seen_ml_kem.insert(key.ml_kem_ek.clone())
            {
                return Err(EqualityTransportError::InvalidConfiguration(
                    "native-PQ roster keys must have deployed lengths and be distinct",
                ));
            }
        }
        Ok(Self {
            party_keys: ed25519_party_keys,
            coordinator_key: coordinator_key.ed25519,
            profile: TransportSecurityProfile::NativePostQuantum,
            native_party_keys: party_keys,
            native_coordinator_key: Some(coordinator_key),
        })
    }

    fn validate_ed25519_roster(party_keys: &[[u8; 32]], coordinator_key: [u8; 32]) -> Result<()> {
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
        // Distinct Ed25519 encodings are not sufficient for the peer-DH role:
        // Edwards P and -P have different encodings but the same Montgomery
        // u-coordinate. Reject that alias (and zero) at roster construction so
        // two logical parties can never collapse onto one confidentiality key.
        let mut seen_montgomery = HashSet::with_capacity(party_keys.len());
        for key in party_keys {
            let montgomery = CompressedEdwardsY(*key)
                .decompress()
                .ok_or(EqualityTransportError::InvalidConfiguration(
                    "party key cannot be converted for peer confidentiality",
                ))?
                .to_montgomery()
                .to_bytes();
            if montgomery.iter().all(|byte| *byte == 0) || !seen_montgomery.insert(montgomery) {
                return Err(EqualityTransportError::InvalidConfiguration(
                    "party keys must have distinct nonzero Montgomery identities",
                ));
            }
        }
        Ok(())
    }

    pub fn n_parties(&self) -> usize {
        self.party_keys.len()
    }

    pub fn coordinator(&self) -> usize {
        self.party_keys.len()
    }

    pub fn security_profile(&self) -> TransportSecurityProfile {
        self.profile
    }

    fn key(&self, sender: usize) -> Option<[u8; 32]> {
        if sender == self.coordinator() {
            Some(self.coordinator_key)
        } else {
            self.party_keys.get(sender).copied()
        }
    }

    fn native_key(&self, sender: usize) -> Option<&NativePqTransportPublicIdentity> {
        if sender == self.coordinator() {
            self.native_coordinator_key.as_ref()
        } else {
            self.native_party_keys.get(sender)
        }
    }

    fn validate_native_identity(
        &self,
        sender: usize,
        identity: &NativePqTransportIdentity,
    ) -> Result<()> {
        let expected =
            self.native_key(sender)
                .ok_or(EqualityTransportError::InvalidConfiguration(
                    "native-PQ endpoint used outside a native-PQ roster",
                ))?;
        if identity.signing_key.verifying_key().to_bytes() != expected.ed25519
            || identity.ml_dsa.public_bytes() != expected.ml_dsa
            || identity.ml_kem_ek != expected.ml_kem_ek
            || identity.ml_kem_dk.len() != ML_KEM_768_DK_BYTES
        {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ endpoint identity does not match its roster slot",
            ));
        }
        Ok(())
    }
}

/// Crossing-specific spelling for the shared authenticated transport roster.
///
/// The underlying wire envelope is shared with equality and the session digest
/// includes a circuit tag, so a signed frame cannot cross between the two.
pub type CrossingTransportRoster = EqualityTransportRoster;

/// Crossing-specific spelling for the shared fail-closed transport error.
pub type CrossingTransportError = EqualityTransportError;

/// One bounded authenticated wire frame. It intentionally has no `Debug` or
/// `Clone`. Peer-ingress payloads are end-to-end encrypted; a router may inspect
/// only the public sender/recipient/sequence and forward the bytes.
pub struct AuthenticatedEqualityFrame {
    sender: usize,
    recipient: usize,
    sequence: u64,
    wire: Vec<u8>,
}

/// Crossing-specific spelling for the shared authenticated wire envelope.
pub type AuthenticatedCrossingFrame = AuthenticatedEqualityFrame;

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
    session_digest: TransportSessionDigest,
    roster: EqualityTransportRoster,
    party: usize,
    signing_key: SigningKey,
    ml_dsa: Option<MlDsaKey>,
    ml_kem_dk: Option<Vec<u8>>,
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
        validate_equality_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::ClassicalCompatibility {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ roster requires native-PQ endpoint credentials",
            ));
        }
        if party >= roster.n_parties()
            || signing_key.verifying_key().to_bytes() != roster.party_keys[party]
        {
            return Err(EqualityTransportError::InvalidConfiguration(
                "party signing key does not match its roster slot",
            ));
        }
        Self::new_with_crypto(
            session,
            roster,
            party,
            signing_key,
            None,
            None,
            input,
            preprocessing,
        )
    }

    pub fn new_native_post_quantum(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        party: usize,
        identity: NativePqTransportIdentity,
        input: PartyEqualityInput,
        preprocessing: TripleMaterial,
    ) -> Result<Self> {
        validate_equality_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::NativePostQuantum {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ endpoint requires a native-PQ roster",
            ));
        }
        roster.validate_native_identity(party, &identity)?;
        let NativePqTransportIdentity {
            signing_key,
            ml_dsa,
            ml_kem_dk,
            ..
        } = identity;
        Self::new_with_crypto(
            session,
            roster,
            party,
            signing_key,
            Some(ml_dsa),
            Some(ml_kem_dk),
            input,
            preprocessing,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn new_with_crypto(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        party: usize,
        signing_key: SigningKey,
        ml_dsa: Option<MlDsaKey>,
        ml_kem_dk: Option<Vec<u8>>,
        input: PartyEqualityInput,
        preprocessing: TripleMaterial,
    ) -> Result<Self> {
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
            session_digest: transport_session_digest(&session, &roster)?,
            session,
            roster: roster.clone(),
            party,
            signing_key,
            ml_dsa,
            ml_kem_dk,
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
                    self.ml_dsa.as_ref(),
                    &self.roster,
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
        match decode_party_inbound(
            &self.session,
            self.session_digest,
            self.party,
            &self.signing_key,
            self.ml_kem_dk.as_deref(),
            &self.roster,
            decoded,
        )? {
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

/// Party-side authenticated transport for the full demand/supply crossing.
///
/// This is the crossing analogue of [`EqualityPartyMachine`]. It owns only one
/// party's mod-`t` curve shares and Beaver row. Peer ingress remains encrypted
/// end to end; the router sees only public routing and the coordinator receives
/// gate shares plus the final `(p*, V*)` XOR shares.
pub struct CrossingPartyMachine {
    session: PartyMpcSession,
    session_digest: TransportSessionDigest,
    roster: EqualityTransportRoster,
    party: usize,
    signing_key: SigningKey,
    ml_dsa: Option<MlDsaKey>,
    ml_kem_dk: Option<Vec<u8>>,
    outbound: Receiver<RawOutbound>,
    peer_in: Sender<PeerInputMessage>,
    coordinator_in: Sender<CoordinatorMessage>,
    result: Receiver<std::result::Result<PartyReport, PartyMpcError>>,
    outbound_sequences: Vec<u64>,
    inbound_sequences: Vec<u64>,
}

/// Prepare one PartyMPC crossing input directly from this party's mod-`t`
/// share of the canonical packed private-book fold.
///
/// The packed share is intended to be the party-local output of masked
/// threshold decryption over `fold_private_book_ciphertexts`: demand occupies
/// `0..K`, supply `K..2K`, and the injective metadata sum is slot `2K`. No
/// side-specific ciphertext or second plaintext encoding is accepted or
/// constructed here. Under the current semi-honest claim this adapter cannot
/// prove that a malicious caller supplied the share derived from that fold.
#[cfg(feature = "amm-input-binding")]
pub fn prepare_private_book_crossing_input<R: rand::Rng>(
    session: &PartyMpcSession,
    party: usize,
    packed_mod_t_share: &[u64],
    rng: &mut R,
) -> Result<PartyArithmeticInput> {
    use crate::private_book_relation::{FoldedPrivateBookCiphertext, PRIVATE_BOOK_LIVE_SLOTS};

    validate_crossing_transport_session_shape(session)?;
    let demand = FoldedPrivateBookCiphertext::demand_slots();
    let supply = FoldedPrivateBookCiphertext::supply_slots();
    if session.buckets != demand.len()
        || packed_mod_t_share.len() != PRIVATE_BOOK_LIVE_SLOTS
        || packed_mod_t_share
            .iter()
            .any(|value| *value >= session.plaintext_modulus)
    {
        return Err(EqualityTransportError::InvalidConfiguration(
            "packed private-book share has the wrong N4K4/mod-t shape",
        ));
    }
    PartyArithmeticInput::new(
        session,
        party,
        &packed_mod_t_share[demand],
        &packed_mod_t_share[supply],
        rng,
    )
    .map_err(Into::into)
}

fn validate_crossing_transport_session_shape(session: &PartyMpcSession) -> Result<()> {
    if session.circuit != CircuitKind::Crossing {
        return Err(EqualityTransportError::InvalidConfiguration(
            "crossing transport requires a crossing session",
        ));
    }
    Ok(())
}

impl CrossingPartyMachine {
    pub fn new(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        party: usize,
        signing_key: SigningKey,
        input: PartyArithmeticInput,
        preprocessing: TripleMaterial,
    ) -> Result<Self> {
        validate_crossing_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::ClassicalCompatibility {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ roster requires native-PQ endpoint credentials",
            ));
        }
        if party >= roster.n_parties()
            || signing_key.verifying_key().to_bytes() != roster.party_keys[party]
        {
            return Err(EqualityTransportError::InvalidConfiguration(
                "party signing key does not match its roster slot",
            ));
        }
        Self::new_with_crypto(
            session,
            roster,
            party,
            signing_key,
            None,
            None,
            input,
            preprocessing,
        )
    }

    pub fn new_native_post_quantum(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        party: usize,
        identity: NativePqTransportIdentity,
        input: PartyArithmeticInput,
        preprocessing: TripleMaterial,
    ) -> Result<Self> {
        validate_crossing_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::NativePostQuantum {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ endpoint requires a native-PQ roster",
            ));
        }
        roster.validate_native_identity(party, &identity)?;
        let NativePqTransportIdentity {
            signing_key,
            ml_dsa,
            ml_kem_dk,
            ..
        } = identity;
        Self::new_with_crypto(
            session,
            roster,
            party,
            signing_key,
            Some(ml_dsa),
            Some(ml_kem_dk),
            input,
            preprocessing,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn new_with_crypto(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        party: usize,
        signing_key: SigningKey,
        ml_dsa: Option<MlDsaKey>,
        ml_kem_dk: Option<Vec<u8>>,
        input: PartyArithmeticInput,
        preprocessing: TripleMaterial,
    ) -> Result<Self> {
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
            let _ = result_tx.send(run_party(input, preprocessing, channels));
        }));

        Ok(Self {
            session_digest: transport_session_digest(&session, &roster)?,
            session,
            roster: roster.clone(),
            party,
            signing_key,
            ml_dsa,
            ml_kem_dk,
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
                    self.ml_dsa.as_ref(),
                    &self.roster,
                )?))
            }
            Err(TryRecvError::Empty) | Err(TryRecvError::Disconnected) => Ok(None),
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
        match decode_party_inbound(
            &self.session,
            self.session_digest,
            self.party,
            &self.signing_key,
            self.ml_kem_dk.as_deref(),
            &self.roster,
            decoded,
        )? {
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
    session_digest: TransportSessionDigest,
    roster: EqualityTransportRoster,
    signing_key: SigningKey,
    ml_dsa: Option<MlDsaKey>,
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
        validate_equality_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::ClassicalCompatibility {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ roster requires native-PQ endpoint credentials",
            ));
        }
        if signing_key.verifying_key().to_bytes() != roster.coordinator_key {
            return Err(EqualityTransportError::InvalidConfiguration(
                "coordinator signing key does not match the roster",
            ));
        }
        Self::new_with_crypto(session, roster, signing_key, None)
    }

    pub fn new_native_post_quantum(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        identity: NativePqTransportIdentity,
    ) -> Result<Self> {
        validate_equality_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::NativePostQuantum {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ endpoint requires a native-PQ roster",
            ));
        }
        roster.validate_native_identity(roster.coordinator(), &identity)?;
        let NativePqTransportIdentity {
            signing_key,
            ml_dsa,
            ..
        } = identity;
        Self::new_with_crypto(session, roster, signing_key, Some(ml_dsa))
    }

    fn new_with_crypto(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        signing_key: SigningKey,
        ml_dsa: Option<MlDsaKey>,
    ) -> Result<Self> {
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
            session_digest: transport_session_digest(&session, &roster)?,
            session,
            roster: roster.clone(),
            signing_key,
            ml_dsa,
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
                    self.ml_dsa.as_ref(),
                    &self.roster,
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

/// Reveal-only coordinator transport for a full PartyMPC crossing.
///
/// It has no endpoint for plaintext curves or party mod-`t` shares. The result
/// is produced only after the underlying coordinator receives a full roster of
/// authenticated gate and final output shares.
pub struct CrossingCoordinatorMachine {
    session: PartyMpcSession,
    session_digest: TransportSessionDigest,
    roster: EqualityTransportRoster,
    signing_key: SigningKey,
    ml_dsa: Option<MlDsaKey>,
    party_in: Sender<PartyMessage>,
    outbound: Receiver<RawOutbound>,
    result: Receiver<std::result::Result<DistributedRun, PartyMpcError>>,
    outbound_sequences: Vec<u64>,
    inbound_sequences: Vec<u64>,
}

impl CrossingCoordinatorMachine {
    pub fn new(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        signing_key: SigningKey,
    ) -> Result<Self> {
        validate_crossing_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::ClassicalCompatibility {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ roster requires native-PQ endpoint credentials",
            ));
        }
        if signing_key.verifying_key().to_bytes() != roster.coordinator_key {
            return Err(EqualityTransportError::InvalidConfiguration(
                "coordinator signing key does not match the roster",
            ));
        }
        Self::new_with_crypto(session, roster, signing_key, None)
    }

    pub fn new_native_post_quantum(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        identity: NativePqTransportIdentity,
    ) -> Result<Self> {
        validate_crossing_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::NativePostQuantum {
            return Err(EqualityTransportError::InvalidConfiguration(
                "native-PQ endpoint requires a native-PQ roster",
            ));
        }
        roster.validate_native_identity(roster.coordinator(), &identity)?;
        let NativePqTransportIdentity {
            signing_key,
            ml_dsa,
            ..
        } = identity;
        Self::new_with_crypto(session, roster, signing_key, Some(ml_dsa))
    }

    fn new_with_crypto(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        signing_key: SigningKey,
        ml_dsa: Option<MlDsaKey>,
    ) -> Result<Self> {
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
            let _ = result_tx.send(channels.coordinate(&result_session));
        }));
        Ok(Self {
            session_digest: transport_session_digest(&session, &roster)?,
            session,
            roster: roster.clone(),
            signing_key,
            ml_dsa,
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
                    self.ml_dsa.as_ref(),
                    &self.roster,
                )?))
            }
            Ok(_) => Err(EqualityTransportError::MalformedFrame(
                "coordinator emitted a party message",
            )),
            Err(TryRecvError::Empty) | Err(TryRecvError::Disconnected) => Ok(None),
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

    pub fn try_result(&mut self) -> Result<Option<DistributedRun>> {
        match self.result.try_recv() {
            Ok(result) => result.map(Some).map_err(Into::into),
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => Err(EqualityTransportError::WorkerPanicked),
        }
    }
}

fn validate_equality_transport_session(
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

fn validate_crossing_transport_session(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
) -> Result<()> {
    validate_crossing_transport_session_shape(session)?;
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
            if session.circuit != CircuitKind::Equality
                || binding != session.binding()
                || message_party != party
                || equal > 1
            {
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
        RawOutbound::Party(PartyMessage::OutputShare {
            session: binding,
            party: message_party,
            pstar,
            vstar,
        }) => {
            if session.circuit != CircuitKind::Crossing
                || binding != session.binding()
                || message_party != party
                || pstar.len() != index_bits(session.buckets)
                || vstar.len() != session.value_bits
                || pstar.iter().chain(&vstar).any(|bit| *bit > 1)
            {
                return Err(EqualityTransportError::SessionMismatch);
            }
            let mut bytes = Vec::with_capacity(8 + pstar.len() + vstar.len());
            put_u32(&mut bytes, pstar.len())?;
            bytes.extend_from_slice(&pstar);
            put_u32(&mut bytes, vstar.len())?;
            bytes.extend_from_slice(&vstar);
            Ok((
                session.n_parties,
                EncodedPayload {
                    kind: KIND_OUTPUT_SHARE,
                    bytes,
                },
            ))
        }
        _ => Err(EqualityTransportError::MalformedFrame(
            "party message is incompatible with this transport circuit",
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
    session_digest: TransportSessionDigest,
    party: usize,
    signing_key: &SigningKey,
    ml_kem_dk: Option<&[u8]>,
    roster: &EqualityTransportRoster,
    frame: DecodedFrame<'_>,
) -> Result<PartyInbound> {
    match frame.kind {
        KIND_PEER_INGRESS => {
            if frame.sender >= session.n_parties || frame.recipient != party {
                return Err(EqualityTransportError::RecipientMismatch);
            }
            let mut plaintext = decrypt_peer_payload(
                frame.payload,
                session_digest,
                frame.sender,
                frame.recipient,
                frame.sequence,
                signing_key,
                ml_kem_dk,
                roster,
            )?;
            let decoded = (|| {
                let mut input = Reader::new(&plaintext);
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
            })();
            // `bits` above owns the only retained copy. Do not leave the full
            // decoded ingress serialization in a freed allocator page.
            plaintext.fill(0);
            decoded
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
            if session.circuit != CircuitKind::Equality
                || frame.payload.len() != 1
                || frame.payload[0] > 1
            {
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
        KIND_OUTPUT_SHARE => {
            if session.circuit != CircuitKind::Crossing {
                return Err(EqualityTransportError::MalformedFrame(
                    "crossing output share used under another circuit",
                ));
            }
            let (pstar, vstar) = decode_output_share(frame.payload, session)?;
            Ok(PartyMessage::OutputShare {
                session: session.binding(),
                party: frame.sender,
                pstar,
                vstar,
            })
        }
        _ => Err(EqualityTransportError::MalformedFrame(
            "message kind is not coordinator-addressed",
        )),
    }
}

fn decode_output_share(payload: &[u8], session: &PartyMpcSession) -> Result<(Vec<u8>, Vec<u8>)> {
    let mut input = Reader::new(payload);
    let pstar = input.bytes(MAX_PAYLOAD_BYTES)?.to_vec();
    let vstar = input.bytes(MAX_PAYLOAD_BYTES)?.to_vec();
    input.finish()?;
    if pstar.len() != index_bits(session.buckets)
        || vstar.len() != session.value_bits
        || pstar.iter().chain(&vstar).any(|bit| *bit > 1)
    {
        return Err(EqualityTransportError::MalformedFrame(
            "invalid crossing output share",
        ));
    }
    Ok((pstar, vstar))
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
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    sequence: u64,
    mut payload: EncodedPayload,
    signing_key: &SigningKey,
    ml_dsa: Option<&MlDsaKey>,
    roster: &EqualityTransportRoster,
) -> Result<AuthenticatedEqualityFrame> {
    if payload.bytes.len() > MAX_PAYLOAD_BYTES {
        return Err(EqualityTransportError::MalformedFrame(
            "payload exceeds its allocation limit",
        ));
    }
    if payload.kind == KIND_PEER_INGRESS {
        let mut plaintext = std::mem::take(&mut payload.bytes);
        let encrypted = encrypt_peer_payload(
            &plaintext,
            session_digest,
            sender,
            recipient,
            sequence,
            signing_key,
            roster,
        );
        // The wire retains only the encrypted carrier. Wipe the serialized
        // Boolean ingress even if encryption fails closed.
        plaintext.fill(0);
        payload.bytes = encrypted?;
    }
    let sender_u32 = u32::try_from(sender)
        .map_err(|_| EqualityTransportError::MalformedFrame("sender does not fit u32"))?;
    let recipient_u32 = u32::try_from(recipient)
        .map_err(|_| EqualityTransportError::MalformedFrame("recipient does not fit u32"))?;
    let payload_len = u32::try_from(payload.bytes.len())
        .map_err(|_| EqualityTransportError::MalformedFrame("payload length does not fit u32"))?;
    let mut wire = Vec::with_capacity(
        FIXED_CONTENT_BYTES + payload.bytes.len() + roster.profile.trailer_bytes(),
    );
    wire.extend_from_slice(FRAME_MAGIC);
    wire.push(roster.profile.wire_tag());
    wire.extend_from_slice(&session_digest);
    wire.extend_from_slice(&sender_u32.to_be_bytes());
    wire.extend_from_slice(&recipient_u32.to_be_bytes());
    wire.extend_from_slice(&sequence.to_be_bytes());
    wire.push(payload.kind);
    wire.extend_from_slice(&payload_len.to_be_bytes());
    wire.extend_from_slice(&payload.bytes);
    let signing_message = frame_signing_message(&wire);
    let signature = signing_key.sign(&signing_message);
    wire.extend_from_slice(&signature.to_bytes());
    match roster.profile {
        TransportSecurityProfile::ClassicalCompatibility => {
            if ml_dsa.is_some() {
                return Err(EqualityTransportError::InvalidConfiguration(
                    "classical transport received native-PQ signing material",
                ));
            }
        }
        TransportSecurityProfile::NativePostQuantum => {
            let ml_dsa = ml_dsa.ok_or(EqualityTransportError::InvalidConfiguration(
                "native-PQ frame requires ML-DSA signing material",
            ))?;
            let signature = ml_dsa
                .try_sign(FRAME_ML_DSA_CONTEXT, &signing_message)
                .ok_or(EqualityTransportError::EntropyUnavailable)?;
            if signature.len() != ML_DSA_SIG_LEN {
                return Err(EqualityTransportError::AuthenticationFailed);
            }
            wire.extend_from_slice(&signature);
        }
    }
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

/// Encrypt one party-to-party ingress payload against an eavesdropping router.
///
/// The outer Ed25519 signature authenticates the complete encrypted carrier.
/// XChaCha20-Poly1305 additionally confirms that the named recipient derived
/// the same HKDF-SHA256 key before any plaintext is parsed. Every frame has a
/// fresh 192-bit OS nonce and the AEAD associated data binds the exact session,
/// route, sequence, and plaintext length. Reusing a signing identity across
/// sessions therefore does not reuse a peer-ingress key or nonce domain.
fn encrypt_peer_payload(
    plaintext: &[u8],
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    sequence: u64,
    signing_key: &SigningKey,
    roster: &EqualityTransportRoster,
) -> Result<Vec<u8>> {
    let kem_overhead = match roster.profile {
        TransportSecurityProfile::ClassicalCompatibility => 0,
        TransportSecurityProfile::NativePostQuantum => ML_KEM_768_CT_BYTES,
    };
    if plaintext.len()
        > MAX_PAYLOAD_BYTES.saturating_sub(kem_overhead + PEER_NONCE_BYTES + PEER_AEAD_TAG_BYTES)
    {
        return Err(EqualityTransportError::MalformedFrame(
            "peer-ingress plaintext exceeds its allocation limit",
        ));
    }
    if sender >= roster.n_parties() || recipient >= roster.n_parties() {
        return Err(EqualityTransportError::RecipientMismatch);
    }
    if signing_key.verifying_key().to_bytes() != roster.party_keys[sender] {
        return Err(EqualityTransportError::SenderMismatch);
    }
    let mut shared = peer_shared_secret(signing_key, roster.party_keys[recipient])?;
    let mut kem_ciphertext = Vec::new();
    let mut peer_key = match roster.profile {
        TransportSecurityProfile::ClassicalCompatibility => {
            derive_peer_key(shared, session_digest, sender, recipient)?
        }
        TransportSecurityProfile::NativePostQuantum => {
            let recipient_key = roster.native_key(recipient).ok_or(
                EqualityTransportError::InvalidConfiguration(
                    "native-PQ recipient has no enrolled KEM key",
                ),
            )?;
            let (ciphertext, mut ml_kem_shared) = ml_kem768_encaps(&recipient_key.ml_kem_ek)
                .ok_or(EqualityTransportError::ConfidentialityFailed)?;
            if ciphertext.len() != ML_KEM_768_CT_BYTES {
                ml_kem_shared.fill(0);
                return Err(EqualityTransportError::ConfidentialityFailed);
            }
            let transcript = peer_hybrid_transcript(
                session_digest,
                sender,
                recipient,
                sequence,
                roster,
                &ciphertext,
            )?;
            let combined = combine_hybrid_kem(&shared, &ml_kem_shared, &transcript);
            ml_kem_shared.fill(0);
            kem_ciphertext = ciphertext;
            combined
        }
    };
    shared.fill(0);
    let mut nonce = [0u8; PEER_NONCE_BYTES];
    OsRng
        .try_fill_bytes(&mut nonce)
        .map_err(|_| EqualityTransportError::EntropyUnavailable)?;
    let aad = peer_aead_aad(session_digest, sender, recipient, sequence, plaintext.len())?;
    let encryption = (|| {
        let cipher = XChaCha20Poly1305::new_from_slice(&peer_key)
            .map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
        cipher
            .encrypt(
                XNonce::from_slice(&nonce),
                Payload {
                    msg: plaintext,
                    aad: &aad,
                },
            )
            .map_err(|_| EqualityTransportError::ConfidentialityFailed)
    })();
    peer_key.fill(0);
    let ciphertext = encryption?;
    let mut encrypted =
        Vec::with_capacity(kem_ciphertext.len() + PEER_NONCE_BYTES + ciphertext.len());
    encrypted.extend_from_slice(&kem_ciphertext);
    encrypted.extend_from_slice(&nonce);
    encrypted.extend_from_slice(&ciphertext);
    nonce.fill(0);
    Ok(encrypted)
}

fn decrypt_peer_payload(
    encrypted: &[u8],
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    sequence: u64,
    signing_key: &SigningKey,
    ml_kem_dk: Option<&[u8]>,
    roster: &EqualityTransportRoster,
) -> Result<Vec<u8>> {
    let kem_overhead = match roster.profile {
        TransportSecurityProfile::ClassicalCompatibility => 0,
        TransportSecurityProfile::NativePostQuantum => ML_KEM_768_CT_BYTES,
    };
    if encrypted.len() < kem_overhead + PEER_NONCE_BYTES + PEER_AEAD_TAG_BYTES
        || encrypted.len() > MAX_PAYLOAD_BYTES
    {
        return Err(EqualityTransportError::MalformedFrame(
            "encrypted peer-ingress payload has an invalid length",
        ));
    }
    if sender >= roster.n_parties()
        || recipient >= roster.n_parties()
        || signing_key.verifying_key().to_bytes() != roster.party_keys[recipient]
    {
        return Err(EqualityTransportError::RecipientMismatch);
    }
    let nonce_start = kem_overhead;
    let nonce_end = nonce_start + PEER_NONCE_BYTES;
    let nonce: [u8; PEER_NONCE_BYTES] = encrypted[nonce_start..nonce_end]
        .try_into()
        .map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let ciphertext = &encrypted[nonce_end..];
    let plaintext_len = ciphertext
        .len()
        .checked_sub(PEER_AEAD_TAG_BYTES)
        .ok_or(EqualityTransportError::ConfidentialityFailed)?;
    let mut shared = peer_shared_secret(signing_key, roster.party_keys[sender])?;
    let mut peer_key = match roster.profile {
        TransportSecurityProfile::ClassicalCompatibility => {
            if ml_kem_dk.is_some() {
                return Err(EqualityTransportError::InvalidConfiguration(
                    "classical transport received native-PQ decapsulation material",
                ));
            }
            derive_peer_key(shared, session_digest, sender, recipient)?
        }
        TransportSecurityProfile::NativePostQuantum => {
            let ml_kem_dk = ml_kem_dk.ok_or(EqualityTransportError::InvalidConfiguration(
                "native-PQ peer ingress requires ML-KEM decapsulation material",
            ))?;
            let kem_ciphertext = &encrypted[..ML_KEM_768_CT_BYTES];
            let mut ml_kem_shared = ml_kem768_decaps(ml_kem_dk, kem_ciphertext)
                .ok_or(EqualityTransportError::ConfidentialityFailed)?;
            let transcript = peer_hybrid_transcript(
                session_digest,
                sender,
                recipient,
                sequence,
                roster,
                kem_ciphertext,
            )?;
            let combined = combine_hybrid_kem(&shared, &ml_kem_shared, &transcript);
            ml_kem_shared.fill(0);
            combined
        }
    };
    shared.fill(0);
    let aad = peer_aead_aad(session_digest, sender, recipient, sequence, plaintext_len)?;
    let decrypt = (|| {
        let cipher = XChaCha20Poly1305::new_from_slice(&peer_key)
            .map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
        cipher
            .decrypt(
                XNonce::from_slice(&nonce),
                Payload {
                    msg: ciphertext,
                    aad: &aad,
                },
            )
            .map_err(|_| EqualityTransportError::ConfidentialityFailed)
    })();
    peer_key.fill(0);
    decrypt
}

fn peer_hybrid_transcript(
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    sequence: u64,
    roster: &EqualityTransportRoster,
    kem_ciphertext: &[u8],
) -> Result<Vec<u8>> {
    let sender_u32 =
        u32::try_from(sender).map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let recipient_u32 =
        u32::try_from(recipient).map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let sender_key = roster
        .native_key(sender)
        .ok_or(EqualityTransportError::ConfidentialityFailed)?;
    let recipient_key = roster
        .native_key(recipient)
        .ok_or(EqualityTransportError::ConfidentialityFailed)?;
    let mut transcript = Vec::with_capacity(
        PEER_HYBRID_TRANSCRIPT_DOMAIN.len()
            + 64
            + 4
            + 4
            + 8
            + 64
            + sender_key.ml_dsa.len()
            + recipient_key.ml_dsa.len()
            + recipient_key.ml_kem_ek.len()
            + kem_ciphertext.len(),
    );
    transcript.extend_from_slice(&(PEER_HYBRID_TRANSCRIPT_DOMAIN.len() as u64).to_be_bytes());
    transcript.extend_from_slice(PEER_HYBRID_TRANSCRIPT_DOMAIN);
    transcript.extend_from_slice(&session_digest);
    transcript.extend_from_slice(&sender_u32.to_be_bytes());
    transcript.extend_from_slice(&recipient_u32.to_be_bytes());
    transcript.extend_from_slice(&sequence.to_be_bytes());
    transcript.extend_from_slice(&sender_key.ed25519);
    transcript.extend_from_slice(&recipient_key.ed25519);
    transcript.extend_from_slice(&sender_key.ml_dsa);
    transcript.extend_from_slice(&recipient_key.ml_dsa);
    transcript.extend_from_slice(&recipient_key.ml_kem_ek);
    transcript.extend_from_slice(kem_ciphertext);
    Ok(transcript)
}

/// Standard Ed25519-secret / Ed25519-public conversion to a Curve25519 shared
/// point, used only under the transport-specific KDF below. The roster already
/// rejects weak Ed25519 identities; an all-zero converted shared point is also
/// refused explicitly.
fn peer_shared_secret(signing_key: &SigningKey, peer_public: [u8; 32]) -> Result<[u8; 32]> {
    let peer = CompressedEdwardsY(peer_public)
        .decompress()
        .ok_or(EqualityTransportError::ConfidentialityFailed)?
        .to_montgomery();
    let mut expanded = Sha512::digest(signing_key.to_bytes());
    let mut scalar: [u8; 32] = expanded[..32]
        .try_into()
        .map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    expanded.fill(0);
    let shared = peer.mul_clamped(scalar).to_bytes();
    scalar.fill(0);
    if shared.iter().all(|byte| *byte == 0) {
        return Err(EqualityTransportError::ConfidentialityFailed);
    }
    Ok(shared)
}

fn derive_peer_key(
    mut shared: [u8; 32],
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
) -> Result<[u8; 32]> {
    let sender =
        u32::try_from(sender).map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let recipient =
        u32::try_from(recipient).map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let hkdf = Hkdf::<Sha256>::new(Some(PEER_KEY_DOMAIN), &shared);
    let mut info = Vec::with_capacity(PEER_KEY_DOMAIN.len() + 8 + 64 + 4 + 4);
    info.extend_from_slice(&(PEER_KEY_DOMAIN.len() as u64).to_be_bytes());
    info.extend_from_slice(PEER_KEY_DOMAIN);
    info.extend_from_slice(&session_digest);
    info.extend_from_slice(&sender.to_be_bytes());
    info.extend_from_slice(&recipient.to_be_bytes());
    let mut peer_key = [0u8; 32];
    let expanded = hkdf
        .expand(&info, &mut peer_key)
        .map_err(|_| EqualityTransportError::ConfidentialityFailed);
    shared.fill(0);
    expanded?;
    Ok(peer_key)
}

#[allow(clippy::too_many_arguments)]
fn peer_aead_aad(
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    sequence: u64,
    plaintext_len: usize,
) -> Result<Vec<u8>> {
    let sender =
        u32::try_from(sender).map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let recipient =
        u32::try_from(recipient).map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let plaintext_len =
        u64::try_from(plaintext_len).map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let mut aad = Vec::with_capacity(8 + PEER_AAD_DOMAIN.len() + 64 + 4 + 4 + 8 + 8);
    aad.extend_from_slice(&(PEER_AAD_DOMAIN.len() as u64).to_be_bytes());
    aad.extend_from_slice(PEER_AAD_DOMAIN);
    aad.extend_from_slice(&session_digest);
    aad.extend_from_slice(&sender.to_be_bytes());
    aad.extend_from_slice(&recipient.to_be_bytes());
    aad.extend_from_slice(&sequence.to_be_bytes());
    aad.extend_from_slice(&plaintext_len.to_be_bytes());
    Ok(aad)
}

fn verify_frame<'a>(
    bytes: &'a [u8],
    expected_session: TransportSessionDigest,
    expected_recipient: usize,
    roster: &EqualityTransportRoster,
) -> Result<DecodedFrame<'a>> {
    let trailer_bytes = roster.profile.trailer_bytes();
    if bytes.len() < FIXED_CONTENT_BYTES + trailer_bytes || bytes.len() > MAX_FRAME_BYTES {
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
    let signature_start = checksum_start.checked_sub(trailer_bytes - 32).ok_or(
        EqualityTransportError::MalformedFrame("frame signature trailer underflow"),
    )?;
    let content = &bytes[..signature_start];
    let mut input = Reader::new(content);
    if input.array::<8>()? != *FRAME_MAGIC {
        return Err(EqualityTransportError::MalformedFrame(
            "wrong frame version",
        ));
    }
    if input.byte()? != roster.profile.wire_tag() {
        return Err(EqualityTransportError::AuthenticationFailed);
    }
    if input.array::<64>()? != expected_session {
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
    let ed25519_end = signature_start + 64;
    let signature_bytes: [u8; 64] = bytes[signature_start..ed25519_end]
        .try_into()
        .map_err(|_| EqualityTransportError::MalformedFrame("invalid signature length"))?;
    let signing_message = frame_signing_message(content);
    verifying
        .verify_strict(&signing_message, &Signature::from_bytes(&signature_bytes))
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
    match roster.profile {
        TransportSecurityProfile::ClassicalCompatibility => {
            if ed25519_end != checksum_start {
                return Err(EqualityTransportError::MalformedFrame(
                    "classical frame has a non-canonical signature trailer",
                ));
            }
        }
        TransportSecurityProfile::NativePostQuantum => {
            let public_key = roster
                .native_key(sender)
                .ok_or(EqualityTransportError::AuthenticationFailed)?;
            let pq_signature = &bytes[ed25519_end..checksum_start];
            if !ml_dsa_verify(
                &public_key.ml_dsa,
                FRAME_ML_DSA_CONTEXT,
                &signing_message,
                pq_signature,
            ) {
                return Err(EqualityTransportError::AuthenticationFailed);
            }
        }
    }
    Ok(DecodedFrame {
        sender,
        recipient,
        sequence,
        kind,
        payload,
    })
}

fn transport_session_digest(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
) -> Result<TransportSessionDigest> {
    let circuit_tag = match session.circuit {
        CircuitKind::Crossing => 0,
        CircuitKind::Equality => 1,
        CircuitKind::LessThan => {
            return Err(EqualityTransportError::InvalidConfiguration(
                "transport does not support this circuit",
            ));
        }
    };
    if session.n_parties != roster.n_parties() {
        return Err(EqualityTransportError::InvalidConfiguration(
            "session and transport roster sizes differ",
        ));
    }
    let mut hash = Sha512::new();
    hash.update((SESSION_DOMAIN.len() as u64).to_be_bytes());
    hash.update(SESSION_DOMAIN);
    hash.update([roster.profile.wire_tag()]);
    hash.update(session.nonce);
    hash.update((session.n_parties as u64).to_be_bytes());
    hash.update((session.buckets as u64).to_be_bytes());
    hash.update((session.value_bits as u64).to_be_bytes());
    hash.update(session.plaintext_modulus.to_be_bytes());
    hash.update(session.quorum_timeout.as_secs().to_be_bytes());
    hash.update(session.quorum_timeout.subsec_nanos().to_be_bytes());
    hash.update([circuit_tag]);
    hash.update(session.preprocessing_binding_bytes());
    hash.update((roster.party_keys.len() as u64).to_be_bytes());
    for key in &roster.party_keys {
        hash.update(key);
    }
    hash.update(roster.coordinator_key);
    if roster.profile == TransportSecurityProfile::NativePostQuantum {
        for key in &roster.native_party_keys {
            hash.update((key.ml_dsa.len() as u64).to_be_bytes());
            hash.update(&key.ml_dsa);
            hash.update((key.ml_kem_ek.len() as u64).to_be_bytes());
            hash.update(&key.ml_kem_ek);
        }
        let coordinator = roster.native_coordinator_key.as_ref().ok_or(
            EqualityTransportError::InvalidConfiguration(
                "native-PQ roster is missing its coordinator key",
            ),
        )?;
        hash.update((coordinator.ml_dsa.len() as u64).to_be_bytes());
        hash.update(&coordinator.ml_dsa);
        hash.update((coordinator.ml_kem_ek.len() as u64).to_be_bytes());
        hash.update(&coordinator.ml_kem_ek);
    }
    Ok(hash.finalize().into())
}

/// Verify that a reveal-only equality transcript is exactly reconstructed from
/// the authenticated party-to-coordinator gate and decision frames.
///
/// This is the public evidence a process-separated party checks before signing
/// a Dark Bazaar decision claim. It prevents a supervising router from turning
/// the party into a signing oracle for an invented bit or substituted masked
/// transcript. It proves transport provenance and reconstruction only; it does
/// not upgrade the semi-honest arithmetic or trusted preprocessing assumptions.
pub fn verify_public_decision_transcript(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
    frames: &[Vec<u8>],
    transcript: &DecisionTranscript,
) -> Result<()> {
    validate_equality_transport_session(session, roster)?;
    if !transcript.is_reveal_only(session) {
        return Err(EqualityTransportError::MalformedFrame(
            "decision transcript is not reveal-only for this session",
        ));
    }
    let gates = session.exact_and_gates();
    let frames_per_party = gates
        .checked_add(1)
        .ok_or(EqualityTransportError::MalformedFrame(
            "decision transcript frame count overflow",
        ))?;
    let expected_frames = frames_per_party.checked_mul(session.n_parties).ok_or(
        EqualityTransportError::MalformedFrame("decision transcript frame count overflow"),
    )?;
    if frames.len() != expected_frames {
        return Err(EqualityTransportError::MalformedFrame(
            "decision transcript has an incomplete authenticated frame set",
        ));
    }
    let decision_sequence = u64::try_from(gates).map_err(|_| {
        EqualityTransportError::MalformedFrame("decision transcript gate count does not fit u64")
    })?;
    let finished_sequence =
        decision_sequence
            .checked_add(1)
            .ok_or(EqualityTransportError::MalformedFrame(
                "decision transcript sequence exhausted",
            ))?;
    let session_digest = transport_session_digest(session, roster)?;
    let mut next_sequence = vec![0u64; session.n_parties];
    let mut gate_counts = vec![0usize; gates];
    let mut masked = vec![(0u8, 0u8); gates];
    let mut decision_count = 0usize;
    let mut revealed_equal = 0u8;

    for wire in frames {
        let frame = verify_frame(wire, session_digest, roster.coordinator(), roster)?;
        if frame.sender >= session.n_parties {
            return Err(EqualityTransportError::SenderMismatch);
        }
        let expected = next_sequence[frame.sender];
        if frame.sequence != expected {
            return Err(EqualityTransportError::SequenceMismatch {
                sender: frame.sender,
                have: frame.sequence,
                need: expected,
            });
        }
        next_sequence[frame.sender] =
            expected
                .checked_add(1)
                .ok_or(EqualityTransportError::MalformedFrame(
                    "decision transcript sequence exhausted",
                ))?;
        match frame.kind {
            KIND_GATE_SHARE if frame.sequence < decision_sequence => {
                let (gate, d, e) = decode_gate(frame.payload)?;
                if gate != frame.sequence as usize {
                    return Err(EqualityTransportError::MalformedFrame(
                        "authenticated gate share is out of canonical order",
                    ));
                }
                gate_counts[gate] = gate_counts[gate].checked_add(1).ok_or(
                    EqualityTransportError::MalformedFrame("gate share count overflow"),
                )?;
                masked[gate].0 ^= d;
                masked[gate].1 ^= e;
            }
            KIND_DECISION_SHARE if frame.sequence == decision_sequence => {
                if frame.payload.len() != 1 || frame.payload[0] > 1 {
                    return Err(EqualityTransportError::MalformedFrame(
                        "invalid authenticated decision share",
                    ));
                }
                decision_count += 1;
                revealed_equal ^= frame.payload[0];
            }
            _ => {
                return Err(EqualityTransportError::MalformedFrame(
                    "authenticated decision transcript frame has the wrong kind or phase",
                ));
            }
        }
    }

    if next_sequence
        .iter()
        .any(|sequence| *sequence != finished_sequence)
        || gate_counts.iter().any(|count| *count != session.n_parties)
        || decision_count != session.n_parties
        || revealed_equal != transcript.revealed_equal
        || transcript.masked.iter().enumerate().any(|(gate, opening)| {
            opening.gate != gate || opening.d != masked[gate].0 || opening.e != masked[gate].1
        })
    {
        return Err(EqualityTransportError::MalformedFrame(
            "authenticated frames do not reconstruct the decision transcript",
        ));
    }
    Ok(())
}

/// Verify that a crossing result and reveal-only transcript are reconstructed
/// exactly from the complete authenticated public frame set.
///
/// A relying party (or each computation signer) runs this before endorsing the
/// canonical fhEgg claim. The router cannot substitute `(p*, V*)`, omit a
/// party, reorder one route's phase, invent a masked opening, or deliver a
/// coordinator opening which differs from the XOR of the signed gate shares.
/// The evidence therefore includes every party-to-coordinator gate/output
/// frame and every coordinator-to-party gate-opening frame; encrypted peer
/// ingress remains private and is deliberately absent. This establishes
/// transport provenance and exact transcript reconstruction—not malicious
/// input/triple formation.
pub fn verify_public_crossing_transcript(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
    frames: &[Vec<u8>],
    crossing: &Crossing,
    transcript: &DistributedTranscript,
) -> Result<()> {
    validate_crossing_transport_session(session, roster)?;
    if !transcript.is_reveal_only(session) {
        return Err(EqualityTransportError::MalformedFrame(
            "crossing transcript is not reveal-only for this session",
        ));
    }
    let gates = session.exact_and_gates();
    let gate_frames =
        gates
            .checked_mul(session.n_parties)
            .ok_or(EqualityTransportError::MalformedFrame(
                "crossing transcript frame count overflow",
            ))?;
    let expected_frames = gate_frames
        .checked_mul(2)
        .and_then(|both_directions| both_directions.checked_add(session.n_parties))
        .ok_or(EqualityTransportError::MalformedFrame(
            "crossing transcript frame count overflow",
        ))?;
    if frames.len() != expected_frames {
        return Err(EqualityTransportError::MalformedFrame(
            "crossing transcript has an incomplete authenticated frame set",
        ));
    }
    let output_sequence = u64::try_from(gates).map_err(|_| {
        EqualityTransportError::MalformedFrame("crossing gate count does not fit u64")
    })?;
    let finished_sequence =
        output_sequence
            .checked_add(1)
            .ok_or(EqualityTransportError::MalformedFrame(
                "crossing transcript sequence exhausted",
            ))?;
    let session_digest = transport_session_digest(session, roster)?;
    let mut party_next_sequence = vec![0u64; session.n_parties];
    let mut coordinator_next_sequence = vec![0u64; session.n_parties];
    let mut gate_counts = vec![0usize; gates];
    let mut masked = vec![(0u8, 0u8); gates];
    let mut opened_counts = vec![0usize; gates];
    let mut coordinator_opened = vec![None; gates];
    let mut output_count = 0usize;
    let mut pstar = vec![0u8; index_bits(session.buckets)];
    let mut vstar = vec![0u8; session.value_bits];

    for wire in frames {
        let recipient = encoded_frame_recipient(wire)?;
        if recipient > roster.coordinator() {
            return Err(EqualityTransportError::RecipientMismatch);
        }
        let frame = verify_frame(wire, session_digest, recipient, roster)?;
        if frame.sender < session.n_parties && frame.recipient == roster.coordinator() {
            let expected = party_next_sequence[frame.sender];
            if frame.sequence != expected {
                return Err(EqualityTransportError::SequenceMismatch {
                    sender: frame.sender,
                    have: frame.sequence,
                    need: expected,
                });
            }
            party_next_sequence[frame.sender] =
                expected
                    .checked_add(1)
                    .ok_or(EqualityTransportError::MalformedFrame(
                        "crossing party transcript sequence exhausted",
                    ))?;
            match frame.kind {
                KIND_GATE_SHARE if frame.sequence < output_sequence => {
                    let (gate, d, e) = decode_gate(frame.payload)?;
                    if gate != frame.sequence as usize {
                        return Err(EqualityTransportError::MalformedFrame(
                            "authenticated gate share is out of canonical order",
                        ));
                    }
                    gate_counts[gate] = gate_counts[gate].checked_add(1).ok_or(
                        EqualityTransportError::MalformedFrame("gate share count overflow"),
                    )?;
                    masked[gate].0 ^= d;
                    masked[gate].1 ^= e;
                }
                KIND_OUTPUT_SHARE if frame.sequence == output_sequence => {
                    let (p_share, v_share) = decode_output_share(frame.payload, session)?;
                    for (out, share) in pstar.iter_mut().zip(p_share) {
                        *out ^= share;
                    }
                    for (out, share) in vstar.iter_mut().zip(v_share) {
                        *out ^= share;
                    }
                    output_count = output_count.checked_add(1).ok_or(
                        EqualityTransportError::MalformedFrame("output share count overflow"),
                    )?;
                }
                _ => {
                    return Err(EqualityTransportError::MalformedFrame(
                        "authenticated crossing party frame has the wrong kind or phase",
                    ));
                }
            }
        } else if frame.sender == roster.coordinator() && frame.recipient < session.n_parties {
            let expected = coordinator_next_sequence[frame.recipient];
            if frame.sequence != expected {
                return Err(EqualityTransportError::SequenceMismatch {
                    sender: frame.sender,
                    have: frame.sequence,
                    need: expected,
                });
            }
            coordinator_next_sequence[frame.recipient] =
                expected
                    .checked_add(1)
                    .ok_or(EqualityTransportError::MalformedFrame(
                        "crossing coordinator transcript sequence exhausted",
                    ))?;
            if frame.kind != KIND_GATE_OPENED || frame.sequence >= output_sequence {
                return Err(EqualityTransportError::MalformedFrame(
                    "authenticated crossing coordinator frame has the wrong kind or phase",
                ));
            }
            let (gate, d, e) = decode_gate(frame.payload)?;
            if gate != frame.sequence as usize {
                return Err(EqualityTransportError::MalformedFrame(
                    "authenticated gate opening is out of canonical order",
                ));
            }
            if coordinator_opened[gate].is_some_and(|opening| opening != (d, e)) {
                return Err(EqualityTransportError::MalformedFrame(
                    "coordinator broadcast inconsistent gate openings",
                ));
            }
            coordinator_opened[gate] = Some((d, e));
            opened_counts[gate] = opened_counts[gate].checked_add(1).ok_or(
                EqualityTransportError::MalformedFrame("gate opening count overflow"),
            )?;
        } else {
            return Err(EqualityTransportError::MalformedFrame(
                "authenticated crossing evidence contains a private or misrouted frame",
            ));
        }
    }

    let index = super::decode_bits(&pstar).map_err(EqualityTransportError::Mpc)? as usize;
    let volume = super::decode_bits(&vstar).map_err(EqualityTransportError::Mpc)?;
    if index >= session.buckets || (volume == 0 && index != 0) {
        return Err(EqualityTransportError::MalformedFrame(
            "authenticated output shares reconstruct an invalid crossing",
        ));
    }
    let reconstructed = Crossing {
        p_star: (volume != 0).then_some(index),
        v_star: volume,
    };
    if party_next_sequence
        .iter()
        .any(|sequence| *sequence != finished_sequence)
        || coordinator_next_sequence
            .iter()
            .any(|sequence| *sequence != output_sequence)
        || gate_counts.iter().any(|count| *count != session.n_parties)
        || opened_counts
            .iter()
            .any(|count| *count != session.n_parties)
        || coordinator_opened
            .iter()
            .enumerate()
            .any(|(gate, opening)| *opening != Some(masked[gate]))
        || output_count != session.n_parties
        || &reconstructed != crossing
        || transcript.revealed_pstar != pstar
        || transcript.revealed_vstar != vstar
        || transcript.masked.iter().enumerate().any(|(gate, opening)| {
            opening.gate != gate || opening.d != masked[gate].0 || opening.e != masked[gate].1
        })
    {
        return Err(EqualityTransportError::MalformedFrame(
            "authenticated frames do not reconstruct the crossing transcript",
        ));
    }
    Ok(())
}

fn encoded_frame_recipient(bytes: &[u8]) -> Result<usize> {
    const RECIPIENT_OFFSET: usize = 8 + 1 + 64 + 4;
    let end = RECIPIENT_OFFSET + 4;
    let field = bytes
        .get(RECIPIENT_OFFSET..end)
        .ok_or(EqualityTransportError::MalformedFrame(
            "frame is too short to name a recipient",
        ))?;
    Ok(u32::from_be_bytes(
        field
            .try_into()
            .map_err(|_| EqualityTransportError::MalformedFrame("invalid recipient field"))?,
    ) as usize)
}

/// Domain- and invocation-separate a trusted preprocessing seed.
///
/// A static deployment seed must never map to the same Beaver row twice. The
/// caller supplies an independently authenticated public context (normally the
/// strict worker-config digest or Dark AMM task digest); this function also
/// mixes fresh CSPRNG entropy so a retry of the exact same task receives an
/// independent triple stream. This prevents accidental one-time-pad reuse. A
/// certified session additionally binds the preprocessing authority and audited
/// batch digest; it does not replace that trusted authority with dealer-free
/// preprocessing.
pub fn fresh_preprocessing_seed<R: RngCore + CryptoRng>(
    session: &PartyMpcSession,
    public_context: [u8; 32],
    base_seed: &[u8; 32],
    rng: &mut R,
) -> Result<[u8; 32]> {
    fresh_preprocessing_seed_for(
        session,
        CircuitKind::Equality,
        PREPROCESSING_SEED_DOMAIN,
        1,
        public_context,
        base_seed,
        rng,
    )
}

/// Domain- and invocation-separate trusted preprocessing for one crossing.
///
/// This is the crossing counterpart of [`fresh_preprocessing_seed`]. The
/// caller normally uses the returned seed to instantiate the trusted-dealer
/// RNG for [`super::trusted_dealer_triples`]. It prevents accidental Beaver-row
/// reuse but does not turn trusted preprocessing into malicious-secure setup.
pub fn fresh_crossing_preprocessing_seed<R: RngCore + CryptoRng>(
    session: &PartyMpcSession,
    public_context: [u8; 32],
    base_seed: &[u8; 32],
    rng: &mut R,
) -> Result<[u8; 32]> {
    fresh_preprocessing_seed_for(
        session,
        CircuitKind::Crossing,
        CROSSING_PREPROCESSING_SEED_DOMAIN,
        0,
        public_context,
        base_seed,
        rng,
    )
}

fn fresh_preprocessing_seed_for<R: RngCore + CryptoRng>(
    session: &PartyMpcSession,
    circuit: CircuitKind,
    domain: &[u8],
    circuit_tag: u8,
    public_context: [u8; 32],
    base_seed: &[u8; 32],
    rng: &mut R,
) -> Result<[u8; 32]> {
    if session.circuit != circuit || public_context == [0; 32] || *base_seed == [0; 32] {
        return Err(EqualityTransportError::InvalidConfiguration(
            "fresh preprocessing requires the matching circuit, nonzero public context, and nonzero trusted root",
        ));
    }
    let mut invocation = [0u8; 32];
    rng.try_fill_bytes(&mut invocation)
        .map_err(|_| EqualityTransportError::EntropyUnavailable)?;
    let mut hash = Sha256::new();
    hash.update((domain.len() as u64).to_be_bytes());
    hash.update(domain);
    hash.update(session.nonce);
    hash.update((session.n_parties as u64).to_be_bytes());
    hash.update((session.buckets as u64).to_be_bytes());
    hash.update((session.value_bits as u64).to_be_bytes());
    hash.update(session.plaintext_modulus.to_be_bytes());
    hash.update(session.quorum_timeout.as_secs().to_be_bytes());
    hash.update(session.quorum_timeout.subsec_nanos().to_be_bytes());
    hash.update([circuit_tag]);
    hash.update(session.preprocessing_binding_bytes());
    hash.update(public_context);
    hash.update(base_seed);
    hash.update(invocation);
    invocation.fill(0);
    Ok(hash.finalize().into())
}

fn frame_signing_message(content: &[u8]) -> [u8; 64] {
    let mut hash = Sha512::new();
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

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use ed25519_dalek::SigningKey;
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    use super::{
        decrypt_peer_payload, encrypt_peer_payload, fresh_preprocessing_seed, peer_shared_secret,
        sign_frame, verify_public_decision_transcript, CompressedEdwardsY, EncodedPayload,
        EqualityTransportError, EqualityTransportRoster, KIND_DECISION_SHARE, KIND_GATE_SHARE,
        KIND_PEER_INGRESS, PEER_NONCE_BYTES,
    };
    use crate::mpc_party::{DecisionTranscript, MaskedOpening, PartyMpcSession};

    fn fixture() -> (PartyMpcSession, EqualityTransportRoster, [SigningKey; 3]) {
        let keys = [
            SigningKey::from_bytes(&[0x21; 32]),
            SigningKey::from_bytes(&[0x22; 32]),
            SigningKey::from_bytes(&[0x23; 32]),
        ];
        let coordinator = SigningKey::from_bytes(&[0x31; 32]);
        let roster = EqualityTransportRoster::new(
            keys.iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            coordinator.verifying_key().to_bytes(),
        )
        .unwrap();
        let session =
            PartyMpcSession::equality([0x41; 32], 3, 8, 65_537, Duration::from_secs(5)).unwrap();
        (session, roster, keys)
    }

    #[test]
    fn peer_ingress_is_randomized_and_opens_only_at_the_named_party() {
        let (session, roster, keys) = fixture();
        let session_digest = super::transport_session_digest(&session, &roster).unwrap();
        let plaintext = EncodedPayload {
            kind: KIND_PEER_INGRESS,
            bytes: vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 1, 0, 1, 0, 1, 0, 1, 0],
        };
        let first =
            encrypt_peer_payload(&plaintext.bytes, session_digest, 0, 1, 0, &keys[0], &roster)
                .unwrap();
        let second =
            encrypt_peer_payload(&plaintext.bytes, session_digest, 0, 1, 0, &keys[0], &roster)
                .unwrap();
        assert_ne!(first, second, "fresh frame nonces must randomize the wire");
        assert_ne!(&first[PEER_NONCE_BYTES..], plaintext.bytes);
        assert_eq!(
            decrypt_peer_payload(&first, session_digest, 0, 1, 0, &keys[1], None, &roster).unwrap(),
            plaintext.bytes
        );
        assert_eq!(
            decrypt_peer_payload(&first, session_digest, 0, 1, 0, &keys[2], None, &roster),
            Err(EqualityTransportError::RecipientMismatch)
        );

        for index in [0, PEER_NONCE_BYTES, first.len() - 1] {
            let mut corrupted = first.clone();
            corrupted[index] ^= 1;
            assert_eq!(
                decrypt_peer_payload(&corrupted, session_digest, 0, 1, 0, &keys[1], None, &roster,),
                Err(EqualityTransportError::ConfidentialityFailed),
                "nonce, ciphertext, and Poly1305-tag corruption must all fail closed"
            );
        }
        assert_eq!(
            decrypt_peer_payload(&first, session_digest, 0, 1, 1, &keys[1], None, &roster),
            Err(EqualityTransportError::ConfidentialityFailed),
            "the AEAD associated data binds sequence"
        );
    }

    #[test]
    fn converted_party_identities_derive_the_same_directional_key_material() {
        let (_, roster, keys) = fixture();
        let alice = peer_shared_secret(&keys[0], roster.party_keys[1]).unwrap();
        let bob = peer_shared_secret(&keys[1], roster.party_keys[0]).unwrap();
        assert_eq!(alice, bob);
    }

    #[test]
    fn edwards_sign_aliases_cannot_collapse_two_party_dh_identities() {
        let key = SigningKey::from_bytes(&[0x71; 32]);
        let encoded = key.verifying_key().to_bytes();
        let mut negated = encoded;
        negated[31] ^= 0x80;
        let negated_key = ed25519_dalek::VerifyingKey::from_bytes(&negated).unwrap();
        assert!(!negated_key.is_weak());
        assert_ne!(encoded, negated);
        assert_eq!(
            CompressedEdwardsY(encoded)
                .decompress()
                .unwrap()
                .to_montgomery(),
            CompressedEdwardsY(negated)
                .decompress()
                .unwrap()
                .to_montgomery()
        );
        let coordinator = SigningKey::from_bytes(&[0x72; 32]);
        assert!(matches!(
            EqualityTransportRoster::new(
                vec![encoded, negated],
                coordinator.verifying_key().to_bytes()
            ),
            Err(EqualityTransportError::InvalidConfiguration(
                "party keys must have distinct nonzero Montgomery identities"
            ))
        ));
    }

    #[test]
    fn preprocessing_seed_is_context_and_invocation_separated() {
        let (session, _, _) = fixture();
        let base = [0x51; 32];
        let context = [0x61; 32];
        let mut rng_a = StdRng::seed_from_u64(1);
        let mut rng_a_again = StdRng::seed_from_u64(1);
        let mut rng_b = StdRng::seed_from_u64(2);
        let first = fresh_preprocessing_seed(&session, context, &base, &mut rng_a).unwrap();
        assert_eq!(
            first,
            fresh_preprocessing_seed(&session, context, &base, &mut rng_a_again).unwrap(),
            "the KDF is canonical for the same explicit inputs"
        );
        assert_ne!(
            first,
            fresh_preprocessing_seed(&session, context, &base, &mut rng_b).unwrap(),
            "a retry must receive an independent triple stream"
        );
        let mut rng_context = StdRng::seed_from_u64(1);
        assert_ne!(
            first,
            fresh_preprocessing_seed(&session, [0x62; 32], &base, &mut rng_context).unwrap(),
            "a substituted public task must not share Beaver material"
        );
        let mut rng_zero = StdRng::seed_from_u64(1);
        assert!(fresh_preprocessing_seed(&session, [0; 32], &base, &mut rng_zero).is_err());
        let mut rng_zero_root = StdRng::seed_from_u64(1);
        assert!(
            fresh_preprocessing_seed(&session, context, &[0; 32], &mut rng_zero_root).is_err(),
            "fresh entropy must not silently bless a missing trusted preprocessing root"
        );

        let mut changed_session = session.clone();
        changed_session.nonce[0] ^= 1;
        let mut rng_session = StdRng::seed_from_u64(1);
        assert_ne!(
            first,
            fresh_preprocessing_seed(&changed_session, context, &base, &mut rng_session).unwrap(),
            "the complete equality session separates preprocessing streams"
        );
    }

    #[test]
    fn public_transcript_requires_the_exact_authenticated_frame_set() {
        let (session, roster, keys) = fixture();
        let session_digest = super::transport_session_digest(&session, &roster).unwrap();
        let gates = session.exact_and_gates();
        let mut reconstructed = vec![(0u8, 0u8); gates];
        let mut frames = Vec::with_capacity((gates + 1) * session.n_parties());
        let mut revealed_equal = 0u8;
        for party in 0..session.n_parties() {
            for gate in 0..gates {
                let d = ((party + gate) & 1) as u8;
                let e = ((party * 3 + gate) & 1) as u8;
                reconstructed[gate].0 ^= d;
                reconstructed[gate].1 ^= e;
                let mut bytes = Vec::with_capacity(10);
                bytes.extend_from_slice(&(gate as u64).to_be_bytes());
                bytes.extend_from_slice(&[d, e]);
                frames.push(
                    sign_frame(
                        session_digest,
                        party,
                        roster.coordinator(),
                        gate as u64,
                        EncodedPayload {
                            kind: KIND_GATE_SHARE,
                            bytes,
                        },
                        &keys[party],
                        None,
                        &roster,
                    )
                    .unwrap()
                    .into_bytes(),
                );
            }
            let share = u8::from(party == 0);
            revealed_equal ^= share;
            frames.push(
                sign_frame(
                    session_digest,
                    party,
                    roster.coordinator(),
                    gates as u64,
                    EncodedPayload {
                        kind: KIND_DECISION_SHARE,
                        bytes: vec![share],
                    },
                    &keys[party],
                    None,
                    &roster,
                )
                .unwrap()
                .into_bytes(),
            );
        }
        let transcript = DecisionTranscript {
            masked: reconstructed
                .iter()
                .enumerate()
                .map(|(gate, (d, e))| MaskedOpening { gate, d: *d, e: *e })
                .collect(),
            revealed_equal,
            and_gates: gates,
            scalar_opening_rounds: gates,
            modeled_batched_rounds: super::super::modeled_batched_rounds(&session),
            gate_share_messages: gates * session.n_parties(),
            output_share_messages: session.n_parties(),
        };
        verify_public_decision_transcript(&session, &roster, &frames, &transcript).unwrap();

        let mut substituted = transcript.clone();
        substituted.masked[0].d ^= 1;
        assert!(
            verify_public_decision_transcript(&session, &roster, &frames, &substituted).is_err()
        );
        let mut false_bit = transcript.clone();
        false_bit.revealed_equal ^= 1;
        assert!(verify_public_decision_transcript(&session, &roster, &frames, &false_bit).is_err());
        let mut incomplete = frames.clone();
        incomplete.pop();
        assert!(
            verify_public_decision_transcript(&session, &roster, &incomplete, &transcript).is_err()
        );
        let mut reordered = frames.clone();
        reordered.swap(0, 1);
        assert!(matches!(
            verify_public_decision_transcript(&session, &roster, &reordered, &transcript),
            Err(EqualityTransportError::SequenceMismatch { .. })
        ));
    }
}

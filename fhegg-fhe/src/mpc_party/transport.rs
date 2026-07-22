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

use std::collections::{HashSet, VecDeque};
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
use hmac::{Hmac, Mac};
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
const SEALED_FRAME_MAGIC: &[u8; 8] = b"FHEQv005";
const LINK_CONTROL_MAGIC: &[u8; 8] = b"FHEHv005";
const FRAME_SIGNATURE_DOMAIN: &[u8] = b"fhegg/party-mpc-frame-signature/v4";
const FRAME_ML_DSA_CONTEXT: &[u8] = b"fhegg/party-mpc/frame/v4";
const FRAME_CHECKSUM_DOMAIN: &[u8] = b"fhegg/party-mpc-frame-checksum/v4";
const SESSION_DOMAIN: &[u8] = b"fhegg/party-mpc-transport-session/v4";
const PREPROCESSING_ROSTER_DOMAIN: &[u8] = b"fhegg/party-mpc-preprocessing-roster/v1";
const V5_LINK_HELLO_SIGNATURE_DOMAIN: &[u8] = b"fhegg/party-mpc/link-hello-signature/v5";
const V5_LINK_HELLO_ML_DSA_CONTEXT: &[u8] = b"fhegg/party-mpc/link-hello/v5";
const V5_LINK_KEM_TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/party-mpc/link-kem-transcript/v5";
const V5_LINK_KEY_DOMAIN: &[u8] = b"fhegg/party-mpc/link-keys/v5";
const V5_LINK_CONFIRM_DOMAIN: &[u8] = b"fhegg/party-mpc/link-confirm/v5";
const V5_FRAME_MAC_DOMAIN: &[u8] = b"fhegg/party-mpc/frame-mac/v5";
const V5_ROUTE_ROOT_DOMAIN: &[u8] = b"fhegg/party-mpc/route-root/v5";
const V5_ENDPOINT_SEAL_DOMAIN: &[u8] = b"fhegg/party-mpc/endpoint-seal/v5";
const V5_ENDPOINT_SEAL_ML_DSA_CONTEXT: &[u8] = b"fhegg/party-mpc/endpoint-seal/v5";
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
const SEALED_TRAILER_BYTES: usize = 64 + 32;
const ML_KEM_768_EK_BYTES: usize = 1_184;
const ML_KEM_768_DK_BYTES: usize = 2_400;
const ML_KEM_768_CT_BYTES: usize = 1_088;

type TransportSessionDigest = [u8; 64];

const KIND_PEER_INGRESS: u8 = 1;
const KIND_GATE_SHARE: u8 = 2;
const KIND_GATE_OPENED: u8 = 3;
const KIND_DECISION_SHARE: u8 = 4;
const KIND_OUTPUT_SHARE: u8 = 5;
const KIND_LINK_HELLO: u8 = 0x81;
const KIND_LINK_CONFIRM: u8 = 0x82;

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
    /// Crossing-only v5: one roster/session/preprocessing-bound hybrid
    /// ML-KEM link setup, direction-separated per-frame HMAC-SHA512, and a
    /// dual Ed25519/ML-DSA terminal seal from every endpoint.  This profile is
    /// deliberately not accepted by the equality machines or v4 constructors.
    NativePostQuantumSealedCrossing,
}

impl TransportSecurityProfile {
    fn wire_tag(self) -> u8 {
        match self {
            Self::ClassicalCompatibility => 0,
            Self::NativePostQuantum => 1,
            Self::NativePostQuantumSealedCrossing => 2,
        }
    }

    fn trailer_bytes(self) -> usize {
        match self {
            Self::ClassicalCompatibility => CLASSICAL_TRAILER_BYTES,
            Self::NativePostQuantum => NATIVE_PQ_TRAILER_BYTES,
            Self::NativePostQuantumSealedCrossing => SEALED_TRAILER_BYTES,
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

    /// Borrow the ML-DSA half of this enrolled identity for another protocol
    /// that deliberately uses the same committee slot (for example the
    /// native-PQ full-claim clearing quorum).  The secret bytes remain opaque.
    pub fn ml_dsa_signing_key(&self) -> &MlDsaKey {
        &self.ml_dsa
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
        Self::new_native_with_profile(
            party_keys,
            coordinator_key,
            TransportSecurityProfile::NativePostQuantum,
        )
    }

    /// Construct the v5 native-PQ sealed crossing roster. This cannot be used
    /// by equality machines and cannot consume or emit v4 native-PQ frames.
    pub fn new_native_post_quantum_sealed_crossing(
        party_keys: Vec<NativePqTransportPublicIdentity>,
        coordinator_key: NativePqTransportPublicIdentity,
    ) -> Result<Self> {
        Self::new_native_with_profile(
            party_keys,
            coordinator_key,
            TransportSecurityProfile::NativePostQuantumSealedCrossing,
        )
    }

    fn new_native_with_profile(
        party_keys: Vec<NativePqTransportPublicIdentity>,
        coordinator_key: NativePqTransportPublicIdentity,
        profile: TransportSecurityProfile,
    ) -> Result<Self> {
        let ed25519_party_keys: Vec<_> = party_keys.iter().map(|key| key.ed25519).collect();
        Self::validate_ed25519_roster(&ed25519_party_keys, coordinator_key.ed25519)?;
        if profile == TransportSecurityProfile::NativePostQuantumSealedCrossing {
            let mut seen_montgomery = HashSet::with_capacity(ed25519_party_keys.len() + 1);
            for key in ed25519_party_keys
                .iter()
                .chain(std::iter::once(&coordinator_key.ed25519))
            {
                let montgomery = CompressedEdwardsY(*key)
                    .decompress()
                    .ok_or(EqualityTransportError::InvalidConfiguration(
                        "sealed endpoint key cannot be converted for hybrid link setup",
                    ))?
                    .to_montgomery()
                    .to_bytes();
                if montgomery.iter().all(|byte| *byte == 0) || !seen_montgomery.insert(montgomery) {
                    return Err(EqualityTransportError::InvalidConfiguration(
                        "sealed endpoint keys must have distinct nonzero Montgomery identities",
                    ));
                }
            }
        }
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
            profile,
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

    /// Canonical ordered identity of the exact preprocessing/runtime roster.
    /// FHTRI004 binds this digest before candidate generation, then the final
    /// transport session independently binds the completed batch.
    pub fn preprocessing_roster_digest(&self) -> [u8; 64] {
        let mut hash = Sha512::new();
        hash.update((PREPROCESSING_ROSTER_DOMAIN.len() as u64).to_be_bytes());
        hash.update(PREPROCESSING_ROSTER_DOMAIN);
        hash.update([self.profile.wire_tag()]);
        hash.update((self.party_keys.len() as u64).to_be_bytes());
        for key in &self.party_keys {
            hash.update(key);
        }
        hash.update(self.coordinator_key);
        if self.profile != TransportSecurityProfile::ClassicalCompatibility {
            for key in &self.native_party_keys {
                hash.update((key.ml_dsa.len() as u64).to_be_bytes());
                hash.update(&key.ml_dsa);
                hash.update((key.ml_kem_ek.len() as u64).to_be_bytes());
                hash.update(&key.ml_kem_ek);
            }
            if let Some(coordinator) = &self.native_coordinator_key {
                hash.update((coordinator.ml_dsa.len() as u64).to_be_bytes());
                hash.update(&coordinator.ml_dsa);
                hash.update((coordinator.ml_kem_ek.len() as u64).to_be_bytes());
                hash.update(&coordinator.ml_kem_ek);
            }
        }
        hash.finalize().into()
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

#[derive(Clone, Copy)]
struct RouteAccumulator {
    count: u64,
    root: [u8; 64],
}

impl Default for RouteAccumulator {
    fn default() -> Self {
        Self {
            count: 0,
            root: [0; 64],
        }
    }
}

struct LinkKeys {
    send_mac: [u8; 64],
    receive_mac: [u8; 64],
    send_aead: [u8; 32],
    receive_aead: [u8; 32],
    send_nonce: [u8; 64],
    receive_nonce: [u8; 64],
    confirm: [u8; 64],
    ready: bool,
}

impl Drop for LinkKeys {
    fn drop(&mut self) {
        self.send_mac.fill(0);
        self.receive_mac.fill(0);
        self.send_aead.fill(0);
        self.receive_aead.fill(0);
        self.send_nonce.fill(0);
        self.receive_nonce.fill(0);
        self.confirm.fill(0);
    }
}

struct SealedCrossingEndpoint {
    endpoint: usize,
    links: Vec<Option<LinkKeys>>,
    pending_control: VecDeque<AuthenticatedEqualityFrame>,
    sent: Vec<RouteAccumulator>,
    accepted: Vec<RouteAccumulator>,
    terminal_taken: bool,
}

/// One endpoint's final dual-authenticated statement over every semantic route
/// it sent and accepted.  Fields are intentionally private: callers can carry
/// seals to the public verifier but cannot synthesize or edit one.
pub struct NativePqCrossingEndpointSeal {
    endpoint: usize,
    session_digest: TransportSessionDigest,
    sent: Vec<RouteAccumulator>,
    accepted: Vec<RouteAccumulator>,
    ed25519_signature: [u8; 64],
    ml_dsa_signature: Vec<u8>,
}

impl NativePqCrossingEndpointSeal {
    pub fn endpoint(&self) -> usize {
        self.endpoint
    }
}

impl SealedCrossingEndpoint {
    fn new(
        endpoint: usize,
        session_digest: TransportSessionDigest,
        roster: &EqualityTransportRoster,
        identity: &NativePqTransportIdentity,
    ) -> Result<Self> {
        if roster.profile != TransportSecurityProfile::NativePostQuantumSealedCrossing {
            return Err(EqualityTransportError::InvalidConfiguration(
                "sealed link state requires the v5 crossing profile",
            ));
        }
        roster.validate_native_identity(endpoint, identity)?;
        let endpoints = roster.n_parties() + 1;
        let mut state = Self {
            endpoint,
            links: (0..endpoints).map(|_| None).collect(),
            pending_control: VecDeque::new(),
            sent: vec![RouteAccumulator::default(); endpoints],
            accepted: vec![RouteAccumulator::default(); endpoints],
            terminal_taken: false,
        };
        for recipient in (endpoint + 1)..endpoints {
            let (frame, keys) =
                make_link_hello(session_digest, endpoint, recipient, roster, identity)?;
            state.links[recipient] = Some(keys);
            state.pending_control.push_back(frame);
        }
        Ok(state)
    }

    fn all_links_ready(&self) -> bool {
        self.links.iter().enumerate().all(|(peer, link)| {
            peer == self.endpoint || link.as_ref().is_some_and(|link| link.ready)
        })
    }

    fn try_next_control(&mut self) -> Option<AuthenticatedEqualityFrame> {
        self.pending_control.pop_front()
    }

    fn seal_semantic_frame(
        &mut self,
        session_digest: TransportSessionDigest,
        sender: usize,
        recipient: usize,
        sequence: u64,
        mut payload: EncodedPayload,
    ) -> Result<AuthenticatedEqualityFrame> {
        if sender != self.endpoint || recipient == sender {
            return Err(EqualityTransportError::SenderMismatch);
        }
        let link = self.links.get(recipient).and_then(Option::as_ref).ok_or(
            EqualityTransportError::InvalidConfiguration("sealed route has no established link"),
        )?;
        if !link.ready {
            return Err(EqualityTransportError::InvalidConfiguration(
                "sealed route used before responder key confirmation",
            ));
        }
        if payload.kind == KIND_PEER_INGRESS {
            let mut plaintext = std::mem::take(&mut payload.bytes);
            let encrypted = encrypt_v5_peer_payload(
                &plaintext,
                session_digest,
                sender,
                recipient,
                sequence,
                &link.send_aead,
                &link.send_nonce,
            );
            plaintext.fill(0);
            payload.bytes = encrypted?;
        }
        if payload.bytes.len() > MAX_PAYLOAD_BYTES {
            return Err(EqualityTransportError::MalformedFrame(
                "sealed payload exceeds its allocation limit",
            ));
        }
        let mut wire =
            Vec::with_capacity(FIXED_CONTENT_BYTES + payload.bytes.len() + SEALED_TRAILER_BYTES);
        wire.extend_from_slice(SEALED_FRAME_MAGIC);
        wire.push(TransportSecurityProfile::NativePostQuantumSealedCrossing.wire_tag());
        wire.extend_from_slice(&session_digest);
        wire.extend_from_slice(&(sender as u32).to_be_bytes());
        wire.extend_from_slice(&(recipient as u32).to_be_bytes());
        wire.extend_from_slice(&sequence.to_be_bytes());
        wire.push(payload.kind);
        wire.extend_from_slice(&(payload.bytes.len() as u32).to_be_bytes());
        wire.extend_from_slice(&payload.bytes);
        let tag = v5_frame_mac(&link.send_mac, &wire)?;
        wire.extend_from_slice(&tag);
        wire.extend_from_slice(&frame_checksum(&wire));
        if wire.len() > MAX_FRAME_BYTES {
            return Err(EqualityTransportError::MalformedFrame(
                "sealed frame exceeds its allocation limit",
            ));
        }
        update_route_root(
            session_digest,
            sender,
            recipient,
            &mut self.sent[recipient],
            &wire,
        )?;
        Ok(AuthenticatedEqualityFrame {
            sender,
            recipient,
            sequence,
            wire,
        })
    }

    fn verify_semantic_frame<'a>(
        &self,
        bytes: &'a [u8],
        session_digest: TransportSessionDigest,
        expected_recipient: usize,
    ) -> Result<DecodedFrame<'a>> {
        if expected_recipient != self.endpoint
            || bytes.len() < FIXED_CONTENT_BYTES + SEALED_TRAILER_BYTES
        {
            return Err(EqualityTransportError::RecipientMismatch);
        }
        let checksum_start = bytes.len() - 32;
        if bytes[checksum_start..] != frame_checksum(&bytes[..checksum_start]) {
            return Err(EqualityTransportError::MalformedFrame(
                "sealed frame checksum mismatch",
            ));
        }
        let mac_start = checksum_start - 64;
        let content = &bytes[..mac_start];
        let mut input = Reader::new(content);
        if input.array::<8>()? != *SEALED_FRAME_MAGIC
            || input.byte()? != TransportSecurityProfile::NativePostQuantumSealedCrossing.wire_tag()
        {
            return Err(EqualityTransportError::AuthenticationFailed);
        }
        if input.array::<64>()? != session_digest {
            return Err(EqualityTransportError::SessionMismatch);
        }
        let sender = input.u32()? as usize;
        let recipient = input.u32()? as usize;
        let sequence = input.u64()?;
        let kind = input.byte()?;
        let payload = input.bytes(MAX_PAYLOAD_BYTES)?;
        input.finish()?;
        if recipient != expected_recipient || sender == recipient {
            return Err(EqualityTransportError::RecipientMismatch);
        }
        let link = self
            .links
            .get(sender)
            .and_then(Option::as_ref)
            .ok_or(EqualityTransportError::SenderMismatch)?;
        if !link.ready {
            return Err(EqualityTransportError::AuthenticationFailed);
        }
        let mut mac = <Hmac<Sha512> as Mac>::new_from_slice(&link.receive_mac)
            .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
        mac.update(&v5_frame_mac_message(content));
        let carried = &bytes[mac_start..checksum_start];
        mac.verify_slice(carried)
            .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
        Ok(DecodedFrame {
            sender,
            recipient,
            sequence,
            kind,
            payload,
        })
    }

    fn note_accepted(
        &mut self,
        session_digest: TransportSessionDigest,
        sender: usize,
        bytes: &[u8],
    ) -> Result<()> {
        update_route_root(
            session_digest,
            sender,
            self.endpoint,
            &mut self.accepted[sender],
            bytes,
        )
    }

    fn accept_control(
        &mut self,
        bytes: &[u8],
        session_digest: TransportSessionDigest,
        roster: &EqualityTransportRoster,
        signing_key: &SigningKey,
        ml_kem_dk: &[u8],
    ) -> Result<()> {
        match link_control_kind(bytes)? {
            KIND_LINK_HELLO => {
                let control = verify_link_hello(bytes, session_digest, self.endpoint, roster)?;
                if control.sender >= self.endpoint
                    || control.payload.len() != ML_KEM_768_CT_BYTES
                    || self.links[control.sender].is_some()
                {
                    return Err(EqualityTransportError::AuthenticationFailed);
                }
                let mut classical =
                    peer_shared_secret(signing_key, roster.party_keys[control.sender])?;
                let mut pq = ml_kem768_decaps(ml_kem_dk, control.payload)
                    .ok_or(EqualityTransportError::ConfidentialityFailed)?;
                let transcript = v5_link_kem_transcript(
                    session_digest,
                    control.sender,
                    self.endpoint,
                    roster,
                    control.payload,
                )?;
                let mut combined = combine_hybrid_kem(&classical, &pq, &transcript);
                classical.fill(0);
                pq.fill(0);
                let mut keys = derive_v5_link_keys(
                    &combined,
                    session_digest,
                    control.sender,
                    self.endpoint,
                    self.endpoint,
                )?;
                combined.fill(0);
                let mut responder_nonce = [0u8; 32];
                OsRng
                    .try_fill_bytes(&mut responder_nonce)
                    .map_err(|_| EqualityTransportError::EntropyUnavailable)?;
                let frame = sign_link_confirmation(
                    session_digest,
                    self.endpoint,
                    control.sender,
                    responder_nonce,
                    &keys.confirm,
                )?;
                finalize_v5_link_keys(
                    &mut keys,
                    session_digest,
                    control.sender,
                    self.endpoint,
                    self.endpoint,
                    responder_nonce,
                )?;
                keys.ready = true;
                self.links[control.sender] = Some(keys);
                self.pending_control.push_back(frame);
                Ok(())
            }
            KIND_LINK_CONFIRM => {
                let sender = encoded_control_sender(bytes)?;
                if sender <= self.endpoint {
                    return Err(EqualityTransportError::AuthenticationFailed);
                }
                let keys = self.links[sender]
                    .as_mut()
                    .ok_or(EqualityTransportError::AuthenticationFailed)?;
                if keys.ready {
                    return Err(EqualityTransportError::AuthenticationFailed);
                }
                let responder_nonce = verify_link_confirmation(
                    bytes,
                    session_digest,
                    self.endpoint,
                    sender,
                    &keys.confirm,
                )?;
                finalize_v5_link_keys(
                    keys,
                    session_digest,
                    self.endpoint,
                    sender,
                    self.endpoint,
                    responder_nonce,
                )?;
                keys.ready = true;
                Ok(())
            }
            _ => Err(EqualityTransportError::MalformedFrame(
                "unknown sealed-link control kind",
            )),
        }
    }

    fn try_terminal_seal(
        &mut self,
        session: &PartyMpcSession,
        roster: &EqualityTransportRoster,
        signing_key: &SigningKey,
        ml_dsa: &MlDsaKey,
    ) -> Result<Option<NativePqCrossingEndpointSeal>> {
        if self.terminal_taken {
            return Ok(None);
        }
        if !self.pending_control.is_empty() || !self.all_links_ready() {
            return Ok(None);
        }
        for peer in 0..=roster.coordinator() {
            let (expected_sent, expected_accepted) =
                expected_crossing_route_counts(session, roster, self.endpoint, peer)?;
            if self.sent[peer].count != expected_sent
                || self.accepted[peer].count != expected_accepted
            {
                return Ok(None);
            }
        }
        let session_digest = transport_session_digest(session, roster)?;
        let message =
            endpoint_seal_message(session_digest, self.endpoint, &self.sent, &self.accepted)?;
        let ed25519_signature = signing_key.sign(&message).to_bytes();
        let ml_dsa_signature = ml_dsa
            .try_sign(V5_ENDPOINT_SEAL_ML_DSA_CONTEXT, &message)
            .ok_or(EqualityTransportError::EntropyUnavailable)?;
        if ml_dsa_signature.len() != ML_DSA_SIG_LEN {
            return Err(EqualityTransportError::AuthenticationFailed);
        }
        self.terminal_taken = true;
        Ok(Some(NativePqCrossingEndpointSeal {
            endpoint: self.endpoint,
            session_digest,
            sent: self.sent.clone(),
            accepted: self.accepted.clone(),
            ed25519_signature,
            ml_dsa_signature,
        }))
    }
}

fn finalize_v5_link_keys(
    keys: &mut LinkKeys,
    session_digest: TransportSessionDigest,
    initiator: usize,
    responder: usize,
    endpoint: usize,
    responder_nonce: [u8; 32],
) -> Result<()> {
    let initiator_side = endpoint == initiator;
    if !initiator_side && endpoint != responder {
        return Err(EqualityTransportError::InvalidConfiguration(
            "invalid final link role",
        ));
    }
    let mut ikm = Vec::with_capacity(64 * 5 + 32 * 3);
    let (lo_mac, hi_mac, lo_aead, hi_aead, lo_nonce, hi_nonce) = if initiator_side {
        (
            &keys.send_mac,
            &keys.receive_mac,
            &keys.send_aead,
            &keys.receive_aead,
            &keys.send_nonce,
            &keys.receive_nonce,
        )
    } else {
        (
            &keys.receive_mac,
            &keys.send_mac,
            &keys.receive_aead,
            &keys.send_aead,
            &keys.receive_nonce,
            &keys.send_nonce,
        )
    };
    ikm.extend_from_slice(lo_mac);
    ikm.extend_from_slice(hi_mac);
    ikm.extend_from_slice(lo_aead);
    ikm.extend_from_slice(hi_aead);
    ikm.extend_from_slice(lo_nonce);
    ikm.extend_from_slice(hi_nonce);
    ikm.extend_from_slice(&keys.confirm);
    ikm.extend_from_slice(&responder_nonce);
    let hkdf = Hkdf::<Sha512>::new(Some(V5_LINK_CONFIRM_DOMAIN), &ikm);
    let mut info = Vec::new();
    info.extend_from_slice(&session_digest);
    info.extend_from_slice(&(initiator as u64).to_be_bytes());
    info.extend_from_slice(&(responder as u64).to_be_bytes());
    info.extend_from_slice(&responder_nonce);
    let mut expanded = [0u8; 64 + 64 + 32 + 32 + 64 + 64];
    hkdf.expand(&info, &mut expanded)
        .map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    if initiator_side {
        keys.send_mac.copy_from_slice(&expanded[0..64]);
        keys.receive_mac.copy_from_slice(&expanded[64..128]);
        keys.send_aead.copy_from_slice(&expanded[128..160]);
        keys.receive_aead.copy_from_slice(&expanded[160..192]);
        keys.send_nonce.copy_from_slice(&expanded[192..256]);
        keys.receive_nonce.copy_from_slice(&expanded[256..320]);
    } else {
        keys.receive_mac.copy_from_slice(&expanded[0..64]);
        keys.send_mac.copy_from_slice(&expanded[64..128]);
        keys.receive_aead.copy_from_slice(&expanded[128..160]);
        keys.send_aead.copy_from_slice(&expanded[160..192]);
        keys.receive_nonce.copy_from_slice(&expanded[192..256]);
        keys.send_nonce.copy_from_slice(&expanded[256..320]);
    }
    keys.confirm.fill(0);
    expanded.fill(0);
    ikm.fill(0);
    Ok(())
}

fn v5_frame_mac(key: &[u8; 64], content: &[u8]) -> Result<[u8; 64]> {
    hmac_sha512(key, &v5_frame_mac_message(content))
}

fn v5_frame_mac_message(content: &[u8]) -> Vec<u8> {
    let mut message = Vec::with_capacity(V5_FRAME_MAC_DOMAIN.len() + 16 + content.len());
    message.extend_from_slice(&(V5_FRAME_MAC_DOMAIN.len() as u64).to_be_bytes());
    message.extend_from_slice(V5_FRAME_MAC_DOMAIN);
    message.extend_from_slice(&(content.len() as u64).to_be_bytes());
    message.extend_from_slice(content);
    message
}

fn v5_peer_nonce(
    key: &[u8; 64],
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    sequence: u64,
) -> Result<[u8; PEER_NONCE_BYTES]> {
    let mut message = Vec::new();
    message.extend_from_slice(&session_digest);
    message.extend_from_slice(&(sender as u64).to_be_bytes());
    message.extend_from_slice(&(recipient as u64).to_be_bytes());
    message.extend_from_slice(&sequence.to_be_bytes());
    let full = hmac_sha512(key, &message)?;
    Ok(full[..PEER_NONCE_BYTES].try_into().unwrap())
}

fn encrypt_v5_peer_payload(
    plaintext: &[u8],
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    sequence: u64,
    key: &[u8; 32],
    nonce_key: &[u8; 64],
) -> Result<Vec<u8>> {
    if plaintext.len() > MAX_PAYLOAD_BYTES.saturating_sub(PEER_AEAD_TAG_BYTES) {
        return Err(EqualityTransportError::MalformedFrame(
            "sealed peer payload too large",
        ));
    }
    let nonce = v5_peer_nonce(nonce_key, session_digest, sender, recipient, sequence)?;
    let aad = peer_aead_aad(session_digest, sender, recipient, sequence, plaintext.len())?;
    XChaCha20Poly1305::new_from_slice(key)
        .map_err(|_| EqualityTransportError::ConfidentialityFailed)?
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: plaintext,
                aad: &aad,
            },
        )
        .map_err(|_| EqualityTransportError::ConfidentialityFailed)
}

fn decrypt_v5_peer_payload(
    encrypted: &[u8],
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    sequence: u64,
    key: &[u8; 32],
    nonce_key: &[u8; 64],
) -> Result<Vec<u8>> {
    let plaintext_len = encrypted
        .len()
        .checked_sub(PEER_AEAD_TAG_BYTES)
        .ok_or(EqualityTransportError::ConfidentialityFailed)?;
    let nonce = v5_peer_nonce(nonce_key, session_digest, sender, recipient, sequence)?;
    let aad = peer_aead_aad(session_digest, sender, recipient, sequence, plaintext_len)?;
    XChaCha20Poly1305::new_from_slice(key)
        .map_err(|_| EqualityTransportError::ConfidentialityFailed)?
        .decrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: encrypted,
                aad: &aad,
            },
        )
        .map_err(|_| EqualityTransportError::ConfidentialityFailed)
}

fn update_route_root(
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    accumulator: &mut RouteAccumulator,
    wire: &[u8],
) -> Result<()> {
    let next = accumulator
        .count
        .checked_add(1)
        .ok_or(EqualityTransportError::MalformedFrame(
            "route frame count exhausted",
        ))?;
    let wire_digest = Sha512::digest(wire);
    let mut hash = Sha512::new();
    hash.update((V5_ROUTE_ROOT_DOMAIN.len() as u64).to_be_bytes());
    hash.update(V5_ROUTE_ROOT_DOMAIN);
    hash.update(session_digest);
    hash.update((sender as u64).to_be_bytes());
    hash.update((recipient as u64).to_be_bytes());
    hash.update(next.to_be_bytes());
    hash.update(accumulator.root);
    hash.update(wire_digest);
    accumulator.root = hash.finalize().into();
    accumulator.count = next;
    Ok(())
}

struct DecodedLinkControl<'a> {
    sender: usize,
    payload: &'a [u8],
}

fn make_link_hello(
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    roster: &EqualityTransportRoster,
    identity: &NativePqTransportIdentity,
) -> Result<(AuthenticatedEqualityFrame, LinkKeys)> {
    let recipient_key =
        roster
            .native_key(recipient)
            .ok_or(EqualityTransportError::InvalidConfiguration(
                "sealed link recipient has no ML-KEM key",
            ))?;
    let (ciphertext, mut pq) = ml_kem768_encaps(&recipient_key.ml_kem_ek)
        .ok_or(EqualityTransportError::ConfidentialityFailed)?;
    if ciphertext.len() != ML_KEM_768_CT_BYTES {
        pq.fill(0);
        return Err(EqualityTransportError::ConfidentialityFailed);
    }
    let mut classical = peer_shared_secret(&identity.signing_key, recipient_key.ed25519)?;
    let transcript =
        v5_link_kem_transcript(session_digest, sender, recipient, roster, &ciphertext)?;
    let mut combined = combine_hybrid_kem(&classical, &pq, &transcript);
    classical.fill(0);
    pq.fill(0);
    let keys = derive_v5_link_keys(&combined, session_digest, sender, recipient, sender)?;
    combined.fill(0);
    let frame = sign_link_control(
        session_digest,
        sender,
        recipient,
        KIND_LINK_HELLO,
        &ciphertext,
        &identity.signing_key,
        &identity.ml_dsa,
        roster,
    )?;
    Ok((frame, keys))
}

fn derive_v5_link_keys(
    shared: &[u8; 32],
    session_digest: TransportSessionDigest,
    initiator: usize,
    responder: usize,
    endpoint: usize,
) -> Result<LinkKeys> {
    if initiator >= responder || (endpoint != initiator && endpoint != responder) {
        return Err(EqualityTransportError::InvalidConfiguration(
            "sealed link roles are not canonical",
        ));
    }
    const EXPANDED: usize = 64 + 64 + 32 + 32 + 64 + 64 + 64;
    let hkdf = Hkdf::<Sha512>::new(Some(V5_LINK_KEY_DOMAIN), shared);
    let mut info = Vec::with_capacity(V5_LINK_KEY_DOMAIN.len() + 64 + 16);
    info.extend_from_slice(&(V5_LINK_KEY_DOMAIN.len() as u64).to_be_bytes());
    info.extend_from_slice(V5_LINK_KEY_DOMAIN);
    info.extend_from_slice(&session_digest);
    info.extend_from_slice(&(initiator as u64).to_be_bytes());
    info.extend_from_slice(&(responder as u64).to_be_bytes());
    let mut expanded = [0u8; EXPANDED];
    hkdf.expand(&info, &mut expanded)
        .map_err(|_| EqualityTransportError::ConfidentialityFailed)?;
    let lo_mac: [u8; 64] = expanded[0..64].try_into().unwrap();
    let hi_mac: [u8; 64] = expanded[64..128].try_into().unwrap();
    let lo_aead: [u8; 32] = expanded[128..160].try_into().unwrap();
    let hi_aead: [u8; 32] = expanded[160..192].try_into().unwrap();
    let lo_nonce: [u8; 64] = expanded[192..256].try_into().unwrap();
    let hi_nonce: [u8; 64] = expanded[256..320].try_into().unwrap();
    let confirm: [u8; 64] = expanded[320..384].try_into().unwrap();
    expanded.fill(0);
    let initiator_side = endpoint == initiator;
    Ok(LinkKeys {
        send_mac: if initiator_side { lo_mac } else { hi_mac },
        receive_mac: if initiator_side { hi_mac } else { lo_mac },
        send_aead: if initiator_side { lo_aead } else { hi_aead },
        receive_aead: if initiator_side { hi_aead } else { lo_aead },
        send_nonce: if initiator_side { lo_nonce } else { hi_nonce },
        receive_nonce: if initiator_side { hi_nonce } else { lo_nonce },
        confirm,
        ready: false,
    })
}

fn v5_link_kem_transcript(
    session_digest: TransportSessionDigest,
    initiator: usize,
    responder: usize,
    roster: &EqualityTransportRoster,
    ciphertext: &[u8],
) -> Result<Vec<u8>> {
    let initiator_key =
        roster
            .native_key(initiator)
            .ok_or(EqualityTransportError::InvalidConfiguration(
                "missing link initiator identity",
            ))?;
    let responder_key =
        roster
            .native_key(responder)
            .ok_or(EqualityTransportError::InvalidConfiguration(
                "missing link responder identity",
            ))?;
    let mut out = Vec::new();
    out.extend_from_slice(&(V5_LINK_KEM_TRANSCRIPT_DOMAIN.len() as u64).to_be_bytes());
    out.extend_from_slice(V5_LINK_KEM_TRANSCRIPT_DOMAIN);
    out.extend_from_slice(&session_digest);
    out.extend_from_slice(&(initiator as u64).to_be_bytes());
    out.extend_from_slice(&(responder as u64).to_be_bytes());
    out.extend_from_slice(&initiator_key.ed25519);
    out.extend_from_slice(&initiator_key.ml_dsa);
    out.extend_from_slice(&responder_key.ed25519);
    out.extend_from_slice(&responder_key.ml_dsa);
    out.extend_from_slice(&responder_key.ml_kem_ek);
    out.extend_from_slice(ciphertext);
    Ok(out)
}

fn sign_link_confirmation(
    session_digest: TransportSessionDigest,
    responder: usize,
    initiator: usize,
    responder_nonce: [u8; 32],
    confirmation_key: &[u8; 64],
) -> Result<AuthenticatedEqualityFrame> {
    let mut wire = Vec::new();
    wire.extend_from_slice(LINK_CONTROL_MAGIC);
    wire.push(TransportSecurityProfile::NativePostQuantumSealedCrossing.wire_tag());
    wire.extend_from_slice(&session_digest);
    wire.extend_from_slice(&(responder as u32).to_be_bytes());
    wire.extend_from_slice(&(initiator as u32).to_be_bytes());
    wire.push(KIND_LINK_CONFIRM);
    wire.extend_from_slice(&(responder_nonce.len() as u32).to_be_bytes());
    wire.extend_from_slice(&responder_nonce);
    let tag = hmac_sha512(confirmation_key, &link_confirmation_message(&wire))?;
    wire.extend_from_slice(&tag);
    wire.extend_from_slice(&frame_checksum(&wire));
    Ok(AuthenticatedEqualityFrame {
        sender: responder,
        recipient: initiator,
        sequence: 0,
        wire,
    })
}

fn verify_link_confirmation(
    bytes: &[u8],
    session_digest: TransportSessionDigest,
    initiator: usize,
    responder: usize,
    confirmation_key: &[u8; 64],
) -> Result<[u8; 32]> {
    const HEADER: usize = 8 + 1 + 64 + 4 + 4 + 1 + 4;
    if bytes.len() != HEADER + 32 + 64 + 32 {
        return Err(EqualityTransportError::MalformedFrame(
            "link confirmation length",
        ));
    }
    let checksum_start = bytes.len() - 32;
    if bytes[checksum_start..] != frame_checksum(&bytes[..checksum_start]) {
        return Err(EqualityTransportError::MalformedFrame(
            "link confirmation checksum",
        ));
    }
    let tag_start = checksum_start - 64;
    let content = &bytes[..tag_start];
    let mut input = Reader::new(content);
    if input.array::<8>()? != *LINK_CONTROL_MAGIC
        || input.byte()? != TransportSecurityProfile::NativePostQuantumSealedCrossing.wire_tag()
        || input.array::<64>()? != session_digest
        || input.u32()? as usize != responder
        || input.u32()? as usize != initiator
        || input.byte()? != KIND_LINK_CONFIRM
    {
        return Err(EqualityTransportError::AuthenticationFailed);
    }
    let nonce: [u8; 32] = input
        .bytes(32)?
        .try_into()
        .map_err(|_| EqualityTransportError::MalformedFrame("link confirmation nonce"))?;
    input.finish()?;
    let mut mac = <Hmac<Sha512> as Mac>::new_from_slice(confirmation_key)
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
    mac.update(&link_confirmation_message(content));
    mac.verify_slice(&bytes[tag_start..checksum_start])
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
    Ok(nonce)
}

fn link_confirmation_message(content: &[u8]) -> Vec<u8> {
    let mut message = Vec::with_capacity(V5_LINK_CONFIRM_DOMAIN.len() + 16 + content.len());
    message.extend_from_slice(&(V5_LINK_CONFIRM_DOMAIN.len() as u64).to_be_bytes());
    message.extend_from_slice(V5_LINK_CONFIRM_DOMAIN);
    message.extend_from_slice(&(content.len() as u64).to_be_bytes());
    message.extend_from_slice(content);
    message
}

fn hmac_sha512(key: &[u8], message: &[u8]) -> Result<[u8; 64]> {
    let mut mac = <Hmac<Sha512> as Mac>::new_from_slice(key)
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
    mac.update(message);
    Ok(mac.finalize().into_bytes().into())
}

fn sign_link_control(
    session_digest: TransportSessionDigest,
    sender: usize,
    recipient: usize,
    kind: u8,
    payload: &[u8],
    signing_key: &SigningKey,
    ml_dsa: &MlDsaKey,
    roster: &EqualityTransportRoster,
) -> Result<AuthenticatedEqualityFrame> {
    if payload.len() > MAX_PAYLOAD_BYTES || kind != KIND_LINK_HELLO {
        return Err(EqualityTransportError::MalformedFrame(
            "invalid link control payload",
        ));
    }
    let mut wire = Vec::new();
    wire.extend_from_slice(LINK_CONTROL_MAGIC);
    wire.push(TransportSecurityProfile::NativePostQuantumSealedCrossing.wire_tag());
    wire.extend_from_slice(&session_digest);
    wire.extend_from_slice(&(sender as u32).to_be_bytes());
    wire.extend_from_slice(&(recipient as u32).to_be_bytes());
    wire.push(kind);
    wire.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    wire.extend_from_slice(payload);
    let message = link_control_signing_message(&wire);
    wire.extend_from_slice(&signing_key.sign(&message).to_bytes());
    let pq = ml_dsa
        .try_sign(V5_LINK_HELLO_ML_DSA_CONTEXT, &message)
        .ok_or(EqualityTransportError::EntropyUnavailable)?;
    if pq.len() != ML_DSA_SIG_LEN {
        return Err(EqualityTransportError::AuthenticationFailed);
    }
    wire.extend_from_slice(&pq);
    wire.extend_from_slice(&frame_checksum(&wire));
    if wire.len() > MAX_FRAME_BYTES
        || roster.key(sender) != Some(signing_key.verifying_key().to_bytes())
    {
        return Err(EqualityTransportError::InvalidConfiguration(
            "link-control signer does not match roster",
        ));
    }
    Ok(AuthenticatedEqualityFrame {
        sender,
        recipient,
        sequence: 0,
        wire,
    })
}

fn verify_link_hello<'a>(
    bytes: &'a [u8],
    session_digest: TransportSessionDigest,
    expected_recipient: usize,
    roster: &EqualityTransportRoster,
) -> Result<DecodedLinkControl<'a>> {
    let fixed = 8 + 1 + 64 + 4 + 4 + 1 + 4;
    if bytes.len() < fixed + NATIVE_PQ_TRAILER_BYTES || bytes.len() > MAX_FRAME_BYTES {
        return Err(EqualityTransportError::MalformedFrame(
            "link control length",
        ));
    }
    let checksum_start = bytes.len() - 32;
    if bytes[checksum_start..] != frame_checksum(&bytes[..checksum_start]) {
        return Err(EqualityTransportError::MalformedFrame(
            "link control checksum",
        ));
    }
    let signature_start = checksum_start - 64 - ML_DSA_SIG_LEN;
    let content = &bytes[..signature_start];
    let mut input = Reader::new(content);
    if input.array::<8>()? != *LINK_CONTROL_MAGIC
        || input.byte()? != TransportSecurityProfile::NativePostQuantumSealedCrossing.wire_tag()
        || input.array::<64>()? != session_digest
    {
        return Err(EqualityTransportError::SessionMismatch);
    }
    let sender = input.u32()? as usize;
    let recipient = input.u32()? as usize;
    let kind = input.byte()?;
    let payload = input.bytes(MAX_PAYLOAD_BYTES)?;
    input.finish()?;
    if recipient != expected_recipient || sender == recipient || kind != KIND_LINK_HELLO {
        return Err(EqualityTransportError::RecipientMismatch);
    }
    let public = roster
        .native_key(sender)
        .ok_or(EqualityTransportError::SenderMismatch)?;
    let message = link_control_signing_message(content);
    let ed: [u8; 64] = bytes[signature_start..signature_start + 64]
        .try_into()
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
    VerifyingKey::from_bytes(&public.ed25519)
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?
        .verify_strict(&message, &Signature::from_bytes(&ed))
        .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
    if !ml_dsa_verify(
        &public.ml_dsa,
        V5_LINK_HELLO_ML_DSA_CONTEXT,
        &message,
        &bytes[signature_start + 64..checksum_start],
    ) {
        return Err(EqualityTransportError::AuthenticationFailed);
    }
    Ok(DecodedLinkControl { sender, payload })
}

fn link_control_kind(bytes: &[u8]) -> Result<u8> {
    const KIND_OFFSET: usize = 8 + 1 + 64 + 4 + 4;
    if !bytes.starts_with(LINK_CONTROL_MAGIC) {
        return Err(EqualityTransportError::MalformedFrame(
            "not a v5 link control frame",
        ));
    }
    bytes
        .get(KIND_OFFSET)
        .copied()
        .ok_or(EqualityTransportError::MalformedFrame(
            "truncated link control kind",
        ))
}

fn encoded_control_sender(bytes: &[u8]) -> Result<usize> {
    const SENDER_OFFSET: usize = 8 + 1 + 64;
    Ok(u32::from_be_bytes(
        bytes
            .get(SENDER_OFFSET..SENDER_OFFSET + 4)
            .ok_or(EqualityTransportError::MalformedFrame(
                "truncated control sender",
            ))?
            .try_into()
            .map_err(|_| EqualityTransportError::MalformedFrame("control sender"))?,
    ) as usize)
}

fn link_control_signing_message(content: &[u8]) -> [u8; 64] {
    let mut hash = Sha512::new();
    hash.update((V5_LINK_HELLO_SIGNATURE_DOMAIN.len() as u64).to_be_bytes());
    hash.update(V5_LINK_HELLO_SIGNATURE_DOMAIN);
    hash.update((content.len() as u64).to_be_bytes());
    hash.update(content);
    hash.finalize().into()
}

/// True only for v5 handshake/key-confirmation frames. Routers must forward
/// these, but must not include them in the semantic public crossing evidence.
pub fn is_native_post_quantum_crossing_control_frame(bytes: &[u8]) -> bool {
    bytes.starts_with(LINK_CONTROL_MAGIC)
}

fn expected_crossing_route_counts(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
    sender: usize,
    recipient: usize,
) -> Result<(u64, u64)> {
    if sender == recipient {
        return Ok((0, 0));
    }
    let gates = u64::try_from(session.exact_and_gates())
        .map_err(|_| EqualityTransportError::MalformedFrame("gate count does not fit u64"))?;
    let peer_ingress = u64::try_from(session.buckets)
        .ok()
        .and_then(|buckets| buckets.checked_mul(2))
        .ok_or(EqualityTransportError::MalformedFrame(
            "peer ingress count overflow",
        ))?;
    let coordinator = roster.coordinator();
    let route_count = |from: usize, to: usize| -> Result<u64> {
        if from == to {
            Ok(0)
        } else if from < coordinator && to < coordinator {
            Ok(peer_ingress)
        } else if from < coordinator && to == coordinator {
            gates
                .checked_add(1)
                .ok_or(EqualityTransportError::MalformedFrame(
                    "party route count overflow",
                ))
        } else if from == coordinator && to < coordinator {
            Ok(gates)
        } else {
            Ok(0)
        }
    };
    let sent = route_count(sender, recipient)?;
    let accepted = route_count(recipient, sender)?;
    Ok((sent, accepted))
}

fn endpoint_seal_message(
    session_digest: TransportSessionDigest,
    endpoint: usize,
    sent: &[RouteAccumulator],
    accepted: &[RouteAccumulator],
) -> Result<[u8; 64]> {
    if sent.len() != accepted.len() || endpoint >= sent.len() {
        return Err(EqualityTransportError::MalformedFrame(
            "endpoint seal has a malformed route vector",
        ));
    }
    let mut hash = Sha512::new();
    hash.update((V5_ENDPOINT_SEAL_DOMAIN.len() as u64).to_be_bytes());
    hash.update(V5_ENDPOINT_SEAL_DOMAIN);
    hash.update(session_digest);
    hash.update((endpoint as u64).to_be_bytes());
    hash.update((sent.len() as u64).to_be_bytes());
    for (peer, (outbound, inbound)) in sent.iter().zip(accepted).enumerate() {
        hash.update((peer as u64).to_be_bytes());
        hash.update(outbound.count.to_be_bytes());
        hash.update(outbound.root);
        hash.update(inbound.count.to_be_bytes());
        hash.update(inbound.root);
    }
    Ok(hash.finalize().into())
}

/// Opaque authority capability issued only after the complete native-PQ
/// crossing evidence has been authenticated and reconstructed.
///
/// The v5 verifier fills these private fields; keeping the type here while the
/// verifier is assembled also gives the claim-signing barrier an atomic,
/// compile-safe integration point.
pub struct VerifiedPublicCrossingTranscript {
    session: PartyMpcSession,
    crossing: Crossing,
    transcript: DistributedTranscript,
    ordered_party_authorities: Vec<([u8; 32], Vec<u8>)>,
    claim_binding: [u8; 64],
}

impl VerifiedPublicCrossingTranscript {
    pub(crate) fn matches_clearing_context(
        &self,
        claim: &crate::attestation::ClearingClaim,
        session: &PartyMpcSession,
        crossing: &Crossing,
        transcript: &DistributedTranscript,
        ordered_quorum_keys: &[crate::attestation::NativePqPartyPublicKey],
    ) -> bool {
        self.session == *session
            && &self.crossing == crossing
            && &self.transcript == transcript
            && self.claim_binding == claim.native_pq_verified_crossing_binding()
            && self.ordered_party_authorities.len() == ordered_quorum_keys.len()
            && self
                .ordered_party_authorities
                .iter()
                .zip(ordered_quorum_keys)
                .all(|((ed25519, ml_dsa), expected)| {
                    ed25519 == expected.ed25519() && ml_dsa.as_slice() == expected.ml_dsa()
                })
    }
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
        if preprocessing.requires_durable_custody() {
            return Err(EqualityTransportError::InvalidConfiguration(
                "certified preprocessing requires a durable-custody party machine",
            ));
        }
        preprocessing.validate_runtime_binding()?;
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
    sealed_endpoint: Option<SealedCrossingEndpoint>,
    result_completed: bool,
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

    /// Construct the v5 link-authenticated crossing endpoint.  Link handshakes
    /// are emitted through `try_next_frame` before semantic frames; no v4
    /// per-frame signature fallback is available under this roster profile.
    pub fn new_native_post_quantum_sealed(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        party: usize,
        identity: NativePqTransportIdentity,
        input: PartyArithmeticInput,
        preprocessing: TripleMaterial,
    ) -> Result<Self> {
        validate_crossing_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::NativePostQuantumSealedCrossing {
            return Err(EqualityTransportError::InvalidConfiguration(
                "sealed native-PQ endpoint requires the v5 sealed crossing profile",
            ));
        }
        roster.validate_native_identity(party, &identity)?;
        let session_digest = transport_session_digest(&session, &roster)?;
        let sealed_endpoint =
            SealedCrossingEndpoint::new(party, session_digest, &roster, &identity)?;
        let NativePqTransportIdentity {
            signing_key,
            ml_dsa,
            ml_kem_dk,
            ..
        } = identity;
        let mut machine = Self::new_with_crypto(
            session,
            roster,
            party,
            signing_key,
            Some(ml_dsa),
            Some(ml_kem_dk),
            input,
            preprocessing,
        )?;
        machine.sealed_endpoint = Some(sealed_endpoint);
        Ok(machine)
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
        if preprocessing.requires_durable_custody() {
            return Err(EqualityTransportError::InvalidConfiguration(
                "certified preprocessing requires a durable-custody party machine",
            ));
        }
        preprocessing.validate_runtime_binding()?;
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
            sealed_endpoint: None,
            result_completed: false,
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn try_next_frame(&mut self) -> Result<Option<AuthenticatedEqualityFrame>> {
        if let Some(endpoint) = self.sealed_endpoint.as_mut() {
            if let Some(control) = endpoint.try_next_control() {
                return Ok(Some(control));
            }
            if !endpoint.all_links_ready() {
                return Ok(None);
            }
        }
        loop {
            match self.outbound.try_recv() {
                Ok(raw) => {
                    let raw = match raw {
                        RawOutbound::Peer(message) if message.to == self.party => {
                            if message.from != self.party
                                || message.session != self.session.binding()
                            {
                                return Err(EqualityTransportError::SessionMismatch);
                            }
                            self.peer_in
                                .send(message)
                                .map_err(|_| EqualityTransportError::ChannelClosed)?;
                            continue;
                        }
                        other => other,
                    };
                    let (recipient, payload) =
                        encode_party_outbound(&self.session, self.party, raw)?;
                    let sequence = self.outbound_sequences[recipient];
                    self.outbound_sequences[recipient] =
                        sequence
                            .checked_add(1)
                            .ok_or(EqualityTransportError::MalformedFrame(
                                "outbound sequence exhausted",
                            ))?;
                    let frame = if let Some(endpoint) = self.sealed_endpoint.as_mut() {
                        endpoint.seal_semantic_frame(
                            self.session_digest,
                            self.party,
                            recipient,
                            sequence,
                            payload,
                        )?
                    } else {
                        sign_frame(
                            self.session_digest,
                            self.party,
                            recipient,
                            sequence,
                            payload,
                            &self.signing_key,
                            self.ml_dsa.as_ref(),
                            &self.roster,
                        )?
                    };
                    return Ok(Some(frame));
                }
                Err(TryRecvError::Empty) | Err(TryRecvError::Disconnected) => return Ok(None),
            }
        }
    }

    pub fn accept_frame(&mut self, bytes: &[u8]) -> Result<()> {
        if is_native_post_quantum_crossing_control_frame(bytes) {
            let endpoint = self
                .sealed_endpoint
                .as_mut()
                .ok_or(EqualityTransportError::AuthenticationFailed)?;
            return endpoint.accept_control(
                bytes,
                self.session_digest,
                &self.roster,
                &self.signing_key,
                self.ml_kem_dk
                    .as_deref()
                    .ok_or(EqualityTransportError::InvalidConfiguration(
                        "sealed party is missing ML-KEM decapsulation material",
                    ))?,
            );
        }
        let decoded = if let Some(endpoint) = self.sealed_endpoint.as_ref() {
            endpoint.verify_semantic_frame(bytes, self.session_digest, self.party)?
        } else {
            verify_frame(bytes, self.session_digest, self.party, &self.roster)?
        };
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
        let inbound = if self.sealed_endpoint.is_some() && decoded.kind == KIND_PEER_INGRESS {
            decode_v5_party_peer_inbound(
                &self.session,
                self.session_digest,
                self.party,
                self.sealed_endpoint.as_ref().unwrap(),
                decoded,
            )?
        } else {
            decode_party_inbound(
                &self.session,
                self.session_digest,
                self.party,
                &self.signing_key,
                self.ml_kem_dk.as_deref(),
                &self.roster,
                decoded,
            )?
        };
        match inbound {
            PartyInbound::Peer(message) => self
                .peer_in
                .send(message)
                .map_err(|_| EqualityTransportError::ChannelClosed)?,
            PartyInbound::Coordinator(message) => self
                .coordinator_in
                .send(message)
                .map_err(|_| EqualityTransportError::ChannelClosed)?,
        }
        if let Some(endpoint) = self.sealed_endpoint.as_mut() {
            endpoint.note_accepted(self.session_digest, sender, bytes)?;
        }
        self.inbound_sequences[sender] = expected + 1;
        Ok(())
    }

    pub fn try_result(&mut self) -> Result<Option<PartyReport>> {
        match self.result.try_recv() {
            Ok(result) => {
                let report = result.map_err(EqualityTransportError::from)?;
                self.result_completed = true;
                Ok(Some(report))
            }
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => Err(EqualityTransportError::WorkerPanicked),
        }
    }

    /// Produce this party's one-shot terminal route seal only after the exact
    /// PartyMPC schedule has completed and every expected route is closed.
    pub fn try_terminal_seal(&mut self) -> Result<Option<NativePqCrossingEndpointSeal>> {
        if !self.result_completed {
            return Ok(None);
        }
        let endpoint =
            self.sealed_endpoint
                .as_mut()
                .ok_or(EqualityTransportError::InvalidConfiguration(
                    "terminal seals require the v5 sealed crossing profile",
                ))?;
        endpoint.try_terminal_seal(
            &self.session,
            &self.roster,
            &self.signing_key,
            self.ml_dsa
                .as_ref()
                .ok_or(EqualityTransportError::InvalidConfiguration(
                    "sealed crossing party is missing ML-DSA material",
                ))?,
        )
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
    ml_kem_dk: Option<Vec<u8>>,
    party_in: Sender<PartyMessage>,
    outbound: Receiver<RawOutbound>,
    result: Receiver<std::result::Result<DistributedRun, PartyMpcError>>,
    outbound_sequences: Vec<u64>,
    inbound_sequences: Vec<u64>,
    sealed_endpoint: Option<SealedCrossingEndpoint>,
    result_completed: bool,
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

    pub fn new_native_post_quantum_sealed(
        session: PartyMpcSession,
        roster: EqualityTransportRoster,
        identity: NativePqTransportIdentity,
    ) -> Result<Self> {
        validate_crossing_transport_session(&session, &roster)?;
        if roster.profile != TransportSecurityProfile::NativePostQuantumSealedCrossing {
            return Err(EqualityTransportError::InvalidConfiguration(
                "sealed native-PQ coordinator requires the v5 sealed crossing profile",
            ));
        }
        let coordinator = roster.coordinator();
        roster.validate_native_identity(coordinator, &identity)?;
        let session_digest = transport_session_digest(&session, &roster)?;
        let sealed_endpoint =
            SealedCrossingEndpoint::new(coordinator, session_digest, &roster, &identity)?;
        let NativePqTransportIdentity {
            signing_key,
            ml_dsa,
            ml_kem_dk,
            ..
        } = identity;
        let mut machine = Self::new_with_crypto(session, roster, signing_key, Some(ml_dsa))?;
        machine.ml_kem_dk = Some(ml_kem_dk);
        machine.sealed_endpoint = Some(sealed_endpoint);
        Ok(machine)
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
            ml_kem_dk: None,
            party_in: party_in_tx,
            outbound: outbound_rx,
            result: result_rx,
            outbound_sequences: vec![0; roster.n_parties()],
            inbound_sequences: vec![0; roster.n_parties()],
            sealed_endpoint: None,
            result_completed: false,
        })
    }

    pub fn try_next_frame(&mut self) -> Result<Option<AuthenticatedEqualityFrame>> {
        if let Some(endpoint) = self.sealed_endpoint.as_mut() {
            if let Some(control) = endpoint.try_next_control() {
                return Ok(Some(control));
            }
            if !endpoint.all_links_ready() {
                return Ok(None);
            }
        }
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
                let frame = if let Some(endpoint) = self.sealed_endpoint.as_mut() {
                    endpoint.seal_semantic_frame(
                        self.session_digest,
                        self.roster.coordinator(),
                        recipient,
                        sequence,
                        payload,
                    )?
                } else {
                    sign_frame(
                        self.session_digest,
                        self.roster.coordinator(),
                        recipient,
                        sequence,
                        payload,
                        &self.signing_key,
                        self.ml_dsa.as_ref(),
                        &self.roster,
                    )?
                };
                Ok(Some(frame))
            }
            Ok(_) => Err(EqualityTransportError::MalformedFrame(
                "coordinator emitted a party message",
            )),
            Err(TryRecvError::Empty) | Err(TryRecvError::Disconnected) => Ok(None),
        }
    }

    pub fn accept_frame(&mut self, bytes: &[u8]) -> Result<()> {
        if is_native_post_quantum_crossing_control_frame(bytes) {
            let endpoint = self
                .sealed_endpoint
                .as_mut()
                .ok_or(EqualityTransportError::AuthenticationFailed)?;
            return endpoint.accept_control(
                bytes,
                self.session_digest,
                &self.roster,
                &self.signing_key,
                self.ml_kem_dk
                    .as_deref()
                    .ok_or(EqualityTransportError::InvalidConfiguration(
                        "sealed coordinator is missing ML-KEM decapsulation material",
                    ))?,
            );
        }
        let decoded = if let Some(endpoint) = self.sealed_endpoint.as_ref() {
            endpoint.verify_semantic_frame(bytes, self.session_digest, self.roster.coordinator())?
        } else {
            verify_frame(
                bytes,
                self.session_digest,
                self.roster.coordinator(),
                &self.roster,
            )?
        };
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
        if let Some(endpoint) = self.sealed_endpoint.as_mut() {
            endpoint.note_accepted(self.session_digest, sender, bytes)?;
        }
        self.inbound_sequences[sender] = expected + 1;
        Ok(())
    }

    pub fn try_result(&mut self) -> Result<Option<DistributedRun>> {
        match self.result.try_recv() {
            Ok(result) => {
                let run = result.map_err(EqualityTransportError::from)?;
                self.result_completed = true;
                Ok(Some(run))
            }
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => Err(EqualityTransportError::WorkerPanicked),
        }
    }

    pub fn try_terminal_seal(&mut self) -> Result<Option<NativePqCrossingEndpointSeal>> {
        if !self.result_completed {
            return Ok(None);
        }
        let endpoint =
            self.sealed_endpoint
                .as_mut()
                .ok_or(EqualityTransportError::InvalidConfiguration(
                    "terminal seals require the v5 sealed crossing profile",
                ))?;
        endpoint.try_terminal_seal(
            &self.session,
            &self.roster,
            &self.signing_key,
            self.ml_dsa
                .as_ref()
                .ok_or(EqualityTransportError::InvalidConfiguration(
                    "sealed crossing coordinator is missing ML-DSA material",
                ))?,
        )
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
    validate_preprocessing_roster(session, roster)?;
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
    validate_preprocessing_roster(session, roster)?;
    Ok(())
}

fn validate_preprocessing_roster(
    session: &PartyMpcSession,
    roster: &EqualityTransportRoster,
) -> Result<()> {
    if let Some(binding) = session.preprocessing_binding() {
        if binding.roster_digest() != roster.preprocessing_roster_digest() {
            return Err(EqualityTransportError::InvalidConfiguration(
                "certified preprocessing is bound to a different transport roster",
            ));
        }
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

fn decode_v5_party_peer_inbound(
    session: &PartyMpcSession,
    session_digest: TransportSessionDigest,
    party: usize,
    endpoint: &SealedCrossingEndpoint,
    frame: DecodedFrame<'_>,
) -> Result<PartyInbound> {
    if frame.kind != KIND_PEER_INGRESS
        || frame.sender >= session.n_parties
        || frame.recipient != party
        || frame.sender == party
    {
        return Err(EqualityTransportError::RecipientMismatch);
    }
    let link = endpoint
        .links
        .get(frame.sender)
        .and_then(Option::as_ref)
        .ok_or(EqualityTransportError::SenderMismatch)?;
    let mut plaintext = decrypt_v5_peer_payload(
        frame.payload,
        session_digest,
        frame.sender,
        party,
        frame.sequence,
        &link.receive_aead,
        &link.receive_nonce,
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
                "sealed peer ingress shape mismatch",
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
    plaintext.fill(0);
    decoded
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
        TransportSecurityProfile::NativePostQuantum
        | TransportSecurityProfile::NativePostQuantumSealedCrossing => {
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
        TransportSecurityProfile::NativePostQuantum
        | TransportSecurityProfile::NativePostQuantumSealedCrossing => ML_KEM_768_CT_BYTES,
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
        TransportSecurityProfile::NativePostQuantum
        | TransportSecurityProfile::NativePostQuantumSealedCrossing => {
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
        TransportSecurityProfile::NativePostQuantum
        | TransportSecurityProfile::NativePostQuantumSealedCrossing => ML_KEM_768_CT_BYTES,
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
        TransportSecurityProfile::NativePostQuantum
        | TransportSecurityProfile::NativePostQuantumSealedCrossing => {
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
        TransportSecurityProfile::NativePostQuantum
        | TransportSecurityProfile::NativePostQuantumSealedCrossing => {
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
    if roster.profile != TransportSecurityProfile::ClassicalCompatibility {
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

/// Verify the v5 crossing evidence and issue the opaque authority capability
/// consumed by the clearing-claim signing barrier.
///
/// HMAC keys remain endpoint-local. Public authentication therefore comes
/// from the complete set of dual Ed25519/ML-DSA terminal seals: for every
/// directed route the sender's final root/count must equal the recipient's,
/// and every public route is recomputed from the supplied frame bytes. Private
/// peer-ingress routes are not disclosed, but both endpoints independently
/// seal the same exact nonzero root and the protocol-fixed frame count.
pub fn verify_native_post_quantum_public_crossing_transcript(
    session: &PartyMpcSession,
    roster: &CrossingTransportRoster,
    frames: &[Vec<u8>],
    seals: &[NativePqCrossingEndpointSeal],
    crossing: &Crossing,
    transcript: &DistributedTranscript,
    claim: &crate::attestation::ClearingClaim,
) -> Result<VerifiedPublicCrossingTranscript> {
    validate_crossing_transport_session(session, roster)?;
    if roster.profile != TransportSecurityProfile::NativePostQuantumSealedCrossing {
        return Err(EqualityTransportError::InvalidConfiguration(
            "v5 crossing verification requires the sealed native-PQ profile",
        ));
    }
    let ordered_quorum_keys = roster
        .native_party_keys
        .iter()
        .map(|key| crate::attestation::NativePqPartyPublicKey::new(key.ed25519, key.ml_dsa.clone()))
        .collect::<Vec<_>>();
    if !claim.matches_native_pq_verified_crossing_context(
        session,
        crossing,
        transcript,
        &ordered_quorum_keys,
    ) {
        return Err(EqualityTransportError::InvalidConfiguration(
            "clearing claim does not match the sealed crossing context",
        ));
    }
    if !transcript.is_reveal_only(session) {
        return Err(EqualityTransportError::MalformedFrame(
            "crossing transcript is not reveal-only for this session",
        ));
    }
    let endpoints = roster.n_parties() + 1;
    if seals.len() != endpoints {
        return Err(EqualityTransportError::AuthenticationFailed);
    }
    let session_digest = transport_session_digest(session, roster)?;
    for (endpoint, seal) in seals.iter().enumerate() {
        if seal.endpoint != endpoint
            || seal.session_digest != session_digest
            || seal.sent.len() != endpoints
            || seal.accepted.len() != endpoints
        {
            return Err(EqualityTransportError::AuthenticationFailed);
        }
        for peer in 0..endpoints {
            let (sent, accepted) = expected_crossing_route_counts(session, roster, endpoint, peer)?;
            if seal.sent[peer].count != sent || seal.accepted[peer].count != accepted {
                return Err(EqualityTransportError::AuthenticationFailed);
            }
        }
        let message = endpoint_seal_message(session_digest, endpoint, &seal.sent, &seal.accepted)?;
        let public = roster
            .native_key(endpoint)
            .ok_or(EqualityTransportError::AuthenticationFailed)?;
        VerifyingKey::from_bytes(&public.ed25519)
            .map_err(|_| EqualityTransportError::AuthenticationFailed)?
            .verify_strict(&message, &Signature::from_bytes(&seal.ed25519_signature))
            .map_err(|_| EqualityTransportError::AuthenticationFailed)?;
        if !ml_dsa_verify(
            &public.ml_dsa,
            V5_ENDPOINT_SEAL_ML_DSA_CONTEXT,
            &message,
            &seal.ml_dsa_signature,
        ) {
            return Err(EqualityTransportError::AuthenticationFailed);
        }
    }
    for sender in 0..endpoints {
        for recipient in 0..endpoints {
            if seals[sender].sent[recipient].count != seals[recipient].accepted[sender].count
                || seals[sender].sent[recipient].root != seals[recipient].accepted[sender].root
            {
                return Err(EqualityTransportError::AuthenticationFailed);
            }
        }
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
        .and_then(|count| count.checked_add(session.n_parties))
        .ok_or(EqualityTransportError::MalformedFrame(
            "crossing transcript frame count overflow",
        ))?;
    if frames.len() != expected_frames {
        return Err(EqualityTransportError::MalformedFrame(
            "crossing transcript has an incomplete sealed frame set",
        ));
    }
    let output_sequence = u64::try_from(gates)
        .map_err(|_| EqualityTransportError::MalformedFrame("gate count does not fit u64"))?;
    let finished_sequence =
        output_sequence
            .checked_add(1)
            .ok_or(EqualityTransportError::MalformedFrame(
                "crossing sequence exhausted",
            ))?;
    let mut public_roots = vec![vec![RouteAccumulator::default(); endpoints]; endpoints];
    let mut party_next = vec![0u64; session.n_parties];
    let mut coordinator_next = vec![0u64; session.n_parties];
    let mut gate_counts = vec![0usize; gates];
    let mut masked = vec![(0u8, 0u8); gates];
    let mut opened_counts = vec![0usize; gates];
    let mut coordinator_opened = vec![None; gates];
    let mut output_count = 0usize;
    let mut pstar = vec![0u8; index_bits(session.buckets)];
    let mut vstar = vec![0u8; session.value_bits];

    for wire in frames {
        if is_native_post_quantum_crossing_control_frame(wire) {
            return Err(EqualityTransportError::MalformedFrame(
                "link-control frame was included as public crossing evidence",
            ));
        }
        let frame = parse_v5_public_frame(wire, session_digest)?;
        if !((frame.sender < session.n_parties && frame.recipient == roster.coordinator())
            || (frame.sender == roster.coordinator() && frame.recipient < session.n_parties))
        {
            return Err(EqualityTransportError::MalformedFrame(
                "sealed public evidence contains a private or misrouted frame",
            ));
        }
        update_route_root(
            session_digest,
            frame.sender,
            frame.recipient,
            &mut public_roots[frame.sender][frame.recipient],
            wire,
        )?;
        if frame.sender < session.n_parties {
            let expected = party_next[frame.sender];
            if frame.sequence != expected {
                return Err(EqualityTransportError::SequenceMismatch {
                    sender: frame.sender,
                    have: frame.sequence,
                    need: expected,
                });
            }
            party_next[frame.sender] = expected + 1;
            match frame.kind {
                KIND_GATE_SHARE if frame.sequence < output_sequence => {
                    let (gate, d, e) = decode_gate(frame.payload)?;
                    if gate != frame.sequence as usize {
                        return Err(EqualityTransportError::MalformedFrame(
                            "sealed gate share is out of canonical order",
                        ));
                    }
                    gate_counts[gate] += 1;
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
                    output_count += 1;
                }
                _ => {
                    return Err(EqualityTransportError::MalformedFrame(
                        "sealed party frame has the wrong kind or phase",
                    ))
                }
            }
        } else {
            let expected = coordinator_next[frame.recipient];
            if frame.sequence != expected {
                return Err(EqualityTransportError::SequenceMismatch {
                    sender: frame.sender,
                    have: frame.sequence,
                    need: expected,
                });
            }
            coordinator_next[frame.recipient] = expected + 1;
            if frame.kind != KIND_GATE_OPENED || frame.sequence >= output_sequence {
                return Err(EqualityTransportError::MalformedFrame(
                    "sealed coordinator frame has the wrong kind or phase",
                ));
            }
            let (gate, d, e) = decode_gate(frame.payload)?;
            if gate != frame.sequence as usize
                || coordinator_opened[gate].is_some_and(|opening| opening != (d, e))
            {
                return Err(EqualityTransportError::MalformedFrame(
                    "sealed coordinator opening is noncanonical or inconsistent",
                ));
            }
            coordinator_opened[gate] = Some((d, e));
            opened_counts[gate] += 1;
        }
    }

    for party in 0..session.n_parties {
        let coordinator = roster.coordinator();
        if public_roots[party][coordinator].count != seals[party].sent[coordinator].count
            || public_roots[party][coordinator].root != seals[party].sent[coordinator].root
            || public_roots[coordinator][party].count != seals[coordinator].sent[party].count
            || public_roots[coordinator][party].root != seals[coordinator].sent[party].root
        {
            return Err(EqualityTransportError::AuthenticationFailed);
        }
    }
    let index = super::decode_bits(&pstar).map_err(EqualityTransportError::Mpc)? as usize;
    let volume = super::decode_bits(&vstar).map_err(EqualityTransportError::Mpc)?;
    if index >= session.buckets || (volume == 0 && index != 0) {
        return Err(EqualityTransportError::MalformedFrame(
            "sealed output shares reconstruct an invalid crossing",
        ));
    }
    let reconstructed = Crossing {
        p_star: (volume != 0).then_some(index),
        v_star: volume,
    };
    if party_next
        .iter()
        .any(|sequence| *sequence != finished_sequence)
        || coordinator_next
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
            "sealed frames do not reconstruct the crossing transcript",
        ));
    }
    Ok(VerifiedPublicCrossingTranscript {
        session: session.clone(),
        crossing: crossing.clone(),
        transcript: transcript.clone(),
        ordered_party_authorities: roster
            .native_party_keys
            .iter()
            .map(|key| (key.ed25519, key.ml_dsa.clone()))
            .collect(),
        claim_binding: claim.native_pq_verified_crossing_binding(),
    })
}

fn parse_v5_public_frame<'a>(
    bytes: &'a [u8],
    session_digest: TransportSessionDigest,
) -> Result<DecodedFrame<'a>> {
    if bytes.len() < FIXED_CONTENT_BYTES + SEALED_TRAILER_BYTES || bytes.len() > MAX_FRAME_BYTES {
        return Err(EqualityTransportError::MalformedFrame(
            "sealed public frame length",
        ));
    }
    let checksum_start = bytes.len() - 32;
    if bytes[checksum_start..] != frame_checksum(&bytes[..checksum_start]) {
        return Err(EqualityTransportError::MalformedFrame(
            "sealed public frame checksum",
        ));
    }
    let content = &bytes[..checksum_start - 64];
    let mut input = Reader::new(content);
    if input.array::<8>()? != *SEALED_FRAME_MAGIC
        || input.byte()? != TransportSecurityProfile::NativePostQuantumSealedCrossing.wire_tag()
    {
        return Err(EqualityTransportError::AuthenticationFailed);
    }
    if input.array::<64>()? != session_digest {
        return Err(EqualityTransportError::SessionMismatch);
    }
    let sender = input.u32()? as usize;
    let recipient = input.u32()? as usize;
    let sequence = input.u64()?;
    let kind = input.byte()?;
    let payload = input.bytes(MAX_PAYLOAD_BYTES)?;
    input.finish()?;
    Ok(DecodedFrame {
        sender,
        recipient,
        sequence,
        kind,
        payload,
    })
}

/// Public router predicate for the exact v5 semantic crossing carrier.
pub fn is_native_post_quantum_crossing_public_evidence_frame(bytes: &[u8]) -> bool {
    bytes.starts_with(SEALED_FRAME_MAGIC)
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
        EqualityTransportError, EqualityTransportRoster, NativePqTransportPublicIdentity,
        TransportSecurityProfile, KIND_DECISION_SHARE, KIND_GATE_SHARE, KIND_PEER_INGRESS,
        PEER_NONCE_BYTES,
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

    #[test]
    fn sealed_roster_rejects_a_coordinator_montgomery_alias_hidden_by_edwards_sign() {
        let party_zero = SigningKey::from_bytes(&[0x75; 32]);
        let party_one = SigningKey::from_bytes(&[0x76; 32]);
        let mut coordinator_alias = party_zero.verifying_key().to_bytes();
        coordinator_alias[31] ^= 0x80;
        assert_ne!(coordinator_alias, party_zero.verifying_key().to_bytes());
        assert_eq!(
            CompressedEdwardsY(coordinator_alias)
                .decompress()
                .unwrap()
                .to_montgomery(),
            CompressedEdwardsY(party_zero.verifying_key().to_bytes())
                .decompress()
                .unwrap()
                .to_montgomery(),
        );
        let public = |ed25519, byte| {
            NativePqTransportPublicIdentity::from_parts(
                ed25519,
                vec![byte; super::ML_DSA_PK_LEN],
                vec![byte.wrapping_add(1); super::ML_KEM_768_EK_BYTES],
            )
            .unwrap()
        };
        let parties = vec![
            public(party_zero.verifying_key().to_bytes(), 1),
            public(party_one.verifying_key().to_bytes(), 3),
        ];
        let coordinator = public(coordinator_alias, 5);
        assert!(matches!(
            EqualityTransportRoster::new_native_post_quantum_sealed_crossing(parties, coordinator,),
            Err(EqualityTransportError::InvalidConfiguration(
                "sealed endpoint keys must have distinct nonzero Montgomery identities"
            ))
        ));
    }

    #[test]
    fn sealed_session_and_preprocessing_digests_bind_every_pq_roster_key() {
        let party_zero = SigningKey::from_bytes(&[0x65; 32]);
        let party_one = SigningKey::from_bytes(&[0x66; 32]);
        let coordinator = SigningKey::from_bytes(&[0x67; 32]);
        let public = |ed25519, dsa, kem| {
            NativePqTransportPublicIdentity::from_parts(
                ed25519,
                vec![dsa; super::ML_DSA_PK_LEN],
                vec![kem; super::ML_KEM_768_EK_BYTES],
            )
            .unwrap()
        };
        let roster = EqualityTransportRoster::new_native_post_quantum_sealed_crossing(
            vec![
                public(party_zero.verifying_key().to_bytes(), 1, 2),
                public(party_one.verifying_key().to_bytes(), 3, 4),
            ],
            public(coordinator.verifying_key().to_bytes(), 5, 6),
        )
        .unwrap();
        let changed_party_dsa = EqualityTransportRoster::new_native_post_quantum_sealed_crossing(
            vec![
                public(party_zero.verifying_key().to_bytes(), 7, 2),
                public(party_one.verifying_key().to_bytes(), 3, 4),
            ],
            public(coordinator.verifying_key().to_bytes(), 5, 6),
        )
        .unwrap();
        let changed_coordinator_kem =
            EqualityTransportRoster::new_native_post_quantum_sealed_crossing(
                vec![
                    public(party_zero.verifying_key().to_bytes(), 1, 2),
                    public(party_one.verifying_key().to_bytes(), 3, 4),
                ],
                public(coordinator.verifying_key().to_bytes(), 5, 8),
            )
            .unwrap();
        let session =
            PartyMpcSession::new([0x68; 32], 2, 1, 8, 257, Duration::from_secs(1)).unwrap();
        let session_digest = super::transport_session_digest(&session, &roster).unwrap();
        assert_ne!(
            session_digest,
            super::transport_session_digest(&session, &changed_party_dsa).unwrap()
        );
        assert_ne!(
            session_digest,
            super::transport_session_digest(&session, &changed_coordinator_kem).unwrap()
        );
        assert_ne!(
            roster.preprocessing_roster_digest(),
            changed_party_dsa.preprocessing_roster_digest()
        );
        assert_ne!(
            roster.preprocessing_roster_digest(),
            changed_coordinator_kem.preprocessing_roster_digest()
        );
    }

    #[test]
    fn sealed_route_schedule_keeps_party_output_asymmetric_from_opening_broadcast() {
        let keys = [
            SigningKey::from_bytes(&[0x77; 32]),
            SigningKey::from_bytes(&[0x78; 32]),
        ];
        let coordinator = SigningKey::from_bytes(&[0x79; 32]);
        let roster = EqualityTransportRoster {
            party_keys: keys
                .iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            coordinator_key: coordinator.verifying_key().to_bytes(),
            profile: TransportSecurityProfile::NativePostQuantumSealedCrossing,
            native_party_keys: Vec::new(),
            native_coordinator_key: None,
        };
        let session =
            PartyMpcSession::new([0x7a; 32], 2, 1, 8, 257, Duration::from_secs(1)).unwrap();
        let gates = session.exact_and_gates() as u64;
        assert_eq!(
            super::expected_crossing_route_counts(&session, &roster, 0, roster.coordinator())
                .unwrap(),
            (gates + 1, gates),
        );
        assert_eq!(
            super::expected_crossing_route_counts(&session, &roster, roster.coordinator(), 0)
                .unwrap(),
            (gates, gates + 1),
        );
    }
}

//! Handoff Protocol: transferring live capability references to third parties.
//!
//! A handoff transfers a live capability reference to a third party without
//! requiring the original holder and the target to be online simultaneously.
//!
//! The key insight: a [`HandoffCertificate`] is like a bearer capability proof but
//! at the NETWORK layer. It is a signed statement: "I (the introducer) authorize
//! recipient R to contact target T with these permissions."
//!
//! # Flow
//!
//! 1. **Introducer** creates a swiss entry at the target federation, then signs
//!    a `HandoffCertificate` naming the recipient.
//! 2. The certificate can travel out-of-band (QR code, email, file, BLE mesh).
//! 3. **Recipient** presents the certificate to the target federation.
//! 4. **Target** validates the introducer's signature, checks the swiss number,
//!    and creates a routing entry granting the recipient access.
//!
//! # Security Properties
//!
//! - Only the named recipient can present the certificate (recipient signature check).
//! - The target must recognize the introducer (trust path).
//! - Swiss numbers are pre-registered, preventing replay after revocation.
//! - Optional expiration and use-count limits.

use dregg_cell::{AuthRequired, EffectMask};
use dregg_types::{CellId, PublicKey, Signature, SigningKey, sign};
use serde::{Deserialize, Serialize};

// TODO(unified-lace): migrate FederationId to StrandId for introducer identity,
// and GroupId for known_federations. Phase B of unified lace migration.
use crate::FederationId;
use crate::sturdy::SwissTable;

// =============================================================================
// Errors
// =============================================================================

/// Errors during handoff validation or presentation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HandoffError {
    /// The introducer's signature on the certificate is invalid.
    InvalidIntroducerSignature,
    /// The recipient's signature on the presentation is invalid.
    InvalidRecipientSignature,
    /// The introducer's ML-DSA-65 (post-quantum) half of the HYBRID signature is
    /// invalid *against the enrolled introducer key*. Raised when the classical
    /// ed25519 half may be valid but the PQ half is missing, malformed, or signed
    /// under a key other than the identity's ENROLLED ML-DSA key — the exact
    /// forgery a quantum adversary would mount. Fail-closed.
    InvalidIntroducerPqSignature,
    /// The recipient's ML-DSA-65 (post-quantum) half of the HYBRID presentation is
    /// invalid against the introducer-PINNED recipient ML-DSA key. Fail-closed.
    InvalidRecipientPqSignature,
    /// The introducer is not a recognized/trusted federation.
    UntrustedIntroducer,
    /// The swiss number in the certificate is not in the target's swiss table.
    SwissNotFound,
    /// The certificate has expired (past the expiration height).
    Expired,
    /// The certificate has been used the maximum number of times.
    MaxUsesExhausted,
    /// Deserialization failed.
    DeserializationFailed(String),
    /// The nonce has already been seen (replay attempt).
    ReplayDetected,
    /// The certificate grants MORE authority than the introducer holds on the
    /// target (the swiss-registered entry). This is an authority-amplification
    /// attempt and violates the Granovetter discipline (only connectivity
    /// begets connectivity): `granted ⊄ held`. Mirrors the Lean
    /// `Exec/CapTP.lean::handoff_non_amplifying` spec (`granted ≤ held`).
    Amplification,
    /// The certificate's claimed `target_cell` does not match the cell the
    /// swiss entry actually points to (`held.cell_id`). A handoff must re-share
    /// the SAME target the introducer holds — it cannot redirect a swiss entry
    /// registered for cell X to confer access to a different cell Y. Enforces
    /// the Lean `Exec/CapTP.lean::handoff_same_target` spec
    /// (`granted.target = held.target`): without this check, the granted
    /// `cell_id` is the cert's (introducer-asserted) claim, so a forged cert
    /// could name an arbitrary target and the non-amplification check (over
    /// rights, not target) would not catch it.
    TargetMismatch,
}

impl std::fmt::Display for HandoffError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HandoffError::InvalidIntroducerSignature => {
                write!(f, "invalid introducer signature on handoff certificate")
            }
            HandoffError::InvalidRecipientSignature => {
                write!(f, "invalid recipient signature on handoff presentation")
            }
            HandoffError::InvalidIntroducerPqSignature => write!(
                f,
                "invalid introducer ML-DSA (post-quantum) half: not signed under the enrolled key"
            ),
            HandoffError::InvalidRecipientPqSignature => write!(
                f,
                "invalid recipient ML-DSA (post-quantum) half on handoff presentation"
            ),
            HandoffError::UntrustedIntroducer => {
                write!(f, "introducer is not a trusted federation")
            }
            HandoffError::SwissNotFound => {
                write!(f, "swiss number not found in target's table")
            }
            HandoffError::Expired => write!(f, "handoff certificate has expired"),
            HandoffError::MaxUsesExhausted => {
                write!(f, "handoff certificate max uses exhausted")
            }
            HandoffError::DeserializationFailed(msg) => {
                write!(f, "handoff deserialization failed: {msg}")
            }
            HandoffError::ReplayDetected => write!(f, "replay detected: nonce already seen"),
            HandoffError::Amplification => write!(
                f,
                "handoff amplifies authority: granted permissions exceed introducer's held swiss entry"
            ),
            HandoffError::TargetMismatch => write!(
                f,
                "handoff target mismatch: certificate target_cell differs from the swiss entry's cell"
            ),
        }
    }
}

impl std::error::Error for HandoffError {}

// =============================================================================
// HandoffCertificate
// =============================================================================

/// A certificate that authorizes a recipient to enliven a capability at a target federation.
///
/// Can travel out-of-band (QR code, email, file, BLE mesh message). The recipient
/// presents this to the target federation along with a proof that they are indeed
/// the named recipient.
// AUDIT[P2]: Public fields enable post-receive tampering, but the validation flow
// (`validate_handoff`) is verify-and-consume (no stored cert is reused), so the
// analogous P0 against `HeldToken` does not apply here directly. Still, callers
// that *store* a verified `HandoffCertificate` for later authority decisions
// would need durable-binding semantics — flag for review if such a callsite is
// introduced.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HandoffCertificate {
    /// Who is granting the handoff (the current holder introducing the recipient).
    pub introducer: FederationId,
    /// Ed25519 signature by the introducer over the certificate's signing message.
    pub introducer_signature: Signature,

    /// The target federation hosting the capability.
    pub target_federation: FederationId,
    /// The cell on the target federation being handed off.
    pub target_cell: CellId,

    /// The recipient's Ed25519 public key (who is receiving the handoff).
    pub recipient_pk: [u8; 32],

    /// What authority is being delegated.
    pub permissions: AuthRequired,
    /// Optional effect mask restricting which effects the recipient can trigger.
    pub allowed_effects: Option<EffectMask>,

    /// Optional expiration expressed as a federation block height.
    pub expires_at: Option<u64>,
    /// Maximum number of times this certificate can be presented.
    pub max_uses: Option<u32>,
    /// Random nonce for replay prevention.
    pub nonce: [u8; 32],

    /// The swiss number the recipient should present to the target.
    /// Pre-registered by the introducer with the target's `SwissTable`.
    pub swiss: [u8; 32],
}

impl HandoffCertificate {
    /// Create a handoff certificate (called by the introducer).
    ///
    /// The introducer must have already registered a swiss entry at the target
    /// federation (via `SwissTable::export_with_options` or similar). The `swiss`
    /// parameter is the number registered at the target.
    pub fn create(
        introducer_key: &SigningKey,
        introducer_federation: FederationId,
        target_federation: FederationId,
        target_cell: CellId,
        recipient_pk: [u8; 32],
        permissions: AuthRequired,
        allowed_effects: Option<EffectMask>,
        expires_at: Option<u64>,
        max_uses: Option<u32>,
        swiss: [u8; 32],
    ) -> Self {
        let mut nonce = [0u8; 32];
        getrandom::fill(&mut nonce).expect("getrandom failed");

        // Build the certificate without signature first
        let mut cert = HandoffCertificate {
            introducer: introducer_federation,
            introducer_signature: Signature([0u8; 64]),
            target_federation,
            target_cell,
            recipient_pk,
            permissions,
            allowed_effects,
            expires_at,
            max_uses,
            nonce,
            swiss,
        };

        // Sign and fill in the signature
        let message = cert.signing_message();
        cert.introducer_signature = sign(introducer_key, &message);

        cert
    }

    /// Compute the canonical message that the introducer signs.
    ///
    /// Includes all fields except the signature itself, domain-separated
    /// to prevent cross-protocol confusion.
    pub fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"dregg-handoff-cert-v1");
        msg.extend_from_slice(&self.introducer.0);
        msg.extend_from_slice(&self.target_federation.0);
        msg.extend_from_slice(&self.target_cell.0);
        msg.extend_from_slice(&self.recipient_pk);
        // Encode permissions as a tag byte. For Custom, the tag byte is
        // followed by the 32-byte vk_hash inline, so that two
        // handoff certificates differing only in their app-defined auth
        // mode produce distinct signing messages (and thus distinct
        // signatures — a Custom { A } cert cannot be replayed as Custom { B }).
        msg.push(match &self.permissions {
            AuthRequired::None => 0,
            AuthRequired::Signature => 1,
            AuthRequired::Proof => 2,
            AuthRequired::Either => 3,
            AuthRequired::Impossible => 4,
            AuthRequired::Custom { .. } => 5,
        });
        if let AuthRequired::Custom { vk_hash } = &self.permissions {
            msg.extend_from_slice(vk_hash);
        }
        // Encode allowed_effects
        match self.allowed_effects {
            Some(mask) => {
                msg.push(0x01);
                msg.extend_from_slice(&mask.to_le_bytes());
            }
            None => {
                msg.push(0x00);
            }
        }
        // Encode expires_at
        match self.expires_at {
            Some(h) => {
                msg.push(0x01);
                msg.extend_from_slice(&h.to_le_bytes());
            }
            None => {
                msg.push(0x00);
            }
        }
        // Encode max_uses
        match self.max_uses {
            Some(n) => {
                msg.push(0x01);
                msg.extend_from_slice(&n.to_le_bytes());
            }
            None => {
                msg.push(0x00);
            }
        }
        msg.extend_from_slice(&self.nonce);
        msg.extend_from_slice(&self.swiss);
        msg
    }

    /// Verify the introducer's signature on this certificate.
    ///
    /// Requires knowing the introducer's public key (derived from their
    /// federation identity or looked up from a directory).
    pub fn verify_signature(&self, introducer_pk: &PublicKey) -> bool {
        let message = self.signing_message();
        introducer_pk.verify(&message, &self.introducer_signature)
    }

    /// Check if the certificate is still valid (not expired, not exhausted).
    ///
    /// Note: use-count checking requires external state (a nonce registry);
    /// this only checks the expiration.
    pub fn is_valid(&self, current_height: u64) -> bool {
        if let Some(exp) = self.expires_at
            && current_height > exp
        {
            return false;
        }
        true
    }

    /// Serialize for out-of-band transport (QR code, file, BLE).
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("handoff certificate serialization failed")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, HandoffError> {
        postcard::from_bytes(bytes).map_err(|e| HandoffError::DeserializationFailed(e.to_string()))
    }

    /// Encode as a compact string for URLs and QR codes.
    ///
    /// Format: `dregg-handoff:<base58-encoded-bytes>`
    pub fn to_compact_string(&self) -> String {
        let bytes = self.to_bytes();
        format!("dregg-handoff:{}", bs58::encode(&bytes).into_string())
    }

    /// Decode from a compact string.
    pub fn from_compact_string(s: &str) -> Result<Self, HandoffError> {
        let rest = s.strip_prefix("dregg-handoff:").ok_or_else(|| {
            HandoffError::DeserializationFailed("missing dregg-handoff: prefix".into())
        })?;

        let bytes = bs58::decode(rest)
            .into_vec()
            .map_err(|e| HandoffError::DeserializationFailed(format!("base58 decode: {e}")))?;

        Self::from_bytes(&bytes)
    }
}

// =============================================================================
// HandoffPresentation
// =============================================================================

/// A presentation of a handoff certificate to the target federation.
///
/// The recipient signs the certificate's nonce to prove they are the named
/// recipient (not someone who intercepted the certificate in transit).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HandoffPresentation {
    /// The handoff certificate being presented.
    pub certificate: HandoffCertificate,
    /// Ed25519 signature by the recipient, proving they own the recipient_pk.
    /// Signs the presentation message (domain-separated with the nonce).
    pub recipient_signature: Signature,
}

impl HandoffPresentation {
    /// Create a presentation (called by the recipient).
    ///
    /// The recipient signs a message binding themselves to this specific certificate,
    /// proving they own the `recipient_pk` named in the certificate.
    pub fn create(certificate: HandoffCertificate, recipient_key: &SigningKey) -> Self {
        let message = Self::presentation_message(&certificate);
        let recipient_signature = sign(recipient_key, &message);
        HandoffPresentation {
            certificate,
            recipient_signature,
        }
    }

    /// The message the recipient signs to prove identity.
    ///
    /// Domain-separated and includes the nonce to prevent cross-certificate replay.
    pub fn presentation_message(cert: &HandoffCertificate) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"dregg-handoff-present-v1");
        msg.extend_from_slice(&cert.nonce);
        msg.extend_from_slice(&cert.target_cell.0);
        msg.extend_from_slice(&cert.target_federation.0);
        msg
    }

    /// Verify the recipient's signature on this presentation.
    pub fn verify_recipient_signature(&self) -> bool {
        let pk = PublicKey(self.certificate.recipient_pk);
        let message = Self::presentation_message(&self.certificate);
        pk.verify(&message, &self.recipient_signature)
    }
}

// =============================================================================
// Hybrid post-quantum halves (ed25519 ∧ ML-DSA-65)
// =============================================================================
//
// A quantum adversary who breaks ed25519 discrete-log can forge BOTH the
// introducer's and the recipient's classical handoff signatures — i.e. forge a
// cross-node capability/authority transfer out of thin air. To close this we
// bind a SECOND, module-lattice signature (ML-DSA-65, FIPS 204) onto the SAME
// canonical handoff messages. A hybrid handoff validates only when the ed25519
// AND the ML-DSA halves both check, so forging requires breaking ed25519 AND
// ML-SIS/ML-LWE simultaneously.
//
// ENROLL + PIN (the whole point). The ML-DSA public key is NOT self-carried in
// the handoff — that would give ZERO post-quantum security (a quantum adversary
// forges the ed25519 half over identity P, generates its OWN ML-DSA keypair, and
// signs the PQ half under it). Instead:
//   * The INTRODUCER's ML-DSA key is PINNED to the identity's ENROLLED key,
//     which `validate_handoff_hybrid` takes as a parameter (the caller supplies
//     the introducer's enrolled ML-DSA public key exactly as it already supplies
//     the introducer's enrolled ed25519 `PublicKey`). The verifier RECOMPUTES the
//     signed message using the enrolled key; a signature under any other key fails.
//   * The RECIPIENT's ML-DSA key is PINNED into the certificate by the
//     introducer: `recipient_ml_dsa_pk` is covered by the introducer's ML-DSA
//     signature, so a quantum adversary cannot substitute their own without
//     forging the (lattice-hard) introducer PQ half.
//
// The ML-DSA key is derived DETERMINISTICALLY from the same 32-byte ed25519 seed
// the classical identity uses (`ML-DSA.KeyGen(ξ = seed)`), mirroring
// `turn::pq::MlDsaTurnKey::from_ed25519_seed` and `federation::frost` — so a node
// built from one mnemonic agrees on both keys with no separate ceremony.

mod hybrid_pq {
    use fips204::ml_dsa_65;
    use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};

    /// Domain-separation context for the ML-DSA half of a HYBRID *handoff*
    /// signature (FIPS 204 `ctx`). Distinct from the turn-path (`dregg-hybrid-turn-v1`)
    /// and consensus-quorum contexts so a handoff PQ signature can never be
    /// replayed as a turn or quorum half, and vice versa.
    pub const HANDOFF_PQ_CTX: &[u8] = b"dregg-captp-handoff-hybrid-v1";

    /// Serialized length of an ML-DSA-65 public key (FIPS 204).
    pub const ML_DSA_PK_LEN: usize = ml_dsa_65::PK_LEN;

    /// The PQ half of a hybrid identity: an ML-DSA-65 signing key plus its
    /// serialized public key, derived from the SAME seed as the ed25519 identity.
    pub struct MlDsaHandoffKey {
        secret: ml_dsa_65::PrivateKey,
        public_bytes: [u8; ml_dsa_65::PK_LEN],
    }

    impl MlDsaHandoffKey {
        /// Derive the ML-DSA-65 keypair deterministically from a 32-byte ed25519
        /// seed (`ML-DSA.KeyGen(ξ = seed)`).
        pub fn from_ed25519_seed(seed: &[u8; 32]) -> Self {
            let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(seed);
            Self {
                secret: sk,
                public_bytes: pk.into_bytes(),
            }
        }

        /// The serialized ML-DSA-65 public key.
        pub fn public_bytes(&self) -> Vec<u8> {
            self.public_bytes.to_vec()
        }

        /// Sign `message` under [`HANDOFF_PQ_CTX`] (hedged from OS entropy).
        pub fn sign(&self, message: &[u8]) -> Vec<u8> {
            self.secret
                .try_sign(message, HANDOFF_PQ_CTX)
                .expect("ml-dsa handoff sign failed (RNG)")
                .to_vec()
        }
    }

    /// Verify an ML-DSA-65 signature over `message` under [`HANDOFF_PQ_CTX`].
    /// Returns `false` — never a panic — on a wrong-length / undecodable key or
    /// signature, or a failed check. This is the fail-CLOSED primitive: a
    /// missing or present-but-invalid PQ half must reject the whole hybrid handoff.
    pub fn ml_dsa_verify(public_bytes: &[u8], message: &[u8], sig_bytes: &[u8]) -> bool {
        let Ok(pk_arr) = <[u8; ml_dsa_65::PK_LEN]>::try_from(public_bytes) else {
            return false;
        };
        let Ok(sig) = <[u8; ml_dsa_65::SIG_LEN]>::try_from(sig_bytes) else {
            return false;
        };
        let Ok(vk) = ml_dsa_65::PublicKey::try_from_bytes(pk_arr) else {
            return false;
        };
        vk.verify(message, &sig, HANDOFF_PQ_CTX)
    }
}

pub use hybrid_pq::{ML_DSA_PK_LEN, MlDsaHandoffKey};

/// A HYBRID handoff certificate: the classical [`HandoffCertificate`] plus the
/// post-quantum (ML-DSA-65) half. Travels out-of-band exactly like the classical
/// certificate (postcard / base58 / QR). See the module comment for the enroll +
/// pin discipline.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HybridHandoffCertificate {
    /// The classical certificate (carries the ed25519 introducer signature).
    pub base: HandoffCertificate,
    /// The recipient's ML-DSA-65 public key, PINNED here by the introducer:
    /// covered by `introducer_ml_dsa_sig`, so a quantum adversary cannot swap in
    /// their own recipient PQ key without forging the (lattice-hard) introducer
    /// PQ half.
    pub recipient_ml_dsa_pk: Vec<u8>,
    /// The introducer's ML-DSA-65 signature over [`HybridHandoffCertificate::hybrid_signing_message`].
    /// The introducer's ML-DSA *public* key is deliberately NOT carried here — the
    /// verifier recomputes the message with the ENROLLED introducer key, so a
    /// signature made under any other key fails to verify.
    pub introducer_ml_dsa_sig: Vec<u8>,
}

impl HybridHandoffCertificate {
    /// Create a hybrid handoff certificate (called by the introducer).
    ///
    /// `recipient_ml_dsa_pk` is the recipient's enrolled ML-DSA-65 public key
    /// (the introducer knows/vouches for the recipient and pins it into the
    /// cert). The introducer's own ML-DSA key is derived from `introducer_key`'s
    /// ed25519 seed, so no separate PQ key material is needed.
    #[allow(clippy::too_many_arguments)]
    pub fn create(
        introducer_key: &SigningKey,
        introducer_federation: FederationId,
        target_federation: FederationId,
        target_cell: CellId,
        recipient_pk: [u8; 32],
        permissions: AuthRequired,
        allowed_effects: Option<EffectMask>,
        expires_at: Option<u64>,
        max_uses: Option<u32>,
        swiss: [u8; 32],
        recipient_ml_dsa_pk: Vec<u8>,
    ) -> Self {
        let base = HandoffCertificate::create(
            introducer_key,
            introducer_federation,
            target_federation,
            target_cell,
            recipient_pk,
            permissions,
            allowed_effects,
            expires_at,
            max_uses,
            swiss,
        );
        let intro_pq = MlDsaHandoffKey::from_ed25519_seed(&introducer_key.to_bytes());
        let intro_pq_pk = intro_pq.public_bytes();
        let message = Self::hybrid_signing_message(&base, &intro_pq_pk, &recipient_ml_dsa_pk);
        let introducer_ml_dsa_sig = intro_pq.sign(&message);
        HybridHandoffCertificate {
            base,
            recipient_ml_dsa_pk,
            introducer_ml_dsa_sig,
        }
    }

    /// The canonical message the introducer signs with ML-DSA. Binds the entire
    /// classical signing message PLUS both hybrid public keys (the introducer's
    /// own and the pinned recipient's), each length-prefixed and domain-separated.
    /// Signer passes its own ML-DSA public key; the verifier passes the ENROLLED
    /// key — mismatch ⇒ different message ⇒ signature fails (this IS the pin).
    pub fn hybrid_signing_message(
        base: &HandoffCertificate,
        introducer_ml_dsa_pk: &[u8],
        recipient_ml_dsa_pk: &[u8],
    ) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"dregg-handoff-cert-hybrid-v1");
        let bm = base.signing_message();
        msg.extend_from_slice(&(bm.len() as u64).to_le_bytes());
        msg.extend_from_slice(&bm);
        msg.extend_from_slice(&(introducer_ml_dsa_pk.len() as u64).to_le_bytes());
        msg.extend_from_slice(introducer_ml_dsa_pk);
        msg.extend_from_slice(&(recipient_ml_dsa_pk.len() as u64).to_le_bytes());
        msg.extend_from_slice(recipient_ml_dsa_pk);
        msg
    }

    /// The canonical message the recipient signs with ML-DSA to present. Binds
    /// the classical presentation message plus the pinned recipient ML-DSA key.
    pub fn hybrid_presentation_message(
        base: &HandoffCertificate,
        recipient_ml_dsa_pk: &[u8],
    ) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"dregg-handoff-present-hybrid-v1");
        let pm = HandoffPresentation::presentation_message(base);
        msg.extend_from_slice(&(pm.len() as u64).to_le_bytes());
        msg.extend_from_slice(&pm);
        msg.extend_from_slice(&(recipient_ml_dsa_pk.len() as u64).to_le_bytes());
        msg.extend_from_slice(recipient_ml_dsa_pk);
        msg
    }

    /// Serialize for out-of-band transport.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("hybrid handoff certificate serialization failed")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, HandoffError> {
        postcard::from_bytes(bytes).map_err(|e| HandoffError::DeserializationFailed(e.to_string()))
    }
}

/// A HYBRID presentation of a [`HybridHandoffCertificate`]: the recipient proves
/// ownership of BOTH the ed25519 `recipient_pk` and the introducer-pinned
/// `recipient_ml_dsa_pk`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HybridHandoffPresentation {
    /// The hybrid certificate being presented.
    pub certificate: HybridHandoffCertificate,
    /// Ed25519 signature by the recipient over the classical presentation message.
    pub recipient_signature: Signature,
    /// ML-DSA-65 signature by the recipient over
    /// [`HybridHandoffCertificate::hybrid_presentation_message`], under the
    /// introducer-pinned `recipient_ml_dsa_pk`.
    pub recipient_ml_dsa_sig: Vec<u8>,
}

impl HybridHandoffPresentation {
    /// Create a hybrid presentation (called by the recipient). The recipient's
    /// ML-DSA key is derived from `recipient_key`'s ed25519 seed — it must match
    /// the `recipient_ml_dsa_pk` the introducer pinned in the certificate, or the
    /// PQ half will be rejected by the target.
    pub fn create(certificate: HybridHandoffCertificate, recipient_key: &SigningKey) -> Self {
        let base = &certificate.base;
        let recipient_signature = sign(
            recipient_key,
            &HandoffPresentation::presentation_message(base),
        );
        let recip_pq = MlDsaHandoffKey::from_ed25519_seed(&recipient_key.to_bytes());
        let message = HybridHandoffCertificate::hybrid_presentation_message(
            base,
            &certificate.recipient_ml_dsa_pk,
        );
        let recipient_ml_dsa_sig = recip_pq.sign(&message);
        HybridHandoffPresentation {
            certificate,
            recipient_signature,
            recipient_ml_dsa_sig,
        }
    }

    /// Serialize for out-of-band transport.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("hybrid handoff presentation serialization failed")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, HandoffError> {
        postcard::from_bytes(bytes).map_err(|e| HandoffError::DeserializationFailed(e.to_string()))
    }
}

// =============================================================================
// Handoff Validation (target side)
// =============================================================================

/// The result of a successful handoff validation at the target federation.
#[derive(Clone, Debug)]
pub struct HandoffAcceptance {
    /// A routing token the recipient can use for subsequent access.
    pub routing_token: [u8; 32],
    /// The cell they now have access to.
    pub cell_id: CellId,
    /// The permissions they were granted.
    pub permissions: AuthRequired,
    /// The effect mask, if any.
    pub allowed_effects: Option<EffectMask>,
}

/// Validate and accept/reject a handoff presentation at the target federation.
///
/// Performs the following checks:
/// 1. Verify introducer signature on certificate
/// 2. Verify recipient signature on presentation
/// 3. Check introducer is a known/trusted federation
/// 4. Check certificate is not expired
/// 5. Check swiss number is valid in our swiss table (and enliven it)
/// 6. **Non-amplification (Granovetter):** check the granted permissions and
///    effect mask are an *attenuation* (subset) of what the introducer actually
///    holds — the swiss entry the introducer registered at this target. The
///    handoff certificate's `permissions`/`allowed_effects` are introducer-
///    asserted and could claim arbitrary authority; the swiss entry is the
///    target federation's own authoritative record of what it granted the
///    introducer for this cell. A handoff must not confer MORE than that.
///
/// The held authority is read from the swiss entry returned by `enliven`
/// (`SwissEntry::permissions` / `SwissEntry::allowed_effects`), NOT from the
/// certificate — so an attacker who forges/inflates the certificate's
/// permissions cannot escalate beyond the introducer's registered rights.
/// This enforces the Lean spec `Exec/CapTP.lean::handoff_non_amplifying`
/// (`cert.granted.rights ≤ cert.held.rights`), where `held` is the swiss entry.
///
/// On success, enlivens the swiss entry and returns a `HandoffAcceptance` with
/// a routing token for ongoing access. The returned `permissions`/
/// `allowed_effects` are the certificate's granted (attenuated) authority.
/// The wire tag of an `AuthRequired` for the verified Lean handoff gate (mirrors
/// `cell/src/permissions.rs::AuthRequired` constructor order, which the Lean `AuthReq` shares):
/// `0=None 1=Signature 2=Proof 3=Either 4=Impossible 5+(vk_hash digest)=Custom`. The `Custom`
/// vk_hash is folded to a small `u64` (the Lean rule compares Custom only for tag equality, so any
/// injective fold of the 32 bytes preserves the verdict; we use the first 8 bytes as a `u64`).
fn auth_required_tag(a: &AuthRequired) -> u64 {
    match a {
        AuthRequired::None => 0,
        AuthRequired::Signature => 1,
        AuthRequired::Proof => 2,
        AuthRequired::Either => 3,
        AuthRequired::Impossible => 4,
        AuthRequired::Custom { vk_hash } => {
            let mut b = [0u8; 8];
            b.copy_from_slice(&vk_hash[..8]);
            5u64.saturating_add(u64::from_le_bytes(b))
        }
    }
}

/// The effect-mask wire field for the verified Lean handoff gate: `None` (unrestricted) ⇒ `"x"`,
/// a concrete mask ⇒ its decimal value.
fn effect_mask_field(m: Option<EffectMask>) -> String {
    match m {
        None => "x".to_string(),
        Some(mask) => mask.to_string(),
    }
}

/// Decide the §6 non-amplification verdict via the VERIFIED Lean export
/// `dregg_captp_validate_handoff` (= `Dregg2.Exec.CapTPConcrete.handoffNonAmplifyingC`). Returns
/// `Some(true)` (non-amplifying) / `Some(false)` (amplifies) when the gate ran, or `None` when the
/// verified gate is unavailable (feature off / archive lacks the export) so the caller falls back to
/// the Rust lattice. Routes through the [`crate::verified_gate`] seam; returns `None` when no
/// verified gate is registered (every FFI-free target / archive lacks the export) so the crate has
/// no hard dependency on the Lean archive.
fn verified_non_amplifying(
    granted_perm: &AuthRequired,
    held_perm: &AuthRequired,
    granted_eff: Option<EffectMask>,
    held_eff: Option<EffectMask>,
) -> Option<bool> {
    let gate = crate::verified_gate::gate()?;
    if !gate.distributed_exports_available() {
        return None;
    }
    let wire = format!(
        "h={};g={};he={};ge={}",
        auth_required_tag(held_perm),
        auth_required_tag(granted_perm),
        effect_mask_field(held_eff),
        effect_mask_field(granted_eff),
    );
    // FFI / wire error ⇒ fall back to the Rust lattice (never break the live handoff path).
    gate.handoff_non_amplifying(&wire)
}

pub fn validate_handoff(
    presentation: &HandoffPresentation,
    introducer_pk: &PublicKey,
    swiss_table: &mut SwissTable,
    known_federations: &[FederationId],
    current_height: u64,
) -> Result<HandoffAcceptance, HandoffError> {
    let cert = &presentation.certificate;

    // 1. Verify introducer signature
    if !cert.verify_signature(introducer_pk) {
        return Err(HandoffError::InvalidIntroducerSignature);
    }

    // 2. Verify recipient signature (proves the presenter owns recipient_pk)
    if !presentation.verify_recipient_signature() {
        return Err(HandoffError::InvalidRecipientSignature);
    }

    // 3. Check the introducer is a known federation
    if !known_federations.contains(&cert.introducer) {
        return Err(HandoffError::UntrustedIntroducer);
    }

    // 4. Check expiration
    if !cert.is_valid(current_height) {
        return Err(HandoffError::Expired);
    }

    // 5. Validate the swiss number READ-ONLY (F-2 fix). The returned entry IS
    //    the introducer's HELD authority on the target cell — the rights the
    //    target federation recorded when the introducer registered this swiss
    //    number. This is the authoritative `held` for the non-amplification
    //    check below (the certificate's own `permissions` are introducer-
    //    asserted and must not be trusted as an upper bound on themselves).
    //
    //    CRITICAL ORDERING (F-2): we use `check` (a NON-mutating validation),
    //    NOT `enliven` (which bumps `use_count`). The use-consuming `enliven`
    //    happens ONLY on the success path, AFTER every rejecting check (target
    //    binding §5b, non-amplification §6) has passed. Previously `enliven` ran
    //    here — so an attacker presenting an amplifying (rejected-for-
    //    amplification) cert against a known swiss number still burned a use of
    //    the introducer's budget, exhausting a one-shot handoff and griefing the
    //    legitimate recipient (`finding_amplifying_handoff_consumes_a_use_on_rejection`).
    //    Moving the mutation to the success path closes that DoS: a rejected
    //    presentation now leaves `use_count` untouched.
    let held = swiss_table
        .check(&cert.swiss, current_height)
        .map_err(|e| match e {
            crate::sturdy::EnlivenError::NotFound => HandoffError::SwissNotFound,
            crate::sturdy::EnlivenError::Expired => HandoffError::Expired,
            crate::sturdy::EnlivenError::ExhaustedUses => HandoffError::MaxUsesExhausted,
        })?;

    // 5b. Target binding (Lean `handoff_same_target`): the cell the recipient is
    //     introduced to MUST be the cell the swiss entry actually points to. The
    //     certificate's `target_cell` is introducer-asserted; the swiss entry's
    //     `cell_id` is the target federation's authoritative record. Without this,
    //     a forged cert could name an arbitrary `target_cell` (and we'd hand the
    //     recipient a routing token for it), because the §6 non-amplification check
    //     compares RIGHTS, not target. Bind them: granted.target == held.target.
    if cert.target_cell != held.cell_id {
        return Err(HandoffError::TargetMismatch);
    }

    // 6. Non-amplification (Granovetter): granted ⊆ held — on BOTH the permission lattice and the
    //    effect-mask facet.
    //
    //    STRONG-FORM SWAP: on every native build (Lean unconditional), this verdict is decided BY the VERIFIED
    //    Lean export `dregg_captp_validate_handoff` (= `Dregg2.Exec.CapTPConcrete.handoffNonAmplifyingC`,
    //    proved equal to the export by `captp_validate_handoff_eq`); the Rust lattice below is then the
    //    DIFFERENTIAL sibling. Without the feature (or when the archive lacks the export) the Rust
    //    lattice decides. Either way the decision is fail-CLOSED on amplification.
    //
    //    a) Permission lattice: the granted `AuthRequired` must be narrower-than-or-equal to the held
    //       `AuthRequired` (Impossible ≤ Proof/Signature ≤ Either ≤ None; Custom comparable only to an
    //       identical Custom). b) Effect facet mask: a `None` held mask is unrestricted (any granted
    //       mask attenuates it); a concrete held mask requires the granted mask be a bitwise subset.
    let rust_non_amplifying = cert.permissions.is_narrower_or_equal(&held.permissions)
        && match (cert.allowed_effects, held.allowed_effects) {
            (_, None) => true,        // held unrestricted: granted always attenuates
            (None, Some(_)) => false, // held restricted, granted unrestricted: amplify
            (Some(granted_mask), Some(held_mask)) => {
                dregg_cell::is_facet_attenuation(held_mask, granted_mask)
            }
        };
    // The AUTHORITATIVE verdict: the verified Lean gate when linked, else the Rust lattice.
    let non_amplifying = verified_non_amplifying(
        &cert.permissions,
        &held.permissions,
        cert.allowed_effects,
        held.allowed_effects,
    )
    .unwrap_or(rust_non_amplifying);
    if !non_amplifying {
        return Err(HandoffError::Amplification);
    }

    // 6c. REPLAY (CAPTP-DEEP-1): the certificate's 32-byte `nonce` may be
    //     consumed at most once at this target, INDEPENDENTLY of the swiss
    //     entry's `max_uses`. Without this, a durable (unlimited-use) swiss entry
    //     let one captured certificate be re-presented forever (the `nonce` field
    //     and the `ReplayDetected` variant were decorative). We consult the
    //     target's seen-nonce registry BEFORE consuming a use, so a replay neither
    //     advances the swiss budget nor mints a second routing token. The nonce is
    //     registered on the success path below (after enliven), so a presentation
    //     that is rejected for a LATER reason cannot poison a still-unused nonce.
    if swiss_table.handoff_nonce_seen(&cert.nonce) {
        return Err(HandoffError::ReplayDetected);
    }

    // 7. SUCCESS PATH — only now consume a use (F-2). Every rejecting check above
    //    ran against the read-only `check`; the presentation is fully validated,
    //    so enliven (bumping `use_count`) is correct here. Because all rejecting
    //    branches returned before this point, a rejected presentation never
    //    advances the swiss budget. We re-run the swiss admission inside `enliven`
    //    (it re-checks expiry/use-limit), which under single-threaded validation
    //    is the same decision `check` just made — but doing it here keeps the
    //    use-count bump atomic with acceptance.
    swiss_table
        .enliven(&cert.swiss, current_height)
        .map_err(|e| match e {
            crate::sturdy::EnlivenError::NotFound => HandoffError::SwissNotFound,
            crate::sturdy::EnlivenError::Expired => HandoffError::Expired,
            crate::sturdy::EnlivenError::ExhaustedUses => HandoffError::MaxUsesExhausted,
        })?;

    // 7b. CONSUME the nonce: this accepted presentation has now used the
    //     certificate. Any subsequent presentation of the same nonce is a replay
    //     and is rejected at §6c above. `register_handoff_nonce` returns false if
    //     it was somehow already present (it cannot be here — §6c just checked),
    //     so we ignore the bool; the insert is idempotent and fail-closed.
    let _ = swiss_table.register_handoff_nonce(cert.nonce);

    // Generate a routing token for the recipient
    let mut routing_token = [0u8; 32];
    getrandom::fill(&mut routing_token).expect("getrandom failed");

    Ok(HandoffAcceptance {
        routing_token,
        cell_id: cert.target_cell,
        permissions: cert.permissions.clone(),
        allowed_effects: cert.allowed_effects,
    })
}

/// HYBRID validation: the same gate as [`validate_handoff`], but requiring BOTH
/// the ed25519 AND the ML-DSA-65 halves of the introducer's and recipient's
/// signatures. Closes the post-quantum capability-handoff forgery:
///
/// * `introducer_ml_dsa_pk` — the introducer identity's ENROLLED ML-DSA-65 public
///   key (supplied by the caller from its identity roster, exactly as
///   `introducer_pk` is). The introducer's PQ half is verified UNDER this enrolled
///   key (the signed message is recomputed with it), so a signature made under any
///   other — e.g. a quantum adversary's fresh — ML-DSA key is rejected. NEVER
///   trusts a self-carried PQ key.
/// * the recipient's PQ half is verified under the introducer-PINNED
///   `certificate.recipient_ml_dsa_pk` (authenticated by the introducer PQ half).
///
/// Fail-CLOSED: a missing, malformed, or mis-keyed PQ half rejects. The PQ checks
/// are pure and run BEFORE any swiss-budget mutation (this fn then delegates the
/// swiss / non-amplification / target-binding / replay / enliven logic to
/// [`validate_handoff`], which uses a read-only `check` until the success path).
pub fn validate_handoff_hybrid(
    presentation: &HybridHandoffPresentation,
    introducer_pk: &PublicKey,
    introducer_ml_dsa_pk: &[u8],
    swiss_table: &mut SwissTable,
    known_federations: &[FederationId],
    current_height: u64,
) -> Result<HandoffAcceptance, HandoffError> {
    let hcert = &presentation.certificate;
    let base_cert = &hcert.base;

    // 1. Introducer classical (ed25519) half.
    if !base_cert.verify_signature(introducer_pk) {
        return Err(HandoffError::InvalidIntroducerSignature);
    }

    // 2. Introducer post-quantum (ML-DSA-65) half — PINNED to the ENROLLED key.
    //    The message is recomputed with `introducer_ml_dsa_pk`, so a signature
    //    under any other ML-DSA key (the quantum-forgery case) fails.
    let intro_msg = HybridHandoffCertificate::hybrid_signing_message(
        base_cert,
        introducer_ml_dsa_pk,
        &hcert.recipient_ml_dsa_pk,
    );
    if !hybrid_pq::ml_dsa_verify(
        introducer_ml_dsa_pk,
        &intro_msg,
        &hcert.introducer_ml_dsa_sig,
    ) {
        return Err(HandoffError::InvalidIntroducerPqSignature);
    }

    // 3. Recipient classical (ed25519) half.
    let recip_pk = PublicKey(base_cert.recipient_pk);
    let present_msg = HandoffPresentation::presentation_message(base_cert);
    if !recip_pk.verify(&present_msg, &presentation.recipient_signature) {
        return Err(HandoffError::InvalidRecipientSignature);
    }

    // 4. Recipient post-quantum half — verified UNDER the introducer-pinned
    //    `recipient_ml_dsa_pk` (authenticated by step 2). Fail-closed.
    let recip_msg = HybridHandoffCertificate::hybrid_presentation_message(
        base_cert,
        &hcert.recipient_ml_dsa_pk,
    );
    if !hybrid_pq::ml_dsa_verify(
        &hcert.recipient_ml_dsa_pk,
        &recip_msg,
        &presentation.recipient_ml_dsa_sig,
    ) {
        return Err(HandoffError::InvalidRecipientPqSignature);
    }

    // 5+. Delegate the swiss / non-amplification / target-binding / replay /
    //     enliven logic (which re-checks the ed25519 halves, harmless).
    let base_pres = HandoffPresentation {
        certificate: base_cert.clone(),
        recipient_signature: presentation.recipient_signature,
    };
    validate_handoff(
        &base_pres,
        introducer_pk,
        swiss_table,
        known_federations,
        current_height,
    )
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::generate_keypair;

    fn setup_introducer() -> (SigningKey, PublicKey, FederationId) {
        let (sk, pk) = generate_keypair();
        let fed = FederationId(pk.0);
        (sk, pk, fed)
    }

    fn setup_recipient() -> (SigningKey, PublicKey) {
        generate_keypair()
    }

    /// Helper: create a full handoff scenario (introducer registers swiss, creates cert).
    fn full_handoff_setup() -> (
        HandoffCertificate,
        SigningKey,   // recipient key
        PublicKey,    // introducer pk
        FederationId, // introducer federation
        FederationId, // target federation
        SwissTable,   // target's swiss table (with the swiss pre-registered)
    ) {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // Introducer registers a swiss entry at the target
        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        // Introducer creates the handoff certificate
        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None, // no expiration
            None, // unlimited uses
            swiss,
        );

        (cert, recip_sk, intro_pk, intro_fed, target_fed, swiss_table)
    }

    #[test]
    fn create_and_verify_signature() {
        let (cert, _recip_sk, intro_pk, _intro_fed, _target_fed, _swiss_table) =
            full_handoff_setup();

        assert!(cert.verify_signature(&intro_pk));

        // Wrong key should fail
        let (_, wrong_pk) = generate_keypair();
        assert!(!cert.verify_signature(&wrong_pk));
    }

    #[test]
    fn present_to_target_success() {
        let (cert, recip_sk, intro_pk, intro_fed, _target_fed, mut swiss_table) =
            full_handoff_setup();

        // Recipient creates presentation
        let presentation = HandoffPresentation::create(cert, &recip_sk);

        // Target validates
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);

        let acceptance = result.unwrap();
        assert_eq!(acceptance.cell_id, CellId([0xEE; 32]));
        assert_eq!(acceptance.permissions, AuthRequired::Signature);
    }

    #[test]
    fn expired_certificate_rejected() {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, Some(200));

        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            Some(200), // expires at height 200
            None,
            swiss,
        );

        let presentation = HandoffPresentation::create(cert, &recip_sk);

        let known = vec![intro_fed];
        // Present at height 201 (past expiration)
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 201);

        assert_eq!(result.unwrap_err(), HandoffError::Expired);
    }

    #[test]
    fn wrong_recipient_rejected() {
        let (cert, _recip_sk, intro_pk, intro_fed, _target_fed, mut swiss_table) =
            full_handoff_setup();

        // An impostor tries to present (different key than recipient_pk)
        let (impostor_sk, _impostor_pk) = generate_keypair();
        let presentation = HandoffPresentation::create(cert, &impostor_sk);

        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);

        assert_eq!(result.unwrap_err(), HandoffError::InvalidRecipientSignature);
    }

    #[test]
    fn untrusted_introducer_rejected() {
        let (cert, recip_sk, intro_pk, _intro_fed, _target_fed, mut swiss_table) =
            full_handoff_setup();

        let presentation = HandoffPresentation::create(cert, &recip_sk);

        // Empty known federations list (introducer not trusted)
        let known: Vec<FederationId> = vec![];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);

        assert_eq!(result.unwrap_err(), HandoffError::UntrustedIntroducer);
    }

    #[test]
    fn max_uses_exhausted() {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let mut swiss_table = SwissTable::new();
        // Swiss entry with max_uses = 1
        let swiss = swiss_table.export_with_options(
            target_cell,
            AuthRequired::Signature,
            100,
            None,
            None,
            Some(1), // one-time use
        );

        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            Some(1),
            swiss,
        );

        let known = vec![intro_fed];

        // First presentation succeeds.
        let presentation1 = HandoffPresentation::create(cert, &recip_sk);
        let result = validate_handoff(&presentation1, &intro_pk, &mut swiss_table, &known, 150);
        assert!(result.is_ok());

        // Second presentation with a DISTINCT certificate (fresh nonce, so it is
        // NOT caught by replay-detection) against the SAME one-shot swiss entry:
        // it fails because the swiss `max_uses` budget is exhausted. (Replaying the
        // identical cert would instead be caught earlier as `ReplayDetected`; this
        // test isolates the swiss-exhaustion path with a fresh nonce.)
        let cert2 = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            Some(1),
            swiss,
        );
        let presentation2 = HandoffPresentation::create(cert2, &recip_sk);
        let result = validate_handoff(&presentation2, &intro_pk, &mut swiss_table, &known, 151);
        assert_eq!(result.unwrap_err(), HandoffError::MaxUsesExhausted);
    }

    #[test]
    fn compact_string_roundtrip() {
        let (cert, _recip_sk, _intro_pk, _intro_fed, _target_fed, _swiss_table) =
            full_handoff_setup();

        let compact = cert.to_compact_string();
        assert!(compact.starts_with("dregg-handoff:"));

        let decoded = HandoffCertificate::from_compact_string(&compact).unwrap();
        assert_eq!(decoded.introducer, cert.introducer);
        assert_eq!(decoded.target_federation, cert.target_federation);
        assert_eq!(decoded.target_cell, cert.target_cell);
        assert_eq!(decoded.recipient_pk, cert.recipient_pk);
        assert_eq!(decoded.nonce, cert.nonce);
        assert_eq!(decoded.swiss, cert.swiss);
        assert_eq!(decoded.introducer_signature, cert.introducer_signature);
    }

    #[test]
    fn bytes_roundtrip() {
        let (cert, _recip_sk, _intro_pk, _intro_fed, _target_fed, _swiss_table) =
            full_handoff_setup();

        let bytes = cert.to_bytes();
        let decoded = HandoffCertificate::from_bytes(&bytes).unwrap();
        assert_eq!(decoded.nonce, cert.nonce);
        assert_eq!(decoded.swiss, cert.swiss);
    }

    #[test]
    fn invalid_compact_string_prefix() {
        let result = HandoffCertificate::from_compact_string("invalid:abc");
        assert!(matches!(
            result,
            Err(HandoffError::DeserializationFailed(_))
        ));
    }

    #[test]
    fn certificate_validity_check() {
        let (cert_no_expiry, _, _, _, _, _) = full_handoff_setup();

        // No expiry: always valid
        assert!(cert_no_expiry.is_valid(0));
        assert!(cert_no_expiry.is_valid(u64::MAX));

        // With expiry
        let (intro_sk, _intro_pk, intro_fed) = setup_introducer();
        let (_, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let cert_with_expiry = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            Some(500), // expires at height 500
            None,
            [0x42; 32],
        );

        assert!(cert_with_expiry.is_valid(499));
        assert!(cert_with_expiry.is_valid(500)); // at expiry height: still valid
        assert!(!cert_with_expiry.is_valid(501)); // past expiry: invalid
    }

    // ── Non-amplification (Granovetter: granted ≤ held) ─────────────────────
    //
    // These exercise the §6 check in `validate_handoff`. The HELD authority is
    // the swiss entry the introducer registered at the target (its `permissions`
    // / `allowed_effects`); the GRANTED authority is the certificate's
    // `permissions` / `allowed_effects`. The Lean spec
    // `Exec/CapTP.lean::handoff_non_amplifying` proves `granted ≤ held`; these
    // confirm the Rust validator enforces it.

    /// Helper: full handoff where held (swiss) and granted (cert) auth/effects
    /// are specified independently, so we can construct attenuating, equal, and
    /// amplifying scenarios.
    #[allow(clippy::too_many_arguments)]
    fn handoff_with_auth(
        held_perm: AuthRequired,
        held_effects: Option<EffectMask>,
        granted_perm: AuthRequired,
        granted_effects: Option<EffectMask>,
    ) -> (
        HandoffPresentation,
        PublicKey,    // introducer pk
        FederationId, // introducer federation
        SwissTable,   // target's swiss table (held entry registered)
    ) {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // Introducer registers the swiss entry recording what IT holds.
        let mut swiss_table = SwissTable::new();
        let swiss =
            swiss_table.export_with_options(target_cell, held_perm, 100, None, held_effects, None);

        // Introducer creates a certificate granting (possibly inflated) authority.
        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            granted_perm,
            granted_effects,
            None,
            None,
            swiss,
        );

        let presentation = HandoffPresentation::create(cert, &recip_sk);
        (presentation, intro_pk, intro_fed, swiss_table)
    }

    #[test]
    fn attenuating_handoff_passes() {
        // Held = Either; granted = Signature (strictly narrower). Must pass.
        let (presentation, intro_pk, intro_fed, mut swiss_table) =
            handoff_with_auth(AuthRequired::Either, None, AuthRequired::Signature, None);
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        let acceptance = result.expect("attenuating handoff must be accepted");
        assert_eq!(acceptance.permissions, AuthRequired::Signature);
    }

    #[test]
    fn equal_rights_handoff_passes() {
        // Held = Signature; granted = Signature (equal). Must pass.
        let (presentation, intro_pk, intro_fed, mut swiss_table) =
            handoff_with_auth(AuthRequired::Signature, None, AuthRequired::Signature, None);
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert!(result.is_ok(), "equal-rights handoff must be accepted");
    }

    #[test]
    fn amplifying_handoff_rejected() {
        // Held = Signature; granted = None (LOOSER requirement = MORE authority).
        // The introducer only holds a signature-gated cap but tries to gift an
        // unauthenticated (None) cap. This is amplification and must be rejected.
        let (presentation, intro_pk, intro_fed, mut swiss_table) =
            handoff_with_auth(AuthRequired::Signature, None, AuthRequired::None, None);
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::Amplification,
            "granting None over held Signature must be rejected as amplification"
        );
    }

    #[test]
    fn amplifying_handoff_from_impossible_rejected() {
        // Held = Impossible (the introducer holds NOTHING usable); granted =
        // Signature. The most extreme amplification: conjuring authority from a
        // locked cap. Must be rejected.
        let (presentation, intro_pk, intro_fed, mut swiss_table) = handoff_with_auth(
            AuthRequired::Impossible,
            None,
            AuthRequired::Signature,
            None,
        );
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(result.unwrap_err(), HandoffError::Amplification);
    }

    #[test]
    fn effect_mask_attenuating_handoff_passes() {
        use dregg_cell::{EFFECT_EMIT_EVENT, EFFECT_TRANSFER};
        // Held = {transfer, emit}; granted = {emit} (subset). Must pass.
        let held = Some(EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        let granted = Some(EFFECT_EMIT_EVENT);
        let (presentation, intro_pk, intro_fed, mut swiss_table) = handoff_with_auth(
            AuthRequired::Signature,
            held,
            AuthRequired::Signature,
            granted,
        );
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert!(
            result.is_ok(),
            "effect-mask subset handoff must be accepted"
        );
    }

    #[test]
    fn effect_mask_amplifying_handoff_rejected() {
        use dregg_cell::{EFFECT_EMIT_EVENT, EFFECT_TRANSFER};
        // Held = {emit}; granted = {transfer, emit} (superset — adds transfer).
        // Granting an effect bit the introducer doesn't hold is amplification.
        let held = Some(EFFECT_EMIT_EVENT);
        let granted = Some(EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        let (presentation, intro_pk, intro_fed, mut swiss_table) = handoff_with_auth(
            AuthRequired::Signature,
            held,
            AuthRequired::Signature,
            granted,
        );
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(result.unwrap_err(), HandoffError::Amplification);
    }

    #[test]
    fn effect_mask_unrestricted_grant_over_restricted_hold_rejected() {
        use dregg_cell::EFFECT_EMIT_EVENT;
        // Held = {emit} (restricted); granted = None (unrestricted = all effects).
        // Granting unrestricted authority over a faceted hold is amplification.
        let held = Some(EFFECT_EMIT_EVENT);
        let (presentation, intro_pk, intro_fed, mut swiss_table) =
            handoff_with_auth(AuthRequired::Signature, held, AuthRequired::Signature, None);
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(result.unwrap_err(), HandoffError::Amplification);
    }

    #[test]
    fn target_mismatch_rejected() {
        // The introducer registers a swiss entry for cell X, but mints a certificate
        // claiming a DIFFERENT target cell Y. A forged/redirected cert must NOT confer
        // access to Y off an entry registered for X (Lean `handoff_same_target`).
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let registered_cell = CellId([0x11; 32]); // X: what the swiss entry points to
        let claimed_cell = CellId([0x22; 32]); // Y: what the cert claims

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(registered_cell, AuthRequired::Signature, 100, None);

        // Cert names Y, not X.
        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            claimed_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            None,
            swiss,
        );
        let presentation = HandoffPresentation::create(cert, &recip_sk);
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::TargetMismatch,
            "a cert claiming a target cell other than the swiss entry's cell must be rejected"
        );
    }

    #[test]
    fn out_of_band_scenario() {
        // Simulates: create certificate offline, transport as string, present later
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // Step 1: Introducer registers swiss at target (online)
        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        // Step 2: Introducer creates cert and encodes to string (can be offline)
        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            None,
            swiss,
        );
        let compact = cert.to_compact_string();

        // Step 3: Time passes... certificate travels out-of-band (QR, email, etc.)

        // Step 4: Recipient decodes and presents (online, potentially much later)
        let decoded_cert = HandoffCertificate::from_compact_string(&compact).unwrap();
        let presentation = HandoffPresentation::create(decoded_cert, &recip_sk);

        // Step 5: Target validates
        let known = vec![intro_fed];
        let acceptance = validate_handoff(
            &presentation,
            &intro_pk,
            &mut swiss_table,
            &known,
            500, // much later
        )
        .unwrap();

        assert_eq!(acceptance.cell_id, target_cell);
        assert_eq!(acceptance.permissions, AuthRequired::Signature);
    }

    // ── Hybrid post-quantum handoff (ed25519 ∧ ML-DSA-65) ───────────────────

    /// Full hybrid setup: returns the presentation, the introducer's ed25519 pk,
    /// the introducer's ENROLLED ML-DSA pk, the introducer federation, and the
    /// target swiss table (with the swiss pre-registered).
    fn full_hybrid_setup() -> (
        HybridHandoffPresentation,
        PublicKey,    // introducer ed25519 pk
        Vec<u8>,      // introducer ENROLLED ml-dsa pk
        FederationId, // introducer federation
        SwissTable,
    ) {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // The introducer's ENROLLED ML-DSA key (derived from its ed25519 seed).
        let intro_ml_dsa_pk =
            MlDsaHandoffKey::from_ed25519_seed(&intro_sk.to_bytes()).public_bytes();
        // The recipient's ML-DSA key, which the introducer pins into the cert.
        let recip_ml_dsa_pk =
            MlDsaHandoffKey::from_ed25519_seed(&recip_sk.to_bytes()).public_bytes();

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        let cert = HybridHandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            None,
            swiss,
            recip_ml_dsa_pk,
        );
        let presentation = HybridHandoffPresentation::create(cert, &recip_sk);
        (
            presentation,
            intro_pk,
            intro_ml_dsa_pk,
            intro_fed,
            swiss_table,
        )
    }

    #[test]
    fn hybrid_honest_handoff_passes() {
        let (presentation, intro_pk, intro_ml_dsa_pk, intro_fed, mut swiss_table) =
            full_hybrid_setup();
        let known = vec![intro_fed];
        let acceptance = validate_handoff_hybrid(
            &presentation,
            &intro_pk,
            &intro_ml_dsa_pk,
            &mut swiss_table,
            &known,
            150,
        )
        .expect("honest hybrid handoff must be accepted");
        assert_eq!(acceptance.cell_id, CellId([0xEE; 32]));
        assert_eq!(acceptance.permissions, AuthRequired::Signature);
    }

    #[test]
    fn hybrid_roundtrips_out_of_band() {
        let (presentation, _, _, _, _) = full_hybrid_setup();
        let bytes = presentation.to_bytes();
        let decoded = HybridHandoffPresentation::from_bytes(&bytes).unwrap();
        assert_eq!(
            decoded.recipient_ml_dsa_sig,
            presentation.recipient_ml_dsa_sig
        );
        assert_eq!(
            decoded.certificate.recipient_ml_dsa_pk,
            presentation.certificate.recipient_ml_dsa_pk
        );
    }

    /// THE ADVERSARIAL TEST. The introducer's ed25519 half is valid for identity P
    /// (as a quantum adversary who broke ed25519 could produce), but the ML-DSA
    /// half is signed under an ATTACKER's fresh ML-DSA key — NOT P's enrolled key.
    /// `validate_handoff_hybrid` must REJECT.
    #[test]
    fn hybrid_introducer_pq_under_attacker_key_rejected() {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let enrolled_intro_ml_dsa_pk =
            MlDsaHandoffKey::from_ed25519_seed(&intro_sk.to_bytes()).public_bytes();
        let recip_ml_dsa_pk =
            MlDsaHandoffKey::from_ed25519_seed(&recip_sk.to_bytes()).public_bytes();

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        // Honest classical cert (valid ed25519 introducer half).
        let base = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            None,
            swiss,
        );
        // Attacker forges the PQ half under their OWN fresh ML-DSA key.
        let attacker_pq = MlDsaHandoffKey::from_ed25519_seed(&[0xAB; 32]);
        let forged_msg = HybridHandoffCertificate::hybrid_signing_message(
            &base,
            &attacker_pq.public_bytes(),
            &recip_ml_dsa_pk,
        );
        let forged_cert = HybridHandoffCertificate {
            base,
            recipient_ml_dsa_pk: recip_ml_dsa_pk,
            introducer_ml_dsa_sig: attacker_pq.sign(&forged_msg),
        };
        let presentation = HybridHandoffPresentation::create(forged_cert, &recip_sk);

        let known = vec![intro_fed];
        let result = validate_handoff_hybrid(
            &presentation,
            &intro_pk,
            &enrolled_intro_ml_dsa_pk, // enrolled key ≠ attacker key
            &mut swiss_table,
            &known,
            150,
        );
        assert_eq!(
            result.unwrap_err(),
            HandoffError::InvalidIntroducerPqSignature,
            "PQ half under a non-enrolled ML-DSA key must be rejected"
        );
    }

    /// Recipient variant: the recipient's ed25519 half is valid but their ML-DSA
    /// half is signed under an attacker key that is NOT the introducer-pinned
    /// `recipient_ml_dsa_pk`. Must REJECT.
    #[test]
    fn hybrid_recipient_pq_under_attacker_key_rejected() {
        let (presentation, intro_pk, intro_ml_dsa_pk, intro_fed, mut swiss_table) =
            full_hybrid_setup();

        // Overwrite the recipient PQ signature with one under an attacker key,
        // leaving the (introducer-pinned) recipient_ml_dsa_pk and the valid
        // ed25519 recipient signature intact.
        let attacker_pq = MlDsaHandoffKey::from_ed25519_seed(&[0xCD; 32]);
        let recip_msg = HybridHandoffCertificate::hybrid_presentation_message(
            &presentation.certificate.base,
            &presentation.certificate.recipient_ml_dsa_pk,
        );
        let mut forged = presentation;
        forged.recipient_ml_dsa_sig = attacker_pq.sign(&recip_msg);

        let known = vec![intro_fed];
        let result = validate_handoff_hybrid(
            &forged,
            &intro_pk,
            &intro_ml_dsa_pk,
            &mut swiss_table,
            &known,
            150,
        );
        assert_eq!(
            result.unwrap_err(),
            HandoffError::InvalidRecipientPqSignature
        );
    }

    /// A missing PQ half (empty signature bytes) must fail CLOSED.
    #[test]
    fn hybrid_missing_pq_half_fails_closed() {
        let (mut presentation, intro_pk, intro_ml_dsa_pk, intro_fed, mut swiss_table) =
            full_hybrid_setup();
        presentation.certificate.introducer_ml_dsa_sig = Vec::new();
        let known = vec![intro_fed];
        let result = validate_handoff_hybrid(
            &presentation,
            &intro_pk,
            &intro_ml_dsa_pk,
            &mut swiss_table,
            &known,
            150,
        );
        assert_eq!(
            result.unwrap_err(),
            HandoffError::InvalidIntroducerPqSignature,
            "an absent PQ half must fail closed, never pass"
        );
    }

    /// Verifying against the WRONG enrolled introducer key (as if the roster
    /// pinned a different identity's PQ key) must reject even an otherwise honest
    /// certificate — the pin is load-bearing.
    #[test]
    fn hybrid_wrong_enrolled_key_rejected() {
        let (presentation, intro_pk, _correct, intro_fed, mut swiss_table) = full_hybrid_setup();
        let wrong_enrolled = MlDsaHandoffKey::from_ed25519_seed(&[0x99; 32]).public_bytes();
        let known = vec![intro_fed];
        let result = validate_handoff_hybrid(
            &presentation,
            &intro_pk,
            &wrong_enrolled,
            &mut swiss_table,
            &known,
            150,
        );
        assert_eq!(
            result.unwrap_err(),
            HandoffError::InvalidIntroducerPqSignature
        );
    }
}

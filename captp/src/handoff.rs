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
    /// invalid *against the introducer's id-committed ML-DSA key*. Raised when the
    /// classical ed25519 half may be valid but the PQ half is missing, malformed,
    /// or signed under a key other than the one the introducer's FederationId
    /// commits to — the exact forgery a quantum adversary would mount. Fail-closed.
    InvalidIntroducerPqSignature,
    /// The introducer's FederationId does not COMMIT to the self-carried ML-DSA-65
    /// public key (`H("dregg-hybrid-id-v1", P_ed ‖ P_ml) != introducer`). The key
    /// was not enrolled by the introducer's identity — e.g. a quantum adversary who
    /// forged the ed25519 half and self-supplied their OWN ML-DSA key, or a legacy
    /// ed25519-only FederationId that commits to no ML-DSA key at all. The
    /// FederationId IS the enrollment (replacing the out-of-band enrolled roster).
    IntroducerIdentityCommitmentMismatch,
    /// The recipient's ML-DSA-65 (post-quantum) half of the HYBRID presentation is
    /// invalid against the introducer-PINNED recipient ML-DSA key. Fail-closed.
    InvalidRecipientPqSignature,
    /// The wire-supplied introducer public key does NOT correspond to the
    /// certificate's claimed `introducer` id (the CLASSICAL live path's id↔pk
    /// binding, F-1). `validate_handoff` verifies the introducer signature against a
    /// wire-supplied `introducer_pk`, then checks the claimed `introducer` is a known
    /// federation — but NEITHER binds `introducer_pk` to `cert.introducer`. Without
    /// this, a presenter sets `introducer = <trusted F>`, signs the cert with their
    /// OWN key, and supplies their own pk: the signature verifies (it covers
    /// `introducer = F`) and F is trusted, so the handoff is falsely ATTRIBUTED to F
    /// which never signed. The classical path therefore requires a LEGACY ed25519 id
    /// (`introducer.0 == introducer_pk.0`); a HYBRID introducer id commits to an
    /// ML-DSA key absent from the classical wire and MUST use `validate_handoff_hybrid`
    /// (which binds id↔pk via `verify_committed_ml_dsa`), so it fails CLOSED here.
    IntroducerKeyMismatch,
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
    /// §6 non-amplification COULD NOT BE DECIDED: no verified Lean gate is
    /// registered in this process (or the linked archive lacks the export, or the
    /// gate errored on the wire). The handoff is still REFUSED — fail-closed is the
    /// only safe verdict for an undecided authority comparison — but this is a
    /// MISCONFIGURED VALIDATOR, not a detected attack.
    ///
    /// # Why this is not [`HandoffError::Amplification`]
    ///
    /// It used to be. `validate_handoff` decided §6 through the gate and collapsed
    /// `None` into the amplifying verdict (`.unwrap_or(false)`), so a vat that had
    /// simply never called `dregg_exec_lean::register_distributed_gates()` accused
    /// every honest peer of authority amplification — on a first, honest,
    /// `granted == held` presentation. Two facts with opposite remedies ("your
    /// certificate is an attack" / "my validator never installed its checker")
    /// arrived as the same byte, so neither an operator, a peer, nor a test could
    /// tell whether the check had run at all. `handoff_session::accept_handoff`
    /// even reported `Refused { amplification: true }` back over the wire, which
    /// slandered the presenter for the receiver's own misconfiguration.
    ///
    /// A silent hard refusal and a silent accept are the same defect wearing
    /// different clothes: in both, the caller cannot tell whether the check ran.
    /// Naming the case fixes that without relaxing anything — the handoff is
    /// refused exactly as before, and the amplification decision itself is
    /// untouched and still comes only from the verified Lean gate.
    VerifiedGateUnavailable,
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
                "invalid introducer ML-DSA (post-quantum) half: not signed under the id-committed key"
            ),
            HandoffError::IntroducerIdentityCommitmentMismatch => write!(
                f,
                "introducer FederationId does not commit to the presented ML-DSA-65 public key \
                 (the key was not enrolled by the introducer's identity)"
            ),
            HandoffError::InvalidRecipientPqSignature => write!(
                f,
                "invalid recipient ML-DSA (post-quantum) half on handoff presentation"
            ),
            HandoffError::IntroducerKeyMismatch => write!(
                f,
                "introducer public key does not correspond to the certificate's introducer id \
                 (classical handoff requires a legacy ed25519 id == pk; a hybrid id must use the hybrid path)"
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
            HandoffError::VerifiedGateUnavailable => write!(
                f,
                "handoff REFUSED because §6 non-amplification could not be decided: no verified \
                 Lean CapTP gate is registered in this process (call \
                 `dregg_exec_lean::register_distributed_gates()` at startup, as `node/src/lib.rs` \
                 does). This is a misconfigured validator, NOT an amplifying certificate"
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
// ENROLL + PIN (the whole point). Self-carrying an ML-DSA public key with no
// binding gives ZERO post-quantum security (a quantum adversary forges the
// ed25519 half over identity P, generates its OWN ML-DSA keypair, and signs the
// PQ half under it — a self-consistent forgery). We close that TWO ways:
//   * The INTRODUCER's ML-DSA key is self-carried in the certificate but GATED by
//     the introducer's IDENTITY: `validate_handoff_hybrid` requires the
//     introducer's `FederationId` to COMMIT to it —
//     `introducer.verify_committed_ml_dsa(introducer_ed25519, introducer_ml_dsa_pk)`
//     recomputes `H("dregg-hybrid-id-v1", P_ed ‖ P_ml)` and equality-checks the
//     FederationId. The FederationId IS the enrollment (replacing the old
//     out-of-band enrolled ML-DSA parameter, GAP #2): a self-supplied key that
//     does not hash into the introducer's identity is REJECTED, so the adversary's
//     own ML-DSA key can never anchor a forged handoff. The verifier then verifies
//     the PQ half under that id-committed key.
//   * The RECIPIENT's ML-DSA key is PINNED into the certificate by the
//     introducer: `recipient_ml_dsa_pk` is covered by the introducer's (now
//     id-committed) ML-DSA signature, so a quantum adversary cannot substitute
//     their own without forging the (lattice-hard) introducer PQ half. The
//     recipient's PQ half is thus authenticated in-band — there is no out-of-band
//     recipient parameter to enroll.
//
// The ML-DSA key is derived DETERMINISTICALLY from the same 32-byte ed25519 seed
// the classical identity uses (`ML-DSA.KeyGen(ξ = seed)`), mirroring
// `turn::pq::MlDsaTurnKey::from_ed25519_seed` and `federation::frost` — so a node
// built from one mnemonic agrees on both keys with no separate ceremony.

mod hybrid_pq {
    //! Delegates to the shared `dregg-pq` leaf, pinning the handoff
    //! domain-separation context.

    /// Domain-separation context for the ML-DSA half of a HYBRID *handoff*
    /// signature (FIPS 204 `ctx`). Distinct from the turn-path (`dregg-hybrid-turn-v1`)
    /// and consensus-quorum contexts so a handoff PQ signature can never be
    /// replayed as a turn or quorum half, and vice versa.
    pub const HANDOFF_PQ_CTX: &[u8] = b"dregg-captp-handoff-hybrid-v1";

    /// Serialized length of an ML-DSA-65 public key (FIPS 204).
    pub const ML_DSA_PK_LEN: usize = dregg_pq::ML_DSA_PK_LEN;

    /// The PQ half of a hybrid identity: an ML-DSA-65 signing key plus its
    /// serialized public key, derived from the SAME seed as the ed25519 identity.
    ///
    /// A thin newtype over the shared [`dregg_pq::MlDsaKey`] primitive that pins
    /// the handoff domain-separation context ([`HANDOFF_PQ_CTX`]).
    pub struct MlDsaHandoffKey(dregg_pq::MlDsaKey);

    impl MlDsaHandoffKey {
        /// Derive the ML-DSA-65 keypair deterministically from a 32-byte ed25519
        /// seed (`ML-DSA.KeyGen(ξ = seed)`).
        pub fn from_ed25519_seed(seed: &[u8; 32]) -> Self {
            // `dregg-captp` is FFI-free by construction, so nothing in this crate's test binary
            // installs a verified PQ core and `dregg-pq` refuses the derivation with an
            // uncatchable `process::abort()`. The dev-only `dregg-pq-testkit` links the archive
            // and installs the cores; this and `ml_dsa_verify` below are the two entries from this
            // crate into `dregg-pq`, so the lib-test binary is covered by these two lines.
            //
            // `#[cfg(test)]` because the shipped crate stays archive-free — a node installs the
            // same cores at startup.
            #[cfg(test)]
            dregg_pq_testkit::install_or_panic();
            Self(dregg_pq::MlDsaKey::from_ed25519_seed(seed))
        }

        /// The serialized ML-DSA-65 public key.
        pub fn public_bytes(&self) -> Vec<u8> {
            self.0.public_bytes()
        }

        /// Sign `message` under [`HANDOFF_PQ_CTX`] (hedged from OS entropy).
        pub fn sign(&self, message: &[u8]) -> Vec<u8> {
            self.0.sign(HANDOFF_PQ_CTX, message)
        }
    }

    /// Verify an ML-DSA-65 signature over `message` under [`HANDOFF_PQ_CTX`].
    /// Returns `false` — never a panic — on a wrong-length / undecodable key or
    /// signature, or a failed check. This is the fail-CLOSED primitive: a
    /// missing or present-but-invalid PQ half must reject the whole hybrid handoff.
    pub fn ml_dsa_verify(public_bytes: &[u8], message: &[u8], sig_bytes: &[u8]) -> bool {
        // The other entry from this crate into `dregg-pq` — see `MlDsaHandoffKey::from_ed25519_seed`.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        dregg_pq::ml_dsa_verify(public_bytes, HANDOFF_PQ_CTX, message, sig_bytes)
    }
}

pub use hybrid_pq::{ML_DSA_PK_LEN, MlDsaHandoffKey};

/// A party's HYBRID handoff identity: the ed25519 key and the ML-DSA-65 key its seed derives, held
/// TOGETHER and derived ONCE. Used by an introducer to issue certificates and by a recipient to
/// present them.
///
/// This type exists because the derivation is expensive and the signing sites were not.
/// `MlDsaHandoffKey::from_ed25519_seed` is deterministic FIPS 204 `ML-DSA.KeyGen(ξ)` and, on the
/// deployed build, runs the Lean-verified keygen core across the FFI boundary at **174–227 ms of
/// CPU**. Both [`HybridHandoffCertificate::create`] and [`HybridHandoffPresentation::create`] take a
/// BARE `SigningKey`, so there was nothing for a derived key to belong to and every certificate
/// issued and every presentation made paid a fresh keygen for one unchanging key — an introducer
/// that vouches for n recipients paid n of them.
///
/// **The key lives INSIDE the identity, not in a lookup table.** A process-global map keyed by seed
/// would pool every party's ML-DSA secret in one process-lifetime structure outliving the identities
/// that own them, and make "who may read this entry" a property of a lookup key rather than of
/// ownership. Here the derived key is a private field of the object that owns the ed25519 key, so
/// two parties are two objects and cross-identity sharing has no path to express itself.
///
/// Both fields are private, set together at construction, with no mutator — so an identity cannot be
/// re-keyed in place and its two halves cannot drift apart.
pub struct HybridHandoffIdentity {
    classical: SigningKey,
    /// Behind an `Arc` so the in-module tests can prove by OBJECT IDENTITY, rather than by a
    /// stopwatch, that signing reads this key instead of deriving another.
    pq: std::sync::Arc<MlDsaHandoffKey>,
    ml_dsa_pk: Vec<u8>,
}

impl std::fmt::Debug for HybridHandoffIdentity {
    /// Never renders key material.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("HybridHandoffIdentity(..)")
    }
}

impl HybridHandoffIdentity {
    /// Take ownership of an ed25519 identity and derive its ML-DSA half. This is where the keygen
    /// is paid — once.
    pub fn new(classical: SigningKey) -> Self {
        let pq = std::sync::Arc::new(MlDsaHandoffKey::from_ed25519_seed(&classical.to_bytes()));
        let ml_dsa_pk = pq.public_bytes();
        Self {
            classical,
            pq,
            ml_dsa_pk,
        }
    }

    /// This party's ed25519 public key.
    pub fn ed25519_public(&self) -> PublicKey {
        self.classical.public_key()
    }

    /// This party's ML-DSA-65 public key — the value an introducer PINS for a recipient, and the
    /// one a `FederationId` must commit to for an introducer.
    pub fn ml_dsa_public_bytes(&self) -> &[u8] {
        &self.ml_dsa_pk
    }

    /// Issue a hybrid handoff certificate as the INTRODUCER — the same bytes
    /// [`HybridHandoffCertificate::create`] produces, with no key derivation however many
    /// certificates this introducer issues.
    #[allow(clippy::too_many_arguments)]
    pub fn issue_certificate(
        &self,
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
    ) -> HybridHandoffCertificate {
        let base = HandoffCertificate::create(
            &self.classical,
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
        let introducer_ml_dsa_pk = self.ml_dsa_pk.clone();
        let message = HybridHandoffCertificate::hybrid_signing_message(
            &base,
            &introducer_ml_dsa_pk,
            &recipient_ml_dsa_pk,
        );
        let introducer_ml_dsa_sig = self.pq.sign(&message);
        HybridHandoffCertificate {
            base,
            introducer_ml_dsa_pk,
            recipient_ml_dsa_pk,
            introducer_ml_dsa_sig,
        }
    }

    /// Present a hybrid handoff certificate as the RECIPIENT — the same bytes
    /// [`HybridHandoffPresentation::create`] produces, with no key derivation however many
    /// certificates this recipient presents.
    pub fn present(&self, certificate: HybridHandoffCertificate) -> HybridHandoffPresentation {
        let recipient_signature = sign(
            &self.classical,
            &HandoffPresentation::presentation_message(&certificate.base),
        );
        let message = HybridHandoffCertificate::hybrid_presentation_message(
            &certificate.base,
            &certificate.recipient_ml_dsa_pk,
        );
        let recipient_ml_dsa_sig = self.pq.sign(&message);
        HybridHandoffPresentation {
            certificate,
            recipient_signature,
            recipient_ml_dsa_sig,
        }
    }
}

/// A HYBRID handoff certificate: the classical [`HandoffCertificate`] plus the
/// post-quantum (ML-DSA-65) half. Travels out-of-band exactly like the classical
/// certificate (postcard / base58 / QR). See the module comment for the enroll +
/// pin discipline.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HybridHandoffCertificate {
    /// The classical certificate (carries the ed25519 introducer signature).
    pub base: HandoffCertificate,
    /// The introducer's ML-DSA-65 public key, SELF-CARRIED in the certificate.
    ///
    /// Safe to self-carry because the verifier does NOT trust it on its own:
    /// [`validate_handoff_hybrid`] first requires the introducer's IDENTITY to
    /// commit to it — `base.introducer.verify_committed_ml_dsa(introducer_ed25519,
    /// introducer_ml_dsa_pk)` recomputes `H("dregg-hybrid-id-v1", P_ed ‖ P_ml)`
    /// and equality-checks the introducer `FederationId`. A key not committed by
    /// the introducer's identity is REJECTED (the FederationId is the enrollment,
    /// replacing the out-of-band enrolled parameter — GAP #2).
    pub introducer_ml_dsa_pk: Vec<u8>,
    /// The recipient's ML-DSA-65 public key, PINNED here by the introducer:
    /// covered by `introducer_ml_dsa_sig`, so a quantum adversary cannot swap in
    /// their own recipient PQ key without forging the (lattice-hard) introducer
    /// PQ half.
    pub recipient_ml_dsa_pk: Vec<u8>,
    /// The introducer's ML-DSA-65 signature over [`HybridHandoffCertificate::hybrid_signing_message`],
    /// made under the id-committed `introducer_ml_dsa_pk`.
    pub introducer_ml_dsa_sig: Vec<u8>,
}

impl HybridHandoffCertificate {
    /// Create a hybrid handoff certificate (called by the introducer).
    ///
    /// `recipient_ml_dsa_pk` is the recipient's enrolled ML-DSA-65 public key
    /// (the introducer knows/vouches for the recipient and pins it into the
    /// cert). The introducer's own ML-DSA key is derived from `introducer_key`'s
    /// ed25519 seed, so no separate PQ key material is needed.
    ///
    /// A ONE-SHOT: it builds a [`HybridHandoffIdentity`], uses it once and drops it, so it pays a
    /// full ML-DSA keygen (174–227 ms on the deployed build) per certificate. An introducer that
    /// vouches for more than one recipient should hold a [`HybridHandoffIdentity`] and call
    /// [`HybridHandoffIdentity::issue_certificate`]. The bytes are identical either way.
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
        HybridHandoffIdentity::new(introducer_key.clone()).issue_certificate(
            introducer_federation,
            target_federation,
            target_cell,
            recipient_pk,
            permissions,
            allowed_effects,
            expires_at,
            max_uses,
            swiss,
            recipient_ml_dsa_pk,
        )
    }

    /// The canonical message the introducer signs with ML-DSA. Binds the entire
    /// classical signing message PLUS both hybrid public keys (the introducer's
    /// own and the pinned recipient's), each length-prefixed and domain-separated.
    /// Both signer and verifier pass the introducer's self-carried ML-DSA public
    /// key; the verifier only trusts that key after the introducer's FederationId
    /// is shown to commit to it (`verify_committed_ml_dsa`).
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
    ///
    /// A ONE-SHOT: it builds a [`HybridHandoffIdentity`], uses it once and drops it, so it pays a
    /// full ML-DSA keygen (174–227 ms on the deployed build) per presentation. A recipient that
    /// presents more than one certificate should hold a [`HybridHandoffIdentity`] and call
    /// [`HybridHandoffIdentity::present`]. The bytes are identical either way.
    pub fn create(certificate: HybridHandoffCertificate, recipient_key: &SigningKey) -> Self {
        HybridHandoffIdentity::new(recipient_key.clone()).present(certificate)
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
/// `0=None 1=Signature 2=Proof 3=Either 4=Impossible 5+(vk_hash)=Custom`. The `Custom` tag carries
/// the FULL 32-byte `vk_hash` INJECTIVELY as the decimal of `5 + BE(vk_hash)` (a value up to
/// 256 bits). The verified Lean gate decodes it as `custom (n - 5)` over an UNBOUNDED `Nat`
/// (`Dregg2.Exec.DistributedExports.authOfTag`) and compares Custom identities by equality
/// (`CapTPConcrete.handoffNonAmplifyingC`), so the ENTIRE 256-bit identity is the comparison key —
/// two Custom predicates differing in ANY byte get DISTINCT tags. (F-2: previously only
/// `vk_hash[..8]` was folded to a `u64`, so two distinct Customs agreeing in their first 8 bytes
/// collided to the SAME tag; the gate then judged `Custom{h1} == Custom{h2}` and admitted an
/// authority never held. The Lean decode was already full-width-faithful — the truncation was
/// entirely here — so restoring injectivity is a Rust-wire-only change, no Lean/AIR follow-up.)
fn auth_required_tag(a: &AuthRequired) -> String {
    match a {
        AuthRequired::None => "0".to_string(),
        AuthRequired::Signature => "1".to_string(),
        AuthRequired::Proof => "2".to_string(),
        AuthRequired::Either => "3".to_string(),
        AuthRequired::Impossible => "4".to_string(),
        AuthRequired::Custom { vk_hash } => custom_tag_decimal(vk_hash),
    }
}

/// The wire tag for `AuthRequired::Custom { vk_hash }`: the decimal string of
/// `5 + BE(vk_hash)`, reading the 32 bytes as a big-endian 256-bit unsigned integer.
/// INJECTIVE in `vk_hash` (distinct hashes ⇒ distinct tags). The `+ 5` matches the
/// Lean `authOfTag`/`tagOfAuth` offset reserving `0..=4` for the concrete variants;
/// the gate recovers `custom (tag - 5)` and compares the full identity by equality.
fn custom_tag_decimal(vk_hash: &[u8; 32]) -> String {
    // value = 5 + BE(vk_hash), on a 33-byte big-endian buffer that absorbs the carry.
    let mut buf = [0u8; 33];
    buf[1..].copy_from_slice(vk_hash);
    let mut carry: u16 = 5;
    for b in buf.iter_mut().rev() {
        let s = *b as u16 + carry;
        *b = (s & 0xff) as u8;
        carry = s >> 8;
        if carry == 0 {
            break;
        }
    }
    be_bytes_to_decimal(&buf)
}

/// A big-endian byte slice → its unsigned decimal string (repeated long division by
/// 10). Returns `"0"` for an all-zero input.
fn be_bytes_to_decimal(bytes: &[u8]) -> String {
    let mut num = bytes.to_vec();
    let mut digits: Vec<u8> = Vec::new();
    while !num.iter().all(|&b| b == 0) {
        let mut rem: u16 = 0;
        for b in num.iter_mut() {
            let cur = (rem << 8) | *b as u16;
            *b = (cur / 10) as u8;
            rem = cur % 10;
        }
        digits.push(b'0' + rem as u8);
    }
    if digits.is_empty() {
        return "0".to_string();
    }
    digits.reverse();
    String::from_utf8(digits).expect("digits are ASCII 0-9 by construction")
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
/// verified gate is unavailable (no gate registered / archive lacks the export / a wire error) — in
/// which case [`validate_handoff`] FAILS CLOSED and REFUSES with
/// [`HandoffError::VerifiedGateUnavailable`], rather than running an unverified Rust decision on the
/// live path or blaming the presenter with [`HandoffError::Amplification`]. Routes through the
/// [`crate::verified_gate`] seam so the crate has no hard dependency on the Lean archive.
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
    // FFI / wire error ⇒ `None` ⇒ the caller FAILS CLOSED (refuses the handoff as
    // `VerifiedGateUnavailable`), never a silent unverified Rust decision.
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

    // 1. Verify introducer signature (against the WIRE-supplied introducer_pk).
    if !cert.verify_signature(introducer_pk) {
        return Err(HandoffError::InvalidIntroducerSignature);
    }

    // 1b. F-1 — BIND the wire-supplied `introducer_pk` to the CLAIMED introducer id.
    //     Step 1 proves the cert was signed by whoever owns `introducer_pk`; the
    //     known-federation check (§3, below) proves `cert.introducer` is trusted.
    //     NEITHER proves `introducer_pk` is actually `cert.introducer`'s key — so a
    //     presenter could name a trusted federation F as `introducer`, sign with
    //     their OWN key, and supply their own pk: the signature verifies (it covers
    //     `introducer = F`) and F is trusted, so the handoff is falsely ATTRIBUTED to
    //     F which never signed (the introducer-impersonation forgery). Close it: the
    //     CLASSICAL path admits only a LEGACY ed25519 identity, whose id IS its
    //     ed25519 pk. A HYBRID introducer id (`H("dregg-hybrid-id-v1", P_ed ‖ P_ml)`)
    //     commits to an ML-DSA key not present on this classical wire; it cannot be
    //     bound here and MUST use `validate_handoff_hybrid` (which binds id↔pk via
    //     `verify_committed_ml_dsa`). So a non-legacy id fails CLOSED.
    if cert.introducer.0 != introducer_pk.0 {
        return Err(HandoffError::IntroducerKeyMismatch);
    }

    validate_handoff_body(presentation, swiss_table, known_federations, current_height)
}

/// The introducer-AUTHENTICATED remainder of handoff validation, shared by the
/// classical [`validate_handoff`] and the hybrid [`validate_handoff_hybrid`]. The
/// caller MUST have already authenticated the introducer AND bound its key to
/// `cert.introducer` (classical: the legacy `id == pk` equality; hybrid: the
/// `verify_committed_ml_dsa` id-commitment) before calling this. It takes no
/// `introducer_pk` and performs NO introducer key↔id binding of its own — it runs:
/// recipient signature, known-federation, expiry, swiss admission (read-only),
/// target binding, §6 non-amplification, replay, and the use-consuming success path.
fn validate_handoff_body(
    presentation: &HandoffPresentation,
    swiss_table: &mut SwissTable,
    known_federations: &[FederationId],
    current_height: u64,
) -> Result<HandoffAcceptance, HandoffError> {
    let cert = &presentation.certificate;

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
    //    effect-mask facet. The AUTHORITATIVE decider is the VERIFIED Lean export
    //    `dregg_captp_validate_handoff` (= `Dregg2.Exec.CapTPConcrete.handoffNonAmplifyingC`, proved
    //    equal to the export by `captp_validate_handoff_eq`), routed through the [`crate::verified_gate`]
    //    seam. The hand-written Rust rights lattice is NO LONGER a live decider here: it was a
    //    differential twin that could silently diverge in a config where the gate is absent, so it has
    //    been deleted from this live path.
    //
    //    FAIL CLOSED, AND SAY WHICH: when no verified gate is registered (an FFI-free target, a vat
    //    that never installed the `dregg-exec-lean` gate, or an archive lacking the export) the
    //    handoff is REFUSED — never a silent unverified Rust decision. But it is refused as
    //    `VerifiedGateUnavailable`, NOT as `Amplification`: the gate having been unable to run is a
    //    fact about THIS VALIDATOR, and reporting it as an attack by the presenter is what let a
    //    missing `register_distributed_gates()` masquerade as an honest peer amplifying authority.
    //    The refusal is identical; only its NAME now distinguishes "could not check" from "checked,
    //    and it amplifies". (The concrete rights lattice `AuthRequired::is_narrower_or_equal` +
    //    `is_facet_attenuation` remains pinned Rust↔Lean by `handoff_lattice_differential.rs`, and
    //    both poles over a linked archive — attenuating ADMITTED, amplifying REFUSED — are exercised
    //    by `node/src/captp_handoff_e2e.rs`, `teasting/tests/captp_verified_gate_poles.rs`, and
    //    `dregg-redteam`'s CapTP attack suites.)
    let non_amplifying = match verified_non_amplifying(
        &cert.permissions,
        &held.permissions,
        cert.allowed_effects,
        held.allowed_effects,
    ) {
        Some(v) => v,
        None => return Err(HandoffError::VerifiedGateUnavailable),
    };
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
/// * The introducer's ML-DSA-65 public key is SELF-CARRIED in the certificate
///   (`certificate.introducer_ml_dsa_pk`) but trusted ONLY after the introducer's
///   IDENTITY commits to it: `certificate.base.introducer.verify_committed_ml_dsa(
///   introducer_ed25519, introducer_ml_dsa_pk)` recomputes `H("dregg-hybrid-id-v1",
///   P_ed ‖ P_ml)` and equality-checks the introducer `FederationId`. The
///   FederationId IS the enrollment — this replaces the old out-of-band enrolled
///   ML-DSA parameter (GAP #2). A quantum adversary who forges the ed25519 half and
///   self-supplies their OWN ML-DSA key is rejected, because that key does not hash
///   into the introducer's FederationId; a legacy ed25519-only FederationId (which
///   commits to no ML-DSA key) is also rejected (staged flag-day). The PQ half is
///   then verified under that id-committed key.
/// * the recipient's PQ half is verified under the introducer-PINNED
///   `certificate.recipient_ml_dsa_pk` (authenticated in-band by the introducer PQ
///   half, which is itself now id-committed) — no out-of-band recipient parameter.
///
/// Fail-CLOSED: a missing, malformed, mis-keyed, or non-id-committed PQ half
/// rejects. The PQ checks are pure and run BEFORE any swiss-budget mutation (this
/// fn then delegates the swiss / non-amplification / target-binding / replay /
/// enliven logic to [`validate_handoff`], which uses a read-only `check` until the
/// success path).
pub fn validate_handoff_hybrid(
    presentation: &HybridHandoffPresentation,
    introducer_pk: &PublicKey,
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

    // 2. Introducer IDENTITY id-commitment gate (replaces the out-of-band enrolled
    //    ML-DSA parameter, GAP #2). The introducer self-carries its ML-DSA-65
    //    public key, but we do NOT trust it on its own: the introducer's
    //    FederationId must COMMIT to it. `verify_committed_ml_dsa` recomputes
    //    `H("dregg-hybrid-id-v1", P_ed ‖ P_ml)` and equality-checks the
    //    FederationId, so the FederationId IS the enrollment. A self-supplied key
    //    not committed by the introducer's identity — the quantum-forgery case,
    //    where the adversary forges the ed25519 half and presents their OWN ML-DSA
    //    key — is rejected here BEFORE its (self-consistent) signature is ever
    //    trusted. A legacy ed25519-only FederationId commits to no ML-DSA key and
    //    also fails CLOSED (staged flag-day).
    if !base_cert
        .introducer
        .verify_committed_ml_dsa(&introducer_pk.0, &hcert.introducer_ml_dsa_pk)
    {
        return Err(HandoffError::IntroducerIdentityCommitmentMismatch);
    }

    // 3. Introducer post-quantum (ML-DSA-65) half — verified under the now
    //    id-committed self-carried key. A signature under any other ML-DSA key
    //    fails.
    let intro_msg = HybridHandoffCertificate::hybrid_signing_message(
        base_cert,
        &hcert.introducer_ml_dsa_pk,
        &hcert.recipient_ml_dsa_pk,
    );
    if !hybrid_pq::ml_dsa_verify(
        &hcert.introducer_ml_dsa_pk,
        &intro_msg,
        &hcert.introducer_ml_dsa_sig,
    ) {
        return Err(HandoffError::InvalidIntroducerPqSignature);
    }

    // 4. Recipient classical (ed25519) half.
    let recip_pk = PublicKey(base_cert.recipient_pk);
    let present_msg = HandoffPresentation::presentation_message(base_cert);
    if !recip_pk.verify(&present_msg, &presentation.recipient_signature) {
        return Err(HandoffError::InvalidRecipientSignature);
    }

    // 5. Recipient post-quantum half — verified UNDER the introducer-pinned
    //    `recipient_ml_dsa_pk` (authenticated in-band by the id-committed
    //    introducer PQ half, steps 2–3). Fail-closed.
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

    // 6+. Run the swiss / non-amplification / target-binding / replay / enliven
    //     logic via the shared introducer-authenticated body (which re-checks the
    //     recipient ed25519 half, harmless). We call `validate_handoff_body`
    //     DIRECTLY rather than `validate_handoff`: the hybrid introducer was already
    //     authenticated AND bound to its id above (ed25519 sig + id-commitment via
    //     `verify_committed_ml_dsa`, steps 1–3), so re-imposing the CLASSICAL legacy
    //     `id == pk` binding would REJECT this (hashed) hybrid id — the id-commitment
    //     IS the hybrid path's id↔pk binding.
    let base_pres = HandoffPresentation {
        certificate: base_cert.clone(),
        recipient_signature: presentation.recipient_signature,
    };
    validate_handoff_body(&base_pres, swiss_table, known_federations, current_height)
}

// =============================================================================
// TEST-ONLY: the §6 non-amplification gate for the in-crate unit tests
// =============================================================================
//
// `validate_handoff` decides §6 non-amplification ONLY through the verified Lean
// gate and FAILS CLOSED (refuses) when none is registered (the twin-deletion
// posture). The lib's own unit tests below drive both LEGITIMATE (attenuating)
// and AMPLIFYING handoffs through `validate_handoff` and must observe the REAL
// verdict — so the permissive "assume non-amplifying" stand-in used by the
// integration tests (`tests/common/mod.rs`) is WRONG here: it would ADMIT the
// amplifying cases the `amplifying_*_rejected` tests require to be refused.
//
// This installs a gate that computes the verdict from the SAME retained,
// Lean-pinned lattice the live path deleted only as a *decider*:
// `AuthRequired::is_narrower_or_equal` + `dregg_cell::is_facet_attenuation`,
// which `handoff_lattice_differential.rs` pins clause-for-clause to the Lean
// `Dregg2.Exec.CapTPConcrete.authNarrowerOrEqual` decision table. It is
// `#[cfg(test)]`, never a live path (integration binaries compile the crate
// WITHOUT `cfg(test)`, so `validate_handoff` still fail-closes there); the live
// verdict routes to `dregg-exec-lean`'s real Lean gate.
#[cfg(test)]
struct LatticeVerdictGate;

#[cfg(test)]
impl crate::verified_gate::CaptpVerifiedGate for LatticeVerdictGate {
    fn distributed_exports_available(&self) -> bool {
        true
    }

    fn handoff_non_amplifying(&self, wire: &str) -> Option<bool> {
        // wire: "h=<held_tag>;g=<granted_tag>;he=<held_eff>;ge=<granted_eff>"
        // built by `verified_non_amplifying` via `auth_required_tag` /
        // `effect_mask_field`; an effect field of "x" means unrestricted (None).
        let (mut held_tag, mut granted_tag): (Option<&str>, Option<&str>) = (None, None);
        let (mut held_eff, mut granted_eff) = (None, None);
        for field in wire.split(';') {
            let (k, v) = field.split_once('=')?;
            match k {
                // Tags are decimal strings — the Custom tag is the full 256-bit
                // `5 + BE(vk_hash)` (far past `u64`), so parse it big-width, not as u64.
                "h" => held_tag = Some(v),
                "g" => granted_tag = Some(v),
                "he" => held_eff = Some(parse_test_effect_field(v)),
                "ge" => granted_eff = Some(parse_test_effect_field(v)),
                _ => {}
            }
        }
        let held = auth_required_from_tag(held_tag?);
        let granted = auth_required_from_tag(granted_tag?);
        // Non-amplifying ⟺ granted ⊆ held on BOTH the permission lattice and the
        // effect facet — the exact two-leg predicate `validate_handoff` used
        // before the twin-deletion (and that `handoffNonAmplifyingC` proves).
        let perm_ok = granted.is_narrower_or_equal(&held);
        let eff_ok = match (granted_eff?, held_eff?) {
            (_, None) => true,        // held unrestricted: granted always attenuates
            (None, Some(_)) => false, // held restricted, granted unrestricted: amplify
            (Some(g), Some(h)) => dregg_cell::is_facet_attenuation(h, g),
        };
        Some(perm_ok && eff_ok)
    }

    fn process_drop(&self, _wire: &str) -> Option<String> {
        None
    }
    fn pipeline_resolve(&self, _wire: &str) -> Option<String> {
        None
    }
}

/// Parse an `effect_mask_field` wire value: `"x"` ⇒ unrestricted (`None`), a
/// decimal ⇒ the concrete `EffectMask`. (`EffectMask` is a `u32`.)
#[cfg(test)]
fn parse_test_effect_field(v: &str) -> Option<EffectMask> {
    if v == "x" {
        None
    } else {
        v.parse::<EffectMask>().ok()
    }
}

/// Invert `auth_required_tag` for the test gate. Tags `"0".."4"` are the concrete
/// variants; any other decimal is `Custom` and is decoded as the FULL 32-byte
/// `vk_hash = tag - 5` (the exact inverse of [`custom_tag_decimal`]). Reconstructing
/// the whole identity — not just its first 8 bytes — is what lets this gate observe
/// the F-2 fix: two tags differing anywhere rebuild DISTINCT `Custom`s, so the
/// lattice's `Custom` tag-equality judges distinct authorities distinct.
#[cfg(test)]
fn auth_required_from_tag(t: &str) -> AuthRequired {
    match t {
        "0" => AuthRequired::None,
        "1" => AuthRequired::Signature,
        "2" => AuthRequired::Proof,
        "3" => AuthRequired::Either,
        "4" => AuthRequired::Impossible,
        dec => AuthRequired::Custom {
            vk_hash: vk_hash_from_custom_tag(dec),
        },
    }
}

/// The inverse of [`custom_tag_decimal`]: a decimal `tag` (`= 5 + BE(vk_hash)`) →
/// the 32-byte big-endian `vk_hash`. Parses the decimal into a little-endian byte
/// magnitude, subtracts 5, and lays it out big-endian. Test-only; any real Custom
/// tag is `≥ 5` and `< 2^256 + 5`, so the round-trip is exact.
#[cfg(test)]
fn vk_hash_from_custom_tag(dec: &str) -> [u8; 32] {
    // Parse decimal → little-endian magnitude (le[0] = least-significant byte).
    let mut le: Vec<u8> = vec![0];
    for ch in dec.bytes() {
        let d = match ch {
            b'0'..=b'9' => (ch - b'0') as u16,
            _ => continue,
        };
        // le = le * 10 + d
        let mut carry = d;
        for b in le.iter_mut() {
            let cur = *b as u16 * 10 + carry;
            *b = (cur & 0xff) as u8;
            carry = cur >> 8;
        }
        while carry > 0 {
            le.push((carry & 0xff) as u8);
            carry >>= 8;
        }
    }
    // Subtract 5 (borrow-propagating; every real Custom tag is ≥ 5).
    let mut borrow: i16 = 5;
    for b in le.iter_mut() {
        if borrow == 0 {
            break;
        }
        let cur = *b as i16 - (borrow & 0xff);
        if cur < 0 {
            *b = (cur + 256) as u8;
            borrow = 1;
        } else {
            *b = cur as u8;
            borrow = 0;
        }
    }
    // Little-endian magnitude → 32-byte big-endian vk_hash.
    let mut out = [0u8; 32];
    for (i, &b) in le.iter().enumerate() {
        if i < 32 {
            out[31 - i] = b;
        }
    }
    out
}

/// Install the real-verdict §6 gate for THIS test process (idempotent). Called by
/// the setup helpers of the handoff unit tests (here and in `handoff_session`) so
/// every unit test observes the true attenuation verdict rather than the
/// no-gate fail-closed refusal.
#[cfg(test)]
pub(crate) fn install_test_lattice_gate() {
    use std::sync::Once;
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        crate::verified_gate::register_captp_verified_gate(Box::new(LatticeVerdictGate));
    });
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
        super::install_test_lattice_gate();
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
        super::install_test_lattice_gate();
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
        super::install_test_lattice_gate();
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
    /// the introducer's HYBRID FederationId (which cryptographically COMMITS to the
    /// introducer's ed25519 AND ML-DSA keys — the enrollment), and the target swiss
    /// table (with the swiss pre-registered). No out-of-band enrolled ML-DSA key is
    /// threaded: the identity commitment replaces it (GAP #2).
    fn full_hybrid_setup() -> (
        HybridHandoffPresentation,
        PublicKey,    // introducer ed25519 pk
        FederationId, // introducer HYBRID federation id (commits to ed25519 ∧ ml-dsa)
        SwissTable,
    ) {
        super::install_test_lattice_gate();
        let (intro_sk, intro_pk) = generate_keypair();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // The introducer's ML-DSA key (derived from its ed25519 seed) and its
        // HYBRID FederationId = H("dregg-hybrid-id-v1", P_ed ‖ P_ml). The id IS the
        // enrollment: the self-carried ML-DSA key hashes into it.
        let intro_ml_dsa_pk =
            MlDsaHandoffKey::from_ed25519_seed(&intro_sk.to_bytes()).public_bytes();
        let intro_fed = FederationId::derive_hybrid(&intro_pk.0, &intro_ml_dsa_pk);
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
        (presentation, intro_pk, intro_fed, swiss_table)
    }

    #[test]
    fn hybrid_honest_handoff_passes() {
        let (presentation, intro_pk, intro_fed, mut swiss_table) = full_hybrid_setup();
        let known = vec![intro_fed];
        let acceptance =
            validate_handoff_hybrid(&presentation, &intro_pk, &mut swiss_table, &known, 150)
                .expect("honest hybrid handoff must be accepted");
        assert_eq!(acceptance.cell_id, CellId([0xEE; 32]));
        assert_eq!(acceptance.permissions, AuthRequired::Signature);
    }

    #[test]
    fn hybrid_roundtrips_out_of_band() {
        let (presentation, _, _, _) = full_hybrid_setup();
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

    /// THE ADVERSARIAL TEST (GAP #2 id-commitment closure). The introducer's
    /// HYBRID FederationId = `H("dregg-hybrid-id-v1", P_ed ‖ P_ml)`. A quantum
    /// adversary who broke ed25519 keeps P_ed (forges the classical half), but
    /// self-supplies their OWN fresh ML-DSA key AND a valid ML-DSA signature under
    /// it. Because that key does NOT hash into the introducer's FederationId, the
    /// id-commitment gate REJECTS it (`IntroducerIdentityCommitmentMismatch`)
    /// BEFORE the (self-consistent) PQ signature is ever trusted — and it is NOT a
    /// roster / known-federation mismatch (the FederationId is in `known`).
    ///
    /// This is the crux the hybrid-id foundation buys: the introducer self-carries
    /// its ML-DSA key (previously an unsafe out-of-band / self-carry pattern), but
    /// the verifier trusts it ONLY because the introducer's IDENTITY commits to it.
    #[test]
    fn hybrid_introducer_pq_under_attacker_key_rejected() {
        let (intro_sk, intro_pk) = generate_keypair();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // The HONEST introducer identity commits to BOTH of its keys.
        let honest_intro_ml =
            MlDsaHandoffKey::from_ed25519_seed(&intro_sk.to_bytes()).public_bytes();
        let intro_fed = FederationId::derive_hybrid(&intro_pk.0, &honest_intro_ml);
        let recip_ml_dsa_pk =
            MlDsaHandoffKey::from_ed25519_seed(&recip_sk.to_bytes()).public_bytes();

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        // Honest classical cert (valid ed25519 introducer half over the same id).
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
        // The attacker self-supplies their OWN fresh ML-DSA key and signs the
        // hybrid message under it — a self-consistent PQ half that verifies against
        // the attacker key.
        let attacker_pq = MlDsaHandoffKey::from_ed25519_seed(&[0xAB; 32]);
        let attacker_ml = attacker_pq.public_bytes();
        let forged_msg =
            HybridHandoffCertificate::hybrid_signing_message(&base, &attacker_ml, &recip_ml_dsa_pk);
        let forged_cert = HybridHandoffCertificate {
            base,
            introducer_ml_dsa_pk: attacker_ml.clone(),
            recipient_ml_dsa_pk: recip_ml_dsa_pk,
            introducer_ml_dsa_sig: attacker_pq.sign(&forged_msg),
        };
        // The forged PQ half IS itself a valid ML-DSA signature under the
        // attacker's key — so had the verifier trusted a self-carried key on its
        // own, this forgery would PASS. It is rejected ONLY because the introducer's
        // FederationId does not commit to that key.
        assert!(super::hybrid_pq::ml_dsa_verify(
            &attacker_ml,
            &forged_msg,
            &forged_cert.introducer_ml_dsa_sig
        ));

        let presentation = HybridHandoffPresentation::create(forged_cert, &recip_sk);
        let known = vec![intro_fed]; // the honest id IS trusted — not a roster miss
        let result =
            validate_handoff_hybrid(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::IntroducerIdentityCommitmentMismatch,
            "a self-supplied ML-DSA key not committed by the introducer FederationId \
             must be rejected by the id-commitment, not a roster mismatch"
        );
    }

    /// STAGED FLAG-DAY: a LEGACY ed25519-only introducer FederationId
    /// (`FederationId(pk.0)`, the raw ed25519 pk) commits to NO ML-DSA key, so the
    /// id-commitment gate fails CLOSED — a hybrid handoff requires a hybrid
    /// introducer identity. Even with an honestly self-carried ML-DSA key and a
    /// valid PQ signature under it, a legacy id can never satisfy the enrollment.
    #[test]
    fn hybrid_legacy_ed25519_only_introducer_rejected() {
        let (intro_sk, intro_pk) = generate_keypair();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // Legacy identity: the FederationId is the raw ed25519 pk, not H(ed ‖ ml).
        let intro_fed = FederationId(intro_pk.0);
        let recip_ml_dsa_pk =
            MlDsaHandoffKey::from_ed25519_seed(&recip_sk.to_bytes()).public_bytes();

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        // `create` honestly self-carries the introducer's real ML-DSA key.
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
        let known = vec![intro_fed];
        let result =
            validate_handoff_hybrid(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::IntroducerIdentityCommitmentMismatch,
            "a legacy ed25519-only introducer FederationId commits to no ML-DSA key \
             and must be rejected (staged flag-day)"
        );
    }

    /// Recipient variant: the recipient's ed25519 half is valid but their ML-DSA
    /// half is signed under an attacker key that is NOT the introducer-pinned
    /// `recipient_ml_dsa_pk`. Must REJECT.
    #[test]
    fn hybrid_recipient_pq_under_attacker_key_rejected() {
        let (presentation, intro_pk, intro_fed, mut swiss_table) = full_hybrid_setup();

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
        let result = validate_handoff_hybrid(&forged, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::InvalidRecipientPqSignature
        );
    }

    /// A missing PQ half (empty signature bytes) must fail CLOSED. The introducer
    /// identity still commits to the self-carried ML-DSA key, so the id-commitment
    /// gate passes and it is the ABSENT signature that rejects.
    #[test]
    fn hybrid_missing_pq_half_fails_closed() {
        let (mut presentation, intro_pk, intro_fed, mut swiss_table) = full_hybrid_setup();
        presentation.certificate.introducer_ml_dsa_sig = Vec::new();
        let known = vec![intro_fed];
        let result =
            validate_handoff_hybrid(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::InvalidIntroducerPqSignature,
            "an absent PQ half must fail closed, never pass"
        );
    }

    /// The introducer's self-carried ML-DSA key must be BOUND into the id: mutating
    /// a single byte of `introducer_ml_dsa_pk` (so it no longer hashes into the
    /// FederationId) is rejected by the id-commitment even though the FederationId
    /// is trusted — the commitment is load-bearing.
    #[test]
    fn hybrid_tampered_introducer_ml_dsa_pk_rejected() {
        let (mut presentation, intro_pk, intro_fed, mut swiss_table) = full_hybrid_setup();
        // Flip a byte of the self-carried key: it now differs from the key the
        // FederationId commits to.
        presentation.certificate.introducer_ml_dsa_pk[0] ^= 0xff;
        let known = vec![intro_fed];
        let result =
            validate_handoff_hybrid(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::IntroducerIdentityCommitmentMismatch,
            "a self-carried ML-DSA key not committed by the FederationId must reject"
        );
    }

    // ── F-1: introducer id↔pk binding on the classical live path ────────────

    /// F-1 FALSIFIER (introducer impersonation on the LIVE classical path). A
    /// presenter names a TRUSTED federation F as the cert's `introducer`, SIGNS the
    /// cert with their OWN key, and supplies their own pk on the wire. Pre-fix, the
    /// introducer-signature check (against the attacker pk, which really did sign)
    /// AND the known-federation check (F is trusted) BOTH passed, so the handoff was
    /// falsely ATTRIBUTED to F which never signed. The id↔pk binding now REFUSES it:
    /// the wire pk is not F's key.
    #[test]
    fn f1_introducer_impersonation_is_refused() {
        super::install_test_lattice_gate();
        // A trusted federation F the attacker wants to be credited as introducer.
        let (_f_sk, f_pk, f_fed) = setup_introducer();
        // The attacker's OWN key (unrelated to F).
        let (atk_sk, atk_pk) = generate_keypair();
        assert_ne!(atk_pk.0, f_pk.0, "the attacker key must differ from F's");
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        // The cert CLAIMS introducer = F but is SIGNED with the attacker's key.
        let cert = HandoffCertificate::create(
            &atk_sk, // signs with the attacker key ...
            f_fed,   // ... while naming F as the introducer
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            None,
            swiss,
        );
        let presentation = HandoffPresentation::create(cert, &recip_sk);
        // F is trusted; the attacker supplies THEIR OWN pk (which validates the
        // signature they actually produced). Both legacy checks pass — only the
        // id↔pk binding catches the impersonation.
        let known = vec![f_fed];
        let result = validate_handoff(&presentation, &atk_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::IntroducerKeyMismatch,
            "a cert naming introducer=F but signed under an unrelated key, presented with the \
             signer's own pk, must be refused: the wire pk is not bound to F"
        );
    }

    /// F-1 positive: a GENUINE introducer (legacy id == its ed25519 pk) still
    /// accepts — the binding does not reject honest handoffs.
    #[test]
    fn f1_genuine_introducer_still_accepts() {
        let (cert, recip_sk, intro_pk, intro_fed, _target_fed, mut swiss_table) =
            full_handoff_setup();
        let presentation = HandoffPresentation::create(cert, &recip_sk);
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert!(
            result.is_ok(),
            "a genuine introducer whose id is its ed25519 pk must still be accepted"
        );
    }

    // ── F-2: injective Custom encoding to the §6 gate ───────────────────────

    /// F-2 FALSIFIER (Custom auth truncated to 64 bits). Two DISTINCT Custom
    /// predicates that COLLIDE in their first 8 `vk_hash` bytes but differ later
    /// must be judged DISTINCT authorities. Pre-fix, `auth_required_tag` folded only
    /// `vk_hash[..8]` to a u64, so both encoded to the SAME wire tag: the gate judged
    /// `Custom{h1} == Custom{h2}` (non-amplifying) and admitted an authority never held.
    #[test]
    fn f2_custom_collision_in_first_8_bytes_is_amplification() {
        super::install_test_lattice_gate();
        // h1 and h2 AGREE on bytes 0..8, DIFFER at byte 8 (past the old fold window).
        let mut h1 = [0u8; 32];
        for (i, b) in h1.iter_mut().take(8).enumerate() {
            *b = i as u8;
        }
        let mut h2 = h1;
        h2[8] ^= 0xff;

        // (a) DIRECT: the LIVE encoder must give DISTINCT tags — the injectivity itself.
        assert_ne!(
            super::auth_required_tag(&AuthRequired::Custom { vk_hash: h1 }),
            super::auth_required_tag(&AuthRequired::Custom { vk_hash: h2 }),
            "Customs colliding in their first 8 bytes must encode to DISTINCT wire tags"
        );

        // (b) END-TO-END: held = Custom{h1}, granted = Custom{h2} (h1 ≠ h2) amplifies.
        let (presentation, intro_pk, intro_fed, mut swiss_table) = handoff_with_auth(
            AuthRequired::Custom { vk_hash: h1 },
            None,
            AuthRequired::Custom { vk_hash: h2 },
            None,
        );
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert_eq!(
            result.unwrap_err(),
            HandoffError::Amplification,
            "granting Custom{{h2}} over held Custom{{h1}} with h1 != h2 (colliding first 8 bytes) \
             must be refused as amplification"
        );
    }

    /// F-2 positive: an EQUAL Custom → Custom handoff (`Custom{h} → Custom{h}`)
    /// still attenuates — the injective encoding does not over-reject.
    #[test]
    fn f2_equal_custom_handoff_still_attenuates() {
        super::install_test_lattice_gate();
        let mut h = [0u8; 32];
        h[8] = 0x7c;
        h[31] = 0x01;
        let (presentation, intro_pk, intro_fed, mut swiss_table) = handoff_with_auth(
            AuthRequired::Custom { vk_hash: h },
            None,
            AuthRequired::Custom { vk_hash: h },
            None,
        );
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);
        assert!(
            result.is_ok(),
            "an equal Custom→Custom handoff (h == h) must still attenuate"
        );
    }

    /// The Custom tag codec round-trips: `vk_hash_from_custom_tag(custom_tag_decimal(h)) == h`
    /// across edge magnitudes (zero, low byte, high byte, all-ones). This pins the
    /// injective full-width encoding the F-2 fix relies on.
    #[test]
    fn f2_custom_tag_codec_roundtrips() {
        let cases: [[u8; 32]; 5] = [
            [0u8; 32],
            {
                let mut h = [0u8; 32];
                h[31] = 1; // value 1 (least-significant byte)
                h
            },
            {
                let mut h = [0u8; 32];
                h[0] = 0xff; // most-significant byte set (large 256-bit value)
                h
            },
            [0xffu8; 32], // 2^256 - 1: the +5 carry crosses into a 33rd byte
            {
                let mut h = [0u8; 32];
                for (i, b) in h.iter_mut().enumerate() {
                    *b = (i as u8).wrapping_mul(7).wrapping_add(3);
                }
                h
            },
        ];
        for h in cases {
            let tag = super::custom_tag_decimal(&h);
            assert!(
                tag.bytes().all(|c| c.is_ascii_digit()),
                "the wire tag must be all decimal digits (the Lean gate parses digits only)"
            );
            assert_eq!(
                super::vk_hash_from_custom_tag(&tag),
                h,
                "custom tag codec must round-trip the full 32-byte identity"
            );
        }
    }

    // ── The HELD ML-DSA key: `HybridHandoffIdentity` ─────────────────────────

    /// THE MANDATORY ONE. Four parties, issuing and presenting INTERLEAVED: no party may ever
    /// present, or sign under, another party's derived ML-DSA key.
    ///
    /// A held identity is a memo, and a memo that ever served one party's key to another would be a
    /// FORGERY ENGINE rather than a slow path. The falsifier is on the wire: every introducer's PQ
    /// half must verify under its own id-committed key and under NO other's, and the same for every
    /// recipient's presentation half.
    #[test]
    fn two_identities_never_share_a_derived_pq_key() {
        super::install_test_lattice_gate();
        let seeds: [[u8; 32]; 4] = [[0x11; 32], [0x22; 32], [0x33; 32], [0xf0; 32]];
        let parties: Vec<HybridHandoffIdentity> = seeds
            .iter()
            .map(|s| HybridHandoffIdentity::new(SigningKey::from_bytes(s)))
            .collect();

        // The truth each party must keep telling, computed independently of the identity.
        let expected: Vec<Vec<u8>> = seeds
            .iter()
            .map(|s| MlDsaHandoffKey::from_ed25519_seed(s).public_bytes())
            .collect();
        for (i, a) in expected.iter().enumerate() {
            for (j, b) in expected.iter().enumerate() {
                if i != j {
                    assert_ne!(
                        a, b,
                        "distinct seeds must derive distinct keys ({i} vs {j})"
                    );
                }
            }
        }

        // INTERLEAVED: each round, every party issues a certificate to its right-hand neighbour and
        // that neighbour presents it. A single-slot or last-writer cache mis-serves somebody.
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);
        let mut issued: Vec<Vec<HybridHandoffPresentation>> =
            (0..parties.len()).map(|_| Vec::new()).collect();
        for round in 0..3u64 {
            for i in 0..parties.len() {
                let j = (i + 1) % parties.len();
                let intro = &parties[i];
                let recip = &parties[j];
                assert_eq!(
                    intro.ml_dsa_public_bytes(),
                    expected[i],
                    "party {i} presented a PQ key that is not the one its own seed derives \
                     (round {round})"
                );
                let mut swiss_table = SwissTable::new();
                let swiss =
                    swiss_table.export(target_cell, AuthRequired::Signature, 100 + round, None);
                let cert = intro.issue_certificate(
                    FederationId::derive_hybrid(&intro.ed25519_public().0, expected[i].as_slice()),
                    target_fed,
                    target_cell,
                    recip.ed25519_public().0,
                    AuthRequired::Signature,
                    None,
                    None,
                    None,
                    swiss,
                    expected[j].clone(),
                );
                assert_eq!(cert.introducer_ml_dsa_pk, expected[i]);
                assert_eq!(cert.recipient_ml_dsa_pk, expected[j]);
                issued[i].push(recip.present(cert));
            }
        }

        // THE FALSIFIER, on the wire: each half verifies under its own key and under no other's.
        for (i, per_party) in issued.iter().enumerate() {
            let j = (i + 1) % parties.len();
            for presentation in per_party {
                let base = &presentation.certificate.base;
                let intro_msg = HybridHandoffCertificate::hybrid_signing_message(
                    base,
                    &presentation.certificate.introducer_ml_dsa_pk,
                    &presentation.certificate.recipient_ml_dsa_pk,
                );
                let recip_msg = HybridHandoffCertificate::hybrid_presentation_message(
                    base,
                    &presentation.certificate.recipient_ml_dsa_pk,
                );
                assert!(
                    hybrid_pq::ml_dsa_verify(
                        &expected[i],
                        &intro_msg,
                        &presentation.certificate.introducer_ml_dsa_sig
                    ),
                    "introducer {i}'s own PQ half must verify under its own key"
                );
                assert!(
                    hybrid_pq::ml_dsa_verify(
                        &expected[j],
                        &recip_msg,
                        &presentation.recipient_ml_dsa_sig
                    ),
                    "recipient {j}'s own PQ half must verify under its own key"
                );
                for (k, other) in expected.iter().enumerate() {
                    if k != i {
                        assert!(
                            !hybrid_pq::ml_dsa_verify(
                                other,
                                &intro_msg,
                                &presentation.certificate.introducer_ml_dsa_sig
                            ),
                            "introducer {i}'s PQ signature verified under party {k}'s key — two \
                             identities are sharing a derived key"
                        );
                    }
                    if k != j {
                        assert!(
                            !hybrid_pq::ml_dsa_verify(
                                other,
                                &recip_msg,
                                &presentation.recipient_ml_dsa_sig
                            ),
                            "recipient {j}'s PQ signature verified under party {k}'s key — two \
                             identities are sharing a derived key"
                        );
                    }
                }
            }
        }
    }

    /// The identity derives its ML-DSA key ONCE, proven by OBJECT IDENTITY rather than by a
    /// stopwatch: a timing assertion flakes on a loaded box and says nothing about which key was
    /// served. Issuing to many recipients must read the same `Arc`.
    #[test]
    fn an_identity_derives_its_pq_key_once_however_many_certificates_it_issues() {
        super::install_test_lattice_gate();
        let intro = HybridHandoffIdentity::new(SigningKey::from_bytes(&[0x7a; 32]));
        let held = std::sync::Arc::clone(&intro.pq);
        let intro_fed =
            FederationId::derive_hybrid(&intro.ed25519_public().0, intro.ml_dsa_public_bytes());
        for i in 0..4u64 {
            let recip = HybridHandoffIdentity::new(SigningKey::from_bytes(&[0x80 + i as u8; 32]));
            let mut swiss_table = SwissTable::new();
            let swiss = swiss_table.export(CellId([0xEE; 32]), AuthRequired::Signature, 100, None);
            let cert = intro.issue_certificate(
                intro_fed,
                FederationId([0xDD; 32]),
                CellId([0xEE; 32]),
                recip.ed25519_public().0,
                AuthRequired::Signature,
                None,
                None,
                None,
                swiss,
                recip.ml_dsa_public_bytes().to_vec(),
            );
            assert!(
                std::sync::Arc::ptr_eq(&held, &intro.pq),
                "issuing replaced the introducer's derived key — the identity must hold ONE key"
            );
            assert_eq!(cert.introducer_ml_dsa_pk, intro.ml_dsa_public_bytes());
        }
    }

    /// The one-shot constructors must remain equivalent to the held-identity path: this refactor
    /// changed WHEN the key is derived, never WHAT is signed or by which key.
    ///
    /// Byte-equality is NOT the claim and cannot be: `HandoffCertificate::create` draws a fresh
    /// random `nonce` per certificate and the ML-DSA half is hedged, so two certificates differ in
    /// both halves by construction. What must match is the IDENTITY — the presented ML-DSA public
    /// key — and that each certificate's own PQ half verifies under it.
    #[test]
    fn the_one_shot_and_the_held_identity_agree_on_the_key() {
        super::install_test_lattice_gate();
        let intro_sk = SigningKey::from_bytes(&[0x7b; 32]);
        let intro = HybridHandoffIdentity::new(SigningKey::from_bytes(&[0x7b; 32]));
        let recip_ml = MlDsaHandoffKey::from_ed25519_seed(&[0x7c; 32]).public_bytes();
        let intro_fed =
            FederationId::derive_hybrid(&intro.ed25519_public().0, intro.ml_dsa_public_bytes());

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(CellId([0xEE; 32]), AuthRequired::Signature, 100, None);

        let one_shot = HybridHandoffCertificate::create(
            &intro_sk,
            intro_fed,
            FederationId([0xDD; 32]),
            CellId([0xEE; 32]),
            [0x42; 32],
            AuthRequired::Signature,
            None,
            None,
            None,
            swiss,
            recip_ml.clone(),
        );
        let held = intro.issue_certificate(
            intro_fed,
            FederationId([0xDD; 32]),
            CellId([0xEE; 32]),
            [0x42; 32],
            AuthRequired::Signature,
            None,
            None,
            None,
            swiss,
            recip_ml,
        );

        assert_eq!(
            one_shot.introducer_ml_dsa_pk, held.introducer_ml_dsa_pk,
            "both paths must present the SAME derived ML-DSA identity"
        );
        assert_eq!(
            one_shot.introducer_ml_dsa_pk,
            intro.ml_dsa_public_bytes(),
            "and it must be the key the held identity actually carries"
        );
        assert_eq!(one_shot.recipient_ml_dsa_pk, held.recipient_ml_dsa_pk);
        // Each certificate's own PQ half must verify under that one key. The nonce differs between
        // them, so each is checked against its OWN signing message.
        for cert in [&one_shot, &held] {
            let msg = HybridHandoffCertificate::hybrid_signing_message(
                &cert.base,
                &cert.introducer_ml_dsa_pk,
                &cert.recipient_ml_dsa_pk,
            );
            assert!(hybrid_pq::ml_dsa_verify(
                &cert.introducer_ml_dsa_pk,
                &msg,
                &cert.introducer_ml_dsa_sig
            ));
            assert!(cert.base.verify_signature(&intro.ed25519_public()));
        }
    }
}

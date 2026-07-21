//! Canonical attestation envelope for the public output-boundary result.
//!
//! A receipt binds the protocol/session, ordered roster, public BFV identity,
//! ordered ciphertext/commitment digests, public clearing rule, strict
//! distributed-MPC transcript digest, and `(p*, V*)`. Verification reconstructs
//! that binding from independently supplied expected objects. The receipt is
//! therefore not allowed to define its own verification context.
//!
//! # Deliberate security boundary
//!
//! Canonical SHA-256 binding and [`DistributedTranscript::is_reveal_only`] prove
//! neither malicious MPC correctness nor that parties supplied authorized
//! inputs. [`ComputationIntegrityEvidence::BindingOnly`] names that residual and
//! can never pass [`AttestedClearingReceipt::verify_full`]. Full verification
//! requires a host-supplied [`ComputationIntegrityVerifier`] to validate external
//! evidence over the exact claim. The classical compatibility verifier signs its
//! SHA-256 digest; the native-PQ verifier signs a SHA-512 authority transcript
//! containing the full canonical claim. This module does not pretend that an
//! output-only self-assertion is a proof, signature, SNARK, or MPC MAC.
//!
//! [`DistributedTranscript::is_reveal_only`]: crate::mpc_party::DistributedTranscript::is_reveal_only

use std::collections::{BTreeSet, HashSet};
use std::fmt;

use dregg_pq::{ml_dsa_verify, MlDsaKey, ML_DSA_PK_LEN, ML_DSA_SIG_LEN};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use fhe_traits::Serialize as FheSerialize;
use sha2::{Digest, Sha256, Sha512};

use crate::bfv_lean::LeanCiphertext;
use crate::mpc::Crossing;
use crate::mpc_party::{DistributedTranscript, PartyMpcSession};
use crate::threshold::quorum::QuorumKeygenSession;
use crate::threshold::{BfvParams, CollectivePublicKey, KeygenSession};

/// Stable protocol discriminator. It is part of every claim and replay key.
pub const CLEARING_ATTESTATION_PROTOCOL_ID: [u8; 32] = *b"FHEGG-CLEARING-ATTESTATION-V1!!!";

/// The current public clearing rule: maximize `min(D[p], S[p])`, breaking ties
/// toward the lowest bucket, and publish only `(p*, V*)`.
pub const CLEARING_RULE_VERSION: u32 = 1;

pub type Digest32 = [u8; 32];

/// Full-width authority digest used by native-PQ clearing endorsements.
///
/// Its preimage contains the full canonical claim and raw enrolled key pairs,
/// rather than merely wrapping the classical 256-bit claim/verifier digests.
pub type NativePqAuthorityDigest = [u8; 64];

const PARTY_ID_DOMAIN: &[u8] = b"fhegg/attestation/party-id/v1";
const CIPHERTEXT_DOMAIN: &[u8] = b"fhegg/attestation/input-ciphertext/v1";
const MODULI_DOMAIN: &[u8] = b"fhegg/attestation/bfv-moduli/v1";
const PUBLIC_KEY_DOMAIN: &[u8] = b"fhegg/attestation/bfv-collective-pk/v1";
const ENCRYPTION_DOMAIN: &[u8] = b"fhegg/attestation/bfv-encryption-domain/v1";
const TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/attestation/distributed-transcript/v1";
const CLAIM_DOMAIN: &[u8] = b"fhegg/attestation/clearing-claim/v1";
const ENVELOPE_DOMAIN: &[u8] = b"fhegg/attestation/envelope/v1";
const REPLAY_DOMAIN: &[u8] = b"fhegg/attestation/replay-session/v1";
const QUORUM_ROSTER_DOMAIN: &[u8] = b"fhegg/attestation/quorum-roster/v1";
const QUORUM_VERIFIER_DOMAIN: &[u8] = b"fhegg/attestation/quorum-verifier/v1";
const QUORUM_SIGNATURE_DOMAIN: &[u8] = b"fhegg/attestation/quorum-signature/v1";
const QUORUM_EVIDENCE_VERSION: u8 = 1;
const NATIVE_PQ_PARTY_ID_DOMAIN: &[u8] = b"fhegg/attestation/native-pq-party-id/v1";
const NATIVE_PQ_QUORUM_ROSTER_DOMAIN: &[u8] = b"fhegg/attestation/native-pq-quorum-roster/v1";
const NATIVE_PQ_QUORUM_VERIFIER_DOMAIN: &[u8] = b"fhegg/attestation/native-pq-quorum-verifier/v1";
const NATIVE_PQ_QUORUM_SIGNATURE_DOMAIN: &[u8] = b"fhegg/attestation/native-pq-quorum-signature/v2";
const NATIVE_PQ_QUORUM_EVIDENCE_VERSION: u8 = 2;
/// FIPS 204 context for the ML-DSA half of a native-PQ clearing endorsement.
/// The separately domain-separated 512-bit authority message binds the exact
/// enrolled key-pair roster, threshold, and full canonical clearing claim.
pub const NATIVE_PQ_CLEARING_ML_DSA_CONTEXT: &[u8] = b"fhegg/clearing-quorum/native-pq/ml-dsa/v2";
const REPLAY_SNAPSHOT_MAGIC: &[u8; 8] = b"FHRSv001";
const REPLAY_SNAPSHOT_DOMAIN: &[u8] = b"fhegg/replay-snapshot/v1";
const MAX_REPLAY_SNAPSHOT_ENTRIES: usize = 1_000_000;

fn domain_digest(domain: &[u8], bytes: &[u8]) -> Digest32 {
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u64).to_be_bytes());
    hasher.update(domain);
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    hasher.finalize().into()
}

fn native_pq_authority_digest(domain: &[u8], bytes: &[u8]) -> NativePqAuthorityDigest {
    let mut hasher = Sha512::new();
    hasher.update((domain.len() as u64).to_be_bytes());
    hasher.update(domain);
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    hasher.finalize().into()
}

fn bfv_moduli_digest(params: &BfvParams) -> Digest32 {
    let mut moduli = CanonicalBytes::default();
    moduli.u64(params.moduli().len() as u64);
    for &modulus in params.moduli() {
        moduli.u64(modulus);
    }
    domain_digest(MODULI_DOMAIN, &moduli.finish())
}

fn bfv_public_key_digest(collective_public_key: &CollectivePublicKey) -> Digest32 {
    domain_digest(PUBLIC_KEY_DOMAIN, &collective_public_key.pk.to_bytes())
}

fn bfv_encryption_domain_digest(
    degree: u64,
    moduli_digest: &Digest32,
    plaintext_modulus: u64,
    collective_public_key_digest: &Digest32,
) -> Digest32 {
    let mut domain = CanonicalBytes::default();
    domain.u64(degree);
    domain.digest(moduli_digest);
    domain.u64(plaintext_modulus);
    domain.digest(collective_public_key_digest);
    domain_digest(ENCRYPTION_DOMAIN, &domain.finish())
}

#[derive(Default)]
struct CanonicalBytes(Vec<u8>);

impl CanonicalBytes {
    fn u8(&mut self, value: u8) {
        self.0.push(value);
    }

    fn u32(&mut self, value: u32) {
        self.0.extend_from_slice(&value.to_be_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_be_bytes());
    }

    fn digest(&mut self, value: &Digest32) {
        self.0.extend_from_slice(value);
    }

    fn bytes(&mut self, value: &[u8]) {
        self.u64(value.len() as u64);
        self.0.extend_from_slice(value);
    }

    fn finish(self) -> Vec<u8> {
        self.0
    }
}

/// Digest of an authenticated/public party identity, for example a transport
/// signing key. Only the digest is retained by the receipt, so raw identity
/// bytes cannot leak through `Debug` output.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PartyIdentity(pub Digest32);

impl PartyIdentity {
    pub fn from_public_identity_bytes(bytes: &[u8]) -> Self {
        Self(domain_digest(PARTY_ID_DOMAIN, bytes))
    }
}

/// Which externally retained input object an ordered digest identifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InputDigestKind {
    Ciphertext,
    Commitment,
}

/// One ordered input reference. The raw ciphertext/commitment preimage is not
/// stored, so deriving `Debug` cannot disclose it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InputDigest {
    pub kind: InputDigestKind,
    pub digest: Digest32,
}

impl InputDigest {
    /// Bind canonical fhe.rs ciphertext wire bytes.
    pub fn ciphertext(ciphertext: &LeanCiphertext) -> Self {
        Self::ciphertext_bytes(&ciphertext.to_fhe_bytes())
    }

    /// Bind externally retained canonical ciphertext bytes.
    pub fn ciphertext_bytes(bytes: &[u8]) -> Self {
        Self {
            kind: InputDigestKind::Ciphertext,
            digest: domain_digest(CIPHERTEXT_DOMAIN, bytes),
        }
    }

    /// Bind a commitment digest produced by the named upstream commitment
    /// scheme. The kind tag and enclosing claim domain separate it from a
    /// ciphertext digest; this function does not re-interpret the commitment.
    pub fn commitment(commitment_digest: Digest32) -> Self {
        Self {
            kind: InputDigestKind::Commitment,
            digest: commitment_digest,
        }
    }

    fn encode(&self, out: &mut CanonicalBytes) {
        out.u8(match self.kind {
            InputDigestKind::Ciphertext => 0,
            InputDigestKind::Commitment => 1,
        });
        out.digest(&self.digest);
    }
}

/// Public identity of the BFV key domain used by the folded input. It contains
/// parameters and public hashes only, never a secret key or decryption share.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BfvPublicIdentity {
    /// Total key-custody roster size fixed by distributed key generation.
    pub n_parties: u64,
    /// Number of live custody parties required for one opening.  This equals
    /// `n_parties` for the legacy n-of-n key and is strictly smaller for the
    /// crash-tolerant Shamir path.
    pub opening_threshold: u64,
    pub degree: u64,
    pub moduli_digest: Digest32,
    pub plaintext_modulus: u64,
    pub crp_seed: Digest32,
    pub collective_public_key_digest: Digest32,
}

impl BfvPublicIdentity {
    pub fn from_public(
        params: &BfvParams,
        keygen: &KeygenSession,
        collective_public_key: &CollectivePublicKey,
    ) -> Self {
        let moduli_digest = bfv_moduli_digest(params);
        let collective_public_key_digest = bfv_public_key_digest(collective_public_key);
        Self {
            n_parties: keygen.n_parties() as u64,
            opening_threshold: keygen.n_parties() as u64,
            degree: params.degree() as u64,
            moduli_digest,
            plaintext_modulus: params.plaintext_modulus(),
            crp_seed: keygen.crp_seed(),
            collective_public_key_digest,
        }
    }

    /// Canonical identity of exactly the BFV parameters and collective public
    /// key that determine encryption. Custody roster, threshold, and CRP remain
    /// separately bound by the full attestation identity.
    pub fn encryption_domain_digest(&self) -> Digest32 {
        bfv_encryption_domain_digest(
            self.degree,
            &self.moduli_digest,
            self.plaintext_modulus,
            &self.collective_public_key_digest,
        )
    }

    /// Construct the same encryption-domain identity directly from live BFV
    /// objects at encrypted-order ingress, before a complete custody identity
    /// is necessarily available.
    pub fn encryption_domain_digest_from_public(
        params: &BfvParams,
        collective_public_key: &CollectivePublicKey,
    ) -> Digest32 {
        bfv_encryption_domain_digest(
            params.degree() as u64,
            &bfv_moduli_digest(params),
            params.plaintext_modulus(),
            &bfv_public_key_digest(collective_public_key),
        )
    }

    /// Public identity for a crash-tolerant Shamir custody domain.
    pub fn from_quorum_public(
        params: &BfvParams,
        keygen: &QuorumKeygenSession,
        collective_public_key: &CollectivePublicKey,
    ) -> Self {
        let mut identity =
            Self::from_public(params, keygen.public_key_session(), collective_public_key);
        identity.opening_threshold = keygen.threshold() as u64;
        identity
    }

    fn encode(&self, out: &mut CanonicalBytes) {
        out.u64(self.n_parties);
        out.u64(self.opening_threshold);
        out.u64(self.degree);
        out.digest(&self.moduli_digest);
        out.u64(self.plaintext_modulus);
        out.digest(&self.crp_seed);
        out.digest(&self.collective_public_key_digest);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClearingTieBreak {
    LowestBucket,
}

/// Entire public rule/shape tuple. `buckets`, `value_bits`, and
/// `plaintext_modulus` are deliberately repeated here rather than inferred from
/// a transcript supplied by the receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicClearingRule {
    pub version: u32,
    pub buckets: u64,
    pub value_bits: u32,
    pub plaintext_modulus: u64,
    pub tie_break: ClearingTieBreak,
}

impl PublicClearingRule {
    fn for_session(session: &PartyMpcSession) -> Self {
        Self {
            version: CLEARING_RULE_VERSION,
            buckets: session.buckets() as u64,
            value_bits: session.value_bits() as u32,
            plaintext_modulus: session.plaintext_modulus(),
            tie_break: ClearingTieBreak::LowestBucket,
        }
    }

    fn encode(&self, out: &mut CanonicalBytes) {
        out.u32(self.version);
        out.u64(self.buckets);
        out.u32(self.value_bits);
        out.u64(self.plaintext_modulus);
        out.u8(match self.tie_break {
            ClearingTieBreak::LowestBucket => 0,
        });
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClearingOutcomeBinding {
    pub p_star: Option<u64>,
    pub v_star: u64,
}

impl ClearingOutcomeBinding {
    fn from_crossing(crossing: &Crossing) -> Self {
        Self {
            p_star: crossing.p_star.map(|p| p as u64),
            v_star: crossing.v_star,
        }
    }

    fn encode(&self, out: &mut CanonicalBytes) {
        match self.p_star {
            Some(p_star) => {
                out.u8(1);
                out.u64(p_star);
            }
            None => out.u8(0),
        }
        out.u64(self.v_star);
    }
}

/// All fields covered by computation-integrity evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClearingClaim {
    pub protocol_id: Digest32,
    pub session_nonce: Digest32,
    pub n_parties: u64,
    pub ordered_roster: Vec<PartyIdentity>,
    pub bfv: BfvPublicIdentity,
    pub ordered_inputs: Vec<InputDigest>,
    pub rule: PublicClearingRule,
    pub transcript_digest: Digest32,
    pub outcome: ClearingOutcomeBinding,
}

impl ClearingClaim {
    fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = CanonicalBytes::default();
        out.digest(&self.protocol_id);
        out.digest(&self.session_nonce);
        out.u64(self.n_parties);
        out.u64(self.ordered_roster.len() as u64);
        for identity in &self.ordered_roster {
            out.digest(&identity.0);
        }
        self.bfv.encode(&mut out);
        out.u64(self.ordered_inputs.len() as u64);
        for input in &self.ordered_inputs {
            input.encode(&mut out);
        }
        self.rule.encode(&mut out);
        out.digest(&self.transcript_digest);
        self.outcome.encode(&mut out);
        out.finish()
    }

    pub fn digest(&self) -> Digest32 {
        domain_digest(CLAIM_DOMAIN, &self.canonical_bytes())
    }
}

/// Honest residual carried by a receipt that has canonical binding but no
/// independently checked malicious-computation evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComputationIntegrityResidual {
    OutputOnlySelfAssertion,
}

/// A binding-only residual or externally verifiable public evidence. Merely
/// placing bytes in `External` proves nothing: [`verify_full`](AttestedClearingReceipt::verify_full)
/// calls a separately supplied verifier selected by the relying party.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComputationIntegrityEvidence {
    BindingOnly(ComputationIntegrityResidual),
    External {
        verifier_id: Digest32,
        evidence: Vec<u8>,
    },
}

impl ComputationIntegrityEvidence {
    fn encode(&self, out: &mut CanonicalBytes) {
        match self {
            Self::BindingOnly(ComputationIntegrityResidual::OutputOnlySelfAssertion) => {
                out.u8(0);
                out.u8(0);
            }
            Self::External {
                verifier_id,
                evidence,
            } => {
                out.u8(1);
                out.digest(verifier_id);
                out.bytes(evidence);
            }
        }
    }
}

/// Expected public objects are supplied independently by the verifier, not read
/// back from the receipt under test.
pub struct ExpectedClearingContext<'a> {
    pub session: &'a PartyMpcSession,
    pub ordered_roster: &'a [PartyIdentity],
    pub bfv: &'a BfvPublicIdentity,
    pub ordered_inputs: &'a [InputDigest],
    pub transcript: &'a DistributedTranscript,
    pub crossing: &'a Crossing,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AttestationError {
    InvalidRoster,
    EmptyInputBinding,
    BfvSessionMismatch,
    TranscriptNotRevealOnly,
    TranscriptOutputMismatch,
    InvalidOutput,
    BindingMismatch,
    ComputationIntegrityResidual(ComputationIntegrityResidual),
    IntegrityVerifierMismatch,
    InvalidComputationIntegrityEvidence,
    ReplayDetected,
}

impl fmt::Display for AttestationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "clearing attestation error: {self:?}")
    }
}

impl std::error::Error for AttestationError {}

pub type Result<T> = std::result::Result<T, AttestationError>;

/// Relying-party-selected verifier for a proof, threshold signature, MPC MAC
/// certificate, TEE quote, or another explicitly named integrity mechanism.
pub trait ComputationIntegrityVerifier {
    fn verifier_id(&self) -> Digest32;
    fn verify(&self, claim_digest: &Digest32, evidence: &[u8]) -> bool;

    /// Verify evidence against the full canonical claim. Digest-only mechanisms
    /// retain the default; roster-aware mechanisms override this to require the
    /// claim's declared roster to equal their configured key roster exactly.
    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        self.verify(&claim.digest(), evidence)
    }
}

/// Configuration/assembly failures for the authenticated quorum verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuorumVerifierError {
    EmptyRoster,
    RosterTooLarge { roster_len: usize },
    InvalidThreshold { threshold: usize, roster_len: usize },
    InvalidPublicKey { index: usize },
    DuplicatePublicKey { index: usize },
    UnknownSigner { index: usize },
    SignerKeyMismatch { index: usize },
    DuplicateSigner { index: usize },
    NonCanonicalSignerOrder,
    InsufficientSignatures { have: usize, need: usize },
    InvalidSignature { index: usize },
    InvalidPostQuantumPublicKey { index: usize, actual_len: usize },
    DuplicatePostQuantumPublicKey { index: usize },
    PostQuantumSignerKeyMismatch { index: usize },
    PostQuantumSigningFailed { index: usize },
    InvalidPostQuantumSignature { index: usize },
}

impl fmt::Display for QuorumVerifierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "authenticated clearing quorum error: {self:?}")
    }
}

impl std::error::Error for QuorumVerifierError {}

/// One party's strict Ed25519 endorsement of an exact clearing claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyClaimSignature {
    pub signer_index: u32,
    pub signature: [u8; 64],
}

/// Classical-compatibility computation-integrity verifier backed by a declared
/// ordered Ed25519 party roster and a `threshold`-of-`n` signature policy.
///
/// # Precise trust statement
///
/// Acceptance proves that at least `threshold` distinct keys from this exact
/// ordered roster endorsed the exact canonical [`ClearingClaim`] digest. It
/// authenticates attribution and quorum agreement; it is **not** by itself a
/// UC/malicious-MPC correctness proof. Interpreting acceptance as computation
/// correctness requires the deployment policy to ensure the accepted quorum
/// contains an honest party that verified the computation before signing.
/// This verifier is not post-quantum: native-PQ deployments must use
/// [`NativePqAuthenticatedQuorumVerifier`], which requires a roster-bound
/// ML-DSA signature alongside every counted Ed25519 signature.
#[derive(Clone, Debug)]
pub struct AuthenticatedQuorumVerifier {
    ordered_public_keys: Vec<[u8; 32]>,
    ordered_roster: Vec<PartyIdentity>,
    threshold: usize,
    roster_digest: Digest32,
    verifier_id: Digest32,
}

impl AuthenticatedQuorumVerifier {
    /// Construct the explicitly classical compatibility profile.
    pub fn new_classical_compatibility(
        ordered_public_keys: Vec<[u8; 32]>,
        threshold: usize,
    ) -> std::result::Result<Self, QuorumVerifierError> {
        Self::new(ordered_public_keys, threshold)
    }

    pub fn new(
        ordered_public_keys: Vec<[u8; 32]>,
        threshold: usize,
    ) -> std::result::Result<Self, QuorumVerifierError> {
        if ordered_public_keys.is_empty() {
            return Err(QuorumVerifierError::EmptyRoster);
        }
        if ordered_public_keys.len() > u32::MAX as usize {
            return Err(QuorumVerifierError::RosterTooLarge {
                roster_len: ordered_public_keys.len(),
            });
        }
        if threshold == 0 || threshold > ordered_public_keys.len() {
            return Err(QuorumVerifierError::InvalidThreshold {
                threshold,
                roster_len: ordered_public_keys.len(),
            });
        }
        let mut seen = HashSet::with_capacity(ordered_public_keys.len());
        let mut ordered_roster = Vec::with_capacity(ordered_public_keys.len());
        for (index, key) in ordered_public_keys.iter().enumerate() {
            let verifying_key = VerifyingKey::from_bytes(key)
                .map_err(|_| QuorumVerifierError::InvalidPublicKey { index })?;
            if verifying_key.is_weak() {
                return Err(QuorumVerifierError::InvalidPublicKey { index });
            }
            if !seen.insert(*key) {
                return Err(QuorumVerifierError::DuplicatePublicKey { index });
            }
            ordered_roster.push(PartyIdentity::from_public_identity_bytes(key));
        }

        let mut roster = CanonicalBytes::default();
        roster.u64(ordered_public_keys.len() as u64);
        for key in &ordered_public_keys {
            roster.bytes(key);
        }
        let roster_digest = domain_digest(QUORUM_ROSTER_DOMAIN, &roster.finish());
        let mut verifier = CanonicalBytes::default();
        verifier.digest(&roster_digest);
        verifier.u64(threshold as u64);
        let verifier_id = domain_digest(QUORUM_VERIFIER_DOMAIN, &verifier.finish());

        Ok(Self {
            ordered_public_keys,
            ordered_roster,
            threshold,
            roster_digest,
            verifier_id,
        })
    }

    pub fn ordered_roster(&self) -> &[PartyIdentity] {
        &self.ordered_roster
    }

    pub fn ordered_public_keys(&self) -> &[[u8; 32]] {
        &self.ordered_public_keys
    }

    pub fn threshold(&self) -> usize {
        self.threshold
    }

    pub fn roster_digest(&self) -> Digest32 {
        self.roster_digest
    }

    /// The exact domain-separated message every party signs.
    pub fn signing_message(&self, claim_digest: &Digest32) -> Digest32 {
        let mut message = CanonicalBytes::default();
        message.digest(&self.verifier_id);
        message.digest(&self.roster_digest);
        message.u64(self.threshold as u64);
        message.digest(claim_digest);
        domain_digest(QUORUM_SIGNATURE_DOMAIN, &message.finish())
    }

    /// Sign an exact claim as `signer_index`, refusing a secret key that does
    /// not correspond to that roster slot.
    pub fn sign_claim(
        &self,
        claim_digest: &Digest32,
        signer_index: usize,
        signing_key: &SigningKey,
    ) -> std::result::Result<PartyClaimSignature, QuorumVerifierError> {
        let expected = self.ordered_public_keys.get(signer_index).ok_or(
            QuorumVerifierError::UnknownSigner {
                index: signer_index,
            },
        )?;
        if signing_key.verifying_key().to_bytes() != *expected {
            return Err(QuorumVerifierError::SignerKeyMismatch {
                index: signer_index,
            });
        }
        Ok(PartyClaimSignature {
            signer_index: signer_index as u32,
            signature: signing_key
                .sign(&self.signing_message(claim_digest))
                .to_bytes(),
        })
    }

    /// Assemble canonical external evidence. Signatures must be in strictly
    /// increasing roster order; duplicates/reordering and sub-threshold sets
    /// fail before an envelope can be emitted.
    pub fn assemble_evidence(
        &self,
        claim_digest: &Digest32,
        signatures: &[PartyClaimSignature],
    ) -> std::result::Result<ComputationIntegrityEvidence, QuorumVerifierError> {
        self.verify_signatures(claim_digest, signatures)?;
        let mut evidence = CanonicalBytes::default();
        evidence.u8(QUORUM_EVIDENCE_VERSION);
        evidence.digest(&self.roster_digest);
        evidence.u32(self.threshold as u32);
        evidence.u32(signatures.len() as u32);
        for signature in signatures {
            evidence.u32(signature.signer_index);
            evidence.0.extend_from_slice(&signature.signature);
        }
        Ok(ComputationIntegrityEvidence::External {
            verifier_id: self.verifier_id,
            evidence: evidence.finish(),
        })
    }

    fn verify_signatures(
        &self,
        claim_digest: &Digest32,
        signatures: &[PartyClaimSignature],
    ) -> std::result::Result<(), QuorumVerifierError> {
        if signatures.len() < self.threshold {
            return Err(QuorumVerifierError::InsufficientSignatures {
                have: signatures.len(),
                need: self.threshold,
            });
        }
        if signatures.len() > self.ordered_public_keys.len() {
            return Err(QuorumVerifierError::UnknownSigner {
                index: self.ordered_public_keys.len(),
            });
        }
        let message = self.signing_message(claim_digest);
        let mut previous = None;
        for signature in signatures {
            let index = signature.signer_index as usize;
            if let Some(prior) = previous {
                if index == prior {
                    return Err(QuorumVerifierError::DuplicateSigner { index });
                }
                if index < prior {
                    return Err(QuorumVerifierError::NonCanonicalSignerOrder);
                }
            }
            previous = Some(index);
            let key = self
                .ordered_public_keys
                .get(index)
                .ok_or(QuorumVerifierError::UnknownSigner { index })?;
            let verifying_key = VerifyingKey::from_bytes(key)
                .map_err(|_| QuorumVerifierError::InvalidPublicKey { index })?;
            verifying_key
                .verify_strict(&message, &Signature::from_bytes(&signature.signature))
                .map_err(|_| QuorumVerifierError::InvalidSignature { index })?;
        }
        Ok(())
    }

    fn decode_and_verify(&self, claim_digest: &Digest32, evidence: &[u8]) -> bool {
        const HEADER_LEN: usize = 1 + 32 + 4 + 4;
        const RECORD_LEN: usize = 4 + 64;
        if evidence.len() < HEADER_LEN || evidence[0] != QUORUM_EVIDENCE_VERSION {
            return false;
        }
        let mut roster_digest = [0u8; 32];
        roster_digest.copy_from_slice(&evidence[1..33]);
        if roster_digest != self.roster_digest {
            return false;
        }
        let threshold = u32::from_be_bytes(evidence[33..37].try_into().expect("fixed width"));
        let count = u32::from_be_bytes(evidence[37..41].try_into().expect("fixed width")) as usize;
        let Some(expected_len) = count
            .checked_mul(RECORD_LEN)
            .and_then(|records_len| HEADER_LEN.checked_add(records_len))
        else {
            return false;
        };
        if threshold as usize != self.threshold
            || count < self.threshold
            || count > self.ordered_public_keys.len()
            || evidence.len() != expected_len
        {
            return false;
        }
        let mut signatures = Vec::with_capacity(count);
        for record in evidence[HEADER_LEN..].chunks_exact(RECORD_LEN) {
            let signer_index = u32::from_be_bytes(record[..4].try_into().expect("fixed width"));
            let mut signature = [0u8; 64];
            signature.copy_from_slice(&record[4..]);
            signatures.push(PartyClaimSignature {
                signer_index,
                signature,
            });
        }
        self.verify_signatures(claim_digest, &signatures).is_ok()
    }
}

/// Explicit name for the Ed25519-only compatibility verifier.  The historical
/// [`AuthenticatedQuorumVerifier`] name remains source-compatible, but callers
/// selecting a security profile should use this name so a classical receipt is
/// never mistaken for native-PQ evidence.
pub type ClassicalCompatibilityQuorumVerifier = AuthenticatedQuorumVerifier;

/// Explicit name for an Ed25519-only clearing endorsement.
pub type ClassicalCompatibilityPartyClaimSignature = PartyClaimSignature;

/// One roster slot in the native-PQ clearing quorum.  The two public keys are
/// enrolled as one indivisible identity: neither half is accepted from evidence
/// or from a self-carried claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePqPartyPublicKey {
    ed25519: [u8; 32],
    ml_dsa: Vec<u8>,
}

impl NativePqPartyPublicKey {
    pub fn new(ed25519: [u8; 32], ml_dsa: Vec<u8>) -> Self {
        Self { ed25519, ml_dsa }
    }

    pub fn ed25519(&self) -> &[u8; 32] {
        &self.ed25519
    }

    pub fn ml_dsa(&self) -> &[u8] {
        &self.ml_dsa
    }

    fn identity(&self) -> PartyIdentity {
        let mut identity = CanonicalBytes::default();
        identity.bytes(&self.ed25519);
        identity.bytes(&self.ml_dsa);
        PartyIdentity(domain_digest(NATIVE_PQ_PARTY_ID_DOMAIN, &identity.finish()))
    }
}

/// One party's paired endorsement.  A record counts toward the threshold only
/// when both signatures authenticate the same message at the same enrolled
/// roster index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePqPartyClaimSignature {
    pub signer_index: u32,
    pub ed25519_signature: [u8; 64],
    pub ml_dsa_signature: Vec<u8>,
}

/// Native-PQ computation-integrity verifier for a canonical clearing claim.
///
/// Each roster slot permanently pairs one Ed25519 public key with one ML-DSA-65
/// public key.  Acceptance requires `threshold` distinct, canonically ordered
/// slots, and every counted slot must supply **both** valid signatures over the
/// same domain-separated 512-bit authority message over the full claim and raw
/// roster. Consequently an attacker cannot satisfy the PQ half by attaching a
/// fresh self-chosen key to a forged classical identity, and the native path does
/// not inherit the 256-bit digest-only compatibility path's collision ceiling.
///
/// This authenticates quorum attribution/agreement.  As with the classical
/// verifier, malicious-computation correctness additionally relies on what the
/// endorsing parties checked before signing.
#[derive(Clone, Debug)]
pub struct NativePqAuthenticatedQuorumVerifier {
    ordered_public_keys: Vec<NativePqPartyPublicKey>,
    ordered_roster: Vec<PartyIdentity>,
    threshold: usize,
    roster_digest: Digest32,
    verifier_id: Digest32,
}

impl NativePqAuthenticatedQuorumVerifier {
    pub fn new(
        ordered_public_keys: Vec<NativePqPartyPublicKey>,
        threshold: usize,
    ) -> std::result::Result<Self, QuorumVerifierError> {
        if ordered_public_keys.is_empty() {
            return Err(QuorumVerifierError::EmptyRoster);
        }
        if ordered_public_keys.len() > u32::MAX as usize {
            return Err(QuorumVerifierError::RosterTooLarge {
                roster_len: ordered_public_keys.len(),
            });
        }
        if threshold == 0 || threshold > ordered_public_keys.len() {
            return Err(QuorumVerifierError::InvalidThreshold {
                threshold,
                roster_len: ordered_public_keys.len(),
            });
        }

        let mut seen_ed25519 = HashSet::with_capacity(ordered_public_keys.len());
        let mut seen_ml_dsa = HashSet::with_capacity(ordered_public_keys.len());
        let mut ordered_roster = Vec::with_capacity(ordered_public_keys.len());
        for (index, key_pair) in ordered_public_keys.iter().enumerate() {
            let verifying_key = VerifyingKey::from_bytes(&key_pair.ed25519)
                .map_err(|_| QuorumVerifierError::InvalidPublicKey { index })?;
            if verifying_key.is_weak() {
                return Err(QuorumVerifierError::InvalidPublicKey { index });
            }
            if !seen_ed25519.insert(key_pair.ed25519) {
                return Err(QuorumVerifierError::DuplicatePublicKey { index });
            }
            if key_pair.ml_dsa.len() != ML_DSA_PK_LEN {
                return Err(QuorumVerifierError::InvalidPostQuantumPublicKey {
                    index,
                    actual_len: key_pair.ml_dsa.len(),
                });
            }
            if !seen_ml_dsa.insert(key_pair.ml_dsa.clone()) {
                return Err(QuorumVerifierError::DuplicatePostQuantumPublicKey { index });
            }
            ordered_roster.push(key_pair.identity());
        }

        let mut roster = CanonicalBytes::default();
        roster.u64(ordered_public_keys.len() as u64);
        for key_pair in &ordered_public_keys {
            roster.bytes(&key_pair.ed25519);
            roster.bytes(&key_pair.ml_dsa);
        }
        let roster_digest = domain_digest(NATIVE_PQ_QUORUM_ROSTER_DOMAIN, &roster.finish());
        let mut verifier = CanonicalBytes::default();
        verifier.digest(&roster_digest);
        verifier.u64(threshold as u64);
        let verifier_id = domain_digest(NATIVE_PQ_QUORUM_VERIFIER_DOMAIN, &verifier.finish());

        Ok(Self {
            ordered_public_keys,
            ordered_roster,
            threshold,
            roster_digest,
            verifier_id,
        })
    }

    pub fn ordered_roster(&self) -> &[PartyIdentity] {
        &self.ordered_roster
    }

    pub fn ordered_public_keys(&self) -> &[NativePqPartyPublicKey] {
        &self.ordered_public_keys
    }

    pub fn threshold(&self) -> usize {
        self.threshold
    }

    pub fn roster_digest(&self) -> Digest32 {
        self.roster_digest
    }

    /// The single exact 512-bit authority message authenticated by both
    /// signature schemes.
    ///
    /// The SHA-512 preimage contains the raw enrolled key pairs and the full
    /// canonical claim. In particular, this must not accept `claim.digest()`:
    /// wrapping that 256-bit value would retain its generic quantum collision
    /// ceiling instead of providing a native-PQ authority boundary.
    pub fn signing_message(&self, claim: &ClearingClaim) -> NativePqAuthorityDigest {
        let mut message = CanonicalBytes::default();
        message.u8(NATIVE_PQ_QUORUM_EVIDENCE_VERSION);
        message.digest(&self.verifier_id);
        message.digest(&self.roster_digest);
        message.u64(self.ordered_public_keys.len() as u64);
        for key_pair in &self.ordered_public_keys {
            message.bytes(&key_pair.ed25519);
            message.bytes(&key_pair.ml_dsa);
        }
        message.u64(self.threshold as u64);
        message.bytes(&claim.canonical_bytes());
        native_pq_authority_digest(NATIVE_PQ_QUORUM_SIGNATURE_DOMAIN, &message.finish())
    }

    /// Produce one paired endorsement, refusing either secret key unless its
    /// public key equals the key enrolled at `signer_index`.
    pub fn sign_claim(
        &self,
        claim: &ClearingClaim,
        signer_index: usize,
        ed25519_signing_key: &SigningKey,
        ml_dsa_signing_key: &MlDsaKey,
    ) -> std::result::Result<NativePqPartyClaimSignature, QuorumVerifierError> {
        let expected = self.ordered_public_keys.get(signer_index).ok_or(
            QuorumVerifierError::UnknownSigner {
                index: signer_index,
            },
        )?;
        if ed25519_signing_key.verifying_key().to_bytes() != expected.ed25519 {
            return Err(QuorumVerifierError::SignerKeyMismatch {
                index: signer_index,
            });
        }
        if ml_dsa_signing_key.public_bytes() != expected.ml_dsa {
            return Err(QuorumVerifierError::PostQuantumSignerKeyMismatch {
                index: signer_index,
            });
        }
        let message = self.signing_message(claim);
        let ml_dsa_signature = ml_dsa_signing_key
            .try_sign(NATIVE_PQ_CLEARING_ML_DSA_CONTEXT, &message)
            .ok_or(QuorumVerifierError::PostQuantumSigningFailed {
                index: signer_index,
            })?;
        Ok(NativePqPartyClaimSignature {
            signer_index: signer_index as u32,
            ed25519_signature: ed25519_signing_key.sign(&message).to_bytes(),
            ml_dsa_signature,
        })
    }

    pub fn assemble_evidence(
        &self,
        claim: &ClearingClaim,
        signatures: &[NativePqPartyClaimSignature],
    ) -> std::result::Result<ComputationIntegrityEvidence, QuorumVerifierError> {
        self.verify_signatures(claim, signatures)?;
        let mut evidence = CanonicalBytes::default();
        evidence.u8(NATIVE_PQ_QUORUM_EVIDENCE_VERSION);
        evidence.digest(&self.roster_digest);
        evidence.u32(self.threshold as u32);
        evidence.u32(signatures.len() as u32);
        for signature in signatures {
            evidence.u32(signature.signer_index);
            evidence.0.extend_from_slice(&signature.ed25519_signature);
            evidence.bytes(&signature.ml_dsa_signature);
        }
        Ok(ComputationIntegrityEvidence::External {
            verifier_id: self.verifier_id,
            evidence: evidence.finish(),
        })
    }

    fn verify_signatures(
        &self,
        claim: &ClearingClaim,
        signatures: &[NativePqPartyClaimSignature],
    ) -> std::result::Result<(), QuorumVerifierError> {
        if signatures.len() < self.threshold {
            return Err(QuorumVerifierError::InsufficientSignatures {
                have: signatures.len(),
                need: self.threshold,
            });
        }
        if signatures.len() > self.ordered_public_keys.len() {
            return Err(QuorumVerifierError::UnknownSigner {
                index: self.ordered_public_keys.len(),
            });
        }
        let message = self.signing_message(claim);
        let mut previous = None;
        for signature in signatures {
            let index = signature.signer_index as usize;
            if let Some(prior) = previous {
                if index == prior {
                    return Err(QuorumVerifierError::DuplicateSigner { index });
                }
                if index < prior {
                    return Err(QuorumVerifierError::NonCanonicalSignerOrder);
                }
            }
            previous = Some(index);
            let key_pair = self
                .ordered_public_keys
                .get(index)
                .ok_or(QuorumVerifierError::UnknownSigner { index })?;
            let verifying_key = VerifyingKey::from_bytes(&key_pair.ed25519)
                .map_err(|_| QuorumVerifierError::InvalidPublicKey { index })?;
            verifying_key
                .verify_strict(
                    &message,
                    &Signature::from_bytes(&signature.ed25519_signature),
                )
                .map_err(|_| QuorumVerifierError::InvalidSignature { index })?;
            if !ml_dsa_verify(
                &key_pair.ml_dsa,
                NATIVE_PQ_CLEARING_ML_DSA_CONTEXT,
                &message,
                &signature.ml_dsa_signature,
            ) {
                return Err(QuorumVerifierError::InvalidPostQuantumSignature { index });
            }
        }
        Ok(())
    }

    fn decode_and_verify(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        const HEADER_LEN: usize = 1 + 32 + 4 + 4;
        const RECORD_LEN: usize = 4 + 64 + 8 + ML_DSA_SIG_LEN;
        if evidence.len() < HEADER_LEN || evidence[0] != NATIVE_PQ_QUORUM_EVIDENCE_VERSION {
            return false;
        }
        let mut roster_digest = [0u8; 32];
        roster_digest.copy_from_slice(&evidence[1..33]);
        if roster_digest != self.roster_digest {
            return false;
        }
        let threshold = u32::from_be_bytes(evidence[33..37].try_into().expect("fixed width"));
        let count = u32::from_be_bytes(evidence[37..41].try_into().expect("fixed width")) as usize;
        let Some(expected_len) = count
            .checked_mul(RECORD_LEN)
            .and_then(|records_len| HEADER_LEN.checked_add(records_len))
        else {
            return false;
        };
        if threshold as usize != self.threshold
            || count < self.threshold
            || count > self.ordered_public_keys.len()
            || evidence.len() != expected_len
        {
            return false;
        }

        let mut signatures = Vec::with_capacity(count);
        for record in evidence[HEADER_LEN..].chunks_exact(RECORD_LEN) {
            let signer_index = u32::from_be_bytes(record[..4].try_into().expect("fixed width"));
            let mut ed25519_signature = [0u8; 64];
            ed25519_signature.copy_from_slice(&record[4..68]);
            let ml_dsa_len =
                u64::from_be_bytes(record[68..76].try_into().expect("fixed width")) as usize;
            if ml_dsa_len != ML_DSA_SIG_LEN {
                return false;
            }
            signatures.push(NativePqPartyClaimSignature {
                signer_index,
                ed25519_signature,
                ml_dsa_signature: record[76..].to_vec(),
            });
        }
        self.verify_signatures(claim, &signatures).is_ok()
    }
}

impl ComputationIntegrityVerifier for NativePqAuthenticatedQuorumVerifier {
    fn verifier_id(&self) -> Digest32 {
        self.verifier_id
    }

    fn verify(&self, _claim_digest: &Digest32, _evidence: &[u8]) -> bool {
        // Native-PQ evidence deliberately has no digest-only verification path:
        // accepting a 256-bit claim digest here would reintroduce the authority
        // bottleneck this verifier exists to remove. `verify_full` dispatches to
        // `verify_claim`, which supplies the full canonical claim.
        false
    }

    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        claim.n_parties == self.ordered_roster.len() as u64
            && claim.ordered_roster == self.ordered_roster
            && self.decode_and_verify(claim, evidence)
    }
}

impl ComputationIntegrityVerifier for AuthenticatedQuorumVerifier {
    fn verifier_id(&self) -> Digest32 {
        self.verifier_id
    }

    fn verify(&self, claim_digest: &Digest32, evidence: &[u8]) -> bool {
        self.decode_and_verify(claim_digest, evidence)
    }

    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        claim.n_parties == self.ordered_roster.len() as u64
            && claim.ordered_roster == self.ordered_roster
            && self.decode_and_verify(&claim.digest(), evidence)
    }
}

/// Stateful replay gate. Durable deployments should implement this against
/// persistent transactional storage; [`InMemoryReplayGuard`] is process-local.
pub trait ReplayGuard {
    /// Atomically return `true` and record a fresh id, or return `false` if it
    /// has already been accepted.
    fn check_and_record(&mut self, replay_id: Digest32) -> bool;
}

#[derive(Clone, Default)]
pub struct InMemoryReplayGuard {
    seen: HashSet<Digest32>,
}

impl ReplayGuard for InMemoryReplayGuard {
    fn check_and_record(&mut self, replay_id: Digest32) -> bool {
        self.seen.insert(replay_id)
    }
}

/// Strict restart snapshot for a replay guard.
///
/// The caller chooses a public `context` (for example a game/session or
/// verifier-configuration digest), persists [`to_wire_bytes`](Self::to_wire_bytes)
/// in the same transaction as the authorized mutation, and restores it with
/// [`from_wire_bytes`](Self::from_wire_bytes). The canonical checksum detects
/// corruption and context confusion; it is not a MAC and cannot prevent a
/// storage operator from rolling back to an older valid snapshot. Production
/// rollback resistance still requires monotonic or consensus-backed storage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotReplayGuard {
    context: Digest32,
    revision: u64,
    seen: BTreeSet<Digest32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplaySnapshotError {
    MalformedWire,
    ContextMismatch,
    TooManyEntries,
    NonCanonicalOrder,
    ChecksumMismatch,
}

impl fmt::Display for ReplaySnapshotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "replay snapshot error: {self:?}")
    }
}

impl std::error::Error for ReplaySnapshotError {}

impl SnapshotReplayGuard {
    pub fn new(context: Digest32) -> Self {
        Self {
            context,
            revision: 0,
            seen: BTreeSet::new(),
        }
    }

    pub fn context(&self) -> Digest32 {
        self.context
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    pub fn len(&self) -> usize {
        self.seen.len()
    }

    pub fn is_empty(&self) -> bool {
        self.seen.is_empty()
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + 32 + 8 + 8 + self.seen.len() * 32 + 32);
        out.extend_from_slice(REPLAY_SNAPSHOT_MAGIC);
        out.extend_from_slice(&self.context);
        out.extend_from_slice(&self.revision.to_be_bytes());
        out.extend_from_slice(&(self.seen.len() as u64).to_be_bytes());
        for replay_id in &self.seen {
            out.extend_from_slice(replay_id);
        }
        let checksum = domain_digest(REPLAY_SNAPSHOT_DOMAIN, &out);
        out.extend_from_slice(&checksum);
        out
    }

    pub fn from_wire_bytes(
        expected_context: Digest32,
        bytes: &[u8],
    ) -> std::result::Result<Self, ReplaySnapshotError> {
        const HEADER: usize = 8 + 32 + 8 + 8;
        const CHECKSUM: usize = 32;
        if bytes.len() < HEADER + CHECKSUM || bytes[..8] != *REPLAY_SNAPSHOT_MAGIC {
            return Err(ReplaySnapshotError::MalformedWire);
        }
        let context: Digest32 = bytes[8..40]
            .try_into()
            .map_err(|_| ReplaySnapshotError::MalformedWire)?;
        if context != expected_context {
            return Err(ReplaySnapshotError::ContextMismatch);
        }
        let revision = u64::from_be_bytes(
            bytes[40..48]
                .try_into()
                .map_err(|_| ReplaySnapshotError::MalformedWire)?,
        );
        let count_u64 = u64::from_be_bytes(
            bytes[48..56]
                .try_into()
                .map_err(|_| ReplaySnapshotError::MalformedWire)?,
        );
        let count = usize::try_from(count_u64).map_err(|_| ReplaySnapshotError::TooManyEntries)?;
        if count > MAX_REPLAY_SNAPSHOT_ENTRIES {
            return Err(ReplaySnapshotError::TooManyEntries);
        }
        let expected_len = count
            .checked_mul(32)
            .and_then(|entries| HEADER.checked_add(entries))
            .and_then(|body| body.checked_add(CHECKSUM))
            .ok_or(ReplaySnapshotError::TooManyEntries)?;
        if bytes.len() != expected_len || revision != count_u64 {
            return Err(ReplaySnapshotError::MalformedWire);
        }
        let body_end = expected_len - CHECKSUM;
        let expected_checksum = domain_digest(REPLAY_SNAPSHOT_DOMAIN, &bytes[..body_end]);
        if bytes[body_end..] != expected_checksum {
            return Err(ReplaySnapshotError::ChecksumMismatch);
        }
        let mut seen = BTreeSet::new();
        let mut previous: Option<Digest32> = None;
        for chunk in bytes[HEADER..body_end].chunks_exact(32) {
            let replay_id: Digest32 = chunk
                .try_into()
                .map_err(|_| ReplaySnapshotError::MalformedWire)?;
            if previous.is_some_and(|prior| prior >= replay_id) || !seen.insert(replay_id) {
                return Err(ReplaySnapshotError::NonCanonicalOrder);
            }
            previous = Some(replay_id);
        }
        Ok(Self {
            context,
            revision,
            seen,
        })
    }

    pub fn snapshot_digest(&self) -> Digest32 {
        domain_digest(REPLAY_SNAPSHOT_DOMAIN, &self.to_wire_bytes())
    }
}

impl ReplayGuard for SnapshotReplayGuard {
    fn check_and_record(&mut self, replay_id: Digest32) -> bool {
        if self.seen.contains(&replay_id) || self.revision == u64::MAX {
            return false;
        }
        self.seen.insert(replay_id);
        self.revision += 1;
        true
    }
}

/// Canonical envelope. Fields remain public for transport adapters; security
/// comes from independent reconstruction plus digest/evidence verification, not
/// Rust field privacy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestedClearingReceipt {
    pub claim: ClearingClaim,
    pub computation_integrity: ComputationIntegrityEvidence,
}

impl AttestedClearingReceipt {
    pub fn issue(
        context: &ExpectedClearingContext<'_>,
        computation_integrity: ComputationIntegrityEvidence,
    ) -> Result<Self> {
        Ok(Self {
            claim: claim_from_context(context)?,
            computation_integrity,
        })
    }

    pub fn claim_digest(&self) -> Digest32 {
        self.claim.digest()
    }

    pub fn canonical_envelope_bytes(&self) -> Vec<u8> {
        let mut out = CanonicalBytes::default();
        out.bytes(&self.claim.canonical_bytes());
        self.computation_integrity.encode(&mut out);
        out.finish()
    }

    pub fn envelope_digest(&self) -> Digest32 {
        domain_digest(ENVELOPE_DOMAIN, &self.canonical_envelope_bytes())
    }

    /// Check the complete binding and strict reveal/output schema. This does not
    /// upgrade a binding-only receipt into a malicious-correctness attestation.
    pub fn verify_binding(&self, expected: &ExpectedClearingContext<'_>) -> Result<()> {
        let expected_claim = claim_from_context(expected)?;
        if self.claim != expected_claim {
            return Err(AttestationError::BindingMismatch);
        }
        Ok(())
    }

    /// Full verification is deliberately stricter than binding verification:
    /// external evidence must verify against the exact claim, then the protocol
    /// session is consumed by the replay guard. Failed evidence never burns a
    /// replay id.
    pub fn verify_full<V: ComputationIntegrityVerifier, R: ReplayGuard>(
        &self,
        expected: &ExpectedClearingContext<'_>,
        verifier: &V,
        replay_guard: &mut R,
    ) -> Result<()> {
        self.verify_binding(expected)?;
        let (verifier_id, evidence) = match &self.computation_integrity {
            ComputationIntegrityEvidence::BindingOnly(residual) => {
                return Err(AttestationError::ComputationIntegrityResidual(*residual));
            }
            ComputationIntegrityEvidence::External {
                verifier_id,
                evidence,
            } => (verifier_id, evidence),
        };
        if verifier_id != &verifier.verifier_id() {
            return Err(AttestationError::IntegrityVerifierMismatch);
        }
        if !verifier.verify_claim(&self.claim, evidence) {
            return Err(AttestationError::InvalidComputationIntegrityEvidence);
        }
        if !replay_guard.check_and_record(self.replay_id()) {
            return Err(AttestationError::ReplayDetected);
        }
        Ok(())
    }

    fn replay_id(&self) -> Digest32 {
        let mut bytes = CanonicalBytes::default();
        bytes.digest(&self.claim.protocol_id);
        bytes.digest(&self.claim.session_nonce);
        domain_digest(REPLAY_DOMAIN, &bytes.finish())
    }
}

fn claim_from_context(context: &ExpectedClearingContext<'_>) -> Result<ClearingClaim> {
    validate_context(context)?;
    Ok(ClearingClaim {
        protocol_id: CLEARING_ATTESTATION_PROTOCOL_ID,
        session_nonce: context.session.nonce(),
        n_parties: context.session.n_parties() as u64,
        ordered_roster: context.ordered_roster.to_vec(),
        bfv: context.bfv.clone(),
        ordered_inputs: context.ordered_inputs.to_vec(),
        rule: PublicClearingRule::for_session(context.session),
        transcript_digest: transcript_digest(context.transcript),
        outcome: ClearingOutcomeBinding::from_crossing(context.crossing),
    })
}

fn validate_context(context: &ExpectedClearingContext<'_>) -> Result<()> {
    if context.ordered_roster.len() != context.session.n_parties()
        || context
            .ordered_roster
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != context.ordered_roster.len()
    {
        return Err(AttestationError::InvalidRoster);
    }
    if context.ordered_inputs.is_empty() {
        return Err(AttestationError::EmptyInputBinding);
    }
    if context.bfv.opening_threshold != context.session.n_parties() as u64
        || context.bfv.opening_threshold == 0
        || context.bfv.opening_threshold > context.bfv.n_parties
        || context.bfv.plaintext_modulus != context.session.plaintext_modulus()
    {
        return Err(AttestationError::BfvSessionMismatch);
    }
    if !context.transcript.is_reveal_only(context.session) {
        return Err(AttestationError::TranscriptNotRevealOnly);
    }
    validate_output(context.session, context.crossing)?;
    if !transcript_matches_crossing(context.transcript, context.crossing) {
        return Err(AttestationError::TranscriptOutputMismatch);
    }
    Ok(())
}

fn validate_output(session: &PartyMpcSession, crossing: &Crossing) -> Result<()> {
    match crossing.p_star {
        Some(p_star) if p_star < session.buckets() && crossing.v_star != 0 => {}
        None if crossing.v_star == 0 => {}
        _ => return Err(AttestationError::InvalidOutput),
    }
    let limit = 1u64 << session.value_bits();
    if crossing.v_star >= limit || crossing.v_star >= session.plaintext_modulus() {
        return Err(AttestationError::InvalidOutput);
    }
    Ok(())
}

fn bits_value(bits: &[u8]) -> Option<u64> {
    bits.iter()
        .enumerate()
        .try_fold(0u64, |value, (bit, &set)| {
            (set <= 1).then_some(value | (u64::from(set) << bit))
        })
}

fn transcript_matches_crossing(transcript: &DistributedTranscript, crossing: &Crossing) -> bool {
    let Some(revealed_pstar) = bits_value(&transcript.revealed_pstar) else {
        return false;
    };
    let Some(revealed_vstar) = bits_value(&transcript.revealed_vstar) else {
        return false;
    };
    let expected_pstar = crossing.p_star.map_or(0, |p| p as u64);
    revealed_pstar == expected_pstar && revealed_vstar == crossing.v_star
}

fn transcript_digest(transcript: &DistributedTranscript) -> Digest32 {
    let mut out = CanonicalBytes::default();
    out.u64(transcript.masked.len() as u64);
    for opening in &transcript.masked {
        out.u64(opening.gate as u64);
        out.u8(opening.d);
        out.u8(opening.e);
    }
    out.bytes(&transcript.revealed_pstar);
    out.bytes(&transcript.revealed_vstar);
    out.u64(transcript.and_gates as u64);
    out.u64(transcript.scalar_opening_rounds as u64);
    out.u64(transcript.modeled_batched_rounds as u64);
    out.u64(transcript.gate_share_messages as u64);
    out.u64(transcript.output_share_messages as u64);
    domain_digest(TRANSCRIPT_DOMAIN, &out.finish())
}

//! One receipt that is both quorum-authenticated and privately proved.
//!
//! fhegg-fhe's canonical [`ClearingClaim`] deliberately carries a single
//! [`ComputationIntegrityEvidence`] value.  A plain quorum verifier proves who
//! endorsed the claim but not the clearing computation; a plain HidingFRI
//! verifier proves the fixed private-book relation but not who authorized the
//! claimed FHE/session boundary.  [`PrivateAttestedClearingVerifier`] composes
//! both checks into one relying-party-selected verifier and one replay-protected
//! receipt. Neither half can be omitted or substituted.
//!
//! The proved relation is the Lean-emitted fixed `N=4,K=4` program: the witness
//! contains hidden `(side, limit, quantity)` orders and a hiding blind; the
//! public statement contains only a session felt, rule id, faithful eight-felt
//! order root, and exact lowest-argmax `(p*, V*)`.  The statement is derived from
//! and checked against the canonical fhEgg claim rather than trusted from proof
//! bytes.
//!
//! # Exact remaining boundary
//!
//! Acceptance proves all of the following in one evidence object:
//!
//! * the configured threshold of the exact ordered roster signed the complete
//!   canonical claim (including every ciphertext/commitment digest);
//! * the fixed four-order family carries exactly four ordered ciphertext rows
//!   followed by exactly one commitment to the proved private-book root;
//! * the HidingFRI proof verifies that `(p*, V*)` is the fixed rule's result for
//!   some private book opening that root; and
//! * session, rule, root, price, and volume agree across proof and claim.
//!
//! It does **not** yet prove that the separately listed BFV ciphertext digests
//! encrypt that same private book.  Quorum co-endorsement is not a lattice
//! same-opening proof.  Until the BFV-to-root relation is added, this is a real
//! private-computation proof plus authenticated claim composition, not the final
//! Tier-0/no-single-viewer apex.

use std::fmt;

use dregg_circuit_prove::dark_bazaar_private::{self, DarkBazaarPrivateZkProof, PublicStatement};
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, CLEARING_ATTESTATION_PROTOCOL_ID, CLEARING_RULE_VERSION,
    ClearingClaim, ClearingTieBreak, ComputationIntegrityEvidence, ComputationIntegrityVerifier,
    Digest32, InputDigestKind, PartyClaimSignature, QuorumVerifierError,
};

const EVIDENCE_MAGIC: &[u8; 8] = b"DBAPv001";
const EVIDENCE_VERSION: u32 = 1;
const BABYBEAR_P: u64 = 2_013_265_921;
const MIN_VOLUME_BITS: u32 = 6;
const MAX_QUORUM_EVIDENCE_BYTES: usize = 1 << 20;
const MAX_PROOF_BYTES: usize = 64 << 20;
const ROOT_COMMITMENT_DOMAIN: &str = "dreggnet-market/private-book-root/v1";
const CLAIM_SESSION_DOMAIN: &str = "dreggnet-market/private-claim-session/v1";
const VERIFIER_ID_DOMAIN: &str = "dreggnet-market/private-attested-verifier/v1";
const EVIDENCE_CHECKSUM_DOMAIN: &str = "dreggnet-market/private-attested-evidence/v1";

/// Stable commitment digest placed in the canonical claim for the exact
/// eight-felt public root. Every felt is encoded as fixed-width big-endian bytes;
/// no lossy 256-to-field fold occurs here.
pub fn private_order_root_commitment(
    order_root: [u32; dark_bazaar_private::DIGEST_WIDTH],
) -> Digest32 {
    let mut hasher = blake3::Hasher::new_derive_key(ROOT_COMMITMENT_DOMAIN);
    for lane in order_root {
        hasher.update(&lane.to_be_bytes());
    }
    *hasher.finalize().as_bytes()
}

/// Injectively encode one canonical BabyBear session felt as the full fhEgg
/// replay nonce. This is available before receipt assembly, allowing a producer
/// to compute the proof/root first and then include that root in the claim
/// without a circular claim-digest dependency.
pub fn private_claim_session_nonce(session: u32) -> Option<Digest32> {
    if session as u64 >= BABYBEAR_P {
        return None;
    }
    let mut nonce = [0u8; 32];
    nonce[..4].copy_from_slice(&session.to_be_bytes());
    let mut hasher = blake3::Hasher::new_derive_key(CLAIM_SESSION_DOMAIN);
    hasher.update(&CLEARING_ATTESTATION_PROTOCOL_ID);
    hasher.update(&session.to_be_bytes());
    let digest = hasher.finalize();
    nonce[4..].copy_from_slice(&digest.as_bytes()[..28]);
    Some(nonce)
}

/// Decode only the injective canonical nonce image above. The fixed circuit has
/// one BabyBear session input and therefore cannot faithfully compress an
/// arbitrary 256-bit nonce. Refusing every other nonce prevents two full replay
/// ids from aliasing to one private proof; a future wider descriptor can remove
/// this fixed-family restriction by publishing a faithful multi-limb nonce.
pub fn private_claim_session_felt(session_nonce: Digest32) -> Option<u32> {
    let session = u32::from_be_bytes(session_nonce[..4].try_into().ok()?);
    (private_claim_session_nonce(session)? == session_nonce).then_some(session)
}

/// Exact fhEgg rule shape selected independently by the relying party. The
/// private circuit proves integer clearing, while this policy prevents the same
/// evidence from being silently reinterpreted under another MPC bit width or
/// plaintext modulus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateAttestedClearingPolicy {
    value_bits: u32,
    bfv: fhegg_fhe::attestation::BfvPublicIdentity,
}

impl PrivateAttestedClearingPolicy {
    pub fn new(
        value_bits: u32,
        bfv: fhegg_fhe::attestation::BfvPublicIdentity,
    ) -> Result<Self, PrivateAttestedVerifierConfigError> {
        let range = 1u64
            .checked_shl(value_bits)
            .ok_or(PrivateAttestedVerifierConfigError::InvalidRuleShape)?;
        if value_bits < MIN_VOLUME_BITS
            || bfv.plaintext_modulus < range
            || bfv.degree == 0
            || bfv.n_parties == 0
            || bfv.opening_threshold == 0
            || bfv.opening_threshold > bfv.n_parties
        {
            return Err(PrivateAttestedVerifierConfigError::InvalidRuleShape);
        }
        Ok(Self { value_bits, bfv })
    }

    pub const fn value_bits(&self) -> u32 {
        self.value_bits
    }

    pub const fn plaintext_modulus(&self) -> u64 {
        self.bfv.plaintext_modulus
    }

    pub const fn bfv(&self) -> &fhegg_fhe::attestation::BfvPublicIdentity {
        &self.bfv
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateAttestedVerifierConfigError {
    InvalidRuleShape,
}

impl fmt::Display for PrivateAttestedVerifierConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid fixed private-clearing rule policy")
    }
}

impl std::error::Error for PrivateAttestedVerifierConfigError {}

/// Assembly errors are kept separate from receipt verification: a producer may
/// never emit a composite envelope whose two components do not already verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateAttestedEvidenceError {
    ClaimMismatch(&'static str),
    Quorum(QuorumVerifierError),
    PrivateProof(String),
    EvidenceTooLarge,
}

impl fmt::Display for PrivateAttestedEvidenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ClaimMismatch(reason) => write!(f, "private proof/claim mismatch: {reason}"),
            Self::Quorum(error) => write!(f, "quorum evidence refused: {error}"),
            Self::PrivateProof(error) => write!(f, "private clearing proof refused: {error}"),
            Self::EvidenceTooLarge => write!(f, "private attested evidence exceeds wire bounds"),
        }
    }
}

impl std::error::Error for PrivateAttestedEvidenceError {}

/// Relying-party policy requiring both an exact authenticated quorum and the
/// installed fixed private-clearing verifier.
#[derive(Clone, Debug)]
pub struct PrivateAttestedClearingVerifier {
    quorum: AuthenticatedQuorumVerifier,
    policy: PrivateAttestedClearingPolicy,
    verifier_id: Digest32,
}

impl PrivateAttestedClearingVerifier {
    pub fn new(quorum: AuthenticatedQuorumVerifier, policy: PrivateAttestedClearingPolicy) -> Self {
        let mut hasher = blake3::Hasher::new_derive_key(VERIFIER_ID_DOMAIN);
        hasher.update(EVIDENCE_MAGIC);
        hasher.update(&EVIDENCE_VERSION.to_be_bytes());
        hasher.update(&ComputationIntegrityVerifier::verifier_id(&quorum));
        hasher.update(CLAIM_SESSION_DOMAIN.as_bytes());
        hasher.update(ROOT_COMMITMENT_DOMAIN.as_bytes());
        hasher.update(EVIDENCE_CHECKSUM_DOMAIN.as_bytes());
        hasher.update(&CLEARING_ATTESTATION_PROTOCOL_ID);
        hasher.update(&CLEARING_RULE_VERSION.to_be_bytes());
        hasher.update(&dark_bazaar_private::RULE_ID.to_be_bytes());
        hasher.update(&(dark_bazaar_private::PRICE_COUNT as u64).to_be_bytes());
        hasher.update(&MIN_VOLUME_BITS.to_be_bytes());
        hasher.update(&policy.value_bits.to_be_bytes());
        hasher.update(&policy.bfv.n_parties.to_be_bytes());
        hasher.update(&policy.bfv.opening_threshold.to_be_bytes());
        hasher.update(&policy.bfv.degree.to_be_bytes());
        hasher.update(&policy.bfv.moduli_digest);
        hasher.update(&policy.bfv.plaintext_modulus.to_be_bytes());
        hasher.update(&policy.bfv.crp_seed);
        hasher.update(&policy.bfv.collective_public_key_digest);
        hasher.update(&(MAX_QUORUM_EVIDENCE_BYTES as u64).to_be_bytes());
        hasher.update(&(MAX_PROOF_BYTES as u64).to_be_bytes());
        hasher.update(dark_bazaar_private::DARK_BAZAAR_PRIVATE_DESCRIPTOR_JSON.as_bytes());
        let verifier_id = *hasher.finalize().as_bytes();
        Self {
            quorum,
            policy,
            verifier_id,
        }
    }

    pub fn quorum(&self) -> &AuthenticatedQuorumVerifier {
        &self.quorum
    }

    /// Assemble one canonical external-evidence value. The proof and quorum
    /// signatures are checked before bytes are returned; receipt verification
    /// repeats both checks against its independently reconstructed claim.
    pub fn assemble_evidence(
        &self,
        claim: &ClearingClaim,
        signatures: &[PartyClaimSignature],
        proof: &DarkBazaarPrivateZkProof,
        statement: PublicStatement,
    ) -> Result<ComputationIntegrityEvidence, PrivateAttestedEvidenceError> {
        statement_matches_claim(&self.policy, claim, statement)
            .map_err(PrivateAttestedEvidenceError::ClaimMismatch)?;
        dark_bazaar_private::verify_zk(proof, statement)
            .map_err(PrivateAttestedEvidenceError::PrivateProof)?;

        let quorum_evidence = match self
            .quorum
            .assemble_evidence(&claim.digest(), signatures)
            .map_err(PrivateAttestedEvidenceError::Quorum)?
        {
            ComputationIntegrityEvidence::External { evidence, .. } => evidence,
            ComputationIntegrityEvidence::BindingOnly(_) => unreachable!("quorum is external"),
        };
        let proof_bytes = proof
            .to_postcard()
            .map_err(PrivateAttestedEvidenceError::PrivateProof)?;
        if quorum_evidence.len() > MAX_QUORUM_EVIDENCE_BYTES || proof_bytes.len() > MAX_PROOF_BYTES
        {
            return Err(PrivateAttestedEvidenceError::EvidenceTooLarge);
        }

        let body_len =
            EVIDENCE_MAGIC.len() + 4 + 12 * 4 + 4 + 4 + quorum_evidence.len() + proof_bytes.len();
        let mut evidence = Vec::with_capacity(body_len + 32);
        evidence.extend_from_slice(EVIDENCE_MAGIC);
        evidence.extend_from_slice(&EVIDENCE_VERSION.to_be_bytes());
        encode_statement(&mut evidence, statement);
        evidence.extend_from_slice(&(quorum_evidence.len() as u32).to_be_bytes());
        evidence.extend_from_slice(&(proof_bytes.len() as u32).to_be_bytes());
        evidence.extend_from_slice(&quorum_evidence);
        evidence.extend_from_slice(&proof_bytes);
        let checksum = blake3::Hasher::new_derive_key(EVIDENCE_CHECKSUM_DOMAIN)
            .update(&evidence)
            .finalize();
        evidence.extend_from_slice(checksum.as_bytes());

        Ok(ComputationIntegrityEvidence::External {
            verifier_id: self.verifier_id,
            evidence,
        })
    }

    fn verify_composite(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        let Some((statement, quorum_evidence, proof_bytes)) = decode_evidence(evidence) else {
            return false;
        };
        if statement_matches_claim(&self.policy, claim, statement).is_err()
            || !self.quorum.verify_claim(claim, quorum_evidence)
        {
            return false;
        }
        let Ok(proof) = DarkBazaarPrivateZkProof::from_postcard(proof_bytes) else {
            return false;
        };
        if proof.to_postcard().as_deref() != Ok(proof_bytes) {
            return false;
        }
        dark_bazaar_private::verify_zk(&proof, statement).is_ok()
    }
}

impl ComputationIntegrityVerifier for PrivateAttestedClearingVerifier {
    fn verifier_id(&self) -> Digest32 {
        self.verifier_id
    }

    fn verify(&self, _claim_digest: &Digest32, _evidence: &[u8]) -> bool {
        // Digest-only verification cannot check roster, rule shape, root
        // placement, or output equality. The full-claim entrypoint is required.
        false
    }

    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        self.verify_composite(claim, evidence)
    }
}

fn statement_matches_claim(
    policy: &PrivateAttestedClearingPolicy,
    claim: &ClearingClaim,
    statement: PublicStatement,
) -> Result<(), &'static str> {
    if claim.protocol_id != CLEARING_ATTESTATION_PROTOCOL_ID {
        return Err("protocol id is not fhEgg clearing v1");
    }
    if private_claim_session_felt(claim.session_nonce) != Some(statement.session) {
        return Err("claim nonce is not the canonical injective image of the proof session");
    }
    if statement.rule != dark_bazaar_private::RULE_ID {
        return Err("proof rule id is not the installed private family");
    }
    if claim.rule.version != CLEARING_RULE_VERSION
        || claim.rule.buckets != dark_bazaar_private::PRICE_COUNT as u64
        || claim.rule.tie_break != ClearingTieBreak::LowestBucket
        || claim.rule.value_bits != policy.value_bits
        || claim.rule.plaintext_modulus != policy.bfv.plaintext_modulus
        || claim.bfv != policy.bfv
    {
        return Err("claim clearing rule is incompatible with the private family");
    }
    if claim.outcome.p_star != Some(statement.p_star as u64)
        || claim.outcome.v_star != statement.v_star as u64
    {
        return Err("proof output differs from the canonical claim output");
    }
    let root_digest = private_order_root_commitment(statement.order_root);
    let expected_inputs = dark_bazaar_private::ORDER_COUNT + 1;
    if claim.ordered_inputs.len() != expected_inputs
        || !claim.ordered_inputs[..dark_bazaar_private::ORDER_COUNT]
            .iter()
            .all(|input| input.kind == InputDigestKind::Ciphertext)
        || claim.ordered_inputs[dark_bazaar_private::ORDER_COUNT].kind
            != InputDigestKind::Commitment
        || claim.ordered_inputs[dark_bazaar_private::ORDER_COUNT].digest != root_digest
    {
        return Err(
            "claim inputs are not four ordered ciphertext rows followed by the proved private-book root",
        );
    }
    Ok(())
}

fn encode_statement(out: &mut Vec<u8>, statement: PublicStatement) {
    out.extend_from_slice(&statement.session.to_be_bytes());
    out.extend_from_slice(&statement.rule.to_be_bytes());
    for lane in statement.order_root {
        out.extend_from_slice(&lane.to_be_bytes());
    }
    out.extend_from_slice(&statement.p_star.to_be_bytes());
    out.extend_from_slice(&statement.v_star.to_be_bytes());
}

fn decode_evidence(evidence: &[u8]) -> Option<(PublicStatement, &[u8], &[u8])> {
    const HEADER_LEN: usize = 8 + 4 + 12 * 4 + 4 + 4;
    const CHECKSUM_LEN: usize = 32;
    if evidence.len() < HEADER_LEN + CHECKSUM_LEN || &evidence[..8] != EVIDENCE_MAGIC {
        return None;
    }
    if u32::from_be_bytes(evidence[8..12].try_into().ok()?) != EVIDENCE_VERSION {
        return None;
    }
    let mut cursor = 12;
    let mut take_u32 = || {
        let value = u32::from_be_bytes(evidence.get(cursor..cursor + 4)?.try_into().ok()?);
        cursor += 4;
        Some(value)
    };
    let session = take_u32()?;
    let rule = take_u32()?;
    let mut order_root = [0u32; dark_bazaar_private::DIGEST_WIDTH];
    for lane in &mut order_root {
        *lane = take_u32()?;
    }
    let p_star = take_u32()?;
    let v_star = take_u32()?;
    let quorum_len = take_u32()? as usize;
    let proof_len = take_u32()? as usize;
    if quorum_len > MAX_QUORUM_EVIDENCE_BYTES || proof_len > MAX_PROOF_BYTES {
        return None;
    }
    let body_len = cursor.checked_add(quorum_len)?.checked_add(proof_len)?;
    let total_len = body_len.checked_add(CHECKSUM_LEN)?;
    if total_len != evidence.len() {
        return None;
    }
    let expected = blake3::Hasher::new_derive_key(EVIDENCE_CHECKSUM_DOMAIN)
        .update(&evidence[..body_len])
        .finalize();
    if expected.as_bytes() != &evidence[body_len..] {
        return None;
    }
    let quorum_end = cursor + quorum_len;
    let proof_end = quorum_end + proof_len;
    Some((
        PublicStatement {
            session,
            rule,
            order_root,
            p_star,
            v_star,
        },
        &evidence[cursor..quorum_end],
        &evidence[quorum_end..proof_end],
    ))
}

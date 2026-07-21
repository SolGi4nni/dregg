//! Transferable private-book/BFV evidence inside one authenticated receipt.
//!
//! This is the acceptance adapter for the three independently necessary
//! checks at the fixed Dark Bazaar `N=4,K=4` boundary:
//!
//! * an exact roster quorum authenticates the complete canonical fhEgg claim;
//! * the Lean-emitted HidingFRI proof establishes the private clearing rule and
//!   public `(p*, V*)` for an opening of the eight-felt private-book root; and
//! * one transferable Bulletproof proves that the exact four configured BFV
//!   rows encrypt that same hidden book under the exact configured parameters
//!   and collective public key.
//!
//! The relying party supplies every public object independently when it builds
//! [`PrivateBfvAttestedClearingVerifier`]. Proof bytes never get to select the
//! session, statement, BFV key, parameters, or ciphertext rows they are checked
//! against. The claim must begin with the four canonical proof-row ciphertext
//! digests in order and then the proved root commitment. The source-bound
//! constructor additionally pins a canonical suffix of signed-message/exact-row
//! pairs followed by the direct packed homomorphic fold of those proof rows.
//! Every suffix ciphertext must byte-identify a distinct proof row; a separately
//! encrypted live-source row is refused at verifier installation.
//! This is the live-ingress cutover: quorum co-membership is no longer asked to
//! stand in for ciphertext equality.
//!
//! # Exact remaining boundary
//!
//! The transferable relation is a Bulletproof R1CS over Curve25519. Its security
//! is classical and relies on discrete-log and Fiat-Shamir assumptions, BLAKE3
//! collision resistance/XOF pseudorandomness for public binding and randomized
//! equation compression, and the experimental `bulletproofs` v5 `yoloproofs`
//! backend; it is not a production-qualified or post-quantum lattice proof. The
//! circuit proves existence of bounded-short encryption coefficients, not ideal
//! entropy, seed distinctness, or the exact deployed CBD probability mass.
//! Proof production is also centralized: one process receives the complete
//! private book and all four encryption seeds. Verification no longer needs that
//! witness, but distributed/house-blind proof generation and a true
//! no-single-viewer pipeline remain separate work. The legacy
//! [`PrivateBfvAttestedClearingVerifier::new`] constructor remains for
//! proof-only/non-market consumers; a live source-bound market must use
//! [`PrivateBfvAttestedClearingVerifier::new_source_bound`] and the canonical
//! private-book ingress.

use std::fmt;

use dregg_circuit_prove::dark_bazaar_private::{self, DarkBazaarPrivateZkProof, PublicStatement};
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    CLEARING_ATTESTATION_PROTOCOL_ID, CLEARING_RULE_VERSION, ClearingClaim, ClearingTieBreak,
    ComputationIntegrityEvidence, ComputationIntegrityVerifier, Digest32, ExpectedClearingContext,
    InputDigest, InputDigestKind, NativePqAuthenticatedQuorumVerifier, NativePqPartyClaimSignature,
    PartyClaimSignature, QuorumVerifierError,
};
use fhegg_fhe::mpc_party::CertifiedPreprocessingBinding;
use fhegg_fhe::private_book_bfv_zk::{PrivateBookBfvZkProof, verify_private_book_bfv_zk};
use fhegg_fhe::private_book_relation::{
    PRIVATE_BOOK_BFV_CODEC_ID, PRIVATE_BOOK_PUBLIC_BOUND, PrivateBookCiphertexts,
    fold_private_book_ciphertexts,
};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey};

use crate::private_attested_clearing::{
    PrivateAttestedClearingPolicy, private_order_root_commitment,
};

const EVIDENCE_MAGIC: &[u8; 8] = b"DBAZv001";
const EVIDENCE_VERSION: u32 = 1;
const VERIFIER_ID_DOMAIN: &str = "dreggnet-market/private-bfv-attested-verifier/v1";
const EVIDENCE_CHECKSUM_DOMAIN: &str = "dreggnet-market/private-bfv-attested-evidence/v1";
const MAX_QUORUM_EVIDENCE_BYTES: usize = 1 << 20;
const MAX_CLEARING_PROOF_BYTES: usize = 64 << 20;
const MAX_BFV_PROOF_BYTES: usize = 64 << 10;
const BABYBEAR_MODULUS: u32 = 2_013_265_921;
const VERIFIED_AUTHORITY_DOMAIN: &str = "dreggnet-market/private-bfv-attested-authority/v1";
const ROSTER_COMMITMENT_DOMAIN: &str = "dreggnet-market/private-bfv-attested-roster/v1";

/// Downstream-safe description of one fully verified private clearing.
///
/// The ordinary `FheggSettlementReceipt` retains the
/// public claim digest needed by generic fhEgg consumers.  A game mechanic that
/// specifically requires the Dark Bazaar private-book relation needs more: the
/// exact relying-party verifier, complete evidence envelope, private proof
/// session/rule/root, full MPC session, and authenticated ordered roster.  This
/// value can only be minted by [`PrivateBfvAttestedClearingVerifier::verify_authority`]
/// after all three proof components pass against an independently reconstructed
/// context.  It carries no private witness or decryption material.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateBfvQuorumSecurity {
    ClassicalCompatibility,
    NativePostQuantum,
}

impl PrivateBfvQuorumSecurity {
    const fn tag(self) -> u8 {
        match self {
            Self::ClassicalCompatibility => 0,
            Self::NativePostQuantum => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBfvVerifiedAuthority {
    verifier_id: Digest32,
    claim_digest: Digest32,
    /// Digest of the complete claim plus computation-integrity evidence.  This
    /// commits the quorum certificate, HidingFRI proof, and BFV same-opening
    /// proof rather than only their public claim.
    certificate_digest: Digest32,
    claim_session_nonce: Digest32,
    private_session: u32,
    relation: u32,
    private_root: [u32; 8],
    private_root_commitment: Digest32,
    quorum_security: PrivateBfvQuorumSecurity,
    roster_commitment: Digest32,
    roster_len: u64,
    price: u32,
    volume: u32,
    /// Domain-separated commitment to every field above.  Consequence adapters
    /// bind this value to the target engine's real receipt/audit digest.
    authority_digest: Digest32,
}

impl PrivateBfvVerifiedAuthority {
    pub const fn verifier_id(&self) -> Digest32 {
        self.verifier_id
    }

    pub const fn claim_digest(&self) -> Digest32 {
        self.claim_digest
    }

    pub const fn certificate_digest(&self) -> Digest32 {
        self.certificate_digest
    }

    pub const fn claim_session_nonce(&self) -> Digest32 {
        self.claim_session_nonce
    }

    pub const fn private_session(&self) -> u32 {
        self.private_session
    }

    pub const fn relation(&self) -> u32 {
        self.relation
    }

    pub const fn private_root(&self) -> [u32; 8] {
        self.private_root
    }

    pub const fn private_root_commitment(&self) -> Digest32 {
        self.private_root_commitment
    }

    pub const fn quorum_security(&self) -> PrivateBfvQuorumSecurity {
        self.quorum_security
    }

    pub const fn roster_commitment(&self) -> Digest32 {
        self.roster_commitment
    }

    pub const fn roster_len(&self) -> u64 {
        self.roster_len
    }

    pub const fn price(&self) -> u32 {
        self.price
    }

    pub const fn volume(&self) -> u32 {
        self.volume
    }

    pub const fn authority_digest(&self) -> Digest32 {
        self.authority_digest
    }

    /// Detect field-level corruption in a retained authority record. This is an
    /// audit integrity check, not a substitute for the verifier call that
    /// originally minted the value.
    pub fn binding_verifies(&self) -> bool {
        self.private_root_commitment == private_order_root_commitment(self.private_root)
            && self.authority_digest
                == verified_authority_digest(
                    self.verifier_id,
                    self.claim_digest,
                    self.certificate_digest,
                    self.claim_session_nonce,
                    PublicStatement {
                        session: self.private_session,
                        rule: self.relation,
                        order_root: self.private_root,
                        p_star: self.price,
                        v_star: self.volume,
                    },
                    self.private_root_commitment,
                    self.quorum_security,
                    self.roster_commitment,
                    self.roster_len,
                )
    }

    #[cfg(test)]
    pub(crate) fn test_fixture(claim_digest: Digest32, price: u32, volume: u32) -> Self {
        let verifier_id = [0x11; 32];
        let certificate_digest = [0x22; 32];
        let claim_session_nonce = [0x33; 32];
        let statement = PublicStatement {
            session: 17,
            rule: dark_bazaar_private::RULE_ID,
            order_root: [1, 2, 3, 4, 5, 6, 7, 8],
            p_star: price,
            v_star: volume,
        };
        let private_root_commitment = private_order_root_commitment(statement.order_root);
        let quorum_security = PrivateBfvQuorumSecurity::NativePostQuantum;
        let roster_commitment = [0x44; 32];
        let roster_len = 2;
        let authority_digest = verified_authority_digest(
            verifier_id,
            claim_digest,
            certificate_digest,
            claim_session_nonce,
            statement,
            private_root_commitment,
            quorum_security,
            roster_commitment,
            roster_len,
        );
        Self {
            verifier_id,
            claim_digest,
            certificate_digest,
            claim_session_nonce,
            private_session: statement.session,
            relation: statement.rule,
            private_root: statement.order_root,
            private_root_commitment,
            quorum_security,
            roster_commitment,
            roster_len,
            price,
            volume,
            authority_digest,
        }
    }

    #[cfg(test)]
    pub(crate) fn tamper_verifier(&mut self) {
        self.verifier_id[0] ^= 1;
    }

    #[cfg(test)]
    pub(crate) fn tamper_certificate(&mut self) {
        self.certificate_digest[0] ^= 1;
    }

    #[cfg(test)]
    pub(crate) fn tamper_root(&mut self) {
        self.private_root[0] ^= 1;
    }

    #[cfg(test)]
    pub(crate) fn tamper_roster(&mut self) {
        self.roster_commitment[0] ^= 1;
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBfvAuthorityError {
    Binding(AttestationError),
    MissingExternalEvidence,
    VerifierIdMismatch,
    InvalidCompositeEvidence,
    RosterLengthOverflow,
}

impl fmt::Display for PrivateBfvAuthorityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Binding(error) => write!(f, "private authority binding refused: {error}"),
            Self::MissingExternalEvidence => {
                write!(
                    f,
                    "private authority requires external computation evidence"
                )
            }
            Self::VerifierIdMismatch => {
                write!(f, "private authority evidence names another verifier")
            }
            Self::InvalidCompositeEvidence => write!(
                f,
                "private authority quorum/HidingFRI/BFV composite did not verify"
            ),
            Self::RosterLengthOverflow => {
                write!(f, "private authority roster length exceeds u64")
            }
        }
    }
}

impl std::error::Error for PrivateBfvAuthorityError {}

impl From<AttestationError> for PrivateBfvAuthorityError {
    fn from(error: AttestationError) -> Self {
        Self::Binding(error)
    }
}

/// Configuration is rejected before the verifier can be selected by a relying
/// party. In particular, a merely hash-compatible policy is not accepted for a
/// non-deployed parameter set or malformed private-book rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateBfvAttestedVerifierConfigError {
    WrongParameters,
    BfvIdentityMismatch,
    InvalidCiphertextRows,
    InvalidSourceInputs,
    InvalidStatement,
}

impl fmt::Display for PrivateBfvAttestedVerifierConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongParameters => write!(f, "private BFV receipt requires the exact fold set"),
            Self::BfvIdentityMismatch => write!(
                f,
                "claim BFV identity does not name the configured parameters/public key"
            ),
            Self::InvalidCiphertextRows => {
                write!(f, "invalid canonical private-book BFV ciphertext rows")
            }
            Self::InvalidSourceInputs => write!(
                f,
                "source inputs are not distinct message/exact-proof-row pairs"
            ),
            Self::InvalidStatement => write!(f, "invalid fixed private-book public statement"),
        }
    }
}

impl std::error::Error for PrivateBfvAttestedVerifierConfigError {}

/// Producer-side assembly errors. No envelope is returned unless every
/// component already verifies against the independently configured public data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBfvAttestedEvidenceError {
    ClaimMismatch(&'static str),
    WrongQuorumSecurityProfile,
    Quorum(QuorumVerifierError),
    PrivateProof(String),
    BfvProof(String),
    EvidenceTooLarge,
}

impl fmt::Display for PrivateBfvAttestedEvidenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ClaimMismatch(reason) => write!(f, "private BFV proof/claim mismatch: {reason}"),
            Self::WrongQuorumSecurityProfile => write!(
                f,
                "evidence signatures do not match the installed quorum security profile"
            ),
            Self::Quorum(error) => write!(f, "quorum evidence refused: {error}"),
            Self::PrivateProof(error) => write!(f, "private clearing proof refused: {error}"),
            Self::BfvProof(error) => write!(f, "private-book BFV proof refused: {error}"),
            Self::EvidenceTooLarge => {
                write!(f, "private BFV attested evidence exceeds wire bounds")
            }
        }
    }
}

#[derive(Clone)]
enum PrivateBfvQuorumVerifier {
    ClassicalCompatibility(AuthenticatedQuorumVerifier),
    NativePostQuantum(NativePqAuthenticatedQuorumVerifier),
}

impl PrivateBfvQuorumVerifier {
    fn verifier_id(&self) -> Digest32 {
        match self {
            Self::ClassicalCompatibility(verifier) => verifier.verifier_id(),
            Self::NativePostQuantum(verifier) => verifier.verifier_id(),
        }
    }

    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        match self {
            Self::ClassicalCompatibility(verifier) => verifier.verify_claim(claim, evidence),
            Self::NativePostQuantum(verifier) => verifier.verify_claim(claim, evidence),
        }
    }
}

impl std::error::Error for PrivateBfvAttestedEvidenceError {}

/// Relying-party-selected verifier for one exact private statement and BFV
/// input set. A verifier is intentionally receipt/session-specific: its id
/// commits the complete statement, full claim nonce, parameters, key identity,
/// and four ordered ciphertext rows.
#[derive(Clone)]
pub struct PrivateBfvAttestedClearingVerifier {
    quorum: PrivateBfvQuorumVerifier,
    policy: PrivateAttestedClearingPolicy,
    expected_claim_session_nonce: Digest32,
    statement: PublicStatement,
    params: BfvParams,
    public_key: CollectivePublicKey,
    ciphertexts: PrivateBookCiphertexts,
    row_inputs: [InputDigest; dark_bazaar_private::ORDER_COUNT],
    /// Canonical live-source suffix. `None` is the legacy proof-only layout;
    /// `Some` means each message is paired with a distinct exact proof row.
    source_inputs: Option<Vec<InputDigest>>,
    /// Deterministically derived packed homomorphic fold of the exact proof
    /// rows. Present iff this verifier uses the live source-bound layout.
    packed_fold_input: Option<InputDigest>,
    /// Independently provisioned hybrid preprocessing authority, audited
    /// batch, and base circuit/session digest. Strict native-PQ settlement
    /// compares the claim's first-class binding against this exact value.
    required_preprocessing: Option<CertifiedPreprocessingBinding>,
    /// `Some` selects an exact tail after the packed fold (or proof prefix for
    /// proof-only mode). Native-PQ hosted settlement uses this to pin the
    /// certified-preprocessing authority/batch and source-board commitment.
    /// `None` preserves the legacy compatibility layout.
    required_tail_inputs: Option<Vec<InputDigest>>,
    verifier_id: Digest32,
}

impl PrivateBfvAttestedClearingVerifier {
    /// Install the exact public verification context. The proof statement's
    /// BabyBear session and the claim's full replay nonce are both pinned; they
    /// need not be a lossy derivation of one another.
    pub fn new(
        quorum: AuthenticatedQuorumVerifier,
        policy: PrivateAttestedClearingPolicy,
        expected_claim_session_nonce: Digest32,
        statement: PublicStatement,
        params: BfvParams,
        public_key: CollectivePublicKey,
        ciphertexts: PrivateBookCiphertexts,
    ) -> Result<Self, PrivateBfvAttestedVerifierConfigError> {
        Self::new_inner(
            PrivateBfvQuorumVerifier::ClassicalCompatibility(quorum),
            policy,
            expected_claim_session_nonce,
            statement,
            params,
            public_key,
            ciphertexts,
            None,
            None,
            None,
        )
    }

    /// Install a live-market verifier whose source-board ciphertexts are the
    /// exact canonical proof rows.
    ///
    /// `source_inputs` is the canonical `[message, ciphertext, ...]` sequence
    /// returned by authenticated ingress (normally listing first, then bids).
    /// A ciphertext may name each proof row at most once; padding rows need not
    /// have a trader message.  The complete sequence is pinned in the verifier
    /// id and must immediately follow the proof-row/root prefix in the claim;
    /// the verifier-derived packed fold must be the next input.
    #[allow(clippy::too_many_arguments)]
    pub fn new_source_bound(
        quorum: AuthenticatedQuorumVerifier,
        policy: PrivateAttestedClearingPolicy,
        expected_claim_session_nonce: Digest32,
        statement: PublicStatement,
        params: BfvParams,
        public_key: CollectivePublicKey,
        ciphertexts: PrivateBookCiphertexts,
        source_inputs: Vec<InputDigest>,
    ) -> Result<Self, PrivateBfvAttestedVerifierConfigError> {
        Self::new_inner(
            PrivateBfvQuorumVerifier::ClassicalCompatibility(quorum),
            policy,
            expected_claim_session_nonce,
            statement,
            params,
            public_key,
            ciphertexts,
            Some(source_inputs),
            None,
            None,
        )
    }

    /// Install the exact public verification context with a strict native-PQ
    /// full-claim quorum.  There is no digest-only or classical downgrade path.
    pub fn new_native_post_quantum(
        quorum: NativePqAuthenticatedQuorumVerifier,
        policy: PrivateAttestedClearingPolicy,
        expected_claim_session_nonce: Digest32,
        statement: PublicStatement,
        params: BfvParams,
        public_key: CollectivePublicKey,
        ciphertexts: PrivateBookCiphertexts,
    ) -> Result<Self, PrivateBfvAttestedVerifierConfigError> {
        Self::new_inner(
            PrivateBfvQuorumVerifier::NativePostQuantum(quorum),
            policy,
            expected_claim_session_nonce,
            statement,
            params,
            public_key,
            ciphertexts,
            None,
            None,
            Some(Vec::new()),
        )
    }

    /// Source-bound native-PQ variant used by the shielded Dark Bazaar apex.
    #[allow(clippy::too_many_arguments)]
    pub fn new_source_bound_native_post_quantum(
        quorum: NativePqAuthenticatedQuorumVerifier,
        policy: PrivateAttestedClearingPolicy,
        expected_claim_session_nonce: Digest32,
        statement: PublicStatement,
        params: BfvParams,
        public_key: CollectivePublicKey,
        ciphertexts: PrivateBookCiphertexts,
        source_inputs: Vec<InputDigest>,
        required_preprocessing: CertifiedPreprocessingBinding,
        required_tail_inputs: Vec<InputDigest>,
    ) -> Result<Self, PrivateBfvAttestedVerifierConfigError> {
        Self::new_inner(
            PrivateBfvQuorumVerifier::NativePostQuantum(quorum),
            policy,
            expected_claim_session_nonce,
            statement,
            params,
            public_key,
            ciphertexts,
            Some(source_inputs),
            Some(required_preprocessing),
            Some(required_tail_inputs),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn new_inner(
        quorum: PrivateBfvQuorumVerifier,
        policy: PrivateAttestedClearingPolicy,
        expected_claim_session_nonce: Digest32,
        statement: PublicStatement,
        params: BfvParams,
        public_key: CollectivePublicKey,
        ciphertexts: PrivateBookCiphertexts,
        source_inputs: Option<Vec<InputDigest>>,
        required_preprocessing: Option<CertifiedPreprocessingBinding>,
        required_tail_inputs: Option<Vec<InputDigest>>,
    ) -> Result<Self, PrivateBfvAttestedVerifierConfigError> {
        validate_configuration(&policy, &params, &public_key, &ciphertexts)?;
        validate_statement(statement)?;

        let row_inputs = ciphertexts.rows().each_ref().map(InputDigest::ciphertext);
        if let Some(inputs) = source_inputs.as_deref() {
            validate_source_inputs(inputs, &row_inputs)?;
        }
        let packed_fold_input = if source_inputs.is_some() {
            let folded = fold_private_book_ciphertexts(&ciphertexts, &params)
                .map_err(|_| PrivateBfvAttestedVerifierConfigError::InvalidCiphertextRows)?;
            Some(InputDigest::ciphertext(folded.ciphertext()))
        } else {
            None
        };
        let verifier_id = derive_verifier_id(
            &quorum,
            &policy,
            expected_claim_session_nonce,
            statement,
            &params,
            &row_inputs,
            source_inputs.as_deref(),
            packed_fold_input,
            required_preprocessing.as_ref(),
            required_tail_inputs.as_deref(),
        );
        Ok(Self {
            quorum,
            policy,
            expected_claim_session_nonce,
            statement,
            params,
            public_key,
            ciphertexts,
            row_inputs,
            source_inputs,
            packed_fold_input,
            required_preprocessing,
            required_tail_inputs,
            verifier_id,
        })
    }

    pub fn quorum(&self) -> Option<&AuthenticatedQuorumVerifier> {
        match &self.quorum {
            PrivateBfvQuorumVerifier::ClassicalCompatibility(verifier) => Some(verifier),
            PrivateBfvQuorumVerifier::NativePostQuantum(_) => None,
        }
    }

    pub fn native_post_quantum_quorum(&self) -> Option<&NativePqAuthenticatedQuorumVerifier> {
        match &self.quorum {
            PrivateBfvQuorumVerifier::ClassicalCompatibility(_) => None,
            PrivateBfvQuorumVerifier::NativePostQuantum(verifier) => Some(verifier),
        }
    }

    pub const fn statement(&self) -> PublicStatement {
        self.statement
    }

    pub const fn expected_claim_session_nonce(&self) -> Digest32 {
        self.expected_claim_session_nonce
    }

    pub const fn ciphertexts(&self) -> &PrivateBookCiphertexts {
        &self.ciphertexts
    }

    /// Verify the complete composite without consuming replay state and mint a
    /// typed authority for a downstream game/market consequence.
    ///
    /// This method deliberately requires the independently retained expected
    /// context.  It first reconstructs the canonical claim, then requires the
    /// receipt's selected verifier id to equal this verifier, and finally runs
    /// the full quorum + HidingFRI + BFV/private-root verifier.  Replay remains
    /// the settlement boundary's job: callers must still pass the original
    /// receipt through `verify_full` while committing the consequence.
    pub fn verify_authority(
        &self,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
    ) -> Result<PrivateBfvVerifiedAuthority, PrivateBfvAuthorityError> {
        let authority = self.prepare_authority_metadata(receipt, expected)?;
        let ComputationIntegrityEvidence::External { evidence, .. } =
            &receipt.computation_integrity
        else {
            unreachable!("authority metadata already required external evidence")
        };
        if !self.verify_composite(&receipt.claim, evidence) {
            return Err(PrivateBfvAuthorityError::InvalidCompositeEvidence);
        }
        Ok(authority)
    }

    /// Cheap metadata projection used only by the crate's specialized atomic
    /// wrapper immediately before it calls `verify_full` with this same
    /// verifier/receipt/context. Keeping it crate-private avoids running the
    /// minutes-class composite twice while preventing unverified callers from
    /// obtaining an authority value.
    pub(crate) fn prepare_authority_metadata(
        &self,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
    ) -> Result<PrivateBfvVerifiedAuthority, PrivateBfvAuthorityError> {
        receipt.verify_binding(expected)?;
        let verifier_id = match &receipt.computation_integrity {
            ComputationIntegrityEvidence::BindingOnly(_) => {
                return Err(PrivateBfvAuthorityError::MissingExternalEvidence);
            }
            ComputationIntegrityEvidence::External {
                verifier_id,
                evidence: _,
            } => verifier_id,
        };
        if verifier_id != &self.verifier_id {
            return Err(PrivateBfvAuthorityError::VerifierIdMismatch);
        }
        if self.claim_matches_public(&receipt.claim).is_err() {
            return Err(PrivateBfvAuthorityError::InvalidCompositeEvidence);
        }

        let roster_len = u64::try_from(receipt.claim.ordered_roster.len())
            .map_err(|_| PrivateBfvAuthorityError::RosterLengthOverflow)?;
        let quorum_security = match &self.quorum {
            PrivateBfvQuorumVerifier::ClassicalCompatibility(_) => {
                PrivateBfvQuorumSecurity::ClassicalCompatibility
            }
            PrivateBfvQuorumVerifier::NativePostQuantum(_) => {
                PrivateBfvQuorumSecurity::NativePostQuantum
            }
        };
        let roster_commitment = roster_commitment(&receipt.claim.ordered_roster, roster_len);
        let private_root_commitment = private_order_root_commitment(self.statement.order_root);
        let certificate_digest = receipt.envelope_digest();
        let claim_digest = receipt.claim_digest();
        let authority_digest = verified_authority_digest(
            self.verifier_id,
            claim_digest,
            certificate_digest,
            self.expected_claim_session_nonce,
            self.statement,
            private_root_commitment,
            quorum_security,
            roster_commitment,
            roster_len,
        );
        Ok(PrivateBfvVerifiedAuthority {
            verifier_id: self.verifier_id,
            claim_digest,
            certificate_digest,
            claim_session_nonce: self.expected_claim_session_nonce,
            private_session: self.statement.session,
            relation: self.statement.rule,
            private_root: self.statement.order_root,
            private_root_commitment,
            quorum_security,
            roster_commitment,
            roster_len,
            price: self.statement.p_star,
            volume: self.statement.v_star,
            authority_digest,
        })
    }

    /// Assemble one canonical external evidence body only after quorum,
    /// HidingFRI, and BFV/private-root verification all succeed.
    pub fn assemble_evidence(
        &self,
        claim: &ClearingClaim,
        signatures: &[PartyClaimSignature],
        clearing_proof: &DarkBazaarPrivateZkProof,
        bfv_proof: &PrivateBookBfvZkProof,
    ) -> Result<ComputationIntegrityEvidence, PrivateBfvAttestedEvidenceError> {
        self.claim_matches_public(claim)
            .map_err(PrivateBfvAttestedEvidenceError::ClaimMismatch)?;
        dark_bazaar_private::verify_zk(clearing_proof, self.statement)
            .map_err(PrivateBfvAttestedEvidenceError::PrivateProof)?;
        verify_private_book_bfv_zk(
            bfv_proof,
            self.statement,
            &self.ciphertexts,
            &self.params,
            &self.public_key,
        )
        .map_err(|error| PrivateBfvAttestedEvidenceError::BfvProof(error.to_string()))?;

        let PrivateBfvQuorumVerifier::ClassicalCompatibility(quorum) = &self.quorum else {
            return Err(PrivateBfvAttestedEvidenceError::WrongQuorumSecurityProfile);
        };
        let quorum_evidence = match quorum
            .assemble_evidence(&claim.digest(), signatures)
            .map_err(PrivateBfvAttestedEvidenceError::Quorum)?
        {
            ComputationIntegrityEvidence::External { evidence, .. } => evidence,
            ComputationIntegrityEvidence::BindingOnly(_) => unreachable!("quorum is external"),
        };
        self.assemble_verified_components(quorum_evidence, clearing_proof, bfv_proof)
    }

    /// Assemble the strict native-PQ variant.  Both Ed25519 and ML-DSA-65
    /// authenticate the verifier-selected full canonical claim.
    pub fn assemble_native_post_quantum_evidence(
        &self,
        claim: &ClearingClaim,
        signatures: &[NativePqPartyClaimSignature],
        clearing_proof: &DarkBazaarPrivateZkProof,
        bfv_proof: &PrivateBookBfvZkProof,
    ) -> Result<ComputationIntegrityEvidence, PrivateBfvAttestedEvidenceError> {
        self.claim_matches_public(claim)
            .map_err(PrivateBfvAttestedEvidenceError::ClaimMismatch)?;
        dark_bazaar_private::verify_zk(clearing_proof, self.statement)
            .map_err(PrivateBfvAttestedEvidenceError::PrivateProof)?;
        verify_private_book_bfv_zk(
            bfv_proof,
            self.statement,
            &self.ciphertexts,
            &self.params,
            &self.public_key,
        )
        .map_err(|error| PrivateBfvAttestedEvidenceError::BfvProof(error.to_string()))?;

        let PrivateBfvQuorumVerifier::NativePostQuantum(quorum) = &self.quorum else {
            return Err(PrivateBfvAttestedEvidenceError::WrongQuorumSecurityProfile);
        };
        let quorum_evidence = match quorum
            .assemble_evidence(claim, signatures)
            .map_err(PrivateBfvAttestedEvidenceError::Quorum)?
        {
            ComputationIntegrityEvidence::External { evidence, .. } => evidence,
            ComputationIntegrityEvidence::BindingOnly(_) => unreachable!("quorum is external"),
        };
        self.assemble_verified_components(quorum_evidence, clearing_proof, bfv_proof)
    }

    fn assemble_verified_components(
        &self,
        quorum_evidence: Vec<u8>,
        clearing_proof: &DarkBazaarPrivateZkProof,
        bfv_proof: &PrivateBookBfvZkProof,
    ) -> Result<ComputationIntegrityEvidence, PrivateBfvAttestedEvidenceError> {
        let clearing_bytes = clearing_proof
            .to_postcard()
            .map_err(PrivateBfvAttestedEvidenceError::PrivateProof)?;
        let bfv_bytes = bfv_proof.to_bytes();
        if quorum_evidence.len() > MAX_QUORUM_EVIDENCE_BYTES
            || clearing_bytes.len() > MAX_CLEARING_PROOF_BYTES
            || bfv_bytes.len() > MAX_BFV_PROOF_BYTES
        {
            return Err(PrivateBfvAttestedEvidenceError::EvidenceTooLarge);
        }

        let mut evidence = Vec::with_capacity(
            EVIDENCE_MAGIC.len()
                + 4
                + 3 * 4
                + quorum_evidence.len()
                + clearing_bytes.len()
                + bfv_bytes.len()
                + 32,
        );
        evidence.extend_from_slice(EVIDENCE_MAGIC);
        evidence.extend_from_slice(&EVIDENCE_VERSION.to_be_bytes());
        evidence.extend_from_slice(&(quorum_evidence.len() as u32).to_be_bytes());
        evidence.extend_from_slice(&(clearing_bytes.len() as u32).to_be_bytes());
        evidence.extend_from_slice(&(bfv_bytes.len() as u32).to_be_bytes());
        evidence.extend_from_slice(&quorum_evidence);
        evidence.extend_from_slice(&clearing_bytes);
        evidence.extend_from_slice(&bfv_bytes);
        let checksum = blake3::Hasher::new_derive_key(EVIDENCE_CHECKSUM_DOMAIN)
            .update(&evidence)
            .finalize();
        evidence.extend_from_slice(checksum.as_bytes());

        Ok(ComputationIntegrityEvidence::External {
            verifier_id: self.verifier_id,
            evidence,
        })
    }

    fn claim_matches_public(&self, claim: &ClearingClaim) -> Result<(), &'static str> {
        if self.required_preprocessing.as_ref() != claim.preprocessing.as_ref() {
            return Err(
                "claim preprocessing authority/batch/circuit differs from the verifier pin",
            );
        }
        if claim.protocol_id != CLEARING_ATTESTATION_PROTOCOL_ID {
            return Err("protocol id is not fhEgg clearing v1");
        }
        if claim.session_nonce != self.expected_claim_session_nonce {
            return Err("claim session nonce differs from relying-party configuration");
        }
        if self.statement.rule != dark_bazaar_private::RULE_ID {
            return Err("proof rule id is not the installed private family");
        }
        if claim.rule.version != CLEARING_RULE_VERSION
            || claim.rule.buckets != dark_bazaar_private::PRICE_COUNT as u64
            || claim.rule.tie_break != ClearingTieBreak::LowestBucket
            || claim.rule.value_bits != self.policy.value_bits()
            || claim.rule.plaintext_modulus != self.policy.plaintext_modulus()
            || &claim.bfv != self.policy.bfv()
        {
            return Err("claim clearing rule or BFV identity is incompatible with the verifier");
        }
        if claim.outcome.p_star != Some(self.statement.p_star as u64)
            || claim.outcome.v_star != self.statement.v_star as u64
        {
            return Err("proof output differs from the canonical claim output");
        }

        let root =
            InputDigest::commitment(private_order_root_commitment(self.statement.order_root));
        let prefix_len = dark_bazaar_private::ORDER_COUNT + 1;
        if claim.ordered_inputs.len() < prefix_len
            || claim.ordered_inputs[..dark_bazaar_private::ORDER_COUNT] != self.row_inputs[..]
            || claim.ordered_inputs[dark_bazaar_private::ORDER_COUNT] != root
        {
            return Err(
                "claim does not begin with the exact four proof rows followed by the proved root",
            );
        }
        if claim
            .ordered_inputs
            .iter()
            .filter(|input| **input == root)
            .count()
            != 1
        {
            return Err("proved root occurs more than once in the claim");
        }

        if let Some(source_inputs) = self.source_inputs.as_deref() {
            let suffix_end = prefix_len
                .checked_add(source_inputs.len())
                .ok_or("source-bound input length overflow")?;
            let fold_index = suffix_end;
            if claim.ordered_inputs.len() <= fold_index
                || &claim.ordered_inputs[prefix_len..suffix_end] != source_inputs
                || Some(claim.ordered_inputs[fold_index]) != self.packed_fold_input
            {
                return Err(
                    "claim does not carry the exact source rows and their canonical packed fold",
                );
            }
            for row in &self.row_inputs {
                let source_occurrences = source_inputs.iter().filter(|input| *input == row).count();
                let total_occurrences = claim
                    .ordered_inputs
                    .iter()
                    .filter(|input| *input == row)
                    .count();
                if total_occurrences != 1 + source_occurrences {
                    return Err("proof/source row multiplicity differs from canonical layout");
                }
            }
            for message in source_inputs.iter().step_by(2) {
                if claim
                    .ordered_inputs
                    .iter()
                    .filter(|input| *input == message)
                    .count()
                    != 1
                {
                    return Err("source message occurs more than once in the claim");
                }
            }
            let packed = self
                .packed_fold_input
                .expect("source-bound verifier derives a packed fold");
            if claim
                .ordered_inputs
                .iter()
                .filter(|input| **input == packed)
                .count()
                != 1
            {
                return Err("canonical packed fold occurs more than once in the claim");
            }
            if let Some(required_tail) = self.required_tail_inputs.as_deref() {
                let tail_start = fold_index + 1;
                if claim.ordered_inputs.get(tail_start..) != Some(required_tail) {
                    return Err(
                        "claim tail differs from the verifier-pinned preprocessing/source context",
                    );
                }
            }
        } else if self.row_inputs.iter().any(|row| {
            claim
                .ordered_inputs
                .iter()
                .filter(|input| *input == row)
                .count()
                != 1
        }) {
            return Err("proved row occurs more than once in a proof-only claim");
        } else if let Some(required_tail) = self.required_tail_inputs.as_deref() {
            if claim.ordered_inputs.get(prefix_len..) != Some(required_tail) {
                return Err("claim tail differs from the verifier-pinned context");
            }
        }
        Ok(())
    }

    fn verify_composite(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        if self.claim_matches_public(claim).is_err() {
            return false;
        }
        let Some((quorum_bytes, clearing_bytes, bfv_bytes)) = decode_evidence(evidence) else {
            return false;
        };
        if !self.quorum.verify_claim(claim, quorum_bytes) {
            return false;
        }

        let Ok(clearing_proof) = DarkBazaarPrivateZkProof::from_postcard(clearing_bytes) else {
            return false;
        };
        if clearing_proof.to_postcard().as_deref() != Ok(clearing_bytes)
            || dark_bazaar_private::verify_zk(&clearing_proof, self.statement).is_err()
        {
            return false;
        }
        let Ok(bfv_proof) = PrivateBookBfvZkProof::from_bytes(bfv_bytes) else {
            return false;
        };
        if bfv_proof.to_bytes() != bfv_bytes {
            return false;
        }
        verify_private_book_bfv_zk(
            &bfv_proof,
            self.statement,
            &self.ciphertexts,
            &self.params,
            &self.public_key,
        )
        .is_ok()
    }
}

fn roster_commitment(
    roster: &[fhegg_fhe::attestation::PartyIdentity],
    roster_len: u64,
) -> Digest32 {
    let mut hasher = blake3::Hasher::new_derive_key(ROSTER_COMMITMENT_DOMAIN);
    hasher.update(&roster_len.to_be_bytes());
    for identity in roster {
        hasher.update(&identity.0);
    }
    *hasher.finalize().as_bytes()
}

#[allow(clippy::too_many_arguments)]
fn verified_authority_digest(
    verifier_id: Digest32,
    claim_digest: Digest32,
    certificate_digest: Digest32,
    claim_session_nonce: Digest32,
    statement: PublicStatement,
    private_root_commitment: Digest32,
    quorum_security: PrivateBfvQuorumSecurity,
    roster_commitment: Digest32,
    roster_len: u64,
) -> Digest32 {
    let mut hasher = blake3::Hasher::new_derive_key(VERIFIED_AUTHORITY_DOMAIN);
    hasher.update(&verifier_id);
    hasher.update(&claim_digest);
    hasher.update(&certificate_digest);
    hasher.update(&claim_session_nonce);
    hasher.update(&statement.session.to_be_bytes());
    hasher.update(&statement.rule.to_be_bytes());
    for lane in statement.order_root {
        hasher.update(&lane.to_be_bytes());
    }
    hasher.update(&private_root_commitment);
    hasher.update(&[quorum_security.tag()]);
    hasher.update(&roster_commitment);
    hasher.update(&roster_len.to_be_bytes());
    hasher.update(&statement.p_star.to_be_bytes());
    hasher.update(&statement.v_star.to_be_bytes());
    *hasher.finalize().as_bytes()
}

impl ComputationIntegrityVerifier for PrivateBfvAttestedClearingVerifier {
    fn verifier_id(&self) -> Digest32 {
        self.verifier_id
    }

    fn verify(&self, _claim_digest: &Digest32, _evidence: &[u8]) -> bool {
        // Digest-only verification cannot reconstruct the exact input prefix,
        // full session nonce, roster, BFV identity, rule, or output.
        false
    }

    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        self.verify_composite(claim, evidence)
    }
}

fn validate_configuration(
    policy: &PrivateAttestedClearingPolicy,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
    ciphertexts: &PrivateBookCiphertexts,
) -> Result<(), PrivateBfvAttestedVerifierConfigError> {
    let pinned = BfvParams::fold_set();
    if params.degree() != pinned.degree()
        || params.moduli() != pinned.moduli()
        || params.plaintext_modulus() != pinned.plaintext_modulus()
    {
        return Err(PrivateBfvAttestedVerifierConfigError::WrongParameters);
    }
    if policy.bfv().degree != params.degree() as u64
        || policy.bfv().plaintext_modulus != params.plaintext_modulus()
        || policy.bfv().encryption_domain_digest()
            != BfvPublicIdentity::encryption_domain_digest_from_public(params, public_key)
    {
        return Err(PrivateBfvAttestedVerifierConfigError::BfvIdentityMismatch);
    }
    if ciphertexts.rows().iter().any(|row| {
        row.degree != params.degree()
            || row.moduli.as_slice() != params.moduli()
            || row.level != 0
            || !row.variable_time
            || row.polys.len() != 2
            || row.plain_bound != PRIVATE_BOOK_PUBLIC_BOUND
            || row.polys.iter().any(|poly| {
                poly.rows.len() != params.moduli().len()
                    || poly
                        .rows
                        .iter()
                        .any(|coeffs| coeffs.len() != params.degree())
            })
    }) {
        return Err(PrivateBfvAttestedVerifierConfigError::InvalidCiphertextRows);
    }
    Ok(())
}

fn validate_statement(
    statement: PublicStatement,
) -> Result<(), PrivateBfvAttestedVerifierConfigError> {
    if statement.session >= BABYBEAR_MODULUS
        || statement.rule != dark_bazaar_private::RULE_ID
        || statement.p_star as usize >= dark_bazaar_private::PRICE_COUNT
        || statement.v_star
            > (dark_bazaar_private::ORDER_COUNT as u32) * u32::from(dark_bazaar_private::MAX_QTY)
        || statement
            .order_root
            .iter()
            .any(|&lane| lane >= BABYBEAR_MODULUS)
    {
        return Err(PrivateBfvAttestedVerifierConfigError::InvalidStatement);
    }
    Ok(())
}

fn validate_source_inputs(
    source_inputs: &[InputDigest],
    row_inputs: &[InputDigest; dark_bazaar_private::ORDER_COUNT],
) -> Result<(), PrivateBfvAttestedVerifierConfigError> {
    if source_inputs.is_empty()
        || !source_inputs.len().is_multiple_of(2)
        || source_inputs.len() > 2 * dark_bazaar_private::ORDER_COUNT
    {
        return Err(PrivateBfvAttestedVerifierConfigError::InvalidSourceInputs);
    }
    let mut seen_rows = Vec::with_capacity(source_inputs.len() / 2);
    let mut seen_messages = Vec::with_capacity(source_inputs.len() / 2);
    for pair in source_inputs.chunks_exact(2) {
        if pair[0].kind != InputDigestKind::Commitment
            || pair[1].kind != InputDigestKind::Ciphertext
            || !row_inputs.contains(&pair[1])
            || seen_rows.contains(&pair[1])
            || seen_messages.contains(&pair[0])
        {
            return Err(PrivateBfvAttestedVerifierConfigError::InvalidSourceInputs);
        }
        seen_messages.push(pair[0]);
        seen_rows.push(pair[1]);
    }
    Ok(())
}

fn derive_verifier_id(
    quorum: &PrivateBfvQuorumVerifier,
    policy: &PrivateAttestedClearingPolicy,
    expected_claim_session_nonce: Digest32,
    statement: PublicStatement,
    params: &BfvParams,
    row_inputs: &[InputDigest; dark_bazaar_private::ORDER_COUNT],
    source_inputs: Option<&[InputDigest]>,
    packed_fold_input: Option<InputDigest>,
    required_preprocessing: Option<&CertifiedPreprocessingBinding>,
    required_tail_inputs: Option<&[InputDigest]>,
) -> Digest32 {
    let mut hasher = blake3::Hasher::new_derive_key(VERIFIER_ID_DOMAIN);
    hasher.update(EVIDENCE_MAGIC);
    hasher.update(&EVIDENCE_VERSION.to_be_bytes());
    hasher.update(&quorum.verifier_id());
    hasher.update(PRIVATE_BOOK_BFV_CODEC_ID);
    hasher.update(&expected_claim_session_nonce);
    encode_statement(&mut hasher, statement);
    hasher.update(&(params.degree() as u64).to_be_bytes());
    hasher.update(&params.plaintext_modulus().to_be_bytes());
    hasher.update(&(params.moduli().len() as u64).to_be_bytes());
    for modulus in params.moduli() {
        hasher.update(&modulus.to_be_bytes());
    }
    hasher.update(&policy.value_bits().to_be_bytes());
    encode_bfv_identity(&mut hasher, policy.bfv());
    for input in row_inputs {
        hasher.update(&input.digest);
    }
    match source_inputs {
        Some(inputs) => {
            hasher.update(b"source-bound-exact-rows");
            hasher.update(&(inputs.len() as u64).to_be_bytes());
            for input in inputs {
                hasher.update(&[match input.kind {
                    InputDigestKind::Ciphertext => 0,
                    InputDigestKind::Commitment => 1,
                }]);
                hasher.update(&input.digest);
            }
            let packed = packed_fold_input.expect("source-bound verifier derives packed fold");
            hasher.update(&packed.digest);
        }
        None => {
            debug_assert!(packed_fold_input.is_none());
            hasher.update(b"proof-only-legacy-layout");
        }
    }
    match required_preprocessing {
        Some(binding) => {
            hasher.update(&[1]);
            let bytes = binding.canonical_bytes();
            hasher.update(&(bytes.len() as u64).to_be_bytes());
            hasher.update(&bytes);
        }
        None => {
            hasher.update(&[0]);
        }
    }
    match required_tail_inputs {
        Some(inputs) => {
            hasher.update(&[1]);
            hasher.update(&(inputs.len() as u64).to_be_bytes());
            for input in inputs {
                hasher.update(&[match input.kind {
                    InputDigestKind::Commitment => 0,
                    InputDigestKind::Ciphertext => 1,
                }]);
                hasher.update(&input.digest);
            }
        }
        None => {
            hasher.update(&[0]);
        }
    }
    hasher.update(&(MAX_QUORUM_EVIDENCE_BYTES as u64).to_be_bytes());
    hasher.update(&(MAX_CLEARING_PROOF_BYTES as u64).to_be_bytes());
    hasher.update(&(MAX_BFV_PROOF_BYTES as u64).to_be_bytes());
    hasher.update(dark_bazaar_private::DARK_BAZAAR_PRIVATE_DESCRIPTOR_JSON.as_bytes());
    *hasher.finalize().as_bytes()
}

fn encode_statement(hasher: &mut blake3::Hasher, statement: PublicStatement) {
    hasher.update(&statement.session.to_be_bytes());
    hasher.update(&statement.rule.to_be_bytes());
    for lane in statement.order_root {
        hasher.update(&lane.to_be_bytes());
    }
    hasher.update(&statement.p_star.to_be_bytes());
    hasher.update(&statement.v_star.to_be_bytes());
}

fn encode_bfv_identity(hasher: &mut blake3::Hasher, bfv: &BfvPublicIdentity) {
    hasher.update(&bfv.n_parties.to_be_bytes());
    hasher.update(&bfv.opening_threshold.to_be_bytes());
    hasher.update(&bfv.degree.to_be_bytes());
    hasher.update(&bfv.moduli_digest);
    hasher.update(&bfv.plaintext_modulus.to_be_bytes());
    hasher.update(&bfv.crp_seed);
    hasher.update(&bfv.collective_public_key_digest);
}

fn decode_evidence(evidence: &[u8]) -> Option<(&[u8], &[u8], &[u8])> {
    const HEADER_LEN: usize = 8 + 4 + 3 * 4;
    const CHECKSUM_LEN: usize = 32;
    if evidence.len() < HEADER_LEN + CHECKSUM_LEN || &evidence[..8] != EVIDENCE_MAGIC {
        return None;
    }
    if u32::from_be_bytes(evidence[8..12].try_into().ok()?) != EVIDENCE_VERSION {
        return None;
    }
    let quorum_len = u32::from_be_bytes(evidence[12..16].try_into().ok()?) as usize;
    let clearing_len = u32::from_be_bytes(evidence[16..20].try_into().ok()?) as usize;
    let bfv_len = u32::from_be_bytes(evidence[20..24].try_into().ok()?) as usize;
    if quorum_len > MAX_QUORUM_EVIDENCE_BYTES
        || clearing_len > MAX_CLEARING_PROOF_BYTES
        || bfv_len > MAX_BFV_PROOF_BYTES
    {
        return None;
    }
    let quorum_end = HEADER_LEN.checked_add(quorum_len)?;
    let clearing_end = quorum_end.checked_add(clearing_len)?;
    let bfv_end = clearing_end.checked_add(bfv_len)?;
    if bfv_end.checked_add(CHECKSUM_LEN)? != evidence.len() {
        return None;
    }
    let expected = blake3::Hasher::new_derive_key(EVIDENCE_CHECKSUM_DOMAIN)
        .update(&evidence[..bfv_end])
        .finalize();
    if expected.as_bytes() != &evidence[bfv_end..] {
        return None;
    }
    Some((
        &evidence[HEADER_LEN..quorum_end],
        &evidence[quorum_end..clearing_end],
        &evidence[clearing_end..bfv_end],
    ))
}

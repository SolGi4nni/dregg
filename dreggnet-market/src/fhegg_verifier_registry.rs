//! Deployment-selected computation-integrity policy for hosted fhEgg settlement.
//!
//! An uploaded [`crate::fhegg_transport::FheggSettlementBundle`] carries a
//! verifier id, but never selects the verifier behind that id. The host installs
//! one [`FheggVerifierRegistry`] from trusted deployment configuration, and the
//! ordinary frontend-neutral operation path dispatches through that registry.
//! The legacy authenticated-quorum policy remains available; the private Dark
//! Bazaar apex installs the complete quorum + HidingFRI + BFV/private-root
//! verifier instead.
//!
//! `PrivateBfvHostedVerifierConfig` owns only public verification material when
//! the private-attested feature is installed:
//! roster keys, BFV identity/parameters/public key, exact ciphertext rows,
//! private public statement, claim nonce, and canonical source-input digests.
//! It contains no plaintext order, BFV secret/decryption share, encryption seed,
//! or proof witness. Reconstruction re-runs every underlying verifier config
//! check and then compares the resulting verifier id with a separately pinned
//! deployment id. Thus even a coherent substitution of every public preimage is
//! refused unless the deployment pin changes too; receipt bytes cannot perform
//! that policy change.

#[cfg(feature = "private-attested-clearing")]
use std::fmt;

use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ClearingClaim, ComputationIntegrityVerifier, Digest32,
    QuorumVerifierError,
};

#[cfg(feature = "private-attested-clearing")]
use dregg_circuit_prove::dark_bazaar_private::PublicStatement;
#[cfg(feature = "private-attested-clearing")]
use fhegg_fhe::attestation::{
    BfvPublicIdentity, InputDigest, NativePqAuthenticatedQuorumVerifier, NativePqPartyPublicKey,
};
#[cfg(feature = "private-attested-clearing")]
use fhegg_fhe::private_book_relation::PrivateBookCiphertexts;
#[cfg(feature = "private-attested-clearing")]
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey};

#[cfg(feature = "private-attested-clearing")]
use crate::private_attested_clearing::{
    PrivateAttestedClearingPolicy, PrivateAttestedVerifierConfigError,
};
#[cfg(feature = "private-attested-clearing")]
use crate::private_bfv_attested_clearing::{
    PrivateBfvAttestedClearingVerifier, PrivateBfvAttestedVerifierConfigError,
    PrivateBfvAuthorityError, PrivateBfvVerifiedAuthority,
};

/// Which relying-party policy is installed behind the hosted operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FheggVerifierRegistryKind {
    AuthenticatedQuorum,
    #[cfg(feature = "private-attested-clearing")]
    PrivateBfvAttested,
}

#[derive(Clone)]
enum InstalledVerifier {
    AuthenticatedQuorum(AuthenticatedQuorumVerifier),
    #[cfg(feature = "private-attested-clearing")]
    PrivateBfvAttested(PrivateBfvAttestedClearingVerifier),
}

/// One deployment-selected computation-integrity verifier. The wrapper is
/// intentionally not an uploader-controlled map: a host instance installs one
/// exact policy, and normal receipt verification still checks its verifier id.
#[derive(Clone)]
pub struct FheggVerifierRegistry {
    installed: InstalledVerifier,
}

impl FheggVerifierRegistry {
    /// Preserve the existing hosted authenticated-quorum policy.
    pub fn authenticated_quorum(
        ordered_public_keys: Vec<[u8; 32]>,
        threshold: usize,
    ) -> Result<Self, QuorumVerifierError> {
        Ok(Self {
            installed: InstalledVerifier::AuthenticatedQuorum(AuthenticatedQuorumVerifier::new(
                ordered_public_keys,
                threshold,
            )?),
        })
    }

    pub fn kind(&self) -> FheggVerifierRegistryKind {
        match &self.installed {
            InstalledVerifier::AuthenticatedQuorum(_) => {
                FheggVerifierRegistryKind::AuthenticatedQuorum
            }
            #[cfg(feature = "private-attested-clearing")]
            InstalledVerifier::PrivateBfvAttested(_) => {
                FheggVerifierRegistryKind::PrivateBfvAttested
            }
        }
    }

    #[cfg(feature = "private-attested-clearing")]
    fn private_bfv_attested(verifier: PrivateBfvAttestedClearingVerifier) -> Self {
        Self {
            installed: InstalledVerifier::PrivateBfvAttested(verifier),
        }
    }

    /// Mint a downstream authority only when this deployment installed the
    /// complete private-book verifier and the exact receipt composite verifies.
    /// An ordinary authenticated-quorum registry cannot be promoted into a
    /// private/HidingFRI/BFV game consequence.
    #[cfg(feature = "private-attested-clearing")]
    pub fn verify_private_bfv_authority(
        &self,
        receipt: &fhegg_fhe::attestation::AttestedClearingReceipt,
        expected: &fhegg_fhe::attestation::ExpectedClearingContext<'_>,
    ) -> Result<PrivateBfvVerifiedAuthority, FheggVerifierRegistryError> {
        match &self.installed {
            InstalledVerifier::AuthenticatedQuorum(_) => {
                Err(FheggVerifierRegistryError::WrongVerifierKind)
            }
            InstalledVerifier::PrivateBfvAttested(verifier) => {
                Ok(verifier.verify_authority(receipt, expected)?)
            }
        }
    }

    /// Crate-private half of the specialized atomic path. This projects the
    /// exact private authority metadata, but the caller must immediately pass
    /// the same immutable receipt/context through `verify_full` using `self`.
    /// It exists so a game transition does not pay for the minutes-class
    /// HidingFRI/BFV composite twice.
    #[cfg(feature = "private-attested-clearing")]
    pub(crate) fn prepare_private_bfv_authority(
        &self,
        receipt: &fhegg_fhe::attestation::AttestedClearingReceipt,
        expected: &fhegg_fhe::attestation::ExpectedClearingContext<'_>,
    ) -> Result<PrivateBfvVerifiedAuthority, FheggVerifierRegistryError> {
        match &self.installed {
            InstalledVerifier::AuthenticatedQuorum(_) => {
                Err(FheggVerifierRegistryError::WrongVerifierKind)
            }
            InstalledVerifier::PrivateBfvAttested(verifier) => {
                Ok(verifier.prepare_authority_metadata(receipt, expected)?)
            }
        }
    }
}

impl ComputationIntegrityVerifier for FheggVerifierRegistry {
    fn verifier_id(&self) -> Digest32 {
        match &self.installed {
            InstalledVerifier::AuthenticatedQuorum(verifier) => verifier.verifier_id(),
            #[cfg(feature = "private-attested-clearing")]
            InstalledVerifier::PrivateBfvAttested(verifier) => verifier.verifier_id(),
        }
    }

    fn verify(&self, claim_digest: &Digest32, evidence: &[u8]) -> bool {
        match &self.installed {
            InstalledVerifier::AuthenticatedQuorum(verifier) => {
                verifier.verify(claim_digest, evidence)
            }
            #[cfg(feature = "private-attested-clearing")]
            InstalledVerifier::PrivateBfvAttested(verifier) => {
                verifier.verify(claim_digest, evidence)
            }
        }
    }

    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        match &self.installed {
            InstalledVerifier::AuthenticatedQuorum(verifier) => {
                verifier.verify_claim(claim, evidence)
            }
            #[cfg(feature = "private-attested-clearing")]
            InstalledVerifier::PrivateBfvAttested(verifier) => {
                verifier.verify_claim(claim, evidence)
            }
        }
    }
}

/// Fail-closed reconstruction errors for the hosted private verifier.
#[cfg(feature = "private-attested-clearing")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FheggVerifierRegistryError {
    Quorum(QuorumVerifierError),
    InvalidPolicy(PrivateAttestedVerifierConfigError),
    PrivateBfv(PrivateBfvAttestedVerifierConfigError),
    Authority(PrivateBfvAuthorityError),
    WrongVerifierKind,
    RosterBfvMismatch,
    VerifierIdMismatch {
        pinned: Digest32,
        reconstructed: Digest32,
    },
}

#[cfg(feature = "private-attested-clearing")]
impl fmt::Display for FheggVerifierRegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Quorum(error) => write!(f, "hosted fhEgg quorum refused: {error}"),
            Self::InvalidPolicy(error) => write!(f, "hosted private policy refused: {error}"),
            Self::PrivateBfv(error) => write!(f, "hosted private BFV verifier refused: {error}"),
            Self::Authority(error) => write!(f, "hosted private authority refused: {error}"),
            Self::WrongVerifierKind => write!(
                f,
                "hosted verifier is not the private HidingFRI + BFV policy"
            ),
            Self::RosterBfvMismatch => write!(
                f,
                "hosted signature roster does not match the BFV opening roster"
            ),
            Self::VerifierIdMismatch {
                pinned,
                reconstructed,
            } => write!(
                f,
                "hosted verifier id differs from deployment pin (pinned {}, reconstructed {})",
                HexDigest(pinned),
                HexDigest(reconstructed),
            ),
        }
    }
}

#[cfg(feature = "private-attested-clearing")]
impl std::error::Error for FheggVerifierRegistryError {}

#[cfg(feature = "private-attested-clearing")]
impl From<QuorumVerifierError> for FheggVerifierRegistryError {
    fn from(error: QuorumVerifierError) -> Self {
        Self::Quorum(error)
    }
}

#[cfg(feature = "private-attested-clearing")]
impl From<PrivateAttestedVerifierConfigError> for FheggVerifierRegistryError {
    fn from(error: PrivateAttestedVerifierConfigError) -> Self {
        Self::InvalidPolicy(error)
    }
}

#[cfg(feature = "private-attested-clearing")]
impl From<PrivateBfvAttestedVerifierConfigError> for FheggVerifierRegistryError {
    fn from(error: PrivateBfvAttestedVerifierConfigError) -> Self {
        Self::PrivateBfv(error)
    }
}

#[cfg(feature = "private-attested-clearing")]
impl From<PrivateBfvAuthorityError> for FheggVerifierRegistryError {
    fn from(error: PrivateBfvAuthorityError) -> Self {
        Self::Authority(error)
    }
}

/// Owning public restart/configuration material for the full source-bound
/// private verifier. Fields are private so callers cannot install a partially
/// rebuilt policy; [`install`](Self::install) is the only exit.
#[cfg(feature = "private-attested-clearing")]
#[derive(Clone)]
pub struct PrivateBfvHostedVerifierConfig {
    pinned_verifier_id: Digest32,
    quorum: HostedQuorumConfig,
    quorum_threshold: usize,
    value_bits: u32,
    bfv: BfvPublicIdentity,
    expected_claim_session_nonce: Digest32,
    statement: PublicStatement,
    params: BfvParams,
    public_key: CollectivePublicKey,
    ciphertexts: PrivateBookCiphertexts,
    source_inputs: Vec<InputDigest>,
    required_tail_inputs: Vec<InputDigest>,
}

#[cfg(feature = "private-attested-clearing")]
#[derive(Clone)]
enum HostedQuorumConfig {
    ClassicalCompatibility(Vec<[u8; 32]>),
    NativePostQuantum(Vec<NativePqPartyPublicKey>),
}

#[cfg(feature = "private-attested-clearing")]
impl HostedQuorumConfig {
    fn roster_len(&self) -> usize {
        match self {
            Self::ClassicalCompatibility(keys) => keys.len(),
            Self::NativePostQuantum(keys) => keys.len(),
        }
    }
}

#[cfg(feature = "private-attested-clearing")]
impl PrivateBfvHostedVerifierConfig {
    /// Capture every public preimage under an independently provisioned
    /// verifier-id pin. No proof or uploaded bundle is consulted here.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        pinned_verifier_id: Digest32,
        ordered_quorum_public_keys: Vec<[u8; 32]>,
        quorum_threshold: usize,
        value_bits: u32,
        bfv: BfvPublicIdentity,
        expected_claim_session_nonce: Digest32,
        statement: PublicStatement,
        params: BfvParams,
        public_key: CollectivePublicKey,
        ciphertexts: PrivateBookCiphertexts,
        source_inputs: Vec<InputDigest>,
    ) -> Self {
        Self {
            pinned_verifier_id,
            quorum: HostedQuorumConfig::ClassicalCompatibility(ordered_quorum_public_keys),
            quorum_threshold,
            value_bits,
            bfv,
            expected_claim_session_nonce,
            statement,
            params,
            public_key,
            ciphertexts,
            source_inputs,
            required_tail_inputs: Vec::new(),
        }
    }

    /// Capture a strict native-PQ full-claim roster.  Reconstruction never
    /// converts this configuration into the classical compatibility verifier.
    #[allow(clippy::too_many_arguments)]
    pub fn new_native_post_quantum(
        pinned_verifier_id: Digest32,
        ordered_quorum_public_keys: Vec<NativePqPartyPublicKey>,
        quorum_threshold: usize,
        value_bits: u32,
        bfv: BfvPublicIdentity,
        expected_claim_session_nonce: Digest32,
        statement: PublicStatement,
        params: BfvParams,
        public_key: CollectivePublicKey,
        ciphertexts: PrivateBookCiphertexts,
        source_inputs: Vec<InputDigest>,
        required_tail_inputs: Vec<InputDigest>,
    ) -> Self {
        Self {
            pinned_verifier_id,
            quorum: HostedQuorumConfig::NativePostQuantum(ordered_quorum_public_keys),
            quorum_threshold,
            value_bits,
            bfv,
            expected_claim_session_nonce,
            statement,
            params,
            public_key,
            ciphertexts,
            source_inputs,
            required_tail_inputs,
        }
    }

    pub const fn pinned_verifier_id(&self) -> Digest32 {
        self.pinned_verifier_id
    }

    /// Reconstruct the complete verifier from public objects and require exact
    /// equality with the independent deployment pin before it can enter the
    /// hosted registry.
    pub fn install(&self) -> Result<FheggVerifierRegistry, FheggVerifierRegistryError> {
        if self.bfv.opening_threshold != self.quorum.roster_len() as u64
            || self.bfv.n_parties < self.bfv.opening_threshold
        {
            return Err(FheggVerifierRegistryError::RosterBfvMismatch);
        }
        let policy = PrivateAttestedClearingPolicy::new(self.value_bits, self.bfv.clone())?;
        let verifier = match &self.quorum {
            HostedQuorumConfig::ClassicalCompatibility(keys) => {
                PrivateBfvAttestedClearingVerifier::new_source_bound(
                    AuthenticatedQuorumVerifier::new(keys.clone(), self.quorum_threshold)?,
                    policy,
                    self.expected_claim_session_nonce,
                    self.statement,
                    self.params.clone(),
                    self.public_key.clone(),
                    self.ciphertexts.clone(),
                    self.source_inputs.clone(),
                )?
            }
            HostedQuorumConfig::NativePostQuantum(keys) => {
                PrivateBfvAttestedClearingVerifier::new_source_bound_native_post_quantum(
                    NativePqAuthenticatedQuorumVerifier::new(keys.clone(), self.quorum_threshold)?,
                    policy,
                    self.expected_claim_session_nonce,
                    self.statement,
                    self.params.clone(),
                    self.public_key.clone(),
                    self.ciphertexts.clone(),
                    self.source_inputs.clone(),
                    self.required_tail_inputs.clone(),
                )?
            }
        };
        let reconstructed = verifier.verifier_id();
        if reconstructed != self.pinned_verifier_id {
            return Err(FheggVerifierRegistryError::VerifierIdMismatch {
                pinned: self.pinned_verifier_id,
                reconstructed,
            });
        }
        Ok(FheggVerifierRegistry::private_bfv_attested(verifier))
    }
}

#[cfg(feature = "private-attested-clearing")]
struct HexDigest<'a>(&'a Digest32);

#[cfg(feature = "private-attested-clearing")]
impl fmt::Display for HexDigest<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

//! Authenticated DKG-to-table binding for collective Dark AMM bootstrap.
//!
//! A [`DarkPoolPublicHostMaterial`] carries a public key, but the bytes alone do
//! not show that the key is the aggregate of the configured custodian roster.
//! In particular, deriving `CollectivePublicKey` from those same material bytes
//! is circular: an accidentally single-owner key can call itself collective.
//!
//! This module consumes the public `DBPAv001` artifacts emitted independently
//! by `dark-amm-tool collective-party-contribute`.  Every artifact authenticates
//! one canonical fhe.rs public-key contribution under the corresponding
//! decision-roster key and binds it to the exact public worker configuration.
//! Verification replays all contributions, in canonical party order, through
//! [`KeygenCoordinator`] and requires the resulting aggregate key to byte-equal
//! the key in the table's public material before an offering can be built.
//!
//! This closes a real configuration/custody substitution seam.  It does not
//! prove the hidden DKG shares are ternary/CBD-short, bind the public
//! relinearization key to its opaque upstream R1/R2 shares, or prove that the
//! initial reserve ciphertexts open to values whose integer product is `k`.
//! Those are separate lattice/bootstrap certificate obligations.

use std::fmt;

use crate::attestation::AuthenticatedQuorumVerifier;
use crate::dark_amm::{DarkPool, DarkPoolPublicHostMaterial};
use crate::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, PublicKeyContribution,
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use fhe_traits::Serialize as FheSerialize;

const ARTIFACT_MAGIC: &[u8; 8] = b"DBPAv001";
const WORKER_CONFIG_MAGIC: &[u8; 8] = b"DBWCv001";
const CONFIG_DIGEST_DOMAIN: &str = "dregg-dark-amm-collective-worker-configuration-v1";
const SIGNATURE_DOMAIN: &str = "dregg-dark-amm-collective-party-artifact-signature-v1";
const CHECKSUM_DOMAIN: &str = "dregg-dark-amm-collective-worker-input-checksum-v1";
pub const MAX_COLLECTIVE_DKG_CONFIG_BYTES: usize = 64 * 1024;
const MAX_WORKER_TIMEOUT_MILLIS: u64 = 5 * 60 * 1_000;
/// Same bounded ceiling as the command-line producer/consumer.
pub const MAX_COLLECTIVE_DKG_ARTIFACT_BYTES: usize = 64 * 1024 * 1024;

/// Stable fail-closed reasons for the public DKG/table join.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectiveDkgBindingError {
    InvalidConfiguration(&'static str),
    MalformedArtifact(&'static str),
    ConfigMismatch,
    PartyOutOfRange { party: usize, n_parties: usize },
    NonCanonicalPartyOrder { expected: usize, found: usize },
    ContributionMismatch,
    SignerMismatch { party: usize },
    InvalidSignature { party: usize },
    ArtifactCount { have: usize, need: usize },
    KeygenRefused(String),
    MaterialRefused(String),
    CollectiveKeyMismatch,
}

impl fmt::Display for CollectiveDkgBindingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidConfiguration(reason) => {
                write!(f, "invalid collective DKG binding configuration: {reason}")
            }
            Self::MalformedArtifact(reason) => {
                write!(f, "malformed collective DKG artifact: {reason}")
            }
            Self::ConfigMismatch => write!(f, "collective DKG artifact names another config"),
            Self::PartyOutOfRange { party, n_parties } => write!(
                f,
                "collective DKG artifact party {party} is outside 0..{n_parties}"
            ),
            Self::NonCanonicalPartyOrder { expected, found } => write!(
                f,
                "collective DKG artifacts are not in canonical order: expected {expected}, found {found}"
            ),
            Self::ContributionMismatch => {
                write!(
                    f,
                    "collective DKG contribution has another session or party"
                )
            }
            Self::SignerMismatch { party } => {
                write!(f, "collective DKG signer does not own party slot {party}")
            }
            Self::InvalidSignature { party } => {
                write!(
                    f,
                    "collective DKG artifact {party} has an invalid signature"
                )
            }
            Self::ArtifactCount { have, need } => write!(
                f,
                "collective DKG needs exactly {need} party artifacts, received {have}"
            ),
            Self::KeygenRefused(reason) => {
                write!(f, "collective DKG aggregation refused: {reason}")
            }
            Self::MaterialRefused(reason) => {
                write!(f, "collective table material refused: {reason}")
            }
            Self::CollectiveKeyMismatch => write!(
                f,
                "collective table key is not the aggregate of the authenticated DKG contributions"
            ),
        }
    }
}

impl std::error::Error for CollectiveDkgBindingError {}

type Result<T> = std::result::Result<T, CollectiveDkgBindingError>;

/// One party's authenticated public DKG contribution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollectivePartyContributionArtifact {
    party: usize,
    config_digest: [u8; 32],
    contribution: PublicKeyContribution,
    signature: [u8; 64],
}

impl CollectivePartyContributionArtifact {
    /// Issue the exact artifact format used by `dark-amm-tool`.
    pub fn issue(
        config_wire: &[u8],
        keygen: &KeygenSession,
        verifier: &AuthenticatedQuorumVerifier,
        contribution: PublicKeyContribution,
        signing_key: &SigningKey,
    ) -> Result<Self> {
        validate_configuration(config_wire, keygen, verifier)?;
        let party = contribution.party();
        if party >= keygen.n_parties() {
            return Err(CollectiveDkgBindingError::PartyOutOfRange {
                party,
                n_parties: keygen.n_parties(),
            });
        }
        if contribution.session() != keygen {
            return Err(CollectiveDkgBindingError::ContributionMismatch);
        }
        let expected = verifier.ordered_public_keys().get(party).ok_or(
            CollectiveDkgBindingError::PartyOutOfRange {
                party,
                n_parties: keygen.n_parties(),
            },
        )?;
        if signing_key.verifying_key().to_bytes() != *expected {
            return Err(CollectiveDkgBindingError::SignerMismatch { party });
        }
        let config_digest = config_digest(config_wire);
        let contribution_wire = contribution.to_wire_bytes();
        let signature = signing_key
            .sign(&artifact_signing_message(
                party,
                &config_digest,
                &contribution_wire,
            ))
            .to_bytes();
        Ok(Self {
            party,
            config_digest,
            contribution,
            signature,
        })
    }

    pub const fn party(&self) -> usize {
        self.party
    }

    pub fn contribution(&self) -> &PublicKeyContribution {
        &self.contribution
    }

    /// Strict canonical `DBPAv001` wire, compatible with the existing CLI.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let contribution = self.contribution.to_wire_bytes();
        let mut out = Vec::with_capacity(152 + contribution.len());
        out.extend_from_slice(ARTIFACT_MAGIC);
        out.extend_from_slice(
            &u64::try_from(self.party)
                .expect("validated DKG party index fits the canonical u64 wire")
                .to_le_bytes(),
        );
        out.extend_from_slice(&self.config_digest);
        out.extend_from_slice(
            &u64::try_from(contribution.len())
                .expect("bounded DKG contribution length fits the canonical u64 wire")
                .to_le_bytes(),
        );
        out.extend_from_slice(&contribution);
        out.extend_from_slice(&self.signature);
        out.extend_from_slice(&checksum(&out));
        out
    }

    /// Decode and authenticate one artifact against independently supplied
    /// ceremony and signer policy.
    pub fn from_wire_bytes(
        bytes: &[u8],
        config_wire: &[u8],
        keygen: &KeygenSession,
        verifier: &AuthenticatedQuorumVerifier,
    ) -> Result<Self> {
        validate_configuration(config_wire, keygen, verifier)?;
        if bytes.len() < 8 + 8 + 32 + 8 + 64 + 32 || bytes.len() > MAX_COLLECTIVE_DKG_ARTIFACT_BYTES
        {
            return Err(CollectiveDkgBindingError::MalformedArtifact(
                "length is outside the allocation bounds",
            ));
        }
        let content_end = bytes.len() - 32;
        if bytes[content_end..] != checksum(&bytes[..content_end]) {
            return Err(CollectiveDkgBindingError::MalformedArtifact(
                "checksum mismatch",
            ));
        }
        let mut input = Reader::new(&bytes[..content_end]);
        if input.array::<8>()? != *ARTIFACT_MAGIC {
            return Err(CollectiveDkgBindingError::MalformedArtifact(
                "wrong artifact version",
            ));
        }
        let party = input.usize()?;
        if party >= keygen.n_parties() {
            return Err(CollectiveDkgBindingError::PartyOutOfRange {
                party,
                n_parties: keygen.n_parties(),
            });
        }
        let encoded_config_digest = input.array::<32>()?;
        let expected_config_digest = config_digest(config_wire);
        if encoded_config_digest != expected_config_digest {
            return Err(CollectiveDkgBindingError::ConfigMismatch);
        }
        let contribution_wire = input.bytes(MAX_COLLECTIVE_DKG_ARTIFACT_BYTES)?;
        let signature = input.array::<64>()?;
        input.finish()?;
        let contribution = PublicKeyContribution::from_wire_bytes(contribution_wire)
            .map_err(|error| CollectiveDkgBindingError::KeygenRefused(format!("{error:?}")))?;
        if contribution.party() != party || contribution.session() != keygen {
            return Err(CollectiveDkgBindingError::ContributionMismatch);
        }
        if contribution.to_wire_bytes() != contribution_wire {
            return Err(CollectiveDkgBindingError::MalformedArtifact(
                "contribution is not canonical",
            ));
        }
        let public_key = verifier.ordered_public_keys().get(party).ok_or(
            CollectiveDkgBindingError::PartyOutOfRange {
                party,
                n_parties: keygen.n_parties(),
            },
        )?;
        let verifying = VerifyingKey::from_bytes(public_key)
            .map_err(|_| CollectiveDkgBindingError::InvalidSignature { party })?;
        verifying
            .verify_strict(
                &artifact_signing_message(party, &encoded_config_digest, contribution_wire),
                &Signature::from_bytes(&signature),
            )
            .map_err(|_| CollectiveDkgBindingError::InvalidSignature { party })?;
        let artifact = Self {
            party,
            config_digest: encoded_config_digest,
            contribution,
            signature,
        };
        if artifact.to_wire_bytes() != bytes {
            return Err(CollectiveDkgBindingError::MalformedArtifact(
                "artifact is not canonical",
            ));
        }
        Ok(artifact)
    }
}

/// Capability returned only after the complete authenticated contribution
/// roster reproduces the exact public key carried by the table material.
#[derive(Clone)]
pub struct VerifiedCollectiveDkg {
    collective: CollectivePublicKey,
    transcript_digest: [u8; 32],
}

impl VerifiedCollectiveDkg {
    pub fn collective(&self) -> &CollectivePublicKey {
        &self.collective
    }

    pub const fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }
}

/// Verify the complete DKG contribution roster and its exact join to one
/// public Dark Pool carrier.
pub fn verify_collective_dkg_binding(
    config_wire: &[u8],
    keygen: &KeygenSession,
    params: &BfvParams,
    verifier: &AuthenticatedQuorumVerifier,
    material: &DarkPoolPublicHostMaterial,
    artifact_wires: &[&[u8]],
) -> Result<VerifiedCollectiveDkg> {
    validate_configuration(config_wire, keygen, verifier)?;
    let need = keygen.n_parties();
    if artifact_wires.len() != need {
        return Err(CollectiveDkgBindingError::ArtifactCount {
            have: artifact_wires.len(),
            need,
        });
    }
    DarkPool::restore_public_host(params.arc(), material)
        .map_err(|error| CollectiveDkgBindingError::MaterialRefused(error.to_string()))?;

    let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
    let mut transcript =
        blake3::Hasher::new_derive_key("dregg-dark-amm-authenticated-dkg-transcript-v1");
    transcript.update(&config_digest(config_wire));
    transcript.update(
        &u64::try_from(need)
            .expect("validated DKG roster length fits the canonical u64 transcript")
            .to_le_bytes(),
    );
    for (expected_party, wire) in artifact_wires.iter().enumerate() {
        let artifact = CollectivePartyContributionArtifact::from_wire_bytes(
            wire,
            config_wire,
            keygen,
            verifier,
        )?;
        if artifact.party != expected_party {
            return Err(CollectiveDkgBindingError::NonCanonicalPartyOrder {
                expected: expected_party,
                found: artifact.party,
            });
        }
        transcript.update(
            &u64::try_from(wire.len())
                .expect("bounded DKG artifact length fits the canonical u64 transcript")
                .to_le_bytes(),
        );
        transcript.update(blake3::hash(wire).as_bytes());
        coordinator
            .accept(artifact.contribution)
            .map_err(|error| CollectiveDkgBindingError::KeygenRefused(format!("{error:?}")))?;
    }
    let collective = coordinator
        .finish()
        .map_err(|error| CollectiveDkgBindingError::KeygenRefused(format!("{error:?}")))?;
    if collective.pk.to_bytes() != material.public_key_bytes() {
        return Err(CollectiveDkgBindingError::CollectiveKeyMismatch);
    }
    transcript.update(&material.material_digest());
    Ok(VerifiedCollectiveDkg {
        collective,
        transcript_digest: *transcript.finalize().as_bytes(),
    })
}

fn validate_configuration(
    config_wire: &[u8],
    keygen: &KeygenSession,
    verifier: &AuthenticatedQuorumVerifier,
) -> Result<()> {
    if config_wire.is_empty() || config_wire.len() > MAX_COLLECTIVE_DKG_CONFIG_BYTES {
        return Err(CollectiveDkgBindingError::InvalidConfiguration(
            "public worker config must be nonempty and bounded",
        ));
    }
    if keygen.n_parties() < 2 {
        return Err(CollectiveDkgBindingError::InvalidConfiguration(
            "collective custody requires at least two parties",
        ));
    }
    if verifier.ordered_public_keys().len() != keygen.n_parties() {
        return Err(CollectiveDkgBindingError::InvalidConfiguration(
            "signer roster and keygen party counts differ",
        ));
    }
    if config_wire.len() < WORKER_CONFIG_MAGIC.len() + 32 {
        return Err(CollectiveDkgBindingError::InvalidConfiguration(
            "public worker config is truncated",
        ));
    }
    let content_end = config_wire.len() - 32;
    if config_wire[content_end..] != checksum(&config_wire[..content_end]) {
        return Err(CollectiveDkgBindingError::InvalidConfiguration(
            "public worker config checksum mismatch",
        ));
    }
    let mut input = Reader::new(&config_wire[..content_end]);
    let malformed =
        |_| CollectiveDkgBindingError::InvalidConfiguration("public worker config is malformed");
    if input.array::<8>().map_err(malformed)? != *WORKER_CONFIG_MAGIC {
        return Err(CollectiveDkgBindingError::InvalidConfiguration(
            "wrong public worker config version",
        ));
    }
    let n_parties = input.usize().map_err(malformed)?;
    let crp_seed = input.array::<32>().map_err(malformed)?;
    let value_bits = input.usize().map_err(malformed)?;
    let timeout_millis = u64::from_le_bytes(input.array::<8>().map_err(malformed)?);
    let threshold = input.usize().map_err(malformed)?;
    let roster_count = input.usize().map_err(malformed)?;
    if n_parties != keygen.n_parties()
        || crp_seed != keygen.crp_seed()
        || roster_count != n_parties
        || threshold != verifier.threshold()
        || !(1..=63).contains(&value_bits)
        || timeout_millis == 0
        || timeout_millis > MAX_WORKER_TIMEOUT_MILLIS
    {
        return Err(CollectiveDkgBindingError::InvalidConfiguration(
            "public worker config disagrees with the pinned DKG or decision policy",
        ));
    }
    for expected in verifier.ordered_public_keys() {
        if input.array::<32>().map_err(malformed)? != *expected {
            return Err(CollectiveDkgBindingError::InvalidConfiguration(
                "public worker config decision roster differs from relying-party policy",
            ));
        }
    }
    input.finish().map_err(malformed)?;
    Ok(())
}

fn config_digest(config_wire: &[u8]) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(CONFIG_DIGEST_DOMAIN);
    hash.update(
        &u64::try_from(config_wire.len())
            .expect("bounded worker config length fits the canonical u64 digest")
            .to_le_bytes(),
    );
    hash.update(config_wire);
    *hash.finalize().as_bytes()
}

fn artifact_signing_message(
    party: usize,
    config_digest: &[u8; 32],
    contribution_wire: &[u8],
) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(SIGNATURE_DOMAIN);
    hash.update(
        &u64::try_from(party)
            .expect("validated DKG party index fits the canonical u64 signature message")
            .to_le_bytes(),
    );
    hash.update(config_digest);
    hash.update(
        &u64::try_from(contribution_wire.len())
            .expect("bounded DKG contribution length fits the canonical u64 signature message")
            .to_le_bytes(),
    );
    hash.update(blake3::hash(contribution_wire).as_bytes());
    *hash.finalize().as_bytes()
}

fn checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(CHECKSUM_DOMAIN);
    hash.update(
        &u64::try_from(content.len())
            .expect("bounded DKG artifact length fits the canonical u64 checksum")
            .to_le_bytes(),
    );
    hash.update(content);
    *hash.finalize().as_bytes()
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
            .ok_or(CollectiveDkgBindingError::MalformedArtifact(
                "truncated field",
            ))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.take(N)?
            .try_into()
            .map_err(|_| CollectiveDkgBindingError::MalformedArtifact("invalid fixed field"))
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(u64::from_le_bytes(self.array()?)).map_err(|_| {
            CollectiveDkgBindingError::MalformedArtifact("integer does not fit this platform")
        })
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8]> {
        let len = self.usize()?;
        if len > max {
            return Err(CollectiveDkgBindingError::MalformedArtifact(
                "length-delimited field exceeds its limit",
            ));
        }
        self.take(len)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(CollectiveDkgBindingError::MalformedArtifact(
                "trailing bytes",
            ))
        }
    }
}

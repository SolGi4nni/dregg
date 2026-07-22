//! Crash-tolerant `t < n` BFV custody and threshold opening.
//!
//! This is a process-shaped distributed-key-generation and decryption path.
//! Every one of the `n` dealers samples a ternary BFV secret contribution and
//! shares each of its RNS coefficients with a random symmetric bivariate
//! polynomial of degree `t - 1` in each variable.  Each recipient gets one
//! polynomial row: its constant coefficient is the ordinary Shamir share, and
//! pairwise cross-evaluations (`F(i,j) = F(j,i)`) prove that all committed rows
//! belong to one common bivariate polynomial.  The dealer shares the BFV
//! key-generation error in a second bivariate polynomial and publishes every
//! coefficient's exact BFV linear image `C_ab = -a*s_ab + e_ab`.  Recipients
//! verify their private rows against those public images; since `n > t-1`, the
//! accepted equations pin `C_00` to the real fhe.rs public share `p0`.  Salted
//! public row commitments bind the exact private rows checked by the
//! recipients.  Recipients add only the verified secret evaluations locally;
//! no API constructs the corresponding joint secret key.
//!
//! For an opening, the relying party first names exactly `t` live parties.
//! Each selected party applies its Lagrange coefficient locally, adds the
//! Lean-pinned smudge, and emits one public decryption share.  Consequently
//! any `t` parties can open while `n - t` may be offline.  The opening API
//! refuses undersized/non-canonical rosters, missing or duplicate shares,
//! cross-session/cross-ciphertext mixing, and repeat openings of the same
//! ciphertext by one in-memory party state.  [`AuthenticatedQuorumRoster`]
//! and [`AuthenticatedQuorumCombiner`] additionally provide a strict Ed25519
//! transport whose signatures cover the exact DKG identity, custody identity
//! roster, opening nonce/roster, ciphertext, smudge declaration, and share.
//! A successful authenticated combine can also emit
//! [`AuthenticatedOpeningAudit`], a digest-only commitment to that canonical
//! ordered transcript for binding into an outer receipt without copying share
//! coefficients into it.
//!
//! ## Security boundary
//!
//! This is **not yet malicious-secure BFV DKG**.  The bivariate VSS rung is a
//! genuine algebraic consistency check: a dealer cannot give recipients
//! mutually inconsistent degree-`(t-1)` rows without a cross-evaluation
//! complaint, and the salted commitments bind the rows that were checked.
//! Dealer-to-recipient rows and recipient-to-recipient cross-evaluations still
//! require confidential authenticated transport, and all dealers must be
//! available during setup.  The transcript proves the exact algebraic relation
//! between its hidden constants and `p0 = -a*s + e`; it does **not** prove in
//! zero knowledge that those hidden constants are in the required ternary/CBD
//! short ranges.  That is the remaining keygen lattice range-proof seam.
//! A verified-DKG opening now carries a zero-knowledge decryption-share
//! certificate anchored to coefficient-wise Pedersen commitments in that VSS
//! transcript.  Its Bulletproof range arguments and batched Schnorr
//! representation prove `h = lambda * canonical(c1*s_i) + smudge`, including
//! the exact RNS reduction quotients, with every smudge coefficient in the
//! Lean-pinned inclusive range `[-2^80, 2^80]`.  The Fiat-Shamir transcript
//! binds the DKG, custody party and index, opening, exact ciphertext, and public
//! share.  Legacy setup deliberately cannot produce this certificate and a
//! verified combiner rejects it.  The remaining cryptographic seams are the
//! keygen ternary/CBD range proof above and a distributed ceremony in which
//! parties publish and endorse the secret-share commitments; today the
//! verified setup transition constructs those commitments while assembling the
//! accepted VSS result.  The proof is also correctness-grade rather than
//! interactive-grade at BFV degree 4096: it ranges tens of thousands of scalar
//! witnesses per share and still needs a compressed/batched production path.
//! Replay state is in-memory, not persistent.  Under an accepted VSS transcript
//! and at least one honest dealer, fewer than `t` custody parties do not
//! reconstruct the BFV secret; the public result is revealed only after an
//! exact `t`-party opening.
//!
//! The optional q0 BabyBear commitment round below is explicitly
//! experimental.  It gives each party local custody of a field-native opening
//! and binds ordered public contributions into a follow-up digest, but it is
//! neither a public same-opening proof against the Ristretto VSS commitment nor
//! an authenticated broadcast ceremony.  `finish_verified_keygen` also still
//! receives all private dealer bundles.  Classical quorum proof verification
//! remains the live authority; the q0 round is preparatory HidingFRI substrate.

use bulletproofs_r1cs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    traits::VartimeMultiscalarMul,
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use ethnum::I256;
use fhe::bfv::{Ciphertext, Encoding, PublicKey};
use fhe::mbfv::{Aggregate, PublicKeyShare};
use fhe_math::rq::{traits::TryConvertFrom, Context as RqContext, Poly, Representation};
use fhe_traits::{DeserializeParametrized, FheDecoder, FheDecrypter, Serialize as FheSerialize};
use rand_09::Rng;
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::sync::OnceLock;

use merlin::Transcript;
use rand::{rngs::OsRng, CryptoRng, RngCore};

use super::{
    add_mod, aggregate_public_contributions, sk_from_coeffs, BfvParams, CollectivePublicKey,
    KeygenSession, PublicKeyContribution, RnsPoly, MAX_SMUDGE_BITS_TOTAL, MIN_SMUDGE_BITS,
};
use crate::bfv_lean::LeanCiphertext;
use crate::pq_share_commitment::{
    ExperimentalBfvQ0ShareCommitmentKey, ExperimentalBfvQ0ShareOpening, PqShareCommitment,
    BFV_Q0_DEGREE, BFV_Q0_MODULUS,
};

pub type Result<T> = std::result::Result<T, QuorumError>;

const AUTHENTICATED_SHARE_MAGIC: &[u8; 8] = b"FHQAv001";
const AUTHENTICATED_ROSTER_DOMAIN: &[u8] = b"fhegg/quorum-authenticated-roster/v1";
const AUTHENTICATED_SHARE_DOMAIN: &[u8] = b"fhegg/quorum-authenticated-decrypt-share/v1";
const AUTHENTICATED_TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/quorum-opening-transcript/v1";
const AUTHENTICATED_AUDIT_DOMAIN: &[u8] = b"fhegg/quorum-opening-audit/v1";
const DKG_Q0_SHARE_SEED_DOMAIN: &[u8] = b"fhegg/dkg-q0-share-commitment-seed/v1";
const OPENING_SESSION_DOMAIN: &[u8] = b"fhegg/quorum-opening-session/v1";
const VSS_COMMITMENT_MAGIC: &[u8; 8] = b"FHQVv001";
const VSS_ROW_COMMITMENT_DOMAIN: &[u8] = b"fhegg/quorum-bivariate-vss-row/v1";
const VSS_DEALER_COMMITMENT_DOMAIN: &[u8] = b"fhegg/quorum-bivariate-vss-dealer/v1";
const VSS_SETUP_TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/quorum-bivariate-vss-setup/v2";
const VSS_Q0_ANCHORED_TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/quorum-bivariate-vss-q0-anchor/v1";
const VERIFIED_DKG_COLLECTIVE_KEY_DOMAIN: &[u8] = b"fhegg/quorum-verified-dkg-collective-key/v1";
const DECRYPT_SHARE_PROOF_DOMAIN: &[u8] = b"fhegg/quorum-decrypt-share-proof/v1";
const DECRYPT_SHARE_PROOF_MAGIC: &[u8; 8] = b"FHQPv001";
const DECRYPT_SHARE_RELATION_DOMAIN: &[u8] = b"fhegg/quorum-decrypt-relation/v1";
const DECRYPT_QUOTIENT_OFFSET: u64 = 1u64 << 63;

/// Fail-closed protocol errors.  They are intentionally more specific than
/// the legacy n-of-n API so a caller can distinguish liveness from confusion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuorumError {
    InvalidParameters,
    InvalidParty {
        party: usize,
        n_parties: usize,
    },
    QuorumTooSmall {
        have: usize,
        need: usize,
    },
    NonCanonicalRoster,
    MissingDealerShares {
        have: usize,
        need: usize,
    },
    DuplicateDealer {
        dealer: usize,
    },
    DuplicateParty {
        party: usize,
    },
    MissingCustodyParty {
        party: usize,
    },
    CustodyWorkerPanicked {
        party: usize,
    },
    SessionMismatch,
    RecipientMismatch {
        expected: usize,
        actual: usize,
    },
    PartyNotSelected {
        party: usize,
    },
    ParamMismatch,
    SmudgeTooSmall,
    SmudgeTooLarge,
    Replay,
    MalformedWire,
    InvalidPublicKey {
        party: usize,
    },
    DuplicatePublicKey {
        party: usize,
    },
    SignerKeyMismatch {
        party: usize,
    },
    InvalidSignature {
        party: usize,
    },
    AuthenticationRosterMismatch,
    NonCanonicalShareOrder,
    VssCommitmentMismatch {
        dealer: usize,
        recipient: usize,
    },
    VssInconsistentRows {
        dealer: usize,
        left: usize,
        right: usize,
    },
    VssPublicImageMismatch {
        dealer: usize,
        recipient: usize,
    },
    VssTranscriptMismatch,
    MissingDecryptShareProof {
        party: usize,
    },
    InvalidDecryptShareProof {
        party: usize,
    },
    UnsupportedDecryptProofParameters,
    /// The experimental q0 contribution round has no identity-signed,
    /// broadcast-consistent cross-commitment ceremony yet.
    ExperimentalQ0CeremonyUnauthenticated,
}

impl fmt::Display for QuorumError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for QuorumError {}

/// Public setup parameters for a strict `t < n` custody group.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumKeygenSession {
    base: KeygenSession,
    threshold: usize,
}

impl QuorumKeygenSession {
    pub fn from_seed(n_parties: usize, threshold: usize, crp_seed: [u8; 32]) -> Result<Self> {
        if threshold < 2 || threshold >= n_parties {
            return Err(QuorumError::InvalidParameters);
        }
        let base = KeygenSession::from_seed(n_parties, crp_seed)
            .map_err(|_| QuorumError::InvalidParameters)?;
        Ok(Self { base, threshold })
    }

    pub fn n_parties(&self) -> usize {
        self.base.n_parties()
    }

    pub fn threshold(&self) -> usize {
        self.threshold
    }

    /// Public n-party session accepted by the existing public-key coordinator.
    pub fn public_key_session(&self) -> &KeygenSession {
        &self.base
    }
}

/// One dealer's private Shamir evaluation for one recipient.
///
/// This object intentionally has no `Clone`, `Debug`, serializer, or share
/// accessor.  Moving it through a confidential authenticated channel is a host
/// obligation; a public wire codec here would make accidental disclosure easy.
pub struct PrivateDealerShare {
    session: QuorumKeygenSession,
    dealer: usize,
    recipient: usize,
    rows: Vec<Vec<u64>>,
    /// Coefficients of the recipient's private row `F(recipient + 1, y)`,
    /// indexed `[y_degree][rns_modulus][ring_coefficient]`.
    vss_row_coefficients: Vec<Vec<Vec<u64>>>,
    /// Matching private row of the BFV keygen error polynomial. Together the
    /// rows are checked against the public `-a*s + e` coefficient images.
    vss_error_row_coefficients: Vec<Vec<Vec<u64>>>,
    /// Hiding salt for this row's public commitment.  This rides the same
    /// confidential channel as the row and is never included in the public
    /// transcript.
    vss_salt: [u8; 32],
}

impl PrivateDealerShare {
    pub fn dealer(&self) -> usize {
        self.dealer
    }

    pub fn recipient(&self) -> usize {
        self.recipient
    }
}

/// Public contribution plus the `n` private messages produced by one dealer.
pub struct DealerBundle {
    public: PublicKeyContribution,
    private: Vec<PrivateDealerShare>,
    vss_commitment: DealerVssCommitment,
}

impl DealerBundle {
    pub fn vss_commitment(&self) -> &DealerVssCommitment {
        &self.vss_commitment
    }

    pub fn into_parts(self) -> (PublicKeyContribution, Vec<PrivateDealerShare>) {
        (self.public, self.private)
    }

    /// Verify every private row opening and every pairwise bivariate
    /// cross-evaluation before any recipient state can be assembled through
    /// the verified path.
    pub fn verify(self, params: &BfvParams) -> Result<VerifiedDealerBundle> {
        verify_dealer_bundle(self, params)
    }
}

/// Public commitment to one dealer's complete bivariate-VSS dealing.
///
/// Each recipient-row digest is salted; the salt and row travel privately to
/// that recipient.  The dealer digest additionally binds the exact fhe.rs
/// public-key contribution bytes. The public linear images additionally link
/// the hidden bivariate constants to that public share algebraically; hidden
/// shortness/range remains outside this commitment rung.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DealerVssCommitment {
    session: QuorumKeygenSession,
    dealer: usize,
    public_key_digest: [u8; 32],
    row_commitments: Vec<[u8; 32]>,
    /// `C_ab = -a*s_ab + e_ab`, flattened in x-major/y-minor order; every
    /// entry is one RNS ring polynomial.
    linear_commitments: Vec<Vec<Vec<u64>>>,
    digest: [u8; 32],
}

impl DealerVssCommitment {
    pub fn dealer(&self) -> usize {
        self.dealer
    }

    pub fn row_commitments(&self) -> &[[u8; 32]] {
        &self.row_commitments
    }

    pub fn linear_commitments(&self) -> &[Vec<Vec<u64>>] {
        &self.linear_commitments
    }

    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Canonical public wire form. The private rows and salts are deliberately
    /// absent; this message is safe to broadcast (authentication is supplied by
    /// the ceremony transport / later custody endorsements).
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let coefficient_count = self
            .linear_commitments
            .iter()
            .flat_map(|commitment| commitment.iter())
            .map(Vec::len)
            .sum::<usize>();
        let mut out = Vec::with_capacity(
            8 + 8 * 4 + 32 * (3 + self.row_commitments.len()) + coefficient_count * 8,
        );
        out.extend_from_slice(VSS_COMMITMENT_MAGIC);
        out.extend_from_slice(&(self.session.n_parties() as u64).to_le_bytes());
        out.extend_from_slice(&(self.session.threshold() as u64).to_le_bytes());
        out.extend_from_slice(&self.session.base.crp_seed());
        out.extend_from_slice(&(self.dealer as u64).to_le_bytes());
        out.extend_from_slice(&self.public_key_digest);
        out.extend_from_slice(&(self.row_commitments.len() as u64).to_le_bytes());
        for commitment in &self.row_commitments {
            out.extend_from_slice(commitment);
        }
        out.extend_from_slice(&(self.linear_commitments.len() as u64).to_le_bytes());
        for commitment in &self.linear_commitments {
            for row in commitment {
                for &value in row {
                    out.extend_from_slice(&value.to_le_bytes());
                }
            }
        }
        out.extend_from_slice(&self.digest);
        out
    }

    /// Parse and re-hash a canonical public VSS commitment message.
    pub fn from_wire_bytes(bytes: &[u8], params: &BfvParams) -> Result<Self> {
        let mut cursor = WireCursor::new(bytes);
        if cursor.take::<8>()? != *VSS_COMMITMENT_MAGIC {
            return Err(QuorumError::MalformedWire);
        }
        let n = cursor.usize()?;
        let threshold = cursor.usize()?;
        let seed = cursor.take::<32>()?;
        let session = QuorumKeygenSession::from_seed(n, threshold, seed)?;
        let dealer = cursor.usize()?;
        if dealer >= n {
            return Err(QuorumError::InvalidParty {
                party: dealer,
                n_parties: n,
            });
        }
        let public_key_digest = cursor.take::<32>()?;
        let row_count = cursor.usize()?;
        if row_count != n {
            return Err(QuorumError::MalformedWire);
        }
        let mut row_commitments = Vec::with_capacity(row_count);
        for _ in 0..row_count {
            row_commitments.push(cursor.take::<32>()?);
        }
        let linear_count = cursor.usize()?;
        if linear_count != threshold * threshold {
            return Err(QuorumError::MalformedWire);
        }
        let mut linear_commitments = Vec::with_capacity(linear_count);
        for _ in 0..linear_count {
            let mut commitment = Vec::with_capacity(params.moduli().len());
            for &q in params.moduli() {
                let mut row = Vec::with_capacity(params.degree());
                for _ in 0..params.degree() {
                    let value = u64::from_le_bytes(cursor.take::<8>()?);
                    if value >= q {
                        return Err(QuorumError::MalformedWire);
                    }
                    row.push(value);
                }
                commitment.push(row);
            }
            linear_commitments.push(commitment);
        }
        let digest = cursor.take::<32>()?;
        if !cursor.finished()
            || dealer_vss_commitment_digest(
                &session,
                dealer,
                &public_key_digest,
                &row_commitments,
                &linear_commitments,
            ) != digest
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        Ok(Self {
            session,
            dealer,
            public_key_digest,
            row_commitments,
            linear_commitments,
            digest,
        })
    }
}

/// A private row whose public commitment opening and all peer
/// cross-evaluations have passed.  Construction is private to this module, so
/// [`QuorumParty::assemble_verified`] cannot accidentally accept a raw dealing.
pub struct VerifiedPrivateDealerShare {
    inner: PrivateDealerShare,
    dealer_commitment_digest: [u8; 32],
}

impl VerifiedPrivateDealerShare {
    pub fn dealer(&self) -> usize {
        self.inner.dealer
    }

    pub fn recipient(&self) -> usize {
        self.inner.recipient
    }
}

/// One dealer dealing after exact commitment openings and bivariate
/// consistency checks have passed for every recipient row.
pub struct VerifiedDealerBundle {
    public: PublicKeyContribution,
    commitment: DealerVssCommitment,
    private: Vec<VerifiedPrivateDealerShare>,
}

/// Public all-dealer setup transcript.  Its digest is threaded into the
/// opening session and authenticated custody roster.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedDkgTranscript {
    session: QuorumKeygenSession,
    dealer_commitment_digests: Vec<[u8; 32]>,
    /// One coefficient-wise Pedersen commitment vector per custody party, in
    /// RNS-row-major order.  These commitments are constructed from the exact
    /// aggregate rows admitted by the bivariate VSS checker and are therefore
    /// the public key-share anchor used by decrypt-share proofs.
    party_secret_commitments: Vec<Vec<[u8; 32]>>,
    /// Experimental BabyBear-native commitments contributed by the custody
    /// parties after local assembly.  When present they are ordered by party
    /// and included in `digest`.  Each party retains its own opening.
    q0_share_commitments: Option<Vec<PqShareCommitment>>,
    /// Pre-anchor transcript digest used to domain-separate the q0 commitment
    /// keys without introducing a circular digest dependency.
    q0_share_commitment_context: Option<[u8; 32]>,
    /// Domain-separated digest of the exact serialized collective BFV public
    /// key produced by this verified DKG transition.  Downstream transforms
    /// consume this transcript-owned value rather than accepting a caller's
    /// assertion about which encryption key the setup produced.
    collective_key_digest: [u8; 32],
    digest: [u8; 32],
}

impl VerifiedDkgTranscript {
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub fn party_secret_commitments(&self, party: usize) -> Option<&[[u8; 32]]> {
        self.party_secret_commitments.get(party).map(Vec::as_slice)
    }

    pub fn collective_key_digest(&self) -> [u8; 32] {
        self.collective_key_digest
    }

    pub fn q0_share_commitment(&self, party: usize) -> Option<&PqShareCommitment> {
        self.q0_share_commitments.as_ref()?.get(party)
    }

    pub fn q0_share_commitment_context(&self) -> Option<[u8; 32]> {
        self.q0_share_commitment_context
    }

    /// Executable fail-closed tooth for the missing public ceremony.  Local
    /// opening/inclusion checks cannot establish that a malicious custodian's
    /// q0 row equals its VSS/Ristretto row, nor that all observers received
    /// one consistent contribution set.
    pub const fn require_experimental_q0_public_ceremony_authority(&self) -> Result<()> {
        Err(QuorumError::ExperimentalQ0CeremonyUnauthenticated)
    }

    /// Bind one ordered q0 contribution from every custody party into a new
    /// transcript.  Contributions are public but not yet identity-signed;
    /// deployments must authenticate this exchange before treating it as a
    /// ceremony.  The returned transcript remains an experimental HidingFRI
    /// bridge rung and never satisfies production-PQ policy.
    pub fn finalize_experimental_q0_share_commitments(
        mut self,
        contributions: &[ExperimentalQ0ShareCommitmentContribution],
        params: &BfvParams,
    ) -> Result<Self> {
        if params.degree() != BFV_Q0_DEGREE
            || params.moduli().first().copied() != Some(BFV_Q0_MODULUS)
            || self.q0_share_commitments.is_some()
            || self.q0_share_commitment_context.is_some()
            || contributions.len() != self.session.n_parties()
            || self.digest
                != vss_setup_transcript_digest(
                    &self.session,
                    &self.dealer_commitment_digests,
                    &self.party_secret_commitments,
                    self.collective_key_digest,
                    params,
                    None,
                )
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        let context = self.digest;
        let seed = q0_share_commitment_seed(context);
        let mut commitments = Vec::with_capacity(contributions.len());
        for (party, contribution) in contributions.iter().enumerate() {
            let expected_key = ExperimentalBfvQ0ShareCommitmentKey::derive(
                context,
                self.collective_key_digest,
                party,
                seed,
            )
            .map_err(|_| QuorumError::VssTranscriptMismatch)?;
            if contribution.party != party
                || contribution.context != context
                || contribution.collective_key_digest != self.collective_key_digest
                || contribution.commitment.key_id() != expected_key.key_id()
            {
                return Err(QuorumError::VssTranscriptMismatch);
            }
            commitments.push(contribution.commitment.clone());
        }
        self.digest = vss_setup_transcript_digest(
            &self.session,
            &self.dealer_commitment_digests,
            &self.party_secret_commitments,
            self.collective_key_digest,
            params,
            Some(&commitments),
        );
        self.q0_share_commitment_context = Some(context);
        self.q0_share_commitments = Some(commitments);
        Ok(self)
    }
}

/// Party-local public contribution to the experimental q0 dual-anchor round.
/// The secret opening never enters this object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExperimentalQ0ShareCommitmentContribution {
    party: usize,
    context: [u8; 32],
    collective_key_digest: [u8; 32],
    commitment: PqShareCommitment,
}

impl ExperimentalQ0ShareCommitmentContribution {
    pub const fn party(&self) -> usize {
        self.party
    }

    pub const fn context(&self) -> [u8; 32] {
        self.context
    }

    pub fn commitment(&self) -> &PqShareCommitment {
        &self.commitment
    }
}

/// Recipient-local verified setup material.  The Pedersen blindings are the
/// private opening of the public commitment vector in [`VerifiedDkgTranscript`]
/// and never appear in the public transcript or a decrypt-share certificate.
pub struct VerifiedPartyAssembly {
    shares: Vec<VerifiedPrivateDealerShare>,
    secret_commitment_blindings: Vec<[u8; 32]>,
}

/// Outputs of the verified all-dealer setup before party-local assembly.
pub struct VerifiedQuorumSetup {
    collective: CollectivePublicKey,
    transcript: VerifiedDkgTranscript,
    assemblies: Vec<VerifiedPartyAssembly>,
}

impl VerifiedQuorumSetup {
    pub fn into_parts(
        self,
    ) -> (
        CollectivePublicKey,
        VerifiedDkgTranscript,
        Vec<VerifiedPartyAssembly>,
    ) {
        (self.collective, self.transcript, self.assemblies)
    }
}

/// Sample one dealer contribution.
///
/// The public half can go to [`super::KeygenCoordinator`].  Each private half
/// must go only to its named recipient.
pub fn deal(
    session: &QuorumKeygenSession,
    dealer: usize,
    params: &BfvParams,
) -> Result<DealerBundle> {
    let n = session.n_parties();
    if dealer >= n {
        return Err(QuorumError::InvalidParty {
            party: dealer,
            n_parties: n,
        });
    }

    let mut rng = rand_09::rng();
    let secret = (0..params.degree())
        .map(|_| rng.random_range(-1i64..=1))
        .collect::<Vec<_>>();
    let sk = sk_from_coeffs(&secret, params.arc());
    let public_share = PublicKeyShare::new(&sk, session.base.common_random_poly(params), &mut rng)
        .map_err(|_| QuorumError::InvalidParameters)?;
    let public_key =
        PublicKey::from_shares([public_share]).map_err(|_| QuorumError::InvalidParameters)?;
    let public = PublicKeyContribution {
        session: session.base.clone(),
        party: dealer,
        public_key_bytes: public_key.to_bytes(),
    };
    let public_key_ct = public_key_as_lean(&public, params)?;
    let crp_rows = &public_key_ct.polys[1].rows;
    let secret_rows = params
        .moduli()
        .iter()
        .map(|&q| {
            secret
                .iter()
                .map(|&value| value.rem_euclid(q as i64) as u64)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let crp_times_secret = multiply_rns(crp_rows, &secret_rows, params)?;
    // fhe.rs EncKeyGen emits p0 = -a*s + e. Recover the dealer-known CBD error
    // exactly so it can be shared without changing the library's key bytes.
    let error_rows = add_rns(&public_key_ct.polys[0].rows, &crp_times_secret, params)?;

    let t = session.threshold();
    let mut secret_bivariate = (0..t)
        .map(|_| (0..t).map(|_| zero_rns_rows(params)).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let mut error_bivariate = (0..t)
        .map(|_| (0..t).map(|_| zero_rns_rows(params)).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    // Every RNS coefficient gets two independent random SYMMETRIC bivariate
    // polynomials S(x,y), E(x,y), degree t-1 in each variable, with constants
    // secret and the actual fhe.rs keygen error. Recipient i receives both rows;
    // only S(i+1,0) becomes its persistent BFV custody share.
    for (row_index, &q) in params.moduli().iter().enumerate() {
        for (coefficient_index, &constant) in secret.iter().enumerate() {
            secret_bivariate[0][0][row_index][coefficient_index] =
                constant.rem_euclid(q as i64) as u64;
            error_bivariate[0][0][row_index][coefficient_index] =
                error_rows[row_index][coefficient_index];
            for x_degree in 0..t {
                for y_degree in x_degree..t {
                    if x_degree == 0 && y_degree == 0 {
                        continue;
                    }
                    let secret_value = rng.random_range(0..q);
                    secret_bivariate[x_degree][y_degree][row_index][coefficient_index] =
                        secret_value;
                    secret_bivariate[y_degree][x_degree][row_index][coefficient_index] =
                        secret_value;
                    let error_value = rng.random_range(0..q);
                    error_bivariate[x_degree][y_degree][row_index][coefficient_index] = error_value;
                    error_bivariate[y_degree][x_degree][row_index][coefficient_index] = error_value;
                }
            }
        }
    }

    // Public BFV-linear images of every bivariate coefficient. C_00 must be
    // byte-for-byte the p0 ring polynomial already carried by fhe.rs.
    let mut linear_commitments = Vec::with_capacity(t * t);
    for x_degree in 0..t {
        for y_degree in 0..t {
            let product = multiply_rns(crp_rows, &secret_bivariate[x_degree][y_degree], params)?;
            linear_commitments.push(sub_rns(
                &error_bivariate[x_degree][y_degree],
                &product,
                params,
            )?);
        }
    }
    if linear_commitments[0] != public_key_ct.polys[0].rows {
        return Err(QuorumError::VssTranscriptMismatch);
    }

    let mut secret_row_polynomials = (0..n)
        .map(|_| (0..t).map(|_| zero_rns_rows(params)).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let mut error_row_polynomials = (0..n)
        .map(|_| (0..t).map(|_| zero_rns_rows(params)).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    for recipient in 0..n {
        let x = recipient as u64 + 1;
        for y_degree in 0..t {
            for (row_index, &q) in params.moduli().iter().enumerate() {
                for coefficient_index in 0..params.degree() {
                    let secret_coefficients = (0..t)
                        .map(|x_degree| {
                            secret_bivariate[x_degree][y_degree][row_index][coefficient_index]
                        })
                        .collect::<Vec<_>>();
                    secret_row_polynomials[recipient][y_degree][row_index][coefficient_index] =
                        evaluate_polynomial(&secret_coefficients, x, q);
                    let error_coefficients = (0..t)
                        .map(|x_degree| {
                            error_bivariate[x_degree][y_degree][row_index][coefficient_index]
                        })
                        .collect::<Vec<_>>();
                    error_row_polynomials[recipient][y_degree][row_index][coefficient_index] =
                        evaluate_polynomial(&error_coefficients, x, q);
                }
            }
        }
    }

    let public_key_digest: [u8; 32] = Sha256::digest(public.public_key_bytes()).into();
    let mut row_commitments = Vec::with_capacity(n);
    let private = secret_row_polynomials
        .into_iter()
        .zip(error_row_polynomials)
        .enumerate()
        .map(
            |(recipient, (vss_row_coefficients, vss_error_row_coefficients))| {
                let mut vss_salt = [0u8; 32];
                rng.fill(&mut vss_salt);
                row_commitments.push(vss_row_commitment_digest(
                    session,
                    dealer,
                    recipient,
                    &public_key_digest,
                    &vss_salt,
                    &vss_row_coefficients,
                    &vss_error_row_coefficients,
                    params,
                ));
                PrivateDealerShare {
                    session: session.clone(),
                    dealer,
                    recipient,
                    rows: vss_row_coefficients[0].clone(),
                    vss_row_coefficients,
                    vss_error_row_coefficients,
                    vss_salt,
                }
            },
        )
        .collect();
    let digest = dealer_vss_commitment_digest(
        session,
        dealer,
        &public_key_digest,
        &row_commitments,
        &linear_commitments,
    );
    let vss_commitment = DealerVssCommitment {
        session: session.clone(),
        dealer,
        public_key_digest,
        row_commitments,
        linear_commitments,
        digest,
    };
    Ok(DealerBundle {
        public,
        private,
        vss_commitment,
    })
}

fn verify_dealer_bundle(bundle: DealerBundle, params: &BfvParams) -> Result<VerifiedDealerBundle> {
    let DealerBundle {
        public,
        private,
        vss_commitment,
    } = bundle;
    let session = &vss_commitment.session;
    let dealer = vss_commitment.dealer;
    if public.session != session.base
        || public.party != dealer
        || dealer >= session.n_parties()
        || private.len() != session.n_parties()
        || vss_commitment.row_commitments.len() != session.n_parties()
        || vss_commitment.linear_commitments.len() != session.threshold() * session.threshold()
        || vss_commitment
            .linear_commitments
            .iter()
            .any(|commitment| !valid_rows(commitment, params))
    {
        return Err(QuorumError::VssTranscriptMismatch);
    }
    let public_key_ct = public_key_as_lean(&public, params)?;
    if vss_commitment.linear_commitments[0] != public_key_ct.polys[0].rows {
        return Err(QuorumError::VssTranscriptMismatch);
    }
    let public_key_digest: [u8; 32] = Sha256::digest(public.public_key_bytes()).into();
    if public_key_digest != vss_commitment.public_key_digest
        || dealer_vss_commitment_digest(
            session,
            dealer,
            &public_key_digest,
            &vss_commitment.row_commitments,
            &vss_commitment.linear_commitments,
        ) != vss_commitment.digest
    {
        return Err(QuorumError::VssTranscriptMismatch);
    }

    for (recipient, share) in private.iter().enumerate() {
        if share.session != *session || share.dealer != dealer || share.recipient != recipient {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        if !valid_rows(&share.rows, params)
            || share.vss_row_coefficients.len() != session.threshold()
            || share.vss_error_row_coefficients.len() != session.threshold()
            || share
                .vss_row_coefficients
                .iter()
                .any(|coefficient| !valid_rows(coefficient, params))
            || share
                .vss_error_row_coefficients
                .iter()
                .any(|coefficient| !valid_rows(coefficient, params))
            || share.vss_row_coefficients[0] != share.rows
        {
            return Err(QuorumError::ParamMismatch);
        }
        let opened = vss_row_commitment_digest(
            session,
            dealer,
            recipient,
            &public_key_digest,
            &share.vss_salt,
            &share.vss_row_coefficients,
            &share.vss_error_row_coefficients,
            params,
        );
        if opened != vss_commitment.row_commitments[recipient] {
            return Err(QuorumError::VssCommitmentMismatch { dealer, recipient });
        }
    }

    // Genuine VSS check: every pair independently opens one row of the
    // bivariate polynomial, then checks its intersection against the peer row.
    // n >= t+1 in this API, so degree-(t-1) row equality on the n public points
    // pins one common bivariate polynomial rather than merely a list of shares.
    for left in 0..private.len() {
        for right in (left + 1)..private.len() {
            if !vss_cross_evaluations_match(
                &private[left].vss_row_coefficients,
                private[left].recipient,
                &private[right].vss_row_coefficients,
                private[right].recipient,
                params,
            ) || !vss_cross_evaluations_match(
                &private[left].vss_error_row_coefficients,
                private[left].recipient,
                &private[right].vss_error_row_coefficients,
                private[right].recipient,
                params,
            ) {
                return Err(QuorumError::VssInconsistentRows {
                    dealer,
                    left,
                    right,
                });
            }
        }
    }

    // Each recipient checks its exact committed (secret,error) row through the
    // public BFV map. Polynomial identity at n > t-1 x-points forces the hidden
    // constants to satisfy C_00 = p0 = -a*s + e.
    for share in &private {
        if !vss_row_matches_linear_commitments(
            share,
            &public_key_ct.polys[1].rows,
            &vss_commitment.linear_commitments,
            params,
        )? {
            return Err(QuorumError::VssPublicImageMismatch {
                dealer,
                recipient: share.recipient,
            });
        }
    }

    let commitment_digest = vss_commitment.digest;
    Ok(VerifiedDealerBundle {
        public,
        commitment: vss_commitment,
        private: private
            .into_iter()
            .map(|inner| VerifiedPrivateDealerShare {
                inner,
                dealer_commitment_digest: commitment_digest,
            })
            .collect(),
    })
}

/// Finish a DKG only from dealer bundles whose public row openings and
/// bivariate consistency checks already passed.
pub fn finish_verified_keygen(
    session: &QuorumKeygenSession,
    bundles: Vec<VerifiedDealerBundle>,
    params: &BfvParams,
) -> Result<VerifiedQuorumSetup> {
    if bundles.len() != session.n_parties() {
        return Err(QuorumError::MissingDealerShares {
            have: bundles.len(),
            need: session.n_parties(),
        });
    }
    for (dealer, bundle) in bundles.iter().enumerate() {
        if bundle.public.session != session.base
            || bundle.public.party != dealer
            || bundle.commitment.session != *session
            || bundle.commitment.dealer != dealer
            || bundle.private.len() != session.n_parties()
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
    }

    let collective = finish_public_key(
        session,
        &bundles
            .iter()
            .map(|bundle| bundle.public.clone())
            .collect::<Vec<_>>(),
        params,
    )?;
    let dealer_commitment_digests = bundles
        .iter()
        .map(|bundle| bundle.commitment.digest)
        .collect::<Vec<_>>();
    let mut inboxes: Vec<Vec<VerifiedPrivateDealerShare>> = (0..session.n_parties())
        .map(|_| Vec::with_capacity(session.n_parties()))
        .collect();
    for bundle in bundles {
        for share in bundle.private {
            let recipient = share.recipient();
            inboxes[recipient].push(share);
        }
    }

    // Commit the exact aggregate share each party will assemble.  This happens
    // inside the same verified typestate transition that checked every dealer
    // row, so a later decrypt-share proof is anchored to VSS-admitted material,
    // not to a key commitment invented by the decrypting signer.
    let pc_gens = PedersenGens::default();
    let mut rng = OsRng;
    let mut party_secret_commitments = Vec::with_capacity(session.n_parties());
    let mut assemblies = Vec::with_capacity(session.n_parties());
    for inbox in inboxes {
        let mut rows = zero_rns_rows(params);
        for share in &inbox {
            for (acc_row, (share_row, &q)) in rows
                .iter_mut()
                .zip(share.inner.rows.iter().zip(params.moduli()))
            {
                for (acc, &value) in acc_row.iter_mut().zip(share_row) {
                    *acc = add_mod(*acc, value, q);
                }
            }
        }
        let mut commitments = Vec::with_capacity(params.moduli().len() * params.degree());
        let mut blindings = Vec::with_capacity(commitments.capacity());
        for &value in rows.iter().flatten() {
            let blinding = Scalar::random(&mut rng);
            commitments.push(
                pc_gens
                    .commit(Scalar::from(value), blinding)
                    .compress()
                    .to_bytes(),
            );
            blindings.push(blinding.to_bytes());
        }
        party_secret_commitments.push(commitments);
        assemblies.push(VerifiedPartyAssembly {
            shares: inbox,
            secret_commitment_blindings: blindings,
        });
    }
    let collective_key_digest = verified_dkg_collective_key_digest(&collective);
    let digest = vss_setup_transcript_digest(
        session,
        &dealer_commitment_digests,
        &party_secret_commitments,
        collective_key_digest,
        params,
        None,
    );
    let transcript = VerifiedDkgTranscript {
        session: session.clone(),
        dealer_commitment_digests,
        party_secret_commitments,
        q0_share_commitments: None,
        q0_share_commitment_context: None,
        collective_key_digest,
        digest,
    };
    Ok(VerifiedQuorumSetup {
        collective,
        transcript,
        assemblies,
    })
}

/// Aggregate the public dealer contributions into the real collective key.
/// This helper delegates to the same exact fhe.rs-anchored aggregator as n-of-n.
pub fn finish_public_key(
    session: &QuorumKeygenSession,
    contributions: &[PublicKeyContribution],
    params: &BfvParams,
) -> Result<CollectivePublicKey> {
    aggregate_public_contributions(&session.base, contributions, params)
        .map_err(|_| QuorumError::ParamMismatch)
}

/// Party-local Shamir evaluation and one-shot opening state.
///
/// No secret accessor, `Clone`, or `Debug` is provided.
pub struct QuorumParty {
    session: QuorumKeygenSession,
    party: usize,
    rows: Vec<Vec<u64>>,
    vss_setup_digest: Option<[u8; 32]>,
    secret_commitments: Option<Vec<[u8; 32]>>,
    secret_commitment_blindings: Option<Vec<[u8; 32]>>,
    q0_share_opening: Option<ExperimentalBfvQ0ShareOpening>,
    q0_share_commitment: Option<PqShareCommitment>,
    opened_sessions: BTreeSet<[u8; 32]>,
    opened_targets: BTreeSet<[u8; 32]>,
}

impl QuorumParty {
    /// Assemble one recipient's evaluation only after every setup dealer has
    /// contributed exactly once.  Setup is not crash-tolerant; openings are.
    pub fn assemble(
        session: &QuorumKeygenSession,
        party: usize,
        shares: Vec<PrivateDealerShare>,
        params: &BfvParams,
    ) -> Result<Self> {
        if party >= session.n_parties() {
            return Err(QuorumError::InvalidParty {
                party,
                n_parties: session.n_parties(),
            });
        }
        if shares.len() < session.n_parties() {
            return Err(QuorumError::MissingDealerShares {
                have: shares.len(),
                need: session.n_parties(),
            });
        }
        if shares.len() > session.n_parties() {
            return Err(QuorumError::ParamMismatch);
        }

        let mut seen = BTreeSet::new();
        let mut rows = params
            .moduli()
            .iter()
            .map(|_| vec![0u64; params.degree()])
            .collect::<Vec<_>>();
        for share in shares {
            if share.session != *session {
                return Err(QuorumError::SessionMismatch);
            }
            if share.recipient != party {
                return Err(QuorumError::RecipientMismatch {
                    expected: party,
                    actual: share.recipient,
                });
            }
            if share.dealer >= session.n_parties() {
                return Err(QuorumError::InvalidParty {
                    party: share.dealer,
                    n_parties: session.n_parties(),
                });
            }
            if !seen.insert(share.dealer) {
                return Err(QuorumError::DuplicateDealer {
                    dealer: share.dealer,
                });
            }
            if !valid_rows(&share.rows, params) {
                return Err(QuorumError::ParamMismatch);
            }
            for (acc_row, (share_row, &q)) in
                rows.iter_mut().zip(share.rows.iter().zip(params.moduli()))
            {
                for (acc, &value) in acc_row.iter_mut().zip(share_row) {
                    *acc = add_mod(*acc, value, q);
                }
            }
        }
        if seen.len() != session.n_parties() {
            return Err(QuorumError::MissingDealerShares {
                have: seen.len(),
                need: session.n_parties(),
            });
        }

        Ok(Self {
            session: session.clone(),
            party,
            rows,
            vss_setup_digest: None,
            secret_commitments: None,
            secret_commitment_blindings: None,
            q0_share_opening: None,
            q0_share_commitment: None,
            opened_sessions: BTreeSet::new(),
            opened_targets: BTreeSet::new(),
        })
    }

    /// Assemble party-local custody state only from rows admitted by the
    /// all-dealer bivariate-VSS transcript.
    pub fn assemble_verified(
        session: &QuorumKeygenSession,
        party: usize,
        assembly: VerifiedPartyAssembly,
        transcript: &VerifiedDkgTranscript,
        params: &BfvParams,
    ) -> Result<Self> {
        if transcript.session != *session
            || transcript.dealer_commitment_digests.len() != session.n_parties()
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        for share in &assembly.shares {
            let dealer = share.dealer();
            if share.inner.session != *session
                || share.recipient() != party
                || transcript.dealer_commitment_digests.get(dealer)
                    != Some(&share.dealer_commitment_digest)
            {
                return Err(QuorumError::VssTranscriptMismatch);
            }
        }
        let commitments = transcript
            .party_secret_commitments(party)
            .ok_or(QuorumError::VssTranscriptMismatch)?;
        let expected_len = params.moduli().len() * params.degree();
        if commitments.len() != expected_len
            || assembly.secret_commitment_blindings.len() != expected_len
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        let raw = assembly
            .shares
            .into_iter()
            .map(|share| share.inner)
            .collect();
        let mut assembled = Self::assemble(session, party, raw, params)?;
        let pc_gens = PedersenGens::default();
        for ((&value, commitment), blinding_bytes) in assembled
            .rows
            .iter()
            .flatten()
            .zip(commitments)
            .zip(&assembly.secret_commitment_blindings)
        {
            let blinding = Option::<Scalar>::from(Scalar::from_canonical_bytes(*blinding_bytes))
                .ok_or(QuorumError::VssTranscriptMismatch)?;
            if pc_gens
                .commit(Scalar::from(value), blinding)
                .compress()
                .to_bytes()
                != *commitment
            {
                return Err(QuorumError::VssTranscriptMismatch);
            }
        }
        // Assembly consumes the public pre-anchor transcript.  The optional
        // q0 round is performed afterward by each party locally; accepting a
        // coordinator-populated opening here would recreate a trusted viewer.
        if transcript.q0_share_commitments.is_some()
            || transcript.q0_share_commitment_context.is_some()
            || transcript.digest
                != vss_setup_transcript_digest(
                    session,
                    &transcript.dealer_commitment_digests,
                    &transcript.party_secret_commitments,
                    transcript.collective_key_digest,
                    params,
                    None,
                )
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        assembled.vss_setup_digest = Some(transcript.digest);
        assembled.secret_commitments = Some(commitments.to_vec());
        assembled.secret_commitment_blindings = Some(assembly.secret_commitment_blindings);
        Ok(assembled)
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn vss_setup_digest(&self) -> Option<[u8; 32]> {
        self.vss_setup_digest
    }

    /// Locally create this custody party's experimental q0 commitment
    /// contribution.  The opening and its randomizer remain in `self`; only
    /// the public commitment leaves the party boundary.  This localizes the
    /// *new* q0 blinding, but does not repair the older setup architecture:
    /// `finish_verified_keygen` still receives every private dealer bundle and
    /// can reconstruct all aggregate party rows.
    pub fn prepare_experimental_q0_share_commitment<R: CryptoRng + RngCore>(
        &mut self,
        pre_anchor: &VerifiedDkgTranscript,
        params: &BfvParams,
        rng: &mut R,
    ) -> Result<ExperimentalQ0ShareCommitmentContribution> {
        if params.degree() != BFV_Q0_DEGREE
            || params.moduli().first().copied() != Some(BFV_Q0_MODULUS)
            || pre_anchor.q0_share_commitments.is_some()
            || pre_anchor.q0_share_commitment_context.is_some()
            || self.vss_setup_digest != Some(pre_anchor.digest)
            || self.q0_share_opening.is_some()
            || self.q0_share_commitment.is_some()
            || pre_anchor.digest
                != vss_setup_transcript_digest(
                    &pre_anchor.session,
                    &pre_anchor.dealer_commitment_digests,
                    &pre_anchor.party_secret_commitments,
                    pre_anchor.collective_key_digest,
                    params,
                    None,
                )
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        let context = pre_anchor.digest;
        let key = ExperimentalBfvQ0ShareCommitmentKey::derive(
            context,
            pre_anchor.collective_key_digest,
            self.party,
            q0_share_commitment_seed(context),
        )
        .map_err(|_| QuorumError::VssTranscriptMismatch)?;
        let opening = ExperimentalBfvQ0ShareOpening::randomized(&self.rows[0], rng)
            .map_err(|_| QuorumError::VssTranscriptMismatch)?;
        let commitment = key
            .commit(&opening)
            .map_err(|_| QuorumError::VssTranscriptMismatch)?;
        if !opening
            .matches_residues(&self.rows[0])
            .map_err(|_| QuorumError::VssTranscriptMismatch)?
            || !key
                .verify_opening(&commitment, &opening)
                .map_err(|_| QuorumError::VssTranscriptMismatch)?
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        self.q0_share_opening = Some(opening);
        self.q0_share_commitment = Some(commitment.clone());
        Ok(ExperimentalQ0ShareCommitmentContribution {
            party: self.party,
            context,
            collective_key_digest: pre_anchor.collective_key_digest,
            commitment,
        })
    }

    /// Verify inclusion of this party's locally retained q0 opening in the
    /// finalized ordered transcript and adopt its digest for later openings.
    /// This is a local same-row typestate bridge, not a public ZK
    /// cross-commitment proof.
    pub fn bind_experimental_q0_share_commitment(
        &mut self,
        transcript: &VerifiedDkgTranscript,
        params: &BfvParams,
    ) -> Result<()> {
        let context = transcript
            .q0_share_commitment_context
            .ok_or(QuorumError::VssTranscriptMismatch)?;
        let opening = self
            .q0_share_opening
            .as_ref()
            .ok_or(QuorumError::VssTranscriptMismatch)?;
        let local_commitment = self
            .q0_share_commitment
            .as_ref()
            .ok_or(QuorumError::VssTranscriptMismatch)?;
        let commitments = transcript
            .q0_share_commitments
            .as_deref()
            .ok_or(QuorumError::VssTranscriptMismatch)?;
        if params.degree() != BFV_Q0_DEGREE
            || params.moduli().first().copied() != Some(BFV_Q0_MODULUS)
            || self.vss_setup_digest != Some(context)
            || !self.opened_sessions.is_empty()
            || !self.opened_targets.is_empty()
            || commitments.len() != transcript.session.n_parties()
            || transcript.q0_share_commitment(self.party) != Some(local_commitment)
            || transcript.digest
                != vss_setup_transcript_digest(
                    &transcript.session,
                    &transcript.dealer_commitment_digests,
                    &transcript.party_secret_commitments,
                    transcript.collective_key_digest,
                    params,
                    Some(commitments),
                )
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        let key = ExperimentalBfvQ0ShareCommitmentKey::derive(
            context,
            transcript.collective_key_digest,
            self.party,
            q0_share_commitment_seed(context),
        )
        .map_err(|_| QuorumError::VssTranscriptMismatch)?;
        if !opening
            .matches_residues(&self.rows[0])
            .map_err(|_| QuorumError::VssTranscriptMismatch)?
            || !key
                .verify_opening(local_commitment, opening)
                .map_err(|_| QuorumError::VssTranscriptMismatch)?
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        self.vss_setup_digest = Some(transcript.digest);
        Ok(())
    }

    /// Produce one Lagrange-weighted, smudged share for this exact opening.
    /// Repeating the same ciphertext is refused in this party state even under
    /// a different nonce, preventing cheap smudge-averaging replays.
    pub fn partial_decrypt(
        &mut self,
        opening: &QuorumOpeningSession,
        ct: &LeanCiphertext,
        smudge_bits: u32,
        params: &BfvParams,
    ) -> Result<QuorumDecryptShare> {
        if opening.keygen != self.session {
            return Err(QuorumError::SessionMismatch);
        }
        if opening.vss_setup_digest != self.vss_setup_digest {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        if !opening.parties.contains(&self.party) {
            return Err(QuorumError::PartyNotSelected { party: self.party });
        }
        validate_ciphertext(ct, params)?;
        if smudge_bits < MIN_SMUDGE_BITS {
            return Err(QuorumError::SmudgeTooSmall);
        }
        let width = ceil_log2(opening.parties.len()).ok_or(QuorumError::InvalidParameters)?;
        if smudge_bits
            .checked_add(width)
            .map_or(true, |total| total > MAX_SMUDGE_BITS_TOTAL)
        {
            return Err(QuorumError::SmudgeTooLarge);
        }
        let session = opening_digest(opening);
        let target = target_digest(ct);
        if self.opened_sessions.contains(&session) || self.opened_targets.contains(&target) {
            return Err(QuorumError::Replay);
        }

        let mut h = multiply_rns(&self.rows, &ct.polys[1].rows, params)?;
        for (row, &q) in h.iter_mut().zip(params.moduli()) {
            let lambda = lagrange_at_zero(self.party, &opening.parties, q)?;
            for coefficient in row {
                *coefficient = mul_mod(*coefficient, lambda, q);
            }
        }

        let mut rng = rand_09::rng();
        let half = 1u128 << smudge_bits;
        let smudge = (0..params.degree())
            .map(|_| rng.random_range(0..=(half << 1)) as i128 - half as i128)
            .collect::<Vec<_>>();
        for (row, &q) in h.iter_mut().zip(params.moduli()) {
            for (coefficient, &noise) in row.iter_mut().zip(&smudge) {
                *coefficient = add_mod(*coefficient, noise.rem_euclid(q as i128) as u64, q);
            }
        }

        let mut share = QuorumDecryptShare {
            opening: opening.clone(),
            ct: ct.clone(),
            party: self.party,
            smudge_bits,
            h,
            proof: None,
        };
        if self.vss_setup_digest.is_some() {
            let commitments = self
                .secret_commitments
                .as_deref()
                .ok_or(QuorumError::VssTranscriptMismatch)?;
            let blindings = self
                .secret_commitment_blindings
                .as_deref()
                .ok_or(QuorumError::VssTranscriptMismatch)?;
            share.proof = Some(prove_decrypt_share_relation(
                &share,
                &self.rows,
                commitments,
                blindings,
                &smudge,
                params,
            )?);
        }

        self.opened_sessions.insert(session);
        self.opened_targets.insert(target);
        Ok(share)
    }
}

/// Produce the selected custody roster's decryption shares concurrently.
///
/// A degree-4096 verified share currently carries three large aggregated range
/// arguments, so independent custodians must not be serialized by a process
/// coordinator. This helper preserves the ordinary [`QuorumParty::partial_decrypt`]
/// state machine and returns shares in the opening's canonical roster order;
/// it only supplies process-local scheduling. It does not batch or compress
/// the proofs, authenticate a transport, or turn one process into a security
/// boundary.
///
/// `parties` may contain offline/non-selected party states, but it must contain
/// exactly one state for every selected identity. Deterministic roster errors
/// are checked before any worker mutates its replay state.
pub fn partial_decrypt_quorum_parallel(
    parties: &mut [QuorumParty],
    opening: &QuorumOpeningSession,
    ct: &LeanCiphertext,
    smudge_bits: u32,
    params: &BfvParams,
) -> Result<Vec<QuorumDecryptShare>> {
    let mut seen = HashSet::with_capacity(opening.parties.len());
    for party in parties.iter() {
        if opening.parties.contains(&party.party) && !seen.insert(party.party) {
            return Err(QuorumError::DuplicateParty { party: party.party });
        }
    }
    for &party in &opening.parties {
        if !seen.contains(&party) {
            return Err(QuorumError::MissingCustodyParty { party });
        }
    }

    let joined = std::thread::scope(|scope| {
        let mut workers = Vec::with_capacity(opening.parties.len());
        for state in parties.iter_mut() {
            if opening.parties.contains(&state.party) {
                let party = state.party;
                workers.push((
                    party,
                    scope.spawn(move || state.partial_decrypt(opening, ct, smudge_bits, params)),
                ));
            }
        }
        workers
            .into_iter()
            .map(|(party, worker)| {
                worker
                    .join()
                    .map_err(|_| QuorumError::CustodyWorkerPanicked { party })?
            })
            .collect::<Result<Vec<_>>>()
    })?;

    let mut by_party = joined
        .into_iter()
        .map(|share| (share.party, share))
        .collect::<std::collections::BTreeMap<_, _>>();
    opening
        .parties
        .iter()
        .map(|party| {
            by_party
                .remove(party)
                .ok_or(QuorumError::MissingCustodyParty { party: *party })
        })
        .collect()
}

/// Exact live roster and nonce for one `t`-party opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumOpeningSession {
    keygen: QuorumKeygenSession,
    nonce: [u8; 32],
    parties: Vec<usize>,
    vss_setup_digest: Option<[u8; 32]>,
}

impl QuorumOpeningSession {
    /// The roster must contain exactly `t` distinct parties in increasing
    /// order.  Thus a coordinator may choose any live threshold subset, but it
    /// cannot silently reinterpret shares under a different interpolation set.
    pub fn new(keygen: QuorumKeygenSession, nonce: [u8; 32], parties: Vec<usize>) -> Result<Self> {
        Self::new_inner(keygen, None, nonce, parties)
    }

    /// Construct an opening bound to the exact accepted bivariate-VSS setup.
    pub fn new_verified(
        keygen: QuorumKeygenSession,
        transcript: &VerifiedDkgTranscript,
        nonce: [u8; 32],
        parties: Vec<usize>,
    ) -> Result<Self> {
        if transcript.session != keygen {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        Self::new_inner(keygen, Some(transcript.digest), nonce, parties)
    }

    fn new_inner(
        keygen: QuorumKeygenSession,
        vss_setup_digest: Option<[u8; 32]>,
        nonce: [u8; 32],
        parties: Vec<usize>,
    ) -> Result<Self> {
        if parties.len() < keygen.threshold {
            return Err(QuorumError::QuorumTooSmall {
                have: parties.len(),
                need: keygen.threshold,
            });
        }
        if parties.len() != keygen.threshold || parties.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(QuorumError::NonCanonicalRoster);
        }
        if let Some(&party) = parties.iter().find(|&&party| party >= keygen.n_parties()) {
            return Err(QuorumError::InvalidParty {
                party,
                n_parties: keygen.n_parties(),
            });
        }
        Ok(Self {
            keygen,
            nonce,
            parties,
            vss_setup_digest,
        })
    }

    pub fn parties(&self) -> &[usize] {
        &self.parties
    }

    pub fn nonce(&self) -> [u8; 32] {
        self.nonce
    }

    pub fn vss_setup_digest(&self) -> Option<[u8; 32]> {
        self.vss_setup_digest
    }
}

/// Zero-knowledge certificate that one public decryption share is derived from
/// the VSS-authenticated party secret and an in-range smudge.
///
/// The two aggregated Bulletproofs range-check hidden 128-bit decompositions:
/// `smudge + 2^b`, its exact complement `2^(b+1) - (smudge + 2^b)`, and the
/// signed modular quotients.  A batched Schnorr representation proof then ties
/// those commitments and the setup's secret-share commitments to every RNS
/// equation `h = lambda*c1*s + smudge (mod q)`.  The Fiat-Shamir transcript
/// binds the exact DKG, opening, ciphertext, party, declared bound, and `h`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumDecryptShareProof {
    smudge_commitments: Vec<[u8; 32]>,
    smudge_low_range_proof: Vec<u8>,
    smudge_high_range_proof: Vec<u8>,
    product_commitments: Vec<[u8; 32]>,
    quotient_commitments: Vec<[u8; 32]>,
    quotient_range_proof: Vec<u8>,
    relation_nonce: [u8; 32],
    relation_response: [u8; 32],
}

impl QuorumDecryptShareProof {
    fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            64 + (self.smudge_commitments.len()
                + self.product_commitments.len()
                + self.quotient_commitments.len())
                * 32
                + self.smudge_low_range_proof.len()
                + self.smudge_high_range_proof.len()
                + self.quotient_range_proof.len(),
        );
        out.extend_from_slice(DECRYPT_SHARE_PROOF_MAGIC);
        push_byte_vectors(&mut out, &self.smudge_commitments);
        out.extend_from_slice(&(self.smudge_low_range_proof.len() as u64).to_le_bytes());
        out.extend_from_slice(&self.smudge_low_range_proof);
        out.extend_from_slice(&(self.smudge_high_range_proof.len() as u64).to_le_bytes());
        out.extend_from_slice(&self.smudge_high_range_proof);
        push_byte_vectors(&mut out, &self.product_commitments);
        push_byte_vectors(&mut out, &self.quotient_commitments);
        out.extend_from_slice(&(self.quotient_range_proof.len() as u64).to_le_bytes());
        out.extend_from_slice(&self.quotient_range_proof);
        out.extend_from_slice(&self.relation_nonce);
        out.extend_from_slice(&self.relation_response);
        out
    }

    fn from_wire_bytes(bytes: &[u8], params: &BfvParams) -> Result<Self> {
        let mut cursor = WireCursor::new(bytes);
        if cursor.take::<8>()? != *DECRYPT_SHARE_PROOF_MAGIC {
            return Err(QuorumError::MalformedWire);
        }
        let smudge_commitments = take_byte_vectors(&mut cursor, 4 * params.degree())?;
        let smudge_proof_len = cursor.usize()?;
        let smudge_low_range_proof = cursor.bytes(smudge_proof_len)?.to_vec();
        let smudge_high_proof_len = cursor.usize()?;
        let smudge_high_range_proof = cursor.bytes(smudge_high_proof_len)?.to_vec();
        let equations = params.moduli().len() * params.degree();
        let product_commitments = take_byte_vectors(&mut cursor, equations)?;
        let quotient_commitment_count = range_padded_len(2 * equations)?;
        let quotient_commitments = take_byte_vectors(&mut cursor, quotient_commitment_count)?;
        let quotient_proof_len = cursor.usize()?;
        let quotient_range_proof = cursor.bytes(quotient_proof_len)?.to_vec();
        let relation_nonce = cursor.take::<32>()?;
        let relation_response = cursor.take::<32>()?;
        if !cursor.finished()
            || Option::<Scalar>::from(Scalar::from_canonical_bytes(relation_response)).is_none()
        {
            return Err(QuorumError::MalformedWire);
        }
        Ok(Self {
            smudge_commitments,
            smudge_low_range_proof,
            smudge_high_range_proof,
            product_commitments,
            quotient_commitments,
            quotient_range_proof,
            relation_nonce,
            relation_response,
        })
    }
}

/// Public, Lagrange-weighted decryption-share message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumDecryptShare {
    opening: QuorumOpeningSession,
    ct: LeanCiphertext,
    party: usize,
    smudge_bits: u32,
    h: Vec<Vec<u64>>,
    proof: Option<QuorumDecryptShareProof>,
}

impl QuorumDecryptShare {
    pub fn party(&self) -> usize {
        self.party
    }

    pub fn opening(&self) -> &QuorumOpeningSession {
        &self.opening
    }

    pub fn ciphertext(&self) -> &LeanCiphertext {
        &self.ct
    }

    /// Canonical inner-body framing.  Network callers should wrap this with
    /// [`AuthenticatedQuorumRoster::sign_share`].  A verified-DKG share also
    /// carries a zero-knowledge relation/range certificate; legacy setup shares
    /// deliberately carry no such certificate and are refused by a verified
    /// combiner.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let ct_bytes = self.ct.to_fhe_bytes();
        let mut out = Vec::with_capacity(
            128 + ct_bytes.len() + self.h.iter().map(Vec::len).sum::<usize>() * 8,
        );
        out.extend_from_slice(b"FHQDv002");
        out.extend_from_slice(&(self.opening.keygen.n_parties() as u64).to_le_bytes());
        out.extend_from_slice(&(self.opening.keygen.threshold as u64).to_le_bytes());
        out.extend_from_slice(&self.opening.keygen.base.crp_seed());
        out.extend_from_slice(&self.opening.nonce);
        match self.opening.vss_setup_digest {
            Some(digest) => {
                out.push(1);
                out.extend_from_slice(&digest);
            }
            None => out.push(0),
        }
        out.extend_from_slice(&(self.opening.parties.len() as u64).to_le_bytes());
        for &party in &self.opening.parties {
            out.extend_from_slice(&(party as u64).to_le_bytes());
        }
        out.extend_from_slice(&(self.party as u64).to_le_bytes());
        out.extend_from_slice(&self.smudge_bits.to_le_bytes());
        out.extend_from_slice(&self.ct.plain_bound.to_le_bytes());
        out.extend_from_slice(&(ct_bytes.len() as u64).to_le_bytes());
        out.extend_from_slice(&ct_bytes);
        for row in &self.h {
            for &coefficient in row {
                out.extend_from_slice(&coefficient.to_le_bytes());
            }
        }
        match &self.proof {
            Some(proof) => {
                out.push(1);
                let proof = proof.to_wire_bytes();
                out.extend_from_slice(&(proof.len() as u64).to_le_bytes());
                out.extend_from_slice(&proof);
            }
            None => out.push(0),
        }
        out
    }

    pub fn from_wire_bytes(bytes: &[u8], params: &BfvParams) -> Result<Self> {
        let mut cursor = WireCursor::new(bytes);
        if cursor.take::<8>()? != *b"FHQDv002" {
            return Err(QuorumError::MalformedWire);
        }
        let n = cursor.usize()?;
        let threshold = cursor.usize()?;
        let seed = cursor.take::<32>()?;
        let nonce = cursor.take::<32>()?;
        let vss_setup_digest = match cursor.take::<1>()?[0] {
            0 => None,
            1 => Some(cursor.take::<32>()?),
            _ => return Err(QuorumError::MalformedWire),
        };
        let roster_len = cursor.usize()?;
        if roster_len > n {
            return Err(QuorumError::MalformedWire);
        }
        let mut parties = Vec::with_capacity(roster_len);
        for _ in 0..roster_len {
            parties.push(cursor.usize()?);
        }
        let keygen = QuorumKeygenSession::from_seed(n, threshold, seed)?;
        let opening = QuorumOpeningSession::new_inner(keygen, vss_setup_digest, nonce, parties)?;
        let party = cursor.usize()?;
        let smudge_bits = u32::from_le_bytes(cursor.take::<4>()?);
        let plain_bound = u64::from_le_bytes(cursor.take::<8>()?);
        let ct_len = cursor.usize()?;
        let ct_bytes = cursor.bytes(ct_len)?;
        let ct =
            LeanCiphertext::from_fhe_bytes(ct_bytes, params.moduli(), params.degree(), plain_bound)
                .map_err(|_| QuorumError::MalformedWire)?;

        let mut h = Vec::with_capacity(params.moduli().len());
        for &q in params.moduli() {
            let mut row = Vec::with_capacity(params.degree());
            for _ in 0..params.degree() {
                let coefficient = u64::from_le_bytes(cursor.take::<8>()?);
                if coefficient >= q {
                    return Err(QuorumError::MalformedWire);
                }
                row.push(coefficient);
            }
            h.push(row);
        }
        let proof = match cursor.take::<1>()?[0] {
            0 => None,
            1 => {
                let proof_len = cursor.usize()?;
                Some(QuorumDecryptShareProof::from_wire_bytes(
                    cursor.bytes(proof_len)?,
                    params,
                )?)
            }
            _ => return Err(QuorumError::MalformedWire),
        };
        if !cursor.finished() || !opening.parties.contains(&party) {
            return Err(QuorumError::MalformedWire);
        }
        Ok(Self {
            opening,
            ct,
            party,
            smudge_bits,
            h,
            proof,
        })
    }
}

/// Ordered custody identities authorized to authenticate decryption shares for
/// one exact DKG session.
///
/// Party indices are positions in `ordered_public_keys`; the list must contain
/// exactly the DKG's `n` parties, with no duplicate or weak Ed25519 keys.  Its
/// digest covers the DKG `(n,t,crp_seed)`, the accepted bivariate-VSS setup
/// digest on the verified path, and every key in order, so a signature cannot
/// be replayed under a reordered/substituted custody or setup roster.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedQuorumRoster {
    keygen: QuorumKeygenSession,
    vss_setup_digest: Option<[u8; 32]>,
    verified_transcript: Option<VerifiedDkgTranscript>,
    ordered_public_keys: Vec<[u8; 32]>,
    digest: [u8; 32],
}

impl AuthenticatedQuorumRoster {
    pub fn new(keygen: QuorumKeygenSession, ordered_public_keys: Vec<[u8; 32]>) -> Result<Self> {
        Self::new_inner(keygen, None, None, ordered_public_keys)
    }

    /// Bind custody identities to an accepted bivariate-VSS setup transcript.
    pub fn new_verified(
        keygen: QuorumKeygenSession,
        transcript: &VerifiedDkgTranscript,
        ordered_public_keys: Vec<[u8; 32]>,
    ) -> Result<Self> {
        if transcript.session != keygen {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        Self::new_inner(
            keygen,
            Some(transcript.digest),
            Some(transcript.clone()),
            ordered_public_keys,
        )
    }

    fn new_inner(
        keygen: QuorumKeygenSession,
        vss_setup_digest: Option<[u8; 32]>,
        verified_transcript: Option<VerifiedDkgTranscript>,
        ordered_public_keys: Vec<[u8; 32]>,
    ) -> Result<Self> {
        if verified_transcript
            .as_ref()
            .map(|transcript| (&transcript.session, transcript.digest))
            .map_or(vss_setup_digest.is_some(), |(session, digest)| {
                session != &keygen || Some(digest) != vss_setup_digest
            })
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        if ordered_public_keys.len() != keygen.n_parties() {
            return Err(QuorumError::ParamMismatch);
        }
        let mut seen = HashSet::with_capacity(ordered_public_keys.len());
        for (party, key) in ordered_public_keys.iter().enumerate() {
            let verifying = VerifyingKey::from_bytes(key)
                .map_err(|_| QuorumError::InvalidPublicKey { party })?;
            if verifying.is_weak() {
                return Err(QuorumError::InvalidPublicKey { party });
            }
            if !seen.insert(*key) {
                return Err(QuorumError::DuplicatePublicKey { party });
            }
        }
        let digest = authenticated_roster_digest(&keygen, vss_setup_digest, &ordered_public_keys);
        Ok(Self {
            keygen,
            vss_setup_digest,
            verified_transcript,
            ordered_public_keys,
            digest,
        })
    }

    pub fn ordered_public_keys(&self) -> &[[u8; 32]] {
        &self.ordered_public_keys
    }

    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Authenticate an already-formed share as its declared custody party.
    /// The signing key must exactly match that party's roster slot.
    pub fn sign_share(
        &self,
        share: QuorumDecryptShare,
        signing_key: &SigningKey,
    ) -> Result<AuthenticatedQuorumDecryptShare> {
        if share.opening.keygen != self.keygen {
            return Err(QuorumError::SessionMismatch);
        }
        if share.opening.vss_setup_digest != self.vss_setup_digest {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        let expected =
            self.ordered_public_keys
                .get(share.party)
                .ok_or(QuorumError::InvalidParty {
                    party: share.party,
                    n_parties: self.ordered_public_keys.len(),
                })?;
        if signing_key.verifying_key().to_bytes() != *expected {
            return Err(QuorumError::SignerKeyMismatch { party: share.party });
        }
        let signature = signing_key
            .sign(&authenticated_share_message(
                &self.digest,
                &share.to_wire_bytes(),
            ))
            .to_bytes();
        Ok(AuthenticatedQuorumDecryptShare {
            roster_digest: self.digest,
            share,
            signature,
        })
    }

    fn verify_share(&self, signed: &AuthenticatedQuorumDecryptShare) -> Result<()> {
        if signed.roster_digest != self.digest {
            return Err(QuorumError::AuthenticationRosterMismatch);
        }
        if signed.share.opening.keygen != self.keygen {
            return Err(QuorumError::SessionMismatch);
        }
        if signed.share.opening.vss_setup_digest != self.vss_setup_digest {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        let party = signed.share.party;
        let key = self
            .ordered_public_keys
            .get(party)
            .ok_or(QuorumError::InvalidParty {
                party,
                n_parties: self.ordered_public_keys.len(),
            })?;
        let verifying =
            VerifyingKey::from_bytes(key).map_err(|_| QuorumError::InvalidPublicKey { party })?;
        verifying
            .verify_strict(
                &authenticated_share_message(&self.digest, &signed.share.to_wire_bytes()),
                &Signature::from_bytes(&signed.signature),
            )
            .map_err(|_| QuorumError::InvalidSignature { party })
    }
}

/// Canonical, authenticated public decryption-share envelope.
///
/// The signature covers the roster digest and the complete canonical inner
/// share body.  Parsing alone does not authenticate; verification is performed
/// by [`AuthenticatedQuorumCombiner::combine_framed`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedQuorumDecryptShare {
    roster_digest: [u8; 32],
    share: QuorumDecryptShare,
    signature: [u8; 64],
}

/// Digest-only public audit evidence for one successful authenticated opening.
///
/// This contains no decryption-share coefficients, signatures, ciphertext, or
/// plaintext.  Its transcript digest commits to the exact canonical ordered
/// signed envelopes after all identity/session/target checks pass; [`digest`]
/// binds that transcript to the configured custody roster, opening session,
/// ciphertext target, and share count for inclusion in a higher-level receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedOpeningAudit {
    roster_digest: [u8; 32],
    vss_setup_digest: Option<[u8; 32]>,
    opening_digest: [u8; 32],
    ciphertext_digest: [u8; 32],
    transcript_digest: [u8; 32],
    share_count: usize,
}

impl AuthenticatedOpeningAudit {
    pub fn roster_digest(&self) -> [u8; 32] {
        self.roster_digest
    }

    /// The accepted bivariate-VSS setup carried by both the opening and the
    /// authenticated custody roster (`None` only on the legacy setup path).
    pub fn vss_setup_digest(&self) -> Option<[u8; 32]> {
        self.vss_setup_digest
    }

    pub fn opening_digest(&self) -> [u8; 32] {
        self.opening_digest
    }

    pub fn ciphertext_digest(&self) -> [u8; 32] {
        self.ciphertext_digest
    }

    pub fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    pub fn share_count(&self) -> usize {
        self.share_count
    }

    pub fn digest(&self) -> [u8; 32] {
        let mut hash = Sha256::new();
        hash.update(AUTHENTICATED_AUDIT_DOMAIN);
        hash.update(self.roster_digest);
        hash_optional_digest(&mut hash, self.vss_setup_digest);
        hash.update(self.opening_digest);
        hash.update(self.ciphertext_digest);
        hash.update(self.transcript_digest);
        hash.update((self.share_count as u64).to_le_bytes());
        hash.finalize().into()
    }
}

impl AuthenticatedQuorumDecryptShare {
    pub fn party(&self) -> usize {
        self.share.party
    }

    pub fn share(&self) -> &QuorumDecryptShare {
        &self.share
    }

    pub fn roster_digest(&self) -> [u8; 32] {
        self.roster_digest
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let share = self.share.to_wire_bytes();
        let mut out = Vec::with_capacity(8 + 32 + 8 + share.len() + 64);
        out.extend_from_slice(AUTHENTICATED_SHARE_MAGIC);
        out.extend_from_slice(&self.roster_digest);
        out.extend_from_slice(&(share.len() as u64).to_le_bytes());
        out.extend_from_slice(&share);
        out.extend_from_slice(&self.signature);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8], params: &BfvParams) -> Result<Self> {
        let mut cursor = WireCursor::new(bytes);
        if cursor.take::<8>()? != *AUTHENTICATED_SHARE_MAGIC {
            return Err(QuorumError::MalformedWire);
        }
        let roster_digest = cursor.take::<32>()?;
        let share_len = cursor.usize()?;
        let share = QuorumDecryptShare::from_wire_bytes(cursor.bytes(share_len)?, params)?;
        let signature = cursor.take::<64>()?;
        if !cursor.finished() {
            return Err(QuorumError::MalformedWire);
        }
        Ok(Self {
            roster_digest,
            share,
            signature,
        })
    }
}

/// Stateful relying-party gate for authenticated threshold openings.
///
/// It requires exactly one signed envelope per party in the opening's canonical
/// order, verifies every signature against the DKG-bound identity roster, and
/// binds every body to the caller-supplied exact ciphertext before combining.
/// Successfully opened ciphertexts are remembered so a renamed nonce cannot
/// replay the same target through this in-memory combiner.
pub struct AuthenticatedQuorumCombiner {
    roster: AuthenticatedQuorumRoster,
    opened_sessions: BTreeSet<[u8; 32]>,
    opened_targets: BTreeSet<[u8; 32]>,
}

impl AuthenticatedQuorumCombiner {
    pub fn new(roster: AuthenticatedQuorumRoster) -> Self {
        Self {
            roster,
            opened_sessions: BTreeSet::new(),
            opened_targets: BTreeSet::new(),
        }
    }

    pub fn roster(&self) -> &AuthenticatedQuorumRoster {
        &self.roster
    }

    pub fn combine_framed(
        &mut self,
        expected: &QuorumOpeningSession,
        expected_ciphertext: &LeanCiphertext,
        framed_shares: &[Vec<u8>],
        params: &BfvParams,
    ) -> Result<Vec<u64>> {
        self.combine_framed_with_audit(expected, expected_ciphertext, framed_shares, params)
            .map(|(opened, _audit)| opened)
    }

    /// Verify and combine like [`combine_framed`](Self::combine_framed), while
    /// returning a digest-only commitment to the accepted custody transcript.
    pub fn combine_framed_with_audit(
        &mut self,
        expected: &QuorumOpeningSession,
        expected_ciphertext: &LeanCiphertext,
        framed_shares: &[Vec<u8>],
        params: &BfvParams,
    ) -> Result<(Vec<u64>, AuthenticatedOpeningAudit)> {
        if expected.keygen != self.roster.keygen {
            return Err(QuorumError::SessionMismatch);
        }
        if expected.vss_setup_digest != self.roster.vss_setup_digest {
            return Err(QuorumError::VssTranscriptMismatch);
        }
        validate_ciphertext(expected_ciphertext, params)?;
        let session = opening_digest(expected);
        let target = target_digest(expected_ciphertext);
        if self.opened_sessions.contains(&session) || self.opened_targets.contains(&target) {
            return Err(QuorumError::Replay);
        }
        if framed_shares.len() < expected.parties.len() {
            return Err(QuorumError::QuorumTooSmall {
                have: framed_shares.len(),
                need: expected.parties.len(),
            });
        }
        if framed_shares.len() > expected.parties.len() {
            return Err(QuorumError::ParamMismatch);
        }

        let mut seen = BTreeSet::new();
        let mut shares = Vec::with_capacity(framed_shares.len());
        let mut transcript = Sha256::new();
        transcript.update(AUTHENTICATED_TRANSCRIPT_DOMAIN);
        transcript.update(self.roster.digest);
        transcript.update(session);
        transcript.update(target);
        transcript.update((framed_shares.len() as u64).to_le_bytes());
        for (position, wire) in framed_shares.iter().enumerate() {
            let signed = AuthenticatedQuorumDecryptShare::from_wire_bytes(wire, params)?;
            if !seen.insert(signed.share.party) {
                return Err(QuorumError::DuplicateParty {
                    party: signed.share.party,
                });
            }
            let expected_party = expected.parties[position];
            if signed.share.party != expected_party {
                return Err(QuorumError::NonCanonicalShareOrder);
            }
            if signed.share.opening != *expected {
                return Err(QuorumError::SessionMismatch);
            }
            if signed.share.ct != *expected_ciphertext {
                return Err(QuorumError::SessionMismatch);
            }
            self.roster.verify_share(&signed)?;
            let canonical = signed.to_wire_bytes();
            if canonical.as_slice() != wire.as_slice() {
                return Err(QuorumError::MalformedWire);
            }
            transcript.update((signed.share.party as u64).to_le_bytes());
            transcript.update((canonical.len() as u64).to_le_bytes());
            transcript.update(&canonical);
            shares.push(signed.share);
        }
        // Authenticate, canonicalize, and bind the complete ordered roster
        // before starting expensive ZK work.  Independent public share proofs
        // then verify concurrently.  The helper collects indexed Rayon output
        // and replays errors in canonical party order, so scheduling cannot
        // make externally observed failure precedence nondeterministic.
        if let Some(verified_transcript) = &self.roster.verified_transcript {
            verify_decrypt_share_relations_parallel(&shares, verified_transcript, params)?;
        }

        let opened = combine_quorum(&shares, expected, params)?;
        let audit = AuthenticatedOpeningAudit {
            roster_digest: self.roster.digest,
            vss_setup_digest: expected.vss_setup_digest,
            opening_digest: session,
            ciphertext_digest: target,
            transcript_digest: transcript.finalize().into(),
            share_count: shares.len(),
        };
        self.opened_sessions.insert(session);
        self.opened_targets.insert(target);
        Ok((opened, audit))
    }
}

/// Combine exactly the expected live `t`-party roster and reveal the BFV slots.
pub fn combine_quorum(
    shares: &[QuorumDecryptShare],
    expected: &QuorumOpeningSession,
    params: &BfvParams,
) -> Result<Vec<u64>> {
    if shares.is_empty() {
        return Err(QuorumError::QuorumTooSmall {
            have: 0,
            need: expected.parties.len(),
        });
    }
    let first = &shares[0];
    validate_ciphertext(&first.ct, params)?;
    let mut seen = BTreeSet::new();
    for share in shares {
        if share.opening != *expected {
            return Err(QuorumError::SessionMismatch);
        }
        if share.ct != first.ct || !valid_rows(&share.h, params) {
            return Err(QuorumError::ParamMismatch);
        }
        if !expected.parties.contains(&share.party) {
            return Err(QuorumError::PartyNotSelected { party: share.party });
        }
        if !seen.insert(share.party) {
            return Err(QuorumError::DuplicateParty { party: share.party });
        }
        if share.smudge_bits < MIN_SMUDGE_BITS {
            return Err(QuorumError::SmudgeTooSmall);
        }
        let width = ceil_log2(expected.parties.len()).ok_or(QuorumError::InvalidParameters)?;
        if share
            .smudge_bits
            .checked_add(width)
            .map_or(true, |total| total > MAX_SMUDGE_BITS_TOTAL)
        {
            return Err(QuorumError::SmudgeTooLarge);
        }
    }
    if seen.len() < expected.parties.len() {
        return Err(QuorumError::QuorumTooSmall {
            have: seen.len(),
            need: expected.parties.len(),
        });
    }
    if seen.len() > expected.parties.len() {
        return Err(QuorumError::ParamMismatch);
    }

    let mut c0 = first.ct.polys[0].rows.clone();
    for share in shares {
        for (row, (hrow, &q)) in c0.iter_mut().zip(share.h.iter().zip(params.moduli())) {
            for (coefficient, &value) in row.iter_mut().zip(hrow) {
                *coefficient = add_mod(*coefficient, value, q);
            }
        }
    }
    let combined = LeanCiphertext {
        polys: vec![
            RnsPoly { rows: c0 },
            RnsPoly {
                rows: first.ct.polys[1].rows.clone(),
            },
        ],
        ..first.ct.clone()
    };
    let fhe_ct = Ciphertext::from_bytes(&combined.to_fhe_bytes(), params.arc())
        .map_err(|_| QuorumError::ParamMismatch)?;
    let zero_sk = sk_from_coeffs(&vec![0i64; params.degree()], params.arc());
    let plaintext = zero_sk
        .try_decrypt(&fhe_ct)
        .map_err(|_| QuorumError::ParamMismatch)?;
    Vec::<u64>::try_decode(&plaintext, Encoding::simd_at_level(first.ct.level as usize))
        .map_err(|_| QuorumError::ParamMismatch)
}

fn valid_rows(rows: &[Vec<u64>], params: &BfvParams) -> bool {
    rows.len() == params.moduli().len()
        && rows
            .iter()
            .zip(params.moduli())
            .all(|(row, &q)| row.len() == params.degree() && row.iter().all(|&value| value < q))
}

fn validate_ciphertext(ct: &LeanCiphertext, params: &BfvParams) -> Result<()> {
    if ct.moduli != params.moduli()
        || ct.degree != params.degree()
        || ct.polys.len() != 2
        || ct.polys.iter().any(|poly| !valid_rows(&poly.rows, params))
    {
        return Err(QuorumError::ParamMismatch);
    }
    Ok(())
}

fn evaluate_polynomial(coefficients: &[u64], x: u64, q: u64) -> u64 {
    coefficients.iter().rev().fold(0, |value, &coefficient| {
        add_mod(mul_mod(value, x, q), coefficient, q)
    })
}

fn zero_rns_rows(params: &BfvParams) -> Vec<Vec<u64>> {
    params
        .moduli()
        .iter()
        .map(|_| vec![0u64; params.degree()])
        .collect()
}

fn add_rns(left: &[Vec<u64>], right: &[Vec<u64>], params: &BfvParams) -> Result<Vec<Vec<u64>>> {
    if !valid_rows(left, params) || !valid_rows(right, params) {
        return Err(QuorumError::ParamMismatch);
    }
    Ok(left
        .iter()
        .zip(right)
        .zip(params.moduli())
        .map(|((left, right), &q)| {
            left.iter()
                .zip(right)
                .map(|(&left, &right)| add_mod(left, right, q))
                .collect()
        })
        .collect())
}

fn sub_rns(left: &[Vec<u64>], right: &[Vec<u64>], params: &BfvParams) -> Result<Vec<Vec<u64>>> {
    if !valid_rows(left, params) || !valid_rows(right, params) {
        return Err(QuorumError::ParamMismatch);
    }
    Ok(left
        .iter()
        .zip(right)
        .zip(params.moduli())
        .map(|((left, right), &q)| {
            left.iter()
                .zip(right)
                .map(|(&left, &right)| add_mod(left, if right == 0 { 0 } else { q - right }, q))
                .collect()
        })
        .collect())
}

fn public_key_as_lean(
    contribution: &PublicKeyContribution,
    params: &BfvParams,
) -> Result<LeanCiphertext> {
    let bytes = contribution.public_key_bytes();
    if bytes.first() != Some(&0x0a) {
        return Err(QuorumError::InvalidPublicKey {
            party: contribution.party(),
        });
    }
    let mut position = 1usize;
    let length = take_proto_varint(bytes, &mut position)?;
    let length = usize::try_from(length).map_err(|_| QuorumError::MalformedWire)?;
    let end = position
        .checked_add(length)
        .filter(|&end| end == bytes.len())
        .ok_or(QuorumError::MalformedWire)?;
    LeanCiphertext::from_fhe_bytes(&bytes[position..end], params.moduli(), params.degree(), 0)
        .map_err(|_| QuorumError::InvalidPublicKey {
            party: contribution.party(),
        })
}

fn take_proto_varint(bytes: &[u8], position: &mut usize) -> Result<u64> {
    let mut value = 0u64;
    let mut shift = 0u32;
    loop {
        let byte = *bytes.get(*position).ok_or(QuorumError::MalformedWire)?;
        *position += 1;
        if shift >= 64 {
            return Err(QuorumError::MalformedWire);
        }
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Ok(value);
        }
        shift += 7;
    }
}

fn vss_row_matches_linear_commitments(
    share: &PrivateDealerShare,
    crp_rows: &[Vec<u64>],
    linear_commitments: &[Vec<Vec<u64>>],
    params: &BfvParams,
) -> Result<bool> {
    let t = share.session.threshold();
    if linear_commitments.len() != t * t {
        return Ok(false);
    }
    let x = share.recipient as u64 + 1;
    for y_degree in 0..t {
        let product = multiply_rns(crp_rows, &share.vss_row_coefficients[y_degree], params)?;
        let lhs = sub_rns(
            &share.vss_error_row_coefficients[y_degree],
            &product,
            params,
        )?;
        let mut rhs = zero_rns_rows(params);
        for x_degree in (0..t).rev() {
            let commitment = &linear_commitments[x_degree * t + y_degree];
            for (row_index, &q) in params.moduli().iter().enumerate() {
                for coefficient_index in 0..params.degree() {
                    rhs[row_index][coefficient_index] = add_mod(
                        mul_mod(rhs[row_index][coefficient_index], x, q),
                        commitment[row_index][coefficient_index],
                        q,
                    );
                }
            }
        }
        if lhs != rhs {
            return Ok(false);
        }
    }
    Ok(true)
}

fn vss_cross_evaluations_match(
    left_coefficients: &[Vec<Vec<u64>>],
    left_recipient: usize,
    right_coefficients: &[Vec<Vec<u64>>],
    right_recipient: usize,
    params: &BfvParams,
) -> bool {
    for (row_index, &q) in params.moduli().iter().enumerate() {
        for coefficient_index in 0..params.degree() {
            let left_polynomial = left_coefficients
                .iter()
                .map(|coefficient| coefficient[row_index][coefficient_index])
                .collect::<Vec<_>>();
            let right_polynomial = right_coefficients
                .iter()
                .map(|coefficient| coefficient[row_index][coefficient_index])
                .collect::<Vec<_>>();
            let left_at_right =
                evaluate_polynomial(&left_polynomial, right_recipient as u64 + 1, q);
            let right_at_left =
                evaluate_polynomial(&right_polynomial, left_recipient as u64 + 1, q);
            if left_at_right != right_at_left {
                return false;
            }
        }
    }
    true
}

fn vss_row_commitment_digest(
    session: &QuorumKeygenSession,
    dealer: usize,
    recipient: usize,
    public_key_digest: &[u8; 32],
    salt: &[u8; 32],
    row_coefficients: &[Vec<Vec<u64>>],
    error_row_coefficients: &[Vec<Vec<u64>>],
    params: &BfvParams,
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(VSS_ROW_COMMITMENT_DOMAIN);
    hash.update((session.n_parties() as u64).to_le_bytes());
    hash.update((session.threshold() as u64).to_le_bytes());
    hash.update(session.base.crp_seed());
    hash.update((dealer as u64).to_le_bytes());
    hash.update((recipient as u64).to_le_bytes());
    hash.update(public_key_digest);
    hash.update((params.degree() as u64).to_le_bytes());
    hash.update((params.moduli().len() as u64).to_le_bytes());
    for &q in params.moduli() {
        hash.update(q.to_le_bytes());
    }
    hash.update((row_coefficients.len() as u64).to_le_bytes());
    hash.update((error_row_coefficients.len() as u64).to_le_bytes());
    hash.update(salt);
    for coefficient in row_coefficients {
        for row in coefficient {
            for value in row {
                hash.update(value.to_le_bytes());
            }
        }
    }
    for coefficient in error_row_coefficients {
        for row in coefficient {
            for value in row {
                hash.update(value.to_le_bytes());
            }
        }
    }
    hash.finalize().into()
}

fn dealer_vss_commitment_digest(
    session: &QuorumKeygenSession,
    dealer: usize,
    public_key_digest: &[u8; 32],
    row_commitments: &[[u8; 32]],
    linear_commitments: &[Vec<Vec<u64>>],
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(VSS_DEALER_COMMITMENT_DOMAIN);
    hash.update((session.n_parties() as u64).to_le_bytes());
    hash.update((session.threshold() as u64).to_le_bytes());
    hash.update(session.base.crp_seed());
    hash.update((dealer as u64).to_le_bytes());
    hash.update(public_key_digest);
    hash.update((row_commitments.len() as u64).to_le_bytes());
    for commitment in row_commitments {
        hash.update(commitment);
    }
    hash.update((linear_commitments.len() as u64).to_le_bytes());
    for commitment in linear_commitments {
        for row in commitment {
            for value in row {
                hash.update(value.to_le_bytes());
            }
        }
    }
    hash.finalize().into()
}

fn vss_setup_transcript_digest(
    session: &QuorumKeygenSession,
    dealer_commitment_digests: &[[u8; 32]],
    party_secret_commitments: &[Vec<[u8; 32]>],
    collective_key_digest: [u8; 32],
    params: &BfvParams,
    q0_share_commitments: Option<&[PqShareCommitment]>,
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(VSS_SETUP_TRANSCRIPT_DOMAIN);
    hash.update((session.n_parties() as u64).to_le_bytes());
    hash.update((session.threshold() as u64).to_le_bytes());
    hash.update(session.base.crp_seed());
    hash.update((params.degree() as u64).to_le_bytes());
    hash.update(params.plaintext_modulus().to_le_bytes());
    hash.update((params.moduli().len() as u64).to_le_bytes());
    for &q in params.moduli() {
        hash.update(q.to_le_bytes());
    }
    hash.update(collective_key_digest);
    hash.update((dealer_commitment_digests.len() as u64).to_le_bytes());
    for digest in dealer_commitment_digests {
        hash.update(digest);
    }
    hash.update((party_secret_commitments.len() as u64).to_le_bytes());
    for commitments in party_secret_commitments {
        hash.update((commitments.len() as u64).to_le_bytes());
        for commitment in commitments {
            hash.update(commitment);
        }
    }
    let classical_digest: [u8; 32] = hash.finalize().into();
    let Some(commitments) = q0_share_commitments else {
        return classical_digest;
    };
    let mut anchored = Sha256::new();
    anchored.update(VSS_Q0_ANCHORED_TRANSCRIPT_DOMAIN);
    anchored.update(classical_digest);
    anchored.update((commitments.len() as u64).to_le_bytes());
    for commitment in commitments {
        let wire = commitment.to_wire_bytes();
        anchored.update((wire.len() as u64).to_le_bytes());
        anchored.update(wire);
    }
    anchored.finalize().into()
}

fn q0_share_commitment_seed(context: [u8; 32]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((DKG_Q0_SHARE_SEED_DOMAIN.len() as u64).to_le_bytes());
    hash.update(DKG_Q0_SHARE_SEED_DOMAIN);
    hash.update(context);
    hash.finalize().into()
}

fn verified_dkg_collective_key_digest(collective: &CollectivePublicKey) -> [u8; 32] {
    let key_bytes = collective.pk.to_bytes();
    let mut hash = Sha256::new();
    hash.update(VERIFIED_DKG_COLLECTIVE_KEY_DOMAIN);
    hash.update((key_bytes.len() as u64).to_le_bytes());
    hash.update(key_bytes);
    hash.finalize().into()
}

fn hash_optional_digest(hash: &mut Sha256, digest: Option<[u8; 32]>) {
    match digest {
        Some(digest) => {
            hash.update([1]);
            hash.update(digest);
        }
        None => hash.update([0]),
    }
}

fn lagrange_at_zero(party: usize, roster: &[usize], q: u64) -> Result<u64> {
    let x_i = party as u64 + 1;
    let mut numerator = 1u64;
    let mut denominator = 1u64;
    for &other in roster {
        if other == party {
            continue;
        }
        let x_j = other as u64 + 1;
        numerator = mul_mod(numerator, if x_j == 0 { 0 } else { q - x_j }, q);
        let difference = if x_i >= x_j {
            x_i - x_j
        } else {
            q - (x_j - x_i)
        };
        denominator = mul_mod(denominator, difference, q);
    }
    if denominator == 0 {
        return Err(QuorumError::NonCanonicalRoster);
    }
    Ok(mul_mod(numerator, mod_pow(denominator, q - 2, q), q))
}

fn mul_mod(a: u64, b: u64, q: u64) -> u64 {
    ((a as u128 * b as u128) % q as u128) as u64
}

fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut result = 1u64;
    while exponent != 0 {
        if exponent & 1 == 1 {
            result = mul_mod(result, base, modulus);
        }
        base = mul_mod(base, base, modulus);
        exponent >>= 1;
    }
    result
}

fn multiply_rns(
    left_rows: &[Vec<u64>],
    right_rows: &[Vec<u64>],
    params: &BfvParams,
) -> Result<Vec<Vec<u64>>> {
    if !valid_rows(left_rows, params) || !valid_rows(right_rows, params) {
        return Err(QuorumError::ParamMismatch);
    }
    let context = RqContext::new_arc(params.moduli(), params.degree())
        .map_err(|_| QuorumError::InvalidParameters)?;
    let mut left = Poly::try_convert_from(
        left_rows.iter().flatten().copied().collect::<Vec<_>>(),
        &context,
        false,
        Representation::PowerBasis,
    )
    .map_err(|_| QuorumError::ParamMismatch)?;
    let mut right = Poly::try_convert_from(
        right_rows.iter().flatten().copied().collect::<Vec<_>>(),
        &context,
        false,
        Representation::PowerBasis,
    )
    .map_err(|_| QuorumError::ParamMismatch)?;
    left.change_representation(Representation::Ntt);
    right.change_representation(Representation::Ntt);
    let mut product = &left * &right;
    product.change_representation(Representation::PowerBasis);
    Ok(product
        .coefficients()
        .outer_iter()
        .map(|row| row.to_vec())
        .collect())
}

fn decrypt_range_gens() -> &'static BulletproofGens {
    // The deployed fold set has degree 4096 and two RNS moduli.  Both the
    // smudge/complement vector (4N) and quotient vector (2LN) therefore contain
    // 16384 values.  The parameter gate below refuses larger/non-power-of-two
    // shapes instead of silently constructing a weaker proof.
    static GENS: OnceLock<BulletproofGens> = OnceLock::new();
    GENS.get_or_init(|| BulletproofGens::new(64, 32_768))
}

fn range_padded_len(values: usize) -> Result<usize> {
    values
        .checked_next_power_of_two()
        .filter(|&padded| padded <= 32_768)
        .ok_or(QuorumError::UnsupportedDecryptProofParameters)
}

fn decrypt_proof_params_supported(params: &BfvParams, smudge_bits: u32) -> bool {
    let degree = params.degree();
    let moduli = params.moduli().len();
    let smudge_values = degree.checked_mul(4);
    let quotient_values = degree.checked_mul(moduli).and_then(|v| v.checked_mul(2));
    let max_q_bits = params
        .moduli()
        .iter()
        .map(|q| u64::BITS - q.leading_zeros())
        .max()
        .unwrap_or(0);
    let degree_bits = usize::BITS - degree.saturating_sub(1).leading_zeros();
    degree != 0
        && moduli != 0
        && smudge_bits < 127
        && smudge_values.is_some_and(|n| n.is_power_of_two() && n <= 32_768)
        && quotient_values.is_some_and(|n| {
            n.checked_next_power_of_two()
                .is_some_and(|padded| padded <= 32_768)
        })
        // Even the full verifier-admitted signed quotient ranges cannot wrap
        // the ~252-bit Ristretto scalar field after the two equations eliminate
        // their shared hidden product commitment.
        && 2 * max_q_bits + 128 < 250
        && 2 * max_q_bits + degree_bits < 250
}

fn prove_decrypt_share_relation(
    share: &QuorumDecryptShare,
    secret_rows: &[Vec<u64>],
    secret_commitments: &[[u8; 32]],
    secret_blinding_bytes: &[[u8; 32]],
    smudge: &[i128],
    params: &BfvParams,
) -> Result<QuorumDecryptShareProof> {
    if !decrypt_proof_params_supported(params, share.smudge_bits)
        || !valid_rows(secret_rows, params)
        || secret_commitments.len() != params.moduli().len() * params.degree()
        || secret_blinding_bytes.len() != secret_commitments.len()
        || smudge.len() != params.degree()
    {
        return Err(QuorumError::UnsupportedDecryptProofParameters);
    }
    let secret_blindings = secret_blinding_bytes
        .iter()
        .map(|bytes| {
            Option::<Scalar>::from(Scalar::from_canonical_bytes(*bytes))
                .ok_or(QuorumError::VssTranscriptMismatch)
        })
        .collect::<Result<Vec<_>>>()?;
    let pc_gens = PedersenGens::default();
    for ((&value, commitment), &blinding) in secret_rows
        .iter()
        .flatten()
        .zip(secret_commitments)
        .zip(&secret_blindings)
    {
        if pc_gens
            .commit(Scalar::from(value), blinding)
            .compress()
            .to_bytes()
            != *commitment
        {
            return Err(QuorumError::VssTranscriptMismatch);
        }
    }

    let mut transcript = decrypt_share_proof_transcript(share, secret_commitments, params)?;
    let mut rng = OsRng;
    let bound = 1u128 << share.smudge_bits;
    let twice_bound = bound << 1;

    // Range-check both u=smudge+B and v=B-smudge.  Since u+v=2B is proved
    // below and each hidden limb is a canonical u64, this enforces the exact
    // inclusive interval -B <= smudge <= B without exposing even its sign.
    let mut smudge_low_values = Vec::with_capacity(2 * params.degree());
    let mut smudge_high_values = Vec::with_capacity(2 * params.degree());
    let mut smudge_low_blindings = Vec::with_capacity(smudge_low_values.capacity());
    let mut smudge_high_blindings = Vec::with_capacity(smudge_high_values.capacity());
    for &noise in smudge {
        if noise < -(bound as i128) || noise > bound as i128 {
            return Err(QuorumError::SmudgeTooLarge);
        }
        let u = if noise >= 0 {
            bound + noise as u128
        } else {
            bound - noise.unsigned_abs()
        };
        let v = twice_bound - u;
        smudge_low_values.extend_from_slice(&[u as u64, v as u64]);
        smudge_high_values.extend_from_slice(&[(u >> 64) as u64, (v >> 64) as u64]);
        smudge_low_blindings.extend((0..2).map(|_| Scalar::random(&mut rng)));
        smudge_high_blindings.extend((0..2).map(|_| Scalar::random(&mut rng)));
    }
    let (smudge_low_range_proof, smudge_low_points) = RangeProof::prove_multiple(
        decrypt_range_gens(),
        &pc_gens,
        &mut transcript,
        &smudge_low_values,
        &smudge_low_blindings,
        64,
    )
    .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;
    let (smudge_high_range_proof, smudge_high_points) = RangeProof::prove_multiple(
        decrypt_range_gens(),
        &pc_gens,
        &mut transcript,
        &smudge_high_values,
        &smudge_high_blindings,
        32,
    )
    .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;
    let mut smudge_points = smudge_low_points;
    smudge_points.extend(smudge_high_points);
    let mut smudge_blindings = smudge_low_blindings;
    smudge_blindings.extend(smudge_high_blindings);

    // Split the ring relation through a hidden canonical product p:
    //   raw_convolution - p = q*k1
    //   lambda*p + smudge - h = q*k2.
    // `raw_convolution` uses an exact signed I256 accumulator; k1 and k2 fit
    // i128 for the admitted parameters and are independently range-bound.
    let equations = params.moduli().len() * params.degree();
    let mut product_points = Vec::with_capacity(equations);
    let mut product_blindings = Vec::with_capacity(equations);
    let mut quotient_values = Vec::with_capacity(2 * equations);
    let mut quotient_blindings = Vec::with_capacity(2 * equations);
    // The exact integer convolution is the dominant native witness cost at
    // production degree: 2 * N^2 checked I256 products for the deployed two
    // RNS rows.  Every output coefficient is independent.  Compute those
    // outputs in parallel, then consume them below in the original canonical
    // row/coefficient order so OsRng use, commitments, and transcript bytes do
    // not change.
    let raw_convolutions =
        negacyclic_rows_i256_parallel(secret_rows, &share.ct.polys[1].rows, params.degree())?;
    for (row_index, &q) in params.moduli().iter().enumerate() {
        let lambda = lagrange_at_zero(share.party, &share.opening.parties, q)?;
        for coefficient in 0..params.degree() {
            let raw = raw_convolutions[row_index * params.degree() + coefficient];
            let q_wide = I256::from(q);
            let mut product_wide = raw % q_wide;
            if product_wide < I256::ZERO {
                product_wide += q_wide;
            }
            let product = product_wide.as_u64();
            let first_quotient = i256_to_i128((raw - product_wide) / q_wide)?;
            let product_blinding = Scalar::random(&mut rng);
            product_points.push(
                pc_gens
                    .commit(Scalar::from(product), product_blinding)
                    .compress(),
            );
            product_blindings.push(product_blinding);
            let second_numerator = (lambda as i128)
                .checked_mul(product as i128)
                .and_then(|value| value.checked_add(smudge[coefficient]))
                .and_then(|value| value.checked_sub(share.h[row_index][coefficient] as i128))
                .ok_or(QuorumError::UnsupportedDecryptProofParameters)?;
            if second_numerator.rem_euclid(q as i128) != 0 {
                return Err(QuorumError::InvalidDecryptShareProof { party: share.party });
            }
            let second_quotient = second_numerator / q as i128;
            for value in [first_quotient, second_quotient] {
                quotient_values.push(shift_signed_quotient(value)?);
                quotient_blindings.push(Scalar::random(&mut rng));
            }
        }
    }
    let quotient_padded = range_padded_len(quotient_values.len())?;
    while quotient_values.len() < quotient_padded {
        quotient_values.push(0);
        quotient_blindings.push(Scalar::random(&mut rng));
    }
    let (quotient_range_proof, quotient_points) = RangeProof::prove_multiple(
        decrypt_range_gens(),
        &pc_gens,
        &mut transcript,
        &quotient_values,
        &quotient_blindings,
        64,
    )
    .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;

    let secret_points = decompress_points(secret_commitments, share.party)?;
    let smudge_relation_points = smudge_points
        .iter()
        .map(|point| {
            point
                .decompress()
                .ok_or(QuorumError::InvalidDecryptShareProof { party: share.party })
        })
        .collect::<Result<Vec<_>>>()?;
    let product_relation_points = product_points
        .iter()
        .map(|point| {
            point
                .decompress()
                .ok_or(QuorumError::InvalidDecryptShareProof { party: share.party })
        })
        .collect::<Result<Vec<_>>>()?;
    let quotient_relation_points = quotient_points
        .iter()
        .map(|point| {
            point
                .decompress()
                .ok_or(QuorumError::InvalidDecryptShareProof { party: share.party })
        })
        .collect::<Result<Vec<_>>>()?;
    let mut relation = RistrettoPoint::default();
    let mut relation_blinding = Scalar::ZERO;
    accumulate_decrypt_relation(
        &mut transcript,
        share,
        params,
        &secret_points,
        Some(&secret_blindings),
        &smudge_relation_points,
        Some(&smudge_blindings),
        &product_relation_points,
        Some(&product_blindings),
        &quotient_relation_points,
        Some(&quotient_blindings),
        &mut relation,
        Some(&mut relation_blinding),
    )?;

    let nonce = Scalar::random(&mut rng);
    let relation_nonce = (nonce * pc_gens.B_blinding).compress();
    transcript.append_message(DECRYPT_SHARE_RELATION_DOMAIN, relation_nonce.as_bytes());
    let challenge = transcript_challenge_scalar(&mut transcript, b"relation-challenge");
    let relation_response = nonce + challenge * relation_blinding;
    debug_assert_eq!(
        relation_response * pc_gens.B_blinding,
        relation_nonce
            .decompress()
            .expect("fresh compressed Ristretto nonce")
            + challenge * relation
    );
    Ok(QuorumDecryptShareProof {
        smudge_commitments: smudge_points.iter().map(|point| point.to_bytes()).collect(),
        smudge_low_range_proof: smudge_low_range_proof.to_bytes(),
        smudge_high_range_proof: smudge_high_range_proof.to_bytes(),
        product_commitments: product_points
            .iter()
            .map(|point| point.to_bytes())
            .collect(),
        quotient_commitments: quotient_points
            .iter()
            .map(|point| point.to_bytes())
            .collect(),
        quotient_range_proof: quotient_range_proof.to_bytes(),
        relation_nonce: relation_nonce.to_bytes(),
        relation_response: relation_response.to_bytes(),
    })
}

fn verify_decrypt_share_relation(
    share: &QuorumDecryptShare,
    setup: &VerifiedDkgTranscript,
    params: &BfvParams,
) -> Result<()> {
    let proof = share
        .proof
        .as_ref()
        .ok_or(QuorumError::MissingDecryptShareProof { party: share.party })?;
    let quotient_commitment_count = range_padded_len(2 * params.moduli().len() * params.degree())?;
    if share.opening.vss_setup_digest != Some(setup.digest)
        || setup.session != share.opening.keygen
        || !decrypt_proof_params_supported(params, share.smudge_bits)
        || proof.smudge_commitments.len() != 4 * params.degree()
        || proof.product_commitments.len() != params.moduli().len() * params.degree()
        || proof.quotient_commitments.len() != quotient_commitment_count
    {
        return Err(QuorumError::InvalidDecryptShareProof { party: share.party });
    }
    let secret_commitments = setup
        .party_secret_commitments(share.party)
        .ok_or(QuorumError::InvalidDecryptShareProof { party: share.party })?;
    let secret_points = decompress_points(secret_commitments, share.party)?;
    let smudge_points = decompress_points(&proof.smudge_commitments, share.party)?;
    let product_points = decompress_points(&proof.product_commitments, share.party)?;
    let quotient_points = decompress_points(&proof.quotient_commitments, share.party)?;
    let smudge_low_proof = RangeProof::from_bytes(&proof.smudge_low_range_proof)
        .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;
    let smudge_high_proof = RangeProof::from_bytes(&proof.smudge_high_range_proof)
        .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;
    let quotient_proof = RangeProof::from_bytes(&proof.quotient_range_proof)
        .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;
    let pc_gens = PedersenGens::default();
    let mut transcript = decrypt_share_proof_transcript(share, secret_commitments, params)?;
    smudge_low_proof
        .verify_multiple(
            decrypt_range_gens(),
            &pc_gens,
            &mut transcript,
            &proof.smudge_commitments[..2 * params.degree()]
                .iter()
                .map(|bytes| CompressedRistretto(*bytes))
                .collect::<Vec<_>>(),
            64,
        )
        .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;
    smudge_high_proof
        .verify_multiple(
            decrypt_range_gens(),
            &pc_gens,
            &mut transcript,
            &proof.smudge_commitments[2 * params.degree()..]
                .iter()
                .map(|bytes| CompressedRistretto(*bytes))
                .collect::<Vec<_>>(),
            32,
        )
        .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;
    quotient_proof
        .verify_multiple(
            decrypt_range_gens(),
            &pc_gens,
            &mut transcript,
            &proof
                .quotient_commitments
                .iter()
                .map(|bytes| CompressedRistretto(*bytes))
                .collect::<Vec<_>>(),
            64,
        )
        .map_err(|_| QuorumError::InvalidDecryptShareProof { party: share.party })?;

    let mut relation = RistrettoPoint::default();
    accumulate_decrypt_relation(
        &mut transcript,
        share,
        params,
        &secret_points,
        None,
        &smudge_points,
        None,
        &product_points,
        None,
        &quotient_points,
        None,
        &mut relation,
        None,
    )?;
    let nonce = CompressedRistretto(proof.relation_nonce)
        .decompress()
        .ok_or(QuorumError::InvalidDecryptShareProof { party: share.party })?;
    let response = Option::<Scalar>::from(Scalar::from_canonical_bytes(proof.relation_response))
        .ok_or(QuorumError::InvalidDecryptShareProof { party: share.party })?;
    transcript.append_message(DECRYPT_SHARE_RELATION_DOMAIN, &proof.relation_nonce);
    let challenge = transcript_challenge_scalar(&mut transcript, b"relation-challenge");
    if response * pc_gens.B_blinding != nonce + challenge * relation {
        return Err(QuorumError::InvalidDecryptShareProof { party: share.party });
    }
    Ok(())
}

fn verify_decrypt_share_relations_parallel(
    shares: &[QuorumDecryptShare],
    setup: &VerifiedDkgTranscript,
    params: &BfvParams,
) -> Result<()> {
    let outcomes = shares
        .par_iter()
        .map(|share| verify_decrypt_share_relation(share, setup, params))
        .collect::<Vec<_>>();
    for outcome in outcomes {
        outcome?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn accumulate_decrypt_relation(
    transcript: &mut Transcript,
    share: &QuorumDecryptShare,
    params: &BfvParams,
    secret_points: &[RistrettoPoint],
    secret_blindings: Option<&[Scalar]>,
    smudge_points: &[RistrettoPoint],
    smudge_blindings: Option<&[Scalar]>,
    product_points: &[RistrettoPoint],
    product_blindings: Option<&[Scalar]>,
    quotient_points: &[RistrettoPoint],
    quotient_blindings: Option<&[Scalar]>,
    relation: &mut RistrettoPoint,
    mut relation_blinding: Option<&mut Scalar>,
) -> Result<()> {
    let degree = params.degree();
    let pc_gens = PedersenGens::default();
    let two64 = scalar_from_u128(1u128 << 64);
    transcript.append_message(b"relation-domain", DECRYPT_SHARE_RELATION_DOMAIN);
    // Fiat-Shamir challenges must remain byte-for-byte row-major.  Derive them
    // serially first, then use the immutable weights for both the canonical
    // relation fold below and the independent per-secret convolution.
    let mut equation_weights = Vec::with_capacity(params.moduli().len() * degree);
    for _ in params.moduli() {
        for _output in 0..degree {
            let first_weight = transcript_challenge_scalar(transcript, b"product-equation-weight");
            let second_weight = transcript_challenge_scalar(transcript, b"decrypt-equation-weight");
            equation_weights.push((first_weight, second_weight));
        }
    }

    // Each secret slot is independent.  Its inner loop preserves the exact
    // original output order, so dalek Scalar additions produce the identical
    // weight while Rayon spreads the O(R*N^2) work across host cores.
    let secret_weights = accumulate_secret_weights_parallel(
        &equation_weights,
        &share.ct.polys[1].rows,
        degree,
        secret_points.len(),
    )?;

    // These challenges and every point they weight are public.  Collapse the
    // verifier/prover's tens of thousands of independent variable-time scalar
    // multiplications into one dalek Pippenger MSM.  Challenge derivation stays
    // canonical and serial above; only the public linear-algebra evaluation is
    // batched.
    let smudge_complement_weights = (0..degree)
        .map(|_| transcript_challenge_scalar(transcript, b"smudge-complement-weight"))
        .collect::<Vec<_>>();
    let lambdas = params
        .moduli()
        .iter()
        .map(|&q| lagrange_at_zero(share.party, &share.opening.parties, q).map(Scalar::from))
        .collect::<Result<Vec<_>>>()?;
    let public_weights = build_public_decrypt_relation_weights(
        degree,
        share.smudge_bits,
        params.moduli(),
        &lambdas,
        &share.h,
        &equation_weights,
        &smudge_complement_weights,
        &secret_weights,
        smudge_points.len(),
        product_points.len(),
        quotient_points.len(),
        secret_points.len(),
    )?;
    *relation += evaluate_public_decrypt_relation_msm(
        &public_weights,
        smudge_points,
        product_points,
        quotient_points,
        secret_points,
        &pc_gens.B,
    );

    for (row_index, &q) in params.moduli().iter().enumerate() {
        let lambda = lambdas[row_index];
        let q_scalar = Scalar::from(q);
        for output in 0..degree {
            let (first_weight, second_weight) = equation_weights[row_index * degree + output];

            let smudge_low_index = output * 2;
            let smudge_high_index = 2 * degree + output * 2;
            let equation = row_index * degree + output;
            let quotient_index = equation * 2;
            if let (
                Some(smudge_blindings),
                Some(product_blindings),
                Some(quotient_blindings),
                Some(total),
            ) = (
                smudge_blindings,
                product_blindings,
                quotient_blindings,
                relation_blinding.as_deref_mut(),
            ) {
                let smudge_blinding = smudge_blindings[smudge_low_index]
                    + two64 * smudge_blindings[smudge_high_index];
                let first_quotient_blinding = quotient_blindings[quotient_index];
                let second_quotient_blinding = quotient_blindings[quotient_index + 1];
                *total += first_weight
                    * (-product_blindings[equation] - q_scalar * first_quotient_blinding);
                *total += second_weight
                    * (lambda * product_blindings[equation] + smudge_blinding
                        - q_scalar * second_quotient_blinding);
            }
        }
    }

    // Independent random batching for every exact interval-complement equation
    // C(smudge+B) + C(B-smudge) = C(2B).
    for (output, &weight) in smudge_complement_weights.iter().enumerate() {
        let low = output * 2;
        let high = 2 * degree + output * 2;
        if let Some(blindings) = smudge_blindings {
            if let Some(total) = relation_blinding.as_deref_mut() {
                let u_blinding = blindings[low] + two64 * blindings[high];
                let v_blinding = blindings[low + 1] + two64 * blindings[high + 1];
                *total += weight * (u_blinding + v_blinding);
            }
        }
    }

    for (index, &weight) in secret_weights.iter().enumerate() {
        if let (Some(blindings), Some(total)) = (secret_blindings, relation_blinding.as_deref_mut())
        {
            *total += weight * blindings[index];
        }
    }
    Ok(())
}

struct PublicDecryptRelationWeights {
    smudge: Vec<Scalar>,
    product: Vec<Scalar>,
    quotient: Vec<Scalar>,
    secret: Vec<Scalar>,
    generator: Scalar,
}

#[allow(clippy::too_many_arguments)]
fn build_public_decrypt_relation_weights(
    degree: usize,
    smudge_bits: u32,
    moduli: &[u64],
    lambdas: &[Scalar],
    h: &[Vec<u64>],
    equation_weights: &[(Scalar, Scalar)],
    smudge_complement_weights: &[Scalar],
    secret_weights: &[Scalar],
    smudge_point_count: usize,
    product_point_count: usize,
    quotient_point_count: usize,
    secret_point_count: usize,
) -> Result<PublicDecryptRelationWeights> {
    let equations = moduli
        .len()
        .checked_mul(degree)
        .ok_or(QuorumError::UnsupportedDecryptProofParameters)?;
    if degree == 0
        || smudge_bits >= 127
        || lambdas.len() != moduli.len()
        || h.len() != moduli.len()
        || h.iter().any(|row| row.len() != degree)
        || equation_weights.len() != equations
        || smudge_complement_weights.len() != degree
        || secret_weights.len() != equations
        || smudge_point_count != 4 * degree
        || product_point_count != equations
        || quotient_point_count < 2 * equations
        || secret_point_count != equations
    {
        return Err(QuorumError::ParamMismatch);
    }

    let two64 = scalar_from_u128(1u128 << 64);
    let bound = scalar_from_u128(1u128 << smudge_bits);
    let twice_bound = bound + bound;
    let quotient_offset = Scalar::from(DECRYPT_QUOTIENT_OFFSET);
    let mut weights = PublicDecryptRelationWeights {
        smudge: vec![Scalar::ZERO; smudge_point_count],
        product: vec![Scalar::ZERO; product_point_count],
        quotient: vec![Scalar::ZERO; quotient_point_count],
        secret: secret_weights.to_vec(),
        generator: Scalar::ZERO,
    };

    for (row_index, &q) in moduli.iter().enumerate() {
        let lambda = lambdas[row_index];
        let q_scalar = Scalar::from(q);
        for output in 0..degree {
            let equation = row_index * degree + output;
            let (first_weight, second_weight) = equation_weights[equation];
            let smudge_low = output * 2;
            let smudge_high = 2 * degree + output * 2;
            let quotient = equation * 2;

            weights.product[equation] += -first_weight + second_weight * lambda;
            weights.quotient[quotient] -= first_weight * q_scalar;
            weights.quotient[quotient + 1] -= second_weight * q_scalar;
            weights.smudge[smudge_low] += second_weight;
            weights.smudge[smudge_high] += second_weight * two64;
            weights.generator += first_weight * q_scalar * quotient_offset;
            weights.generator += second_weight
                * (q_scalar * quotient_offset - bound - Scalar::from(h[row_index][output]));
        }
    }

    for (output, &weight) in smudge_complement_weights.iter().enumerate() {
        let low = output * 2;
        let high = 2 * degree + output * 2;
        weights.smudge[low] += weight;
        weights.smudge[low + 1] += weight;
        weights.smudge[high] += weight * two64;
        weights.smudge[high + 1] += weight * two64;
        weights.generator -= weight * twice_bound;
    }
    Ok(weights)
}

fn evaluate_public_decrypt_relation_msm(
    weights: &PublicDecryptRelationWeights,
    smudge_points: &[RistrettoPoint],
    product_points: &[RistrettoPoint],
    quotient_points: &[RistrettoPoint],
    secret_points: &[RistrettoPoint],
    generator: &RistrettoPoint,
) -> RistrettoPoint {
    RistrettoPoint::vartime_multiscalar_mul(
        weights
            .smudge
            .iter()
            .chain(&weights.product)
            .chain(&weights.quotient)
            .chain(&weights.secret)
            .chain(std::iter::once(&weights.generator)),
        smudge_points
            .iter()
            .chain(product_points)
            .chain(quotient_points)
            .chain(secret_points)
            .chain(std::iter::once(generator)),
    )
}

/// Parallel form of the exact row-wise negacyclic integer convolution.  The
/// output is always canonical row-major order even though its independent
/// coefficients may complete in any scheduler order.
fn negacyclic_rows_i256_parallel(
    left_rows: &[Vec<u64>],
    right_rows: &[Vec<u64>],
    degree: usize,
) -> Result<Vec<I256>> {
    if degree == 0
        || left_rows.len() != right_rows.len()
        || left_rows.iter().any(|row| row.len() != degree)
        || right_rows.iter().any(|row| row.len() != degree)
    {
        return Err(QuorumError::ParamMismatch);
    }
    (0..left_rows.len() * degree)
        .into_par_iter()
        .map(|equation| {
            let row_index = equation / degree;
            let coefficient = equation % degree;
            negacyclic_coefficient_i256(&left_rows[row_index], &right_rows[row_index], coefficient)
        })
        .collect()
}

/// Parallelize the O(R*N^2) coefficient fold by final secret slot.  Each slot
/// still sums output contributions in the canonical increasing order.
fn accumulate_secret_weights_parallel(
    equation_weights: &[(Scalar, Scalar)],
    ciphertext_rows: &[Vec<u64>],
    degree: usize,
    secret_point_count: usize,
) -> Result<Vec<Scalar>> {
    let expected = ciphertext_rows
        .len()
        .checked_mul(degree)
        .ok_or(QuorumError::UnsupportedDecryptProofParameters)?;
    if degree == 0
        || expected != equation_weights.len()
        || expected != secret_point_count
        || ciphertext_rows.iter().any(|row| row.len() != degree)
    {
        return Err(QuorumError::ParamMismatch);
    }
    Ok((0..secret_point_count)
        .into_par_iter()
        .map(|slot| {
            let row_index = slot / degree;
            let secret_index = slot % degree;
            let mut total = Scalar::ZERO;
            for output in 0..degree {
                let (cipher_index, negative) = if output >= secret_index {
                    (output - secret_index, false)
                } else {
                    (degree + output - secret_index, true)
                };
                let first_weight = equation_weights[row_index * degree + output].0;
                let weight = first_weight * Scalar::from(ciphertext_rows[row_index][cipher_index]);
                if negative {
                    total -= weight;
                } else {
                    total += weight;
                }
            }
            total
        })
        .collect())
}

fn decrypt_share_proof_transcript(
    share: &QuorumDecryptShare,
    secret_commitments: &[[u8; 32]],
    params: &BfvParams,
) -> Result<Transcript> {
    let setup_digest = share
        .opening
        .vss_setup_digest
        .ok_or(QuorumError::VssTranscriptMismatch)?;
    let mut transcript = Transcript::new(DECRYPT_SHARE_PROOF_DOMAIN);
    transcript.append_message(b"setup", &setup_digest);
    transcript.append_message(b"opening", &opening_digest(&share.opening));
    transcript.append_message(b"ciphertext", &target_digest(&share.ct));
    transcript.append_u64(b"party", share.party as u64);
    transcript.append_u64(b"smudge-bits", share.smudge_bits as u64);
    transcript.append_u64(b"degree", params.degree() as u64);
    transcript.append_u64(b"moduli", params.moduli().len() as u64);
    for &q in params.moduli() {
        transcript.append_u64(b"q", q);
    }
    for row in &share.h {
        for &value in row {
            transcript.append_u64(b"h", value);
        }
    }
    transcript.append_u64(b"secret-commitments", secret_commitments.len() as u64);
    for commitment in secret_commitments {
        transcript.append_message(b"secret-commitment", commitment);
    }
    Ok(transcript)
}

fn negacyclic_coefficient_i256(left: &[u64], right: &[u64], output: usize) -> Result<I256> {
    if left.len() != right.len() || output >= left.len() {
        return Err(QuorumError::ParamMismatch);
    }
    let degree = left.len();
    let mut acc = I256::ZERO;
    for (left_index, &left_value) in left.iter().enumerate() {
        let (right_index, negative) = if output >= left_index {
            (output - left_index, false)
        } else {
            (degree + output - left_index, true)
        };
        let product = I256::from(left_value as u128 * right[right_index] as u128);
        acc = if negative {
            acc.checked_sub(product)
        } else {
            acc.checked_add(product)
        }
        .ok_or(QuorumError::UnsupportedDecryptProofParameters)?;
    }
    Ok(acc)
}

fn i256_to_i128(value: I256) -> Result<i128> {
    let narrowed = value.as_i128();
    if I256::from(narrowed) != value {
        return Err(QuorumError::UnsupportedDecryptProofParameters);
    }
    Ok(narrowed)
}

fn shift_signed_quotient(value: i128) -> Result<u64> {
    let value = i64::try_from(value).map_err(|_| QuorumError::UnsupportedDecryptProofParameters)?;
    if value >= 0 {
        DECRYPT_QUOTIENT_OFFSET
            .checked_add(value as u64)
            .ok_or(QuorumError::UnsupportedDecryptProofParameters)
    } else {
        DECRYPT_QUOTIENT_OFFSET
            .checked_sub(value.unsigned_abs())
            .ok_or(QuorumError::UnsupportedDecryptProofParameters)
    }
}

fn scalar_from_u128(value: u128) -> Scalar {
    let two32 = Scalar::from(1u64 << 32);
    Scalar::from(value as u64) + Scalar::from((value >> 64) as u64) * two32 * two32
}

fn transcript_challenge_scalar(transcript: &mut Transcript, label: &'static [u8]) -> Scalar {
    let mut wide = [0u8; 64];
    transcript.challenge_bytes(label, &mut wide);
    Scalar::from_bytes_mod_order_wide(&wide)
}

fn decompress_points(bytes: &[[u8; 32]], party: usize) -> Result<Vec<RistrettoPoint>> {
    bytes
        .iter()
        .map(|bytes| {
            CompressedRistretto(*bytes)
                .decompress()
                .ok_or(QuorumError::InvalidDecryptShareProof { party })
        })
        .collect()
}

fn authenticated_roster_digest(
    keygen: &QuorumKeygenSession,
    vss_setup_digest: Option<[u8; 32]>,
    ordered_public_keys: &[[u8; 32]],
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(AUTHENTICATED_ROSTER_DOMAIN);
    hash.update((keygen.n_parties() as u64).to_le_bytes());
    hash.update((keygen.threshold as u64).to_le_bytes());
    hash.update(keygen.base.crp_seed());
    hash_optional_digest(&mut hash, vss_setup_digest);
    hash.update((ordered_public_keys.len() as u64).to_le_bytes());
    for key in ordered_public_keys {
        hash.update(key);
    }
    hash.finalize().into()
}

fn authenticated_share_message(roster_digest: &[u8; 32], share: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(AUTHENTICATED_SHARE_DOMAIN);
    hash.update(roster_digest);
    hash.update((share.len() as u64).to_le_bytes());
    hash.update(share);
    hash.finalize().into()
}

fn opening_digest(opening: &QuorumOpeningSession) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(OPENING_SESSION_DOMAIN);
    hash.update((opening.keygen.n_parties() as u64).to_le_bytes());
    hash.update((opening.keygen.threshold as u64).to_le_bytes());
    hash.update(opening.keygen.base.crp_seed());
    hash.update(opening.nonce);
    hash_optional_digest(&mut hash, opening.vss_setup_digest);
    hash.update((opening.parties.len() as u64).to_le_bytes());
    for party in &opening.parties {
        hash.update((*party as u64).to_le_bytes());
    }
    hash.finalize().into()
}

fn target_digest(ct: &LeanCiphertext) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"fhegg/quorum-open-target/v1");
    hash.update(ct.plain_bound.to_le_bytes());
    hash.update(ct.to_fhe_bytes());
    hash.finalize().into()
}

fn ceil_log2(n: usize) -> Option<u32> {
    (n != 0).then(|| usize::BITS - (n - 1).leading_zeros())
}

fn push_byte_vectors(out: &mut Vec<u8>, values: &[[u8; 32]]) {
    out.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        out.extend_from_slice(value);
    }
}

fn take_byte_vectors(cursor: &mut WireCursor<'_>, expected: usize) -> Result<Vec<[u8; 32]>> {
    let count = cursor.usize()?;
    if count != expected {
        return Err(QuorumError::MalformedWire);
    }
    (0..count).map(|_| cursor.take::<32>()).collect()
}

struct WireCursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> WireCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N]> {
        let end = self
            .position
            .checked_add(N)
            .filter(|&end| end <= self.bytes.len())
            .ok_or(QuorumError::MalformedWire)?;
        let output = self.bytes[self.position..end]
            .try_into()
            .map_err(|_| QuorumError::MalformedWire)?;
        self.position = end;
        Ok(output)
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(u64::from_le_bytes(self.take::<8>()?))
            .map_err(|_| QuorumError::MalformedWire)
    }

    fn bytes(&mut self, length: usize) -> Result<&'a [u8]> {
        let end = self
            .position
            .checked_add(length)
            .filter(|&end| end <= self.bytes.len())
            .ok_or(QuorumError::MalformedWire)?;
        let output = &self.bytes[self.position..end];
        self.position = end;
        Ok(output)
    }

    fn finished(&self) -> bool {
        self.position == self.bytes.len()
    }
}

#[cfg(test)]
mod vss_tests {
    use super::*;

    #[test]
    fn parallel_exact_convolution_preserves_canonical_row_order() {
        let left = vec![
            vec![1, 3, 5, 7, 11, 13, 17, 19],
            vec![23, 29, 31, 37, 41, 43, 47, 53],
        ];
        let right = vec![
            vec![59, 61, 67, 71, 73, 79, 83, 89],
            vec![97, 101, 103, 107, 109, 113, 127, 131],
        ];
        let expected = left
            .iter()
            .zip(&right)
            .flat_map(|(left, right)| {
                (0..left.len()).map(move |output| {
                    negacyclic_coefficient_i256(left, right, output).expect("valid coefficient")
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(
            negacyclic_rows_i256_parallel(&left, &right, 8).unwrap(),
            expected
        );
    }

    #[test]
    fn parallel_secret_weight_fold_is_byte_identical_to_nested_loop() {
        let degree = 8;
        let ciphertext_rows = vec![
            vec![2, 3, 5, 7, 11, 13, 17, 19],
            vec![23, 29, 31, 37, 41, 43, 47, 53],
        ];
        let equation_weights = (0..ciphertext_rows.len() * degree)
            .map(|i| (Scalar::from((i + 1) as u64), Scalar::from((100 + i) as u64)))
            .collect::<Vec<_>>();
        let mut expected = vec![Scalar::ZERO; ciphertext_rows.len() * degree];
        for row_index in 0..ciphertext_rows.len() {
            for output in 0..degree {
                let first_weight = equation_weights[row_index * degree + output].0;
                for secret_index in 0..degree {
                    let (cipher_index, negative) = if output >= secret_index {
                        (output - secret_index, false)
                    } else {
                        (degree + output - secret_index, true)
                    };
                    let weight =
                        first_weight * Scalar::from(ciphertext_rows[row_index][cipher_index]);
                    let slot = row_index * degree + secret_index;
                    if negative {
                        expected[slot] -= weight;
                    } else {
                        expected[slot] += weight;
                    }
                }
            }
        }
        let parallel = accumulate_secret_weights_parallel(
            &equation_weights,
            &ciphertext_rows,
            degree,
            expected.len(),
        )
        .unwrap();
        assert_eq!(
            parallel.iter().map(Scalar::to_bytes).collect::<Vec<_>>(),
            expected.iter().map(Scalar::to_bytes).collect::<Vec<_>>()
        );
    }

    #[test]
    fn public_relation_msm_is_byte_identical_to_legacy_equation_fold() {
        fn point(index: u64) -> RistrettoPoint {
            let mut uniform = [0u8; 64];
            uniform[..8].copy_from_slice(&index.to_le_bytes());
            uniform[32..40].copy_from_slice(&index.wrapping_mul(0x9e37_79b9).to_le_bytes());
            RistrettoPoint::from_uniform_bytes(&uniform)
        }

        let degree = 3;
        let smudge_bits = 5;
        let moduli = [17, 19];
        let lambdas = [Scalar::from(3u64), Scalar::from(7u64)];
        let h = vec![vec![2, 5, 11], vec![3, 7, 13]];
        let equation_weights = (0..moduli.len() * degree)
            .map(|i| {
                (
                    Scalar::from((i * 17 + 5) as u64),
                    Scalar::from((i * 29 + 11) as u64),
                )
            })
            .collect::<Vec<_>>();
        let complement_weights = [
            Scalar::from(101u64),
            Scalar::from(103u64),
            Scalar::from(107u64),
        ];
        let secret_weights = (0..moduli.len() * degree)
            .map(|i| Scalar::from((i * 31 + 13) as u64))
            .collect::<Vec<_>>();
        let smudge_points = (0..4 * degree)
            .map(|i| point(1 + i as u64))
            .collect::<Vec<_>>();
        let product_points = (0..moduli.len() * degree)
            .map(|i| point(101 + i as u64))
            .collect::<Vec<_>>();
        // Include padded quotient commitments: the builder must give their
        // unused tail exactly zero weight.
        let quotient_points = (0..16).map(|i| point(201 + i as u64)).collect::<Vec<_>>();
        let secret_points = (0..moduli.len() * degree)
            .map(|i| point(301 + i as u64))
            .collect::<Vec<_>>();
        let generator = point(999);

        let weights = build_public_decrypt_relation_weights(
            degree,
            smudge_bits,
            &moduli,
            &lambdas,
            &h,
            &equation_weights,
            &complement_weights,
            &secret_weights,
            smudge_points.len(),
            product_points.len(),
            quotient_points.len(),
            secret_points.len(),
        )
        .unwrap();
        let batched = evaluate_public_decrypt_relation_msm(
            &weights,
            &smudge_points,
            &product_points,
            &quotient_points,
            &secret_points,
            &generator,
        );

        let two64 = scalar_from_u128(1u128 << 64);
        let bound = scalar_from_u128(1u128 << smudge_bits);
        let twice_bound = bound + bound;
        let quotient_offset = Scalar::from(DECRYPT_QUOTIENT_OFFSET);
        let mut legacy = RistrettoPoint::default();
        for (row_index, &q) in moduli.iter().enumerate() {
            let q_scalar = Scalar::from(q);
            for output in 0..degree {
                let equation = row_index * degree + output;
                let (first_weight, second_weight) = equation_weights[equation];
                let low = output * 2;
                let high = 2 * degree + output * 2;
                let quotient = equation * 2;
                let smudge = smudge_points[low] + two64 * smudge_points[high];
                legacy += first_weight
                    * (-product_points[equation]
                        - q_scalar * (quotient_points[quotient] - quotient_offset * generator));
                legacy += second_weight
                    * (lambdas[row_index] * product_points[equation] + smudge
                        - bound * generator
                        - Scalar::from(h[row_index][output]) * generator
                        - q_scalar * (quotient_points[quotient + 1] - quotient_offset * generator));
            }
        }
        for (output, &weight) in complement_weights.iter().enumerate() {
            let low = output * 2;
            let high = 2 * degree + output * 2;
            let u = smudge_points[low] + two64 * smudge_points[high];
            let v = smudge_points[low + 1] + two64 * smudge_points[high + 1];
            legacy += weight * (u + v - twice_bound * generator);
        }
        for (&weight, point) in secret_weights.iter().zip(&secret_points) {
            legacy += weight * point;
        }

        assert_eq!(batched.compress().to_bytes(), legacy.compress().to_bytes());
    }

    #[test]
    fn public_vss_commitment_wire_is_canonical_and_digest_checked() {
        let params = BfvParams::fold_set();
        let session = QuorumKeygenSession::from_seed(3, 2, [0x90; 32]).unwrap();
        let bundle = deal(&session, 0, &params).unwrap();
        let wire = bundle.vss_commitment.to_wire_bytes();
        assert_eq!(
            DealerVssCommitment::from_wire_bytes(&wire, &params).unwrap(),
            bundle.vss_commitment
        );
        let mut tampered = wire;
        *tampered.last_mut().unwrap() ^= 1;
        assert_eq!(
            DealerVssCommitment::from_wire_bytes(&tampered, &params),
            Err(QuorumError::VssTranscriptMismatch)
        );
    }

    #[test]
    fn bivariate_vss_refuses_a_row_that_no_longer_opens_its_public_commitment() {
        let params = BfvParams::fold_set();
        let session = QuorumKeygenSession::from_seed(3, 2, [0x91; 32]).unwrap();
        let mut bundle = deal(&session, 0, &params).unwrap();
        bundle.private[1].vss_salt[0] ^= 1;
        assert!(matches!(
            bundle.verify(&params),
            Err(QuorumError::VssCommitmentMismatch {
                dealer: 0,
                recipient: 1
            })
        ));
    }

    #[test]
    fn bivariate_cross_check_catches_a_recommitted_but_inconsistent_row() {
        let params = BfvParams::fold_set();
        let session = QuorumKeygenSession::from_seed(3, 2, [0x92; 32]).unwrap();
        let mut bundle = deal(&session, 0, &params).unwrap();

        // A malicious dealer may choose a fresh hash commitment, so exercise
        // that stronger attack rather than relying on hash mismatch alone.
        let q = params.moduli()[0];
        bundle.private[0].vss_row_coefficients[1][0][0] =
            add_mod(bundle.private[0].vss_row_coefficients[1][0][0], 1, q);
        let public_key_digest = bundle.vss_commitment.public_key_digest;
        bundle.vss_commitment.row_commitments[0] = vss_row_commitment_digest(
            &session,
            0,
            0,
            &public_key_digest,
            &bundle.private[0].vss_salt,
            &bundle.private[0].vss_row_coefficients,
            &bundle.private[0].vss_error_row_coefficients,
            &params,
        );
        bundle.vss_commitment.digest = dealer_vss_commitment_digest(
            &session,
            0,
            &public_key_digest,
            &bundle.vss_commitment.row_commitments,
            &bundle.vss_commitment.linear_commitments,
        );

        assert!(matches!(
            bundle.verify(&params),
            Err(QuorumError::VssInconsistentRows {
                dealer: 0,
                left: 0,
                right: 1
            })
        ));
    }

    #[test]
    fn public_bfv_image_catches_consistent_recommitted_rows_off_the_rlwe_relation() {
        let params = BfvParams::fold_set();
        let session = QuorumKeygenSession::from_seed(3, 2, [0x95; 32]).unwrap();
        let mut bundle = deal(&session, 0, &params).unwrap();
        let q = params.moduli()[0];

        // Add x*y to the SECRET bivariate polynomial by updating every
        // recipient's y-coefficient. All pairwise intersections still agree,
        // and the malicious dealer recommits every exact row. The unchanged
        // public C_11=-a*s_11+e_11 image is the independent check that bites.
        for share in &mut bundle.private {
            let x = share.recipient as u64 + 1;
            share.vss_row_coefficients[1][0][0] =
                add_mod(share.vss_row_coefficients[1][0][0], x, q);
            let recipient = share.recipient;
            bundle.vss_commitment.row_commitments[recipient] = vss_row_commitment_digest(
                &session,
                0,
                recipient,
                &bundle.vss_commitment.public_key_digest,
                &share.vss_salt,
                &share.vss_row_coefficients,
                &share.vss_error_row_coefficients,
                &params,
            );
        }
        bundle.vss_commitment.digest = dealer_vss_commitment_digest(
            &session,
            0,
            &bundle.vss_commitment.public_key_digest,
            &bundle.vss_commitment.row_commitments,
            &bundle.vss_commitment.linear_commitments,
        );

        assert!(matches!(
            bundle.verify(&params),
            Err(QuorumError::VssPublicImageMismatch {
                dealer: 0,
                recipient: 0
            })
        ));
    }

    #[test]
    fn verified_setup_digest_reaches_party_opening_and_identity_roster() {
        let params = BfvParams::fold_set();
        let session = QuorumKeygenSession::from_seed(3, 2, [0x93; 32]).unwrap();
        let bundles = (0..3)
            .map(|dealer| {
                deal(&session, dealer, &params)
                    .unwrap()
                    .verify(&params)
                    .unwrap()
            })
            .collect();
        let (collective, transcript, mut assemblies) =
            finish_verified_keygen(&session, bundles, &params)
                .unwrap()
                .into_parts();
        // The collective key is live, not a transcript-only stand-in, and the
        // verified transcript itself binds its exact serialized identity.
        assert_eq!(
            transcript.collective_key_digest(),
            verified_dkg_collective_key_digest(&collective)
        );
        let mut substituted_key_digest = transcript.collective_key_digest();
        substituted_key_digest[0] ^= 1;
        assert_ne!(
            transcript.digest(),
            vss_setup_transcript_digest(
                &session,
                &transcript.dealer_commitment_digests,
                &transcript.party_secret_commitments,
                substituted_key_digest,
                &params,
                None,
            )
        );
        assert!(transcript.q0_share_commitment_context().is_none());

        let mut parties = assemblies
            .drain(..)
            .enumerate()
            .map(|(party, assembly)| {
                QuorumParty::assemble_verified(&session, party, assembly, &transcript, &params)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let contributions = parties
            .iter_mut()
            .map(|party| {
                party
                    .prepare_experimental_q0_share_commitment(&transcript, &params, &mut OsRng)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let anchored_transcript = transcript
            .clone()
            .finalize_experimental_q0_share_commitments(&contributions, &params)
            .unwrap();
        assert_eq!(
            anchored_transcript.q0_share_commitment_context(),
            Some(transcript.digest())
        );

        // Split-view tooth: replace another party's contribution with a
        // well-shaped commitment under the correct session/slot key.  Local
        // party-0 inclusion is identical in both finalized transcripts, so
        // neither transcript can claim public ceremony authority until the
        // contribution round is identity-signed and broadcast-consistent.
        let mut split_contributions = contributions.clone();
        let split_key = ExperimentalBfvQ0ShareCommitmentKey::derive(
            transcript.digest(),
            transcript.collective_key_digest(),
            1,
            q0_share_commitment_seed(transcript.digest()),
        )
        .unwrap();
        let split_opening =
            ExperimentalBfvQ0ShareOpening::randomized(&vec![0u64; BFV_Q0_DEGREE], &mut OsRng)
                .unwrap();
        split_contributions[1].commitment = split_key.commit(&split_opening).unwrap();
        let split_transcript = transcript
            .clone()
            .finalize_experimental_q0_share_commitments(&split_contributions, &params)
            .unwrap();
        assert_ne!(split_transcript.digest(), anchored_transcript.digest());
        assert_eq!(
            split_transcript.q0_share_commitment(0),
            anchored_transcript.q0_share_commitment(0)
        );
        assert_eq!(
            split_transcript.require_experimental_q0_public_ceremony_authority(),
            Err(QuorumError::ExperimentalQ0CeremonyUnauthenticated)
        );
        assert_eq!(
            anchored_transcript.require_experimental_q0_public_ceremony_authority(),
            Err(QuorumError::ExperimentalQ0CeremonyUnauthenticated)
        );

        // Local typestate canary only: an honest party retaining its exact
        // VSS-assembled row refuses an all-zero opening under the unchanged
        // finalized contribution.  Public/malicious-party equality still
        // requires the planned HidingFRI cross-commitment proof.
        parties[2].q0_share_opening = Some(
            ExperimentalBfvQ0ShareOpening::randomized(&vec![0u64; BFV_Q0_DEGREE], &mut OsRng)
                .unwrap(),
        );
        assert!(matches!(
            parties[2].bind_experimental_q0_share_commitment(&anchored_transcript, &params),
            Err(QuorumError::VssTranscriptMismatch)
        ));
        parties[0]
            .bind_experimental_q0_share_commitment(&anchored_transcript, &params)
            .unwrap();
        let party = parties.remove(0);
        assert_eq!(party.vss_setup_digest(), Some(anchored_transcript.digest()));
        let opening = QuorumOpeningSession::new_verified(
            session.clone(),
            &anchored_transcript,
            [0x94; 32],
            vec![0, 1],
        )
        .unwrap();
        assert_eq!(
            opening.vss_setup_digest(),
            Some(anchored_transcript.digest())
        );

        let keys = (0..3)
            .map(|i| SigningKey::from_bytes(&[0xa0 + i as u8; 32]))
            .collect::<Vec<_>>();
        let verified_roster = AuthenticatedQuorumRoster::new_verified(
            session.clone(),
            &anchored_transcript,
            keys.iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
        )
        .unwrap();
        let legacy_roster = AuthenticatedQuorumRoster::new(
            session,
            keys.iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
        )
        .unwrap();
        assert_ne!(verified_roster.digest(), legacy_roster.digest());
    }

    #[test]
    fn authenticated_encrypted_orders_gate_real_game_asset_settlement_crypto_tooth() {
        use fhe::bfv::Plaintext;
        use fhe_traits::{FheEncoder, FheEncrypter};
        use std::time::Instant;

        let total_started = Instant::now();
        let params = BfvParams::fold_set();
        let session = QuorumKeygenSession::from_seed(3, 2, [0xb3; 32]).unwrap();
        let verified_dealers = (0..3)
            .map(|dealer| {
                deal(&session, dealer, &params)
                    .unwrap()
                    .verify(&params)
                    .unwrap()
            })
            .collect();
        let (collective, transcript, assemblies) =
            finish_verified_keygen(&session, verified_dealers, &params)
                .unwrap()
                .into_parts();
        let keys = (0..3)
            .map(|party| SigningKey::from_bytes(&[0xc0 + party as u8; 32]))
            .collect::<Vec<_>>();
        let roster = AuthenticatedQuorumRoster::new_verified(
            session.clone(),
            &transcript,
            keys.iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
        )
        .unwrap();
        let mut parties = assemblies
            .into_iter()
            .enumerate()
            .map(|(party, assembly)| {
                QuorumParty::assemble_verified(&session, party, assembly, &transcript, &params)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        eprintln!(
            "fhegg verified-share profile: dkg={:?}",
            total_started.elapsed()
        );

        let mut slots = vec![0u64; params.degree()];
        slots[..4].copy_from_slice(&[7, 19, 31, 43]);
        let plaintext = Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).unwrap();
        let mut rng = rand_09::rng();
        let ciphertext = collective.pk.try_encrypt(&plaintext, &mut rng).unwrap();
        let ciphertext = LeanCiphertext::from_fhe_bytes(
            &ciphertext.to_bytes(),
            params.moduli(),
            params.degree(),
            43,
        )
        .unwrap();
        let opening =
            QuorumOpeningSession::new_verified(session, &transcript, [0xb4; 32], vec![0, 1])
                .unwrap();
        let prove_started = Instant::now();
        let shares = partial_decrypt_quorum_parallel(
            &mut parties,
            &opening,
            &ciphertext,
            MIN_SMUDGE_BITS,
            &params,
        )
        .unwrap();
        eprintln!(
            "fhegg verified-share profile: prove-two={:?}",
            prove_started.elapsed()
        );
        assert!(shares.iter().all(|share| share.proof.is_some()));
        let framed = shares
            .iter()
            .map(|share| {
                roster
                    .sign_share(share.clone(), &keys[share.party])
                    .unwrap()
                    .to_wire_bytes()
            })
            .collect::<Vec<_>>();
        let verify_started = Instant::now();
        let mut combiner = AuthenticatedQuorumCombiner::new(roster.clone());
        let opened = combiner
            .combine_framed(&opening, &ciphertext, &framed, &params)
            .unwrap();
        eprintln!(
            "fhegg verified-share profile: parallel-verify-two={:?}",
            verify_started.elapsed()
        );
        assert_eq!(&opened[..4], &[7, 19, 31, 43]);
        // A same-process, same-fixture reference makes the scheduling gain
        // measurable without comparing unlike hosts or historical builds.
        // Run it second so any shared code/data warmth favors the serial
        // reference rather than the production parallel path.
        let serial_verify_started = Instant::now();
        for share in &shares {
            verify_decrypt_share_relation(share, &transcript, &params).unwrap();
        }
        eprintln!(
            "fhegg verified-share profile: serial-verify-two={:?}",
            serial_verify_started.elapsed()
        );

        let mut forged = shares.clone();
        for share in &mut forged {
            share.proof.as_mut().unwrap().relation_response[0] ^= 1;
        }
        let mut forged_framed = forged
            .iter()
            .map(|share| {
                roster
                    .sign_share(share.clone(), &keys[share.party])
                    .unwrap()
                    .to_wire_bytes()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            AuthenticatedQuorumCombiner::new(roster.clone()).combine_framed(
                &opening,
                &ciphertext,
                &forged_framed,
                &params,
            ),
            Err(QuorumError::InvalidDecryptShareProof {
                party: shares[0].party
            })
        );
        *forged_framed[0].last_mut().unwrap() ^= 1;
        assert_eq!(
            AuthenticatedQuorumCombiner::new(roster).combine_framed(
                &opening,
                &ciphertext,
                &forged_framed,
                &params,
            ),
            Err(QuorumError::InvalidSignature {
                party: shares[0].party
            })
        );
        eprintln!(
            "fhegg verified-share profile: total={:?}",
            total_started.elapsed()
        );
    }
}

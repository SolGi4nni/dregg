//! Distributed input preparation for the exact private-book/BFV proof.
//!
//! The existing `private_book_bfv_zk` prover receives all four orders, the
//! eight root-blinding felts, and all four BFV encryption seeds in one process.
//! This module removes that *input collection* requirement without pretending
//! that Bulletproofs itself has become distributed.
//!
//! Each of the four order owners expands only its own seed into the exact
//! phase-one base inputs used by the current relation:
//!
//! `kind || quantity || u[degree] || e1[degree] || e2[degree] || root_blind[8]`.
//!
//! Owner zero supplies the book's eight canonical root-blinding felts; the
//! other owners' root-blinding lanes are fixed to zero.  Every owner n-of-n
//! additively shares that vector over the Ristretto scalar field among the
//! configured proof workers.  A vector Pedersen commitment is made in the
//! owner's own Bulletproof generator namespace.  The public equality
//!
//! `owner_commitment = sum(worker_share_commitments)`
//!
//! binds every accepted private packet to one owner vector while revealing no
//! vector coordinate.  Each recipient locally verifies its opening and signs
//! an acknowledgement.  A public coordinator can then issue a canonical
//! certificate only after all four dealings and all owner/worker
//! acknowledgements are present.  The session binds the exact public
//! `private_book_relation_digest`, a fresh ceremony nonce, both ordered
//! rosters, and this fixed witness layout.
//!
//! # Exact achieved privacy
//!
//! A coordinator or certificate verifier sees only perfectly hiding vector
//! Pedersen commitments, public identities, and signatures.  Any strict subset
//! of the proof workers has information-theoretically uniform additive shares
//! of every owner's vector.  Thus no single worker learns an order or BFV
//! randomness, and no owner is asked for another owner's order.  Share masks
//! are domain-separated by session, owner, recipient, coordinate, and purpose,
//! so accidentally restarting the same CSPRNG stream in a later ceremony does
//! not let one worker cancel repeated masks to recover order deltas.  This
//! assumes distinct owners are actually operated by distinct principals and
//! that the private packets use a confidential authenticated transport; this
//! module intentionally gives private packets no wire codec.
//!
//! # What this deliberately does not claim
//!
//! The certificate is not an R1CS proof and does not prove that the committed
//! hidden values satisfy the Poseidon root or BFV equations.  Worker
//! acknowledgements authenticate the local commitment-opening check; they are
//! not proofs of correct MPC execution.  A production completion must make a
//! distributed R1CS prover consume the returned `PreparedWitnessShare`s and
//! prove equality between its secret-shared circuit inputs and these public
//! commitments, or compose per-owner BFV proofs with a distributed root proof.
//! The current monolithic `prove_private_book_bfv_zk` API must not be called by
//! reconstructing these shares at a coordinator.
//!
//! The ceremony commits fhe.rs's actual variance-10 CBD coefficients, whose
//! support is `[-20,20]`.  The monolithic reference circuit's bounded-short
//! range contains that full support, but still does not prove exact seeded
//! sampler-image membership; a future distributed backend must preserve that
//! distinction rather than upgrading an authenticated share to a ZK claim.

use std::collections::HashSet;
use std::fmt;
use std::iter;
use std::sync::LazyLock;

use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use rand::{CryptoRng, RngCore};
use rand_09::rngs::StdRng as StdRng09;
use rand_09::{RngCore as RngCore09, SeedableRng as SeedableRng09};

/// Fixed order count of the deployed private N4K4 relation.
pub const ORDER_COUNT: usize = 4;
/// Fixed price count; order kinds are bid-0..3 followed by ask-0..3.
pub const PRICE_COUNT: usize = 4;
/// Ring degree of the deployed BFV fold parameter set.
pub const BFV_DEGREE: usize = 4096;
/// Number of root-blinding BabyBear felts in the exact private statement.
pub const ROOT_BLINDING_WIDTH: usize = 8;
/// fhe.rs CBD variance pinned by the exact Bulletproof relation.
pub const BFV_VARIANCE: usize = 10;
/// Exact support bound of fhe.rs's CBD sampler: two `2*variance`-bit
/// popcounts are subtracted, so coefficients lie in `[-2v, 2v]`.
pub const BFV_SHORT_ABS_BOUND: usize = 2 * BFV_VARIANCE;
/// BabyBear modulus used for canonical private-root blinding lanes.
pub const BABYBEAR_MODULUS: u32 = 2_013_265_921;
/// Maximum supported distributed proof-worker roster.
pub const MAX_WORKERS: usize = 8;
/// Exact production width of one owner's base input vector.
pub const LOCAL_WITNESS_WIDTH: usize = 2 + 3 * BFV_DEGREE + ROOT_BLINDING_WIDTH;

const SESSION_DOMAIN: &str = "fhegg/private-book-distributed-input/session/v1";
const DEAL_DOMAIN: &str = "fhegg/private-book-distributed-input/deal/v1";
const SHARE_MASK_DOMAIN: &str = "fhegg/private-book-distributed-input/share-mask/v1";
const DEAL_SIGNATURE_DOMAIN: &[u8] = b"fhegg/private-book-distributed-input/deal-signature/v1";
const ACK_SIGNATURE_DOMAIN: &[u8] = b"fhegg/private-book-distributed-input/ack-signature/v1";
const CERTIFICATE_DOMAIN: &str = "fhegg/private-book-distributed-input/certificate/v1";
const CHECKSUM_DOMAIN: &str = "fhegg/private-book-distributed-input/checksum/v1";
const LAYOUT_ID: &[u8] = b"FHEGG-PB-BFV-DISTRIBUTED-BASE-INPUT-N4K4-V1";
const CERTIFICATE_MAGIC: &[u8; 8] = b"FHPDI001";

static PRODUCTION_GENS: LazyLock<BulletproofGens> =
    LazyLock::new(|| BulletproofGens::new(LOCAL_WITNESS_WIDTH, ORDER_COUNT));

/// Fail-closed protocol errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DistributedInputError {
    InvalidSession(&'static str),
    InvalidWitness(&'static str),
    PartyOutOfRange,
    SigningKeyMismatch,
    SessionMismatch,
    DealerMismatch,
    RecipientMismatch,
    DuplicateDealer,
    DuplicateAcknowledgement,
    MissingDealers,
    MissingAcknowledgements,
    CommitmentMismatch,
    InvalidCommitment,
    InvalidSignature,
    MalformedCertificate,
    CertificateDigestMismatch,
}

impl fmt::Display for DistributedInputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSession(reason) => {
                write!(f, "invalid distributed-input session: {reason}")
            }
            Self::InvalidWitness(reason) => write!(f, "invalid local proof witness: {reason}"),
            Self::PartyOutOfRange => write!(f, "distributed-input party index is out of range"),
            Self::SigningKeyMismatch => write!(f, "signing key does not match the session roster"),
            Self::SessionMismatch => write!(f, "message belongs to another ceremony session"),
            Self::DealerMismatch => write!(f, "private share names a different dealer"),
            Self::RecipientMismatch => write!(f, "private share names a different recipient"),
            Self::DuplicateDealer => write!(f, "dealer contribution was already accepted"),
            Self::DuplicateAcknowledgement => {
                write!(f, "worker acknowledgement was already accepted")
            }
            Self::MissingDealers => write!(f, "not all four owner dealings are present"),
            Self::MissingAcknowledgements => {
                write!(f, "not every worker acknowledged every owner dealing")
            }
            Self::CommitmentMismatch => write!(f, "private share does not open its commitment"),
            Self::InvalidCommitment => write!(f, "public vector commitment is not canonical"),
            Self::InvalidSignature => write!(f, "distributed-input signature is invalid"),
            Self::MalformedCertificate => write!(f, "malformed distributed-input certificate"),
            Self::CertificateDigestMismatch => {
                write!(f, "distributed-input certificate digest mismatch")
            }
        }
    }
}

impl std::error::Error for DistributedInputError {}

type Result<T> = std::result::Result<T, DistributedInputError>;

/// Private order side used to derive the exact hidden kind code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateSide {
    Bid,
    Ask,
}

/// Public configuration for one distributed input-preparation ceremony.
///
/// `relation_digest` must be the output of the existing exact
/// `private_book_relation_digest` over the statement, four ciphertexts, BFV
/// parameters, and collective key.  The fresh nonce prevents a valid dealing
/// for one proof attempt from becoming a replayable input to another.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedWitnessSession {
    relation_digest: [u8; 32],
    ceremony_nonce: [u8; 32],
    owner_keys: [[u8; 32]; ORDER_COUNT],
    worker_keys: Vec<[u8; 32]>,
    degree: usize,
    digest: [u8; 32],
}

impl DistributedWitnessSession {
    /// Construct the exact production N4K4/degree-4096 ceremony.
    pub fn new(
        relation_digest: [u8; 32],
        ceremony_nonce: [u8; 32],
        owner_keys: [[u8; 32]; ORDER_COUNT],
        worker_keys: Vec<[u8; 32]>,
    ) -> Result<Self> {
        Self::new_inner(
            relation_digest,
            ceremony_nonce,
            owner_keys,
            worker_keys,
            BFV_DEGREE,
        )
    }

    #[cfg(test)]
    pub(crate) fn new_for_test(
        relation_digest: [u8; 32],
        ceremony_nonce: [u8; 32],
        owner_keys: [[u8; 32]; ORDER_COUNT],
        worker_keys: Vec<[u8; 32]>,
        degree: usize,
    ) -> Result<Self> {
        Self::new_inner(
            relation_digest,
            ceremony_nonce,
            owner_keys,
            worker_keys,
            degree,
        )
    }

    fn new_inner(
        relation_digest: [u8; 32],
        ceremony_nonce: [u8; 32],
        owner_keys: [[u8; 32]; ORDER_COUNT],
        worker_keys: Vec<[u8; 32]>,
        degree: usize,
    ) -> Result<Self> {
        if ceremony_nonce == [0; 32] {
            return Err(DistributedInputError::InvalidSession(
                "ceremony nonce must be fresh and nonzero",
            ));
        }
        if !(2..=MAX_WORKERS).contains(&worker_keys.len()) {
            return Err(DistributedInputError::InvalidSession(
                "proof-worker roster must contain 2..=8 parties",
            ));
        }
        if degree == 0 || degree > BFV_DEGREE {
            return Err(DistributedInputError::InvalidSession(
                "BFV degree is outside the protocol bounds",
            ));
        }
        let mut seen = HashSet::with_capacity(ORDER_COUNT + worker_keys.len());
        for key in owner_keys.iter().chain(worker_keys.iter()) {
            let verifying = VerifyingKey::from_bytes(key).map_err(|_| {
                DistributedInputError::InvalidSession("roster contains an invalid Ed25519 key")
            })?;
            if verifying.is_weak() || !seen.insert(*key) {
                return Err(DistributedInputError::InvalidSession(
                    "roster keys must be strong and globally distinct",
                ));
            }
        }
        let digest = session_digest(
            &relation_digest,
            &ceremony_nonce,
            &owner_keys,
            &worker_keys,
            degree,
        );
        Ok(Self {
            relation_digest,
            ceremony_nonce,
            owner_keys,
            worker_keys,
            degree,
            digest,
        })
    }

    /// Complete session digest carried by every public and private message.
    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Exact public BFV/private-root relation digest bound by the ceremony.
    pub const fn relation_digest(&self) -> [u8; 32] {
        self.relation_digest
    }

    /// Fresh caller-supplied proof-attempt nonce.
    pub const fn ceremony_nonce(&self) -> [u8; 32] {
        self.ceremony_nonce
    }

    /// Number of distributed proof workers.
    pub fn n_workers(&self) -> usize {
        self.worker_keys.len()
    }

    /// Ring degree encoded in the witness layout.
    pub const fn degree(&self) -> usize {
        self.degree
    }

    /// Width of one owner's exact base witness vector.
    pub const fn local_witness_width(&self) -> usize {
        2 + 3 * self.degree + ROOT_BLINDING_WIDTH
    }

    fn owner_key(&self, owner: usize) -> Option<[u8; 32]> {
        self.owner_keys.get(owner).copied()
    }

    pub(crate) fn worker_key(&self, worker: usize) -> Option<[u8; 32]> {
        self.worker_keys.get(worker).copied()
    }
}

/// One owner's exact local base witness.
///
/// The type intentionally has no `Clone`, `Debug`, or wire codec.  It can be
/// expanded directly from the same deterministic BFV seed used for that
/// owner's ciphertext, without any process receiving the other three seeds.
pub struct LocalOrderWitness {
    session_digest: [u8; 32],
    owner: usize,
    values: Vec<Scalar>,
}

impl LocalOrderWitness {
    /// Expand one local order and BFV seed into the exact short vectors used by
    /// the existing proof relation.  Only owner zero may supply the root
    /// blinding; all other owners have canonical zero lanes there.
    pub fn from_seed(
        session: &DistributedWitnessSession,
        owner: usize,
        side: PrivateSide,
        limit: u8,
        quantity: u8,
        seed: [u8; 32],
        root_blinding: Option<[u32; ROOT_BLINDING_WIDTH]>,
    ) -> Result<Self> {
        if owner >= ORDER_COUNT {
            return Err(DistributedInputError::PartyOutOfRange);
        }
        if limit as usize >= PRICE_COUNT || quantity > 15 {
            return Err(DistributedInputError::InvalidWitness(
                "order is outside the fixed N4K4 range",
            ));
        }
        if owner == 0 {
            let blinding = root_blinding.ok_or(DistributedInputError::InvalidWitness(
                "owner zero must supply the eight root-blinding felts",
            ))?;
            if blinding.iter().any(|&lane| lane >= BABYBEAR_MODULUS) {
                return Err(DistributedInputError::InvalidWitness(
                    "root blinding is not a canonical BabyBear vector",
                ));
            }
        } else if root_blinding.is_some() {
            return Err(DistributedInputError::InvalidWitness(
                "only owner zero carries the book root blinding",
            ));
        }

        let kind = limit as u64
            + match side {
                PrivateSide::Bid => 0,
                PrivateSide::Ask => PRICE_COUNT as u64,
            };
        let mut rng = StdRng09::from_seed(seed);
        let u = sample_cbd(session.degree, BFV_VARIANCE, &mut rng)?;
        let e1 = sample_cbd(session.degree, BFV_VARIANCE, &mut rng)?;
        let e2 = sample_cbd(session.degree, BFV_VARIANCE, &mut rng)?;

        let mut values = Vec::with_capacity(session.local_witness_width());
        values.push(Scalar::from(kind));
        values.push(Scalar::from(u64::from(quantity)));
        values.extend(u.into_iter().map(signed_scalar));
        values.extend(e1.into_iter().map(signed_scalar));
        values.extend(e2.into_iter().map(signed_scalar));
        values.extend(
            root_blinding
                .unwrap_or([0; ROOT_BLINDING_WIDTH])
                .into_iter()
                .map(|lane| Scalar::from(u64::from(lane))),
        );
        debug_assert_eq!(values.len(), session.local_witness_width());
        Ok(Self {
            session_digest: session.digest,
            owner,
            values,
        })
    }

    /// Owner index whose order occupies this witness vector.
    pub const fn owner(&self) -> usize {
        self.owner
    }

    /// Number of scalar coordinates in this local vector.
    pub fn width(&self) -> usize {
        self.values.len()
    }

    #[cfg(test)]
    pub(crate) fn value_for_test(&self, coordinate: usize) -> Scalar {
        self.values[coordinate]
    }

    #[cfg(test)]
    pub(crate) fn has_short_coefficient_outside_for_test(&self, bound: i64) -> bool {
        let degree = (self.values.len() - 2 - ROOT_BLINDING_WIDTH) / 3;
        let allowed = (-bound..=bound).map(signed_scalar).collect::<Vec<_>>();
        self.values[2..2 + 3 * degree]
            .iter()
            .any(|value| !allowed.contains(value))
    }

    /// Secret-share this local vector among every configured proof worker.
    pub fn deal<R: CryptoRng + RngCore>(
        self,
        session: &DistributedWitnessSession,
        signing_key: &SigningKey,
        rng: &mut R,
    ) -> Result<DealerOutput> {
        if self.session_digest != session.digest {
            return Err(DistributedInputError::SessionMismatch);
        }
        if self.values.len() != session.local_witness_width() {
            return Err(DistributedInputError::InvalidWitness(
                "local witness width does not match the session",
            ));
        }
        let expected_key = session
            .owner_key(self.owner)
            .ok_or(DistributedInputError::PartyOutOfRange)?;
        if signing_key.verifying_key().to_bytes() != expected_key {
            return Err(DistributedInputError::SigningKeyMismatch);
        }

        let workers = session.n_workers();
        let width = self.values.len();
        let mut shares = (0..workers)
            .map(|_| vec![Scalar::ZERO; width])
            .collect::<Vec<_>>();
        for coordinate in 0..width {
            let mut sum = Scalar::ZERO;
            for (recipient, worker_shares) in shares.iter_mut().take(workers - 1).enumerate() {
                let share = random_deal_scalar(
                    rng,
                    session.digest,
                    self.owner,
                    recipient,
                    coordinate,
                    b"witness-share",
                );
                worker_shares[coordinate] = share;
                sum += share;
            }
            shares[workers - 1][coordinate] = self.values[coordinate] - sum;
        }

        let owner_blinding = random_deal_scalar(
            rng,
            session.digest,
            self.owner,
            workers,
            width,
            b"owner-blinding",
        );
        let mut share_blindings = vec![Scalar::ZERO; workers];
        let mut blinding_sum = Scalar::ZERO;
        for (recipient, blinding) in share_blindings.iter_mut().take(workers - 1).enumerate() {
            *blinding = random_deal_scalar(
                rng,
                session.digest,
                self.owner,
                recipient,
                width,
                b"share-blinding",
            );
            blinding_sum += *blinding;
        }
        share_blindings[workers - 1] = owner_blinding - blinding_sum;

        let owner_commitment =
            vector_commitment(session.degree, self.owner, &self.values, owner_blinding);
        let share_commitments = shares
            .iter()
            .zip(&share_blindings)
            .map(|(values, &blinding)| {
                vector_commitment(session.degree, self.owner, values, blinding)
            })
            .collect::<Vec<_>>();
        let digest = deal_digest(
            session.digest,
            self.owner,
            &owner_commitment,
            &share_commitments,
        );
        let signature = signing_key.sign(&deal_signing_message(&digest)).to_bytes();
        let contribution = DealerContribution {
            session_digest: session.digest,
            owner: self.owner,
            owner_commitment,
            share_commitments,
            digest,
            signature,
        };
        contribution.verify(session)?;

        let private_packets = shares
            .into_iter()
            .zip(share_blindings)
            .enumerate()
            .map(|(recipient, (values, blinding))| PrivateWitnessShare {
                session_digest: session.digest,
                dealer_digest: digest,
                owner: self.owner,
                recipient,
                values,
                blinding,
            })
            .collect();
        Ok(DealerOutput {
            contribution,
            private_packets,
        })
    }
}

/// Public signed commitment for one owner's complete dealing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DealerContribution {
    session_digest: [u8; 32],
    owner: usize,
    owner_commitment: [u8; 32],
    share_commitments: Vec<[u8; 32]>,
    digest: [u8; 32],
    signature: [u8; 64],
}

impl DealerContribution {
    /// Owner index committed by this dealing.
    pub const fn owner(&self) -> usize {
        self.owner
    }

    /// Public digest signed by the owner and acknowledged by every worker.
    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Hiding vector commitment to the owner's complete local base witness.
    pub const fn owner_commitment(&self) -> [u8; 32] {
        self.owner_commitment
    }

    fn verify(&self, session: &DistributedWitnessSession) -> Result<()> {
        if self.session_digest != session.digest {
            return Err(DistributedInputError::SessionMismatch);
        }
        if self.owner >= ORDER_COUNT || self.share_commitments.len() != session.n_workers() {
            return Err(DistributedInputError::PartyOutOfRange);
        }
        let owner_point = decode_point(&self.owner_commitment)?;
        let mut sum = RistrettoPoint::default();
        for commitment in &self.share_commitments {
            sum += decode_point(commitment)?;
        }
        if sum != owner_point {
            return Err(DistributedInputError::CommitmentMismatch);
        }
        let expected_digest = deal_digest(
            session.digest,
            self.owner,
            &self.owner_commitment,
            &self.share_commitments,
        );
        if self.digest != expected_digest {
            return Err(DistributedInputError::CertificateDigestMismatch);
        }
        let key = VerifyingKey::from_bytes(
            &session
                .owner_key(self.owner)
                .ok_or(DistributedInputError::PartyOutOfRange)?,
        )
        .map_err(|_| DistributedInputError::InvalidSignature)?;
        key.verify_strict(
            &deal_signing_message(&self.digest),
            &Signature::from_bytes(&self.signature),
        )
        .map_err(|_| DistributedInputError::InvalidSignature)
    }

    #[cfg(test)]
    pub(crate) fn corrupt_share_commitment_for_test(&mut self, worker: usize) {
        self.share_commitments[worker][0] ^= 1;
    }
}

/// One private packet plus its public contribution.
pub struct DealerOutput {
    pub contribution: DealerContribution,
    pub private_packets: Vec<PrivateWitnessShare>,
}

/// One worker's private additive share of one owner's local witness.
///
/// This object has no public serializer, `Clone`, or `Debug`.  It must travel
/// over a confidential authenticated owner-to-worker channel.
pub struct PrivateWitnessShare {
    session_digest: [u8; 32],
    dealer_digest: [u8; 32],
    owner: usize,
    recipient: usize,
    values: Vec<Scalar>,
    blinding: Scalar,
}

impl PrivateWitnessShare {
    /// Intended proof worker.
    pub const fn recipient(&self) -> usize {
        self.recipient
    }

    #[cfg(test)]
    pub(crate) fn corrupt_value_for_test(&mut self, coordinate: usize) {
        self.values[coordinate] += Scalar::ONE;
    }

    #[cfg(test)]
    pub(crate) fn value_for_test(&self, coordinate: usize) -> Scalar {
        self.values[coordinate]
    }

    #[cfg(test)]
    pub(crate) fn blinding_for_test(&self) -> Scalar {
        self.blinding
    }
}

/// Public signed statement that one worker verified its private opening of one
/// dealer's share commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecipientAcknowledgement {
    session_digest: [u8; 32],
    owner: usize,
    worker: usize,
    dealer_digest: [u8; 32],
    signature: [u8; 64],
}

impl RecipientAcknowledgement {
    fn verify(
        &self,
        session: &DistributedWitnessSession,
        contribution: &DealerContribution,
    ) -> Result<()> {
        if self.session_digest != session.digest {
            return Err(DistributedInputError::SessionMismatch);
        }
        if self.owner != contribution.owner || self.dealer_digest != contribution.digest {
            return Err(DistributedInputError::DealerMismatch);
        }
        let key = VerifyingKey::from_bytes(
            &session
                .worker_key(self.worker)
                .ok_or(DistributedInputError::PartyOutOfRange)?,
        )
        .map_err(|_| DistributedInputError::InvalidSignature)?;
        key.verify_strict(
            &ack_signing_message(
                &self.session_digest,
                self.owner,
                self.worker,
                &self.dealer_digest,
            ),
            &Signature::from_bytes(&self.signature),
        )
        .map_err(|_| DistributedInputError::InvalidSignature)
    }

    #[cfg(test)]
    pub(crate) fn corrupt_signature_for_test(&mut self) {
        self.signature[0] ^= 1;
    }
}

/// Party-local state machine which accepts exactly one private dealing from
/// each of the four owners.
pub struct WitnessPartyMachine {
    session: DistributedWitnessSession,
    worker: usize,
    signing_key: SigningKey,
    accepted: Vec<Option<PrivateWitnessShare>>,
}

impl WitnessPartyMachine {
    /// Construct one worker-local state machine under its roster identity.
    pub fn new(
        session: DistributedWitnessSession,
        worker: usize,
        signing_key: SigningKey,
    ) -> Result<Self> {
        let expected = session
            .worker_key(worker)
            .ok_or(DistributedInputError::PartyOutOfRange)?;
        if signing_key.verifying_key().to_bytes() != expected {
            return Err(DistributedInputError::SigningKeyMismatch);
        }
        Ok(Self {
            session,
            worker,
            signing_key,
            accepted: iter::repeat_with(|| None).take(ORDER_COUNT).collect(),
        })
    }

    /// Verify and retain one confidential private packet, returning the public
    /// signed acknowledgement only after its vector commitment opens exactly.
    pub fn accept(
        &mut self,
        contribution: &DealerContribution,
        packet: PrivateWitnessShare,
    ) -> Result<RecipientAcknowledgement> {
        contribution.verify(&self.session)?;
        if packet.session_digest != self.session.digest {
            return Err(DistributedInputError::SessionMismatch);
        }
        if packet.owner != contribution.owner || packet.dealer_digest != contribution.digest {
            return Err(DistributedInputError::DealerMismatch);
        }
        if packet.recipient != self.worker {
            return Err(DistributedInputError::RecipientMismatch);
        }
        if packet.values.len() != self.session.local_witness_width() {
            return Err(DistributedInputError::InvalidWitness(
                "private packet width does not match the session",
            ));
        }
        if self.accepted[packet.owner].is_some() {
            return Err(DistributedInputError::DuplicateDealer);
        }
        let actual = vector_commitment(
            self.session.degree,
            packet.owner,
            &packet.values,
            packet.blinding,
        );
        if actual != contribution.share_commitments[self.worker] {
            return Err(DistributedInputError::CommitmentMismatch);
        }
        let owner = packet.owner;
        let acknowledgement = RecipientAcknowledgement {
            session_digest: self.session.digest,
            owner,
            worker: self.worker,
            dealer_digest: contribution.digest,
            signature: self
                .signing_key
                .sign(&ack_signing_message(
                    &self.session.digest,
                    owner,
                    self.worker,
                    &contribution.digest,
                ))
                .to_bytes(),
        };
        self.accepted[owner] = Some(packet);
        Ok(acknowledgement)
    }

    /// Finish only after all four private owner packets have been accepted.
    pub fn finish(self) -> Result<PreparedWitnessShare> {
        if self.accepted.iter().any(Option::is_none) {
            return Err(DistributedInputError::MissingDealers);
        }
        Ok(PreparedWitnessShare {
            session_digest: self.session.digest,
            worker: self.worker,
            owner_shares: self
                .accepted
                .into_iter()
                .map(|packet| packet.expect("all four owner packets checked above"))
                .collect(),
        })
    }
}

/// Party-local capability containing one additive share of every exact base
/// witness coordinate.  A future distributed R1CS backend consumes these
/// values in place; a coordinator must never collect these objects.
pub struct PreparedWitnessShare {
    session_digest: [u8; 32],
    worker: usize,
    owner_shares: Vec<PrivateWitnessShare>,
}

impl PreparedWitnessShare {
    /// Session to which these private inputs are committed.
    pub const fn session_digest(&self) -> [u8; 32] {
        self.session_digest
    }

    /// Proof-worker index owning these shares.
    pub const fn worker(&self) -> usize {
        self.worker
    }

    /// Borrow one owner vector and its vector-commitment blinding.
    ///
    /// This is the intentional handoff to a distributed proving backend.  The
    /// returned values are only this worker's uniformly random additive share,
    /// never an owner's complete order.
    pub fn owner_share(&self, owner: usize) -> Option<(&[Scalar], Scalar)> {
        self.owner_shares
            .get(owner)
            .map(|packet| (packet.values.as_slice(), packet.blinding))
    }

    /// Fail closed unless this private capability came from the exact four
    /// public owner dealings carried by `certificate`.
    ///
    /// Kept crate-private so downstream code cannot turn dealer identifiers
    /// into a substitute for running the worker-local commitment checks.
    pub(crate) fn verify_certificate_binding(
        &self,
        certificate: &DistributedInputCertificate,
    ) -> Result<()> {
        if self.session_digest != certificate.session_digest {
            return Err(DistributedInputError::SessionMismatch);
        }
        if self.owner_shares.len() != ORDER_COUNT || certificate.dealers.len() != ORDER_COUNT {
            return Err(DistributedInputError::MalformedCertificate);
        }
        for (owner, packet) in self.owner_shares.iter().enumerate() {
            if packet.owner != owner || packet.dealer_digest != certificate.dealers[owner].digest {
                return Err(DistributedInputError::DealerMismatch);
            }
            if packet.recipient != self.worker {
                return Err(DistributedInputError::RecipientMismatch);
            }
        }
        Ok(())
    }
}

/// Public coordinator state machine.  It never accepts a private witness
/// packet or scalar share.
pub struct DistributedInputCoordinator {
    session: DistributedWitnessSession,
    dealers: Vec<Option<DealerContribution>>,
    acknowledgements: Vec<Vec<Option<RecipientAcknowledgement>>>,
}

impl DistributedInputCoordinator {
    /// Begin collecting public artifacts for one exact session.
    pub fn new(session: DistributedWitnessSession) -> Self {
        let workers = session.n_workers();
        Self {
            session,
            dealers: iter::repeat_with(|| None).take(ORDER_COUNT).collect(),
            acknowledgements: (0..ORDER_COUNT)
                .map(|_| iter::repeat_with(|| None).take(workers).collect())
                .collect(),
        }
    }

    /// Accept one signed owner dealing after checking the public aggregate
    /// commitment equality.
    pub fn accept_dealer(&mut self, contribution: DealerContribution) -> Result<()> {
        contribution.verify(&self.session)?;
        let owner = contribution.owner;
        if self.dealers[owner].is_some() {
            return Err(DistributedInputError::DuplicateDealer);
        }
        self.dealers[owner] = Some(contribution);
        Ok(())
    }

    /// Accept one signed recipient acknowledgement for an already accepted
    /// owner dealing.
    pub fn accept_acknowledgement(
        &mut self,
        acknowledgement: RecipientAcknowledgement,
    ) -> Result<()> {
        if acknowledgement.owner >= ORDER_COUNT
            || acknowledgement.worker >= self.session.n_workers()
        {
            return Err(DistributedInputError::PartyOutOfRange);
        }
        let contribution = self.dealers[acknowledgement.owner]
            .as_ref()
            .ok_or(DistributedInputError::MissingDealers)?;
        acknowledgement.verify(&self.session, contribution)?;
        let slot = &mut self.acknowledgements[acknowledgement.owner][acknowledgement.worker];
        if slot.is_some() {
            return Err(DistributedInputError::DuplicateAcknowledgement);
        }
        *slot = Some(acknowledgement);
        Ok(())
    }

    /// Finalize the canonical public certificate.
    pub fn finish(self) -> Result<DistributedInputCertificate> {
        if self.dealers.iter().any(Option::is_none) {
            return Err(DistributedInputError::MissingDealers);
        }
        if self.acknowledgements.iter().flatten().any(Option::is_none) {
            return Err(DistributedInputError::MissingAcknowledgements);
        }
        let dealers = self
            .dealers
            .into_iter()
            .map(|dealer| dealer.expect("all owner dealings checked above"))
            .collect();
        let acknowledgements = self
            .acknowledgements
            .into_iter()
            .flat_map(|row| {
                row.into_iter()
                    .map(|ack| ack.expect("all worker acknowledgements checked above"))
            })
            .collect();
        let mut certificate = DistributedInputCertificate {
            session_digest: self.session.digest,
            degree: self.session.degree,
            n_workers: self.session.n_workers(),
            dealers,
            acknowledgements,
            transcript_digest: [0; 32],
        };
        certificate.transcript_digest = certificate.compute_transcript_digest();
        certificate.verify(&self.session)?;
        Ok(certificate)
    }
}

/// Canonical public proof-input preparation certificate.
///
/// This is evidence of roster-authenticated, commitment-consistent input
/// distribution.  It is not evidence that the private relation is satisfied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedInputCertificate {
    session_digest: [u8; 32],
    degree: usize,
    n_workers: usize,
    dealers: Vec<DealerContribution>,
    acknowledgements: Vec<RecipientAcknowledgement>,
    transcript_digest: [u8; 32],
}

impl DistributedInputCertificate {
    /// Public transcript digest to bind into a distributed R1CS proof.
    pub const fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    /// One hiding commitment binding the concatenation of all four owner
    /// vectors in their separate Bulletproof generator namespaces.
    pub fn joint_input_commitment(&self) -> Result<[u8; 32]> {
        let mut joint = RistrettoPoint::default();
        for dealer in &self.dealers {
            joint += decode_point(&dealer.owner_commitment)?;
        }
        Ok(joint.compress().to_bytes())
    }

    /// Recheck the complete certificate against independently supplied public
    /// session policy.
    pub fn verify(&self, session: &DistributedWitnessSession) -> Result<()> {
        if self.session_digest != session.digest
            || self.degree != session.degree
            || self.n_workers != session.n_workers()
        {
            return Err(DistributedInputError::SessionMismatch);
        }
        if self.dealers.len() != ORDER_COUNT
            || self.acknowledgements.len() != ORDER_COUNT * session.n_workers()
        {
            return Err(DistributedInputError::MalformedCertificate);
        }
        for (owner, dealer) in self.dealers.iter().enumerate() {
            if dealer.owner != owner {
                return Err(DistributedInputError::DealerMismatch);
            }
            dealer.verify(session)?;
        }
        for owner in 0..ORDER_COUNT {
            for worker in 0..session.n_workers() {
                let ack = &self.acknowledgements[owner * session.n_workers() + worker];
                if ack.owner != owner || ack.worker != worker {
                    return Err(DistributedInputError::RecipientMismatch);
                }
                ack.verify(session, &self.dealers[owner])?;
            }
        }
        if self.transcript_digest != self.compute_transcript_digest() {
            return Err(DistributedInputError::CertificateDigestMismatch);
        }
        Ok(())
    }

    /// Strict, bounded canonical public wire.  Private scalar shares and their
    /// commitment blindings are never serialized here.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut body = self.canonical_body();
        body.extend_from_slice(&self.transcript_digest);
        let checksum = keyed_hash(CHECKSUM_DOMAIN, &body);
        body.extend_from_slice(&checksum);
        body
    }

    /// Parse and verify the canonical public wire against the expected session.
    pub fn from_bytes(bytes: &[u8], session: &DistributedWitnessSession) -> Result<Self> {
        if bytes.len() != certificate_wire_len(session.n_workers())? {
            return Err(DistributedInputError::MalformedCertificate);
        }
        let checksum_start = bytes
            .len()
            .checked_sub(32)
            .ok_or(DistributedInputError::MalformedCertificate)?;
        if bytes[checksum_start..] != keyed_hash(CHECKSUM_DOMAIN, &bytes[..checksum_start]) {
            return Err(DistributedInputError::MalformedCertificate);
        }
        let mut input = Reader::new(&bytes[..checksum_start]);
        if input.take::<8>()? != *CERTIFICATE_MAGIC {
            return Err(DistributedInputError::MalformedCertificate);
        }
        let session_digest = input.take::<32>()?;
        let degree = input.usize_u32()?;
        let n_workers = input.usize_u16()?;
        let n_dealers = input.usize_u16()?;
        if degree != session.degree || n_workers != session.n_workers() || n_dealers != ORDER_COUNT
        {
            return Err(DistributedInputError::SessionMismatch);
        }
        let mut dealers = Vec::with_capacity(ORDER_COUNT);
        for _ in 0..ORDER_COUNT {
            let owner = input.usize_u16()?;
            let owner_commitment = input.take::<32>()?;
            let mut share_commitments = Vec::with_capacity(n_workers);
            for _ in 0..n_workers {
                share_commitments.push(input.take::<32>()?);
            }
            let digest = input.take::<32>()?;
            let signature = input.take::<64>()?;
            dealers.push(DealerContribution {
                session_digest,
                owner,
                owner_commitment,
                share_commitments,
                digest,
                signature,
            });
        }
        let acknowledgement_count = input.usize_u16()?;
        if acknowledgement_count != ORDER_COUNT * n_workers {
            return Err(DistributedInputError::MalformedCertificate);
        }
        let mut acknowledgements = Vec::with_capacity(acknowledgement_count);
        for _ in 0..acknowledgement_count {
            acknowledgements.push(RecipientAcknowledgement {
                session_digest,
                owner: input.usize_u16()?,
                worker: input.usize_u16()?,
                dealer_digest: input.take::<32>()?,
                signature: input.take::<64>()?,
            });
        }
        let transcript_digest = input.take::<32>()?;
        input.finish()?;
        let certificate = Self {
            session_digest,
            degree,
            n_workers,
            dealers,
            acknowledgements,
            transcript_digest,
        };
        certificate.verify(session)?;
        if certificate.to_bytes() != bytes {
            return Err(DistributedInputError::MalformedCertificate);
        }
        Ok(certificate)
    }

    fn canonical_body(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            certificate_wire_len(self.n_workers)
                .unwrap_or_default()
                .saturating_sub(64),
        );
        out.extend_from_slice(CERTIFICATE_MAGIC);
        out.extend_from_slice(&self.session_digest);
        out.extend_from_slice(&(self.degree as u32).to_be_bytes());
        out.extend_from_slice(&(self.n_workers as u16).to_be_bytes());
        out.extend_from_slice(&(ORDER_COUNT as u16).to_be_bytes());
        for dealer in &self.dealers {
            out.extend_from_slice(&(dealer.owner as u16).to_be_bytes());
            out.extend_from_slice(&dealer.owner_commitment);
            for commitment in &dealer.share_commitments {
                out.extend_from_slice(commitment);
            }
            out.extend_from_slice(&dealer.digest);
            out.extend_from_slice(&dealer.signature);
        }
        out.extend_from_slice(&(self.acknowledgements.len() as u16).to_be_bytes());
        for ack in &self.acknowledgements {
            out.extend_from_slice(&(ack.owner as u16).to_be_bytes());
            out.extend_from_slice(&(ack.worker as u16).to_be_bytes());
            out.extend_from_slice(&ack.dealer_digest);
            out.extend_from_slice(&ack.signature);
        }
        out
    }

    fn compute_transcript_digest(&self) -> [u8; 32] {
        keyed_hash(CERTIFICATE_DOMAIN, &self.canonical_body())
    }

    #[cfg(test)]
    pub(crate) fn corrupt_ack_signature_for_test(&mut self, index: usize) {
        self.acknowledgements[index].corrupt_signature_for_test();
        self.transcript_digest = self.compute_transcript_digest();
    }
}

fn session_digest(
    relation_digest: &[u8; 32],
    ceremony_nonce: &[u8; 32],
    owner_keys: &[[u8; 32]; ORDER_COUNT],
    worker_keys: &[[u8; 32]],
    degree: usize,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(SESSION_DOMAIN);
    hasher.update(LAYOUT_ID);
    hasher.update(&(ORDER_COUNT as u64).to_be_bytes());
    hasher.update(&(PRICE_COUNT as u64).to_be_bytes());
    hasher.update(&(degree as u64).to_be_bytes());
    hasher.update(&(BFV_VARIANCE as u64).to_be_bytes());
    hasher.update(&(BFV_SHORT_ABS_BOUND as u64).to_be_bytes());
    hasher.update(&(ROOT_BLINDING_WIDTH as u64).to_be_bytes());
    hasher.update(&BABYBEAR_MODULUS.to_be_bytes());
    hasher.update(relation_digest);
    hasher.update(ceremony_nonce);
    for key in owner_keys {
        hasher.update(key);
    }
    hasher.update(&(worker_keys.len() as u64).to_be_bytes());
    for key in worker_keys {
        hasher.update(key);
    }
    *hasher.finalize().as_bytes()
}

fn deal_digest(
    session_digest: [u8; 32],
    owner: usize,
    owner_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(DEAL_DOMAIN);
    hasher.update(&session_digest);
    hasher.update(&(owner as u64).to_be_bytes());
    hasher.update(owner_commitment);
    hasher.update(&(share_commitments.len() as u64).to_be_bytes());
    for commitment in share_commitments {
        hasher.update(commitment);
    }
    *hasher.finalize().as_bytes()
}

fn deal_signing_message(digest: &[u8; 32]) -> Vec<u8> {
    let mut message = Vec::with_capacity(DEAL_SIGNATURE_DOMAIN.len() + digest.len());
    message.extend_from_slice(DEAL_SIGNATURE_DOMAIN);
    message.extend_from_slice(digest);
    message
}

fn ack_signing_message(
    session_digest: &[u8; 32],
    owner: usize,
    worker: usize,
    dealer_digest: &[u8; 32],
) -> Vec<u8> {
    let mut message = Vec::with_capacity(ACK_SIGNATURE_DOMAIN.len() + 80);
    message.extend_from_slice(ACK_SIGNATURE_DOMAIN);
    message.extend_from_slice(session_digest);
    message.extend_from_slice(&(owner as u64).to_be_bytes());
    message.extend_from_slice(&(worker as u64).to_be_bytes());
    message.extend_from_slice(dealer_digest);
    message
}

fn vector_commitment(degree: usize, owner: usize, values: &[Scalar], blinding: Scalar) -> [u8; 32] {
    debug_assert_eq!(values.len(), 2 + 3 * degree + ROOT_BLINDING_WIDTH);
    let blind_base = PedersenGens::default().B_blinding;
    let point = if degree == BFV_DEGREE {
        let generators = PRODUCTION_GENS.share(owner);
        RistrettoPoint::multiscalar_mul(
            values.iter().copied().chain(iter::once(blinding)),
            generators
                .G(values.len())
                .copied()
                .chain(iter::once(blind_base)),
        )
    } else {
        #[cfg(test)]
        {
            let test_gens = BulletproofGens::new(values.len(), ORDER_COUNT);
            let generators = test_gens.share(owner);
            RistrettoPoint::multiscalar_mul(
                values.iter().copied().chain(iter::once(blinding)),
                generators
                    .G(values.len())
                    .copied()
                    .chain(iter::once(blind_base)),
            )
        }
        #[cfg(not(test))]
        unreachable!("production distributed witnesses always use degree 4096")
    };
    point.compress().to_bytes()
}

fn decode_point(bytes: &[u8; 32]) -> Result<RistrettoPoint> {
    let compressed = CompressedRistretto(*bytes);
    let point = compressed
        .decompress()
        .ok_or(DistributedInputError::InvalidCommitment)?;
    if point.compress().to_bytes() != *bytes {
        return Err(DistributedInputError::InvalidCommitment);
    }
    Ok(point)
}

fn random_deal_scalar<R: CryptoRng + RngCore>(
    rng: &mut R,
    session_digest: [u8; 32],
    owner: usize,
    recipient: usize,
    coordinate: usize,
    purpose: &[u8],
) -> Scalar {
    // Mixing the CSPRNG output through the complete private-share context makes
    // accidental RNG stream reuse unlinkable across ceremonies.  The entropy
    // is still required to be secret and cryptographically random: public
    // domain separation is not a substitute for a CSPRNG.
    let mut entropy = [0u8; 64];
    rng.fill_bytes(&mut entropy);
    let mut hasher = blake3::Hasher::new_derive_key(SHARE_MASK_DOMAIN);
    hasher.update(&session_digest);
    hasher.update(&(owner as u64).to_be_bytes());
    hasher.update(&(recipient as u64).to_be_bytes());
    hasher.update(&(coordinate as u64).to_be_bytes());
    hasher.update(&(purpose.len() as u64).to_be_bytes());
    hasher.update(purpose);
    hasher.update(&entropy);
    let mut wide = [0u8; 64];
    hasher.finalize_xof().fill(&mut wide);
    Scalar::from_bytes_mod_order_wide(&wide)
}

fn signed_scalar(value: i64) -> Scalar {
    if value < 0 {
        -Scalar::from(value.unsigned_abs())
    } else {
        Scalar::from(value as u64)
    }
}

/// Exact copy of fhe.rs's pinned CBD bit consumption used by the existing
/// private-book relation.  The layout/session version makes any future sampler
/// change an explicit protocol-version change.
fn sample_cbd<R: RngCore09>(size: usize, variance: usize, rng: &mut R) -> Result<Vec<i64>> {
    if !(1..=16).contains(&variance) {
        return Err(DistributedInputError::InvalidWitness(
            "unsupported BFV CBD variance",
        ));
    }
    let number_bits = 4 * variance;
    let mask_add = ((u64::MAX >> (64 - number_bits)) >> (2 * variance)) as u128;
    let mask_sub = mask_add << (2 * variance);
    let mut pool = 0u128;
    let mut pool_bits = 0usize;
    let mut out = Vec::with_capacity(size);
    for _ in 0..size {
        if pool_bits < number_bits {
            pool |= (rng.next_u64() as u128) << pool_bits;
            pool_bits += 64;
        }
        let value =
            ((pool & mask_add).count_ones() as i64) - ((pool & mask_sub).count_ones() as i64);
        if !(-((2 * variance) as i64)..=(2 * variance) as i64).contains(&value) {
            return Err(DistributedInputError::InvalidWitness(
                "CBD coefficient exceeded the exact fhe.rs support",
            ));
        }
        out.push(value);
        pool >>= number_bits;
        pool_bits -= number_bits;
    }
    Ok(out)
}

fn keyed_hash(domain: &str, bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn certificate_wire_len(workers: usize) -> Result<usize> {
    if !(2..=MAX_WORKERS).contains(&workers) {
        return Err(DistributedInputError::MalformedCertificate);
    }
    let header = 8usize + 32 + 4 + 2 + 2;
    let dealer = 2usize + 32 + workers * 32 + 32 + 64;
    let ack = 2usize + 2 + 32 + 64;
    header
        .checked_add(ORDER_COUNT * dealer)
        .and_then(|len| len.checked_add(2 + ORDER_COUNT * workers * ack))
        .and_then(|len| len.checked_add(32 + 32))
        .ok_or(DistributedInputError::MalformedCertificate)
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N]> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|&end| end <= self.bytes.len())
            .ok_or(DistributedInputError::MalformedCertificate)?;
        let value = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| DistributedInputError::MalformedCertificate)?;
        self.offset = end;
        Ok(value)
    }

    fn usize_u16(&mut self) -> Result<usize> {
        Ok(u16::from_be_bytes(self.take::<2>()?) as usize)
    }

    fn usize_u32(&mut self) -> Result<usize> {
        usize::try_from(u32::from_be_bytes(self.take::<4>()?))
            .map_err(|_| DistributedInputError::MalformedCertificate)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(DistributedInputError::MalformedCertificate)
        }
    }
}

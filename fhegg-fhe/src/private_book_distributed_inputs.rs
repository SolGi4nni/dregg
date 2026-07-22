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
//! `kind || quantity || option[128] || message_slots[9] ||`
//! `u[degree] || e1[degree] || e2[degree] || root_blind[8]`.
//!
//! Owner zero supplies the book's eight canonical root-blinding felts; the
//! other owners' root-blinding lanes are fixed to zero.  Every owner n-of-n
//! additively shares that vector over the Ristretto scalar field among the
//! configured proof workers. Before releasing those shares, each owner also
//! makes a four-value Bulletproof range proof for `kind`, `7-kind`, `quantity`,
//! and `15-quantity`.  An owner-local Bulletproof R1CS proof then constrains a
//! 128-entry boolean one-hot selector to exactly `16*kind + quantity` and derives
//! the private relation's eight unary demand/supply slots plus its injective
//! `kind + 8*quantity` root-code slot from that selector. The same R1CS proof
//! range-constrains all 12,288 BFV `u/e1/e2` coefficients to `[-32,31]`. A
//! transcript-derived random-linear proof links all 12,427 non-root scalar
//! commitments used by these proofs to the exact first 12,427 coordinates of
//! the production vector commitment. Thus this nonlinear order-domain,
//! semantic-message, and bounded-short layer is proved by the one principal who
//! legitimately knows that order; neither a worker nor the public coordinator
//! reconstructs it. A vector Pedersen commitment is made in the owner's own
//! Bulletproof generator namespace.  The public equality
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
//! A coordinator or certificate verifier sees only perfectly hiding vector and
//! scalar Pedersen commitments, zero-knowledge range/R1CS/link proofs, public
//! identities, and signatures. Complement commitments use the negated hidden
//! blinding, so the verifier checks `V_k + V_(7-k) = 7B` and
//! `V_q + V_(15-q) = 15B` without receiving any opening. Any strict subset
//! of the proof workers has uniformly masked additive shares of every owner's
//! vector under the CSPRNG/BLAKE3 scalar-sampling assumption. Thus no single
//! worker learns an order or BFV randomness, and no owner is asked for another
//! owner's order. Share masks are domain-separated by session, owner,
//! recipient, coordinate, and purpose, so accidentally restarting the same
//! CSPRNG stream in a later ceremony does not let one worker cancel repeated
//! masks to recover order deltas.  This
//! assumes distinct owners are actually operated by distinct principals and
//! that the private packets use a confidential authenticated transport; this
//! module intentionally gives private packets no wire codec.
//!
//! # What this deliberately does not claim
//!
//! The certificate proves every hidden order kind is in `0..8`, every hidden
//! quantity is in `0..16`, and the one-hot selector and nine semantic message
//! slots are the exact finite-table image of those values. It also proves the
//! three short-polynomial rows are in `[-32,31]`; all of these claims are linked
//! to the committed/share-held coordinates. It does not yet prove that the
//! deployed `fhe.rs` polynomial message table and bounded randomness satisfy the
//! public BFV ciphertext equations, nor the Poseidon root or clearing result.
//! These Bulletproofs and commitments use the classical Ristretto
//! discrete-log assumption; they are not post-quantum. Worker
//! acknowledgements authenticate the local commitment-opening check; they are
//! not proofs of correct MPC execution.  A production completion must make a
//! distributed R1CS prover consume the returned `PreparedWitnessShare`s and
//! prove equality between its secret-shared circuit inputs and these public
//! commitments, or compose per-owner BFV proofs with a distributed root proof.
//! The current monolithic `prove_private_book_bfv_zk` API must not be called by
//! reconstructing these shares at a coordinator.
//!
//! The ceremony commits fhe.rs's actual variance-10 CBD coefficients, whose
//! support is `[-20,20]`, and proves the monolithic relation's deliberately
//! looser `[-32,31]` bounded-short envelope. It still does not prove exact
//! seeded sampler-image membership, seed entropy, or seed distinctness; a
//! future distributed backend must preserve that distinction.

use std::collections::HashSet;
use std::fmt;
use std::iter;
use std::sync::LazyLock;

#[cfg(test)]
use std::cell::Cell;

use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use bulletproofs_r1cs::r1cs::{ConstraintSystem, LinearCombination, R1CSProof, Variable};
use bulletproofs_r1cs::{
    BulletproofGens as R1csBulletproofGens, LinearProof, PedersenGens as R1csPedersenGens,
};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use merlin::Transcript;
use rand::{CryptoRng, RngCore};
use rand_09::rngs::StdRng as StdRng09;
use rand_09::{RngCore as RngCore09, SeedableRng as SeedableRng09};

#[cfg(not(test))]
use crate::private_book_relation::{private_book_relation_digest, PrivateBookCiphertexts};
#[cfg(not(test))]
use crate::threshold::{BfvParams, CollectivePublicKey};
#[cfg(not(test))]
use dregg_circuit_prove::dark_bazaar_private::PublicStatement;

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
/// Eight side-and-limit order kinds in the fixed N4K4 book.
pub const KIND_COUNT: usize = 2 * PRICE_COUNT;
/// Sixteen private quantity choices, including canonical zero padding.
pub const QUANTITY_COUNT: usize = 16;
/// Exact finite selector table shared with the monolithic BFV relation.
pub const OPTION_COUNT: usize = KIND_COUNT * QUANTITY_COUNT;
/// Four demand, four supply, and one private root-code slot.
pub const MESSAGE_SLOT_WIDTH: usize = 2 * PRICE_COUNT + 1;
/// Exact prefix carried before the three BFV short-polynomial rows.
pub const DERIVED_ORDER_WIDTH: usize = 2 + OPTION_COUNT + MESSAGE_SLOT_WIDTH;
/// Exact production width of one owner's base input vector.
pub const LOCAL_WITNESS_WIDTH: usize = DERIVED_ORDER_WIDTH + 3 * BFV_DEGREE + ROOT_BLINDING_WIDTH;

const SESSION_DOMAIN: &str = "fhegg/private-book-distributed-input/session/v4";
const DEAL_DOMAIN: &str = "fhegg/private-book-distributed-input/deal/v4";
const SHARE_MASK_DOMAIN: &str = "fhegg/private-book-distributed-input/share-mask/v4";
const DEAL_SIGNATURE_DOMAIN: &[u8] = b"fhegg/private-book-distributed-input/deal-signature/v4";
const ACK_SIGNATURE_DOMAIN: &[u8] = b"fhegg/private-book-distributed-input/ack-signature/v4";
const CERTIFICATE_DOMAIN: &str = "fhegg/private-book-distributed-input/certificate/v4";
const CHECKSUM_DOMAIN: &str = "fhegg/private-book-distributed-input/checksum/v4";
const LAYOUT_ID: &[u8] = b"FHEGG-PB-BFV-DISTRIBUTED-BASE-INPUT-N4K4-V4-SHORT";
const CERTIFICATE_MAGIC: &[u8; 8] = b"FHPDI004";
const OWNER_RANGE_TRANSCRIPT: &[u8] = b"fhegg/private-book-owner-range/v1";
const OWNER_SELECTOR_TRANSCRIPT: &[u8] = b"fhegg/private-book-owner-selector-short-r1cs/v2";
const OWNER_LINK_TRANSCRIPT: &[u8] = b"fhegg/private-book-owner-derived-link/v2";
const OWNER_RANGE_COMPONENT_DOMAIN: &str = "fhegg/private-book-owner-range/component/v1";
const OWNER_RANGE_ARTIFACT_DOMAIN: &str = "fhegg/private-book-owner-range/artifact/v3";
const OWNER_RANGE_CHECKSUM_DOMAIN: &str = "fhegg/private-book-owner-range/checksum/v3";
const OWNER_LINK_CHALLENGE_DOMAIN: &str = "fhegg/private-book-owner-derived-link/challenge/v2";
const OWNER_RANGE_ARTIFACT_MAGIC: &[u8; 8] = b"FHPOR003";
const OWNER_RANGE_ARTIFACT_VERSION: u16 = 3;
const OWNER_RANGE_BITS: usize = 8;
const OWNER_RANGE_VALUES: usize = 4;
const OWNER_SHORT_RANGE_BITS: usize = 6;
const OWNER_SHORT_RANGE_SHIFT: u64 = 1 << (OWNER_SHORT_RANGE_BITS - 1);
const OWNER_LINK_PROOFS: usize = 1;
const OWNER_RANGE_PROOF_BYTES: usize = 608;
const OWNER_RANGE_ARTIFACT_HEADER_BYTES: usize = 8 + 2 + 2 + 4 + 4 + 32 + 2 * 32 + 4;
const MAX_OWNER_RANGE_ARTIFACT_BYTES: usize = 512 * 1024;

static PRODUCTION_GENS: LazyLock<BulletproofGens> =
    LazyLock::new(|| BulletproofGens::new(LOCAL_WITNESS_WIDTH.next_power_of_two(), ORDER_COUNT));
static OWNER_SELECTOR_GENS: LazyLock<R1csBulletproofGens> = LazyLock::new(|| {
    R1csBulletproofGens::new(
        owner_r1cs_multiplier_capacity(BFV_DEGREE).expect("fixed capacity"),
        1,
    )
});

#[cfg(test)]
thread_local! {
    static OWNER_PROOF_VERIFICATION_CALLS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_owner_proof_verification_count_for_test() {
    OWNER_PROOF_VERIFICATION_CALLS.with(|count| count.set(0));
}

#[cfg(test)]
pub(crate) fn owner_proof_verification_count_for_test() -> usize {
    OWNER_PROOF_VERIFICATION_CALLS.with(Cell::get)
}

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
    InvalidOrderRangeProof,
    OrderRangeProofRejected,
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
            Self::InvalidOrderRangeProof => write!(f, "owner order-range proof is malformed"),
            Self::OrderRangeProofRejected => write!(f, "owner order-range proof was rejected"),
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
    /// Construct the exact production N4K4/degree-4096 ceremony. The complete
    /// public BFV relation is accepted here so its transcript digest cannot be
    /// chosen independently of the ciphertexts, parameters, key, or statement.
    #[cfg(not(test))]
    pub fn new(
        statement: PublicStatement,
        ciphertexts: &PrivateBookCiphertexts,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
        ceremony_nonce: [u8; 32],
        owner_keys: [[u8; 32]; ORDER_COUNT],
        worker_keys: Vec<[u8; 32]>,
    ) -> Result<Self> {
        if params.degree() != BFV_DEGREE {
            return Err(DistributedInputError::InvalidSession(
                "production distributed BFV requires degree 4096",
            ));
        }
        Self::new_inner(
            private_book_relation_digest(statement, ciphertexts, params, public_key),
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
        DERIVED_ORDER_WIDTH + 3 * self.degree + ROOT_BLINDING_WIDTH
    }

    pub(crate) fn owner_key(&self, owner: usize) -> Option<[u8; 32]> {
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
        let option_index = kind as usize * QUANTITY_COUNT + quantity as usize;
        values.extend(
            (0..OPTION_COUNT).map(|option| Scalar::from(u64::from(option == option_index))),
        );
        values.extend(
            option_message_slots(kind as usize, quantity as usize)
                .into_iter()
                .map(Scalar::from),
        );
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
    pub(crate) fn set_value_for_test(&mut self, coordinate: usize, value: Scalar) {
        self.values[coordinate] = value;
    }

    #[cfg(test)]
    pub(crate) fn has_short_coefficient_outside_for_test(&self, bound: i64) -> bool {
        let degree = (self.values.len() - DERIVED_ORDER_WIDTH - ROOT_BLINDING_WIDTH) / 3;
        let allowed = (-bound..=bound).map(signed_scalar).collect::<Vec<_>>();
        self.values[DERIVED_ORDER_WIDTH..DERIVED_ORDER_WIDTH + 3 * degree]
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
        let order_range_proof = OwnerOrderRangeProof::create(
            session,
            self.owner,
            &self.values,
            owner_blinding,
            owner_commitment,
            &share_commitments,
            digest,
            rng,
        )?;
        let range_proof_digest = order_range_proof.digest();
        let signature = signing_key
            .sign(&deal_signing_message(&digest, &range_proof_digest))
            .to_bytes();
        let contribution = DealerContribution {
            session_digest: session.digest,
            owner: self.owner,
            owner_commitment,
            share_commitments,
            digest,
            order_range_proof,
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
        let continuation = OwnerWitnessContinuation {
            session_digest: session.digest,
            owner: self.owner,
            values: self.values,
        };
        Ok(DealerOutput {
            contribution,
            private_packets,
            continuation,
        })
    }
}

/// Canonical public proof of one owner's committed order semantics.
///
/// Besides the kind/quantity range proof, this contains the
/// selector/message/shortness R1CS proof and a random-linear batch link to the
/// exact distributed vector.
#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnerOrderRangeProof {
    bytes: Vec<u8>,
}

impl OwnerOrderRangeProof {
    #[allow(clippy::too_many_arguments)]
    fn create<R: CryptoRng + RngCore>(
        session: &DistributedWitnessSession,
        owner: usize,
        values: &[Scalar],
        owner_blinding: Scalar,
        owner_commitment: [u8; 32],
        share_commitments: &[[u8; 32]],
        deal_digest: [u8; 32],
        rng: &mut R,
    ) -> Result<Self> {
        if owner >= ORDER_COUNT || values.len() != session.local_witness_width() {
            return Err(DistributedInputError::InvalidOrderRangeProof);
        }
        let kind = small_scalar(values[0]).ok_or(DistributedInputError::InvalidWitness(
            "order kind is not a canonical small integer",
        ))?;
        let quantity = small_scalar(values[1]).ok_or(DistributedInputError::InvalidWitness(
            "order quantity is not a canonical small integer",
        ))?;
        if kind >= 2 * PRICE_COUNT as u64 || quantity > 15 {
            return Err(DistributedInputError::InvalidWitness(
                "order is outside the fixed N4K4 range",
            ));
        }

        let kind_blinding = random_deal_scalar(
            rng,
            session.digest,
            owner,
            session.n_workers() + 1,
            0,
            b"owner-range-blinding",
        );
        let quantity_blinding = random_deal_scalar(
            rng,
            session.digest,
            owner,
            session.n_workers() + 1,
            1,
            b"owner-range-blinding",
        );
        let range_values = [kind, 7 - kind, quantity, 15 - quantity];
        let range_blindings = [
            kind_blinding,
            -kind_blinding,
            quantity_blinding,
            -quantity_blinding,
        ];
        let pc_gens = PedersenGens::default();
        let range_gens = BulletproofGens::new(OWNER_RANGE_BITS, OWNER_RANGE_VALUES);
        let mut range_transcript = owner_range_transcript(
            session,
            owner,
            &owner_commitment,
            share_commitments,
            &deal_digest,
        );
        let (range_proof, commitments) = RangeProof::prove_multiple_with_rng(
            &range_gens,
            &pc_gens,
            &mut range_transcript,
            &range_values,
            &range_blindings,
            OWNER_RANGE_BITS,
            rng,
        )
        .map_err(|_| DistributedInputError::OrderRangeProofRejected)?;
        if commitments.len() != OWNER_RANGE_VALUES {
            return Err(DistributedInputError::OrderRangeProofRejected);
        }
        let kind_point = commitments[0]
            .decompress()
            .ok_or(DistributedInputError::OrderRangeProofRejected)?;
        let quantity_point = commitments[2]
            .decompress()
            .ok_or(DistributedInputError::OrderRangeProofRejected)?;
        if commitments[1] != (Scalar::from(7u64) * pc_gens.B - kind_point).compress()
            || commitments[3] != (Scalar::from(15u64) * pc_gens.B - quantity_point).compress()
        {
            return Err(DistributedInputError::OrderRangeProofRejected);
        }
        let range_proof_bytes = range_proof.to_bytes();
        if range_proof_bytes.len() != OWNER_RANGE_PROOF_BYTES {
            return Err(DistributedInputError::InvalidOrderRangeProof);
        }
        let value_commitments = [commitments[0], commitments[2]];
        let range_component_digest =
            owner_range_component_digest(&value_commitments, &range_proof_bytes, &deal_digest);

        let width = values.len();
        let padded_width = width
            .checked_next_power_of_two()
            .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
        let owner_generators = owner_linear_generators(session, owner, padded_width)?;
        let owner_point = decode_point(&owner_commitment)?;
        let mut secret = values.to_vec();
        secret.resize(padded_width, Scalar::ZERO);

        let committed_scalar_count = owner_committed_scalar_count(session.degree)?;
        if committed_scalar_count + ROOT_BLINDING_WIDTH != width {
            return Err(DistributedInputError::InvalidOrderRangeProof);
        }

        let mut derived_blindings = Vec::with_capacity(committed_scalar_count);
        derived_blindings.push(kind_blinding);
        derived_blindings.push(quantity_blinding);
        for coordinate in 2..committed_scalar_count {
            derived_blindings.push(random_deal_scalar(
                rng,
                session.digest,
                owner,
                session.n_workers() + 2,
                coordinate,
                b"owner-derived-blinding",
            ));
        }
        let selector_transcript = owner_selector_transcript(
            session,
            owner,
            width,
            padded_width,
            &owner_commitment,
            share_commitments,
            &deal_digest,
            &range_component_digest,
        );
        let selector_pc_gens = R1csPedersenGens::default();
        let mut selector_prover =
            bulletproofs_r1cs::r1cs::Prover::new(&selector_pc_gens, selector_transcript);
        let mut derived_commitments = Vec::with_capacity(committed_scalar_count);
        let mut derived_variables = Vec::with_capacity(committed_scalar_count);
        for coordinate in 0..committed_scalar_count {
            let (commitment, variable) =
                selector_prover.commit(values[coordinate], derived_blindings[coordinate]);
            derived_commitments.push(commitment);
            derived_variables.push(variable);
        }
        if derived_commitments[..2] != value_commitments {
            return Err(DistributedInputError::OrderRangeProofRejected);
        }
        constrain_selector_message_relation(
            &mut selector_prover,
            &derived_variables,
            Some(&values[..committed_scalar_count]),
        )
        .map_err(|_| DistributedInputError::OrderRangeProofRejected)?;
        #[cfg(test)]
        let owned_selector_gens: R1csBulletproofGens;
        let selector_gens = if session.degree == BFV_DEGREE {
            &*OWNER_SELECTOR_GENS
        } else {
            #[cfg(test)]
            {
                owned_selector_gens =
                    R1csBulletproofGens::new(owner_r1cs_multiplier_capacity(session.degree)?, 1);
                &owned_selector_gens
            }
            #[cfg(not(test))]
            unreachable!("production distributed witnesses always use degree 4096")
        };
        let selector_proof = selector_prover
            .prove(selector_gens)
            .map_err(|_| DistributedInputError::OrderRangeProofRejected)?;
        let selector_proof_bytes = selector_proof.to_bytes();
        if selector_proof_bytes.len() != owner_selector_r1cs_proof_len(session.degree)? {
            return Err(DistributedInputError::InvalidOrderRangeProof);
        }

        let link_coefficients = owner_derived_link_coefficients(
            session,
            owner,
            &owner_commitment,
            &deal_digest,
            &range_component_digest,
            &derived_commitments,
            &selector_proof_bytes,
        );
        let derived_points = derived_commitments
            .iter()
            .map(|commitment| {
                commitment
                    .decompress()
                    .ok_or(DistributedInputError::InvalidOrderRangeProof)
            })
            .collect::<Result<Vec<_>>>()?;
        let batch_point = RistrettoPoint::multiscalar_mul(
            link_coefficients.iter().copied(),
            derived_points.iter(),
        );
        let statement = (owner_point + batch_point).compress();
        let mut public_coefficients = vec![Scalar::ZERO; padded_width];
        public_coefficients[..committed_scalar_count].copy_from_slice(&link_coefficients);
        let aggregate_blinding = owner_blinding
            + link_coefficients
                .iter()
                .zip(&derived_blindings)
                .fold(Scalar::ZERO, |sum, (coefficient, blinding)| {
                    sum + coefficient * blinding
                });
        let mut link_transcript = owner_link_transcript(
            session,
            owner,
            width,
            padded_width,
            &owner_commitment,
            &deal_digest,
            &range_component_digest,
            &derived_commitments,
            &selector_proof_bytes,
        );
        let link_proof = LinearProof::create(
            &mut link_transcript,
            rng,
            &statement,
            aggregate_blinding,
            secret,
            public_coefficients,
            owner_generators,
            &pc_gens.B,
            &pc_gens.B_blinding,
        )
        .map_err(|_| DistributedInputError::OrderRangeProofRejected)?
        .to_bytes();

        let bytes = encode_owner_range_artifact(
            owner,
            width,
            padded_width,
            deal_digest,
            &derived_commitments,
            &range_proof_bytes,
            &selector_proof_bytes,
            &link_proof,
        )?;
        let proof = Self { bytes };
        proof.verify(
            session,
            owner,
            owner_commitment,
            share_commitments,
            deal_digest,
        )?;
        Ok(proof)
    }

    fn verify(
        &self,
        session: &DistributedWitnessSession,
        owner: usize,
        owner_commitment: [u8; 32],
        share_commitments: &[[u8; 32]],
        deal_digest: [u8; 32],
    ) -> Result<()> {
        #[cfg(test)]
        OWNER_PROOF_VERIFICATION_CALLS.with(|count| count.set(count.get() + 1));

        let width = session.local_witness_width();
        let padded_width = width
            .checked_next_power_of_two()
            .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
        let committed_scalar_count = owner_committed_scalar_count(session.degree)?;
        let decoded =
            decode_owner_range_artifact(&self.bytes, owner, width, padded_width, deal_digest)?;
        let pc_gens = PedersenGens::default();
        let kind = decoded.derived_commitments[0]
            .decompress()
            .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
        let quantity = decoded.derived_commitments[1]
            .decompress()
            .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
        let range_commitments = [
            decoded.derived_commitments[0],
            (Scalar::from(7u64) * pc_gens.B - kind).compress(),
            decoded.derived_commitments[1],
            (Scalar::from(15u64) * pc_gens.B - quantity).compress(),
        ];
        let mut range_transcript = owner_range_transcript(
            session,
            owner,
            &owner_commitment,
            share_commitments,
            &deal_digest,
        );
        decoded
            .range_proof
            .verify_multiple(
                &BulletproofGens::new(OWNER_RANGE_BITS, OWNER_RANGE_VALUES),
                &pc_gens,
                &mut range_transcript,
                &range_commitments,
                OWNER_RANGE_BITS,
            )
            .map_err(|_| DistributedInputError::OrderRangeProofRejected)?;

        let owner_generators = owner_linear_generators(session, owner, padded_width)?;
        let owner_point = decode_point(&owner_commitment)?;
        let range_component_digest = owner_range_component_digest(
            &[
                decoded.derived_commitments[0],
                decoded.derived_commitments[1],
            ],
            &decoded.range_proof_bytes,
            &deal_digest,
        );

        let selector_transcript = owner_selector_transcript(
            session,
            owner,
            width,
            padded_width,
            &owner_commitment,
            share_commitments,
            &deal_digest,
            &range_component_digest,
        );
        let mut selector_verifier = bulletproofs_r1cs::r1cs::Verifier::new(selector_transcript);
        let derived_variables = decoded
            .derived_commitments
            .iter()
            .map(|commitment| selector_verifier.commit(*commitment))
            .collect::<Vec<_>>();
        constrain_selector_message_relation(&mut selector_verifier, &derived_variables, None)
            .map_err(|_| DistributedInputError::OrderRangeProofRejected)?;
        #[cfg(test)]
        let owned_selector_gens: R1csBulletproofGens;
        let selector_gens = if session.degree == BFV_DEGREE {
            &*OWNER_SELECTOR_GENS
        } else {
            #[cfg(test)]
            {
                owned_selector_gens =
                    R1csBulletproofGens::new(owner_r1cs_multiplier_capacity(session.degree)?, 1);
                &owned_selector_gens
            }
            #[cfg(not(test))]
            unreachable!("production distributed witnesses always use degree 4096")
        };
        selector_verifier
            .verify(
                &decoded.selector_proof,
                &R1csPedersenGens::default(),
                selector_gens,
            )
            .map_err(|_| DistributedInputError::OrderRangeProofRejected)?;

        let link_coefficients = owner_derived_link_coefficients(
            session,
            owner,
            &owner_commitment,
            &deal_digest,
            &range_component_digest,
            &decoded.derived_commitments,
            &decoded.selector_proof_bytes,
        );
        let derived_points = decoded
            .derived_commitments
            .iter()
            .map(|commitment| {
                commitment
                    .decompress()
                    .ok_or(DistributedInputError::InvalidOrderRangeProof)
            })
            .collect::<Result<Vec<_>>>()?;
        let batch_point = RistrettoPoint::multiscalar_mul(
            link_coefficients.iter().copied(),
            derived_points.iter(),
        );
        let statement = (owner_point + batch_point).compress();
        let mut public_coefficients = vec![Scalar::ZERO; padded_width];
        public_coefficients[..committed_scalar_count].copy_from_slice(&link_coefficients);
        let mut link_transcript = owner_link_transcript(
            session,
            owner,
            width,
            padded_width,
            &owner_commitment,
            &deal_digest,
            &range_component_digest,
            &decoded.derived_commitments,
            &decoded.selector_proof_bytes,
        );
        decoded
            .link_proof
            .verify(
                &mut link_transcript,
                &statement,
                &owner_generators,
                &pc_gens.B,
                &pc_gens.B_blinding,
                public_coefficients,
            )
            .map_err(|_| DistributedInputError::OrderRangeProofRejected)?;
        Ok(())
    }

    fn digest(&self) -> [u8; 32] {
        keyed_hash(OWNER_RANGE_ARTIFACT_DOMAIN, &self.bytes)
    }

    #[cfg(test)]
    fn corrupt_range_response_for_test(&mut self) {
        // Artifact header through the range-proof length is 120 bytes. The
        // range proof's first response scalar follows four compressed points.
        let response_start = OWNER_RANGE_ARTIFACT_HEADER_BYTES + 4 * 32;
        let original = Option::<Scalar>::from(Scalar::from_canonical_bytes(
            self.bytes[response_start..response_start + 32]
                .try_into()
                .expect("fixed response width"),
        ))
        .expect("honest proof response is canonical");
        self.bytes[response_start..response_start + 32]
            .copy_from_slice(&(original + Scalar::ONE).to_bytes());
        let checksum_start = self.bytes.len() - 32;
        let checksum = owner_range_artifact_checksum(&self.bytes[..checksum_start]);
        self.bytes[checksum_start..].copy_from_slice(&checksum);
    }

    #[cfg(test)]
    fn corrupt_selector_response_for_test(&mut self) {
        let width =
            u32::from_be_bytes(self.bytes[12..16].try_into().expect("artifact width")) as usize;
        let degree = degree_from_witness_width(width).expect("honest artifact degree");
        let extra_commitments =
            owner_committed_scalar_count(degree).expect("honest committed width") - 2;
        let proof_start = OWNER_RANGE_ARTIFACT_HEADER_BYTES
            + OWNER_RANGE_PROOF_BYTES
            + 2
            + extra_commitments * 32
            + 4;
        // One-phase R1CS encoding: version byte, eight compressed points, then
        // the first canonical response scalar.
        let response_start = proof_start + 1 + 8 * 32;
        let original = Option::<Scalar>::from(Scalar::from_canonical_bytes(
            self.bytes[response_start..response_start + 32]
                .try_into()
                .expect("fixed selector response width"),
        ))
        .expect("honest selector response is canonical");
        self.bytes[response_start..response_start + 32]
            .copy_from_slice(&(original + Scalar::ONE).to_bytes());
        self.refresh_checksum_for_test();
    }

    #[cfg(test)]
    fn substitute_selector_proof_for_test(&mut self, other: &Self) {
        let width =
            u32::from_be_bytes(self.bytes[12..16].try_into().expect("artifact width")) as usize;
        let degree = degree_from_witness_width(width).expect("honest artifact degree");
        let extra_commitments =
            owner_committed_scalar_count(degree).expect("honest committed width") - 2;
        let selector_proof_len = owner_selector_r1cs_proof_len(degree).expect("honest proof size");
        let proof_start = OWNER_RANGE_ARTIFACT_HEADER_BYTES
            + OWNER_RANGE_PROOF_BYTES
            + 2
            + extra_commitments * 32
            + 4;
        let proof_end = proof_start + selector_proof_len;
        self.bytes[proof_start..proof_end].copy_from_slice(&other.bytes[proof_start..proof_end]);
        self.refresh_checksum_for_test();
    }

    #[cfg(test)]
    fn corrupt_derived_link_response_for_test(&mut self) {
        let width =
            u32::from_be_bytes(self.bytes[12..16].try_into().expect("artifact width")) as usize;
        let degree = degree_from_witness_width(width).expect("honest artifact degree");
        let extra_commitments =
            owner_committed_scalar_count(degree).expect("honest committed width") - 2;
        let selector_proof_len = owner_selector_r1cs_proof_len(degree).expect("honest proof size");
        let link_proof_start = OWNER_RANGE_ARTIFACT_HEADER_BYTES
            + OWNER_RANGE_PROOF_BYTES
            + 2
            + extra_commitments * 32
            + 4
            + selector_proof_len
            + 2
            + 4;
        let link_proof_end = self.bytes.len() - 32;
        // LinearProof ends in canonical response scalars `a` and `r`.
        let response_start = link_proof_end - 2 * 32;
        debug_assert!(response_start >= link_proof_start);
        let original = Option::<Scalar>::from(Scalar::from_canonical_bytes(
            self.bytes[response_start..response_start + 32]
                .try_into()
                .expect("fixed link response width"),
        ))
        .expect("honest link response is canonical");
        self.bytes[response_start..response_start + 32]
            .copy_from_slice(&(original + Scalar::ONE).to_bytes());
        self.refresh_checksum_for_test();
    }

    #[cfg(test)]
    fn refresh_checksum_for_test(&mut self) {
        let checksum_start = self.bytes.len() - 32;
        let checksum = owner_range_artifact_checksum(&self.bytes[..checksum_start]);
        self.bytes[checksum_start..].copy_from_slice(&checksum);
    }
}

struct DecodedOwnerRangeArtifact {
    derived_commitments: Vec<CompressedRistretto>,
    range_proof: RangeProof,
    range_proof_bytes: Vec<u8>,
    selector_proof: R1CSProof,
    selector_proof_bytes: Vec<u8>,
    link_proof: LinearProof,
}

fn option_message_slots(kind: usize, quantity: usize) -> [u64; MESSAGE_SLOT_WIDTH] {
    debug_assert!(kind < KIND_COUNT && quantity < QUANTITY_COUNT);
    let mut slots = [0u64; MESSAGE_SLOT_WIDTH];
    if kind < PRICE_COUNT {
        for slot in slots.iter_mut().take(kind + 1) {
            *slot = quantity as u64;
        }
    } else {
        for slot in slots.iter_mut().take(2 * PRICE_COUNT).skip(kind) {
            *slot = quantity as u64;
        }
    }
    slots[2 * PRICE_COUNT] = kind as u64 + 8 * quantity as u64;
    slots
}

fn owner_committed_scalar_count(degree: usize) -> Result<usize> {
    DERIVED_ORDER_WIDTH
        .checked_add(
            3usize
                .checked_mul(degree)
                .ok_or(DistributedInputError::InvalidOrderRangeProof)?,
        )
        .ok_or(DistributedInputError::InvalidOrderRangeProof)
}

fn degree_from_witness_width(width: usize) -> Result<usize> {
    width
        .checked_sub(DERIVED_ORDER_WIDTH + ROOT_BLINDING_WIDTH)
        .filter(|remaining| remaining % 3 == 0)
        .map(|remaining| remaining / 3)
        .filter(|degree| *degree > 0 && *degree <= BFV_DEGREE)
        .ok_or(DistributedInputError::InvalidOrderRangeProof)
}

fn owner_r1cs_multiplier_capacity(degree: usize) -> Result<usize> {
    OPTION_COUNT
        .checked_add(
            OWNER_SHORT_RANGE_BITS
                .checked_mul(
                    3usize
                        .checked_mul(degree)
                        .ok_or(DistributedInputError::InvalidOrderRangeProof)?,
                )
                .ok_or(DistributedInputError::InvalidOrderRangeProof)?,
        )
        .and_then(usize::checked_next_power_of_two)
        .ok_or(DistributedInputError::InvalidOrderRangeProof)
}

fn owner_selector_r1cs_proof_len(degree: usize) -> Result<usize> {
    let capacity = owner_r1cs_multiplier_capacity(degree)?;
    (13usize)
        .checked_add(2 * capacity.trailing_zeros() as usize)
        .and_then(|elements| elements.checked_mul(32))
        .and_then(|bytes| bytes.checked_add(1))
        .ok_or(DistributedInputError::InvalidOrderRangeProof)
}

fn shifted_short_assignment(value: Scalar) -> Option<u64> {
    (0..(1u64 << OWNER_SHORT_RANGE_BITS))
        .find(|shifted| signed_scalar(*shifted as i64 - OWNER_SHORT_RANGE_SHIFT as i64) == value)
}

fn small_scalar(value: Scalar) -> Option<u64> {
    let bytes = value.to_bytes();
    if bytes[8..].iter().any(|byte| *byte != 0) {
        return None;
    }
    Some(u64::from_le_bytes(bytes[..8].try_into().ok()?))
}

fn owner_linear_generators(
    session: &DistributedWitnessSession,
    owner: usize,
    padded_width: usize,
) -> Result<Vec<RistrettoPoint>> {
    if owner >= ORDER_COUNT || !padded_width.is_power_of_two() {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    if session.degree == BFV_DEGREE {
        if padded_width != LOCAL_WITNESS_WIDTH.next_power_of_two() {
            return Err(DistributedInputError::InvalidOrderRangeProof);
        }
        return Ok(PRODUCTION_GENS
            .share(owner)
            .G(padded_width)
            .copied()
            .collect());
    }
    #[cfg(test)]
    {
        return Ok(BulletproofGens::new(padded_width, ORDER_COUNT)
            .share(owner)
            .G(padded_width)
            .copied()
            .collect());
    }
    #[cfg(not(test))]
    Err(DistributedInputError::InvalidOrderRangeProof)
}

fn owner_range_transcript(
    session: &DistributedWitnessSession,
    owner: usize,
    owner_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
    deal_digest: &[u8; 32],
) -> Transcript {
    let mut transcript = Transcript::new(OWNER_RANGE_TRANSCRIPT);
    transcript.append_message(b"layout", LAYOUT_ID);
    transcript.append_message(b"session", &session.digest());
    transcript.append_message(b"relation", &session.relation_digest());
    transcript.append_u64(b"owner", owner as u64);
    transcript.append_u64(b"degree", session.degree as u64);
    transcript.append_u64(b"width", session.local_witness_width() as u64);
    transcript.append_message(b"deal", deal_digest);
    transcript.append_message(b"owner-commitment", owner_commitment);
    transcript.append_u64(b"share-count", share_commitments.len() as u64);
    for commitment in share_commitments {
        transcript.append_message(b"share-commitment", commitment);
    }
    transcript
}

fn owner_range_component_digest(
    value_commitments: &[CompressedRistretto; 2],
    range_proof_bytes: &[u8],
    deal_digest: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(OWNER_RANGE_COMPONENT_DOMAIN);
    hasher.update(deal_digest);
    for commitment in value_commitments {
        hasher.update(commitment.as_bytes());
    }
    hasher.update(&(range_proof_bytes.len() as u64).to_be_bytes());
    hasher.update(range_proof_bytes);
    *hasher.finalize().as_bytes()
}

#[allow(clippy::too_many_arguments)]
fn owner_selector_transcript(
    session: &DistributedWitnessSession,
    owner: usize,
    width: usize,
    padded_width: usize,
    owner_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
    deal_digest: &[u8; 32],
    range_component_digest: &[u8; 32],
) -> Transcript {
    let mut transcript = Transcript::new(OWNER_SELECTOR_TRANSCRIPT);
    transcript.append_message(b"layout", LAYOUT_ID);
    transcript.append_message(b"session", &session.digest());
    transcript.append_message(b"relation", &session.relation_digest());
    transcript.append_u64(b"owner", owner as u64);
    transcript.append_u64(b"width", width as u64);
    transcript.append_u64(b"padded-width", padded_width as u64);
    transcript.append_u64(b"option-count", OPTION_COUNT as u64);
    transcript.append_u64(b"message-slot-width", MESSAGE_SLOT_WIDTH as u64);
    transcript.append_u64(
        b"committed-scalar-count",
        owner_committed_scalar_count(session.degree).expect("validated session width") as u64,
    );
    transcript.append_u64(b"short-range-bits", OWNER_SHORT_RANGE_BITS as u64);
    transcript.append_message(b"deal", deal_digest);
    transcript.append_message(b"owner-commitment", owner_commitment);
    transcript.append_u64(b"share-count", share_commitments.len() as u64);
    for commitment in share_commitments {
        transcript.append_message(b"share-commitment", commitment);
    }
    transcript.append_message(b"range-component", range_component_digest);
    transcript
}

fn constrain_selector_message_relation<CS: ConstraintSystem>(
    cs: &mut CS,
    variables: &[Variable],
    assignments: Option<&[Scalar]>,
) -> std::result::Result<(), bulletproofs_r1cs::r1cs::R1CSError> {
    if variables.len() < DERIVED_ORDER_WIDTH
        || (variables.len() - DERIVED_ORDER_WIDTH) % 3 != 0
        || assignments.is_some_and(|values| values.len() != variables.len())
    {
        return Err(bulletproofs_r1cs::r1cs::R1CSError::GadgetError {
            description: "private-book derived witness has the wrong width".to_owned(),
        });
    }
    let kind = variables[0];
    let quantity = variables[1];
    let selectors = &variables[2..2 + OPTION_COUNT];
    let message_slots = &variables[2 + OPTION_COUNT..DERIVED_ORDER_WIDTH];
    let mut selector_sum = LinearCombination::from(-Scalar::ONE);
    let mut kind_sum = LinearCombination::from(Scalar::ZERO);
    let mut quantity_sum = LinearCombination::from(Scalar::ZERO);
    let mut table_index_sum = LinearCombination::from(Scalar::ZERO);
    let mut slot_sums = (0..MESSAGE_SLOT_WIDTH)
        .map(|_| LinearCombination::from(Scalar::ZERO))
        .collect::<Vec<_>>();
    for (option, selector) in selectors.iter().copied().enumerate() {
        let (_, _, boolean_product) = cs.multiply(selector.into(), selector - Scalar::ONE);
        cs.constrain(boolean_product.into());
        let option_kind = option / QUANTITY_COUNT;
        let option_quantity = option % QUANTITY_COUNT;
        selector_sum = selector_sum + selector;
        kind_sum = kind_sum + selector * Scalar::from(option_kind as u64);
        quantity_sum = quantity_sum + selector * Scalar::from(option_quantity as u64);
        table_index_sum = table_index_sum + selector * Scalar::from(option as u64);
        for (slot, value) in option_message_slots(option_kind, option_quantity)
            .into_iter()
            .enumerate()
        {
            slot_sums[slot] = slot_sums[slot].clone() + selector * Scalar::from(value);
        }
    }
    cs.constrain(selector_sum);
    cs.constrain(kind - kind_sum);
    cs.constrain(quantity - quantity_sum);
    cs.constrain(table_index_sum - kind * Scalar::from(QUANTITY_COUNT as u64) - quantity);
    for (slot, expected) in message_slots.iter().zip(slot_sums) {
        cs.constrain(*slot - expected);
    }
    for (coordinate, variable) in variables
        .iter()
        .copied()
        .enumerate()
        .skip(DERIVED_ORDER_WIDTH)
    {
        let shifted = assignments.and_then(|values| shifted_short_assignment(values[coordinate]));
        range_lc(
            cs,
            variable + Scalar::from(OWNER_SHORT_RANGE_SHIFT),
            shifted,
            OWNER_SHORT_RANGE_BITS,
        )?;
    }
    Ok(())
}

fn bit<CS: ConstraintSystem>(
    cs: &mut CS,
    value: Option<u64>,
) -> std::result::Result<Variable, bulletproofs_r1cs::r1cs::R1CSError> {
    let assignment = value.map(Scalar::from);
    let (left, right, output) = cs.allocate_multiplier(assignment.zip(assignment))?;
    cs.constrain(left - right);
    cs.constrain(output - left);
    Ok(left)
}

fn range_lc<CS: ConstraintSystem>(
    cs: &mut CS,
    value_lc: LinearCombination,
    value: Option<u64>,
    bits: usize,
) -> std::result::Result<(), bulletproofs_r1cs::r1cs::R1CSError> {
    let mut bit_sum = LinearCombination::from(Scalar::ZERO);
    for index in 0..bits {
        let bit_value = value.map(|value| (value >> index) & 1);
        let variable = bit(cs, bit_value)?;
        bit_sum = bit_sum + variable * Scalar::from(1u64 << index);
    }
    cs.constrain(value_lc - bit_sum);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn owner_derived_link_coefficients(
    session: &DistributedWitnessSession,
    owner: usize,
    owner_commitment: &[u8; 32],
    deal_digest: &[u8; 32],
    range_component_digest: &[u8; 32],
    derived_commitments: &[CompressedRistretto],
    selector_proof_bytes: &[u8],
) -> Vec<Scalar> {
    let mut hasher = blake3::Hasher::new_derive_key(OWNER_LINK_CHALLENGE_DOMAIN);
    hasher.update(LAYOUT_ID);
    hasher.update(&session.digest());
    hasher.update(&session.relation_digest());
    hasher.update(&(owner as u64).to_be_bytes());
    hasher.update(owner_commitment);
    hasher.update(deal_digest);
    hasher.update(range_component_digest);
    hasher.update(&(derived_commitments.len() as u64).to_be_bytes());
    for commitment in derived_commitments {
        hasher.update(commitment.as_bytes());
    }
    hasher.update(&(selector_proof_bytes.len() as u64).to_be_bytes());
    hasher.update(selector_proof_bytes);
    let mut reader = hasher.finalize_xof();
    (0..derived_commitments.len())
        .map(|_| {
            loop {
                let mut candidate = [0u8; 32];
                reader.fill(&mut candidate);
                if let Some(coefficient) =
                    Option::<Scalar>::from(Scalar::from_canonical_bytes(candidate))
                {
                    // Canonical rejection sampling is exactly uniform over the
                    // field, including zero. Mapping zero to one would double
                    // the mass at one and invalidate the exact 1/|Scalar|
                    // random-linear-compression soundness account.
                    break coefficient;
                }
            }
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn owner_link_transcript(
    session: &DistributedWitnessSession,
    owner: usize,
    width: usize,
    padded_width: usize,
    owner_commitment: &[u8; 32],
    deal_digest: &[u8; 32],
    range_component_digest: &[u8; 32],
    derived_commitments: &[CompressedRistretto],
    selector_proof_bytes: &[u8],
) -> Transcript {
    let mut transcript = Transcript::new(OWNER_LINK_TRANSCRIPT);
    transcript.append_message(b"layout", LAYOUT_ID);
    transcript.append_message(b"session", &session.digest());
    transcript.append_message(b"relation", &session.relation_digest());
    transcript.append_u64(b"owner", owner as u64);
    transcript.append_u64(b"width", width as u64);
    transcript.append_u64(b"padded-width", padded_width as u64);
    transcript.append_message(b"deal", deal_digest);
    transcript.append_message(b"owner-commitment", owner_commitment);
    transcript.append_message(b"range-component", range_component_digest);
    transcript.append_u64(b"derived-count", derived_commitments.len() as u64);
    for commitment in derived_commitments {
        transcript.append_message(b"derived-commitment", commitment.as_bytes());
    }
    transcript.append_message(b"selector-proof", selector_proof_bytes);
    transcript
}

fn expected_owner_link_proof_len(padded_width: usize) -> Result<usize> {
    if !padded_width.is_power_of_two() {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    (2usize)
        .checked_mul(padded_width.trailing_zeros() as usize)
        .and_then(|value| value.checked_add(3))
        .and_then(|value| value.checked_mul(32))
        .ok_or(DistributedInputError::InvalidOrderRangeProof)
}

fn owner_range_artifact_wire_len(width: usize, padded_width: usize) -> Result<usize> {
    let degree = degree_from_witness_width(width)?;
    let committed_scalar_count = owner_committed_scalar_count(degree)?;
    let extra_commitments = committed_scalar_count
        .checked_sub(2)
        .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
    let selector_proof_len = owner_selector_r1cs_proof_len(degree)?;
    let link_len = expected_owner_link_proof_len(padded_width)?;
    // Header (including kind/quantity commitments), range proof, the remaining
    // derived scalar commitments, selector R1CS proof, one framed batch-link
    // proof, then the artifact checksum.
    OWNER_RANGE_ARTIFACT_HEADER_BYTES
        .checked_add(OWNER_RANGE_PROOF_BYTES)
        .and_then(|value| value.checked_add(2 + extra_commitments * 32))
        .and_then(|value| value.checked_add(4 + selector_proof_len))
        .and_then(|value| value.checked_add(2))
        .and_then(|value| value.checked_add(OWNER_LINK_PROOFS * (4 + link_len)))
        .and_then(|value| value.checked_add(32))
        .filter(|value| *value <= MAX_OWNER_RANGE_ARTIFACT_BYTES)
        .ok_or(DistributedInputError::InvalidOrderRangeProof)
}

fn owner_range_artifact_checksum(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(OWNER_RANGE_CHECKSUM_DOMAIN);
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn encode_owner_range_artifact(
    owner: usize,
    width: usize,
    padded_width: usize,
    deal_digest: [u8; 32],
    derived_commitments: &[CompressedRistretto],
    range_proof_bytes: &[u8],
    selector_proof_bytes: &[u8],
    link_proof: &[u8],
) -> Result<Vec<u8>> {
    let degree = degree_from_witness_width(width)?;
    let committed_scalar_count = owner_committed_scalar_count(degree)?;
    let extra_commitments = committed_scalar_count
        .checked_sub(2)
        .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
    let selector_proof_len = owner_selector_r1cs_proof_len(degree)?;
    let expected_len = owner_range_artifact_wire_len(width, padded_width)?;
    let expected_link_len = expected_owner_link_proof_len(padded_width)?;
    if owner >= ORDER_COUNT
        || owner > u16::MAX as usize
        || width > u32::MAX as usize
        || padded_width > u32::MAX as usize
        || width == 0
        || padded_width < width
        || derived_commitments.len() != committed_scalar_count
        || range_proof_bytes.len() != OWNER_RANGE_PROOF_BYTES
        || selector_proof_bytes.len() != selector_proof_len
        || link_proof.len() != expected_link_len
        || derived_commitments.iter().any(|commitment| {
            commitment
                .decompress()
                .is_none_or(|point| point.compress() != *commitment)
        })
    {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    let mut out = Vec::with_capacity(expected_len);
    out.extend_from_slice(OWNER_RANGE_ARTIFACT_MAGIC);
    out.extend_from_slice(&OWNER_RANGE_ARTIFACT_VERSION.to_be_bytes());
    out.extend_from_slice(&(owner as u16).to_be_bytes());
    out.extend_from_slice(&(width as u32).to_be_bytes());
    out.extend_from_slice(&(padded_width as u32).to_be_bytes());
    out.extend_from_slice(&deal_digest);
    for commitment in &derived_commitments[..2] {
        out.extend_from_slice(commitment.as_bytes());
    }
    out.extend_from_slice(&(range_proof_bytes.len() as u32).to_be_bytes());
    out.extend_from_slice(range_proof_bytes);
    out.extend_from_slice(&(extra_commitments as u16).to_be_bytes());
    for commitment in &derived_commitments[2..] {
        out.extend_from_slice(commitment.as_bytes());
    }
    out.extend_from_slice(&(selector_proof_bytes.len() as u32).to_be_bytes());
    out.extend_from_slice(selector_proof_bytes);
    out.extend_from_slice(&(OWNER_LINK_PROOFS as u16).to_be_bytes());
    out.extend_from_slice(&(link_proof.len() as u32).to_be_bytes());
    out.extend_from_slice(link_proof);
    let checksum = owner_range_artifact_checksum(&out);
    out.extend_from_slice(&checksum);
    if out.len() != expected_len {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    Ok(out)
}

fn decode_owner_range_artifact(
    bytes: &[u8],
    owner: usize,
    width: usize,
    padded_width: usize,
    deal_digest: [u8; 32],
) -> Result<DecodedOwnerRangeArtifact> {
    let degree = degree_from_witness_width(width)?;
    let committed_scalar_count = owner_committed_scalar_count(degree)?;
    let extra_commitments = committed_scalar_count
        .checked_sub(2)
        .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
    if bytes.len() != owner_range_artifact_wire_len(width, padded_width)? {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    let checksum_start = bytes
        .len()
        .checked_sub(32)
        .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
    if bytes[checksum_start..] != owner_range_artifact_checksum(&bytes[..checksum_start]) {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    let mut reader = OwnerRangeReader::new(&bytes[..checksum_start]);
    if reader.take::<8>()? != *OWNER_RANGE_ARTIFACT_MAGIC
        || u16::from_be_bytes(reader.take::<2>()?) != OWNER_RANGE_ARTIFACT_VERSION
        || u16::from_be_bytes(reader.take::<2>()?) as usize != owner
        || u32::from_be_bytes(reader.take::<4>()?) as usize != width
        || u32::from_be_bytes(reader.take::<4>()?) as usize != padded_width
        || reader.take::<32>()? != deal_digest
    {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    let mut derived_commitments = Vec::with_capacity(committed_scalar_count);
    derived_commitments.extend([
        canonical_owner_range_point(reader.take::<32>()?)?,
        canonical_owner_range_point(reader.take::<32>()?)?,
    ]);
    let range_len = u32::from_be_bytes(reader.take::<4>()?) as usize;
    if range_len != OWNER_RANGE_PROOF_BYTES {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    let range_proof_bytes = reader.take_slice(range_len)?.to_vec();
    let range_proof = RangeProof::from_bytes(&range_proof_bytes)
        .map_err(|_| DistributedInputError::InvalidOrderRangeProof)?;
    if u16::from_be_bytes(reader.take::<2>()?) as usize != extra_commitments {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    for _ in 0..extra_commitments {
        derived_commitments.push(canonical_owner_range_point(reader.take::<32>()?)?);
    }
    let selector_proof_len = u32::from_be_bytes(reader.take::<4>()?) as usize;
    if selector_proof_len != owner_selector_r1cs_proof_len(degree)? {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    let selector_proof_bytes = reader.take_slice(selector_proof_len)?.to_vec();
    let selector_proof = R1CSProof::from_bytes(&selector_proof_bytes)
        .map_err(|_| DistributedInputError::InvalidOrderRangeProof)?;
    if selector_proof.to_bytes() != selector_proof_bytes {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    if u16::from_be_bytes(reader.take::<2>()?) as usize != OWNER_LINK_PROOFS {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    let expected_link_len = expected_owner_link_proof_len(padded_width)?;
    let link_len = u32::from_be_bytes(reader.take::<4>()?) as usize;
    if link_len != expected_link_len {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    let link_proof = LinearProof::from_bytes(reader.take_slice(link_len)?)
        .map_err(|_| DistributedInputError::InvalidOrderRangeProof)?;
    reader.finish()?;
    Ok(DecodedOwnerRangeArtifact {
        derived_commitments,
        range_proof,
        range_proof_bytes,
        selector_proof,
        selector_proof_bytes,
        link_proof,
    })
}

fn canonical_owner_range_point(bytes: [u8; 32]) -> Result<CompressedRistretto> {
    let compressed = CompressedRistretto(bytes);
    let point = compressed
        .decompress()
        .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
    if point.compress() != compressed {
        return Err(DistributedInputError::InvalidOrderRangeProof);
    }
    Ok(compressed)
}

struct OwnerRangeReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> OwnerRangeReader<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.take_slice(N)?
            .try_into()
            .map_err(|_| DistributedInputError::InvalidOrderRangeProof)
    }

    fn take_slice(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(DistributedInputError::InvalidOrderRangeProof)?;
        self.offset = end;
        Ok(value)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(DistributedInputError::InvalidOrderRangeProof)
        }
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
    order_range_proof: OwnerOrderRangeProof,
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
        let range_proof_digest = self.order_range_proof.digest();
        let key = VerifyingKey::from_bytes(
            &session
                .owner_key(self.owner)
                .ok_or(DistributedInputError::PartyOutOfRange)?,
        )
        .map_err(|_| DistributedInputError::InvalidSignature)?;
        key.verify_strict(
            &deal_signing_message(&self.digest, &range_proof_digest),
            &Signature::from_bytes(&self.signature),
        )
        .map_err(|_| DistributedInputError::InvalidSignature)?;
        // Proof parsing and verification are deliberately after cheap roster,
        // commitment, digest, and signature checks. Unauthenticated network
        // input must not reach the range/R1CS/16k-vector proof work.
        self.order_range_proof.verify(
            session,
            self.owner,
            self.owner_commitment,
            &self.share_commitments,
            self.digest,
        )
    }

    #[cfg(test)]
    pub(crate) fn corrupt_share_commitment_for_test(&mut self, worker: usize) {
        self.share_commitments[worker][0] ^= 1;
    }

    #[cfg(test)]
    pub(crate) fn corrupt_owner_signature_for_test(&mut self) {
        self.signature[0] ^= 1;
    }

    #[cfg(test)]
    pub(crate) fn corrupt_range_proof_and_resign_for_test(&mut self, signing_key: &SigningKey) {
        self.order_range_proof.corrupt_range_response_for_test();
        self.resign_for_test(signing_key);
    }

    #[cfg(test)]
    pub(crate) fn corrupt_selector_proof_and_resign_for_test(&mut self, signing_key: &SigningKey) {
        self.order_range_proof.corrupt_selector_response_for_test();
        self.resign_for_test(signing_key);
    }

    #[cfg(test)]
    pub(crate) fn corrupt_derived_link_and_resign_for_test(&mut self, signing_key: &SigningKey) {
        self.order_range_proof
            .corrupt_derived_link_response_for_test();
        self.resign_for_test(signing_key);
    }

    #[cfg(test)]
    pub(crate) fn substitute_selector_proof_and_resign_for_test(
        &mut self,
        other: &Self,
        signing_key: &SigningKey,
    ) {
        self.order_range_proof
            .substitute_selector_proof_for_test(&other.order_range_proof);
        self.resign_for_test(signing_key);
    }

    #[cfg(test)]
    fn resign_for_test(&mut self, signing_key: &SigningKey) {
        self.signature = signing_key
            .sign(&deal_signing_message(
                &self.digest,
                &self.order_range_proof.digest(),
            ))
            .to_bytes();
    }

    #[cfg(test)]
    pub(crate) fn order_range_proof_len_for_test(&self) -> usize {
        self.order_range_proof.bytes.len()
    }
}

/// One private packet plus its public contribution.
pub struct DealerOutput {
    pub contribution: DealerContribution,
    pub private_packets: Vec<PrivateWitnessShare>,
    /// Owner-local continuation consumed only after the base certificate fixes
    /// the exact-BFV coefficient challenge. It never enters the coordinator or
    /// worker packet surface.
    pub continuation: OwnerWitnessContinuation,
}

/// Owner-retained committed witness used to derive post-challenge BFV integer
/// quotients without reconstructing any other owner's order or randomness.
///
/// This capability intentionally has no `Clone`, `Debug`, or wire codec.
pub struct OwnerWitnessContinuation {
    session_digest: [u8; 32],
    owner: usize,
    values: Vec<Scalar>,
}

impl OwnerWitnessContinuation {
    pub const fn owner(&self) -> usize {
        self.owner
    }

    pub(crate) const fn session_digest(&self) -> [u8; 32] {
        self.session_digest
    }

    pub(crate) fn values(&self) -> &[Scalar] {
        &self.values
    }
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
/// distribution and of the linked hidden order-domain, one-hot selector,
/// nine-slot semantic message, and bounded BFV-shortness subrelation. It is not
/// evidence that the remaining Poseidon, BFV polynomial-opening, or clearing
/// relation is satisfied.
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

    /// Commitment to one worker's additive share of one owner vector.
    ///
    /// This is crate-private because the public certificate wire remains the
    /// canonical API; the distributed BFV continuation uses it to assemble a
    /// worker's cross-owner relation-proof statement without opening shares.
    pub(crate) fn share_commitment(&self, owner: usize, worker: usize) -> Option<[u8; 32]> {
        self.dealers
            .get(owner)
            .and_then(|dealer| dealer.share_commitments.get(worker))
            .copied()
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
        if bytes.len() != certificate_wire_len(session.degree, session.n_workers())? {
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
            let range_proof_len = input.usize_u32()?;
            let width = session.local_witness_width();
            let padded_width = width
                .checked_next_power_of_two()
                .ok_or(DistributedInputError::MalformedCertificate)?;
            if range_proof_len != owner_range_artifact_wire_len(width, padded_width)? {
                return Err(DistributedInputError::MalformedCertificate);
            }
            let order_range_proof = OwnerOrderRangeProof {
                bytes: input.take_slice(range_proof_len)?.to_vec(),
            };
            let signature = input.take::<64>()?;
            dealers.push(DealerContribution {
                session_digest,
                owner,
                owner_commitment,
                share_commitments,
                digest,
                order_range_proof,
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
            certificate_wire_len(self.degree, self.n_workers)
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
            out.extend_from_slice(&(dealer.order_range_proof.bytes.len() as u32).to_be_bytes());
            out.extend_from_slice(&dealer.order_range_proof.bytes);
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
    hasher.update(&(OPTION_COUNT as u64).to_be_bytes());
    hasher.update(&(MESSAGE_SLOT_WIDTH as u64).to_be_bytes());
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

fn deal_signing_message(digest: &[u8; 32], range_proof_digest: &[u8; 32]) -> Vec<u8> {
    let mut message =
        Vec::with_capacity(DEAL_SIGNATURE_DOMAIN.len() + digest.len() + range_proof_digest.len());
    message.extend_from_slice(DEAL_SIGNATURE_DOMAIN);
    message.extend_from_slice(digest);
    message.extend_from_slice(range_proof_digest);
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
    debug_assert_eq!(
        values.len(),
        DERIVED_ORDER_WIDTH + 3 * degree + ROOT_BLINDING_WIDTH
    );
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

fn certificate_wire_len(degree: usize, workers: usize) -> Result<usize> {
    if degree == 0 || degree > BFV_DEGREE || !(2..=MAX_WORKERS).contains(&workers) {
        return Err(DistributedInputError::MalformedCertificate);
    }
    let width = degree
        .checked_mul(3)
        .and_then(|value| value.checked_add(DERIVED_ORDER_WIDTH + ROOT_BLINDING_WIDTH))
        .ok_or(DistributedInputError::MalformedCertificate)?;
    let padded_width = width
        .checked_next_power_of_two()
        .ok_or(DistributedInputError::MalformedCertificate)?;
    let range_artifact = owner_range_artifact_wire_len(width, padded_width)
        .map_err(|_| DistributedInputError::MalformedCertificate)?;
    let header = 8usize + 32 + 4 + 2 + 2;
    let dealer = 2usize + 32 + workers * 32 + 32 + 4 + range_artifact + 64;
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
        self.take_slice(N)?
            .try_into()
            .map_err(|_| DistributedInputError::MalformedCertificate)
    }

    fn take_slice(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|&end| end <= self.bytes.len())
            .ok_or(DistributedInputError::MalformedCertificate)?;
        let value = &self.bytes[self.offset..end];
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

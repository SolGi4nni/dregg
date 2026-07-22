//! Exact-BFV continuation of the distributed private-book input ceremony.
//!
//! The module is being built as a separate, versioned second phase so the
//! already-gated base-input certificate remains independently verifiable.

use std::fmt;
use std::iter;
use std::sync::{Arc, LazyLock};

#[cfg(test)]
use std::cell::Cell;

use bulletproofs_r1cs::r1cs::{ConstraintSystem, LinearCombination, R1CSProof};
use bulletproofs_r1cs::{
    BulletproofGens, BulletproofGens as R1csBulletproofGens, LinearProof, PedersenGens,
    PedersenGens as R1csPedersenGens,
};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use merlin::Transcript;
use rand::{CryptoRng, RngCore};

use crate::private_book_bfv_exact::{self, ExactBfvBatchEquation, ExactBfvPublicRelation};
use crate::private_book_distributed_inputs::{
    DistributedInputCertificate, DistributedWitnessSession, OwnerWitnessContinuation,
    PreparedWitnessShare, BFV_DEGREE, DERIVED_ORDER_WIDTH, ORDER_COUNT, ROOT_BLINDING_WIDTH,
};
use crate::private_book_distributed_root::RootLinkCertificate;
use crate::private_book_relation::PrivateBookCiphertexts;
use crate::threshold::{BfvParams, CollectivePublicKey};
use dregg_circuit_prove::dark_bazaar_private::PublicStatement;

/// Number of independent Rademacher compressions for each RNS modulus.
pub const BFV_COMPRESSION_ROUNDS: usize = private_book_bfv_exact::COMPRESSION_ROUNDS;
/// Number of RNS moduli in the deployed BFV fold set.
pub const BFV_RNS_MODULI: usize =
    private_book_bfv_exact::OWNER_BATCH_EQUATION_COUNT / BFV_COMPRESSION_ROUNDS;
/// Number of signed integer quotient witnesses supplied by each owner.
pub const OWNER_BFV_QUOTIENT_COUNT: usize = private_book_bfv_exact::OWNER_BATCH_EQUATION_COUNT;
/// Bit width used by the monolithic exact relation for shifted signed quotients.
pub const BFV_QUOTIENT_BITS: usize = private_book_bfv_exact::QUOTIENT_BITS;
/// Signed interval represented by the 24-bit shifted range gadget.
pub const BFV_QUOTIENT_SHIFT: i64 = 1 << (BFV_QUOTIENT_BITS - 1);
/// Existing conservative exact-integer bound retained from the monolithic proof.
pub const MAX_ABS_BFV_BATCH_QUOTIENT: i64 = private_book_bfv_exact::MAX_ABS_BATCH_QUOTIENT;

const ROUND_DOMAIN: &str = "fhegg/private-book-distributed-bfv/round/v1";
const FIRST_CHALLENGE_DOMAIN: &str = "fhegg/private-book-distributed-bfv/coefficient-challenge/v1";
const QUOTIENT_SHARE_DOMAIN: &str = "fhegg/private-book-distributed-bfv/quotient-share/v1";
const QUOTIENT_BLIND_DOMAIN: &str = "fhegg/private-book-distributed-bfv/quotient-blind/v1";
const DEAL_DOMAIN: &str = "fhegg/private-book-distributed-bfv/deal/v1";
const DEAL_SIGNATURE_DOMAIN: &[u8] = b"fhegg/private-book-distributed-bfv/deal-signature/v1";
const ACK_SIGNATURE_DOMAIN: &[u8] = b"fhegg/private-book-distributed-bfv/ack-signature/v1";
const PROOF_TRANSCRIPT: &[u8] = b"fhegg/private-book-distributed-bfv/quotient-r1cs/v1";
const LINK_TRANSCRIPT: &[u8] = b"fhegg/private-book-distributed-bfv/quotient-link/v1";
const LINK_CHALLENGE_DOMAIN: &str = "fhegg/private-book-distributed-bfv/quotient-link-challenge/v1";
const PROOF_DIGEST_DOMAIN: &str = "fhegg/private-book-distributed-bfv/proof-digest/v1";
const CERTIFICATE_DOMAIN: &str = "fhegg/private-book-distributed-bfv/certificate/v1";
const RELATION_ROUND_DOMAIN: &str = "fhegg/private-book-distributed-bfv/relation-round/v1";
const SECOND_CHALLENGE_DOMAIN: &str = "fhegg/private-book-distributed-bfv/relation-challenge/v1";
const RELATION_ALPHA_DOMAIN: &str = "fhegg/private-book-distributed-bfv/relation-alpha/v1";
const WORKER_RELATION_TRANSCRIPT: &[u8] = b"fhegg/private-book-distributed-bfv/worker-relation/v1";
const WORKER_RELATION_PROOF_DOMAIN: &str =
    "fhegg/private-book-distributed-bfv/worker-relation-proof/v1";
const WORKER_RELATION_SIGNATURE_DOMAIN: &[u8] =
    b"fhegg/private-book-distributed-bfv/worker-relation-signature/v1";
const RELATION_CERTIFICATE_DOMAIN: &str =
    "fhegg/private-book-distributed-bfv/relation-certificate/v1";
const QUOTIENT_CERTIFICATE_CHECKSUM_DOMAIN: &str =
    "fhegg/private-book-distributed-bfv/quotient-certificate-checksum/v1";
const RELATION_CERTIFICATE_CHECKSUM_DOMAIN: &str =
    "fhegg/private-book-distributed-bfv/relation-certificate-checksum/v1";
const ENVELOPE_DOMAIN: &str = "fhegg/private-book-distributed-bfv/public-envelope/v2-root-bound";
const ENVELOPE_CHECKSUM_DOMAIN: &str =
    "fhegg/private-book-distributed-bfv/public-envelope-checksum/v2-root-bound";
const QUOTIENT_CERTIFICATE_MAGIC: &[u8; 8] = b"FHQCT001";
const WORKER_RELATION_PROOF_MAGIC: &[u8; 8] = b"FHRWP001";
const RELATION_CERTIFICATE_MAGIC: &[u8; 8] = b"FHRLC001";
const ENVELOPE_MAGIC: &[u8; 8] = b"FHDBE002";
const PUBLIC_WIRE_VERSION: u16 = 1;
const ENVELOPE_WIRE_VERSION: u16 = 2;
const WORKER_RELATION_PROOF_CHECKSUM_DOMAIN: &str =
    "fhegg/private-book-distributed-bfv/worker-relation-wire-checksum/v1";

const PADDED_QUOTIENT_COUNT: usize = OWNER_BFV_QUOTIENT_COUNT.next_power_of_two();
const QUOTIENT_R1CS_CAPACITY: usize =
    (OWNER_BFV_QUOTIENT_COUNT * BFV_QUOTIENT_BITS).next_power_of_two();
const PRODUCTION_OWNER_BFV_BLOCK_WIDTH: usize = 16_384;

static QUOTIENT_R1CS_GENS: LazyLock<R1csBulletproofGens> =
    LazyLock::new(|| R1csBulletproofGens::new(QUOTIENT_R1CS_CAPACITY, 1));
static PRODUCTION_BFV_GENS: LazyLock<BulletproofGens> =
    LazyLock::new(|| BulletproofGens::new(PRODUCTION_OWNER_BFV_BLOCK_WIDTH, ORDER_COUNT));

const _: () = assert!(
    DERIVED_ORDER_WIDTH + 3 * BFV_DEGREE + ROOT_BLINDING_WIDTH + OWNER_BFV_QUOTIENT_COUNT
        <= PRODUCTION_OWNER_BFV_BLOCK_WIDTH
);

#[cfg(test)]
thread_local! {
    static QUOTIENT_PROOF_VERIFICATION_CALLS: Cell<usize> = const { Cell::new(0) };
    static RELATION_PROOF_VERIFICATION_CALLS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
fn reset_quotient_proof_verification_count() {
    QUOTIENT_PROOF_VERIFICATION_CALLS.with(|count| count.set(0));
}

#[cfg(test)]
fn quotient_proof_verification_count() -> usize {
    QUOTIENT_PROOF_VERIFICATION_CALLS.with(Cell::get)
}

#[cfg(test)]
fn reset_relation_proof_verification_count() {
    RELATION_PROOF_VERIFICATION_CALLS.with(|count| count.set(0));
}

#[cfg(test)]
fn relation_proof_verification_count() -> usize {
    RELATION_PROOF_VERIFICATION_CALLS.with(Cell::get)
}

type Result<T> = std::result::Result<T, DistributedBfvError>;

/// Fail-closed errors from the post-base-certificate exact-BFV phase.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DistributedBfvError {
    BaseCertificateRejected,
    SessionMismatch,
    PartyOutOfRange,
    SigningKeyMismatch,
    InvalidQuotientCount,
    QuotientOutOfRange,
    InvalidCommitment,
    CommitmentMismatch,
    InvalidSignature,
    InvalidProof,
    ProofRejected,
    DuplicateDealer,
    MissingDealers,
    DuplicateAcknowledgement,
    MissingAcknowledgements,
    RecipientMismatch,
    CertificateMismatch,
    ExactPublicRelation,
    ExactRelationMismatch,
    DuplicateWorkerProof,
    MissingWorkerProofs,
    RelationRejected,
    RootLinkRejected,
    MalformedWire,
    IntegerOverflow,
}

impl fmt::Display for DistributedBfvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::BaseCertificateRejected => "base distributed-input certificate was rejected",
            Self::SessionMismatch => "distributed BFV phase/session mismatch",
            Self::PartyOutOfRange => "distributed BFV party index is out of range",
            Self::SigningKeyMismatch => "distributed BFV signing key does not match the roster",
            Self::InvalidQuotientCount => "distributed BFV quotient count is not canonical",
            Self::QuotientOutOfRange => "distributed BFV quotient exceeded the pinned bound",
            Self::InvalidCommitment => "distributed BFV quotient commitment is malformed",
            Self::CommitmentMismatch => "distributed BFV quotient commitment does not open",
            Self::InvalidSignature => "distributed BFV signature is invalid",
            Self::InvalidProof => "distributed BFV quotient proof is malformed",
            Self::ProofRejected => "distributed BFV quotient proof was rejected",
            Self::DuplicateDealer => "duplicate distributed BFV owner contribution",
            Self::MissingDealers => "distributed BFV owner contributions are incomplete",
            Self::DuplicateAcknowledgement => "duplicate distributed BFV worker acknowledgement",
            Self::MissingAcknowledgements => {
                "distributed BFV worker acknowledgements are incomplete"
            }
            Self::RecipientMismatch => "distributed BFV private packet has the wrong recipient",
            Self::CertificateMismatch => "distributed BFV certificate transcript mismatch",
            Self::ExactPublicRelation => "exact deployed BFV public relation was rejected",
            Self::ExactRelationMismatch => {
                "owner witness does not satisfy an exact compressed BFV equation"
            }
            Self::DuplicateWorkerProof => "duplicate distributed BFV worker relation proof",
            Self::MissingWorkerProofs => "distributed BFV worker relation proofs are incomplete",
            Self::RelationRejected => "distributed BFV collapsed exact relation was rejected",
            Self::RootLinkRejected => {
                "distributed BFV owner vectors do not open the clearing Poseidon root"
            }
            Self::MalformedWire => "distributed BFV public wire is malformed or non-canonical",
            Self::IntegerOverflow => "exact distributed BFV integer evaluation overflowed",
        };
        f.write_str(message)
    }
}

impl std::error::Error for DistributedBfvError {}

/// Public first-phase context.  Its coefficient challenge is sampled only
/// after the complete v4 input certificate and its joint commitment are fixed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedBfvRound {
    session: DistributedWitnessSession,
    input_certificate_digest: [u8; 32],
    joint_input_commitment: [u8; 32],
    digest: [u8; 32],
    coefficient_challenge: [u8; 32],
}

/// Independently derived deployed BFV public relation shared by all four
/// owners and every proof worker. Its coefficient table is never accepted
/// from a prover.
#[derive(Clone)]
pub struct DistributedBfvPublicRelation {
    exact: ExactBfvPublicRelation,
}

impl DistributedBfvPublicRelation {
    pub fn derive(
        statement: PublicStatement,
        ciphertexts: &PrivateBookCiphertexts,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
    ) -> Result<Self> {
        Ok(Self {
            exact: ExactBfvPublicRelation::derive(statement, ciphertexts, params, public_key)
                .map_err(|_| DistributedBfvError::ExactPublicRelation)?,
        })
    }

    pub const fn relation_digest(&self) -> [u8; 32] {
        self.exact.relation_digest()
    }

    /// Exact statement already bound into the independently derived public
    /// coefficient family. Same-opening continuation verifiers must obtain the
    /// root statement here rather than accepting a parallel caller value.
    pub const fn statement(&self) -> PublicStatement {
        self.exact.statement()
    }
}

impl DistributedBfvRound {
    pub fn new(
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        if session.relation_digest() != public_relation.relation_digest() {
            return Err(DistributedBfvError::ExactPublicRelation);
        }
        input_certificate
            .verify(session)
            .map_err(|_| DistributedBfvError::BaseCertificateRejected)?;
        Self::new_after_verified_input(session, input_certificate)
    }

    #[cfg(test)]
    fn new_for_test(
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
    ) -> Result<Self> {
        input_certificate
            .verify(session)
            .map_err(|_| DistributedBfvError::BaseCertificateRejected)?;
        Self::new_after_verified_input(session, input_certificate)
    }

    fn new_after_verified_input(
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
    ) -> Result<Self> {
        let input_certificate_digest = input_certificate.transcript_digest();
        let joint_input_commitment = input_certificate
            .joint_input_commitment()
            .map_err(|_| DistributedBfvError::BaseCertificateRejected)?;
        let digest = hash_parts(
            ROUND_DOMAIN,
            &[
                session.digest().as_slice(),
                session.relation_digest().as_slice(),
                input_certificate_digest.as_slice(),
                joint_input_commitment.as_slice(),
                (session.degree() as u64).to_be_bytes().as_slice(),
                (BFV_RNS_MODULI as u64).to_be_bytes().as_slice(),
                (BFV_COMPRESSION_ROUNDS as u64).to_be_bytes().as_slice(),
                (BFV_QUOTIENT_BITS as u64).to_be_bytes().as_slice(),
                MAX_ABS_BFV_BATCH_QUOTIENT.to_be_bytes().as_slice(),
            ],
        );
        let coefficient_challenge = hash_parts(
            FIRST_CHALLENGE_DOMAIN,
            &[
                digest.as_slice(),
                input_certificate_digest.as_slice(),
                joint_input_commitment.as_slice(),
            ],
        );
        Ok(Self {
            session: session.clone(),
            input_certificate_digest,
            joint_input_commitment,
            digest,
            coefficient_challenge,
        })
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub const fn coefficient_challenge(&self) -> [u8; 32] {
        self.coefficient_challenge
    }

    pub const fn input_certificate_digest(&self) -> [u8; 32] {
        self.input_certificate_digest
    }

    pub const fn joint_input_commitment(&self) -> [u8; 32] {
        self.joint_input_commitment
    }

    pub const fn degree(&self) -> usize {
        self.session.degree()
    }

    pub fn n_workers(&self) -> usize {
        self.session.n_workers()
    }
}

/// One owner's exact integer quotients for the transcript-compressed BFV rows.
///
/// This capability deliberately has no wire encoding: the owner consumes it
/// into signed, range-proved additive shares.  The final worker relation—not
/// constructor honesty—binds these values to the committed BFV witness.
pub struct OwnerBfvQuotients {
    round_digest: [u8; 32],
    owner: usize,
    values: Vec<i64>,
}

impl OwnerBfvQuotients {
    fn from_values(round: &DistributedBfvRound, owner: usize, values: Vec<i64>) -> Result<Self> {
        if owner >= ORDER_COUNT {
            return Err(DistributedBfvError::PartyOutOfRange);
        }
        if values.len() != OWNER_BFV_QUOTIENT_COUNT {
            return Err(DistributedBfvError::InvalidQuotientCount);
        }
        if values
            .iter()
            .any(|value| value.unsigned_abs() > MAX_ABS_BFV_BATCH_QUOTIENT as u64)
        {
            return Err(DistributedBfvError::QuotientOutOfRange);
        }
        Ok(Self {
            round_digest: round.digest,
            owner,
            values,
        })
    }

    /// Derive the only production quotient witness from the owner-retained
    /// base opening and independently supplied deployed BFV public relation.
    /// Every one of the 384 integer numerators must divide its pinned RNS
    /// modulus exactly before any quotient is shared.
    pub fn derive_exact(
        round: &DistributedBfvRound,
        continuation: OwnerWitnessContinuation,
        public: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        if continuation.session_digest() != round.session.digest()
            || continuation.owner() >= ORDER_COUNT
            || continuation.values().len() != base_witness_width(round.degree())?
        {
            return Err(DistributedBfvError::SessionMismatch);
        }
        if public.relation_digest() != round.session.relation_digest() {
            return Err(DistributedBfvError::ExactPublicRelation);
        }
        let owner = continuation.owner();
        let equations = public
            .exact
            .owner_batch_equations(&round.coefficient_challenge, owner, round.degree())
            .map_err(|_| DistributedBfvError::ExactPublicRelation)?;
        let values = evaluate_exact_quotients(continuation.values(), round.degree(), &equations)?;
        Self::from_values(round, owner, values)
    }

    pub const fn owner(&self) -> usize {
        self.owner
    }

    /// Range-prove, commitment-bind, and n-of-n share the owner quotients.
    pub fn deal<R: CryptoRng + RngCore>(
        self,
        round: &DistributedBfvRound,
        signing_key: &SigningKey,
        rng: &mut R,
    ) -> Result<BfvQuotientDealerOutput> {
        if self.round_digest != round.digest {
            return Err(DistributedBfvError::SessionMismatch);
        }
        let expected_key = round
            .session
            .owner_key(self.owner)
            .ok_or(DistributedBfvError::PartyOutOfRange)?;
        if signing_key.verifying_key().to_bytes() != expected_key {
            return Err(DistributedBfvError::SigningKeyMismatch);
        }
        let scalar_values = self
            .values
            .iter()
            .copied()
            .map(signed_scalar)
            .collect::<Vec<_>>();
        let workers = round.n_workers();
        let mut shares = (0..workers)
            .map(|_| vec![Scalar::ZERO; OWNER_BFV_QUOTIENT_COUNT])
            .collect::<Vec<_>>();
        for coordinate in 0..OWNER_BFV_QUOTIENT_COUNT {
            let mut sum = Scalar::ZERO;
            for (recipient, worker_values) in shares.iter_mut().take(workers - 1).enumerate() {
                let share = random_scalar(
                    rng,
                    QUOTIENT_SHARE_DOMAIN,
                    round.digest,
                    self.owner,
                    recipient,
                    coordinate,
                );
                worker_values[coordinate] = share;
                sum += share;
            }
            shares[workers - 1][coordinate] = scalar_values[coordinate] - sum;
        }

        let owner_blinding = random_scalar(
            rng,
            QUOTIENT_BLIND_DOMAIN,
            round.digest,
            self.owner,
            workers,
            OWNER_BFV_QUOTIENT_COUNT,
        );
        let mut share_blindings = vec![Scalar::ZERO; workers];
        let mut blinding_sum = Scalar::ZERO;
        for (recipient, blinding) in share_blindings.iter_mut().take(workers - 1).enumerate() {
            *blinding = random_scalar(
                rng,
                QUOTIENT_BLIND_DOMAIN,
                round.digest,
                self.owner,
                recipient,
                OWNER_BFV_QUOTIENT_COUNT,
            );
            blinding_sum += *blinding;
        }
        share_blindings[workers - 1] = owner_blinding - blinding_sum;

        let owner_commitment =
            quotient_vector_commitment(round.degree(), self.owner, &scalar_values, owner_blinding)?;
        let share_commitments = shares
            .iter()
            .zip(&share_blindings)
            .map(|(values, blinding)| {
                quotient_vector_commitment(round.degree(), self.owner, values, *blinding)
            })
            .collect::<Result<Vec<_>>>()?;
        let digest = quotient_deal_digest(round, self.owner, &owner_commitment, &share_commitments);
        let proof = OwnerQuotientProof::create(
            round,
            self.owner,
            &self.values,
            owner_blinding,
            owner_commitment,
            &share_commitments,
            digest,
            rng,
        )?;
        let proof_digest = proof.digest();
        let contribution = BfvQuotientDealerContribution {
            round_digest: round.digest,
            owner: self.owner,
            owner_commitment,
            share_commitments,
            digest,
            proof,
            signature: signing_key
                .sign(&quotient_deal_signing_message(&digest, &proof_digest))
                .to_bytes(),
        };
        contribution.verify(round)?;
        let private_packets = shares
            .into_iter()
            .zip(share_blindings)
            .enumerate()
            .map(|(recipient, (values, blinding))| PrivateBfvQuotientShare {
                round_digest: round.digest,
                dealer_digest: digest,
                owner: self.owner,
                recipient,
                values,
                blinding,
            })
            .collect();
        Ok(BfvQuotientDealerOutput {
            contribution,
            private_packets,
        })
    }
}

fn evaluate_exact_quotients(
    witness: &[Scalar],
    degree: usize,
    equations: &[ExactBfvBatchEquation],
) -> Result<Vec<i64>> {
    if witness.len() != base_witness_width(degree)? || equations.len() != OWNER_BFV_QUOTIENT_COUNT {
        return Err(DistributedBfvError::ExactRelationMismatch);
    }
    equations
        .iter()
        .map(|equation| {
            if equation.base_coefficients.len() != witness.len() || equation.modulus == 0 {
                return Err(DistributedBfvError::ExactRelationMismatch);
            }
            let mut numerator = equation.public_constant;
            for (coordinate, (&coefficient, value)) in
                equation.base_coefficients.iter().zip(witness).enumerate()
            {
                if coefficient == 0 {
                    continue;
                }
                let integer = witness_integer(value, coordinate, degree)?;
                numerator = numerator
                    .checked_add(
                        coefficient
                            .checked_mul(integer)
                            .ok_or(DistributedBfvError::IntegerOverflow)?,
                    )
                    .ok_or(DistributedBfvError::IntegerOverflow)?;
            }
            let modulus = i128::from(equation.modulus);
            if numerator % modulus != 0 {
                return Err(DistributedBfvError::ExactRelationMismatch);
            }
            let quotient = numerator / modulus;
            if quotient.unsigned_abs() > MAX_ABS_BFV_BATCH_QUOTIENT as u128 {
                return Err(DistributedBfvError::QuotientOutOfRange);
            }
            i64::try_from(quotient).map_err(|_| DistributedBfvError::IntegerOverflow)
        })
        .collect()
}

fn witness_integer(value: &Scalar, coordinate: usize, degree: usize) -> Result<i128> {
    let short_start = DERIVED_ORDER_WIDTH;
    let short_end = short_start + 3 * degree;
    if (short_start..short_end).contains(&coordinate) {
        return (-32i64..=31)
            .find(|candidate| signed_scalar(*candidate) == *value)
            .map(i128::from)
            .ok_or(DistributedBfvError::ExactRelationMismatch);
    }
    let bytes = value.to_bytes();
    if bytes[8..].iter().any(|byte| *byte != 0) {
        return Err(DistributedBfvError::ExactRelationMismatch);
    }
    Ok(i128::from(u64::from_le_bytes(
        bytes[..8]
            .try_into()
            .map_err(|_| DistributedBfvError::ExactRelationMismatch)?,
    )))
}

/// Owner output split into one public contribution and private worker packets.
pub struct BfvQuotientDealerOutput {
    pub contribution: BfvQuotientDealerContribution,
    pub private_packets: Vec<PrivateBfvQuotientShare>,
}

/// Public owner contribution for the bounded integer quotient phase.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BfvQuotientDealerContribution {
    round_digest: [u8; 32],
    owner: usize,
    owner_commitment: [u8; 32],
    share_commitments: Vec<[u8; 32]>,
    digest: [u8; 32],
    proof: OwnerQuotientProof,
    signature: [u8; 64],
}

impl BfvQuotientDealerContribution {
    pub const fn owner(&self) -> usize {
        self.owner
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    fn verify(&self, round: &DistributedBfvRound) -> Result<()> {
        self.verify_authentication(round)?;
        self.verify_proof(round)
    }

    fn verify_authentication(&self, round: &DistributedBfvRound) -> Result<()> {
        if self.round_digest != round.digest
            || self.owner >= ORDER_COUNT
            || self.share_commitments.len() != round.n_workers()
        {
            return Err(DistributedBfvError::SessionMismatch);
        }
        if self.digest
            != quotient_deal_digest(
                round,
                self.owner,
                &self.owner_commitment,
                &self.share_commitments,
            )
        {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        // Authenticate cheap public bytes before invoking either proof system.
        let key = VerifyingKey::from_bytes(
            &round
                .session
                .owner_key(self.owner)
                .ok_or(DistributedBfvError::PartyOutOfRange)?,
        )
        .map_err(|_| DistributedBfvError::InvalidSignature)?;
        key.verify_strict(
            &quotient_deal_signing_message(&self.digest, &self.proof.digest()),
            &Signature::from_bytes(&self.signature),
        )
        .map_err(|_| DistributedBfvError::InvalidSignature)?;

        let owner_point = decode_point(&self.owner_commitment)?;
        let share_sum = self
            .share_commitments
            .iter()
            .try_fold(RistrettoPoint::default(), |sum, commitment| {
                decode_point(commitment).map(|point| sum + point)
            })?;
        if share_sum != owner_point {
            return Err(DistributedBfvError::CommitmentMismatch);
        }
        Ok(())
    }

    fn verify_proof(&self, round: &DistributedBfvRound) -> Result<()> {
        #[cfg(test)]
        QUOTIENT_PROOF_VERIFICATION_CALLS.with(|count| count.set(count.get() + 1));
        self.proof.verify(
            round,
            self.owner,
            self.owner_commitment,
            &self.share_commitments,
            self.digest,
        )
    }

    #[cfg(test)]
    fn corrupt_signature_for_test(&mut self) {
        self.signature[0] ^= 1;
    }

    #[cfg(test)]
    fn corrupt_range_proof_and_resign_for_test(&mut self, signing_key: &SigningKey) {
        self.proof.range_proof[0] ^= 1;
        self.signature = signing_key
            .sign(&quotient_deal_signing_message(
                &self.digest,
                &self.proof.digest(),
            ))
            .to_bytes();
    }
}

/// Private quotient capability delivered to exactly one proof worker.
pub struct PrivateBfvQuotientShare {
    round_digest: [u8; 32],
    dealer_digest: [u8; 32],
    owner: usize,
    recipient: usize,
    values: Vec<Scalar>,
    blinding: Scalar,
}

/// Roster-authenticated acknowledgement of one private quotient opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BfvQuotientAcknowledgement {
    round_digest: [u8; 32],
    owner: usize,
    worker: usize,
    dealer_digest: [u8; 32],
    signature: [u8; 64],
}

impl BfvQuotientAcknowledgement {
    fn verify(
        &self,
        round: &DistributedBfvRound,
        contribution: &BfvQuotientDealerContribution,
    ) -> Result<()> {
        if self.round_digest != round.digest
            || self.owner != contribution.owner
            || self.dealer_digest != contribution.digest
            || self.worker >= round.n_workers()
        {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        let key = VerifyingKey::from_bytes(
            &round
                .session
                .worker_key(self.worker)
                .ok_or(DistributedBfvError::PartyOutOfRange)?,
        )
        .map_err(|_| DistributedBfvError::InvalidSignature)?;
        key.verify_strict(
            &quotient_ack_signing_message(
                &round.digest,
                self.owner,
                self.worker,
                &self.dealer_digest,
            ),
            &Signature::from_bytes(&self.signature),
        )
        .map_err(|_| DistributedBfvError::InvalidSignature)
    }
}

/// One-shot worker receiver for all four owner quotient packets.
pub struct BfvQuotientWorkerMachine {
    round: DistributedBfvRound,
    worker: usize,
    signing_key: SigningKey,
    accepted: Vec<Option<PrivateBfvQuotientShare>>,
}

impl BfvQuotientWorkerMachine {
    pub fn new(round: DistributedBfvRound, worker: usize, signing_key: SigningKey) -> Result<Self> {
        let expected = round
            .session
            .worker_key(worker)
            .ok_or(DistributedBfvError::PartyOutOfRange)?;
        if signing_key.verifying_key().to_bytes() != expected {
            return Err(DistributedBfvError::SigningKeyMismatch);
        }
        Ok(Self {
            round,
            worker,
            signing_key,
            accepted: iter::repeat_with(|| None).take(ORDER_COUNT).collect(),
        })
    }

    pub fn accept(
        &mut self,
        contribution: &BfvQuotientDealerContribution,
        packet: PrivateBfvQuotientShare,
    ) -> Result<BfvQuotientAcknowledgement> {
        contribution.verify(&self.round)?;
        if packet.round_digest != self.round.digest
            || packet.dealer_digest != contribution.digest
            || packet.owner != contribution.owner
            || packet.recipient != self.worker
        {
            return Err(DistributedBfvError::RecipientMismatch);
        }
        if self.accepted[packet.owner].is_some() {
            return Err(DistributedBfvError::DuplicateDealer);
        }
        if packet.values.len() != OWNER_BFV_QUOTIENT_COUNT {
            return Err(DistributedBfvError::InvalidQuotientCount);
        }
        let commitment = quotient_vector_commitment(
            self.round.degree(),
            packet.owner,
            &packet.values,
            packet.blinding,
        )?;
        if commitment != contribution.share_commitments[self.worker] {
            return Err(DistributedBfvError::CommitmentMismatch);
        }
        let acknowledgement = BfvQuotientAcknowledgement {
            round_digest: self.round.digest,
            owner: packet.owner,
            worker: self.worker,
            dealer_digest: packet.dealer_digest,
            signature: self
                .signing_key
                .sign(&quotient_ack_signing_message(
                    &self.round.digest,
                    packet.owner,
                    self.worker,
                    &packet.dealer_digest,
                ))
                .to_bytes(),
        };
        let owner = packet.owner;
        self.accepted[owner] = Some(packet);
        Ok(acknowledgement)
    }

    pub fn finish(self) -> Result<PreparedBfvQuotientShare> {
        if self.accepted.iter().any(Option::is_none) {
            return Err(DistributedBfvError::MissingDealers);
        }
        Ok(PreparedBfvQuotientShare {
            round_digest: self.round.digest,
            worker: self.worker,
            owner_shares: self
                .accepted
                .into_iter()
                .map(|packet| packet.expect("all owner quotient packets checked"))
                .collect(),
        })
    }
}

/// Worker-local quotient shares consumed by the second-challenge proof.
pub struct PreparedBfvQuotientShare {
    round_digest: [u8; 32],
    worker: usize,
    owner_shares: Vec<PrivateBfvQuotientShare>,
}

impl PreparedBfvQuotientShare {
    pub const fn round_digest(&self) -> [u8; 32] {
        self.round_digest
    }

    pub const fn worker(&self) -> usize {
        self.worker
    }

    pub fn owner_share(&self, owner: usize) -> Option<(&[Scalar], Scalar)> {
        self.owner_shares
            .get(owner)
            .map(|share| (share.values.as_slice(), share.blinding))
    }

    fn verify_certificate_binding(&self, certificate: &BfvQuotientCertificate) -> Result<()> {
        if self.round_digest != certificate.round_digest
            || self.owner_shares.len() != ORDER_COUNT
            || certificate.dealers.len() != ORDER_COUNT
        {
            return Err(DistributedBfvError::SessionMismatch);
        }
        for (owner, packet) in self.owner_shares.iter().enumerate() {
            if packet.owner != owner
                || packet.recipient != self.worker
                || packet.dealer_digest != certificate.dealers[owner].digest
            {
                return Err(DistributedBfvError::CertificateMismatch);
            }
        }
        Ok(())
    }
}

/// Public coordinator for the post-challenge quotient custody transcript.
pub struct BfvQuotientCoordinator {
    round: DistributedBfvRound,
    dealers: Vec<Option<BfvQuotientDealerContribution>>,
    acknowledgements: Vec<Option<BfvQuotientAcknowledgement>>,
}

impl BfvQuotientCoordinator {
    pub fn new(round: DistributedBfvRound) -> Self {
        let acknowledgements = ORDER_COUNT * round.n_workers();
        Self {
            round,
            dealers: iter::repeat_with(|| None).take(ORDER_COUNT).collect(),
            acknowledgements: iter::repeat_with(|| None).take(acknowledgements).collect(),
        }
    }

    pub fn accept_dealer(&mut self, contribution: BfvQuotientDealerContribution) -> Result<()> {
        contribution.verify(&self.round)?;
        let slot = &mut self.dealers[contribution.owner];
        if slot.is_some() {
            return Err(DistributedBfvError::DuplicateDealer);
        }
        *slot = Some(contribution);
        Ok(())
    }

    pub fn accept_acknowledgement(
        &mut self,
        acknowledgement: BfvQuotientAcknowledgement,
    ) -> Result<()> {
        let dealer = self
            .dealers
            .get(acknowledgement.owner)
            .and_then(Option::as_ref)
            .ok_or(DistributedBfvError::MissingDealers)?;
        acknowledgement.verify(&self.round, dealer)?;
        let index = acknowledgement.owner * self.round.n_workers() + acknowledgement.worker;
        if self.acknowledgements[index].is_some() {
            return Err(DistributedBfvError::DuplicateAcknowledgement);
        }
        self.acknowledgements[index] = Some(acknowledgement);
        Ok(())
    }

    pub fn finish(self) -> Result<BfvQuotientCertificate> {
        if self.dealers.iter().any(Option::is_none) {
            return Err(DistributedBfvError::MissingDealers);
        }
        if self.acknowledgements.iter().any(Option::is_none) {
            return Err(DistributedBfvError::MissingAcknowledgements);
        }
        let dealers = self
            .dealers
            .into_iter()
            .map(|dealer| dealer.expect("all quotient dealers checked"))
            .collect::<Vec<_>>();
        let acknowledgements = self
            .acknowledgements
            .into_iter()
            .map(|ack| ack.expect("all quotient acknowledgements checked"))
            .collect::<Vec<_>>();
        let transcript_digest =
            quotient_certificate_digest(&self.round, &dealers, &acknowledgements);
        let certificate = BfvQuotientCertificate {
            round_digest: self.round.digest,
            dealers,
            acknowledgements,
            transcript_digest,
        };
        certificate.verify(&self.round)?;
        Ok(certificate)
    }
}

/// Complete public bounded-quotient custody certificate. It contains only
/// commitments, zero-knowledge proofs, and signatures—never quotient shares.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BfvQuotientCertificate {
    round_digest: [u8; 32],
    dealers: Vec<BfvQuotientDealerContribution>,
    acknowledgements: Vec<BfvQuotientAcknowledgement>,
    transcript_digest: [u8; 32],
}

impl BfvQuotientCertificate {
    pub const fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    /// Strict canonical public encoding. Private quotient shares and openings
    /// are capabilities and never appear in this wire.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut body = self.canonical_body();
        let checksum = hash_parts(QUOTIENT_CERTIFICATE_CHECKSUM_DOMAIN, &[body.as_slice()]);
        body.extend_from_slice(&checksum);
        body
    }

    /// Decode and fully reverify the public quotient custody transcript.
    pub fn from_bytes(bytes: &[u8], round: &DistributedBfvRound) -> Result<Self> {
        if bytes.len() != quotient_certificate_wire_len(round.n_workers())? {
            return Err(DistributedBfvError::MalformedWire);
        }
        let checksum_start = bytes
            .len()
            .checked_sub(32)
            .ok_or(DistributedBfvError::MalformedWire)?;
        if bytes[checksum_start..]
            != hash_parts(
                QUOTIENT_CERTIFICATE_CHECKSUM_DOMAIN,
                &[&bytes[..checksum_start]],
            )
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let mut input = WireReader::new(&bytes[..checksum_start]);
        if input.take::<8>()? != *QUOTIENT_CERTIFICATE_MAGIC
            || input.u16()? != PUBLIC_WIRE_VERSION
            || input.take::<32>()? != round.digest
            || input.usize_u16()? != ORDER_COUNT
            || input.usize_u16()? != round.n_workers()
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let mut dealers = Vec::with_capacity(ORDER_COUNT);
        for expected_owner in 0..ORDER_COUNT {
            let owner = input.usize_u16()?;
            if owner != expected_owner {
                return Err(DistributedBfvError::MalformedWire);
            }
            let owner_commitment = input.take::<32>()?;
            let mut share_commitments = Vec::with_capacity(round.n_workers());
            for _ in 0..round.n_workers() {
                share_commitments.push(input.take::<32>()?);
            }
            let digest = input.take::<32>()?;
            if input.usize_u16()? != OWNER_BFV_QUOTIENT_COUNT {
                return Err(DistributedBfvError::MalformedWire);
            }
            let mut shifted_commitments = Vec::with_capacity(OWNER_BFV_QUOTIENT_COUNT);
            for _ in 0..OWNER_BFV_QUOTIENT_COUNT {
                shifted_commitments.push(input.take::<32>()?);
            }
            let range_len = input.usize_u32()?;
            if range_len != expected_quotient_range_proof_len()? {
                return Err(DistributedBfvError::MalformedWire);
            }
            let range_proof = input.take_slice(range_len)?.to_vec();
            let link_len = input.usize_u32()?;
            if link_len != expected_linear_proof_len(PADDED_QUOTIENT_COUNT)? {
                return Err(DistributedBfvError::MalformedWire);
            }
            let link_proof = input.take_slice(link_len)?.to_vec();
            let signature = input.take::<64>()?;
            dealers.push(BfvQuotientDealerContribution {
                round_digest: round.digest,
                owner,
                owner_commitment,
                share_commitments,
                digest,
                proof: OwnerQuotientProof {
                    shifted_commitments,
                    range_proof,
                    link_proof,
                },
                signature,
            });
        }
        let acknowledgement_count = input.usize_u16()?;
        if acknowledgement_count != ORDER_COUNT * round.n_workers() {
            return Err(DistributedBfvError::MalformedWire);
        }
        let mut acknowledgements = Vec::with_capacity(acknowledgement_count);
        for owner in 0..ORDER_COUNT {
            for worker in 0..round.n_workers() {
                let parsed_owner = input.usize_u16()?;
                let parsed_worker = input.usize_u16()?;
                if parsed_owner != owner || parsed_worker != worker {
                    return Err(DistributedBfvError::MalformedWire);
                }
                acknowledgements.push(BfvQuotientAcknowledgement {
                    round_digest: round.digest,
                    owner,
                    worker,
                    dealer_digest: input.take::<32>()?,
                    signature: input.take::<64>()?,
                });
            }
        }
        let transcript_digest = input.take::<32>()?;
        input.finish()?;
        let certificate = Self {
            round_digest: round.digest,
            dealers,
            acknowledgements,
            transcript_digest,
        };
        certificate.verify(round)?;
        if certificate.to_bytes() != bytes {
            return Err(DistributedBfvError::MalformedWire);
        }
        Ok(certificate)
    }

    fn canonical_body(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(QUOTIENT_CERTIFICATE_MAGIC);
        out.extend_from_slice(&PUBLIC_WIRE_VERSION.to_be_bytes());
        out.extend_from_slice(&self.round_digest);
        out.extend_from_slice(&(self.dealers.len() as u16).to_be_bytes());
        let workers = self
            .dealers
            .first()
            .map_or(0, |dealer| dealer.share_commitments.len());
        out.extend_from_slice(&(workers as u16).to_be_bytes());
        for dealer in &self.dealers {
            out.extend_from_slice(&(dealer.owner as u16).to_be_bytes());
            out.extend_from_slice(&dealer.owner_commitment);
            for commitment in &dealer.share_commitments {
                out.extend_from_slice(commitment);
            }
            out.extend_from_slice(&dealer.digest);
            out.extend_from_slice(&(dealer.proof.shifted_commitments.len() as u16).to_be_bytes());
            for commitment in &dealer.proof.shifted_commitments {
                out.extend_from_slice(commitment);
            }
            out.extend_from_slice(&(dealer.proof.range_proof.len() as u32).to_be_bytes());
            out.extend_from_slice(&dealer.proof.range_proof);
            out.extend_from_slice(&(dealer.proof.link_proof.len() as u32).to_be_bytes());
            out.extend_from_slice(&dealer.proof.link_proof);
            out.extend_from_slice(&dealer.signature);
        }
        out.extend_from_slice(&(self.acknowledgements.len() as u16).to_be_bytes());
        for acknowledgement in &self.acknowledgements {
            out.extend_from_slice(&(acknowledgement.owner as u16).to_be_bytes());
            out.extend_from_slice(&(acknowledgement.worker as u16).to_be_bytes());
            out.extend_from_slice(&acknowledgement.dealer_digest);
            out.extend_from_slice(&acknowledgement.signature);
        }
        out.extend_from_slice(&self.transcript_digest);
        out
    }

    pub fn owner_commitment(&self, owner: usize) -> Option<[u8; 32]> {
        self.dealers
            .get(owner)
            .map(|dealer| dealer.owner_commitment)
    }

    pub fn share_commitment(&self, owner: usize, worker: usize) -> Option<[u8; 32]> {
        self.dealers
            .get(owner)
            .and_then(|dealer| dealer.share_commitments.get(worker))
            .copied()
    }

    pub fn verify(&self, round: &DistributedBfvRound) -> Result<()> {
        if self.round_digest != round.digest
            || self.dealers.len() != ORDER_COUNT
            || self.acknowledgements.len() != ORDER_COUNT * round.n_workers()
        {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        for (owner, dealer) in self.dealers.iter().enumerate() {
            if dealer.owner != owner {
                return Err(DistributedBfvError::CertificateMismatch);
            }
            dealer.verify_authentication(round)?;
        }
        for owner in 0..ORDER_COUNT {
            for worker in 0..round.n_workers() {
                let acknowledgement = &self.acknowledgements[owner * round.n_workers() + worker];
                if acknowledgement.owner != owner || acknowledgement.worker != worker {
                    return Err(DistributedBfvError::CertificateMismatch);
                }
                acknowledgement.verify(round, &self.dealers[owner])?;
            }
        }
        if self.transcript_digest
            != quotient_certificate_digest(round, &self.dealers, &self.acknowledgements)
        {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        // All cheap structure, digests, commitment sums, and signatures have
        // passed before the first expensive R1CS/LinearProof verification.
        for dealer in &self.dealers {
            dealer.verify_proof(round)?;
        }
        Ok(())
    }
}

/// Post-custody public context for the exact BFV relation proof.
///
/// The second challenge is derived only after the complete bounded-quotient
/// certificate is fixed. All 1,536 exact integer equations are collapsed into
/// one 65,536-coordinate public linear relation over the four owner generator
/// namespaces. The per-worker proofs below open only a uniformly masked scalar
/// image; their sum is the public zero relation.
#[derive(Clone)]
pub struct DistributedBfvRelationRound {
    round: DistributedBfvRound,
    quotient_certificate_digest: [u8; 32],
    digest: [u8; 32],
    second_challenge: [u8; 32],
    block_width: usize,
    public_coefficients: Arc<[Scalar]>,
    public_constant: Scalar,
    generators: Arc<[RistrettoPoint]>,
    worker_commitments: Vec<[u8; 32]>,
}

impl DistributedBfvRelationRound {
    /// Build the production relation from the independently derived deployed
    /// BFV coefficient table and both complete custody certificates.
    pub fn new(
        round: &DistributedBfvRound,
        input_certificate: &DistributedInputCertificate,
        quotient_certificate: &BfvQuotientCertificate,
        public: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        let context = Self::context(round, input_certificate, quotient_certificate, true)?;
        if public.relation_digest() != round.session.relation_digest() {
            return Err(DistributedBfvError::ExactPublicRelation);
        }
        let (public_coefficients, public_constant) = collapse_exact_relation(
            round,
            public,
            &context.second_challenge,
            context.block_width,
        )?;
        Ok(Self {
            round: round.clone(),
            quotient_certificate_digest: quotient_certificate.transcript_digest,
            digest: context.digest,
            second_challenge: context.second_challenge,
            block_width: context.block_width,
            public_coefficients: public_coefficients.into(),
            public_constant,
            generators: context.generators.into(),
            worker_commitments: context.worker_commitments,
        })
    }

    fn new_after_verified_certificates(
        round: &DistributedBfvRound,
        input_certificate: &DistributedInputCertificate,
        quotient_certificate: &BfvQuotientCertificate,
        public: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        if public.relation_digest() != round.session.relation_digest() {
            return Err(DistributedBfvError::ExactPublicRelation);
        }
        let context = Self::context(round, input_certificate, quotient_certificate, false)?;
        let (public_coefficients, public_constant) = collapse_exact_relation(
            round,
            public,
            &context.second_challenge,
            context.block_width,
        )?;
        Ok(Self {
            round: round.clone(),
            quotient_certificate_digest: quotient_certificate.transcript_digest,
            digest: context.digest,
            second_challenge: context.second_challenge,
            block_width: context.block_width,
            public_coefficients: public_coefficients.into(),
            public_constant,
            generators: context.generators.into(),
            worker_commitments: context.worker_commitments,
        })
    }

    #[cfg(test)]
    fn new_for_test(
        round: &DistributedBfvRound,
        input_certificate: &DistributedInputCertificate,
        quotient_certificate: &BfvQuotientCertificate,
    ) -> Result<Self> {
        let context = Self::context(round, input_certificate, quotient_certificate, true)?;
        let (public_coefficients, public_constant) =
            collapse_test_copy_relation(round, &context.second_challenge, context.block_width)?;
        Ok(Self {
            round: round.clone(),
            quotient_certificate_digest: quotient_certificate.transcript_digest,
            digest: context.digest,
            second_challenge: context.second_challenge,
            block_width: context.block_width,
            public_coefficients: public_coefficients.into(),
            public_constant,
            generators: context.generators.into(),
            worker_commitments: context.worker_commitments,
        })
    }

    fn context(
        round: &DistributedBfvRound,
        input_certificate: &DistributedInputCertificate,
        quotient_certificate: &BfvQuotientCertificate,
        verify_certificates: bool,
    ) -> Result<RelationContext> {
        if verify_certificates {
            input_certificate
                .verify(&round.session)
                .map_err(|_| DistributedBfvError::BaseCertificateRejected)?;
            quotient_certificate.verify(round)?;
        }
        if input_certificate.transcript_digest() != round.input_certificate_digest
            || input_certificate
                .joint_input_commitment()
                .map_err(|_| DistributedBfvError::BaseCertificateRejected)?
                != round.joint_input_commitment
        {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        let block_width = owner_bfv_block_width(round.degree())?;
        let relation_width = block_width
            .checked_mul(ORDER_COUNT)
            .ok_or(DistributedBfvError::InvalidQuotientCount)?;
        if !relation_width.is_power_of_two() {
            return Err(DistributedBfvError::InvalidQuotientCount);
        }
        let digest = hash_parts(
            RELATION_ROUND_DOMAIN,
            &[
                round.digest.as_slice(),
                round.session.relation_digest().as_slice(),
                round.input_certificate_digest.as_slice(),
                quotient_certificate.transcript_digest.as_slice(),
                (block_width as u64).to_be_bytes().as_slice(),
                (relation_width as u64).to_be_bytes().as_slice(),
            ],
        );
        let second_challenge = hash_parts(
            SECOND_CHALLENGE_DOMAIN,
            &[
                digest.as_slice(),
                quotient_certificate.transcript_digest.as_slice(),
            ],
        );
        let generators = relation_generators(round.degree(), block_width)?;
        if generators.len() != relation_width {
            return Err(DistributedBfvError::InvalidQuotientCount);
        }
        let mut worker_commitments = Vec::with_capacity(round.n_workers());
        for worker in 0..round.n_workers() {
            let mut commitment = RistrettoPoint::default();
            for owner in 0..ORDER_COUNT {
                commitment += decode_point(
                    &input_certificate
                        .share_commitment(owner, worker)
                        .ok_or(DistributedBfvError::CertificateMismatch)?,
                )?;
                commitment += decode_point(
                    &quotient_certificate
                        .share_commitment(owner, worker)
                        .ok_or(DistributedBfvError::CertificateMismatch)?,
                )?;
            }
            worker_commitments.push(commitment.compress().to_bytes());
        }
        Ok(RelationContext {
            digest,
            second_challenge,
            block_width,
            generators,
            worker_commitments,
        })
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub const fn second_challenge(&self) -> [u8; 32] {
        self.second_challenge
    }

    pub fn n_workers(&self) -> usize {
        self.round.n_workers()
    }

    fn relation_width(&self) -> usize {
        self.public_coefficients.len()
    }

    fn verify_certificate_digests(
        &self,
        input_certificate: &DistributedInputCertificate,
        quotient_certificate: &BfvQuotientCertificate,
    ) -> Result<()> {
        if input_certificate.transcript_digest() != self.round.input_certificate_digest
            || quotient_certificate.transcript_digest != self.quotient_certificate_digest
        {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        Ok(())
    }
}

struct RelationContext {
    digest: [u8; 32],
    second_challenge: [u8; 32],
    block_width: usize,
    generators: Vec<RistrettoPoint>,
    worker_commitments: Vec<[u8; 32]>,
}

/// One proof worker's masked image of the exact BFV relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BfvWorkerRelationProof {
    relation_round_digest: [u8; 32],
    worker: usize,
    image: [u8; 32],
    proof: Vec<u8>,
    signature: [u8; 64],
}

impl BfvWorkerRelationProof {
    /// Consume this worker's two private share capabilities and prove their
    /// collapsed exact relation against the certificate commitments.
    #[allow(clippy::too_many_arguments)]
    pub fn create<R: CryptoRng + RngCore>(
        relation_round: &DistributedBfvRelationRound,
        input_share: PreparedWitnessShare,
        quotient_share: PreparedBfvQuotientShare,
        input_certificate: &DistributedInputCertificate,
        quotient_certificate: &BfvQuotientCertificate,
        signing_key: &SigningKey,
        rng: &mut R,
    ) -> Result<Self> {
        relation_round.verify_certificate_digests(input_certificate, quotient_certificate)?;
        input_share
            .verify_certificate_binding(input_certificate)
            .map_err(|_| DistributedBfvError::BaseCertificateRejected)?;
        quotient_share.verify_certificate_binding(quotient_certificate)?;
        let worker = input_share.worker();
        if worker != quotient_share.worker() || worker >= relation_round.n_workers() {
            return Err(DistributedBfvError::SessionMismatch);
        }
        let expected_key = relation_round
            .round
            .session
            .worker_key(worker)
            .ok_or(DistributedBfvError::PartyOutOfRange)?;
        if signing_key.verifying_key().to_bytes() != expected_key {
            return Err(DistributedBfvError::SigningKeyMismatch);
        }

        let base_width = base_witness_width(relation_round.round.degree())?;
        let mut secret = Vec::with_capacity(relation_round.relation_width());
        let mut blinding = Scalar::ZERO;
        for owner in 0..ORDER_COUNT {
            let block_start = secret.len();
            let (base_values, base_blinding) = input_share
                .owner_share(owner)
                .ok_or(DistributedBfvError::MissingDealers)?;
            let (quotient_values, quotient_blinding) = quotient_share
                .owner_share(owner)
                .ok_or(DistributedBfvError::MissingDealers)?;
            if base_values.len() != base_width || quotient_values.len() != OWNER_BFV_QUOTIENT_COUNT
            {
                return Err(DistributedBfvError::InvalidQuotientCount);
            }
            secret.extend_from_slice(base_values);
            secret.extend_from_slice(quotient_values);
            secret.resize(block_start + relation_round.block_width, Scalar::ZERO);
            blinding += base_blinding + quotient_blinding;
        }
        if secret.len() != relation_round.relation_width() {
            return Err(DistributedBfvError::InvalidQuotientCount);
        }
        let image = secret
            .iter()
            .zip(relation_round.public_coefficients.iter())
            .fold(Scalar::ZERO, |sum, (value, coefficient)| {
                sum + value * coefficient
            });
        let worker_commitment = relation_round.worker_commitments[worker];
        let statement =
            (decode_point(&worker_commitment)? + image * PedersenGens::default().B).compress();
        let mut transcript = worker_relation_transcript(
            relation_round,
            worker,
            &worker_commitment,
            &image.to_bytes(),
        );
        let proof = LinearProof::create(
            &mut transcript,
            rng,
            &statement,
            blinding,
            secret,
            relation_round.public_coefficients.to_vec(),
            relation_round.generators.to_vec(),
            &PedersenGens::default().B,
            &PedersenGens::default().B_blinding,
        )
        .map_err(|_| DistributedBfvError::ProofRejected)?
        .to_bytes();
        let proof_digest = worker_relation_proof_digest(&proof);
        let mut result = Self {
            relation_round_digest: relation_round.digest,
            worker,
            image: image.to_bytes(),
            proof,
            signature: [0; 64],
        };
        result.signature = signing_key
            .sign(&worker_relation_signing_message(
                &relation_round.digest,
                worker,
                &result.image,
                &proof_digest,
            ))
            .to_bytes();
        result.verify(relation_round)?;
        Ok(result)
    }

    pub const fn worker(&self) -> usize {
        self.worker
    }

    /// Canonical worker-to-coordinator public transport frame.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut body = Vec::with_capacity(176 + self.proof.len());
        body.extend_from_slice(WORKER_RELATION_PROOF_MAGIC);
        body.extend_from_slice(&PUBLIC_WIRE_VERSION.to_be_bytes());
        body.extend_from_slice(&self.relation_round_digest);
        body.extend_from_slice(&(self.worker as u16).to_be_bytes());
        body.extend_from_slice(&self.image);
        body.extend_from_slice(&(self.proof.len() as u32).to_be_bytes());
        body.extend_from_slice(&self.proof);
        body.extend_from_slice(&self.signature);
        let checksum = hash_parts(WORKER_RELATION_PROOF_CHECKSUM_DOMAIN, &[body.as_slice()]);
        body.extend_from_slice(&checksum);
        body
    }

    /// Strictly decode and verify a worker-to-coordinator frame.
    pub fn from_bytes(bytes: &[u8], relation_round: &DistributedBfvRelationRound) -> Result<Self> {
        let proof_len = expected_linear_proof_len(relation_round.relation_width())?;
        if bytes.len() != 176 + proof_len {
            return Err(DistributedBfvError::MalformedWire);
        }
        let checksum_start = bytes.len() - 32;
        if bytes[checksum_start..]
            != hash_parts(
                WORKER_RELATION_PROOF_CHECKSUM_DOMAIN,
                &[&bytes[..checksum_start]],
            )
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let mut input = WireReader::new(&bytes[..checksum_start]);
        if input.take::<8>()? != *WORKER_RELATION_PROOF_MAGIC
            || input.u16()? != PUBLIC_WIRE_VERSION
            || input.take::<32>()? != relation_round.digest
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let worker = input.usize_u16()?;
        let image = input.take::<32>()?;
        if input.usize_u32()? != proof_len {
            return Err(DistributedBfvError::MalformedWire);
        }
        let proof = input.take_slice(proof_len)?.to_vec();
        let signature = input.take::<64>()?;
        input.finish()?;
        let result = Self {
            relation_round_digest: relation_round.digest,
            worker,
            image,
            proof,
            signature,
        };
        result.verify(relation_round)?;
        if result.to_bytes() != bytes {
            return Err(DistributedBfvError::MalformedWire);
        }
        Ok(result)
    }

    fn image_scalar(&self) -> Result<Scalar> {
        Option::<Scalar>::from(Scalar::from_canonical_bytes(self.image))
            .ok_or(DistributedBfvError::InvalidProof)
    }

    fn verify(&self, relation_round: &DistributedBfvRelationRound) -> Result<()> {
        let image = self.verify_authentication(relation_round)?;
        self.verify_linear_proof(relation_round, image)
    }

    fn verify_authentication(
        &self,
        relation_round: &DistributedBfvRelationRound,
    ) -> Result<Scalar> {
        if self.relation_round_digest != relation_round.digest
            || self.worker >= relation_round.n_workers()
            || self.proof.len() != expected_linear_proof_len(relation_round.relation_width())?
        {
            return Err(DistributedBfvError::InvalidProof);
        }
        let image = self.image_scalar()?;
        let key = VerifyingKey::from_bytes(
            &relation_round
                .round
                .session
                .worker_key(self.worker)
                .ok_or(DistributedBfvError::PartyOutOfRange)?,
        )
        .map_err(|_| DistributedBfvError::InvalidSignature)?;
        key.verify_strict(
            &worker_relation_signing_message(
                &relation_round.digest,
                self.worker,
                &self.image,
                &worker_relation_proof_digest(&self.proof),
            ),
            &Signature::from_bytes(&self.signature),
        )
        .map_err(|_| DistributedBfvError::InvalidSignature)?;
        Ok(image)
    }

    fn verify_linear_proof(
        &self,
        relation_round: &DistributedBfvRelationRound,
        image: Scalar,
    ) -> Result<()> {
        #[cfg(test)]
        RELATION_PROOF_VERIFICATION_CALLS.with(|count| count.set(count.get() + 1));
        let worker_commitment = relation_round.worker_commitments[self.worker];
        let statement =
            (decode_point(&worker_commitment)? + image * PedersenGens::default().B).compress();
        let proof =
            LinearProof::from_bytes(&self.proof).map_err(|_| DistributedBfvError::InvalidProof)?;
        let mut transcript = worker_relation_transcript(
            relation_round,
            self.worker,
            &worker_commitment,
            &self.image,
        );
        proof
            .verify(
                &mut transcript,
                &statement,
                &relation_round.generators,
                &PedersenGens::default().B,
                &PedersenGens::default().B_blinding,
                relation_round.public_coefficients.to_vec(),
            )
            .map_err(|_| DistributedBfvError::ProofRejected)
    }

    #[cfg(test)]
    fn corrupt_signature_for_test(&mut self) {
        self.signature[0] ^= 1;
    }
}

/// Public collector for exactly one relation proof from every proof worker.
pub struct BfvRelationCoordinator {
    relation_round: DistributedBfvRelationRound,
    proofs: Vec<Option<BfvWorkerRelationProof>>,
}

impl BfvRelationCoordinator {
    pub fn new(relation_round: DistributedBfvRelationRound) -> Self {
        let proofs = iter::repeat_with(|| None)
            .take(relation_round.n_workers())
            .collect();
        Self {
            relation_round,
            proofs,
        }
    }

    pub fn accept(&mut self, proof: BfvWorkerRelationProof) -> Result<()> {
        proof.verify(&self.relation_round)?;
        if self.proofs[proof.worker].is_some() {
            return Err(DistributedBfvError::DuplicateWorkerProof);
        }
        let worker = proof.worker;
        self.proofs[worker] = Some(proof);
        Ok(())
    }

    pub fn finish(self) -> Result<BfvRelationCertificate> {
        if self.proofs.iter().any(Option::is_none) {
            return Err(DistributedBfvError::MissingWorkerProofs);
        }
        let proofs = self
            .proofs
            .into_iter()
            .map(|proof| proof.expect("all worker relation proofs checked"))
            .collect::<Vec<_>>();
        verify_relation_sum(&self.relation_round, &proofs)?;
        let transcript_digest = relation_certificate_digest(&self.relation_round, &proofs);
        let certificate = BfvRelationCertificate {
            relation_round_digest: self.relation_round.digest,
            proofs,
            transcript_digest,
        };
        certificate.verify(&self.relation_round)?;
        Ok(certificate)
    }
}

/// Final public exact-BFV certificate: each worker proved its committed base
/// and quotient shares under the post-custody challenge, and the masked images
/// sum to the canonical public zero relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BfvRelationCertificate {
    relation_round_digest: [u8; 32],
    proofs: Vec<BfvWorkerRelationProof>,
    transcript_digest: [u8; 32],
}

impl BfvRelationCertificate {
    pub const fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    /// Canonical public final-relation certificate wire.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut body = self.canonical_body();
        let checksum = hash_parts(RELATION_CERTIFICATE_CHECKSUM_DOMAIN, &[body.as_slice()]);
        body.extend_from_slice(&checksum);
        body
    }

    /// Decode and reverify every signed worker proof and the public zero sum.
    pub fn from_bytes(bytes: &[u8], relation_round: &DistributedBfvRelationRound) -> Result<Self> {
        if bytes.len()
            != relation_certificate_wire_len(
                relation_round.n_workers(),
                relation_round.relation_width(),
            )?
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let checksum_start = bytes
            .len()
            .checked_sub(32)
            .ok_or(DistributedBfvError::MalformedWire)?;
        if bytes[checksum_start..]
            != hash_parts(
                RELATION_CERTIFICATE_CHECKSUM_DOMAIN,
                &[&bytes[..checksum_start]],
            )
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let mut input = WireReader::new(&bytes[..checksum_start]);
        if input.take::<8>()? != *RELATION_CERTIFICATE_MAGIC
            || input.u16()? != PUBLIC_WIRE_VERSION
            || input.take::<32>()? != relation_round.digest
            || input.usize_u16()? != relation_round.n_workers()
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let proof_len = expected_linear_proof_len(relation_round.relation_width())?;
        let mut proofs = Vec::with_capacity(relation_round.n_workers());
        for worker in 0..relation_round.n_workers() {
            if input.usize_u16()? != worker {
                return Err(DistributedBfvError::MalformedWire);
            }
            let image = input.take::<32>()?;
            if input.usize_u32()? != proof_len {
                return Err(DistributedBfvError::MalformedWire);
            }
            let proof = input.take_slice(proof_len)?.to_vec();
            let signature = input.take::<64>()?;
            proofs.push(BfvWorkerRelationProof {
                relation_round_digest: relation_round.digest,
                worker,
                image,
                proof,
                signature,
            });
        }
        let transcript_digest = input.take::<32>()?;
        input.finish()?;
        let certificate = Self {
            relation_round_digest: relation_round.digest,
            proofs,
            transcript_digest,
        };
        certificate.verify(relation_round)?;
        if certificate.to_bytes() != bytes {
            return Err(DistributedBfvError::MalformedWire);
        }
        Ok(certificate)
    }

    fn canonical_body(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(RELATION_CERTIFICATE_MAGIC);
        out.extend_from_slice(&PUBLIC_WIRE_VERSION.to_be_bytes());
        out.extend_from_slice(&self.relation_round_digest);
        out.extend_from_slice(&(self.proofs.len() as u16).to_be_bytes());
        for proof in &self.proofs {
            out.extend_from_slice(&(proof.worker as u16).to_be_bytes());
            out.extend_from_slice(&proof.image);
            out.extend_from_slice(&(proof.proof.len() as u32).to_be_bytes());
            out.extend_from_slice(&proof.proof);
            out.extend_from_slice(&proof.signature);
        }
        out.extend_from_slice(&self.transcript_digest);
        out
    }

    pub fn verify(&self, relation_round: &DistributedBfvRelationRound) -> Result<()> {
        if self.relation_round_digest != relation_round.digest
            || self.proofs.len() != relation_round.n_workers()
        {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        let mut images = Vec::with_capacity(self.proofs.len());
        for (worker, proof) in self.proofs.iter().enumerate() {
            if proof.worker != worker {
                return Err(DistributedBfvError::CertificateMismatch);
            }
            images.push(proof.verify_authentication(relation_round)?);
        }
        if images
            .into_iter()
            .fold(relation_round.public_constant, |sum, image| sum + image)
            != Scalar::ZERO
        {
            return Err(DistributedBfvError::RelationRejected);
        }
        if self.transcript_digest != relation_certificate_digest(relation_round, &self.proofs) {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        // Defer every expensive inner-product proof until the complete cheap
        // authentication/digest/sum layer has succeeded.
        for proof in &self.proofs {
            proof.verify_linear_proof(relation_round, proof.image_scalar()?)?;
        }
        Ok(())
    }
}

/// One transportable public object for the complete distributed exact-BFV
/// ceremony. Public statement, ciphertexts, BFV parameters, collective key,
/// and roster remain independently supplied verifier policy; this envelope
/// contains all four mandatory proof certificates and binds their ordered
/// digests. In particular, the nonlinear root link is never optional: without
/// it this object would admit the valid-BFV-book-A / valid-clearing-book-B
/// substitution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedBfvProofEnvelope {
    session_digest: [u8; 32],
    relation_digest: [u8; 32],
    input_certificate: DistributedInputCertificate,
    quotient_certificate: BfvQuotientCertificate,
    relation_certificate: BfvRelationCertificate,
    root_certificate: RootLinkCertificate,
    transcript_digest: [u8; 32],
}

impl DistributedBfvProofEnvelope {
    pub fn new(
        session: &DistributedWitnessSession,
        public: &DistributedBfvPublicRelation,
        input_certificate: DistributedInputCertificate,
        quotient_certificate: BfvQuotientCertificate,
        relation_certificate: BfvRelationCertificate,
        root_certificate: RootLinkCertificate,
    ) -> Result<Self> {
        let round = DistributedBfvRound::new(session, &input_certificate, public)?;
        quotient_certificate.verify(&round)?;
        let relation_round = DistributedBfvRelationRound::new_after_verified_certificates(
            &round,
            &input_certificate,
            &quotient_certificate,
            public,
        )?;
        relation_certificate.verify(&relation_round)?;
        root_certificate
            .verify_after_verified_input(session, &input_certificate, public)
            .map_err(|_| DistributedBfvError::RootLinkRejected)?;
        let mut envelope = Self {
            session_digest: session.digest(),
            relation_digest: public.relation_digest(),
            input_certificate,
            quotient_certificate,
            relation_certificate,
            root_certificate,
            transcript_digest: [0; 32],
        };
        envelope.transcript_digest = envelope.compute_transcript_digest();
        Ok(envelope)
    }

    pub const fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    pub const fn input_certificate(&self) -> &DistributedInputCertificate {
        &self.input_certificate
    }

    pub const fn quotient_certificate(&self) -> &BfvQuotientCertificate {
        &self.quotient_certificate
    }

    pub const fn relation_certificate(&self) -> &BfvRelationCertificate {
        &self.relation_certificate
    }

    pub const fn root_certificate(&self) -> &RootLinkCertificate {
        &self.root_certificate
    }

    pub fn verify(
        &self,
        session: &DistributedWitnessSession,
        public: &DistributedBfvPublicRelation,
    ) -> Result<()> {
        if self.session_digest != session.digest()
            || self.relation_digest != session.relation_digest()
            || self.relation_digest != public.relation_digest()
        {
            return Err(DistributedBfvError::SessionMismatch);
        }
        let round = DistributedBfvRound::new(session, &self.input_certificate, public)?;
        self.quotient_certificate.verify(&round)?;
        let relation_round = DistributedBfvRelationRound::new_after_verified_certificates(
            &round,
            &self.input_certificate,
            &self.quotient_certificate,
            public,
        )?;
        self.relation_certificate.verify(&relation_round)?;
        self.root_certificate
            .verify_after_verified_input(session, &self.input_certificate, public)
            .map_err(|_| DistributedBfvError::RootLinkRejected)?;
        if self.transcript_digest != self.compute_transcript_digest() {
            return Err(DistributedBfvError::CertificateMismatch);
        }
        Ok(())
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let input = self.input_certificate.to_bytes();
        let quotient = self.quotient_certificate.to_bytes();
        let relation = self.relation_certificate.to_bytes();
        let root = self.root_certificate.to_bytes();
        let mut body = Vec::with_capacity(
            8 + 2
                + 2 * 32
                + 4 * 4
                + input.len()
                + quotient.len()
                + relation.len()
                + root.len()
                + 64,
        );
        body.extend_from_slice(ENVELOPE_MAGIC);
        body.extend_from_slice(&ENVELOPE_WIRE_VERSION.to_be_bytes());
        body.extend_from_slice(&self.session_digest);
        body.extend_from_slice(&self.relation_digest);
        for component in [&input, &quotient, &relation, &root] {
            body.extend_from_slice(&(component.len() as u32).to_be_bytes());
            body.extend_from_slice(component);
        }
        body.extend_from_slice(&self.transcript_digest);
        let checksum = hash_parts(ENVELOPE_CHECKSUM_DOMAIN, &[body.as_slice()]);
        body.extend_from_slice(&checksum);
        body
    }

    /// Strict bounded decode. The parser reconstructs both Fiat--Shamir rounds
    /// from independently supplied verifier policy and reverifies every nested
    /// proof, signature, commitment sum, and final relation image sum.
    pub fn from_bytes(
        bytes: &[u8],
        session: &DistributedWitnessSession,
        public: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        if bytes.len() < 164 {
            return Err(DistributedBfvError::MalformedWire);
        }
        let checksum_start = bytes
            .len()
            .checked_sub(32)
            .ok_or(DistributedBfvError::MalformedWire)?;
        if bytes[checksum_start..]
            != hash_parts(ENVELOPE_CHECKSUM_DOMAIN, &[&bytes[..checksum_start]])
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        validate_envelope_framing(&bytes[..checksum_start], session)?;
        let mut input = WireReader::new(&bytes[..checksum_start]);
        if input.take::<8>()? != *ENVELOPE_MAGIC
            || input.u16()? != ENVELOPE_WIRE_VERSION
            || input.take::<32>()? != session.digest()
            || input.take::<32>()? != session.relation_digest()
            || public.relation_digest() != session.relation_digest()
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let input_len = input.usize_u32()?;
        if input_len
            != DistributedInputCertificate::expected_wire_len(session)
                .map_err(|_| DistributedBfvError::MalformedWire)?
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let input_certificate =
            DistributedInputCertificate::from_bytes(input.take_slice(input_len)?, session)
                .map_err(|_| DistributedBfvError::BaseCertificateRejected)?;
        let round = DistributedBfvRound::new_after_verified_input(session, &input_certificate)?;

        let quotient_len = input.usize_u32()?;
        if quotient_len != quotient_certificate_wire_len(session.n_workers())? {
            return Err(DistributedBfvError::MalformedWire);
        }
        let quotient_certificate =
            BfvQuotientCertificate::from_bytes(input.take_slice(quotient_len)?, &round)?;
        let relation_round = DistributedBfvRelationRound::new_after_verified_certificates(
            &round,
            &input_certificate,
            &quotient_certificate,
            public,
        )?;

        let relation_len = input.usize_u32()?;
        if relation_len
            != relation_certificate_wire_len(
                session.n_workers(),
                owner_bfv_block_width(session.degree())?
                    .checked_mul(ORDER_COUNT)
                    .ok_or(DistributedBfvError::MalformedWire)?,
            )?
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let relation_certificate =
            BfvRelationCertificate::from_bytes(input.take_slice(relation_len)?, &relation_round)?;

        let root_len = input.usize_u32()?;
        if root_len
            != RootLinkCertificate::expected_wire_len(session)
                .map_err(|_| DistributedBfvError::MalformedWire)?
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        let root_certificate = RootLinkCertificate::from_bytes_after_verified_input(
            input.take_slice(root_len)?,
            session,
            &input_certificate,
            public,
        )
        .map_err(|_| DistributedBfvError::RootLinkRejected)?;
        let transcript_digest = input.take::<32>()?;
        input.finish()?;
        let envelope = Self {
            session_digest: session.digest(),
            relation_digest: public.relation_digest(),
            input_certificate,
            quotient_certificate,
            relation_certificate,
            root_certificate,
            transcript_digest,
        };
        if envelope.compute_transcript_digest() != transcript_digest || envelope.to_bytes() != bytes
        {
            return Err(DistributedBfvError::MalformedWire);
        }
        Ok(envelope)
    }

    fn compute_transcript_digest(&self) -> [u8; 32] {
        hash_parts(
            ENVELOPE_DOMAIN,
            &[
                self.session_digest.as_slice(),
                self.relation_digest.as_slice(),
                self.input_certificate.transcript_digest().as_slice(),
                self.quotient_certificate.transcript_digest.as_slice(),
                self.relation_certificate.transcript_digest.as_slice(),
                self.root_certificate.transcript_digest().as_slice(),
            ],
        )
    }
}

fn validate_envelope_framing(body: &[u8], session: &DistributedWitnessSession) -> Result<()> {
    let input_len = DistributedInputCertificate::expected_wire_len(session)
        .map_err(|_| DistributedBfvError::MalformedWire)?;
    let quotient_len = quotient_certificate_wire_len(session.n_workers())?;
    let relation_width = owner_bfv_block_width(session.degree())?
        .checked_mul(ORDER_COUNT)
        .ok_or(DistributedBfvError::MalformedWire)?;
    let relation_len = relation_certificate_wire_len(session.n_workers(), relation_width)?;
    let root_len = RootLinkCertificate::expected_wire_len(session)
        .map_err(|_| DistributedBfvError::MalformedWire)?;
    let expected_body_len = 8usize
        .checked_add(2 + 32 + 32)
        .and_then(|value| value.checked_add(4 + input_len))
        .and_then(|value| value.checked_add(4 + quotient_len))
        .and_then(|value| value.checked_add(4 + relation_len))
        .and_then(|value| value.checked_add(4 + root_len))
        .and_then(|value| value.checked_add(32))
        .ok_or(DistributedBfvError::MalformedWire)?;
    if body.len() != expected_body_len {
        return Err(DistributedBfvError::MalformedWire);
    }
    let mut input = WireReader::new(body);
    if input.take::<8>()? != *ENVELOPE_MAGIC
        || input.u16()? != ENVELOPE_WIRE_VERSION
        || input.take::<32>()? != session.digest()
        || input.take::<32>()? != session.relation_digest()
        || input.usize_u32()? != input_len
    {
        return Err(DistributedBfvError::MalformedWire);
    }
    input.take_slice(input_len)?;
    if input.usize_u32()? != quotient_len {
        return Err(DistributedBfvError::MalformedWire);
    }
    input.take_slice(quotient_len)?;
    if input.usize_u32()? != relation_len {
        return Err(DistributedBfvError::MalformedWire);
    }
    input.take_slice(relation_len)?;
    if input.usize_u32()? != root_len {
        return Err(DistributedBfvError::MalformedWire);
    }
    input.take_slice(root_len)?;
    input.take::<32>()?;
    input.finish()
}

fn collapse_exact_relation(
    round: &DistributedBfvRound,
    public: &DistributedBfvPublicRelation,
    second_challenge: &[u8; 32],
    block_width: usize,
) -> Result<(Vec<Scalar>, Scalar)> {
    let base_width = base_witness_width(round.degree())?;
    if base_width + OWNER_BFV_QUOTIENT_COUNT > block_width {
        return Err(DistributedBfvError::InvalidQuotientCount);
    }
    let relation_width = block_width
        .checked_mul(ORDER_COUNT)
        .ok_or(DistributedBfvError::InvalidQuotientCount)?;
    let mut coefficients = vec![Scalar::ZERO; relation_width];
    let mut public_constant = Scalar::ZERO;
    for owner in 0..ORDER_COUNT {
        let equations = public
            .exact
            .owner_batch_equations(&round.coefficient_challenge, owner, round.degree())
            .map_err(|_| DistributedBfvError::ExactPublicRelation)?;
        if equations.len() != OWNER_BFV_QUOTIENT_COUNT {
            return Err(DistributedBfvError::ExactPublicRelation);
        }
        let block_start = owner * block_width;
        for (equation_index, equation) in equations.iter().enumerate() {
            if equation.base_coefficients.len() != base_width || equation.modulus == 0 {
                return Err(DistributedBfvError::ExactPublicRelation);
            }
            let alpha = relation_alpha(second_challenge, owner, equation_index);
            for (coordinate, coefficient) in equation.base_coefficients.iter().enumerate() {
                coefficients[block_start + coordinate] += alpha * signed_i128_scalar(*coefficient);
            }
            coefficients[block_start + base_width + equation_index] -=
                alpha * Scalar::from(equation.modulus);
            public_constant += alpha * signed_i128_scalar(equation.public_constant);
        }
    }
    Ok((coefficients, public_constant))
}

#[cfg(test)]
fn collapse_test_copy_relation(
    round: &DistributedBfvRound,
    second_challenge: &[u8; 32],
    block_width: usize,
) -> Result<(Vec<Scalar>, Scalar)> {
    let base_width = base_witness_width(round.degree())?;
    if base_width + OWNER_BFV_QUOTIENT_COUNT > block_width {
        return Err(DistributedBfvError::InvalidQuotientCount);
    }
    let mut coefficients = vec![Scalar::ZERO; block_width * ORDER_COUNT];
    for owner in 0..ORDER_COUNT {
        let block_start = owner * block_width;
        for equation in 0..OWNER_BFV_QUOTIENT_COUNT {
            let alpha = relation_alpha(second_challenge, owner, equation);
            coefficients[block_start + equation % base_width] += alpha;
            coefficients[block_start + base_width + equation] -= alpha;
        }
    }
    Ok((coefficients, Scalar::ZERO))
}

fn relation_alpha(second_challenge: &[u8; 32], owner: usize, equation: usize) -> Scalar {
    uniform_nonzero_scalar(
        RELATION_ALPHA_DOMAIN,
        &[second_challenge.as_slice()],
        owner * OWNER_BFV_QUOTIENT_COUNT + equation,
    )
}

fn signed_i128_scalar(value: i128) -> Scalar {
    let mut bytes = [0u8; 32];
    bytes[..16].copy_from_slice(&value.unsigned_abs().to_le_bytes());
    let magnitude = Scalar::from_bytes_mod_order(bytes);
    if value < 0 {
        -magnitude
    } else {
        magnitude
    }
}

fn relation_generators(degree: usize, block_width: usize) -> Result<Vec<RistrettoPoint>> {
    if block_width != owner_bfv_block_width(degree)? {
        return Err(DistributedBfvError::InvalidQuotientCount);
    }
    let mut generators = Vec::with_capacity(block_width * ORDER_COUNT);
    if degree == BFV_DEGREE {
        if block_width != PRODUCTION_OWNER_BFV_BLOCK_WIDTH {
            return Err(DistributedBfvError::InvalidQuotientCount);
        }
        for owner in 0..ORDER_COUNT {
            generators.extend(PRODUCTION_BFV_GENS.share(owner).G(block_width).copied());
        }
    } else {
        #[cfg(test)]
        {
            let test_generators = BulletproofGens::new(block_width, ORDER_COUNT);
            for owner in 0..ORDER_COUNT {
                generators.extend(test_generators.share(owner).G(block_width).copied());
            }
        }
        #[cfg(not(test))]
        return Err(DistributedBfvError::InvalidQuotientCount);
    }
    Ok(generators)
}

fn expected_linear_proof_len(width: usize) -> Result<usize> {
    if !width.is_power_of_two() {
        return Err(DistributedBfvError::InvalidProof);
    }
    (2usize
        .checked_mul(width.trailing_zeros() as usize)
        .and_then(|value| value.checked_add(3))
        .and_then(|value| value.checked_mul(32)))
    .ok_or(DistributedBfvError::InvalidProof)
}

fn expected_quotient_range_proof_len() -> Result<usize> {
    (13usize)
        .checked_add(2 * QUOTIENT_R1CS_CAPACITY.trailing_zeros() as usize)
        .and_then(|elements| elements.checked_mul(32))
        .and_then(|bytes| bytes.checked_add(1))
        .ok_or(DistributedBfvError::InvalidProof)
}

fn quotient_certificate_wire_len(workers: usize) -> Result<usize> {
    if !(2..=8).contains(&workers) {
        return Err(DistributedBfvError::MalformedWire);
    }
    let dealer_bytes = 2usize
        .checked_add(32)
        .and_then(|value| value.checked_add(32 * workers))
        .and_then(|value| value.checked_add(32 + 2 + 32 * OWNER_BFV_QUOTIENT_COUNT + 4))
        .and_then(|value| value.checked_add(expected_quotient_range_proof_len().ok()?))
        .and_then(|value| value.checked_add(4))
        .and_then(|value| value.checked_add(expected_linear_proof_len(PADDED_QUOTIENT_COUNT).ok()?))
        .and_then(|value| value.checked_add(64))
        .ok_or(DistributedBfvError::MalformedWire)?;
    8usize
        .checked_add(2 + 32 + 2 + 2)
        .and_then(|value| value.checked_add(ORDER_COUNT * dealer_bytes))
        .and_then(|value| value.checked_add(2 + ORDER_COUNT * workers * 100))
        .and_then(|value| value.checked_add(32 + 32))
        .ok_or(DistributedBfvError::MalformedWire)
}

fn relation_certificate_wire_len(workers: usize, relation_width: usize) -> Result<usize> {
    if !(2..=8).contains(&workers) {
        return Err(DistributedBfvError::MalformedWire);
    }
    let proof_len = expected_linear_proof_len(relation_width)?;
    let worker_bytes = 2usize
        .checked_add(32 + 4)
        .and_then(|value| value.checked_add(proof_len))
        .and_then(|value| value.checked_add(64))
        .ok_or(DistributedBfvError::MalformedWire)?;
    8usize
        .checked_add(2 + 32 + 2)
        .and_then(|value| value.checked_add(workers * worker_bytes))
        .and_then(|value| value.checked_add(32 + 32))
        .ok_or(DistributedBfvError::MalformedWire)
}

fn worker_relation_transcript(
    relation_round: &DistributedBfvRelationRound,
    worker: usize,
    worker_commitment: &[u8; 32],
    image: &[u8; 32],
) -> Transcript {
    let mut transcript = Transcript::new(WORKER_RELATION_TRANSCRIPT);
    transcript.append_message(b"relation-round", &relation_round.digest);
    transcript.append_message(
        b"quotient-certificate",
        &relation_round.quotient_certificate_digest,
    );
    transcript.append_message(b"second-challenge", &relation_round.second_challenge);
    transcript.append_u64(b"worker", worker as u64);
    transcript.append_u64(b"owner-block-width", relation_round.block_width as u64);
    transcript.append_u64(b"relation-width", relation_round.relation_width() as u64);
    transcript.append_message(b"worker-commitment", worker_commitment);
    transcript.append_message(b"masked-image", image);
    transcript
}

fn worker_relation_proof_digest(proof: &[u8]) -> [u8; 32] {
    hash_parts(WORKER_RELATION_PROOF_DOMAIN, &[proof])
}

fn worker_relation_signing_message(
    relation_round_digest: &[u8; 32],
    worker: usize,
    image: &[u8; 32],
    proof_digest: &[u8; 32],
) -> Vec<u8> {
    let mut message = Vec::with_capacity(WORKER_RELATION_SIGNATURE_DOMAIN.len() + 104);
    message.extend_from_slice(WORKER_RELATION_SIGNATURE_DOMAIN);
    message.extend_from_slice(relation_round_digest);
    message.extend_from_slice(&(worker as u64).to_be_bytes());
    message.extend_from_slice(image);
    message.extend_from_slice(proof_digest);
    message
}

fn verify_relation_sum(
    relation_round: &DistributedBfvRelationRound,
    proofs: &[BfvWorkerRelationProof],
) -> Result<()> {
    let image_sum = proofs
        .iter()
        .try_fold(relation_round.public_constant, |sum, proof| {
            proof.image_scalar().map(|image| sum + image)
        })?;
    if image_sum != Scalar::ZERO {
        return Err(DistributedBfvError::RelationRejected);
    }
    Ok(())
}

fn relation_certificate_digest(
    relation_round: &DistributedBfvRelationRound,
    proofs: &[BfvWorkerRelationProof],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(RELATION_CERTIFICATE_DOMAIN);
    hasher.update(&relation_round.digest);
    hasher.update(&(proofs.len() as u64).to_be_bytes());
    for proof in proofs {
        hasher.update(&(proof.worker as u64).to_be_bytes());
        hasher.update(&proof.image);
        hasher.update(&worker_relation_proof_digest(&proof.proof));
        hasher.update(&proof.signature);
    }
    *hasher.finalize().as_bytes()
}

fn base_witness_width(degree: usize) -> Result<usize> {
    DERIVED_ORDER_WIDTH
        .checked_add(
            3usize
                .checked_mul(degree)
                .ok_or(DistributedBfvError::InvalidQuotientCount)?,
        )
        .and_then(|width| width.checked_add(ROOT_BLINDING_WIDTH))
        .ok_or(DistributedBfvError::InvalidQuotientCount)
}

/// Per-owner block used by the final worker proof. Production is 16,384, so
/// four owner namespaces form one 65,536-coordinate LinearProof.
pub fn owner_bfv_block_width(degree: usize) -> Result<usize> {
    base_witness_width(degree)?
        .checked_add(OWNER_BFV_QUOTIENT_COUNT)
        .and_then(usize::checked_next_power_of_two)
        .ok_or(DistributedBfvError::InvalidQuotientCount)
}

fn hash_parts(domain: &str, parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    for part in parts {
        hasher.update(&(part.len() as u64).to_be_bytes());
        hasher.update(part);
    }
    *hasher.finalize().as_bytes()
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnerQuotientProof {
    shifted_commitments: Vec<[u8; 32]>,
    range_proof: Vec<u8>,
    link_proof: Vec<u8>,
}

impl OwnerQuotientProof {
    #[allow(clippy::too_many_arguments)]
    fn create<R: CryptoRng + RngCore>(
        round: &DistributedBfvRound,
        owner: usize,
        values: &[i64],
        owner_blinding: Scalar,
        owner_commitment: [u8; 32],
        share_commitments: &[[u8; 32]],
        deal_digest: [u8; 32],
        rng: &mut R,
    ) -> Result<Self> {
        if owner >= ORDER_COUNT || values.len() != OWNER_BFV_QUOTIENT_COUNT {
            return Err(DistributedBfvError::InvalidQuotientCount);
        }
        let pc_gens = R1csPedersenGens::default();
        let mut prover = bulletproofs_r1cs::r1cs::Prover::new(
            &pc_gens,
            quotient_range_transcript(
                round,
                owner,
                &owner_commitment,
                share_commitments,
                &deal_digest,
            ),
        );
        let mut range_blindings = Vec::with_capacity(OWNER_BFV_QUOTIENT_COUNT);
        let mut commitments = Vec::with_capacity(OWNER_BFV_QUOTIENT_COUNT);
        for (coordinate, value) in values.iter().copied().enumerate() {
            if value.unsigned_abs() > MAX_ABS_BFV_BATCH_QUOTIENT as u64 {
                return Err(DistributedBfvError::QuotientOutOfRange);
            }
            let shifted = value
                .checked_add(BFV_QUOTIENT_SHIFT)
                .filter(|value| (0..(1 << BFV_QUOTIENT_BITS)).contains(value))
                .ok_or(DistributedBfvError::QuotientOutOfRange)? as u64;
            let blinding = random_scalar(
                rng,
                QUOTIENT_BLIND_DOMAIN,
                round.digest,
                owner,
                round.n_workers() + 1,
                coordinate,
            );
            let (commitment, variable) = prover.commit(Scalar::from(shifted), blinding);
            range_lc(
                &mut prover,
                variable.into(),
                Some(shifted),
                BFV_QUOTIENT_BITS,
            )
            .map_err(|_| DistributedBfvError::ProofRejected)?;
            range_blindings.push(blinding);
            commitments.push(commitment.to_bytes());
        }
        let range_proof = prover
            .prove(&QUOTIENT_R1CS_GENS)
            .map_err(|_| DistributedBfvError::ProofRejected)?
            .to_bytes();

        let coefficients = quotient_link_coefficients(
            round,
            owner,
            &owner_commitment,
            share_commitments,
            &deal_digest,
            &commitments,
            &range_proof,
        );
        let pedersen = PedersenGens::default();
        let shifted_points = commitments
            .iter()
            .map(|commitment| decode_point(commitment))
            .collect::<Result<Vec<_>>>()?;
        let signed_points = shifted_points
            .iter()
            .map(|point| point - Scalar::from(BFV_QUOTIENT_SHIFT as u64) * pedersen.B)
            .collect::<Vec<_>>();
        let owner_point = decode_point(&owner_commitment)?;
        let batch_point =
            RistrettoPoint::multiscalar_mul(coefficients.iter().copied(), signed_points.iter());
        let statement = (owner_point + batch_point).compress();
        let aggregate_blinding = owner_blinding
            + coefficients
                .iter()
                .zip(&range_blindings)
                .fold(Scalar::ZERO, |sum, (coefficient, blinding)| {
                    sum + coefficient * blinding
                });
        let mut secret = values
            .iter()
            .copied()
            .map(signed_scalar)
            .collect::<Vec<_>>();
        secret.resize(PADDED_QUOTIENT_COUNT, Scalar::ZERO);
        let mut public_coefficients = coefficients;
        public_coefficients.resize(PADDED_QUOTIENT_COUNT, Scalar::ZERO);
        let generators = quotient_generators(round.degree(), owner, PADDED_QUOTIENT_COUNT)?;
        let mut transcript = quotient_link_transcript(
            round,
            owner,
            &owner_commitment,
            share_commitments,
            &deal_digest,
            &commitments,
            &range_proof,
        );
        let link_proof = LinearProof::create(
            &mut transcript,
            rng,
            &statement,
            aggregate_blinding,
            secret,
            public_coefficients,
            generators,
            &pedersen.B,
            &pedersen.B_blinding,
        )
        .map_err(|_| DistributedBfvError::ProofRejected)?
        .to_bytes();

        let proof = Self {
            shifted_commitments: commitments,
            range_proof,
            link_proof,
        };
        proof.verify(
            round,
            owner,
            owner_commitment,
            share_commitments,
            deal_digest,
        )?;
        Ok(proof)
    }

    fn verify(
        &self,
        round: &DistributedBfvRound,
        owner: usize,
        owner_commitment: [u8; 32],
        share_commitments: &[[u8; 32]],
        deal_digest: [u8; 32],
    ) -> Result<()> {
        if owner >= ORDER_COUNT
            || self.shifted_commitments.len() != OWNER_BFV_QUOTIENT_COUNT
            || self.range_proof.len() != expected_quotient_range_proof_len()?
            || self.link_proof.len() != expected_linear_proof_len(PADDED_QUOTIENT_COUNT)?
        {
            return Err(DistributedBfvError::InvalidProof);
        }
        let range_proof = R1CSProof::from_bytes(&self.range_proof)
            .map_err(|_| DistributedBfvError::InvalidProof)?;
        let mut verifier = bulletproofs_r1cs::r1cs::Verifier::new(quotient_range_transcript(
            round,
            owner,
            &owner_commitment,
            share_commitments,
            &deal_digest,
        ));
        for commitment in &self.shifted_commitments {
            let variable = verifier.commit(CompressedRistretto(*commitment));
            range_lc(&mut verifier, variable.into(), None, BFV_QUOTIENT_BITS)
                .map_err(|_| DistributedBfvError::ProofRejected)?;
        }
        verifier
            .verify(
                &range_proof,
                &R1csPedersenGens::default(),
                &QUOTIENT_R1CS_GENS,
            )
            .map_err(|_| DistributedBfvError::ProofRejected)?;

        let coefficients = quotient_link_coefficients(
            round,
            owner,
            &owner_commitment,
            share_commitments,
            &deal_digest,
            &self.shifted_commitments,
            &self.range_proof,
        );
        let pedersen = PedersenGens::default();
        let signed_points = self
            .shifted_commitments
            .iter()
            .map(|commitment| {
                decode_point(commitment)
                    .map(|point| point - Scalar::from(BFV_QUOTIENT_SHIFT as u64) * pedersen.B)
            })
            .collect::<Result<Vec<_>>>()?;
        let batch_point =
            RistrettoPoint::multiscalar_mul(coefficients.iter().copied(), signed_points.iter());
        let statement = (decode_point(&owner_commitment)? + batch_point).compress();
        let mut public_coefficients = coefficients;
        public_coefficients.resize(PADDED_QUOTIENT_COUNT, Scalar::ZERO);
        let generators = quotient_generators(round.degree(), owner, PADDED_QUOTIENT_COUNT)?;
        let link_proof = LinearProof::from_bytes(&self.link_proof)
            .map_err(|_| DistributedBfvError::InvalidProof)?;
        let mut transcript = quotient_link_transcript(
            round,
            owner,
            &owner_commitment,
            share_commitments,
            &deal_digest,
            &self.shifted_commitments,
            &self.range_proof,
        );
        link_proof
            .verify(
                &mut transcript,
                &statement,
                &generators,
                &pedersen.B,
                &pedersen.B_blinding,
                public_coefficients,
            )
            .map_err(|_| DistributedBfvError::ProofRejected)
    }

    fn digest(&self) -> [u8; 32] {
        let mut body = Vec::with_capacity(
            8 + self.shifted_commitments.len() * 32
                + self.range_proof.len()
                + self.link_proof.len(),
        );
        body.extend_from_slice(&(self.shifted_commitments.len() as u32).to_be_bytes());
        for commitment in &self.shifted_commitments {
            body.extend_from_slice(commitment);
        }
        body.extend_from_slice(&(self.range_proof.len() as u32).to_be_bytes());
        body.extend_from_slice(&self.range_proof);
        body.extend_from_slice(&(self.link_proof.len() as u32).to_be_bytes());
        body.extend_from_slice(&self.link_proof);
        hash_parts(PROOF_DIGEST_DOMAIN, &[body.as_slice()])
    }
}

fn quotient_range_transcript(
    round: &DistributedBfvRound,
    owner: usize,
    owner_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
    deal_digest: &[u8; 32],
) -> Transcript {
    let mut transcript = Transcript::new(PROOF_TRANSCRIPT);
    append_quotient_context(
        &mut transcript,
        round,
        owner,
        owner_commitment,
        share_commitments,
        deal_digest,
    );
    transcript.append_u64(b"quotient-count", OWNER_BFV_QUOTIENT_COUNT as u64);
    transcript.append_u64(b"quotient-bits", BFV_QUOTIENT_BITS as u64);
    transcript.append_u64(b"quotient-max", MAX_ABS_BFV_BATCH_QUOTIENT as u64);
    transcript
}

fn quotient_link_transcript(
    round: &DistributedBfvRound,
    owner: usize,
    owner_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
    deal_digest: &[u8; 32],
    commitments: &[[u8; 32]],
    range_proof: &[u8],
) -> Transcript {
    let mut transcript = Transcript::new(LINK_TRANSCRIPT);
    append_quotient_context(
        &mut transcript,
        round,
        owner,
        owner_commitment,
        share_commitments,
        deal_digest,
    );
    transcript.append_u64(b"quotient-count", commitments.len() as u64);
    for commitment in commitments {
        transcript.append_message(b"range-commitment", commitment);
    }
    transcript.append_message(b"range-proof", range_proof);
    transcript
}

fn append_quotient_context(
    transcript: &mut Transcript,
    round: &DistributedBfvRound,
    owner: usize,
    owner_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
    deal_digest: &[u8; 32],
) {
    transcript.append_message(b"round", &round.digest);
    transcript.append_message(b"base-certificate", &round.input_certificate_digest);
    transcript.append_message(b"joint-input", &round.joint_input_commitment);
    transcript.append_message(b"coefficient-challenge", &round.coefficient_challenge);
    transcript.append_u64(b"owner", owner as u64);
    transcript.append_message(b"owner-quotient-commitment", owner_commitment);
    transcript.append_u64(b"workers", share_commitments.len() as u64);
    for commitment in share_commitments {
        transcript.append_message(b"worker-quotient-commitment", commitment);
    }
    transcript.append_message(b"deal", deal_digest);
}

#[allow(clippy::too_many_arguments)]
fn quotient_link_coefficients(
    round: &DistributedBfvRound,
    owner: usize,
    owner_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
    deal_digest: &[u8; 32],
    commitments: &[[u8; 32]],
    range_proof: &[u8],
) -> Vec<Scalar> {
    let owner_bytes = (owner as u64).to_be_bytes();
    (0..commitments.len())
        .map(|coordinate| {
            let mut parts = vec![
                round.digest.as_slice(),
                round.input_certificate_digest.as_slice(),
                round.joint_input_commitment.as_slice(),
                round.coefficient_challenge.as_slice(),
                owner_bytes.as_slice(),
                owner_commitment.as_slice(),
                deal_digest.as_slice(),
                range_proof,
            ];
            for commitment in share_commitments {
                parts.push(commitment.as_slice());
            }
            for commitment in commitments {
                parts.push(commitment.as_slice());
            }
            uniform_nonzero_scalar(LINK_CHALLENGE_DOMAIN, &parts, coordinate)
        })
        .collect()
}

fn quotient_generators(degree: usize, owner: usize, count: usize) -> Result<Vec<RistrettoPoint>> {
    if owner >= ORDER_COUNT || count != PADDED_QUOTIENT_COUNT {
        return Err(DistributedBfvError::PartyOutOfRange);
    }
    let start = base_witness_width(degree)?;
    let block = owner_bfv_block_width(degree)?;
    if start + count > block {
        return Err(DistributedBfvError::InvalidQuotientCount);
    }
    if degree == BFV_DEGREE {
        if block != PRODUCTION_OWNER_BFV_BLOCK_WIDTH {
            return Err(DistributedBfvError::InvalidQuotientCount);
        }
        return Ok(PRODUCTION_BFV_GENS
            .share(owner)
            .G(block)
            .skip(start)
            .take(count)
            .copied()
            .collect());
    }
    #[cfg(test)]
    {
        return Ok(BulletproofGens::new(block, ORDER_COUNT)
            .share(owner)
            .G(block)
            .skip(start)
            .take(count)
            .copied()
            .collect());
    }
    #[cfg(not(test))]
    Err(DistributedBfvError::InvalidQuotientCount)
}

fn quotient_vector_commitment(
    degree: usize,
    owner: usize,
    values: &[Scalar],
    blinding: Scalar,
) -> Result<[u8; 32]> {
    if values.len() != OWNER_BFV_QUOTIENT_COUNT {
        return Err(DistributedBfvError::InvalidQuotientCount);
    }
    let generators = quotient_generators(degree, owner, PADDED_QUOTIENT_COUNT)?;
    let pedersen = PedersenGens::default();
    Ok(RistrettoPoint::multiscalar_mul(
        values
            .iter()
            .copied()
            .chain(iter::repeat(Scalar::ZERO).take(PADDED_QUOTIENT_COUNT - values.len()))
            .chain(iter::once(blinding)),
        generators.iter().chain(iter::once(&pedersen.B_blinding)),
    )
    .compress()
    .to_bytes())
}

fn range_lc<CS: ConstraintSystem>(
    cs: &mut CS,
    value: LinearCombination,
    assignment: Option<u64>,
    bits: usize,
) -> std::result::Result<(), bulletproofs_r1cs::r1cs::R1CSError> {
    let mut sum = LinearCombination::from(Scalar::ZERO);
    for bit_index in 0..bits {
        let bit = assignment.map(|value| Scalar::from((value >> bit_index) & 1));
        let (left, right, product) = cs.allocate_multiplier(bit.zip(bit))?;
        cs.constrain(left - right);
        cs.constrain(product - left);
        sum = sum + left * Scalar::from(1u64 << bit_index);
    }
    cs.constrain(value - sum);
    Ok(())
}

fn signed_scalar(value: i64) -> Scalar {
    if value < 0 {
        -Scalar::from(value.unsigned_abs())
    } else {
        Scalar::from(value as u64)
    }
}

fn decode_point(bytes: &[u8; 32]) -> Result<RistrettoPoint> {
    let point = CompressedRistretto(*bytes)
        .decompress()
        .ok_or(DistributedBfvError::InvalidCommitment)?;
    if point.compress().to_bytes() != *bytes {
        return Err(DistributedBfvError::InvalidCommitment);
    }
    Ok(point)
}

fn uniform_nonzero_scalar(domain: &str, parts: &[&[u8]], coordinate: usize) -> Scalar {
    let mut retry = 0u32;
    loop {
        let mut hasher = blake3::Hasher::new_derive_key(domain);
        hasher.update(&(coordinate as u64).to_be_bytes());
        hasher.update(&retry.to_be_bytes());
        for part in parts {
            hasher.update(&(part.len() as u64).to_be_bytes());
            hasher.update(part);
        }
        let candidate = *hasher.finalize().as_bytes();
        if let Some(scalar) = Option::<Scalar>::from(Scalar::from_canonical_bytes(candidate)) {
            if scalar != Scalar::ZERO {
                return scalar;
            }
        }
        retry = retry.wrapping_add(1);
    }
}

fn random_scalar<R: CryptoRng + RngCore>(
    rng: &mut R,
    domain: &str,
    round_digest: [u8; 32],
    owner: usize,
    recipient: usize,
    coordinate: usize,
) -> Scalar {
    let mut entropy = [0u8; 64];
    rng.fill_bytes(&mut entropy);
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(&round_digest);
    hasher.update(&(owner as u64).to_be_bytes());
    hasher.update(&(recipient as u64).to_be_bytes());
    hasher.update(&(coordinate as u64).to_be_bytes());
    hasher.update(&entropy);
    let mut wide = [0u8; 64];
    hasher.finalize_xof().fill(&mut wide);
    Scalar::from_bytes_mod_order_wide(&wide)
}

fn quotient_deal_digest(
    round: &DistributedBfvRound,
    owner: usize,
    owner_commitment: &[u8; 32],
    share_commitments: &[[u8; 32]],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(DEAL_DOMAIN);
    hasher.update(&round.digest);
    hasher.update(&round.coefficient_challenge);
    hasher.update(&(owner as u64).to_be_bytes());
    hasher.update(owner_commitment);
    hasher.update(&(share_commitments.len() as u64).to_be_bytes());
    for commitment in share_commitments {
        hasher.update(commitment);
    }
    *hasher.finalize().as_bytes()
}

fn quotient_deal_signing_message(deal_digest: &[u8; 32], proof_digest: &[u8; 32]) -> Vec<u8> {
    let mut message = Vec::with_capacity(DEAL_SIGNATURE_DOMAIN.len() + 64);
    message.extend_from_slice(DEAL_SIGNATURE_DOMAIN);
    message.extend_from_slice(deal_digest);
    message.extend_from_slice(proof_digest);
    message
}

fn quotient_ack_signing_message(
    round_digest: &[u8; 32],
    owner: usize,
    worker: usize,
    dealer_digest: &[u8; 32],
) -> Vec<u8> {
    let mut message = Vec::with_capacity(ACK_SIGNATURE_DOMAIN.len() + 80);
    message.extend_from_slice(ACK_SIGNATURE_DOMAIN);
    message.extend_from_slice(round_digest);
    message.extend_from_slice(&(owner as u64).to_be_bytes());
    message.extend_from_slice(&(worker as u64).to_be_bytes());
    message.extend_from_slice(dealer_digest);
    message
}

fn quotient_certificate_digest(
    round: &DistributedBfvRound,
    dealers: &[BfvQuotientDealerContribution],
    acknowledgements: &[BfvQuotientAcknowledgement],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CERTIFICATE_DOMAIN);
    hasher.update(&round.digest);
    hasher.update(&round.coefficient_challenge);
    hasher.update(&(dealers.len() as u64).to_be_bytes());
    for dealer in dealers {
        hasher.update(&(dealer.owner as u64).to_be_bytes());
        hasher.update(&dealer.owner_commitment);
        hasher.update(&(dealer.share_commitments.len() as u64).to_be_bytes());
        for commitment in &dealer.share_commitments {
            hasher.update(commitment);
        }
        hasher.update(&dealer.digest);
        hasher.update(&dealer.proof.digest());
        hasher.update(&dealer.signature);
    }
    hasher.update(&(acknowledgements.len() as u64).to_be_bytes());
    for acknowledgement in acknowledgements {
        hasher.update(&(acknowledgement.owner as u64).to_be_bytes());
        hasher.update(&(acknowledgement.worker as u64).to_be_bytes());
        hasher.update(&acknowledgement.dealer_digest);
        hasher.update(&acknowledgement.signature);
    }
    *hasher.finalize().as_bytes()
}

struct WireReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> WireReader<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.take_slice(N)?
            .try_into()
            .map_err(|_| DistributedBfvError::MalformedWire)
    }

    fn take_slice(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or(DistributedBfvError::MalformedWire)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(DistributedBfvError::MalformedWire)?;
        self.offset = end;
        Ok(value)
    }

    fn u16(&mut self) -> Result<u16> {
        Ok(u16::from_be_bytes(self.take::<2>()?))
    }

    fn usize_u16(&mut self) -> Result<usize> {
        Ok(usize::from(self.u16()?))
    }

    fn usize_u32(&mut self) -> Result<usize> {
        usize::try_from(u32::from_be_bytes(self.take::<4>()?))
            .map_err(|_| DistributedBfvError::MalformedWire)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(DistributedBfvError::MalformedWire)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::private_book_distributed_inputs::{
        DistributedInputCoordinator, LocalOrderWitness, PrivateSide, WitnessPartyMachine,
        BFV_DEGREE,
    };
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    fn keys<const N: usize>(base: u8) -> [SigningKey; N] {
        core::array::from_fn(|index| SigningKey::from_bytes(&[base + index as u8; 32]))
    }

    fn refresh_wire_checksum(wire: &mut [u8], domain: &str) {
        let checksum_start = wire.len() - 32;
        let checksum = hash_parts(domain, &[&wire[..checksum_start]]);
        wire[checksum_start..].copy_from_slice(&checksum);
    }

    fn base_ceremony(
        owner_keys: &[SigningKey; ORDER_COUNT],
        worker_keys: &[SigningKey; 3],
        nonce: [u8; 32],
    ) -> (
        DistributedWitnessSession,
        DistributedInputCertificate,
        Vec<PreparedWitnessShare>,
        Vec<OwnerWitnessContinuation>,
    ) {
        let session = DistributedWitnessSession::new_for_test(
            [0x41; 32],
            nonce,
            owner_keys
                .each_ref()
                .map(|key| key.verifying_key().to_bytes()),
            worker_keys
                .iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            16,
        )
        .expect("test session");
        let mut workers = worker_keys
            .iter()
            .enumerate()
            .map(|(worker, key)| {
                WitnessPartyMachine::new(session.clone(), worker, key.clone()).expect("worker")
            })
            .collect::<Vec<_>>();
        let mut coordinator = DistributedInputCoordinator::new(session.clone());
        let mut continuations = Vec::with_capacity(ORDER_COUNT);
        for owner in 0..ORDER_COUNT {
            let witness = LocalOrderWitness::from_seed(
                &session,
                owner,
                if owner < 2 {
                    PrivateSide::Bid
                } else {
                    PrivateSide::Ask
                },
                (owner % 4) as u8,
                (owner + 1) as u8,
                [0x50 + owner as u8; 32],
                (owner == 0).then_some([700; ROOT_BLINDING_WIDTH]),
            )
            .expect("base witness");
            let mut rng = StdRng::from_seed([0x60 + owner as u8; 32]);
            let output = witness
                .deal(&session, &owner_keys[owner], &mut rng)
                .expect("base deal");
            let contribution = output.contribution.clone();
            continuations.push(output.continuation);
            coordinator
                .accept_dealer(output.contribution)
                .expect("base public deal");
            for (worker, packet) in output.private_packets.into_iter().enumerate() {
                let acknowledgement = workers[worker]
                    .accept(&contribution, packet)
                    .expect("base private opening");
                coordinator
                    .accept_acknowledgement(acknowledgement)
                    .expect("base acknowledgement");
            }
        }
        let prepared = workers
            .into_iter()
            .map(|worker| worker.finish().expect("complete base share"))
            .collect();
        let certificate = coordinator.finish().expect("base certificate");
        (session, certificate, prepared, continuations)
    }

    #[test]
    fn bounded_quotients_are_privately_shared_and_publicly_certified() {
        let owner_keys = keys::<ORDER_COUNT>(0x10);
        let worker_keys = keys::<3>(0x30);
        let (session, base_certificate, prepared_inputs, continuations) =
            base_ceremony(&owner_keys, &worker_keys, [0x42; 32]);
        let round =
            DistributedBfvRound::new_for_test(&session, &base_certificate).expect("BFV round");
        assert_ne!(round.coefficient_challenge(), [0; 32]);
        assert_eq!(owner_bfv_block_width(16).unwrap(), 1024);
        assert_eq!(owner_bfv_block_width(BFV_DEGREE).unwrap(), 16_384);
        assert_eq!(
            ORDER_COUNT * owner_bfv_block_width(BFV_DEGREE).unwrap(),
            65_536
        );

        let mut workers = worker_keys
            .iter()
            .enumerate()
            .map(|(worker, key)| {
                BfvQuotientWorkerMachine::new(round.clone(), worker, key.clone())
                    .expect("quotient worker")
            })
            .collect::<Vec<_>>();
        let mut coordinator = BfvQuotientCoordinator::new(round.clone());
        let mut expected = Vec::with_capacity(ORDER_COUNT);
        for owner in 0..ORDER_COUNT {
            let values = (0..OWNER_BFV_QUOTIENT_COUNT)
                .map(|coordinate| {
                    let base_coordinate = coordinate % base_witness_width(round.degree()).unwrap();
                    i64::try_from(
                        witness_integer(
                            &continuations[owner].values()[base_coordinate],
                            base_coordinate,
                            round.degree(),
                        )
                        .unwrap(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            expected.push(
                values
                    .iter()
                    .copied()
                    .map(signed_scalar)
                    .collect::<Vec<_>>(),
            );
            let witness = OwnerBfvQuotients::from_values(&round, owner, values).expect("quotients");
            let mut rng = StdRng::from_seed([0x80 + owner as u8; 32]);
            let output = witness
                .deal(&round, &owner_keys[owner], &mut rng)
                .expect("quotient deal");
            let contribution = output.contribution.clone();
            coordinator
                .accept_dealer(output.contribution)
                .expect("public quotient deal");
            for (worker, packet) in output.private_packets.into_iter().enumerate() {
                let acknowledgement = workers[worker]
                    .accept(&contribution, packet)
                    .expect("private quotient opening");
                coordinator
                    .accept_acknowledgement(acknowledgement)
                    .expect("quotient acknowledgement");
            }
        }
        let prepared = workers
            .into_iter()
            .map(|worker| worker.finish().expect("complete quotient share"))
            .collect::<Vec<_>>();
        let certificate = coordinator.finish().expect("quotient certificate");
        certificate.verify(&round).expect("public verification");
        assert_ne!(certificate.transcript_digest(), [0; 32]);
        let quotient_wire = certificate.to_bytes();
        assert_eq!(
            quotient_wire.len(),
            quotient_certificate_wire_len(round.n_workers()).unwrap()
        );
        assert_eq!(
            BfvQuotientCertificate::from_bytes(&quotient_wire, &round).unwrap(),
            certificate
        );
        reset_quotient_proof_verification_count();
        for cut in 0..quotient_wire.len() {
            assert!(matches!(
                BfvQuotientCertificate::from_bytes(&quotient_wire[..cut], &round),
                Err(DistributedBfvError::MalformedWire)
            ));
        }
        let mut trailing = quotient_wire.clone();
        trailing.push(0);
        assert!(matches!(
            BfvQuotientCertificate::from_bytes(&trailing, &round),
            Err(DistributedBfvError::MalformedWire)
        ));
        for (offset, replacement) in [(0usize, 0xffu8), (8, 0xff), (43, 0), (45, 0), (46, 1)] {
            let mut malformed = quotient_wire.clone();
            malformed[offset] = replacement;
            refresh_wire_checksum(&mut malformed, QUOTIENT_CERTIFICATE_CHECKSUM_DOMAIN);
            assert!(matches!(
                BfvQuotientCertificate::from_bytes(&malformed, &round),
                Err(DistributedBfvError::MalformedWire)
            ));
        }
        let first_range_len =
            46 + 2 + 32 + 32 * round.n_workers() + 32 + 2 + 32 * OWNER_BFV_QUOTIENT_COUNT;
        for encoded in [0u32, u32::MAX] {
            let mut malformed = quotient_wire.clone();
            malformed[first_range_len..first_range_len + 4].copy_from_slice(&encoded.to_be_bytes());
            refresh_wire_checksum(&mut malformed, QUOTIENT_CERTIFICATE_CHECKSUM_DOMAIN);
            assert!(matches!(
                BfvQuotientCertificate::from_bytes(&malformed, &round),
                Err(DistributedBfvError::MalformedWire)
            ));
        }
        assert_eq!(quotient_proof_verification_count(), 0);
        let mut forged_quotient = certificate.clone();
        forged_quotient.dealers[0].corrupt_signature_for_test();
        forged_quotient.transcript_digest = quotient_certificate_digest(
            &round,
            &forged_quotient.dealers,
            &forged_quotient.acknowledgements,
        );
        assert!(matches!(
            BfvQuotientCertificate::from_bytes(&forged_quotient.to_bytes(), &round),
            Err(DistributedBfvError::InvalidSignature)
        ));
        assert_eq!(quotient_proof_verification_count(), 0);
        for owner in 0..ORDER_COUNT {
            assert_eq!(
                decode_point(&certificate.owner_commitment(owner).unwrap()).unwrap(),
                (0..round.n_workers())
                    .map(|worker| {
                        decode_point(&certificate.share_commitment(owner, worker).unwrap()).unwrap()
                    })
                    .sum()
            );
            for coordinate in 0..OWNER_BFV_QUOTIENT_COUNT {
                let reconstructed = prepared.iter().fold(Scalar::ZERO, |sum, worker| {
                    sum + worker.owner_share(owner).unwrap().0[coordinate]
                });
                assert_eq!(reconstructed, expected[owner][coordinate]);
            }
        }

        let relation_round =
            DistributedBfvRelationRound::new_for_test(&round, &base_certificate, &certificate)
                .expect("post-custody relation round");
        assert_ne!(relation_round.second_challenge(), [0; 32]);
        assert_eq!(relation_round.relation_width(), 4_096);
        let mut relation_proofs = Vec::with_capacity(round.n_workers());
        for (worker, (input_share, quotient_share)) in prepared_inputs
            .into_iter()
            .zip(prepared.into_iter())
            .enumerate()
        {
            let mut rng = StdRng::from_seed([0xb0 + worker as u8; 32]);
            relation_proofs.push(
                BfvWorkerRelationProof::create(
                    &relation_round,
                    input_share,
                    quotient_share,
                    &base_certificate,
                    &certificate,
                    &worker_keys[worker],
                    &mut rng,
                )
                .expect("worker exact relation proof"),
            );
        }
        let mut bad_signature = relation_proofs[0].clone();
        bad_signature.corrupt_signature_for_test();
        assert_eq!(
            bad_signature.verify(&relation_round),
            Err(DistributedBfvError::InvalidSignature)
        );
        for proof in &relation_proofs {
            let worker_wire = proof.to_bytes();
            assert_eq!(
                worker_wire.len(),
                176 + expected_linear_proof_len(relation_round.relation_width()).unwrap()
            );
            assert_eq!(
                BfvWorkerRelationProof::from_bytes(&worker_wire, &relation_round).unwrap(),
                *proof
            );
        }

        let mut wrong_public_constant = relation_round.clone();
        wrong_public_constant.public_constant += Scalar::ONE;
        let mut rejected = BfvRelationCoordinator::new(wrong_public_constant);
        for proof in relation_proofs.iter().cloned() {
            rejected.accept(proof).expect("valid worker proof");
        }
        assert!(matches!(
            rejected.finish(),
            Err(DistributedBfvError::RelationRejected)
        ));

        let mut relation_coordinator = BfvRelationCoordinator::new(relation_round.clone());
        for proof in relation_proofs {
            relation_coordinator.accept(proof).expect("worker proof");
        }
        let relation_certificate = relation_coordinator
            .finish()
            .expect("exact relation certificate");
        relation_certificate
            .verify(&relation_round)
            .expect("public exact relation verification");
        assert_ne!(relation_certificate.transcript_digest(), [0; 32]);
        let relation_wire = relation_certificate.to_bytes();
        assert_eq!(
            relation_wire.len(),
            relation_certificate_wire_len(
                relation_round.n_workers(),
                relation_round.relation_width()
            )
            .unwrap()
        );
        assert_eq!(
            BfvRelationCertificate::from_bytes(&relation_wire, &relation_round).unwrap(),
            relation_certificate
        );
        reset_relation_proof_verification_count();
        for cut in 0..relation_wire.len() {
            assert!(matches!(
                BfvRelationCertificate::from_bytes(&relation_wire[..cut], &relation_round),
                Err(DistributedBfvError::MalformedWire)
            ));
        }
        let mut trailing = relation_wire.clone();
        trailing.push(0);
        assert!(matches!(
            BfvRelationCertificate::from_bytes(&trailing, &relation_round),
            Err(DistributedBfvError::MalformedWire)
        ));
        assert_eq!(relation_proof_verification_count(), 0);
        let mut forged_relation = relation_certificate.clone();
        forged_relation.proofs[0].corrupt_signature_for_test();
        forged_relation.transcript_digest =
            relation_certificate_digest(&relation_round, &forged_relation.proofs);
        assert!(matches!(
            BfvRelationCertificate::from_bytes(&forged_relation.to_bytes(), &relation_round),
            Err(DistributedBfvError::InvalidSignature)
        ));
        assert_eq!(relation_proof_verification_count(), 0);
    }

    #[test]
    fn quotient_bounds_signatures_and_round_binding_fail_closed() {
        let owner_keys = keys::<ORDER_COUNT>(0x11);
        let worker_keys = keys::<3>(0x31);
        let (session, base_certificate, _, _) =
            base_ceremony(&owner_keys, &worker_keys, [0x43; 32]);
        let round =
            DistributedBfvRound::new_for_test(&session, &base_certificate).expect("BFV round");
        let mut outside = vec![0i64; OWNER_BFV_QUOTIENT_COUNT];
        outside[0] = MAX_ABS_BFV_BATCH_QUOTIENT + 1;
        assert!(matches!(
            OwnerBfvQuotients::from_values(&round, 0, outside),
            Err(DistributedBfvError::QuotientOutOfRange)
        ));

        let witness = OwnerBfvQuotients::from_values(
            &round,
            0,
            vec![MAX_ABS_BFV_BATCH_QUOTIENT; OWNER_BFV_QUOTIENT_COUNT],
        )
        .unwrap();
        let mut rng = StdRng::from_seed([0x90; 32]);
        let mut output = witness
            .deal(&round, &owner_keys[0], &mut rng)
            .expect("bounded edge");
        reset_quotient_proof_verification_count();
        output.contribution.corrupt_signature_for_test();
        assert_eq!(
            output.contribution.verify(&round),
            Err(DistributedBfvError::InvalidSignature)
        );
        assert_eq!(quotient_proof_verification_count(), 0);

        let witness = OwnerBfvQuotients::from_values(
            &round,
            0,
            vec![-MAX_ABS_BFV_BATCH_QUOTIENT; OWNER_BFV_QUOTIENT_COUNT],
        )
        .unwrap();
        let mut rng = StdRng::from_seed([0x91; 32]);
        let mut output = witness.deal(&round, &owner_keys[0], &mut rng).unwrap();
        output
            .contribution
            .corrupt_range_proof_and_resign_for_test(&owner_keys[0]);
        assert!(matches!(
            output.contribution.verify(&round),
            Err(DistributedBfvError::InvalidProof | DistributedBfvError::ProofRejected)
        ));

        let (other_session, other_base, _, _) =
            base_ceremony(&owner_keys, &worker_keys, [0x44; 32]);
        let other_round =
            DistributedBfvRound::new_for_test(&other_session, &other_base).expect("other round");
        let witness =
            OwnerBfvQuotients::from_values(&round, 0, vec![0; OWNER_BFV_QUOTIENT_COUNT]).unwrap();
        let mut rng = StdRng::from_seed([0x92; 32]);
        let output = witness.deal(&round, &owner_keys[0], &mut rng).unwrap();
        assert_eq!(
            output.contribution.verify(&other_round),
            Err(DistributedBfvError::SessionMismatch)
        );
    }
}

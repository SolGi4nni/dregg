//! Exact-BFV continuation of the distributed private-book input ceremony.
//!
//! The module is being built as a separate, versioned second phase so the
//! already-gated base-input certificate remains independently verifiable.

use std::fmt;
use std::iter;
use std::sync::LazyLock;

#[cfg(test)]
use std::cell::Cell;

use bulletproofs::{BulletproofGens, PedersenGens};
use bulletproofs_r1cs::r1cs::{ConstraintSystem, LinearCombination, R1CSProof};
use bulletproofs_r1cs::{
    BulletproofGens as R1csBulletproofGens, LinearProof, PedersenGens as R1csPedersenGens,
};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use merlin::Transcript;
use rand::{CryptoRng, RngCore};

use crate::private_book_distributed_inputs::{
    DistributedInputCertificate, DistributedWitnessSession, DERIVED_ORDER_WIDTH, ORDER_COUNT,
    ROOT_BLINDING_WIDTH,
};

/// Number of independent Rademacher compressions for each RNS modulus.
pub const BFV_COMPRESSION_ROUNDS: usize = 128;
/// Number of RNS moduli in the deployed BFV fold set.
pub const BFV_RNS_MODULI: usize = 3;
/// Number of signed integer quotient witnesses supplied by each owner.
pub const OWNER_BFV_QUOTIENT_COUNT: usize = BFV_RNS_MODULI * BFV_COMPRESSION_ROUNDS;
/// Bit width used by the monolithic exact relation for shifted signed quotients.
pub const BFV_QUOTIENT_BITS: usize = 24;
/// Signed interval represented by the 24-bit shifted range gadget.
pub const BFV_QUOTIENT_SHIFT: i64 = 1 << (BFV_QUOTIENT_BITS - 1);
/// Existing conservative exact-integer bound retained from the monolithic proof.
pub const MAX_ABS_BFV_BATCH_QUOTIENT: i64 = 1_130_496;

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

const PADDED_QUOTIENT_COUNT: usize = OWNER_BFV_QUOTIENT_COUNT.next_power_of_two();
const QUOTIENT_R1CS_CAPACITY: usize =
    (OWNER_BFV_QUOTIENT_COUNT * BFV_QUOTIENT_BITS).next_power_of_two();

static QUOTIENT_R1CS_GENS: LazyLock<R1csBulletproofGens> =
    LazyLock::new(|| R1csBulletproofGens::new(QUOTIENT_R1CS_CAPACITY, 1));

#[cfg(test)]
thread_local! {
    static QUOTIENT_PROOF_VERIFICATION_CALLS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
fn reset_quotient_proof_verification_count() {
    QUOTIENT_PROOF_VERIFICATION_CALLS.with(|count| count.set(0));
}

#[cfg(test)]
fn quotient_proof_verification_count() -> usize {
    QUOTIENT_PROOF_VERIFICATION_CALLS.with(Cell::get)
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

impl DistributedBfvRound {
    pub fn new(
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
    ) -> Result<Self> {
        input_certificate
            .verify(session)
            .map_err(|_| DistributedBfvError::BaseCertificateRejected)?;
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
    pub fn new(round: &DistributedBfvRound, owner: usize, values: Vec<i64>) -> Result<Self> {
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
            dealer.verify(round)?;
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
        Ok(())
    }
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
            || self.range_proof.len() > 64 * 1024
            || self.link_proof.len() > 16 * 1024
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
    Ok(BulletproofGens::new(block, ORDER_COUNT)
        .share(owner)
        .G(block)
        .skip(start)
        .take(count)
        .copied()
        .collect())
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

    fn base_ceremony(
        owner_keys: &[SigningKey; ORDER_COUNT],
        worker_keys: &[SigningKey; 3],
        nonce: [u8; 32],
    ) -> (DistributedWitnessSession, DistributedInputCertificate) {
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
        for worker in workers {
            let _ = worker.finish().expect("complete base share");
        }
        let certificate = coordinator.finish().expect("base certificate");
        (session, certificate)
    }

    #[test]
    fn bounded_quotients_are_privately_shared_and_publicly_certified() {
        let owner_keys = keys::<ORDER_COUNT>(0x10);
        let worker_keys = keys::<3>(0x30);
        let (session, base_certificate) = base_ceremony(&owner_keys, &worker_keys, [0x42; 32]);
        let round = DistributedBfvRound::new(&session, &base_certificate).expect("BFV round");
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
                .map(|coordinate| ((coordinate + 17 * owner) % 257) as i64 - 128)
                .collect::<Vec<_>>();
            expected.push(
                values
                    .iter()
                    .copied()
                    .map(signed_scalar)
                    .collect::<Vec<_>>(),
            );
            let witness = OwnerBfvQuotients::new(&round, owner, values).expect("quotients");
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
    }

    #[test]
    fn quotient_bounds_signatures_and_round_binding_fail_closed() {
        let owner_keys = keys::<ORDER_COUNT>(0x11);
        let worker_keys = keys::<3>(0x31);
        let (session, base_certificate) = base_ceremony(&owner_keys, &worker_keys, [0x43; 32]);
        let round = DistributedBfvRound::new(&session, &base_certificate).expect("BFV round");
        let mut outside = vec![0i64; OWNER_BFV_QUOTIENT_COUNT];
        outside[0] = MAX_ABS_BFV_BATCH_QUOTIENT + 1;
        assert!(matches!(
            OwnerBfvQuotients::new(&round, 0, outside),
            Err(DistributedBfvError::QuotientOutOfRange)
        ));

        let witness = OwnerBfvQuotients::new(
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

        let witness = OwnerBfvQuotients::new(
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

        let (other_session, other_base) = base_ceremony(&owner_keys, &worker_keys, [0x44; 32]);
        let other_round =
            DistributedBfvRound::new(&other_session, &other_base).expect("other round");
        let witness = OwnerBfvQuotients::new(&round, 0, vec![0; OWNER_BFV_QUOTIENT_COUNT]).unwrap();
        let mut rng = StdRng::from_seed([0x92; 32]);
        let output = witness.deal(&round, &owner_keys[0], &mut rng).unwrap();
        assert_eq!(
            output.contribution.verify(&other_round),
            Err(DistributedBfvError::SessionMismatch)
        );
    }
}

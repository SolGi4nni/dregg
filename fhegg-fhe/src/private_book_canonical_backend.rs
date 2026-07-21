//! Canonical public-relation backend for distributed private-book shares.
//!
//! This is the first concrete [`WorkerLocalProofBackend`] implementation.  For
//! each of the four owners, a worker recomputes the exact vector Pedersen
//! commitment
//!
//! `C[owner, worker] = <share[owner, worker], G[owner]> + blind[owner, worker] H`
//!
//! from its local [`PreparedWitnessShare`] and requires byte-for-byte equality
//! with that worker slot in the verified [`DistributedInputCertificate`].  Its
//! only output is a deterministic digest of those already-public commitments,
//! the worker index, and the exact [`WorkerProofContext`].  The matching
//! [`CanonicalShareOpeningVerifier`] independently derives the sole accepted
//! digest for every worker from the public certificate.  Consequently a
//! backend using this protocol identifier cannot substitute an arbitrary
//! 32-byte payload and still pass public verification.
//!
//! # Exact limitation
//!
//! This validates the exact linear Pedersen-opening contribution and its
//! certificate/session binding.  It does **not** prove the nonlinear BFV,
//! Poseidon-root, order-range, or clearing relation, and it is not proof that a
//! malicious worker actually executed this Rust implementation: the existing
//! worker signature is an attestation by that roster principal.  A future MPC
//! R1CS backend must retain this canonical input-opening gate and add a
//! publicly verifiable proof of the full relation.  The monolithic
//! `prove_private_book_bfv_zk` path remains explicit Tier 1.

use std::fmt;
use std::iter;

use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::traits::MultiscalarMul;

use crate::private_book_distributed_inputs::{
    DistributedInputCertificate, PreparedWitnessShare, ORDER_COUNT, ROOT_BLINDING_WIDTH,
};
use crate::private_book_distributed_prover::{
    PublicDistributedProofVerifier, WorkerLocalProofBackend, WorkerProofContext,
};

const PROTOCOL_DOMAIN: &str = "fhegg/private-book-canonical-share-opening/protocol/v1";
const CONTRIBUTION_DOMAIN: &str = "fhegg/private-book-canonical-share-opening/contribution/v1";
const CERTIFICATE_MAGIC: &[u8; 8] = b"FHPDI001";
const MIN_WORKERS: usize = 2;
const MAX_WORKERS: usize = 8;
const ACK_WIRE_LEN: usize = 2 + 2 + 32 + 64;

/// Errors from the exact canonical share-opening relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalBackendError {
    InvalidCertificate,
    ContextMismatch,
    WorkerOutOfRange,
    MissingOwnerShare,
    InvalidWitnessWidth,
    CommitmentMismatch { owner: usize },
    NonCanonicalContribution { worker: usize },
}

impl fmt::Display for CanonicalBackendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCertificate => write!(f, "canonical backend certificate is malformed"),
            Self::ContextMismatch => write!(f, "canonical backend context does not match"),
            Self::WorkerOutOfRange => write!(f, "canonical backend worker is out of range"),
            Self::MissingOwnerShare => write!(f, "canonical backend is missing an owner share"),
            Self::InvalidWitnessWidth => {
                write!(
                    f,
                    "canonical backend witness width does not match the certificate"
                )
            }
            Self::CommitmentMismatch { owner } => {
                write!(f, "owner {owner} share does not open its public commitment")
            }
            Self::NonCanonicalContribution { worker } => {
                write!(
                    f,
                    "worker {worker} returned a non-canonical relation contribution"
                )
            }
        }
    }
}

impl std::error::Error for CanonicalBackendError {}

/// Stable protocol identifier shared by the concrete backend and verifier.
pub fn canonical_share_opening_protocol_id() -> [u8; 32] {
    *blake3::Hasher::new_derive_key(PROTOCOL_DOMAIN)
        .finalize()
        .as_bytes()
}

/// Worker-local exact Pedersen share-opening backend.
pub struct CanonicalShareOpeningBackend {
    worker: usize,
}

impl CanonicalShareOpeningBackend {
    /// Bind this local backend instance to one proof-worker roster slot.
    pub const fn new(worker: usize) -> Self {
        Self { worker }
    }
}

impl WorkerLocalProofBackend for CanonicalShareOpeningBackend {
    type Error = CanonicalBackendError;

    fn protocol_id(&self) -> [u8; 32] {
        canonical_share_opening_protocol_id()
    }

    fn prove_local(
        &mut self,
        context: &WorkerProofContext,
        input_certificate: &DistributedInputCertificate,
        witness: PreparedWitnessShare,
    ) -> Result<[u8; 32], Self::Error> {
        let view = CertificateCommitmentView::parse(input_certificate)?;
        if input_certificate.transcript_digest() != context.input_certificate_digest()
            || view.n_workers != context.n_workers()
        {
            return Err(CanonicalBackendError::ContextMismatch);
        }
        if self.worker >= view.n_workers || witness.worker() != self.worker {
            return Err(CanonicalBackendError::WorkerOutOfRange);
        }
        let width = 2usize
            .checked_add(
                3usize
                    .checked_mul(view.degree)
                    .ok_or(CanonicalBackendError::InvalidWitnessWidth)?,
            )
            .and_then(|value| value.checked_add(ROOT_BLINDING_WIDTH))
            .ok_or(CanonicalBackendError::InvalidWitnessWidth)?;
        let generators = BulletproofGens::new(width, ORDER_COUNT);
        let blind_base = PedersenGens::default().B_blinding;
        for owner in 0..ORDER_COUNT {
            let (values, blinding) = witness
                .owner_share(owner)
                .ok_or(CanonicalBackendError::MissingOwnerShare)?;
            if values.len() != width {
                return Err(CanonicalBackendError::InvalidWitnessWidth);
            }
            let owner_generators = generators.share(owner);
            let actual = RistrettoPoint::multiscalar_mul(
                values.iter().copied().chain(iter::once(blinding)),
                owner_generators
                    .G(values.len())
                    .copied()
                    .chain(iter::once(blind_base)),
            )
            .compress()
            .to_bytes();
            if actual != view.share_commitments[owner][self.worker] {
                return Err(CanonicalBackendError::CommitmentMismatch { owner });
            }
        }
        Ok(canonical_worker_contribution(
            context,
            self.worker,
            &view.share_commitments,
        ))
    }
}

/// Public verifier accepting exactly one deterministic contribution per
/// worker.  It carries no secret shares and needs no worker-controlled bytes.
pub struct CanonicalShareOpeningVerifier {
    certificate_digest: [u8; 32],
    n_workers: usize,
    share_commitments: Vec<Vec<[u8; 32]>>,
}

impl CanonicalShareOpeningVerifier {
    /// Derive every accepted worker contribution from one public certificate.
    pub fn new(
        input_certificate: &DistributedInputCertificate,
    ) -> Result<Self, CanonicalBackendError> {
        let view = CertificateCommitmentView::parse(input_certificate)?;
        Ok(Self {
            certificate_digest: input_certificate.transcript_digest(),
            n_workers: view.n_workers,
            share_commitments: view.share_commitments,
        })
    }
}

impl PublicDistributedProofVerifier for CanonicalShareOpeningVerifier {
    type Error = CanonicalBackendError;

    fn protocol_id(&self) -> [u8; 32] {
        canonical_share_opening_protocol_id()
    }

    fn verify_transcript_digests(
        &self,
        context: &WorkerProofContext,
        transcript_digests: &[[u8; 32]],
    ) -> Result<(), Self::Error> {
        if self.certificate_digest != context.input_certificate_digest()
            || self.n_workers != context.n_workers()
        {
            return Err(CanonicalBackendError::ContextMismatch);
        }
        if transcript_digests.len() != self.n_workers {
            return Err(CanonicalBackendError::WorkerOutOfRange);
        }
        for (worker, actual) in transcript_digests.iter().enumerate() {
            let expected = canonical_worker_contribution(context, worker, &self.share_commitments);
            if *actual != expected {
                return Err(CanonicalBackendError::NonCanonicalContribution { worker });
            }
        }
        Ok(())
    }
}

fn canonical_worker_contribution(
    context: &WorkerProofContext,
    worker: usize,
    share_commitments: &[Vec<[u8; 32]>],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CONTRIBUTION_DOMAIN);
    hasher.update(&context.digest());
    hasher.update(&(worker as u64).to_be_bytes());
    hasher.update(&(ORDER_COUNT as u64).to_be_bytes());
    for (owner, commitments) in share_commitments.iter().enumerate() {
        hasher.update(&(owner as u64).to_be_bytes());
        hasher.update(&commitments[worker]);
    }
    *hasher.finalize().as_bytes()
}

struct CertificateCommitmentView {
    degree: usize,
    n_workers: usize,
    share_commitments: Vec<Vec<[u8; 32]>>,
}

impl CertificateCommitmentView {
    fn parse(certificate: &DistributedInputCertificate) -> Result<Self, CanonicalBackendError> {
        let wire = certificate.to_bytes();
        let mut reader = Reader::new(&wire);
        if reader.take::<8>()? != *CERTIFICATE_MAGIC {
            return Err(CanonicalBackendError::InvalidCertificate);
        }
        reader.skip(32)?;
        let degree = reader.u32()?;
        let n_workers = reader.u16()?;
        let n_dealers = reader.u16()?;
        if degree == 0
            || !(MIN_WORKERS..=MAX_WORKERS).contains(&n_workers)
            || n_dealers != ORDER_COUNT
        {
            return Err(CanonicalBackendError::InvalidCertificate);
        }
        let mut share_commitments = Vec::with_capacity(ORDER_COUNT);
        for expected_owner in 0..ORDER_COUNT {
            if reader.u16()? != expected_owner {
                return Err(CanonicalBackendError::InvalidCertificate);
            }
            reader.skip(32)?;
            let mut commitments = Vec::with_capacity(n_workers);
            for _ in 0..n_workers {
                commitments.push(reader.take::<32>()?);
            }
            share_commitments.push(commitments);
            reader.skip(32 + 64)?;
        }
        let acknowledgement_count = reader.u16()?;
        let expected_acknowledgements = ORDER_COUNT
            .checked_mul(n_workers)
            .ok_or(CanonicalBackendError::InvalidCertificate)?;
        if acknowledgement_count != expected_acknowledgements {
            return Err(CanonicalBackendError::InvalidCertificate);
        }
        reader.skip(
            acknowledgement_count
                .checked_mul(ACK_WIRE_LEN)
                .ok_or(CanonicalBackendError::InvalidCertificate)?,
        )?;
        reader.skip(32 + 32)?;
        reader.finish()?;
        Ok(Self {
            degree,
            n_workers,
            share_commitments,
        })
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], CanonicalBackendError> {
        let end = self
            .offset
            .checked_add(N)
            .ok_or(CanonicalBackendError::InvalidCertificate)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(CanonicalBackendError::InvalidCertificate)?
            .try_into()
            .map_err(|_| CanonicalBackendError::InvalidCertificate)?;
        self.offset = end;
        Ok(value)
    }

    fn skip(&mut self, len: usize) -> Result<(), CanonicalBackendError> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or(CanonicalBackendError::InvalidCertificate)?;
        if end > self.bytes.len() {
            return Err(CanonicalBackendError::InvalidCertificate);
        }
        self.offset = end;
        Ok(())
    }

    fn u16(&mut self) -> Result<usize, CanonicalBackendError> {
        Ok(u16::from_be_bytes(self.take::<2>()?) as usize)
    }

    fn u32(&mut self) -> Result<usize, CanonicalBackendError> {
        usize::try_from(u32::from_be_bytes(self.take::<4>()?))
            .map_err(|_| CanonicalBackendError::InvalidCertificate)
    }

    fn finish(self) -> Result<(), CanonicalBackendError> {
        if self.offset != self.bytes.len() {
            return Err(CanonicalBackendError::InvalidCertificate);
        }
        Ok(())
    }
}

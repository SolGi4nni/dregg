//! Logarithmic proof-of-opening backend for distributed private-book shares.
//!
//! For each owner, one proof worker knows only its additive vector share and
//! blinding.  This backend proves in zero knowledge that those values open the
//! exact worker slot in the verified [`DistributedInputCertificate`].  It uses
//! the owned Bulletproof fork's logarithmic `LinearProof` with a zero public
//! coefficient vector, so the proved equation is exactly
//!
//! `C[owner, worker] = <share[owner, worker], G[owner]> + blind H`.
//!
//! Vectors are zero-padded to a power of two; the commitment is unchanged
//! because only newly introduced coordinates are zero.  At the deployed
//! degree-4096 shape each owner proof is 992 bytes instead of publishing
//! 12,436 opening scalars (12,435 vector coordinates plus the blinding).  The
//! artifact binds the complete share-bound
//! request context, input certificate, worker, owner, exact unpadded width,
//! padding width, commitment, and generator namespace.  The public coordinator
//! sees proof bytes and commitments only, never a scalar share or blinding.
//!
//! # Exact guarantee and remaining relation
//!
//! The same artifacts also evaluate the first fixed constraint layer natively
//! over shares: the 24 root-blinding coordinates belonging to owners 1..3 must
//! reconstruct to zero.  For each owner, request-derived random coefficients
//! compress its eight coordinates to one Scalar equation. Every worker
//! publishes its uniformly masked linear image and proves that image against
//! its committed share; the verifier sums the images and accepts only zero.
//! The Fiat--Shamir challenge is sampled only after the request has bound the
//! complete ordered certificate/commitment vector and worker roster. In the
//! random-oracle model this degree-one Schwartz--Zippel check lets a nonzero
//! eight-vector pass with probability below `1 / |Scalar|` per owner. This
//! reveals the required compressed zero, never an owner's coordinate or a
//! worker's full vector.
//!
//! This is a classical Fiat--Shamir proof of knowledge under the Ristretto
//! multibase representation/discrete-log assumption.  It replaces the prior
//! signed assertion that a worker checked its share: arbitrary transcript
//! digests are no longer accepted. Each proof uses fresh CSPRNG prover
//! randomness, and its nonce commitments enter Merlin before the challenges.
//! Together with the certificate's public
//! `owner_commitment = sum(worker_share_commitment)` equation, it proves that a
//! full committed input vector is jointly held without reconstructing it.
//!
//! It does **not** prove that those vectors satisfy the nonlinear BFV,
//! Poseidon-root, order-range, or clearing relation.  A distributed constraint
//! evaluator/prover must consume these same bound shares and prove that next
//! layer.  It is not post-quantum; the proof and input commitments are
//! Ristretto/Pedersen.  Worker signatures authenticate transport/roster
//! participation but are not the proof authority.

use std::fmt;
use std::iter;

use bulletproofs::{BulletproofGens, PedersenGens};
use bulletproofs_r1cs::LinearProof;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use merlin::Transcript;
use rand::thread_rng;

use crate::private_book_distributed_inputs::{
    DistributedInputCertificate, PreparedWitnessShare, DERIVED_ORDER_WIDTH, ORDER_COUNT,
    ROOT_BLINDING_WIDTH,
};
use crate::private_book_distributed_prover::{
    PublicDistributedProofVerifier, WorkerLocalProofBackend, WorkerProofArtifact,
    WorkerProofContext,
};

const PROTOCOL_DOMAIN: &str = "fhegg/private-book-share-opening-pok/protocol/v2";
const TRANSCRIPT_LABEL: &[u8] = b"fhegg/private-book-share-opening-pok/v2";
const ARTIFACT_MAGIC: &[u8; 8] = b"FHPSP002";
const ARTIFACT_VERSION: u16 = 2;
const ARTIFACT_CHECKSUM_DOMAIN: &str = "fhegg/private-book-share-opening-pok/artifact/v2";
const ROOT_CONSTRAINT_CHALLENGE_DOMAIN: &str =
    "fhegg/private-book-share-opening-pok/root-constraint-challenge/v1";
const ROOT_CONSTRAINT_TRANSCRIPT_LABEL: &[u8] =
    b"fhegg/private-book-share-opening-pok/root-constraint/v1";
const CERTIFICATE_MAGIC: &[u8; 8] = b"FHPDI003";
const MIN_WORKERS: usize = 2;
const MAX_WORKERS: usize = 8;
const MAX_OWNER_RANGE_ARTIFACT_BYTES: usize = 16 * 1024;
const ACK_WIRE_LEN: usize = 2 + 2 + 32 + 64;
const ZERO_CLAIM_COUNT: usize = ORDER_COUNT - 1;
const ARTIFACT_FIXED_BYTES: usize = 8 + 2 + 2 + 4 + 4 + 32 + 32 + 2 + 2 + 32;

/// Errors from the cryptographic share-opening proof backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalBackendError {
    InvalidCertificate,
    ContextMismatch,
    WorkerOutOfRange,
    MissingOwnerShare,
    InvalidWitnessWidth,
    CommitmentMismatch { owner: usize },
    InvalidProofArtifact { worker: usize },
    ProofRejected { worker: usize, owner: usize },
    LinearConstraintRejected { owner: usize },
}

impl fmt::Display for CanonicalBackendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCertificate => write!(f, "share-opening certificate is malformed"),
            Self::ContextMismatch => write!(f, "share-opening proof context does not match"),
            Self::WorkerOutOfRange => write!(f, "share-opening worker is out of range"),
            Self::MissingOwnerShare => write!(f, "share-opening backend is missing an owner share"),
            Self::InvalidWitnessWidth => write!(f, "share-opening witness width is invalid"),
            Self::CommitmentMismatch { owner } => {
                write!(f, "owner {owner} share does not open its public commitment")
            }
            Self::InvalidProofArtifact { worker } => {
                write!(
                    f,
                    "worker {worker} share-opening proof artifact is malformed"
                )
            }
            Self::ProofRejected { worker, owner } => {
                write!(
                    f,
                    "worker {worker} owner {owner} share-opening proof was rejected"
                )
            }
            Self::LinearConstraintRejected { owner } => {
                write!(f, "owner {owner} root-blinding vector is not jointly zero")
            }
        }
    }
}

impl std::error::Error for CanonicalBackendError {}

/// Stable identifier shared by the proof-producing worker and public verifier.
pub fn canonical_share_opening_protocol_id() -> [u8; 32] {
    *blake3::Hasher::new_derive_key(PROTOCOL_DOMAIN)
        .finalize()
        .as_bytes()
}

/// Worker-local logarithmic proof-of-opening producer.
pub struct CanonicalShareOpeningBackend {
    worker: usize,
}

impl CanonicalShareOpeningBackend {
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
    ) -> Result<WorkerProofArtifact, Self::Error> {
        let view = CertificateCommitmentView::parse(input_certificate)?;
        if input_certificate.transcript_digest() != context.input_certificate_digest()
            || view.n_workers != context.n_workers()
        {
            return Err(CanonicalBackendError::ContextMismatch);
        }
        if self.worker >= view.n_workers || witness.worker() != self.worker {
            return Err(CanonicalBackendError::WorkerOutOfRange);
        }
        let width = witness_width(view.degree)?;
        let padded_width = width
            .checked_next_power_of_two()
            .ok_or(CanonicalBackendError::InvalidWitnessWidth)?;
        let generators = BulletproofGens::new(padded_width, ORDER_COUNT);
        let pedersen = PedersenGens::default();
        let mut proofs = Vec::with_capacity(ORDER_COUNT);
        let mut root_constraint_proofs = Vec::with_capacity(ZERO_CLAIM_COUNT);
        let mut rng = thread_rng();

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
                    .G(width)
                    .copied()
                    .chain(iter::once(pedersen.B_blinding)),
            )
            .compress();
            let commitment = canonical_point(view.share_commitments[owner][self.worker])
                .ok_or(CanonicalBackendError::InvalidCertificate)?;
            if actual != commitment {
                return Err(CanonicalBackendError::CommitmentMismatch { owner });
            }

            let mut secret = values.to_vec();
            secret.resize(padded_width, Scalar::ZERO);
            let public_coefficients = vec![Scalar::ZERO; padded_width];
            let proof_generators = owner_generators
                .G(padded_width)
                .copied()
                .collect::<Vec<_>>();
            let mut transcript = proof_transcript(
                context,
                self.worker,
                owner,
                width,
                padded_width,
                &commitment,
            );
            let proof = LinearProof::create(
                &mut transcript,
                &mut rng,
                &commitment,
                blinding,
                secret,
                public_coefficients,
                proof_generators,
                &pedersen.B,
                &pedersen.B_blinding,
            )
            .map_err(|_| CanonicalBackendError::ProofRejected {
                worker: self.worker,
                owner,
            })?;
            proofs.push(proof.to_bytes());
        }

        // Owners 1..3 have canonical-zero root blinding lanes. Evaluate those
        // constraints over the committed additive shares without opening a
        // coordinate: each worker publishes and proves one random linear image
        // per owner, and the public verifier checks that the images sum to zero.
        for owner in 1..ORDER_COUNT {
            let (values, blinding) = witness
                .owner_share(owner)
                .ok_or(CanonicalBackendError::MissingOwnerShare)?;
            let commitment = canonical_point(view.share_commitments[owner][self.worker])
                .ok_or(CanonicalBackendError::InvalidCertificate)?;
            let public_coefficients =
                root_constraint_coefficients(context, owner, width, padded_width)?;
            let image = values
                .iter()
                .zip(public_coefficients.iter())
                .fold(Scalar::ZERO, |sum, (value, coefficient)| {
                    sum + value * coefficient
                });
            let statement = (commitment
                .decompress()
                .ok_or(CanonicalBackendError::InvalidCertificate)?
                + image * pedersen.B)
                .compress();
            let mut secret = values.to_vec();
            secret.resize(padded_width, Scalar::ZERO);
            let proof_generators = generators
                .share(owner)
                .G(padded_width)
                .copied()
                .collect::<Vec<_>>();
            let mut transcript = root_constraint_transcript(
                context,
                self.worker,
                owner,
                width,
                padded_width,
                &commitment,
                &image,
            );
            let proof = LinearProof::create(
                &mut transcript,
                &mut rng,
                &statement,
                blinding,
                secret,
                public_coefficients,
                proof_generators,
                &pedersen.B,
                &pedersen.B_blinding,
            )
            .map_err(|_| CanonicalBackendError::ProofRejected {
                worker: self.worker,
                owner,
            })?;
            root_constraint_proofs.push((image, proof.to_bytes()));
        }

        let bytes = encode_artifact(
            context,
            self.worker,
            width,
            padded_width,
            &proofs,
            &root_constraint_proofs,
        )?;
        WorkerProofArtifact::new(bytes).map_err(|_| CanonicalBackendError::InvalidProofArtifact {
            worker: self.worker,
        })
    }
}

/// Public verifier for four share-opening and three compressed root-constraint
/// proofs from every worker.
pub struct CanonicalShareOpeningVerifier {
    certificate_digest: [u8; 32],
    degree: usize,
    n_workers: usize,
    share_commitments: Vec<Vec<[u8; 32]>>,
}

impl CanonicalShareOpeningVerifier {
    pub fn new(
        input_certificate: &DistributedInputCertificate,
    ) -> Result<Self, CanonicalBackendError> {
        let view = CertificateCommitmentView::parse(input_certificate)?;
        Ok(Self {
            certificate_digest: input_certificate.transcript_digest(),
            degree: view.degree,
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

    fn verify_public_artifacts(
        &self,
        context: &WorkerProofContext,
        artifacts: &[WorkerProofArtifact],
    ) -> Result<(), Self::Error> {
        if self.certificate_digest != context.input_certificate_digest()
            || self.n_workers != context.n_workers()
        {
            return Err(CanonicalBackendError::ContextMismatch);
        }
        if artifacts.len() != self.n_workers {
            return Err(CanonicalBackendError::WorkerOutOfRange);
        }
        let width = witness_width(self.degree)?;
        let padded_width = width
            .checked_next_power_of_two()
            .ok_or(CanonicalBackendError::InvalidWitnessWidth)?;
        let generators = BulletproofGens::new(padded_width, ORDER_COUNT);
        let pedersen = PedersenGens::default();
        let public_coefficients = vec![Scalar::ZERO; padded_width];
        let mut root_constraint_sums = [Scalar::ZERO; ZERO_CLAIM_COUNT];

        for (worker, artifact) in artifacts.iter().enumerate() {
            let decoded =
                decode_artifact(artifact.as_bytes(), context, worker, width, padded_width)?;
            for (owner, proof) in decoded.opening_proofs.iter().enumerate() {
                let commitment = canonical_point(self.share_commitments[owner][worker])
                    .ok_or(CanonicalBackendError::InvalidCertificate)?;
                let proof_generators = generators
                    .share(owner)
                    .G(padded_width)
                    .copied()
                    .collect::<Vec<_>>();
                let mut transcript =
                    proof_transcript(context, worker, owner, width, padded_width, &commitment);
                proof
                    .verify(
                        &mut transcript,
                        &commitment,
                        &proof_generators,
                        &pedersen.B,
                        &pedersen.B_blinding,
                        public_coefficients.clone(),
                    )
                    .map_err(|_| CanonicalBackendError::ProofRejected { worker, owner })?;
            }
            for (claim_index, claim) in decoded.root_constraint_proofs.iter().enumerate() {
                let owner = claim_index + 1;
                let commitment = canonical_point(self.share_commitments[owner][worker])
                    .ok_or(CanonicalBackendError::InvalidCertificate)?;
                let statement = (commitment
                    .decompress()
                    .ok_or(CanonicalBackendError::InvalidCertificate)?
                    + claim.image * pedersen.B)
                    .compress();
                let proof_generators = generators
                    .share(owner)
                    .G(padded_width)
                    .copied()
                    .collect::<Vec<_>>();
                let public_coefficients =
                    root_constraint_coefficients(context, owner, width, padded_width)?;
                let mut transcript = root_constraint_transcript(
                    context,
                    worker,
                    owner,
                    width,
                    padded_width,
                    &commitment,
                    &claim.image,
                );
                claim
                    .proof
                    .verify(
                        &mut transcript,
                        &statement,
                        &proof_generators,
                        &pedersen.B,
                        &pedersen.B_blinding,
                        public_coefficients,
                    )
                    .map_err(|_| CanonicalBackendError::ProofRejected { worker, owner })?;
                root_constraint_sums[claim_index] += claim.image;
            }
        }
        verify_root_constraint_sums(&root_constraint_sums)?;
        Ok(())
    }
}

fn witness_width(degree: usize) -> Result<usize, CanonicalBackendError> {
    DERIVED_ORDER_WIDTH
        .checked_add(
            3usize
                .checked_mul(degree)
                .ok_or(CanonicalBackendError::InvalidWitnessWidth)?,
        )
        .and_then(|value| value.checked_add(ROOT_BLINDING_WIDTH))
        .ok_or(CanonicalBackendError::InvalidWitnessWidth)
}

fn proof_transcript(
    context: &WorkerProofContext,
    worker: usize,
    owner: usize,
    width: usize,
    padded_width: usize,
    commitment: &CompressedRistretto,
) -> Transcript {
    let mut transcript = Transcript::new(TRANSCRIPT_LABEL);
    transcript.append_message(b"protocol", &canonical_share_opening_protocol_id());
    transcript.append_message(b"request-context", &context.digest());
    transcript.append_message(b"session", &context.session_digest());
    transcript.append_message(b"relation", &context.relation_digest());
    transcript.append_message(b"input-certificate", &context.input_certificate_digest());
    transcript.append_message(b"joint-input-commitment", &context.joint_input_commitment());
    transcript.append_u64(b"worker", worker as u64);
    transcript.append_u64(b"owner", owner as u64);
    transcript.append_u64(b"width", width as u64);
    transcript.append_u64(b"padded-width", padded_width as u64);
    transcript.append_message(b"share-commitment", commitment.as_bytes());
    transcript
}

fn root_constraint_coefficients(
    context: &WorkerProofContext,
    owner: usize,
    width: usize,
    padded_width: usize,
) -> Result<Vec<Scalar>, CanonicalBackendError> {
    if owner == 0 || owner >= ORDER_COUNT || width < ROOT_BLINDING_WIDTH || padded_width < width {
        return Err(CanonicalBackendError::InvalidWitnessWidth);
    }
    let root_start = width - ROOT_BLINDING_WIDTH;
    let mut root_coefficients = [Scalar::ZERO; ROOT_BLINDING_WIDTH];
    let mut retry = 0u32;
    loop {
        let mut hasher = blake3::Hasher::new_derive_key(ROOT_CONSTRAINT_CHALLENGE_DOMAIN);
        hasher.update(&context.digest());
        hasher.update(&context.input_certificate_digest());
        hasher.update(&(owner as u64).to_be_bytes());
        hasher.update(&retry.to_be_bytes());
        let mut reader = hasher.finalize_xof();
        for coefficient in &mut root_coefficients {
            let mut wide = [0u8; 64];
            reader.fill(&mut wide);
            *coefficient = Scalar::from_bytes_mod_order_wide(&wide);
        }
        if root_coefficients
            .iter()
            .any(|coefficient| *coefficient != Scalar::ZERO)
        {
            break;
        }
        retry = retry
            .checked_add(1)
            .ok_or(CanonicalBackendError::InvalidWitnessWidth)?;
    }
    let mut coefficients = vec![Scalar::ZERO; padded_width];
    for (lane, coefficient) in root_coefficients.into_iter().enumerate() {
        coefficients[root_start + lane] = coefficient;
    }
    Ok(coefficients)
}

fn root_constraint_transcript(
    context: &WorkerProofContext,
    worker: usize,
    owner: usize,
    width: usize,
    padded_width: usize,
    commitment: &CompressedRistretto,
    image: &Scalar,
) -> Transcript {
    let mut transcript = Transcript::new(ROOT_CONSTRAINT_TRANSCRIPT_LABEL);
    transcript.append_message(b"protocol", &canonical_share_opening_protocol_id());
    transcript.append_message(b"request-context", &context.digest());
    transcript.append_message(b"session", &context.session_digest());
    transcript.append_message(b"relation", &context.relation_digest());
    transcript.append_message(b"input-certificate", &context.input_certificate_digest());
    transcript.append_message(b"joint-input-commitment", &context.joint_input_commitment());
    transcript.append_u64(b"worker", worker as u64);
    transcript.append_u64(b"owner", owner as u64);
    transcript.append_u64(b"width", width as u64);
    transcript.append_u64(b"padded-width", padded_width as u64);
    transcript.append_message(b"share-commitment", commitment.as_bytes());
    transcript.append_message(b"root-linear-image", &image.to_bytes());
    transcript
}

fn verify_root_constraint_sums(
    sums: &[Scalar; ZERO_CLAIM_COUNT],
) -> Result<(), CanonicalBackendError> {
    for (claim_index, sum) in sums.iter().enumerate() {
        if *sum != Scalar::ZERO {
            return Err(CanonicalBackendError::LinearConstraintRejected {
                owner: claim_index + 1,
            });
        }
    }
    Ok(())
}

fn encode_artifact(
    context: &WorkerProofContext,
    worker: usize,
    width: usize,
    padded_width: usize,
    proofs: &[Vec<u8>],
    root_constraint_proofs: &[(Scalar, Vec<u8>)],
) -> Result<Vec<u8>, CanonicalBackendError> {
    if proofs.len() != ORDER_COUNT
        || root_constraint_proofs.len() != ZERO_CLAIM_COUNT
        || worker > u16::MAX as usize
        || width > u32::MAX as usize
        || padded_width > u32::MAX as usize
    {
        return Err(CanonicalBackendError::InvalidProofArtifact { worker });
    }
    let proof_bytes = proofs.iter().try_fold(0usize, |total, proof| {
        total.checked_add(4)?.checked_add(proof.len())
    });
    let root_constraint_bytes =
        root_constraint_proofs
            .iter()
            .try_fold(0usize, |total, (_, proof)| {
                total
                    .checked_add(32)?
                    .checked_add(4)?
                    .checked_add(proof.len())
            });
    let capacity = ARTIFACT_FIXED_BYTES
        .checked_add(proof_bytes.ok_or(CanonicalBackendError::InvalidProofArtifact { worker })?)
        .and_then(|value| value.checked_add(root_constraint_bytes?))
        .ok_or(CanonicalBackendError::InvalidProofArtifact { worker })?;
    let mut out = Vec::with_capacity(capacity);
    out.extend_from_slice(ARTIFACT_MAGIC);
    out.extend_from_slice(&ARTIFACT_VERSION.to_be_bytes());
    out.extend_from_slice(&(worker as u16).to_be_bytes());
    out.extend_from_slice(&(width as u32).to_be_bytes());
    out.extend_from_slice(&(padded_width as u32).to_be_bytes());
    out.extend_from_slice(&context.digest());
    out.extend_from_slice(&context.input_certificate_digest());
    out.extend_from_slice(&(ORDER_COUNT as u16).to_be_bytes());
    for proof in proofs {
        let len = u32::try_from(proof.len())
            .map_err(|_| CanonicalBackendError::InvalidProofArtifact { worker })?;
        out.extend_from_slice(&len.to_be_bytes());
        out.extend_from_slice(proof);
    }
    out.extend_from_slice(&(ZERO_CLAIM_COUNT as u16).to_be_bytes());
    for (image, proof) in root_constraint_proofs {
        out.extend_from_slice(&image.to_bytes());
        let len = u32::try_from(proof.len())
            .map_err(|_| CanonicalBackendError::InvalidProofArtifact { worker })?;
        out.extend_from_slice(&len.to_be_bytes());
        out.extend_from_slice(proof);
    }
    let checksum = artifact_checksum(&out);
    out.extend_from_slice(&checksum);
    debug_assert_eq!(out.len(), capacity);
    Ok(out)
}

fn decode_artifact(
    bytes: &[u8],
    context: &WorkerProofContext,
    worker: usize,
    width: usize,
    padded_width: usize,
) -> Result<DecodedArtifact, CanonicalBackendError> {
    let invalid = || CanonicalBackendError::InvalidProofArtifact { worker };
    if bytes.len() < ARTIFACT_FIXED_BYTES {
        return Err(invalid());
    }
    let checksum_start = bytes.len().checked_sub(32).ok_or_else(invalid)?;
    if bytes[checksum_start..] != artifact_checksum(&bytes[..checksum_start]) {
        return Err(invalid());
    }
    let mut reader = Reader::new(&bytes[..checksum_start]);
    if reader.take::<8>().map_err(|_| invalid())? != *ARTIFACT_MAGIC
        || u16::from_be_bytes(reader.take::<2>().map_err(|_| invalid())?) != ARTIFACT_VERSION
        || u16::from_be_bytes(reader.take::<2>().map_err(|_| invalid())?) as usize != worker
        || u32::from_be_bytes(reader.take::<4>().map_err(|_| invalid())?) as usize != width
        || u32::from_be_bytes(reader.take::<4>().map_err(|_| invalid())?) as usize != padded_width
        || reader.take::<32>().map_err(|_| invalid())? != context.digest()
        || reader.take::<32>().map_err(|_| invalid())? != context.input_certificate_digest()
        || u16::from_be_bytes(reader.take::<2>().map_err(|_| invalid())?) as usize != ORDER_COUNT
    {
        return Err(invalid());
    }
    let expected_proof_len = (2usize
        .checked_mul(padded_width.trailing_zeros() as usize)
        .and_then(|value| value.checked_add(3))
        .and_then(|value| value.checked_mul(32)))
    .ok_or_else(invalid)?;
    let mut proofs = Vec::with_capacity(ORDER_COUNT);
    for _ in 0..ORDER_COUNT {
        let len = u32::from_be_bytes(reader.take::<4>().map_err(|_| invalid())?) as usize;
        if len != expected_proof_len {
            return Err(invalid());
        }
        let proof_bytes = reader.take_slice(len).map_err(|_| invalid())?;
        proofs.push(LinearProof::from_bytes(proof_bytes).map_err(|_| invalid())?);
    }
    if u16::from_be_bytes(reader.take::<2>().map_err(|_| invalid())?) as usize != ZERO_CLAIM_COUNT {
        return Err(invalid());
    }
    let mut root_constraint_proofs = Vec::with_capacity(ZERO_CLAIM_COUNT);
    for _ in 0..ZERO_CLAIM_COUNT {
        let image_bytes = reader.take::<32>().map_err(|_| invalid())?;
        let image = Option::<Scalar>::from(Scalar::from_canonical_bytes(image_bytes))
            .ok_or_else(invalid)?;
        let len = u32::from_be_bytes(reader.take::<4>().map_err(|_| invalid())?) as usize;
        if len != expected_proof_len {
            return Err(invalid());
        }
        let proof_bytes = reader.take_slice(len).map_err(|_| invalid())?;
        let proof = LinearProof::from_bytes(proof_bytes).map_err(|_| invalid())?;
        root_constraint_proofs.push(RootConstraintProof { image, proof });
    }
    reader.finish().map_err(|_| invalid())?;
    Ok(DecodedArtifact {
        opening_proofs: proofs,
        root_constraint_proofs,
    })
}

struct DecodedArtifact {
    opening_proofs: Vec<LinearProof>,
    root_constraint_proofs: Vec<RootConstraintProof>,
}

struct RootConstraintProof {
    image: Scalar,
    proof: LinearProof,
}

fn artifact_checksum(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(ARTIFACT_CHECKSUM_DOMAIN);
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn canonical_point(bytes: [u8; 32]) -> Option<CompressedRistretto> {
    let compressed = CompressedRistretto(bytes);
    let point = compressed.decompress()?;
    (point.compress() == compressed).then_some(compressed)
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
                let commitment = reader.take::<32>()?;
                if canonical_point(commitment).is_none() {
                    return Err(CanonicalBackendError::InvalidCertificate);
                }
                commitments.push(commitment);
            }
            share_commitments.push(commitments);
            reader.skip(32)?;
            let owner_range_proof_len = reader.u32()?;
            if owner_range_proof_len == 0 || owner_range_proof_len > MAX_OWNER_RANGE_ARTIFACT_BYTES
            {
                return Err(CanonicalBackendError::InvalidCertificate);
            }
            reader.skip(owner_range_proof_len)?;
            reader.skip(64)?;
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
        let slice = self.take_slice(N)?;
        slice
            .try_into()
            .map_err(|_| CanonicalBackendError::InvalidCertificate)
    }

    fn take_slice(&mut self, len: usize) -> Result<&'a [u8], CanonicalBackendError> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or(CanonicalBackendError::InvalidCertificate)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(CanonicalBackendError::InvalidCertificate)?;
        self.offset = end;
        Ok(value)
    }

    fn skip(&mut self, len: usize) -> Result<(), CanonicalBackendError> {
        self.take_slice(len).map(|_| ())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aggregate_root_constraint_rejects_any_nonzero_owner_image() {
        verify_root_constraint_sums(&[Scalar::ZERO; ZERO_CLAIM_COUNT]).unwrap();

        let mut sums = [Scalar::ZERO; ZERO_CLAIM_COUNT];
        sums[1] = Scalar::ONE;
        assert_eq!(
            verify_root_constraint_sums(&sums),
            Err(CanonicalBackendError::LinearConstraintRejected { owner: 2 })
        );
    }
}

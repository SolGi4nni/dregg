//! Commitment-bound Poseidon root link for the distributed private BFV book.
//!
//! The exact distributed BFV certificate proves the encrypted polynomial
//! equations against four owner-vector commitments.  The HidingFRI clearing
//! proof proves a private book against one public Poseidon root.  Those facts
//! cannot merely be placed beside one another: without this protocol, a valid
//! BFV book A can be paired with a valid clearing proof for book B.
//!
//! One existing Tier-1 source viewer (the process which already creates the
//! HidingFRI proof) commits to the four private root codes and eight global
//! root-blinding felts, then proves the deployed arity-16 Poseidon2 relation in
//! a standalone Bulletproof R1CS.  It gives each owner only the Pedersen
//! blinding for that owner's scalar commitment.  Every owner checks the scalar
//! commitment against its own retained vector coordinate and returns a signed
//! logarithmic [`LinearProof`] tying it to the exact public owner commitment.
//! Owner zero additionally links all eight root-blinding coordinates; owners
//! one through three prove their reserved root lanes jointly zero.
//!
//! The coordinator and verifier never receive an order, BFV seed, vector
//! opening, root blind, or scalar-commitment blinding.  The source viewer still
//! sees the complete private book because the present HidingFRI prover already
//! does; this closes cross-book substitution but is not yet a fully distributed
//! HidingFRI prover.  All proof and commitment primitives in this module are
//! classical Ristretto/Fiat--Shamir constructions, not post-quantum.

use std::fmt;
use std::iter;
use std::sync::LazyLock;

use bulletproofs_r1cs::r1cs::{ConstraintSystem, LinearCombination, R1CSProof, Variable, Verifier};
use bulletproofs_r1cs::{r1cs::Prover, BulletproofGens, LinearProof, PedersenGens};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use dregg_circuit_prove::dark_bazaar_private::{
    self, PrivateBookWitness, PublicStatement, Side, RULE_ID,
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use merlin::Transcript;
use rand::{CryptoRng, RngCore};

use crate::private_book_bfv_zk::constrain_poseidon_root_with_blinding_variables;
use crate::private_book_distributed_bfv::DistributedBfvPublicRelation;
use crate::private_book_distributed_inputs::{
    decode_point, expected_owner_link_proof_len, owner_linear_generators,
    DistributedInputCertificate, DistributedInputError, DistributedWitnessSession,
    OwnerWitnessContinuation, DERIVED_ORDER_WIDTH, ORDER_COUNT, ROOT_BLINDING_WIDTH,
};

const ROOT_DRAFT_TRANSCRIPT: &[u8] = b"fhegg/private-book-distributed-root/r1cs/v1";
const ROOT_LINK_TRANSCRIPT: &[u8] = b"fhegg/private-book-distributed-root/linear-link/v1";
const ROOT_DRAFT_DOMAIN: &str = "fhegg/private-book-distributed-root/draft/v1";
const ROOT_COEFFICIENT_DOMAIN: &str = "fhegg/private-book-distributed-root/nonzero-coefficient/v1";
const ROOT_LINK_SIGNATURE_DOMAIN: &str = "fhegg/private-book-distributed-root/owner-signature/v1";
const ROOT_CERTIFICATE_DOMAIN: &str = "fhegg/private-book-distributed-root/certificate/v1";
const ROOT_DRAFT_CHECKSUM_DOMAIN: &str = "fhegg/private-book-distributed-root/draft-checksum/v1";
const ROOT_CERTIFICATE_CHECKSUM_DOMAIN: &str =
    "fhegg/private-book-distributed-root/certificate-checksum/v1";
const ROOT_SCHEMA: &[u8] = b"FHEGG-DARK-BAZAAR-ROOT-V2-POSEIDON16-PACKED128";
const ROOT_DRAFT_MAGIC: &[u8; 8] = b"FHPRD001";
const ROOT_CERTIFICATE_MAGIC: &[u8; 8] = b"FHPRC001";
const ROOT_WIRE_VERSION: u16 = 1;
const ROOT_R1CS_CAPACITY: usize = 1 << 17;
const ROOT_R1CS_PROOF_BYTES: usize = (13 + 2 * 17) * 32 + 1;
const ROOT_SCALAR_COMMITMENTS: usize = ORDER_COUNT + ROOT_BLINDING_WIDTH;
const ROOT_CODE_COORDINATE: usize = DERIVED_ORDER_WIDTH - 1;
const ROOT_DRAFT_WIRE_BYTES: usize =
    8 + 2 + 4 * 32 + 48 + ROOT_SCALAR_COMMITMENTS * 32 + 4 + ROOT_R1CS_PROOF_BYTES + 32 + 32;

static ROOT_GENS: LazyLock<BulletproofGens> =
    LazyLock::new(|| BulletproofGens::new(ROOT_R1CS_CAPACITY, 1));

type Result<T> = std::result::Result<T, DistributedRootError>;

/// Fail-closed root-link protocol errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DistributedRootError {
    Input(DistributedInputError),
    InvalidStatement,
    InvalidWitness,
    InvalidDraft,
    InvalidCommitment,
    InvalidPrivateOpening,
    InvalidProof,
    InvalidSignature,
    SessionMismatch,
    SigningKeyMismatch,
    PartyOutOfRange,
    DuplicateOwner,
    MissingOwners,
    CertificateDigestMismatch,
    MalformedWire,
}

impl fmt::Display for DistributedRootError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(error) => write!(formatter, "distributed input rejected: {error}"),
            Self::InvalidStatement => write!(formatter, "private root statement is invalid"),
            Self::InvalidWitness => write!(formatter, "private root witness is inconsistent"),
            Self::InvalidDraft => write!(formatter, "root-link draft is malformed"),
            Self::InvalidCommitment => write!(formatter, "root scalar commitment is invalid"),
            Self::InvalidPrivateOpening => {
                write!(
                    formatter,
                    "private root-link opening does not match the owner vector"
                )
            }
            Self::InvalidProof => write!(formatter, "root-link proof was rejected"),
            Self::InvalidSignature => write!(formatter, "root-link owner signature is invalid"),
            Self::SessionMismatch => write!(formatter, "root link belongs to another session"),
            Self::SigningKeyMismatch => {
                write!(
                    formatter,
                    "root-link signing key does not match the owner roster"
                )
            }
            Self::PartyOutOfRange => write!(formatter, "root-link owner is out of range"),
            Self::DuplicateOwner => write!(formatter, "root-link owner proof is duplicated"),
            Self::MissingOwners => write!(formatter, "root-link certificate is missing an owner"),
            Self::CertificateDigestMismatch => {
                write!(formatter, "root-link certificate digest mismatch")
            }
            Self::MalformedWire => write!(formatter, "root-link public wire is malformed"),
        }
    }
}

impl std::error::Error for DistributedRootError {}

impl From<DistributedInputError> for DistributedRootError {
    fn from(error: DistributedInputError) -> Self {
        Self::Input(error)
    }
}

/// Public source-viewer proof draft.  It contains no witness opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootLinkDraft {
    session_digest: [u8; 32],
    relation_digest: [u8; 32],
    input_certificate_digest: [u8; 32],
    joint_input_commitment: [u8; 32],
    statement: PublicStatement,
    scalar_commitments: [[u8; 32]; ROOT_SCALAR_COMMITMENTS],
    root_proof: Vec<u8>,
    digest: [u8; 32],
}

/// Source-viewer result. Private packets contain Pedersen blindings and have
/// deliberately no `Clone`, `Debug`, equality, or wire codec.
pub struct RootLinkProverOutput {
    pub draft: RootLinkDraft,
    pub private_packets: Vec<PrivateRootLinkOpening>,
}

/// Confidential source-viewer-to-owner scalar-commitment opening.
pub struct PrivateRootLinkOpening {
    session_digest: [u8; 32],
    input_certificate_digest: [u8; 32],
    draft_digest: [u8; 32],
    owner: usize,
    commitment_blindings: Vec<Scalar>,
}

impl RootLinkDraft {
    /// Create the nonlinear public root proof and four owner-local opening
    /// packets from the exact witness already consumed by HidingFRI.
    pub fn create<R: CryptoRng + RngCore>(
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
        witness: &PrivateBookWitness,
        rng: &mut R,
    ) -> Result<RootLinkProverOutput> {
        input_certificate.verify(session)?;
        if public_relation.relation_digest() != session.relation_digest() {
            return Err(DistributedRootError::SessionMismatch);
        }
        let statement = public_relation.statement();
        let expected = dark_bazaar_private::statement(statement.session, witness)
            .map_err(|_| DistributedRootError::InvalidWitness)?;
        if expected != statement || !valid_statement(statement) {
            return Err(DistributedRootError::InvalidStatement);
        }

        let codes = witness.orders.map(order_code);
        let values = codes
            .into_iter()
            .map(|value| Scalar::from(u64::from(value)))
            .chain(
                witness
                    .blinding
                    .into_iter()
                    .map(|value| Scalar::from(u64::from(value))),
            )
            .collect::<Vec<_>>();
        debug_assert_eq!(values.len(), ROOT_SCALAR_COMMITMENTS);
        let blindings = (0..ROOT_SCALAR_COMMITMENTS)
            .map(|_| Scalar::random(rng))
            .collect::<Vec<_>>();

        let input_certificate_digest = input_certificate.transcript_digest();
        let joint_input_commitment = input_certificate.joint_input_commitment()?;
        let pc_gens = PedersenGens::default();
        let mut prover = Prover::new(
            &pc_gens,
            root_draft_transcript(
                session,
                input_certificate_digest,
                joint_input_commitment,
                statement,
            ),
        );
        let mut commitments = Vec::with_capacity(ROOT_SCALAR_COMMITMENTS);
        let mut variables = Vec::with_capacity(ROOT_SCALAR_COMMITMENTS);
        for (&value, &blinding) in values.iter().zip(&blindings) {
            let (commitment, variable) = prover.commit(value, blinding);
            commitments.push(commitment.to_bytes());
            variables.push(variable);
        }
        constrain_root_variables(
            &mut prover,
            statement,
            &variables,
            Some(codes),
            Some(witness.blinding),
        )
        .map_err(|_| DistributedRootError::InvalidProof)?;
        let root_proof = prover
            .prove(&ROOT_GENS)
            .map_err(|_| DistributedRootError::InvalidProof)?
            .to_bytes();
        if root_proof.len() != ROOT_R1CS_PROOF_BYTES {
            return Err(DistributedRootError::InvalidProof);
        }
        let scalar_commitments: [[u8; 32]; ROOT_SCALAR_COMMITMENTS] = commitments
            .try_into()
            .map_err(|_| DistributedRootError::InvalidDraft)?;
        let mut draft = Self {
            session_digest: session.digest(),
            relation_digest: session.relation_digest(),
            input_certificate_digest,
            joint_input_commitment,
            statement,
            scalar_commitments,
            root_proof,
            digest: [0; 32],
        };
        draft.digest = draft.compute_digest();
        draft.verify_after_verified_input(session, input_certificate, public_relation)?;

        let mut private_packets = Vec::with_capacity(ORDER_COUNT);
        for owner in 0..ORDER_COUNT {
            let mut commitment_blindings = vec![blindings[owner]];
            if owner == 0 {
                commitment_blindings.extend_from_slice(&blindings[ORDER_COUNT..]);
            }
            private_packets.push(PrivateRootLinkOpening {
                session_digest: session.digest(),
                input_certificate_digest,
                draft_digest: draft.digest,
                owner,
                commitment_blindings,
            });
        }
        Ok(RootLinkProverOutput {
            draft,
            private_packets,
        })
    }

    /// Complete standalone verification against independently supplied public
    /// session, input certificate, and clearing statement.
    pub fn verify(
        &self,
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<()> {
        if public_relation.relation_digest() != session.relation_digest() {
            return Err(DistributedRootError::SessionMismatch);
        }
        input_certificate.verify(session)?;
        self.verify_after_verified_input(session, input_certificate, public_relation)
    }

    /// Complete certificate verification when the caller has already verified
    /// the exact input certificate.  The independently derived BFV relation is
    /// still mandatory: no checked path accepts a parallel caller-supplied
    /// clearing statement.
    pub(crate) fn verify_after_verified_input(
        &self,
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<()> {
        if public_relation.relation_digest() != session.relation_digest() {
            return Err(DistributedRootError::SessionMismatch);
        }
        self.verify_after_verified_input_statement(
            session,
            input_certificate,
            public_relation.statement(),
        )
    }

    fn verify_after_verified_input_statement(
        &self,
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        statement: PublicStatement,
    ) -> Result<()> {
        if self.session_digest != session.digest()
            || self.relation_digest != session.relation_digest()
            || self.input_certificate_digest != input_certificate.transcript_digest()
            || self.joint_input_commitment != input_certificate.joint_input_commitment()?
            || self.statement != statement
            || !valid_statement(statement)
            || self.digest != self.compute_digest()
            || self.root_proof.len() != ROOT_R1CS_PROOF_BYTES
        {
            return Err(DistributedRootError::InvalidDraft);
        }
        let commitments = self
            .scalar_commitments
            .iter()
            .map(decode_compressed)
            .collect::<Result<Vec<_>>>()?;
        let proof = R1CSProof::from_bytes(&self.root_proof)
            .map_err(|_| DistributedRootError::InvalidProof)?;
        let mut verifier = Verifier::new(root_draft_transcript(
            session,
            self.input_certificate_digest,
            self.joint_input_commitment,
            statement,
        ));
        let variables = commitments
            .into_iter()
            .map(|commitment| verifier.commit(commitment))
            .collect::<Vec<_>>();
        constrain_root_variables(&mut verifier, statement, &variables, None, None)
            .map_err(|_| DistributedRootError::InvalidProof)?;
        verifier
            .verify(&proof, &PedersenGens::default(), &ROOT_GENS)
            .map_err(|_| DistributedRootError::InvalidProof)
    }

    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub const fn statement(&self) -> PublicStatement {
        self.statement
    }

    /// Canonical standalone draft transport. The verifier still supplies the
    /// independently derived BFV public relation and input certificate.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(ROOT_DRAFT_WIRE_BYTES);
        out.extend_from_slice(ROOT_DRAFT_MAGIC);
        out.extend_from_slice(&ROOT_WIRE_VERSION.to_be_bytes());
        out.extend_from_slice(&self.session_digest);
        out.extend_from_slice(&self.relation_digest);
        out.extend_from_slice(&self.input_certificate_digest);
        out.extend_from_slice(&self.joint_input_commitment);
        out.extend_from_slice(&encode_statement(self.statement));
        for commitment in &self.scalar_commitments {
            out.extend_from_slice(commitment);
        }
        out.extend_from_slice(&(self.root_proof.len() as u32).to_be_bytes());
        out.extend_from_slice(&self.root_proof);
        out.extend_from_slice(&self.digest);
        let checksum = wire_checksum(ROOT_DRAFT_CHECKSUM_DOMAIN, &out);
        out.extend_from_slice(&checksum);
        debug_assert_eq!(out.len(), ROOT_DRAFT_WIRE_BYTES);
        out
    }

    /// Strict canonical draft decode plus complete public re-verification.
    pub fn from_bytes(
        bytes: &[u8],
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        let draft = Self::decode_wire(bytes)?;
        draft.verify(session, input_certificate, public_relation)?;
        if draft.to_bytes() != bytes {
            return Err(DistributedRootError::MalformedWire);
        }
        Ok(draft)
    }

    fn decode_wire(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != ROOT_DRAFT_WIRE_BYTES {
            return Err(DistributedRootError::MalformedWire);
        }
        let checksum_start = bytes.len() - 32;
        if bytes[checksum_start..]
            != wire_checksum(ROOT_DRAFT_CHECKSUM_DOMAIN, &bytes[..checksum_start])
        {
            return Err(DistributedRootError::MalformedWire);
        }
        let mut reader = WireReader::new(&bytes[..checksum_start]);
        if reader.array::<8>()? != *ROOT_DRAFT_MAGIC || reader.u16()? != ROOT_WIRE_VERSION {
            return Err(DistributedRootError::MalformedWire);
        }
        let session_digest = reader.array::<32>()?;
        let relation_digest = reader.array::<32>()?;
        let input_certificate_digest = reader.array::<32>()?;
        let joint_input_commitment = reader.array::<32>()?;
        let statement = decode_statement(reader.array::<48>()?)?;
        let mut scalar_commitments = [[0u8; 32]; ROOT_SCALAR_COMMITMENTS];
        for commitment in &mut scalar_commitments {
            *commitment = reader.array::<32>()?;
            decode_compressed(commitment)?;
        }
        let root_proof_len = reader.usize_u32()?;
        if root_proof_len != ROOT_R1CS_PROOF_BYTES {
            return Err(DistributedRootError::MalformedWire);
        }
        let root_proof = reader.take(root_proof_len)?.to_vec();
        R1CSProof::from_bytes(&root_proof).map_err(|_| DistributedRootError::MalformedWire)?;
        let digest = reader.array::<32>()?;
        reader.finish()?;
        let draft = Self {
            session_digest,
            relation_digest,
            input_certificate_digest,
            joint_input_commitment,
            statement,
            scalar_commitments,
            root_proof,
            digest,
        };
        if draft.compute_digest() != digest {
            return Err(DistributedRootError::MalformedWire);
        }
        Ok(draft)
    }

    fn compute_digest(&self) -> [u8; 32] {
        let statement = encode_statement(self.statement);
        let mut hasher = blake3::Hasher::new_derive_key(ROOT_DRAFT_DOMAIN);
        hash_piece(&mut hasher, ROOT_SCHEMA);
        hash_piece(&mut hasher, &self.session_digest);
        hash_piece(&mut hasher, &self.relation_digest);
        hash_piece(&mut hasher, &self.input_certificate_digest);
        hash_piece(&mut hasher, &self.joint_input_commitment);
        hash_piece(&mut hasher, &statement);
        for commitment in &self.scalar_commitments {
            hash_piece(&mut hasher, commitment);
        }
        hash_piece(&mut hasher, &self.root_proof);
        *hasher.finalize().as_bytes()
    }
}

/// One signed owner-local link into the certified vector commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnerRootLinkProof {
    owner: usize,
    draft_digest: [u8; 32],
    link_proof: Vec<u8>,
    signature: [u8; 64],
}

/// Prove one owner's selected root coordinates without releasing the retained
/// vector or any opening blinding.
pub fn prove_owner_root_link<R: CryptoRng + RngCore>(
    continuation: &OwnerWitnessContinuation,
    session: &DistributedWitnessSession,
    input_certificate: &DistributedInputCertificate,
    draft: &RootLinkDraft,
    private_opening: PrivateRootLinkOpening,
    signing_key: &SigningKey,
    rng: &mut R,
) -> Result<OwnerRootLinkProof> {
    let owner = continuation.owner();
    if owner >= ORDER_COUNT || private_opening.owner != owner {
        return Err(DistributedRootError::PartyOutOfRange);
    }
    if continuation.session_digest() != session.digest()
        || private_opening.session_digest != session.digest()
        || private_opening.input_certificate_digest != input_certificate.transcript_digest()
        || private_opening.draft_digest != draft.digest
        || draft.session_digest != session.digest()
        || draft.input_certificate_digest != input_certificate.transcript_digest()
        || continuation.values().len() != session.local_witness_width()
    {
        return Err(DistributedRootError::SessionMismatch);
    }
    let expected_key = session
        .owner_key(owner)
        .ok_or(DistributedRootError::PartyOutOfRange)?;
    if signing_key.verifying_key().to_bytes() != expected_key {
        return Err(DistributedRootError::SigningKeyMismatch);
    }
    let expected_blindings = if owner == 0 {
        1 + ROOT_BLINDING_WIDTH
    } else {
        1
    };
    if private_opening.commitment_blindings.len() != expected_blindings {
        return Err(DistributedRootError::InvalidPrivateOpening);
    }

    let root_base = root_blinding_base(session);
    let values = continuation.values();
    let code_value = values[ROOT_CODE_COORDINATE];
    let pc_gens = PedersenGens::default();
    let code_commitment = decode_compressed(&draft.scalar_commitments[owner])?;
    if (code_value * pc_gens.B + private_opening.commitment_blindings[0] * pc_gens.B_blinding)
        .compress()
        != code_commitment
    {
        return Err(DistributedRootError::InvalidPrivateOpening);
    }
    if owner == 0 {
        for lane in 0..ROOT_BLINDING_WIDTH {
            let commitment = decode_compressed(&draft.scalar_commitments[ORDER_COUNT + lane])?;
            if (values[root_base + lane] * pc_gens.B
                + private_opening.commitment_blindings[1 + lane] * pc_gens.B_blinding)
                .compress()
                != commitment
            {
                return Err(DistributedRootError::InvalidPrivateOpening);
            }
        }
    } else if values[root_base..root_base + ROOT_BLINDING_WIDTH]
        .iter()
        .any(|value| *value != Scalar::ZERO)
    {
        return Err(DistributedRootError::InvalidPrivateOpening);
    }

    let coefficients = root_link_coefficients(draft, input_certificate, owner);
    let padded_width = session
        .local_witness_width()
        .checked_next_power_of_two()
        .ok_or(DistributedRootError::InvalidProof)?;
    let mut secret = values.to_vec();
    secret.resize(padded_width, Scalar::ZERO);
    let mut public_coefficients = vec![Scalar::ZERO; padded_width];
    public_coefficients[ROOT_CODE_COORDINATE] = coefficients[0];
    for lane in 0..ROOT_BLINDING_WIDTH {
        public_coefficients[root_base + lane] = coefficients[1 + lane];
    }

    let owner_commitment_bytes = input_certificate
        .owner_commitment(owner)
        .ok_or(DistributedRootError::PartyOutOfRange)?;
    let mut statement_point = decode_point(&owner_commitment_bytes)?
        + coefficients[0] * decode_root_point(&draft.scalar_commitments[owner])?;
    let mut aggregate_blinding =
        continuation.owner_blinding() + coefficients[0] * private_opening.commitment_blindings[0];
    if owner == 0 {
        for lane in 0..ROOT_BLINDING_WIDTH {
            statement_point += coefficients[1 + lane]
                * decode_root_point(&draft.scalar_commitments[ORDER_COUNT + lane])?;
            aggregate_blinding +=
                coefficients[1 + lane] * private_opening.commitment_blindings[1 + lane];
        }
    }
    let statement_commitment = statement_point.compress();
    let mut transcript =
        root_link_transcript(draft, input_certificate, owner, &owner_commitment_bytes);
    let link_proof = LinearProof::create(
        &mut transcript,
        rng,
        &statement_commitment,
        aggregate_blinding,
        secret,
        public_coefficients,
        owner_linear_generators(session, owner, padded_width)?,
        &pc_gens.B,
        &pc_gens.B_blinding,
    )
    .map_err(|_| DistributedRootError::InvalidProof)?
    .to_bytes();
    if link_proof.len() != expected_owner_link_proof_len(padded_width)? {
        return Err(DistributedRootError::InvalidProof);
    }
    let signature = signing_key
        .sign(&owner_signing_message(
            session.digest(),
            input_certificate.transcript_digest(),
            draft.digest,
            owner,
            &link_proof,
        ))
        .to_bytes();
    Ok(OwnerRootLinkProof {
        owner,
        draft_digest: draft.digest,
        link_proof,
        signature,
    })
}

/// Public certificate joining all four owner commitments to one nonlinear
/// private-root proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootLinkCertificate {
    session_digest: [u8; 32],
    input_certificate_digest: [u8; 32],
    draft: RootLinkDraft,
    owners: [OwnerRootLinkProof; ORDER_COUNT],
    transcript_digest: [u8; 32],
}

impl RootLinkCertificate {
    pub fn verify(
        &self,
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<()> {
        if public_relation.relation_digest() != session.relation_digest() {
            return Err(DistributedRootError::SessionMismatch);
        }
        input_certificate.verify(session)?;
        self.verify_after_verified_input(session, input_certificate, public_relation)
    }

    pub(crate) fn verify_after_verified_input(
        &self,
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<()> {
        if public_relation.relation_digest() != session.relation_digest() {
            return Err(DistributedRootError::SessionMismatch);
        }
        self.verify_after_verified_input_statement(
            session,
            input_certificate,
            public_relation.statement(),
        )
    }

    fn verify_after_verified_input_statement(
        &self,
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        statement: PublicStatement,
    ) -> Result<()> {
        if self.session_digest != session.digest()
            || self.input_certificate_digest != input_certificate.transcript_digest()
            || self.draft.statement != statement
        {
            return Err(DistributedRootError::SessionMismatch);
        }
        for owner in 0..ORDER_COUNT {
            let proof = &self.owners[owner];
            if proof.owner != owner || proof.draft_digest != self.draft.digest {
                return Err(DistributedRootError::InvalidProof);
            }
            verify_owner_signature(
                proof,
                session,
                self.input_certificate_digest,
                self.draft.digest,
            )?;
        }
        self.draft
            .verify_after_verified_input_statement(session, input_certificate, statement)?;
        for proof in &self.owners {
            verify_owner_link(proof, session, input_certificate, &self.draft)?;
        }
        if self.transcript_digest != self.compute_transcript_digest() {
            return Err(DistributedRootError::CertificateDigestMismatch);
        }
        Ok(())
    }

    pub const fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    /// Exact canonical certificate length under independently supplied session
    /// geometry.
    pub fn expected_wire_len(session: &DistributedWitnessSession) -> Result<usize> {
        let padded_width = session
            .local_witness_width()
            .checked_next_power_of_two()
            .ok_or(DistributedRootError::MalformedWire)?;
        let proof_len = expected_owner_link_proof_len(padded_width)?;
        // Fixed header + draft + owner count + four owner frames + transcript
        // digest + checksum.
        (8usize + 2 + 32 + 32 + 4 + ROOT_DRAFT_WIRE_BYTES + 2 + 32 + 32)
            .checked_add(
                ORDER_COUNT
                    .checked_mul(2 + 32 + 4 + proof_len + 64)
                    .ok_or(DistributedRootError::MalformedWire)?,
            )
            .ok_or(DistributedRootError::MalformedWire)
    }

    /// Canonical devnet-transportable public certificate.
    pub fn to_bytes(&self) -> Vec<u8> {
        let draft = self.draft.to_bytes();
        let mut out = Vec::new();
        out.extend_from_slice(ROOT_CERTIFICATE_MAGIC);
        out.extend_from_slice(&ROOT_WIRE_VERSION.to_be_bytes());
        out.extend_from_slice(&self.session_digest);
        out.extend_from_slice(&self.input_certificate_digest);
        out.extend_from_slice(&(draft.len() as u32).to_be_bytes());
        out.extend_from_slice(&draft);
        out.extend_from_slice(&(ORDER_COUNT as u16).to_be_bytes());
        for proof in &self.owners {
            out.extend_from_slice(&(proof.owner as u16).to_be_bytes());
            out.extend_from_slice(&proof.draft_digest);
            out.extend_from_slice(&(proof.link_proof.len() as u32).to_be_bytes());
            out.extend_from_slice(&proof.link_proof);
            out.extend_from_slice(&proof.signature);
        }
        out.extend_from_slice(&self.transcript_digest);
        let checksum = wire_checksum(ROOT_CERTIFICATE_CHECKSUM_DOMAIN, &out);
        out.extend_from_slice(&checksum);
        out
    }

    /// Framing-first strict decode followed by one complete verification pass.
    pub fn from_bytes(
        bytes: &[u8],
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        let certificate = Self::decode_certificate_wire(bytes, session)?;
        input_certificate.verify(session)?;
        certificate.verify_after_verified_input(session, input_certificate, public_relation)?;
        Ok(certificate)
    }

    /// Strict certificate decode for a composition which already accepted the
    /// exact input certificate.  This avoids re-running all base owner proofs
    /// while preserving every root proof, owner link, signature, digest, and
    /// canonical-wire check.
    pub(crate) fn from_bytes_after_verified_input(
        bytes: &[u8],
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        let certificate = Self::decode_certificate_wire(bytes, session)?;
        certificate.verify_after_verified_input(session, input_certificate, public_relation)?;
        Ok(certificate)
    }

    fn decode_certificate_wire(bytes: &[u8], session: &DistributedWitnessSession) -> Result<Self> {
        if bytes.len() != Self::expected_wire_len(session)? {
            return Err(DistributedRootError::MalformedWire);
        }
        let checksum_start = bytes.len() - 32;
        if bytes[checksum_start..]
            != wire_checksum(ROOT_CERTIFICATE_CHECKSUM_DOMAIN, &bytes[..checksum_start])
        {
            return Err(DistributedRootError::MalformedWire);
        }
        let padded_width = session
            .local_witness_width()
            .checked_next_power_of_two()
            .ok_or(DistributedRootError::MalformedWire)?;
        let expected_link_len = expected_owner_link_proof_len(padded_width)?;
        let mut reader = WireReader::new(&bytes[..checksum_start]);
        if reader.array::<8>()? != *ROOT_CERTIFICATE_MAGIC || reader.u16()? != ROOT_WIRE_VERSION {
            return Err(DistributedRootError::MalformedWire);
        }
        let session_digest = reader.array::<32>()?;
        let input_certificate_digest = reader.array::<32>()?;
        let draft_len = reader.usize_u32()?;
        if draft_len != ROOT_DRAFT_WIRE_BYTES {
            return Err(DistributedRootError::MalformedWire);
        }
        let draft = RootLinkDraft::decode_wire(reader.take(draft_len)?)?;
        if reader.u16()? as usize != ORDER_COUNT {
            return Err(DistributedRootError::MalformedWire);
        }
        let mut owners = Vec::with_capacity(ORDER_COUNT);
        for expected_owner in 0..ORDER_COUNT {
            let owner = reader.u16()? as usize;
            let draft_digest = reader.array::<32>()?;
            let link_len = reader.usize_u32()?;
            if owner != expected_owner || link_len != expected_link_len {
                return Err(DistributedRootError::MalformedWire);
            }
            let link_proof = reader.take(link_len)?.to_vec();
            LinearProof::from_bytes(&link_proof)
                .map_err(|_| DistributedRootError::MalformedWire)?;
            let signature = reader.array::<64>()?;
            owners.push(OwnerRootLinkProof {
                owner,
                draft_digest,
                link_proof,
                signature,
            });
        }
        let transcript_digest = reader.array::<32>()?;
        reader.finish()?;
        let certificate = Self {
            session_digest,
            input_certificate_digest,
            draft,
            owners: owners
                .try_into()
                .map_err(|_| DistributedRootError::MalformedWire)?,
            transcript_digest,
        };
        if certificate.to_bytes() != bytes {
            return Err(DistributedRootError::MalformedWire);
        }
        Ok(certificate)
    }

    fn compute_transcript_digest(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(ROOT_CERTIFICATE_DOMAIN);
        hash_piece(&mut hasher, ROOT_SCHEMA);
        hash_piece(&mut hasher, &self.session_digest);
        hash_piece(&mut hasher, &self.input_certificate_digest);
        hash_piece(&mut hasher, &self.draft.digest);
        for proof in &self.owners {
            hash_piece(&mut hasher, &(proof.owner as u64).to_be_bytes());
            hash_piece(&mut hasher, &proof.link_proof);
            hash_piece(&mut hasher, &proof.signature);
        }
        *hasher.finalize().as_bytes()
    }
}

/// Coordinator state machine accepting exactly one authenticated link from
/// each owner.
pub struct RootLinkCoordinator {
    session: DistributedWitnessSession,
    input_certificate: DistributedInputCertificate,
    draft: RootLinkDraft,
    owners: Vec<Option<OwnerRootLinkProof>>,
}

impl RootLinkCoordinator {
    pub fn new(
        session: DistributedWitnessSession,
        input_certificate: DistributedInputCertificate,
        draft: RootLinkDraft,
        public_relation: &DistributedBfvPublicRelation,
    ) -> Result<Self> {
        draft.verify(&session, &input_certificate, public_relation)?;
        Ok(Self {
            session,
            input_certificate,
            draft,
            owners: iter::repeat_with(|| None).take(ORDER_COUNT).collect(),
        })
    }

    pub fn accept(&mut self, proof: OwnerRootLinkProof) -> Result<()> {
        if proof.owner >= ORDER_COUNT {
            return Err(DistributedRootError::PartyOutOfRange);
        }
        if self.owners[proof.owner].is_some() {
            return Err(DistributedRootError::DuplicateOwner);
        }
        verify_owner_signature(
            &proof,
            &self.session,
            self.input_certificate.transcript_digest(),
            self.draft.digest,
        )?;
        verify_owner_link(&proof, &self.session, &self.input_certificate, &self.draft)?;
        let owner = proof.owner;
        self.owners[owner] = Some(proof);
        Ok(())
    }

    pub fn finish(self) -> Result<RootLinkCertificate> {
        let owners = self
            .owners
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or(DistributedRootError::MissingOwners)?
            .try_into()
            .map_err(|_| DistributedRootError::MissingOwners)?;
        let mut certificate = RootLinkCertificate {
            session_digest: self.session.digest(),
            input_certificate_digest: self.input_certificate.transcript_digest(),
            draft: self.draft,
            owners,
            transcript_digest: [0; 32],
        };
        certificate.transcript_digest = certificate.compute_transcript_digest();
        Ok(certificate)
    }
}

fn verify_owner_signature(
    proof: &OwnerRootLinkProof,
    session: &DistributedWitnessSession,
    input_certificate_digest: [u8; 32],
    draft_digest: [u8; 32],
) -> Result<()> {
    if proof.owner >= ORDER_COUNT || proof.draft_digest != draft_digest {
        return Err(DistributedRootError::InvalidSignature);
    }
    let key = VerifyingKey::from_bytes(
        &session
            .owner_key(proof.owner)
            .ok_or(DistributedRootError::PartyOutOfRange)?,
    )
    .map_err(|_| DistributedRootError::InvalidSignature)?;
    key.verify_strict(
        &owner_signing_message(
            session.digest(),
            input_certificate_digest,
            draft_digest,
            proof.owner,
            &proof.link_proof,
        ),
        &Signature::from_bytes(&proof.signature),
    )
    .map_err(|_| DistributedRootError::InvalidSignature)
}

fn verify_owner_link(
    proof: &OwnerRootLinkProof,
    session: &DistributedWitnessSession,
    input_certificate: &DistributedInputCertificate,
    draft: &RootLinkDraft,
) -> Result<()> {
    let padded_width = session
        .local_witness_width()
        .checked_next_power_of_two()
        .ok_or(DistributedRootError::InvalidProof)?;
    if proof.link_proof.len() != expected_owner_link_proof_len(padded_width)? {
        return Err(DistributedRootError::InvalidProof);
    }
    let linear = LinearProof::from_bytes(&proof.link_proof)
        .map_err(|_| DistributedRootError::InvalidProof)?;
    let coefficients = root_link_coefficients(draft, input_certificate, proof.owner);
    let root_base = root_blinding_base(session);
    let mut public_coefficients = vec![Scalar::ZERO; padded_width];
    public_coefficients[ROOT_CODE_COORDINATE] = coefficients[0];
    for lane in 0..ROOT_BLINDING_WIDTH {
        public_coefficients[root_base + lane] = coefficients[1 + lane];
    }
    let owner_commitment_bytes = input_certificate
        .owner_commitment(proof.owner)
        .ok_or(DistributedRootError::PartyOutOfRange)?;
    let mut statement_point = decode_point(&owner_commitment_bytes)?
        + coefficients[0] * decode_root_point(&draft.scalar_commitments[proof.owner])?;
    if proof.owner == 0 {
        for lane in 0..ROOT_BLINDING_WIDTH {
            statement_point += coefficients[1 + lane]
                * decode_root_point(&draft.scalar_commitments[ORDER_COUNT + lane])?;
        }
    }
    let mut transcript = root_link_transcript(
        draft,
        input_certificate,
        proof.owner,
        &owner_commitment_bytes,
    );
    let pc_gens = PedersenGens::default();
    linear
        .verify(
            &mut transcript,
            &statement_point.compress(),
            &owner_linear_generators(session, proof.owner, padded_width)?,
            &pc_gens.B,
            &pc_gens.B_blinding,
            public_coefficients,
        )
        .map_err(|_| DistributedRootError::InvalidProof)
}

fn constrain_root_variables<CS: ConstraintSystem>(
    cs: &mut CS,
    statement: PublicStatement,
    variables: &[Variable],
    code_values: Option<[u32; ORDER_COUNT]>,
    blinding_values: Option<[u32; ROOT_BLINDING_WIDTH]>,
) -> std::result::Result<(), bulletproofs_r1cs::r1cs::R1CSError> {
    if variables.len() != ROOT_SCALAR_COMMITMENTS {
        return Err(bulletproofs_r1cs::r1cs::R1CSError::GadgetError {
            description: "wrong distributed root variable count".to_owned(),
        });
    }
    let mut packed = LinearCombination::from(Scalar::ZERO);
    let mut packed_value = 0u64;
    for owner in 0..ORDER_COUNT {
        let place = 128u64.pow(owner as u32);
        packed = packed + variables[owner] * Scalar::from(place);
        if let Some(codes) = code_values {
            packed_value += u64::from(codes[owner]) * place;
        }
    }
    let blind_variables: [Variable; ROOT_BLINDING_WIDTH] = variables[ORDER_COUNT..]
        .try_into()
        .expect("eight committed root blinding variables");
    constrain_poseidon_root_with_blinding_variables(
        cs,
        statement,
        packed,
        code_values.map(|_| packed_value),
        &blind_variables,
        blinding_values,
    )
}

fn root_draft_transcript(
    session: &DistributedWitnessSession,
    input_certificate_digest: [u8; 32],
    joint_input_commitment: [u8; 32],
    statement: PublicStatement,
) -> Transcript {
    let mut transcript = Transcript::new(ROOT_DRAFT_TRANSCRIPT);
    transcript.append_message(b"schema", ROOT_SCHEMA);
    transcript.append_message(b"session", &session.digest());
    transcript.append_message(b"relation", &session.relation_digest());
    transcript.append_message(b"input-certificate", &input_certificate_digest);
    transcript.append_message(b"joint-input", &joint_input_commitment);
    transcript.append_message(b"statement", &encode_statement(statement));
    transcript
}

fn root_link_transcript(
    draft: &RootLinkDraft,
    input_certificate: &DistributedInputCertificate,
    owner: usize,
    owner_commitment: &[u8; 32],
) -> Transcript {
    let mut transcript = Transcript::new(ROOT_LINK_TRANSCRIPT);
    transcript.append_message(b"schema", ROOT_SCHEMA);
    transcript.append_message(b"draft", &draft.digest);
    transcript.append_message(b"input-certificate", &input_certificate.transcript_digest());
    transcript.append_u64(b"owner", owner as u64);
    transcript.append_message(b"owner-commitment", owner_commitment);
    for commitment in &draft.scalar_commitments {
        transcript.append_message(b"root-scalar", commitment);
    }
    transcript.append_message(b"root-proof", &draft.root_proof);
    transcript
}

fn root_link_coefficients(
    draft: &RootLinkDraft,
    input_certificate: &DistributedInputCertificate,
    owner: usize,
) -> [Scalar; 1 + ROOT_BLINDING_WIDTH] {
    core::array::from_fn(|coordinate| {
        nonzero_coefficient(
            draft.digest,
            input_certificate.transcript_digest(),
            owner,
            coordinate,
        )
    })
}

fn nonzero_coefficient(
    draft_digest: [u8; 32],
    input_certificate_digest: [u8; 32],
    owner: usize,
    coordinate: usize,
) -> Scalar {
    for counter in 0u64.. {
        let mut hasher = blake3::Hasher::new_derive_key(ROOT_COEFFICIENT_DOMAIN);
        hasher.update(&draft_digest);
        hasher.update(&input_certificate_digest);
        hasher.update(&(owner as u64).to_be_bytes());
        hasher.update(&(coordinate as u64).to_be_bytes());
        hasher.update(&counter.to_be_bytes());
        let mut wide = [0u8; 64];
        hasher.finalize_xof().fill(&mut wide);
        let scalar = Scalar::from_bytes_mod_order_wide(&wide);
        if scalar != Scalar::ZERO {
            return scalar;
        }
    }
    unreachable!("u64 coefficient counter exhausted")
}

fn owner_signing_message(
    session_digest: [u8; 32],
    input_certificate_digest: [u8; 32],
    draft_digest: [u8; 32],
    owner: usize,
    link_proof: &[u8],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(ROOT_LINK_SIGNATURE_DOMAIN);
    hash_piece(&mut hasher, ROOT_SCHEMA);
    hash_piece(&mut hasher, &session_digest);
    hash_piece(&mut hasher, &input_certificate_digest);
    hash_piece(&mut hasher, &draft_digest);
    hash_piece(&mut hasher, &(owner as u64).to_be_bytes());
    hash_piece(&mut hasher, link_proof);
    *hasher.finalize().as_bytes()
}

fn order_code(order: dark_bazaar_private::PrivateOrder) -> u32 {
    let kind = u32::from(order.limit)
        + match order.side {
            Side::Bid => 0,
            Side::Ask => dark_bazaar_private::PRICE_COUNT as u32,
        };
    kind + 8 * u32::from(order.qty)
}

fn root_blinding_base(session: &DistributedWitnessSession) -> usize {
    DERIVED_ORDER_WIDTH + 3 * session.degree()
}

fn valid_statement(statement: PublicStatement) -> bool {
    statement.session < crate::private_book_distributed_inputs::BABYBEAR_MODULUS
        && statement.rule == RULE_ID
        && (statement.p_star as usize) < dark_bazaar_private::PRICE_COUNT
        && statement.v_star <= ORDER_COUNT as u32 * u32::from(dark_bazaar_private::MAX_QTY)
        && statement
            .order_root
            .iter()
            .all(|lane| *lane < crate::private_book_distributed_inputs::BABYBEAR_MODULUS)
}

fn encode_statement(statement: PublicStatement) -> [u8; 48] {
    let mut bytes = [0u8; 48];
    let values = [statement.session, statement.rule]
        .into_iter()
        .chain(statement.order_root)
        .chain([statement.p_star, statement.v_star]);
    for (index, value) in values.enumerate() {
        bytes[index * 4..index * 4 + 4].copy_from_slice(&value.to_be_bytes());
    }
    bytes
}

fn decode_statement(bytes: [u8; 48]) -> Result<PublicStatement> {
    let mut values = [0u32; 12];
    for (index, value) in values.iter_mut().enumerate() {
        *value = u32::from_be_bytes(
            bytes[index * 4..index * 4 + 4]
                .try_into()
                .expect("four-byte statement lane"),
        );
    }
    let statement = PublicStatement {
        session: values[0],
        rule: values[1],
        order_root: values[2..10]
            .try_into()
            .expect("eight root statement lanes"),
        p_star: values[10],
        v_star: values[11],
    };
    valid_statement(statement)
        .then_some(statement)
        .ok_or(DistributedRootError::MalformedWire)
}

fn decode_compressed(bytes: &[u8; 32]) -> Result<CompressedRistretto> {
    let compressed = CompressedRistretto(*bytes);
    let point = compressed
        .decompress()
        .ok_or(DistributedRootError::InvalidCommitment)?;
    if point.compress().to_bytes() != *bytes {
        return Err(DistributedRootError::InvalidCommitment);
    }
    Ok(compressed)
}

fn decode_root_point(bytes: &[u8; 32]) -> Result<RistrettoPoint> {
    decode_compressed(bytes)?
        .decompress()
        .ok_or(DistributedRootError::InvalidCommitment)
}

fn hash_piece(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn wire_checksum(domain: &str, bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hash_piece(&mut hasher, bytes);
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

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(DistributedRootError::MalformedWire)?;
        let slice = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(slice)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.take(N)?
            .try_into()
            .map_err(|_| DistributedRootError::MalformedWire)
    }

    fn u16(&mut self) -> Result<u16> {
        Ok(u16::from_be_bytes(self.array()?))
    }

    fn usize_u32(&mut self) -> Result<usize> {
        usize::try_from(u32::from_be_bytes(self.array()?))
            .map_err(|_| DistributedRootError::MalformedWire)
    }

    fn finish(self) -> Result<()> {
        (self.offset == self.bytes.len())
            .then_some(())
            .ok_or(DistributedRootError::MalformedWire)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::private_book_distributed_bfv::{DistributedBfvRound, OwnerBfvQuotients};
    use crate::private_book_distributed_inputs::{
        DealerOutput, DistributedInputCoordinator, LocalOrderWitness, PrivateSide,
        WitnessPartyMachine,
    };
    use crate::private_book_relation::{encrypt_private_book, PrivateBookEncryptionOpening};
    use crate::threshold::{
        BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    };
    use dregg_circuit_prove::dark_bazaar_private::{verify_zk, PrivateOrder};
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    fn signing_keys<const N: usize>(base: u8) -> [SigningKey; N] {
        core::array::from_fn(|index| SigningKey::from_bytes(&[base + index as u8; 32]))
    }

    fn collective_keygen(session: &KeygenSession, params: &BfvParams) -> CollectivePublicKey {
        let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
        for party in 0..session.n_parties() {
            let (_state, contribution) = ThresholdParty::join(session, party, params).unwrap();
            coordinator.accept(contribution).unwrap();
        }
        coordinator.finish().unwrap()
    }

    fn prepare_mismatched_book(
        session: &DistributedWitnessSession,
        witness_a: &PrivateBookWitness,
        root_blinding_b: [u32; ROOT_BLINDING_WIDTH],
        seeds: [[u8; 32]; ORDER_COUNT],
        owner_keys: &[SigningKey; ORDER_COUNT],
        worker_keys: &[SigningKey; 3],
    ) -> (DistributedInputCertificate, Vec<OwnerWitnessContinuation>) {
        let mut workers = worker_keys
            .iter()
            .enumerate()
            .map(|(worker, key)| {
                WitnessPartyMachine::new(session.clone(), worker, key.clone()).unwrap()
            })
            .collect::<Vec<_>>();
        let mut coordinator = DistributedInputCoordinator::new(session.clone());
        let mut continuations = Vec::with_capacity(ORDER_COUNT);
        for owner in 0..ORDER_COUNT {
            let order = witness_a.orders[owner];
            let local = LocalOrderWitness::from_seed(
                session,
                owner,
                match order.side {
                    Side::Bid => PrivateSide::Bid,
                    Side::Ask => PrivateSide::Ask,
                },
                order.limit,
                order.qty,
                seeds[owner],
                (owner == 0).then_some(root_blinding_b),
            )
            .unwrap();
            let mut rng = StdRng::from_seed([0x90 + owner as u8; 32]);
            let DealerOutput {
                contribution,
                private_packets,
                continuation,
            } = local.deal(session, &owner_keys[owner], &mut rng).unwrap();
            let public = contribution.clone();
            coordinator.accept_dealer(contribution).unwrap();
            for (worker, packet) in private_packets.into_iter().enumerate() {
                let acknowledgement = workers[worker].accept(&public, packet).unwrap();
                coordinator.accept_acknowledgement(acknowledgement).unwrap();
            }
            continuations.push(continuation);
        }
        for worker in workers {
            worker.finish().unwrap();
        }
        (coordinator.finish().unwrap(), continuations)
    }

    #[test]
    fn production_bfv_book_a_and_valid_hidingfri_book_b_cannot_cross_pair() {
        let params = BfvParams::fold_set();
        let key_session = KeygenSession::from_seed(2, [0x21; 32]).unwrap();
        let public_key = collective_keygen(&key_session, &params);
        let witness_a = PrivateBookWitness::try_from_orders_with_blinding(
            &[
                PrivateOrder::bid(10, 2),
                PrivateOrder::bid(6, 1),
                PrivateOrder::ask(5, 0),
                PrivateOrder::ask(8, 1),
            ],
            [17_000; ROOT_BLINDING_WIDTH],
        )
        .unwrap();
        // Owner one differs, while the distributed A vector deliberately uses
        // B's global blind. Thus the old parallel-proof composition has no
        // public root-blind mismatch to save it: only the code link can refuse.
        let witness_b = PrivateBookWitness::try_from_orders_with_blinding(
            &[
                witness_a.orders[0],
                PrivateOrder::bid(9, 3),
                witness_a.orders[2],
                witness_a.orders[3],
            ],
            [23_000; ROOT_BLINDING_WIDTH],
        )
        .unwrap();
        let seeds = [[0x31; 32], [0x32; 32], [0x33; 32], [0x34; 32]];
        let opening_a = PrivateBookEncryptionOpening::from_seeds(seeds);
        let ciphertexts_a =
            encrypt_private_book(&witness_a, &opening_a, &params, &public_key).unwrap();
        let (hiding_b, statement_b) = dark_bazaar_private::prove_zk(0xDBA2, &witness_b).unwrap();
        verify_zk(&hiding_b, statement_b).unwrap();

        // This exact public coefficient family is deliberately statement B +
        // ciphertext rows A. The distributed BFV algebra can still be valid
        // for A because the root was previously only transcript metadata.
        let public_b =
            DistributedBfvPublicRelation::derive(statement_b, &ciphertexts_a, &params, &public_key)
                .unwrap();
        let owner_keys = signing_keys::<ORDER_COUNT>(0x40);
        let worker_keys = signing_keys::<3>(0x60);
        let session = DistributedWitnessSession::new_for_test(
            public_b.relation_digest(),
            [0x80; 32],
            owner_keys
                .each_ref()
                .map(|key| key.verifying_key().to_bytes()),
            worker_keys
                .iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            params.degree(),
        )
        .unwrap();
        let (input_a, continuations_a) = prepare_mismatched_book(
            &session,
            &witness_a,
            witness_b.blinding,
            seeds,
            &owner_keys,
            &worker_keys,
        );
        let mut root_rng = StdRng::from_seed([0xa0; 32]);
        let root_b =
            RootLinkDraft::create(&session, &input_a, &public_b, &witness_b, &mut root_rng)
                .unwrap();
        assert_eq!(root_b.draft.statement(), statement_b);

        let mut packets = root_b.private_packets.into_iter();
        let packet0 = packets.next().unwrap();
        let mut owner_rng = StdRng::from_seed([0xb0; 32]);
        prove_owner_root_link(
            &continuations_a[0],
            &session,
            &input_a,
            &root_b.draft,
            packet0,
            &owner_keys[0],
            &mut owner_rng,
        )
        .expect("unchanged owner zero and B blind link");
        let packet1 = packets.next().unwrap();
        let mut owner_rng = StdRng::from_seed([0xb1; 32]);
        assert!(matches!(
            prove_owner_root_link(
                &continuations_a[1],
                &session,
                &input_a,
                &root_b.draft,
                packet1,
                &owner_keys[1],
                &mut owner_rng,
            ),
            Err(DistributedRootError::InvalidPrivateOpening)
        ));

        // The other leg is not a toy vector: at deployed BFV degree, every
        // owner-A continuation exactly satisfies the independently derived
        // ciphertext-A/public-statement-B integer equations. Before the root
        // link, these were sufficient inputs to the complete BFV ceremony.
        let round = DistributedBfvRound::new(&session, &input_a, &public_b).unwrap();
        for continuation in continuations_a {
            OwnerBfvQuotients::derive_exact(&round, continuation, &public_b)
                .expect("production BFV book A has exact bounded quotients");
        }
    }
}

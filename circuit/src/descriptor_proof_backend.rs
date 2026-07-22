//! Proof-system seam for the canonical DescriptorIR-v2 relation.
//!
//! The semantic program and public statement are backend-independent:
//! [`DescriptorStatementV1`] carries the exact supplied DescriptorIR-v2 bytes
//! plus a canonical BabyBear public-input vector.  Registry/provenance checks
//! authenticate whether those bytes are an approved Lean-emitted program.  A
//! proof backend may choose a different PCS, transcript, distributed proving
//! protocol, or witness custody model, but it does not get to reinterpret those
//! public bytes.
//!
//! The witness is deliberately *not* part of the common interface.  The
//! reference Plonky3 backend consumes a complete local IR-v2 trace through
//! [`Plonky3HidingFriWitness`].  A future collaborative backend can instead use
//! party-local shares as its associated witness type without first assembling a
//! no-viewer witness in one process.
//!
//! This is a compile-time seam, not a proof-wire registry.  Production proof
//! envelopes still need to bind `BACKEND_ID`, statement id, proof bytes, and
//! verifier-parameter identity before multiple proof systems can coexist on a
//! network boundary.  The current STARK binds the parsed relation and public
//! inputs; exact source-byte identity remains the registry/envelope's job.

use serde::{Serialize, de::DeserializeOwned};

use crate::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::heap_root::HeapLeaf;
use crate::stark_zk::{DreggZkStarkConfig, create_zk_config};

/// Domain/version prefix of the canonical DescriptorIR statement encoding.
///
/// Layout after the prefix:
/// `descriptor_len:u64-le || descriptor_bytes || pi_count:u64-le || pi:u32-le*`.
pub const DESCRIPTOR_STATEMENT_V1_MAGIC: &[u8] = b"dregg-ir2-statement-v1\0";
/// BLAKE3 derive-key context for [`DescriptorStatementV1::statement_id`].
pub const DESCRIPTOR_STATEMENT_V1_HASH_CONTEXT: &str = "dregg DescriptorStatementV1 identity";

/// Exact public relation identity shared by every DescriptorIR-v2 proof backend.
///
/// Descriptor bytes are intentionally not JSON-normalized.  The supplied bytes
/// form the program identity consumed by the custom-VK registry; registry and
/// provenance checks separately authenticate whether they are approved
/// Lean-emitted bytes.  Whitespace or field-order changes therefore produce a
/// different statement id even if a permissive JSON parser assigns the same
/// meaning.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DescriptorStatementV1 {
    descriptor_program: Vec<u8>,
    public_inputs: Vec<u32>,
}

impl DescriptorStatementV1 {
    /// Construct and validate one canonical DescriptorIR-v2 public statement.
    pub fn try_new(
        descriptor_program: impl Into<Vec<u8>>,
        public_inputs: Vec<u32>,
    ) -> Result<Self, String> {
        let statement = Self {
            descriptor_program: descriptor_program.into(),
            public_inputs,
        };
        statement.validate()?;
        Ok(statement)
    }

    /// The exact supplied DescriptorIR-v2 program bytes.
    pub fn descriptor_program(&self) -> &[u8] {
        &self.descriptor_program
    }

    /// Canonical BabyBear public inputs (`0 <= pi < BABYBEAR_P`).
    pub fn public_inputs(&self) -> &[u32] {
        &self.public_inputs
    }

    /// Parse the exact program bytes with the deployed DescriptorIR-v2 parser.
    pub fn parse_descriptor(&self) -> Result<EffectVmDescriptor2, String> {
        let json = core::str::from_utf8(&self.descriptor_program)
            .map_err(|e| format!("DescriptorIR program is not UTF-8: {e}"))?;
        require_one_complete_json_object(json)?;
        parse_vm_descriptor2(json)
    }

    /// Convert the already-canonical public input words to the deployed field wrapper.
    pub fn public_input_felts(&self) -> Vec<BabyBear> {
        self.public_inputs
            .iter()
            .copied()
            .map(BabyBear::new)
            .collect()
    }

    /// Validate parser acceptance, PI arity, and unique field encodings.
    pub fn validate(&self) -> Result<(), String> {
        let desc = self.parse_descriptor()?;
        if self.public_inputs.len() != desc.public_input_count {
            return Err(format!(
                "DescriptorIR statement carries {} public inputs but `{}` declares {}",
                self.public_inputs.len(),
                desc.name,
                desc.public_input_count
            ));
        }
        for (index, value) in self.public_inputs.iter().copied().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "DescriptorIR public input {index}={value} is not canonical BabyBear"
                ));
            }
        }
        Ok(())
    }

    /// Canonical backend-independent bytes of this exact program + public statement.
    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            DESCRIPTOR_STATEMENT_V1_MAGIC.len()
                + 16
                + self.descriptor_program.len()
                + 4 * self.public_inputs.len(),
        );
        out.extend_from_slice(DESCRIPTOR_STATEMENT_V1_MAGIC);
        out.extend_from_slice(&(self.descriptor_program.len() as u64).to_le_bytes());
        out.extend_from_slice(&self.descriptor_program);
        out.extend_from_slice(&(self.public_inputs.len() as u64).to_le_bytes());
        for value in &self.public_inputs {
            out.extend_from_slice(&value.to_le_bytes());
        }
        out
    }

    /// Decode the canonical encoding, refusing truncation, trailing bytes, and
    /// non-canonical field words.
    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self, String> {
        if !bytes.starts_with(DESCRIPTOR_STATEMENT_V1_MAGIC) {
            return Err("DescriptorIR statement magic/version mismatch".to_string());
        }
        let mut cursor = DESCRIPTOR_STATEMENT_V1_MAGIC.len();
        let descriptor_len = read_u64(bytes, &mut cursor, "descriptor length")?;
        let descriptor_len = usize::try_from(descriptor_len)
            .map_err(|_| "DescriptorIR descriptor length does not fit usize".to_string())?;
        let descriptor_end = cursor
            .checked_add(descriptor_len)
            .ok_or_else(|| "DescriptorIR descriptor length overflow".to_string())?;
        let descriptor_program = bytes
            .get(cursor..descriptor_end)
            .ok_or_else(|| "truncated DescriptorIR program bytes".to_string())?
            .to_vec();
        cursor = descriptor_end;

        let pi_count = read_u64(bytes, &mut cursor, "public-input count")?;
        let pi_count = usize::try_from(pi_count)
            .map_err(|_| "DescriptorIR public-input count does not fit usize".to_string())?;
        let pi_bytes = pi_count
            .checked_mul(4)
            .ok_or_else(|| "DescriptorIR public-input byte length overflow".to_string())?;
        let expected_end = cursor
            .checked_add(pi_bytes)
            .ok_or_else(|| "DescriptorIR statement length overflow".to_string())?;
        if expected_end != bytes.len() {
            return Err(if expected_end > bytes.len() {
                "truncated DescriptorIR public-input vector".to_string()
            } else {
                "trailing bytes after DescriptorIR public-input vector".to_string()
            });
        }
        let mut public_inputs = Vec::with_capacity(pi_count);
        for chunk in bytes[cursor..expected_end].chunks_exact(4) {
            public_inputs.push(u32::from_le_bytes(
                chunk.try_into().expect("chunk width is four"),
            ));
        }
        Self::try_new(descriptor_program, public_inputs)
    }

    /// Domain-separated identity of the exact canonical statement bytes.
    pub fn statement_id(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key(DESCRIPTOR_STATEMENT_V1_HASH_CONTEXT);
        h.update(&self.to_canonical_bytes());
        *h.finalize().as_bytes()
    }
}

fn read_u64(bytes: &[u8], cursor: &mut usize, what: &str) -> Result<u64, String> {
    let end = cursor
        .checked_add(8)
        .ok_or_else(|| format!("{what} offset overflow"))?;
    let raw = bytes
        .get(*cursor..end)
        .ok_or_else(|| format!("truncated DescriptorIR {what}"))?;
    *cursor = end;
    Ok(u64::from_le_bytes(
        raw.try_into().expect("slice width is eight"),
    ))
}

/// The deployed DescriptorIR parser historically stops after the first top-level
/// object.  The backend-neutral statement boundary cannot inherit that behavior:
/// otherwise `valid_descriptor || attacker_suffix` would acquire a distinct id
/// while the verifier silently ignored the suffix.  Require one complete object
/// before handing bytes to the existing grammar parser.
fn require_one_complete_json_object(json: &str) -> Result<(), String> {
    let bytes = json.as_bytes();
    let mut cursor = 0;
    while bytes.get(cursor).is_some_and(u8::is_ascii_whitespace) {
        cursor += 1;
    }
    if bytes.get(cursor) != Some(&b'{') {
        return Err("DescriptorIR program must be one JSON object".to_string());
    }

    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut object_end = None;
    for (offset, byte) in bytes[cursor..].iter().copied().enumerate() {
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            continue;
        }
        match byte {
            b'"' => in_string = true,
            b'{' => depth += 1,
            b'}' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| "unbalanced DescriptorIR JSON object".to_string())?;
                if depth == 0 {
                    object_end = Some(cursor + offset + 1);
                    break;
                }
            }
            _ => {}
        }
    }
    let object_end =
        object_end.ok_or_else(|| "unterminated DescriptorIR JSON object".to_string())?;
    if bytes[object_end..]
        .iter()
        .any(|byte| !byte.is_ascii_whitespace())
    {
        return Err("trailing bytes after DescriptorIR JSON object".to_string());
    }
    Ok(())
}

/// Verify one proof against the backend-neutral DescriptorIR statement.
pub trait DescriptorProofVerifier: Send + Sync + 'static {
    /// Backend-native proof representation.
    type Proof: Serialize + DeserializeOwned;

    /// Stable implementation/protocol identity.  This must move whenever proof
    /// bytes or verifier semantics move; a future proof envelope will bind it.
    const BACKEND_ID: &'static str;

    /// Verify `proof` against the relation and public inputs selected by `statement`.
    fn verify(statement: &DescriptorStatementV1, proof: &Self::Proof) -> Result<(), String>;
}

/// Prove the canonical relation, with a backend-specific witness custody shape.
pub trait DescriptorProofProver: DescriptorProofVerifier {
    /// The prover input for one call.  It is deliberately backend-specific: a
    /// collaborative prover can use party-local shares rather than a full trace.
    type Witness<'a>
    where
        Self: 'a;

    /// Produce a proof for exactly `statement`.
    fn prove<'a>(
        statement: &DescriptorStatementV1,
        witness: Self::Witness<'a>,
    ) -> Result<Self::Proof, String>;
}

/// Complete local witness used by the current Plonky3 HidingFRI reference backend.
#[derive(Clone, Copy)]
pub struct Plonky3HidingFriWitness<'a> {
    /// Descriptor-width main trace before descriptor-driven auxiliary-lane fill.
    pub base_trace: &'a [Vec<BabyBear>],
    /// Declared ordinary-memory addresses and initial image.
    pub mem_boundary: &'a MemBoundaryWitness,
    /// One canonical heap image per map-opening relation.
    pub map_heaps: &'a [Vec<HeapLeaf>],
    /// Declared universal-memory addresses and initial optional image.
    pub umem_boundary: &'a UMemBoundaryWitness,
}

/// The currently deployed DescriptorIR proof engine, retained as the reference
/// backend while alternative PCS/recursion implementations are developed.
pub struct Plonky3HidingFriReference;

impl DescriptorProofVerifier for Plonky3HidingFriReference {
    type Proof = Ir2BatchProof<DreggZkStarkConfig>;

    const BACKEND_ID: &'static str = "plonky3-hidingfri-babybear-ir2@82cfad73cd734d37a0d51953094f970c531817ec|lb3|lfp0|arity3|q38|qpow16|ext4|salt4|random-codewords4";

    fn verify(statement: &DescriptorStatementV1, proof: &Self::Proof) -> Result<(), String> {
        statement.validate()?;
        verify_vm_descriptor2_with_config(
            &statement.parse_descriptor()?,
            proof,
            &statement.public_input_felts(),
            &create_zk_config(),
        )
    }
}

impl DescriptorProofProver for Plonky3HidingFriReference {
    type Witness<'a> = Plonky3HidingFriWitness<'a>;

    fn prove<'a>(
        statement: &DescriptorStatementV1,
        witness: Self::Witness<'a>,
    ) -> Result<Self::Proof, String> {
        statement.validate()?;
        prove_vm_descriptor2_for_config(
            &statement.parse_descriptor()?,
            witness.base_trace,
            &statement.public_input_felts(),
            witness.mem_boundary,
            witness.map_heaps,
            witness.umem_boundary,
            &create_zk_config(),
        )
    }
}

/// Outcome of a two-backend proving differential over one exact statement.
pub enum DifferentialProofOutcome<ReferenceProof, CandidateProof> {
    /// Both backends produced and accepted their backend-native proof.
    Accepted {
        reference: ReferenceProof,
        candidate: CandidateProof,
    },
    /// Both backends refused the witness before producing a proof.
    Rejected {
        reference: String,
        candidate: String,
    },
}

/// Acceptance decision of a two-backend verifier differential.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DifferentialVerifyDecision {
    Accepted,
    Rejected,
}

/// Run two backend verifiers against the *same immutable statement object*.
///
/// Agreement is only an empirical differential, not a proof of either backend's
/// soundness.  Its purpose is to make relation/statement drift immediately
/// testable while a new implementation is brought up.
pub fn differential_verify<Reference, Candidate>(
    statement: &DescriptorStatementV1,
    reference_proof: &Reference::Proof,
    candidate_proof: &Candidate::Proof,
) -> Result<DifferentialVerifyDecision, String>
where
    Reference: DescriptorProofVerifier,
    Candidate: DescriptorProofVerifier,
{
    let reference = Reference::verify(statement, reference_proof);
    let candidate = Candidate::verify(statement, candidate_proof);
    match (reference, candidate) {
        (Ok(()), Ok(())) => Ok(DifferentialVerifyDecision::Accepted),
        (Err(_), Err(_)) => Ok(DifferentialVerifyDecision::Rejected),
        (Ok(()), Err(candidate)) => Err(format!(
            "backend differential mismatch: reference `{}` accepted but candidate `{}` refused: {candidate}",
            Reference::BACKEND_ID,
            Candidate::BACKEND_ID,
        )),
        (Err(reference), Ok(())) => Err(format!(
            "backend differential mismatch: reference `{}` refused ({reference}) but candidate `{}` accepted",
            Reference::BACKEND_ID,
            Candidate::BACKEND_ID,
        )),
    }
}

/// Prove and then verify the same canonical statement with two real backends.
///
/// The two witness values may have different types.  That is load-bearing for a
/// future no-viewer backend whose input is a set of party-local shares rather
/// than the reference backend's assembled trace.
pub fn differential_prove_and_verify<'reference, 'candidate, Reference, Candidate>(
    statement: &DescriptorStatementV1,
    reference_witness: Reference::Witness<'reference>,
    candidate_witness: Candidate::Witness<'candidate>,
) -> Result<DifferentialProofOutcome<Reference::Proof, Candidate::Proof>, String>
where
    Reference: DescriptorProofProver + 'reference,
    Candidate: DescriptorProofProver + 'candidate,
{
    let reference = Reference::prove(statement, reference_witness);
    let candidate = Candidate::prove(statement, candidate_witness);
    match (reference, candidate) {
        (Err(reference), Err(candidate)) => Ok(DifferentialProofOutcome::Rejected {
            reference,
            candidate,
        }),
        (Ok(_), Err(candidate)) => Err(format!(
            "backend proving differential mismatch: reference `{}` produced a proof but candidate `{}` refused: {candidate}",
            Reference::BACKEND_ID,
            Candidate::BACKEND_ID,
        )),
        (Err(reference), Ok(_)) => Err(format!(
            "backend proving differential mismatch: reference `{}` refused ({reference}) but candidate `{}` produced a proof",
            Reference::BACKEND_ID,
            Candidate::BACKEND_ID,
        )),
        (Ok(reference), Ok(candidate)) => {
            match differential_verify::<Reference, Candidate>(statement, &reference, &candidate)? {
                DifferentialVerifyDecision::Accepted => Ok(DifferentialProofOutcome::Accepted {
                    reference,
                    candidate,
                }),
                DifferentialVerifyDecision::Rejected => Err(format!(
                    "both backends produced proofs that their own verifiers refused (`{}`, `{}`)",
                    Reference::BACKEND_ID,
                    Candidate::BACKEND_ID,
                )),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_DESCRIPTOR: &str = "{\"name\":\"descriptor-backend-seam-v1\",\"ir\":2,\"trace_width\":1,\"public_input_count\":1,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0}],\"hash_sites\":[],\"ranges\":[]}";

    fn test_statement(value: u32) -> DescriptorStatementV1 {
        DescriptorStatementV1::try_new(TEST_DESCRIPTOR.as_bytes(), vec![value]).unwrap()
    }

    fn rows(value: u32) -> Vec<Vec<BabyBear>> {
        vec![vec![BabyBear::new(value)]; 4]
    }

    #[test]
    fn canonical_statement_roundtrip_is_exact_and_fail_closed() {
        let statement = test_statement(7);
        let bytes = statement.to_canonical_bytes();
        assert_eq!(
            DescriptorStatementV1::from_canonical_bytes(&bytes).unwrap(),
            statement
        );

        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(DescriptorStatementV1::from_canonical_bytes(&trailing).is_err());

        let whitespace_program = TEST_DESCRIPTOR.replacen('{', "{ ", 1).into_bytes();
        let whitespace = DescriptorStatementV1::try_new(whitespace_program, vec![7]).unwrap();
        assert_ne!(statement.statement_id(), whitespace.statement_id());

        let mut suffixed_program = TEST_DESCRIPTOR.as_bytes().to_vec();
        suffixed_program.extend_from_slice(b" attacker-controlled-suffix");
        assert!(DescriptorStatementV1::try_new(suffixed_program, vec![7]).is_err());

        assert!(DescriptorStatementV1::try_new(TEST_DESCRIPTOR.as_bytes(), vec![]).is_err());
        assert!(
            DescriptorStatementV1::try_new(TEST_DESCRIPTOR.as_bytes(), vec![BABYBEAR_P]).is_err()
        );
    }

    // A second marker over the SAME real cryptographic backend is enough to
    // compile and exercise the generic two-backend scaffold now.  It is not an
    // independent implementation and is deliberately test-only; the first
    // Dregg-native backend replaces this marker in its differential suite.
    struct ReferenceApiTwin;

    impl DescriptorProofVerifier for ReferenceApiTwin {
        type Proof = <Plonky3HidingFriReference as DescriptorProofVerifier>::Proof;
        const BACKEND_ID: &'static str = "test-only-reference-api-twin";

        fn verify(statement: &DescriptorStatementV1, proof: &Self::Proof) -> Result<(), String> {
            Plonky3HidingFriReference::verify(statement, proof)
        }
    }

    impl DescriptorProofProver for ReferenceApiTwin {
        type Witness<'a> = Plonky3HidingFriWitness<'a>;

        fn prove<'a>(
            statement: &DescriptorStatementV1,
            witness: Self::Witness<'a>,
        ) -> Result<Self::Proof, String> {
            Plonky3HidingFriReference::prove(statement, witness)
        }
    }

    struct RefusingVerifierTwin;

    impl DescriptorProofVerifier for RefusingVerifierTwin {
        type Proof = <Plonky3HidingFriReference as DescriptorProofVerifier>::Proof;
        const BACKEND_ID: &'static str = "test-only-refusing-verifier-twin";

        fn verify(_statement: &DescriptorStatementV1, _proof: &Self::Proof) -> Result<(), String> {
            Err("intentional candidate refusal".to_string())
        }
    }

    impl DescriptorProofProver for RefusingVerifierTwin {
        type Witness<'a> = Plonky3HidingFriWitness<'a>;

        fn prove<'a>(
            statement: &DescriptorStatementV1,
            witness: Self::Witness<'a>,
        ) -> Result<Self::Proof, String> {
            Plonky3HidingFriReference::prove(statement, witness)
        }
    }

    #[test]
    fn hidingfri_reference_runs_through_exact_differential_scaffold() {
        let rows = rows(7);
        let mem = MemBoundaryWitness::default();
        let umem = UMemBoundaryWitness::default();
        let witness = Plonky3HidingFriWitness {
            base_trace: &rows,
            mem_boundary: &mem,
            map_heaps: &[],
            umem_boundary: &umem,
        };
        let statement = test_statement(7);
        let DifferentialProofOutcome::Accepted {
            reference,
            candidate,
        } = differential_prove_and_verify::<Plonky3HidingFriReference, ReferenceApiTwin>(
            &statement, witness, witness,
        )
        .unwrap()
        else {
            panic!("honest relation must not be refused");
        };

        // Both independently blinded proofs bind the parsed relation and the
        // canonical public inputs.  Mutating only the PI vector makes both real
        // verifiers refuse.
        assert_eq!(
            differential_verify::<Plonky3HidingFriReference, ReferenceApiTwin>(
                &test_statement(8),
                &reference,
                &candidate,
            )
            .unwrap(),
            DifferentialVerifyDecision::Rejected
        );

        let encoded = postcard::to_allocvec(&reference).unwrap();
        let decoded: <Plonky3HidingFriReference as DescriptorProofVerifier>::Proof =
            postcard::from_bytes(&encoded).unwrap();
        Plonky3HidingFriReference::verify(&statement, &decoded).unwrap();
    }

    #[test]
    fn differential_scaffold_reports_agreed_witness_refusal() {
        let rows = rows(8);
        let mem = MemBoundaryWitness::default();
        let umem = UMemBoundaryWitness::default();
        let witness = Plonky3HidingFriWitness {
            base_trace: &rows,
            mem_boundary: &mem,
            map_heaps: &[],
            umem_boundary: &umem,
        };
        assert!(matches!(
            differential_prove_and_verify::<Plonky3HidingFriReference, ReferenceApiTwin>(
                &test_statement(7),
                witness,
                witness,
            )
            .unwrap(),
            DifferentialProofOutcome::Rejected { .. }
        ));
    }

    #[test]
    fn differential_scaffold_refuses_backend_acceptance_drift() {
        let rows = rows(7);
        let mem = MemBoundaryWitness::default();
        let umem = UMemBoundaryWitness::default();
        let witness = Plonky3HidingFriWitness {
            base_trace: &rows,
            mem_boundary: &mem,
            map_heaps: &[],
            umem_boundary: &umem,
        };
        let error =
            differential_prove_and_verify::<Plonky3HidingFriReference, RefusingVerifierTwin>(
                &test_statement(7),
                witness,
                witness,
            )
            .err()
            .expect("accept/refuse drift must be a differential failure");
        assert!(error.contains("reference"));
        assert!(error.contains("candidate"));
        assert!(error.contains("intentional candidate refusal"));
    }
}

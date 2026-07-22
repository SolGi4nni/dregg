//! Proof-system seam for DescriptorIR-v2 semantic relations.
//!
//! [`DescriptorStatement`] contains the parsed [`EffectVmDescriptor2`] relation
//! plus canonical BabyBear public inputs.  It deliberately does not retain or
//! hash the JSON text used to construct that relation: Lean-emitted JSON is an
//! internal build/provenance transport, not protocol identity.  A network proof
//! envelope should select an audited relation through a code-owned registry and
//! bind that registry identifier, the backend/config identifier, and the public
//! inputs.
//!
//! The witness is deliberately *not* part of the common interface.  The
//! reference Plonky3 backend consumes a complete local IR-v2 trace through
//! [`Plonky3HidingFriWitness`].  A future collaborative backend can instead use
//! party-local shares as its associated witness type without first assembling a
//! no-viewer witness in one process.
//!
//! This is a compile-time seam, not a proof-wire registry.  The current STARK
//! binds the parsed relation and public inputs.  Production proof envelopes
//! still need code-owned relation resolution and explicit backend/verifier-
//! parameter dispatch before multiple proof systems can coexist on a network
//! boundary.

use serde::{Serialize, de::DeserializeOwned};

use crate::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::heap_root::HeapLeaf;
use crate::stark_zk::{DreggZkStarkConfig, create_zk_config};

/// Backend-neutral semantic relation and public inputs.
///
/// This type begins *after* DescriptorIR parsing and registry/provenance
/// resolution.  It is intentionally not a wire encoding or content-addressed
/// protocol object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DescriptorStatement {
    descriptor: EffectVmDescriptor2,
    public_inputs: Vec<u32>,
}

impl DescriptorStatement {
    /// Construct and validate a parsed DescriptorIR-v2 semantic statement.
    pub fn try_new(
        descriptor: EffectVmDescriptor2,
        public_inputs: Vec<u32>,
    ) -> Result<Self, String> {
        let statement = Self {
            descriptor,
            public_inputs,
        };
        statement.validate()?;
        Ok(statement)
    }

    /// Internal Rust/Lean bridge from emitted JSON into the semantic statement.
    ///
    /// The input text is discarded after parsing.  This helper does not
    /// authenticate Lean emission and must not be used as a protocol identity;
    /// production callers resolve approved relations through their registry.
    pub fn try_from_json(json: &str, public_inputs: Vec<u32>) -> Result<Self, String> {
        Self::try_new(parse_vm_descriptor2(json)?, public_inputs)
    }

    /// Parsed semantic relation consumed identically by every proof backend.
    pub fn descriptor(&self) -> &EffectVmDescriptor2 {
        &self.descriptor
    }

    /// Canonical BabyBear public inputs (`0 <= pi < BABYBEAR_P`).
    pub fn public_inputs(&self) -> &[u32] {
        &self.public_inputs
    }

    /// Convert the already-canonical public input words to the deployed field wrapper.
    pub fn public_input_felts(&self) -> Vec<BabyBear> {
        self.public_inputs
            .iter()
            .copied()
            .map(BabyBear::new)
            .collect()
    }

    /// Validate PI arity and unique field encodings.
    pub fn validate(&self) -> Result<(), String> {
        if self.public_inputs.len() != self.descriptor.public_input_count {
            return Err(format!(
                "DescriptorIR statement carries {} public inputs but `{}` declares {}",
                self.public_inputs.len(),
                self.descriptor.name,
                self.descriptor.public_input_count
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
}

/// Verify one proof against the backend-neutral DescriptorIR statement.
pub trait DescriptorProofVerifier: Send + Sync + 'static {
    /// Backend-native proof representation.
    type Proof: Serialize + DeserializeOwned;

    /// Stable implementation/protocol identity.  This must move whenever proof
    /// bytes or verifier semantics move; a future proof envelope will bind it.
    const BACKEND_ID: &'static str;

    /// Verify `proof` against the relation and public inputs selected by `statement`.
    fn verify(statement: &DescriptorStatement, proof: &Self::Proof) -> Result<(), String>;
}

/// Prove the semantic relation, with a backend-specific witness custody shape.
pub trait DescriptorProofProver: DescriptorProofVerifier {
    /// The prover input for one call.  It is deliberately backend-specific: a
    /// collaborative prover can use party-local shares rather than a full trace.
    type Witness<'a>
    where
        Self: 'a;

    /// Produce a proof for the semantic relation and public inputs in `statement`.
    fn prove<'a>(
        statement: &DescriptorStatement,
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

    fn verify(statement: &DescriptorStatement, proof: &Self::Proof) -> Result<(), String> {
        statement.validate()?;
        verify_vm_descriptor2_with_config(
            statement.descriptor(),
            proof,
            &statement.public_input_felts(),
            &create_zk_config(),
        )
    }
}

impl DescriptorProofProver for Plonky3HidingFriReference {
    type Witness<'a> = Plonky3HidingFriWitness<'a>;

    fn prove<'a>(
        statement: &DescriptorStatement,
        witness: Self::Witness<'a>,
    ) -> Result<Self::Proof, String> {
        statement.validate()?;
        prove_vm_descriptor2_for_config(
            statement.descriptor(),
            witness.base_trace,
            &statement.public_input_felts(),
            witness.mem_boundary,
            witness.map_heaps,
            witness.umem_boundary,
            &create_zk_config(),
        )
    }
}

/// Outcome of a two-backend proving differential over one semantic statement.
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
    statement: &DescriptorStatement,
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

/// Prove and then verify the same semantic statement with two real backends.
///
/// The two witness values may have different types.  That is load-bearing for a
/// future no-viewer backend whose input is a set of party-local shares rather
/// than the reference backend's assembled trace.
pub fn differential_prove_and_verify<'reference, 'candidate, Reference, Candidate>(
    statement: &DescriptorStatement,
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

    fn test_statement(value: u32) -> DescriptorStatement {
        DescriptorStatement::try_from_json(TEST_DESCRIPTOR, vec![value]).unwrap()
    }

    fn rows(value: u32) -> Vec<Vec<BabyBear>> {
        vec![vec![BabyBear::new(value)]; 4]
    }

    #[test]
    fn semantic_statement_validates_public_input_contract() {
        let descriptor = parse_vm_descriptor2(TEST_DESCRIPTOR).unwrap();
        let statement = DescriptorStatement::try_new(descriptor.clone(), vec![7]).unwrap();
        assert_eq!(statement.descriptor(), &descriptor);
        assert_eq!(statement.public_inputs(), &[7]);

        assert!(DescriptorStatement::try_new(descriptor.clone(), vec![]).is_err());
        assert!(DescriptorStatement::try_new(descriptor, vec![BABYBEAR_P]).is_err());
    }

    // A second marker over the SAME real cryptographic backend is enough to
    // compile and exercise the generic two-backend scaffold now.  It is not an
    // independent implementation and is deliberately test-only; the first
    // Dregg-native backend replaces this marker in its differential suite.
    struct ReferenceApiTwin;

    impl DescriptorProofVerifier for ReferenceApiTwin {
        type Proof = <Plonky3HidingFriReference as DescriptorProofVerifier>::Proof;
        const BACKEND_ID: &'static str = "test-only-reference-api-twin";

        fn verify(statement: &DescriptorStatement, proof: &Self::Proof) -> Result<(), String> {
            Plonky3HidingFriReference::verify(statement, proof)
        }
    }

    impl DescriptorProofProver for ReferenceApiTwin {
        type Witness<'a> = Plonky3HidingFriWitness<'a>;

        fn prove<'a>(
            statement: &DescriptorStatement,
            witness: Self::Witness<'a>,
        ) -> Result<Self::Proof, String> {
            Plonky3HidingFriReference::prove(statement, witness)
        }
    }

    struct RefusingVerifierTwin;

    impl DescriptorProofVerifier for RefusingVerifierTwin {
        type Proof = <Plonky3HidingFriReference as DescriptorProofVerifier>::Proof;
        const BACKEND_ID: &'static str = "test-only-refusing-verifier-twin";

        fn verify(_statement: &DescriptorStatement, _proof: &Self::Proof) -> Result<(), String> {
            Err("intentional candidate refusal".to_string())
        }
    }

    impl DescriptorProofProver for RefusingVerifierTwin {
        type Witness<'a> = Plonky3HidingFriWitness<'a>;

        fn prove<'a>(
            statement: &DescriptorStatement,
            witness: Self::Witness<'a>,
        ) -> Result<Self::Proof, String> {
            Plonky3HidingFriReference::prove(statement, witness)
        }
    }

    #[test]
    fn hidingfri_reference_runs_through_semantic_differential_scaffold() {
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

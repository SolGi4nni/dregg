//! The genuine `proof_bind` engine for the `custom` effect — a REAL recursive
//! sub-proof verification, not a bounds check.
//!
//! ## What this closes
//!
//! The deployed `customVmDescriptor2R24` carries one `DescriptorIR2.ProofBind`
//! op binding the Custom row's `custom_proof_commitment` column (var 72) and
//! `custom_program_vk_hash` column (var 68). At the descriptor-IR level the op
//! only *declares* the binding; the in-AIR check is a bounds check
//! (`descriptor_ir2.rs`, `VmConstraint2::ProofBind`), and the EffectVM AIR's
//! Custom leg (`effect_vm/air.rs`) explicitly does NOT verify the external
//! proof — it only records its hash commitment and warns:
//!
//! > "Verifiers MUST independently verify the external proof against the
//! >  committed program VK hash. Without this check, a malicious prover can
//! >  claim any custom_proof_commitment without having a valid external proof."
//!
//! That independent verification is what this module makes a deployed,
//! SDK-reachable, light-client-runnable check. It is the REAL engine the
//! descriptor-semantic toy (`descriptor_ir2.rs::ToyEngine`) modeled: the proof
//! carrier is a genuine [`crate::dsl::circuit::CellProgram`] STARK, the verifier
//! accepts exactly the proofs that the program's AIR accepts, and a verifying
//! proof's exposed `(commit, vk)` are the canonical PI-commitment and the
//! program's VK hash.
//!
//! ## The soundness property
//!
//! [`verify_proof_bind`] turns the descriptor's `proof_bind` gate from "the
//! columns are in range" into "the bound proof VERIFIED, its public-input
//! commitment EQUALS the bound `commit` column, and its program VK EQUALS the
//! bound `vk` column." A custom effect carrying a FORGED sub-proof — a
//! non-verifying STARK, a commitment that does not match the proof's public
//! inputs, or a VK that does not match the program — is REJECTED.
//!
//! ## How the sub-proof binds (the two columns)
//!
//! * `custom_program_vk_hash` (8 felts, EffectVM PI `CUSTOM_PROOFS_BASE + i*12 +
//!   0..8`; column 68 in the rotated descriptor) — the program identity, the
//!   32-byte [`CellProgram::vk_hash`] mapped through
//!   [`crate::effect_vm::bytes32_to_8_limbs`]. The verifier looks the
//!   program up by this hash; an unknown program fails closed.
//! * `custom_proof_commitment` (4 felts, EffectVM PI `... + 8..12`; column 72)
//!   — [`custom_proof_pi_commitment`] of the sub-proof's public inputs. The
//!   verifier recomputes it from the verified sub-proof's PI and requires
//!   equality; a swapped or fabricated commitment fails closed.
//!
//! Both are bound into the turn hash (`turn::Turn::hash`) via
//! `custom_program_proofs`, so the sub-proof bytes + PI cannot be swapped after
//! the fact without changing the turn identity.

#![cfg(feature = "prover")]

use crate::binding::WideHash;
use crate::dsl::circuit::{CellProgram, ProgramRegistry};
use crate::effect_vm::bytes32_to_8_limbs;
use crate::field::BabyBear;

/// Domain separator for the custom sub-proof's public-input commitment. Distinct
/// from every other `WideHash` domain so a commitment minted here cannot be
/// confused with (or replayed as) any other binding hash.
pub const CUSTOM_PROOF_PI_DOMAIN: &str = "dregg-custom-proof-bind-pi-v1";

/// The EffectVM `custom_proof_commitment` column is a DEPLOYED 4-felt descriptor
/// column (`customVmDescriptor2R24`, vars 68..72). It is its OWN binding surface,
/// distinct from the action/presentation binding, and is NOT widened to 8 here:
/// doing so is VK-affecting in the effect-VM AIR (re-emit the descriptor, shift
/// the column layout, re-pin the FP, touch the Lean descriptor). At 4 felts it
/// carries ~62-bit birthday collision resistance — the SAME class of exposure the
/// action binding had, and a forged sub-proof's public inputs are adversary-
/// chosen, so it IS collision-relevant. This 4-felt column is the precise
/// remaining surface to rotate in a dedicated effect-VM descriptor pass.
pub type ProofBindCommitment = [BabyBear; 4];

/// The canonical commitment to a custom sub-proof's public inputs — the value
/// that lands in the Custom row's `custom_proof_commitment` column.
///
/// Prover and verifier MUST agree on this derivation: the prover writes it into
/// the EffectVM Custom row + PI, and [`verify_proof_bind`] recomputes it from the
/// verified sub-proof's public inputs and requires equality.
///
/// Derived as the first 4 felts of the canonical [`WideHash::from_poseidon2`]
/// squeeze under [`CUSTOM_PROOF_PI_DOMAIN`]. Because the first squeeze block of
/// `from_poseidon2` is independent of the (newer) second block, these 4 felts are
/// byte-identical to the pre-8-felt-`WideHash` value — the deployed descriptor FP
/// is unchanged. See [`ProofBindCommitment`] for why this stays at 4 felts.
pub fn custom_proof_pi_commitment(public_inputs: &[BabyBear]) -> ProofBindCommitment {
    let wide = WideHash::from_poseidon2(CUSTOM_PROOF_PI_DOMAIN, public_inputs);
    let felts = wide.to_felts();
    [felts[0], felts[1], felts[2], felts[3]]
}

/// A custom effect's external program proof, fully witnessed: the program it
/// runs under (its descriptor IS the VK), the verifying STARK, and the public
/// inputs the proof attests.
///
/// This is the in-memory form the prover produces and the verifier consumes.
/// On the wire it is carried as `turn::CustomProgramProof { proof_bytes,
/// public_inputs }` plus the program (resolved from the host
/// [`ProgramRegistry`] by the bound VK hash) — exactly the
/// `verify_transition` contract.
#[derive(Clone, Debug)]
pub struct BoundCustomProof {
    /// The program (its descriptor is the VK; `vk_hash` is its identity).
    pub program: CellProgram,
    /// The serialized STARK proof bytes for one transition under `program`.
    pub proof_bytes: Vec<u8>,
    /// The public inputs the sub-proof attests.
    pub public_inputs: Vec<BabyBear>,
}

impl BoundCustomProof {
    /// The 8-felt `custom_program_vk_hash` column value this proof binds.
    pub fn vk_hash_felts(&self) -> [BabyBear; 8] {
        bytes32_to_8_limbs(&self.program.vk_hash)
    }

    /// The 4-felt `custom_proof_commitment` column value this proof binds.
    pub fn proof_commitment(&self) -> ProofBindCommitment {
        custom_proof_pi_commitment(&self.public_inputs)
    }
}

/// Mint a GENUINE custom sub-proof: prove one transition under `program` from
/// `witness_values`, then bundle the verifying STARK + its public inputs into a
/// [`BoundCustomProof`].
///
/// This is the prove side of the deployed `proof_bind` route: the returned
/// proof's `vk_hash_felts()` / `proof_commitment()` are the values the EffectVM
/// Custom row must carry, and [`verify_proof_bind`] will re-verify the STARK and
/// re-derive the commitment. It mints a real proof (via
/// [`CellProgram::prove_transition`]), not a placeholder.
pub fn prove_custom_program(
    program: &CellProgram,
    witness_values: &std::collections::HashMap<String, Vec<BabyBear>>,
    num_rows: usize,
    public_inputs: &[BabyBear],
) -> Result<BoundCustomProof, ProofBindError> {
    let proof_bytes = program
        .prove_transition(witness_values, num_rows, public_inputs)
        .map_err(|e| ProofBindError::SubProofProveFailed(e.to_string()))?;
    Ok(BoundCustomProof {
        program: program.clone(),
        proof_bytes,
        public_inputs: public_inputs.to_vec(),
    })
}

/// The claimed binding read off the EffectVM Custom row / PI: the columns the
/// descriptor's `proof_bind` op pins. The verifier checks the sub-proof against
/// exactly THESE claimed values, so a row that lies about either column is
/// rejected even when the sub-proof itself verifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClaimedProofBind {
    /// The Custom row's `custom_program_vk_hash` column (8 felts, var 68).
    pub vk_hash: [BabyBear; 8],
    /// The Custom row's `custom_proof_commitment` column (4 felts, var 72).
    pub commitment: ProofBindCommitment,
}

/// Why a `proof_bind` verification failed — every variant is a forged or
/// malformed binding the genuine engine REJECTS (where the old bounds-check
/// would have accepted).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofBindError {
    /// The bound VK hash names no program in the host registry — fail closed.
    UnknownProgram { vk_hash: [BabyBear; 8] },
    /// The resolved program's VK does not match the Custom row's bound VK column.
    VkMismatch {
        claimed: [BabyBear; 8],
        program: [BabyBear; 8],
    },
    /// The sub-proof's public-input commitment does not match the bound
    /// `custom_proof_commitment` column.
    CommitmentMismatch { claimed: ProofBindCommitment, recomputed: ProofBindCommitment },
    /// The external STARK sub-proof did not verify under the program's AIR.
    SubProofVerifyFailed(String),
    /// The sub-proof could not be proven (prove side only).
    SubProofProveFailed(String),
}

impl std::fmt::Display for ProofBindError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofBindError::UnknownProgram { .. } => {
                write!(f, "proof_bind: bound VK names no registered program (fail closed)")
            }
            ProofBindError::VkMismatch { .. } => {
                write!(f, "proof_bind: program VK does not match the bound vk column")
            }
            ProofBindError::CommitmentMismatch { .. } => write!(
                f,
                "proof_bind: sub-proof PI commitment does not match the bound commit column"
            ),
            ProofBindError::SubProofVerifyFailed(e) => {
                write!(f, "proof_bind: external sub-proof failed verification: {e}")
            }
            ProofBindError::SubProofProveFailed(e) => {
                write!(f, "proof_bind: external sub-proof could not be proven: {e}")
            }
        }
    }
}

impl std::error::Error for ProofBindError {}

/// **THE genuine `proof_bind` gate.** Verify that a custom effect's bound
/// sub-proof genuinely VERIFIES and that its exposed `(commit, vk)` equal the
/// values the EffectVM Custom row's `proof_bind` op pins.
///
/// This is the deployed, light-client-runnable engine that makes the
/// descriptor's `proof_bind` MEAN "the bound proof verified," replacing the
/// bounds-check-only handling. The four checks, all fail-closed:
///
/// 1. **VK resolves** — the claimed `vk_hash` names a program in `registry`.
///    An unknown program is rejected (no oracle to verify against).
/// 2. **VK binds** — the resolved program's own `vk_hash` (8-felt form) equals
///    the claimed `vk_hash` column. (A registry whose key disagrees with the
///    program's self-computed VK is rejected — defends against a tampered
///    registry entry.)
/// 3. **The STARK verifies** — the external sub-proof verifies under the
///    program's AIR for the given `public_inputs`. A non-verifying proof is
///    rejected. THIS is the recursion the bounds check skipped.
/// 4. **The commitment binds** — the canonical commitment of the verified
///    sub-proof's public inputs equals the claimed `commitment` column. A
///    swapped/fabricated commitment is rejected.
///
/// On success the binding is genuine: SOME proof that verifies under the named
/// program exposes exactly the row's `(commit, vk)`. A forged sub-proof fails
/// at step 3; a mismatched bind fails at step 2 or 4.
pub fn verify_proof_bind(
    registry: &ProgramRegistry,
    proof_bytes: &[u8],
    public_inputs: &[BabyBear],
    claimed: &ClaimedProofBind,
) -> Result<(), ProofBindError> {
    // (1) Resolve the program by the bound VK. The 8-felt PI form is a lossy
    //     projection of the 32-byte key, so resolve over the full registry and
    //     confirm the projection matches in step (2).
    let program = registry
        .iter()
        .map(|(_k, p)| p)
        .find(|p| bytes32_to_8_limbs(&p.vk_hash) == claimed.vk_hash)
        .ok_or(ProofBindError::UnknownProgram {
            vk_hash: claimed.vk_hash,
        })?;

    // (2) The program's self-computed VK must equal the claimed column. (The
    //     `find` above already pins the projection, but recompute from the
    //     descriptor so a registry entry whose stored `vk_hash` disagrees with
    //     its descriptor is rejected — the program cannot lie about its own VK.)
    let program_vk = bytes32_to_8_limbs(&CellProgram::compute_vk_hash(&program.descriptor));
    if program_vk != claimed.vk_hash {
        return Err(ProofBindError::VkMismatch {
            claimed: claimed.vk_hash,
            program: program_vk,
        });
    }

    // (3) THE RECURSION: verify the external STARK sub-proof under the program's
    //     AIR. A forged / non-verifying proof is rejected here.
    program
        .verify_transition(public_inputs, proof_bytes)
        .map_err(|e| ProofBindError::SubProofVerifyFailed(e.to_string()))?;

    // (4) The verified sub-proof's PI commitment must equal the bound column.
    let recomputed = custom_proof_pi_commitment(public_inputs);
    if recomputed != claimed.commitment {
        return Err(ProofBindError::CommitmentMismatch {
            claimed: claimed.commitment,
            recomputed,
        });
    }

    Ok(())
}

/// Convenience: verify a [`BoundCustomProof`] against the binding it claims to
/// expose (its own `vk_hash_felts()` / `proof_commitment()`), through the same
/// engine a light client runs. The honest round-trip
/// (`prove_custom_program` → this) is the positive pole of the soundness test.
pub fn verify_bound_custom_proof(
    registry: &ProgramRegistry,
    bound: &BoundCustomProof,
) -> Result<(), ProofBindError> {
    let claimed = ClaimedProofBind {
        vk_hash: bound.vk_hash_felts(),
        commitment: bound.proof_commitment(),
    };
    verify_proof_bind(registry, &bound.proof_bytes, &bound.public_inputs, &claimed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dsl::circuit::{
        CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
    };
    use std::collections::HashMap;

    /// A minimal but REAL custom program: one boolean column + one conservation
    /// polynomial (the sovereign-transfer shape). Its STARK is genuine; a proof
    /// that fails the AIR does not verify.
    fn demo_program() -> CellProgram {
        let p_minus_1 = BabyBear::new(crate::field::BABYBEAR_P - 1);
        let descriptor = CircuitDescriptor {
            name: "dregg-custom-demo-v1".to_string(),
            trace_width: 4,
            max_degree: 2,
            columns: vec![
                ColumnDef { name: "old".into(), index: 0, kind: ColumnKind::Value },
                ColumnDef { name: "amt".into(), index: 1, kind: ColumnKind::Value },
                ColumnDef { name: "new".into(), index: 2, kind: ColumnKind::Value },
                ColumnDef { name: "dir".into(), index: 3, kind: ColumnKind::Binary },
            ],
            constraints: vec![
                ConstraintExpr::Binary { col: 3 },
                // new - old - amt + 2*dir*amt == 0
                ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm { coeff: BabyBear::ONE, col_indices: vec![2] },
                        PolyTerm { coeff: p_minus_1, col_indices: vec![0] },
                        PolyTerm { coeff: p_minus_1, col_indices: vec![1] },
                        PolyTerm { coeff: BabyBear::new(2), col_indices: vec![3, 1] },
                    ],
                },
            ],
            boundaries: vec![],
            public_input_count: 2,
            lookup_tables: vec![],
        };
        CellProgram::new(descriptor, 1)
    }

    /// Witness for a credit (dir=0): new = old + amt.
    fn honest_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
        let rows = 4;
        let mut w = HashMap::new();
        // old=10, amt=5, new=15, dir=0 on every row (a constant satisfying trace).
        w.insert("old".into(), vec![BabyBear::new(10); rows]);
        w.insert("amt".into(), vec![BabyBear::new(5); rows]);
        w.insert("new".into(), vec![BabyBear::new(15); rows]);
        w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
        (w, rows)
    }

    fn registry_with(program: CellProgram) -> ProgramRegistry {
        let mut r = ProgramRegistry::new();
        r.deploy(program).expect("demo program deploys");
        r
    }

    /// THE POSITIVE POLE: an honest custom effect with a VALID external
    /// sub-proof proves and light-client-verifies through the genuine engine.
    #[test]
    fn honest_custom_proof_bind_verifies() {
        let program = demo_program();
        let registry = registry_with(program.clone());
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];

        let bound = prove_custom_program(&program, &w, rows, &pis)
            .expect("honest sub-proof proves");
        verify_bound_custom_proof(&registry, &bound)
            .expect("the honest bound proof must light-client-verify");
    }

    /// THE NEGATIVE POLE #1 (forged sub-proof bytes): tampered proof bytes do
    /// NOT verify — the genuine engine rejects where the bounds check accepted.
    #[test]
    fn forged_sub_proof_bytes_rejected() {
        let program = demo_program();
        let registry = registry_with(program.clone());
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];
        let mut bound = prove_custom_program(&program, &w, rows, &pis)
            .expect("honest sub-proof proves");

        // Corrupt the proof bytes (a forged sub-proof).
        for b in bound.proof_bytes.iter_mut().take(64) {
            *b ^= 0xFF;
        }
        let err = verify_bound_custom_proof(&registry, &bound)
            .expect_err("a forged sub-proof MUST be rejected");
        assert!(
            matches!(err, ProofBindError::SubProofVerifyFailed(_)),
            "forged proof bytes must fail at the recursion step, got {err:?}"
        );
    }

    /// THE NEGATIVE POLE #2 (mismatched commitment): the bound
    /// `custom_proof_commitment` does NOT match the sub-proof's public inputs —
    /// the swapped commitment is rejected even though the STARK itself verifies.
    #[test]
    fn mismatched_commitment_rejected() {
        let program = demo_program();
        let registry = registry_with(program.clone());
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];
        let bound = prove_custom_program(&program, &w, rows, &pis)
            .expect("honest sub-proof proves");

        let claimed = ClaimedProofBind {
            vk_hash: bound.vk_hash_felts(),
            // A commitment for DIFFERENT public inputs — what a forger would supply.
            commitment: custom_proof_pi_commitment(&[BabyBear::new(99), BabyBear::new(99)]),
        };
        let err = verify_proof_bind(&registry, &bound.proof_bytes, &bound.public_inputs, &claimed)
            .expect_err("a mismatched commitment MUST be rejected");
        assert!(
            matches!(err, ProofBindError::CommitmentMismatch { .. }),
            "swapped commitment must fail the commit-binding step, got {err:?}"
        );
    }

    /// THE NEGATIVE POLE #3 (unknown / mismatched VK): a bound VK that names no
    /// registered program fails closed.
    #[test]
    fn unknown_vk_rejected() {
        let program = demo_program();
        let registry = registry_with(program.clone());
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];
        let bound = prove_custom_program(&program, &w, rows, &pis)
            .expect("honest sub-proof proves");

        let claimed = ClaimedProofBind {
            vk_hash: [BabyBear::new(0xDEAD); 8], // names no program
            commitment: bound.proof_commitment(),
        };
        let err = verify_proof_bind(&registry, &bound.proof_bytes, &bound.public_inputs, &claimed)
            .expect_err("an unknown VK MUST be rejected");
        assert!(
            matches!(err, ProofBindError::UnknownProgram { .. }),
            "unknown VK must fail closed, got {err:?}"
        );
    }

    /// The PI commitment is collision-sensitive: different public inputs give
    /// different commitments (so the commit column genuinely binds the PI).
    #[test]
    fn pi_commitment_is_pi_sensitive() {
        let a = custom_proof_pi_commitment(&[BabyBear::new(1), BabyBear::new(2)]);
        let b = custom_proof_pi_commitment(&[BabyBear::new(1), BabyBear::new(3)]);
        assert_ne!(a, b, "distinct PI must yield distinct commitments");
    }
}

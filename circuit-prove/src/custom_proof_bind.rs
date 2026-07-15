//! Types + the canonical PI-commitment derivation for the `custom` effect's
//! `proof_bind`. **The binding itself is NOT enforced here** — it is enforced by the
//! deployed recursion fold. This module is the host-side derivation surface that fold
//! binds.
//!
//! ## Where the binding actually lives
//!
//! The deployed `customVmDescriptor2R24` carries one `DescriptorIR2.ProofBind` op naming
//! the Custom row's `custom_proof_commitment` column (var 72) and `custom_program_vk_hash`
//! column (var 68). At the descriptor-IR level that op only *declares* the binding: the
//! in-AIR check is a bounds check (`descriptor_ir2.rs`, `VmConstraint2::ProofBind`), and
//! the EffectVM AIR's Custom leg (`effect_vm/air.rs`) does NOT verify the external proof.
//! On its own the row's claimed commitment is therefore UNBACKED.
//!
//! It is backed IN-CIRCUIT by the chain prover's custom fold arm:
//! [`crate::joint_turn_recursive::prove_custom_binding_node_segmented`], wired into
//! [`crate::ivc_turn_chain::prove_chain_core_rotated`]. That node folds two leaves — the
//! effect-vm leg as a DUAL-EXPOSE leaf (chain segment + the claimed 8-felt commitment from
//! PI 46..53) and the custom SUB-PROOF leaf re-proven from the retained
//! `CustomWitnessBundle` ([`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`],
//! whose commitment is computed in-circuit) — and `connect`s the claimed lanes to the
//! genuine ones.
//!
//! **The tooth:** a turn whose effect-vm row claims a commitment no verifying sub-proof
//! backs is UNSAT. There is no satisfying custom leaf whose exposed commitment equals the
//! claimed slots, so the aggregate does not prove — no root, and a pure light client
//! (which folds the recursion tree and never witnesses the sub-proof off-AIR) never
//! receives a verifying artifact.
//!
//! ## Provenance of this module's shape
//!
//! The off-AIR hand-STARK engine that used to live here — `prove_custom_program` /
//! `verify_bound_custom_proof` / `verify_proof_bind` — died with stark-kill (`dd038c08e`).
//! Nothing in the tree verifies a proof-bind off-AIR any more. What survives here is
//! types + [`custom_proof_pi_commitment`], the canonical derivation the fold binds against.
//!
//! ## The teeth (both polarities, and where they run)
//!
//! * `every_forged_commitment_lane_is_rejected_by_the_fold` (in-lib, `joint_turn_recursive`)
//!   — the MECHANISM tooth. Forges each of the 8 lanes INDEPENDENTLY (`k in 0..8`), which is
//!   what makes the SECOND squeeze block load-bearing: a node binding only the first 4 would
//!   accept the `k in 4..8` forgeries. It runs on a plain `cargo test -p dregg-circuit-prove`
//!   (no `#[ignore]`). **Scope:** it drives
//!   [`crate::joint_turn_recursive::prove_custom_binding_node`] — the single-claim variant —
//!   over a stand-in leg. That is the connect MECHANISM, not the deployed wiring.
//! * `circuit-prove/tests/custom_binding_deployed_tooth.rs` and
//!   `custom_binding_production_path.rs` — the DEPLOYED poles: honest-accept + forged-reject
//!   end-to-end through `prove_turn_chain_recursive` → `verify_turn_chain_recursive`.
//!   **⚠ Both are `#[ignore]`d and nothing in CI passes `--ignored`, so the deployed
//!   end-to-end poles are not exercised in automation at HEAD** (`CRATE-EXCELLENCE-PLAN.md`
//!   §4 MOVE 2 is the lane that arms them).
//!
//! So at HEAD the connect mechanism is gated in automation and the deployed wiring is not.
//!
//! ## How the sub-proof binds (the two columns)
//!
//! * `custom_program_vk_hash` (8 felts, EffectVM PI `CUSTOM_PROOFS_BASE + i*12 +
//!   0..8`; column 68 in the rotated descriptor) — the program identity, the
//!   32-byte [`CellProgram::vk_hash`] mapped through
//!   [`dregg_circuit::effect_vm::bytes32_to_8_limbs`]. A re-executing validator resolves
//!   the program by this hash through the host [`ProgramRegistry`], where an unregistered
//!   `vk_hash` does not resolve. On the deployed FOLD path there is no registry lookup:
//!   the sub-proof leaf is re-proven from the program carried on the retained
//!   `CustomWitnessBundle`.
//! * `custom_proof_commitment` (8 felts, EffectVM PI `... + 8..16`; limbs 0..4
//!   at column 72, limbs 4..8 on the member-local commit-teeth columns)
//!   — [`custom_proof_pi_commitment`] of the sub-proof's public inputs. The fold's
//!   custom leaf computes this commitment IN-CIRCUIT from the sub-proof's real PIs
//!   ([`crate::custom_leaf_adapter::incircuit_custom_pi_commitment`]) and `connect`s it,
//!   lane by lane, to the claimed column; a swapped or fabricated commitment has no
//!   satisfying partner and the aggregation is UNSAT.
//!
//! Both are bound into the turn hash (`turn::Turn::hash`) via
//! `custom_program_proofs`, so the sub-proof bytes + PI cannot be swapped after
//! the fact without changing the turn identity.

use dregg_circuit::binding::WideHash;
use dregg_circuit::dsl::circuit::{CellProgram, ProgramRegistry};
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::field::BabyBear;

/// Domain separator for the custom sub-proof's public-input commitment. Distinct
/// from every other `WideHash` domain so a commitment minted here cannot be
/// confused with (or replayed as) any other binding hash.
pub const CUSTOM_PROOF_PI_DOMAIN: &str = "dregg-custom-proof-bind-pi-v1";

/// The number of BabyBear felts in a [`ProofBindCommitment`] — the FULL 8-felt
/// `WideHash` squeeze (~124-bit birthday collision resistance, the same class as
/// the action/presentation bindings and the wide state anchors).
pub const PROOF_BIND_COMMIT_WIDTH: usize = 8;

/// **FLAG-DAY ROTATION (proof-bridge upstream blocker #2): 4 felts → 8 felts.**
///
/// The EffectVM `custom_proof_commitment` binding surface was a DEPLOYED 4-felt
/// descriptor column (`customVmDescriptor2R24`, vars 72..76) carrying only
/// ~62-bit birthday collision resistance — collision-relevant, because a forged
/// sub-proof's public inputs are adversary-chosen. It is now the full 8-felt
/// [`WideHash`] class (~124-bit birthday, matching the 128-bit FRI soundness):
/// the first 4 limbs keep their column home (cols 72..76), the second squeeze
/// block's 4 limbs ride the member-local commit-teeth columns past the wide
/// carriers, and all 8 are published as descriptor PIs the per-turn fold binds.
/// Old 4-felt custom artifacts are REFUSED at the versioned admission boundary
/// (`require_custom_commit_teeth_v2`) — never silently widened or zero-padded.
pub type ProofBindCommitment = [BabyBear; PROOF_BIND_COMMIT_WIDTH];

/// The canonical commitment to a custom sub-proof's public inputs — the value
/// that lands in the Custom row's `custom_proof_commitment` columns + PIs.
///
/// Prover and verifier MUST agree on this derivation: the prover writes it into
/// the EffectVM Custom row + PI, and the light-client fold recomputes it from the
/// verified sub-proof's public inputs and requires equality.
///
/// Derived as the FULL 8-felt canonical [`WideHash::from_poseidon2`] squeeze under
/// [`CUSTOM_PROOF_PI_DOMAIN`] — both squeeze blocks (rate-4 block, permute,
/// rate-4 block again). The first 4 felts are byte-identical to the retired
/// 4-felt commitment (the first squeeze block is independent of the second);
/// felts 4..8 are the genuine second squeeze block, NOT duplication or padding.
pub fn custom_proof_pi_commitment(public_inputs: &[BabyBear]) -> ProofBindCommitment {
    WideHash::from_poseidon2(CUSTOM_PROOF_PI_DOMAIN, public_inputs).to_felts()
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
    /// **PROVER-SIDE-ONLY re-provable trace witness** (the named trace-column witness the
    /// `CellProgram` proves over). Retained so the deployed chain prover can RE-PROVE the sub-proof
    /// as a recursion-foldable leaf ([`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`])
    /// and FOLD it under the custom-binding node — making the commitment binding witnessable by a
    /// PURE LIGHT CLIENT, not just a re-executing validator. `None` for a `BoundCustomProof`
    /// reconstructed from the on-wire [`dregg_turn::CustomProgramProof`] (the wire keeps only the
    /// finished bytes + PIs; the re-provable witness is NEVER serialized). A `None`-witness bound
    /// proof carries the off-AIR verify but cannot be folded — exactly the re-exec-only rung.
    pub witness_values: Option<std::collections::HashMap<String, Vec<BabyBear>>>,
    /// The number of trace rows for [`Self::witness_values`] (prover-side only; `None` off the wire).
    pub num_rows: Option<usize>,
}

impl BoundCustomProof {
    /// The 8-felt `custom_program_vk_hash` column value this proof binds.
    pub fn vk_hash_felts(&self) -> [BabyBear; 8] {
        bytes32_to_8_limbs(&self.program.vk_hash)
    }

    /// The 8-felt `custom_proof_commitment` value this proof binds (flag-day
    /// rotation: was 4 felts / ~62-bit birthday; now the full `WideHash` class).
    pub fn proof_commitment(&self) -> ProofBindCommitment {
        custom_proof_pi_commitment(&self.public_inputs)
    }
}

/// The claimed binding read off the EffectVM Custom row / PI: the columns the
/// descriptor's `proof_bind` op names. These are the CLAIMED values — carrying them
/// checks nothing on its own. The deployed fold
/// ([`crate::joint_turn_recursive::prove_custom_binding_node_segmented`]) `connect`s the
/// claimed `commitment` lanes to the sub-proof leaf's in-circuit-computed commitment, so a
/// row that lies about the commitment leaves the aggregation UNSAT.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClaimedProofBind {
    /// The Custom row's `custom_program_vk_hash` column (8 felts, var 68).
    pub vk_hash: [BabyBear; 8],
    /// The Custom row's `custom_proof_commitment` (8 felts: limbs 0..4 at var 72,
    /// limbs 4..8 on the commit-teeth columns).
    pub commitment: ProofBindCommitment,
}

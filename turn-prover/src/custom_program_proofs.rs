//! Threading GENUINE custom sub-proofs onto a [`Turn`] — the wire projection of
//! `dregg_circuit_prove::custom_proof_bind::BoundCustomProof`.
//!
//! The `Turn::custom_program_proofs` FIELD and the [`CustomProgramProof`] wire
//! type stay in core `dregg-turn` (a re-executing validator must read them with
//! no prove crate linked). Only the constructor — which consumes a
//! `BoundCustomProof`, i.e. a `dregg-circuit-prove` type — lives here.
//!
//! It is an extension trait rather than a free function so the call site is
//! unchanged: `use dregg_turn_prover::TurnCustomProofsExt;` and then
//! `turn.with_custom_program_proofs(&bound)` exactly as before.

use dregg_turn::turn::CustomProgramProof;
use dregg_turn::turn::Turn;

/// Extension trait carrying the prover-side [`Turn`] constructor.
pub trait TurnCustomProofsExt {
    /// See [`TurnCustomProofsExt::with_custom_program_proofs`] on the impl below.
    #[must_use]
    fn with_custom_program_proofs(
        self,
        bound: &[dregg_circuit_prove::custom_proof_bind::BoundCustomProof],
    ) -> Self;
}

impl TurnCustomProofsExt for Turn {
    /// Thread the GENUINE custom sub-proofs into `custom_program_proofs` — the
    /// wire field a custom turn carries so a RE-EXECUTING validator can dispatch each
    /// effect's proof through its `CustomEffectRegistry` (see
    /// `executor::proof_verify::enforce_custom_effect_proofs`).
    ///
    /// This wire field is NOT what binds the commitment for a pure light client: that is
    /// the deployed recursion fold's in-circuit `connect`
    /// (`dregg_circuit_prove::joint_turn_recursive::prove_custom_binding_node_segmented`,
    /// wired in `prove_chain_core_rotated`), which needs no wire proof at all. There is no
    /// off-AIR `verify_proof_bind` engine — it died with stark-kill.
    ///
    /// Each [`dregg_circuit_prove::custom_proof_bind::BoundCustomProof`] (the genuine
    /// STARK + its public inputs) is projected
    /// to the on-wire [`CustomProgramProof`] (proof bytes + raw-u32 public inputs),
    /// in effect order. Both are bound into [`Turn::hash`] so the sub-proof bytes /
    /// PI cannot be swapped after the fact without changing the turn identity. The
    /// `BoundCustomProof`'s exposed `vk_hash_felts()` / `proof_commitment()` are the
    /// values the Custom effect's `(program_vk_hash, proof_commitment)` carry into
    /// the wide producer (cols 68 / 72 the descriptor's `proof_bind` op pins), so
    /// the wide receipt binds exactly this verifying sub-proof.
    fn with_custom_program_proofs(
        mut self,
        bound: &[dregg_circuit_prove::custom_proof_bind::BoundCustomProof],
    ) -> Self {
        let proofs: Vec<CustomProgramProof> = bound
            .iter()
            .map(|b| {
                // Pack the bound proof's 8-felt vk_hash (4 bytes/felt, LE) into
                // the 32-byte registry key the executor dispatches on.
                let felts = b.vk_hash_felts();
                let mut vk_hash = [0u8; 32];
                for (i, f) in felts.iter().enumerate() {
                    vk_hash[i * 4..i * 4 + 4].copy_from_slice(&f.as_u32().to_le_bytes());
                }
                CustomProgramProof {
                    vk_hash,
                    proof_bytes: b.proof_bytes.clone(),
                    public_inputs: b.public_inputs.iter().map(|f| f.as_u32()).collect(),
                }
            })
            .collect();
        self.custom_program_proofs = if proofs.is_empty() {
            None
        } else {
            Some(proofs)
        };
        self
    }
}

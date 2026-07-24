//! Canonical v2 custom-VK registration for the Lean-emitted, HidingFri private
//! preference decision cell.

use std::sync::Arc;

use dregg_cell::custom_effect::{CustomEffectError, CustomEffectRegistry, CustomEffectVerifier};
use dregg_cell::vk_v2::{ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2};
use dregg_circuit_prove::private_preference_cell as preference;

pub fn verifier_fingerprint() -> VerifierFingerprint {
    VerifierFingerprint::SourceHash(preference::hiding_verifier_config_fingerprint())
}

pub fn proving_system_id() -> ProvingSystemId {
    ProvingSystemId::Plonky3BabyBearFri {
        p3_rev: preference::PLONKY3_REV,
    }
}

pub fn vk_components() -> VkComponents<'static> {
    VkComponents {
        program_bytes: preference::PRIVATE_PREFERENCE_CELL_DESCRIPTOR_JSON.as_bytes(),
        air_fingerprint: preference::air_fingerprint(),
        verifier_fingerprint: verifier_fingerprint(),
        proving_system_id: proving_system_id(),
    }
}

pub fn vk_hash() -> [u8; 32] {
    canonical_vk_v2(&vk_components())
}

#[derive(Clone, Copy, Debug, Default)]
pub struct PrivatePreferenceCellCustomVerifier;

impl CustomEffectVerifier for PrivatePreferenceCellCustomVerifier {
    fn name(&self) -> &'static str {
        "private-preference-cell-n4k4-hiding-fri-v1"
    }

    fn vk_hash(&self) -> [u8; 32] {
        vk_hash()
    }

    fn verify(&self, public_inputs: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError> {
        let values = preference::decode_public_input_bytes(public_inputs).map_err(|reason| {
            CustomEffectError::Rejected {
                vk_hash: vk_hash(),
                name: "private-preference-cell-n4k4-hiding-fri-v1",
                reason,
            }
        })?;
        preference::verify_postcard(proof_bytes, &values).map_err(|reason| {
            CustomEffectError::Rejected {
                vk_hash: vk_hash(),
                name: "private-preference-cell-n4k4-hiding-fri-v1",
                reason,
            }
        })
    }
}

/// Register the exact Lean descriptor + HidingFri verifier/config under the
/// canonical v2 components.  No legacy/bytes-free registration is available.
pub fn register(registry: &mut CustomEffectRegistry) -> Result<[u8; 32], CustomEffectError> {
    let components = vk_components();
    registry.register(
        components.program_bytes.to_vec(),
        components.air_fingerprint,
        components.verifier_fingerprint,
        components.proving_system_id,
        Arc::new(PrivatePreferenceCellCustomVerifier),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit_prove::private_preference::{PrivateBallot, PrivatePreferenceWitness};

    fn witness() -> PrivatePreferenceWitness {
        let ballots = [
            PrivateBallot::try_new([3, 2, 0, 1]).unwrap(),
            PrivateBallot::try_new([2, 3, 0, 1]).unwrap(),
            PrivateBallot::try_new([0, 3, 2, 1]).unwrap(),
            PrivateBallot::try_new([1, 2, 3, 0]).unwrap(),
        ];
        PrivatePreferenceWitness::try_from_ballots_with_blinding(
            &ballots,
            core::array::from_fn(|i| 900 + i as u32),
        )
        .unwrap()
    }

    fn pi_bytes(values: &[u32]) -> Vec<u8> {
        values.iter().flat_map(|v| v.to_le_bytes()).collect()
    }

    #[test]
    fn canonical_registration_binds_hiding_config_not_only_descriptor() {
        let mut registry = CustomEffectRegistry::empty();
        let registered = register(&mut registry).expect("exact v2 components register");
        assert_eq!(registered, vk_hash());
        assert_eq!(registered, preference::canonical_vk_hash());
        assert_eq!(
            registry.canonical_bytes(&registered),
            Some(preference::PRIVATE_PREFERENCE_CELL_DESCRIPTOR_JSON.as_bytes())
        );

        let non_hiding = canonical_vk_v2(&VkComponents {
            program_bytes: preference::PRIVATE_PREFERENCE_CELL_DESCRIPTOR_JSON.as_bytes(),
            air_fingerprint: preference::air_fingerprint(),
            verifier_fingerprint: VerifierFingerprint::SourceHash(
                preference::non_hiding_verifier_config_fingerprint(),
            ),
            proving_system_id: proving_system_id(),
        });
        assert_ne!(registered, non_hiding);
    }

    #[test]
    fn real_registry_accepts_hiding_proof_and_refuses_staples() {
        let old = core::array::from_fn(|i| 100 + i as u32);
        let new = core::array::from_fn(|i| 200 + i as u32);
        let (proof, public, retained) =
            preference::prove_zk(77, &witness(), old, new).expect("hiding preference proof");
        let proof_bytes = proof.to_postcard().expect("proof bytes");
        let public_values = public.as_u32_vec();
        assert_eq!(
            retained.public_inputs[0..8],
            old.map(dregg_circuit::field::BabyBear::new)
        );
        assert_eq!(
            retained.app_root_binding.app_root_pi_offset,
            preference::WINNER_PI
        );
        assert_eq!(
            retained.app_root_binding.field_key,
            preference::DECISION_WINNER_FIELD_KEY
        );

        let mut registry = CustomEffectRegistry::empty();
        let vk = register(&mut registry).expect("register exact hiding verifier");
        registry
            .verify(&vk, &pi_bytes(&public_values), &proof_bytes)
            .expect("honest proof verifies through real registry");

        let mut wrong_old = public_values.clone();
        wrong_old[0] += 1;
        assert!(
            registry
                .verify(&vk, &pi_bytes(&wrong_old), &proof_bytes)
                .is_err()
        );

        let mut wrong_new = public_values.clone();
        wrong_new[8] += 1;
        assert!(
            registry
                .verify(&vk, &pi_bytes(&wrong_new), &proof_bytes)
                .is_err()
        );

        let mut wrong_winner = public_values.clone();
        wrong_winner[preference::WINNER_PI] ^= 1;
        assert!(
            registry
                .verify(&vk, &pi_bytes(&wrong_winner), &proof_bytes)
                .is_err()
        );

        let mut stapled_statement = public_values.clone();
        stapled_statement[16] += 1;
        assert!(
            registry
                .verify(&vk, &pi_bytes(&stapled_statement), &proof_bytes)
                .is_err()
        );

        let mut corrupt_proof = proof_bytes.clone();
        let corrupt_at = corrupt_proof.len() / 2;
        corrupt_proof[corrupt_at] ^= 1;
        assert!(
            registry
                .verify(&vk, &pi_bytes(&public_values), &corrupt_proof)
                .is_err()
        );

        let wrong_vk = non_hiding_vk_hash();
        assert!(
            registry
                .verify(&wrong_vk, &pi_bytes(&public_values), &proof_bytes)
                .is_err()
        );
    }

    fn non_hiding_vk_hash() -> [u8; 32] {
        canonical_vk_v2(&VkComponents {
            program_bytes: preference::PRIVATE_PREFERENCE_CELL_DESCRIPTOR_JSON.as_bytes(),
            air_fingerprint: preference::air_fingerprint(),
            verifier_fingerprint: VerifierFingerprint::SourceHash(
                preference::non_hiding_verifier_config_fingerprint(),
            ),
            proving_system_id: proving_system_id(),
        })
    }
}

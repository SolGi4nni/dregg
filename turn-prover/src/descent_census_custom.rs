//! Canonical-v2 custom-VK door for the Lean-authored Descent custody census.
//!
//! The verifier accepts only the hiding-FRI proof for the checked-in fixed-eight
//! AIR.  Its app-write declaration additionally requires the six published
//! custody totals to be written into Descent fields `0..6` using dregg's normal
//! `field_from_u64` byte encoding.  The recursive witness bundle separately
//! welds the proof's authenticated native-eight `fields_root` to the wide
//! EffectVM leg, so validators do not trust the host census builder.

use std::sync::Arc;

use dregg_cell::custom_effect::{
    CustomAppWriteEncoding, CustomEffectError, CustomEffectRegistry, CustomEffectVerifier,
};
use dregg_cell::vk_v2::{ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2};
use dregg_circuit::effect_vm::custom_state_binding::AppRootBinding;
use dregg_circuit_prove::descent_census as census;

const VERIFIER_NAME: &str = "descent-custody-census-fixed8-hiding-fri-v2";

pub fn verifier_fingerprint() -> VerifierFingerprint {
    VerifierFingerprint::SourceHash(census::hiding_verifier_config_fingerprint())
}

pub fn proving_system_id() -> ProvingSystemId {
    ProvingSystemId::Plonky3BabyBearFri {
        p3_rev: census::PLONKY3_REV,
    }
}

pub fn vk_components(program_bytes: &[u8]) -> VkComponents<'_> {
    VkComponents {
        program_bytes,
        air_fingerprint: census::air_fingerprint(),
        verifier_fingerprint: verifier_fingerprint(),
        proving_system_id: proving_system_id(),
    }
}

pub fn vk_hash() -> [u8; 32] {
    let program_bytes = census::canonical_descriptor_bytes();
    canonical_vk_v2(&vk_components(&program_bytes))
}

#[derive(Clone, Copy, Debug, Default)]
pub struct DescentCensusCustomVerifier;

impl CustomEffectVerifier for DescentCensusCustomVerifier {
    fn name(&self) -> &'static str {
        VERIFIER_NAME
    }

    fn vk_hash(&self) -> [u8; 32] {
        vk_hash()
    }

    fn verify(&self, public_inputs: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError> {
        let values = census::decode_public_input_bytes(public_inputs).map_err(|reason| {
            CustomEffectError::Rejected {
                vk_hash: vk_hash(),
                name: VERIFIER_NAME,
                reason,
            }
        })?;
        census::verify_postcard(proof_bytes, &values).map_err(|reason| {
            CustomEffectError::Rejected {
                vk_hash: vk_hash(),
                name: VERIFIER_NAME,
                reason,
            }
        })
    }

    fn app_write_binding(&self) -> Option<AppRootBinding> {
        Some(AppRootBinding {
            app_root_pi_offset: census::APP_WRITE_POLICY.app_root_pi_offset,
            app_root_len: census::APP_WRITE_POLICY.app_root_len,
            field_key: census::APP_WRITE_POLICY.field_key,
        })
    }

    fn app_write_encoding(&self) -> CustomAppWriteEncoding {
        match census::APP_WRITE_POLICY.encoding_tag {
            census::APP_WRITE_ENCODING_DREGG_U64_BE => CustomAppWriteEncoding::DreggU64Be,
            tag => panic!("unsupported Descent census app-write encoding tag {tag}"),
        }
    }
}

/// Install the exact Lean descriptor, AIR, hiding verifier configuration, and
/// count-write policy in a real custom-effect registry.
pub fn register(registry: &mut CustomEffectRegistry) -> Result<[u8; 32], CustomEffectError> {
    let program_bytes = census::canonical_descriptor_bytes();
    let components = vk_components(&program_bytes);
    let air_fingerprint = components.air_fingerprint;
    let verifier_fingerprint = components.verifier_fingerprint;
    let proving_system_id = components.proving_system_id;
    registry.register(
        program_bytes,
        air_fingerprint,
        verifier_fingerprint,
        proving_system_id,
        Arc::new(DescentCensusCustomVerifier),
    )
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;

    fn field_from_u64(value: u64) -> dregg_cell::FieldElement {
        dregg_cell::field_from_u64(value)
    }

    fn fields() -> BTreeMap<u64, dregg_cell::FieldElement> {
        census::RELIC_KEYS
            .into_iter()
            .zip([1, 8, 8, 9, 2, 3, 4, 9])
            .map(|(key, code)| (key, field_from_u64(code)))
            .collect()
    }

    fn pi_bytes(values: &[u32]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    #[test]
    fn canonical_registration_commits_the_hiding_verifier_and_integer_write_policy() {
        let mut registry = CustomEffectRegistry::empty();
        let registered = register(&mut registry).expect("exact Descent census verifier registers");
        assert_eq!(registered, vk_hash());
        assert_eq!(registered, census::canonical_vk_hash());
        let canonical_program = census::canonical_descriptor_bytes();
        assert_eq!(
            registry.canonical_bytes(&registered),
            Some(canonical_program.as_slice())
        );

        let verifier = registry.get(&registered).expect("registered verifier");
        assert_eq!(
            verifier.app_write_binding(),
            Some(AppRootBinding {
                app_root_pi_offset: census::APP_WRITE_POLICY.app_root_pi_offset,
                app_root_len: census::APP_WRITE_POLICY.app_root_len,
                field_key: census::APP_WRITE_POLICY.field_key,
            })
        );
        assert_eq!(
            verifier.app_write_encoding(),
            CustomAppWriteEncoding::DreggU64Be
        );
        assert_eq!(verifier.app_write_encoding().encode(7), field_from_u64(7));
    }

    #[test]
    fn real_registry_accepts_the_hiding_census_and_refuses_statement_tampering() {
        let (proof, statement, retained) =
            census::prove_zk(&fields(), [101; 8], [202; 8]).expect("hiding census proof");
        assert_eq!(statement.counts, [2, 2, 1, 1, 1, 1]);
        assert_eq!(
            retained.app_root_binding.app_root_pi_offset,
            census::PI_COUNTS
        );
        assert_eq!(
            retained.post_fields_root_binding,
            Some(
                dregg_circuit::effect_vm::custom_state_binding::PostFieldsRootBinding {
                    fields_root_pi_offset: census::PI_FIELDS_ROOT,
                }
            )
        );

        let proof_bytes = proof.to_postcard().expect("proof bytes");
        let values: Vec<u32> = statement
            .as_felts()
            .into_iter()
            .map(|felt| felt.as_u32())
            .collect();
        let mut registry = CustomEffectRegistry::empty();
        let vk = register(&mut registry).expect("register exact verifier");
        registry
            .verify(&vk, &pi_bytes(&values), &proof_bytes)
            .expect("honest census verifies through the real registry");

        for index in [0usize, 8, census::PI_FIELDS_ROOT, census::PI_COUNTS] {
            let mut tampered = values.clone();
            tampered[index] += 1;
            assert!(
                registry
                    .verify(&vk, &pi_bytes(&tampered), &proof_bytes)
                    .is_err(),
                "public input {index} must bind"
            );
        }
    }
}

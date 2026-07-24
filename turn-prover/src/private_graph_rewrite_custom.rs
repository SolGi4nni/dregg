//! Canonical-v2 custom-VK registration for the Lean-emitted HidingFri private
//! graph-rewrite **cell carrier**.
//!
//! This is the complete verifier-door weld: the registered descriptor prepends
//! the mandatory `[cell old8 || cell new8]` public-input prefix and retains an
//! app-root binding from the proved semantic `graph_new_root8` to post-state
//! fields `0..8`. Cells cite that descriptor, AIR fingerprint, hiding verifier
//! configuration, and pinned Plonky3 revision as one canonical VK. The registry
//! never accepts the same descriptor under the non-hiding verifier family.

use std::sync::Arc;

use dregg_cell::custom_effect::{CustomEffectError, CustomEffectRegistry, CustomEffectVerifier};
use dregg_cell::vk_v2::{ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2};
use dregg_circuit_prove::private_graph_rewrite_cell as graph;

const VERIFIER_NAME: &str = "private-graph-rewrite-cell-4x2-hiding-fri-v1";

pub fn verifier_fingerprint() -> VerifierFingerprint {
    VerifierFingerprint::SourceHash(graph::hiding_verifier_config_fingerprint())
}

pub fn proving_system_id() -> ProvingSystemId {
    ProvingSystemId::Plonky3BabyBearFri {
        p3_rev: graph::PLONKY3_REV,
    }
}

pub fn vk_components() -> VkComponents<'static> {
    VkComponents {
        program_bytes: graph::PRIVATE_GRAPH_REWRITE_CELL_DESCRIPTOR_JSON.as_bytes(),
        air_fingerprint: graph::air_fingerprint(),
        verifier_fingerprint: verifier_fingerprint(),
        proving_system_id: proving_system_id(),
    }
}

pub fn vk_hash() -> [u8; 32] {
    canonical_vk_v2(&vk_components())
}

#[derive(Clone, Copy, Debug, Default)]
pub struct PrivateGraphRewriteCustomVerifier;

impl CustomEffectVerifier for PrivateGraphRewriteCustomVerifier {
    fn name(&self) -> &'static str {
        VERIFIER_NAME
    }

    fn vk_hash(&self) -> [u8; 32] {
        vk_hash()
    }

    fn verify(&self, public_inputs: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError> {
        let values = graph::decode_public_input_bytes(public_inputs).map_err(|reason| {
            CustomEffectError::Rejected {
                vk_hash: vk_hash(),
                name: VERIFIER_NAME,
                reason,
            }
        })?;
        graph::verify_postcard(proof_bytes, &values).map_err(|reason| CustomEffectError::Rejected {
            vk_hash: vk_hash(),
            name: VERIFIER_NAME,
            reason,
        })
    }
}

/// Install the exact Lean descriptor and hiding verifier/config in the real
/// custom-effect registry. There is intentionally no legacy or bytes-free
/// registration path.
pub fn register(registry: &mut CustomEffectRegistry) -> Result<[u8; 32], CustomEffectError> {
    let components = vk_components();
    registry.register(
        components.program_bytes.to_vec(),
        components.air_fingerprint,
        components.verifier_fingerprint,
        components.proving_system_id,
        Arc::new(PrivateGraphRewriteCustomVerifier),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit_prove::private_graph_rewrite::{
        BoundedContext, BoundedGraph, BoundedPattern, BoundedRule, HostEdgeSlot,
        PrivateGraphRewriteWitness, RuleEdgeSlot,
    };

    fn pattern(slots: [RuleEdgeSlot; 2]) -> BoundedPattern {
        BoundedPattern { slots }
    }

    fn witness() -> PrivateGraphRewriteWitness {
        let context = BoundedContext {
            slots: [HostEdgeSlot::edge(4, 7, 8), HostEdgeSlot::edge(5, 8, 9)],
        };
        let rule0 = BoundedRule {
            lhs: pattern([RuleEdgeSlot::edge(1, 0, 1), RuleEdgeSlot::padding()]),
            rhs: pattern([RuleEdgeSlot::edge(2, 0, 1), RuleEdgeSlot::edge(3, 1, 2)]),
        };
        let rule1 = BoundedRule {
            lhs: pattern([RuleEdgeSlot::edge(6, 2, 3), RuleEdgeSlot::padding()]),
            rhs: pattern([RuleEdgeSlot::edge(7, 3, 2), RuleEdgeSlot::padding()]),
        };
        PrivateGraphRewriteWitness {
            // This is a nontrivial permutation of context ++ instantiated LHS.
            old_graph: BoundedGraph {
                slots: [
                    HostEdgeSlot::edge(1, 4, 5),
                    HostEdgeSlot::edge(4, 7, 8),
                    HostEdgeSlot::padding(),
                    HostEdgeSlot::edge(5, 8, 9),
                ],
            },
            new_graph: BoundedGraph {
                slots: [
                    HostEdgeSlot::edge(4, 7, 8),
                    HostEdgeSlot::edge(5, 8, 9),
                    HostEdgeSlot::edge(2, 4, 5),
                    HostEdgeSlot::edge(3, 5, 6),
                ],
            },
            rules: [rule0, rule1],
            sigma: [4, 5, 6, 7],
            context,
            old_blind: [101, 102, 103, 104],
            new_blind: [201, 202, 203, 204],
            rule_blinds: [[301, 302, 303, 304], [401, 402, 403, 404]],
            rule_slot: false,
        }
    }

    fn pi_bytes(values: &[u32]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn non_hiding_vk_hash() -> [u8; 32] {
        canonical_vk_v2(&VkComponents {
            program_bytes: graph::PRIVATE_GRAPH_REWRITE_CELL_DESCRIPTOR_JSON.as_bytes(),
            air_fingerprint: graph::air_fingerprint(),
            verifier_fingerprint: VerifierFingerprint::SourceHash(
                graph::non_hiding_verifier_config_fingerprint(),
            ),
            proving_system_id: proving_system_id(),
        })
    }

    #[test]
    fn canonical_registration_binds_descriptor_air_and_hiding_config() {
        let mut registry = CustomEffectRegistry::empty();
        let registered = register(&mut registry).expect("exact v2 components register");
        assert_eq!(registered, vk_hash());
        assert_eq!(registered, graph::canonical_vk_hash());
        assert_eq!(
            registry.canonical_bytes(&registered),
            Some(graph::PRIVATE_GRAPH_REWRITE_CELL_DESCRIPTOR_JSON.as_bytes())
        );
        assert_ne!(registered, non_hiding_vk_hash());
    }

    #[test]
    fn real_registry_verifies_rewrite_and_refuses_every_public_join_tamper() {
        let (proof, public) = {
            let old_commit = core::array::from_fn(|lane| 1_000 + lane as u32);
            let new_commit = core::array::from_fn(|lane| 2_000 + lane as u32);
            let (proof, public, retained) =
                graph::prove_zk(11, 77, 9, &witness(), old_commit, new_commit)
                    .expect("private rewrite cell proof");
            assert_eq!(
                retained.app_root_binding.app_root_pi_offset,
                graph::GRAPH_NEW_ROOT_PI_BASE
            );
            assert_eq!(retained.app_root_binding.app_root_len, 8);
            assert_eq!(
                retained.app_root_binding.field_key,
                graph::GRAPH_ROOT_FIELD_KEY
            );
            (proof, public)
        };
        let proof_bytes = proof.to_postcard().expect("postcard proof");
        let public_values = public.as_u32_vec();

        let mut registry = CustomEffectRegistry::empty();
        let vk = register(&mut registry).expect("register exact hiding verifier");
        registry
            .verify(&vk, &pi_bytes(&public_values), &proof_bytes)
            .expect("honest private rewrite verifies through the real registry");

        // Cell pre/post roots plus domain, session, index, ruleset, graph-old,
        // and graph-new each bind independently through the public ABI.
        for pi in [0usize, 8, 16, 17, 20, 21, 29, 37] {
            let mut tampered = public_values.clone();
            tampered[pi] += 1;
            assert!(
                registry
                    .verify(&vk, &pi_bytes(&tampered), &proof_bytes)
                    .is_err(),
                "public input {pi} must bind"
            );
        }

        let mut malformed_pi = pi_bytes(&public_values);
        malformed_pi.pop();
        assert!(registry.verify(&vk, &malformed_pi, &proof_bytes).is_err());

        let mut corrupt_proof = proof_bytes;
        let at = corrupt_proof.len() / 2;
        corrupt_proof[at] ^= 1;
        assert!(
            registry
                .verify(&vk, &pi_bytes(&public_values), &corrupt_proof)
                .is_err()
        );
        assert!(
            registry
                .verify(
                    &non_hiding_vk_hash(),
                    &pi_bytes(&public_values),
                    &corrupt_proof
                )
                .is_err()
        );
    }
}

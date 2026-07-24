//! Predicate-specific verifier for the additive, non-live exact FNSP-v3 transport.
//!
//! Registration and executor dispatch are intentionally absent.  This verifier can only check
//! the typed descriptor recovered from its code-owned canonical program envelope through its
//! predicate-aware entry point; generic verification and every v2/cross-resource route fail
//! closed.

use std::sync::OnceLock;

use dregg_cell::vk_v2::{ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2};
use dregg_turn::ProofVerifier;
use dregg_turn::faithful_note_spend_exact_v3::{
    FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION, FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
    FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE, FaithfulNoteSpendExactV3PublicStatement,
};

use dregg_circuit_prove::faithful_note_spend_exact_v3_identity as identity;

/// Source/build-recipe provenance of the exact verifier closure.  This does not authenticate
/// compiled behavior absent reproducible-build/translation evidence, and no compiled VK or wasm
/// artifact is claimed by this non-live recipe.
pub fn verifier_fingerprint() -> VerifierFingerprint {
    VerifierFingerprint::SourceHash(identity::verifier_source_closure_fingerprint())
}

pub fn proving_system_id() -> ProvingSystemId {
    ProvingSystemId::Plonky3BabyBearFri {
        p3_rev: identity::PLONKY3_REV,
    }
}

/// Canonical non-live identity recipe for the exact FNSP-v3 verifier.
pub fn vk_components() -> VkComponents<'static> {
    VkComponents {
        program_bytes: identity::relation_program_bytes(),
        air_fingerprint: identity::air_fingerprint(),
        verifier_fingerprint: verifier_fingerprint(),
        proving_system_id: proving_system_id(),
    }
}

pub fn vk_hash() -> [u8; 32] {
    canonical_vk_v2(&vk_components())
}

type ExactDescriptor = dregg_circuit::descriptor_ir2::EffectVmDescriptor2;
static EXECUTABLE_RELATION: OnceLock<Result<ExactDescriptor, String>> = OnceLock::new();

fn executable_relation() -> Result<&'static ExactDescriptor, String> {
    match EXECUTABLE_RELATION
        .get_or_init(|| identity::decode_exact_relation_program(vk_components().program_bytes))
    {
        Ok(descriptor) => Ok(descriptor),
        Err(error) => Err(error.clone()),
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct FaithfulNoteSpendExactV3Verifier;

impl FaithfulNoteSpendExactV3Verifier {
    pub const fn new() -> Self {
        Self
    }
}

impl ProofVerifier for FaithfulNoteSpendExactV3Verifier {
    fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
        false
    }

    fn verify_with_predicate(
        &self,
        predicate: &str,
        proof: &[u8],
        action: &str,
        resource: &str,
        public_input_bytes: &[u8],
    ) -> bool {
        if predicate != FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE
            || action != FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION
            || resource != FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE
        {
            return false;
        }
        let public =
            match FaithfulNoteSpendExactV3PublicStatement::decode_verifier_wire(public_input_bytes)
            {
                Ok(public) => public,
                Err(_) => return false,
            };

        // Hostile postcard bytes must become a refusal, never unwind the turn executor.  The
        // callee additionally pins descriptor geometry, exact HidingFRI instance shape, complete
        // postcard consumption, and canonical BabyBear public lanes.
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let descriptor = executable_relation()?;
            dregg_circuit_prove::faithful_note_spend_exact_v3::verify_exact_v3_postcard_with_descriptor(
                descriptor,
                proof,
                public.as_u32_array(),
            )
        }))
        .map(|result| result.is_ok())
        .unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::vk_v2::{VerifierFingerprint, VkComponents, canonical_vk_v2};
    use dregg_turn::faithful_note_spend::{
        FAITHFUL_NOTE_SPEND_PREDICATE, FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT,
    };
    use dregg_turn::faithful_note_spend_exact_v3::{
        FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT,
        FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES,
    };

    #[test]
    fn exact_v3_identity_is_the_staged_code_owned_predicate() {
        assert_eq!(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
            dregg_circuit_prove::faithful_note_spend_exact_v3::STAGED_PREDICATE_NAME
        );
        assert_eq!(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT,
            dregg_circuit_prove::faithful_note_spend_exact_v3::STAGED_PUBLIC_INPUT_COUNT
        );
        identity::validate_provenance().expect("production provenance validates");
        let decoded = identity::decode_relation_program(vk_components().program_bytes)
            .expect("executable relation envelope decodes");
        assert_eq!(decoded.relation_id, identity::RELATION_ID);
        assert_eq!(decoded.relation_version, identity::RELATION_VERSION);
        assert_eq!(decoded.descriptor.name, identity::PREDICATE_NAME);
        assert_eq!(
            executable_relation().expect("cached relation"),
            &decoded.descriptor
        );
        assert!(std::ptr::eq(
            executable_relation().expect("cached relation"),
            executable_relation().expect("cached relation"),
        ));
        assert!(!vk_components().program_bytes.starts_with(b"{"));
        assert_eq!(
            proving_system_id().canonical_bytes(),
            identity::proving_system_canonical_bytes()
        );
        assert_eq!(canonical_vk_v2(&vk_components()), vk_hash());
    }

    #[test]
    fn exact_v3_vk_identity_separates_program_air_source_revision_and_v2() {
        let exact = vk_hash();
        let components = vk_components();

        let mut changed_program = components.program_bytes.to_vec();
        changed_program[12] ^= 1;
        assert_ne!(
            exact,
            canonical_vk_v2(&VkComponents {
                program_bytes: &changed_program,
                air_fingerprint: components.air_fingerprint,
                verifier_fingerprint: components.verifier_fingerprint.clone(),
                proving_system_id: components.proving_system_id.clone(),
            })
        );

        let mut changed_air = components.air_fingerprint;
        changed_air[0] ^= 1;
        assert_ne!(
            exact,
            canonical_vk_v2(&VkComponents {
                program_bytes: components.program_bytes,
                air_fingerprint: changed_air,
                verifier_fingerprint: components.verifier_fingerprint.clone(),
                proving_system_id: components.proving_system_id.clone(),
            })
        );

        let mut changed_source_closure = identity::verifier_source_closure_fingerprint();
        changed_source_closure[0] ^= 1;
        assert_ne!(
            exact,
            canonical_vk_v2(&VkComponents {
                program_bytes: components.program_bytes,
                air_fingerprint: components.air_fingerprint,
                verifier_fingerprint: VerifierFingerprint::SourceHash(changed_source_closure),
                proving_system_id: components.proving_system_id.clone(),
            })
        );

        assert_ne!(
            exact,
            canonical_vk_v2(&VkComponents {
                program_bytes: components.program_bytes,
                air_fingerprint: components.air_fingerprint,
                verifier_fingerprint: components.verifier_fingerprint.clone(),
                proving_system_id: ProvingSystemId::Plonky3BabyBearFri {
                    p3_rev: "different-plonky3-revision",
                },
            })
        );

        // Even if every other component were maliciously reused, v2 descriptor JSON cannot name
        // the exact-v3 executable relation envelope.
        assert_ne!(
            exact,
            canonical_vk_v2(&VkComponents {
                program_bytes: dregg_circuit_prove::faithful_note_spend::DESCRIPTOR_JSON.as_bytes(),
                air_fingerprint: components.air_fingerprint,
                verifier_fingerprint: components.verifier_fingerprint,
                proving_system_id: components.proving_system_id,
            })
        );
    }

    #[test]
    fn equivalent_descriptor_json_encoding_keeps_the_same_vk_identity() {
        const HEADER: &str = concat!(
            "{\"name\":\"faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state\",",
            "\"ir\":2,\"trace_width\":3760,\"public_input_count\":76,"
        );
        let body = identity::EXECUTABLE_DESCRIPTOR_JSON
            .strip_prefix(HEADER)
            .expect("recognized executable descriptor header");
        let alternate_json = format!(
            "{{\n \"trace_width\": 3760, \"public_input_count\": 76, \
             \"ir\": 2, \"name\": \"{}\", {body}\n",
            identity::PREDICATE_NAME
        );
        let alternate = dregg_circuit::descriptor_ir2::parse_vm_descriptor2(&alternate_json)
            .expect("whitespace/key-order equivalent descriptor parses");
        let alternate_program = identity::relation_program_bytes_for_descriptor(&alternate)
            .expect("equivalent descriptor canonically envelopes");
        assert_eq!(alternate_program, identity::relation_program_bytes());
        assert_eq!(
            vk_hash(),
            canonical_vk_v2(&VkComponents {
                program_bytes: &alternate_program,
                air_fingerprint: identity::air_fingerprint(),
                verifier_fingerprint: verifier_fingerprint(),
                proving_system_id: proving_system_id(),
            })
        );
    }

    #[test]
    fn exact_v3_verifier_refuses_generic_cross_version_and_malformed_routes() {
        let verifier = FaithfulNoteSpendExactV3Verifier::new();
        let pi = vec![0u8; FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES];

        assert!(!verifier.verify(
            &[1],
            FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
            FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
            &pi
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_PREDICATE,
            &[1],
            FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
            FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
            &pi,
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
            &[1],
            "transfer",
            FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
            &pi,
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
            &[1],
            FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
            "exact-nullifier-tree",
            &pi,
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
            &[1],
            FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
            FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
            &pi[..pi.len() - 1],
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
            &[1],
            FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
            FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
            &pi,
        ));

        // A v2-width statement can never cross-route into the 76-lane verifier.
        let v2_pi = vec![0u8; FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT * size_of::<u32>()];
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
            &[1],
            FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
            FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
            &v2_pi,
        ));
        let v2_verifier = crate::faithful_note_spend_verifier::FaithfulNoteSpendVerifier::new();
        assert!(!v2_verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
            &[1],
            FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
            FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
            &v2_pi,
        ));

        let mut noncanonical = pi;
        noncanonical[44 * 4..44 * 4 + 4]
            .copy_from_slice(&dregg_circuit::field::BABYBEAR_P.to_le_bytes());
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
            &[1],
            FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
            FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
            &noncanonical,
        ));
    }
}

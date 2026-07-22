//! Predicate-specific verifier for the additive, non-live exact FNSP-v3 transport.
//!
//! Registration and executor dispatch are intentionally absent.  This verifier can only check the
//! one code-owned staged descriptor/config through its predicate-aware entry point; generic
//! verification and every v2/cross-resource route fail closed.

use crate::ProofVerifier;
use crate::faithful_note_spend_exact_v3::{
    FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION, FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
    FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE, FaithfulNoteSpendExactV3PublicStatement,
};

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
            dregg_circuit_prove::faithful_note_spend_exact_v3::verify_staged_exact_v3_postcard(
                proof,
                public.as_u32_array(),
            )
            .is_ok()
        }))
        .unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::faithful_note_spend::{
        FAITHFUL_NOTE_SPEND_PREDICATE, FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT,
    };
    use crate::faithful_note_spend_exact_v3::{
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
        let v2_verifier = crate::FaithfulNoteSpendVerifier::new();
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

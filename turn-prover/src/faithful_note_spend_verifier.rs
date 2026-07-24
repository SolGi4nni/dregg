//! Predicate-only verifier for the faithful hidden-note spend.
//!
//! This is deliberately separate from descriptor-generic verification.  The
//! relation has one executor-owned predicate identity, one fixed public-input
//! ABI, and one HidingFRI configuration.  In particular, the predicate-less
//! [`ProofVerifier::verify`] entry point can never accept this proof.

use dregg_turn::ProofVerifier;
use dregg_turn::faithful_note_spend::{
    FAITHFUL_NOTE_SPEND_PREDICATE, FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT,
};

/// Production verifier for `faithful-note-spend-v2`.
#[derive(Clone, Copy, Debug, Default)]
pub struct FaithfulNoteSpendVerifier;

impl FaithfulNoteSpendVerifier {
    /// Construct the fail-closed predicate-specific verifier.
    pub const fn new() -> Self {
        Self
    }

    fn decode_public_inputs(bytes: &[u8]) -> Option<[u32; FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT]> {
        if bytes.len() != FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT * size_of::<u32>() {
            return None;
        }
        let mut values = [0u32; FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT];
        for (value, chunk) in values.iter_mut().zip(bytes.chunks_exact(4)) {
            *value = u32::from_le_bytes(chunk.try_into().expect("four-byte public-input lane"));
        }
        Some(values)
    }
}

impl ProofVerifier for FaithfulNoteSpendVerifier {
    /// A descriptor identity is mandatory; a bare proof is meaningless.
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
        if predicate != FAITHFUL_NOTE_SPEND_PREDICATE
            || action != "note-spend"
            || resource != "faithful-note-tree"
        {
            return false;
        }
        let public_inputs = match Self::decode_public_inputs(public_input_bytes) {
            Some(inputs) => inputs,
            None => return false,
        };

        // Malformed attacker-controlled proof structure must be a refusal, not
        // a process abort.  The callee additionally performs strict postcard
        // consumption, exact descriptor/instance-shape checks, canonical PI
        // checks, and HidingFRI verification.
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            dregg_circuit_prove::faithful_note_spend::verify_postcard(proof, &public_inputs).is_ok()
        }))
        .unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zero_statement() -> Vec<u8> {
        vec![0; FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT * size_of::<u32>()]
    }

    #[test]
    fn faithful_verifier_refuses_every_ambiguous_or_malformed_entry() {
        let verifier = FaithfulNoteSpendVerifier::new();
        let pi = zero_statement();

        assert!(!verifier.verify(&[1], "note-spend", "faithful-note-tree", &pi));
        assert!(!verifier.verify_with_predicate(
            "faithful-note-spend-v1",
            &[1],
            "note-spend",
            "faithful-note-tree",
            &pi,
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_PREDICATE,
            &[1],
            "transfer",
            "faithful-note-tree",
            &pi,
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_PREDICATE,
            &[1],
            "note-spend",
            "other-tree",
            &pi,
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_PREDICATE,
            &[1],
            "note-spend",
            "faithful-note-tree",
            &pi[..pi.len() - 1],
        ));
        assert!(!verifier.verify_with_predicate(
            FAITHFUL_NOTE_SPEND_PREDICATE,
            &[1],
            "note-spend",
            "faithful-note-tree",
            &pi,
        ));
    }
}

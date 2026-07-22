//! Additive, non-live acceptance seam for exact FNSP-v3 note spends.
//!
//! This module joins three independently owned facts without changing executor dispatch:
//!
//! 1. the signed [`Effect::NoteSpend`] supplies the historical root, nullifier, value, asset, and
//!    strict v3 carrier;
//! 2. a validated exact AAFI transition plus a durable actor anchor supply every accumulator and
//!    outer-state lane; and
//! 3. the code-owned exact-v3 verifier receives only the carrier's inner proof bytes and the
//!    resulting canonical 76-lane statement.
//!
//! The public entry point has no predicate, action, resource, descriptor, VK, or verifier argument.
//! It is intentionally not registered in the live executor yet.

use core::fmt;
use std::error::Error;

use crate::ProofVerifier;
use crate::action::Effect;
use crate::faithful_note_spend_exact_v3::{
    FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION, FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
    FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE, FaithfulNoteSpendExactV3Error,
    FaithfulNoteSpendExactV3ProofCarrier, FaithfulNoteSpendExactV3PublicStatement,
    FaithfulNoteSpendExactV3StateInputs,
};
use crate::faithful_note_spend_exact_v3_anchor::ExactFnspV3DurableAnchor;
use crate::faithful_note_spend_exact_v3_verifier::FaithfulNoteSpendExactV3Verifier;
use dregg_circuit::exact_nullifier_aafi::ValidatedExactAafiTransition;

/// Verify one exact FNSP-v3 note spend against independently validated transition and durable
/// state.
///
/// `signed_effect` must be the effect recovered from the already-authenticated turn envelope.  The
/// executor cutover will call this only after turn signature/authentication checks; this seam does
/// not accept an unsigned proof-controlled statement as a substitute.
///
/// This function is additive and non-live: it does not mutate the exact accumulator, install a
/// verifier, or alter the v2 route.
pub fn verify_faithful_note_spend_exact_v3_acceptance(
    signed_effect: &Effect,
    transition: &ValidatedExactAafiTransition,
    durable_anchor: &ExactFnspV3DurableAnchor,
) -> Result<(), FaithfulNoteSpendExactV3AcceptanceError> {
    verify_with_code_owned_identity(
        &FaithfulNoteSpendExactV3Verifier::new(),
        signed_effect,
        transition,
        durable_anchor,
    )
}

/// Private verifier-injection seam used to prove ordering and exact argument transport in hostile
/// tests.  Production callers can reach only the public function above, which fixes the concrete
/// exact-v3 verifier and every identity string in code.
fn verify_with_code_owned_identity(
    verifier: &dyn ProofVerifier,
    signed_effect: &Effect,
    transition: &ValidatedExactAafiTransition,
    durable_anchor: &ExactFnspV3DurableAnchor,
) -> Result<(), FaithfulNoteSpendExactV3AcceptanceError> {
    let Effect::NoteSpend {
        nullifier,
        value,
        spending_proof,
        ..
    } = signed_effect
    else {
        return Err(FaithfulNoteSpendExactV3Error::NotNoteSpend.into());
    };

    // Join the signed turn fields to the independently validated host transition before parsing or
    // verifying the proof.  Asset type has no field in the exact accumulator transition and stays
    // proof-bound in the 76-lane statement.
    if nullifier.0 != transition.inserted_raw() {
        return Err(FaithfulNoteSpendExactV3AcceptanceError::SignedNullifierMismatch);
    }
    if *value != transition.inserted_value() {
        return Err(
            FaithfulNoteSpendExactV3AcceptanceError::SignedValueMismatch {
                signed: *value,
                transition: transition.inserted_value(),
            },
        );
    }

    // Decode before statement construction so the proof submitted to the verifier is exactly the
    // canonical carrier's inner payload.  Generic/v2/malformed carriers never reach verification.
    let carrier = FaithfulNoteSpendExactV3ProofCarrier::decode(spending_proof)?;

    // This must precede verifier invocation.  It checks both prior and successor FNS3 octets at
    // every scattered durable-state offset, preventing mixed transition/anchor statements.
    let state = FaithfulNoteSpendExactV3StateInputs::derive_from_durable_anchor(
        transition,
        durable_anchor,
    )?;
    let public =
        FaithfulNoteSpendExactV3PublicStatement::from_signed_effect(signed_effect, &state)?;
    let public_wire = public.encode_public_inputs();

    if !verifier.verify_with_predicate(
        FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
        carrier.inner_proof_bytes(),
        FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
        FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
        &public_wire,
    ) {
        return Err(FaithfulNoteSpendExactV3AcceptanceError::ProofRejected);
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FaithfulNoteSpendExactV3AcceptanceError {
    /// Carrier, signed-statement, or independently derived state was invalid.
    Statement(FaithfulNoteSpendExactV3Error),
    /// The signed nullifier did not name the exact key inserted by the validated transition.
    SignedNullifierMismatch,
    /// The signed released value did not equal the exact value inserted by the transition.
    SignedValueMismatch { signed: u64, transition: u64 },
    /// The strict code-owned exact-v3 HidingFRI verifier refused the inner proof.
    ProofRejected,
}

impl From<FaithfulNoteSpendExactV3Error> for FaithfulNoteSpendExactV3AcceptanceError {
    fn from(error: FaithfulNoteSpendExactV3Error) -> Self {
        Self::Statement(error)
    }
}

impl fmt::Display for FaithfulNoteSpendExactV3AcceptanceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Statement(error) => write!(f, "exact FNSP-v3 statement refused: {error}"),
            Self::SignedNullifierMismatch => f.write_str(
                "exact FNSP-v3 signed nullifier does not match the validated transition",
            ),
            Self::SignedValueMismatch { signed, transition } => write!(
                f,
                "exact FNSP-v3 signed value {signed} does not match transition value {transition}"
            ),
            Self::ProofRejected => f.write_str("exact FNSP-v3 proof rejected"),
        }
    }
}

impl Error for FaithfulNoteSpendExactV3AcceptanceError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Statement(error) => Some(error),
            Self::SignedNullifierMismatch
            | Self::SignedValueMismatch { .. }
            | Self::ProofRejected => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    use crate::action::Event;
    use crate::faithful_note_spend::FaithfulNoteSpendProofCarrier;
    use crate::faithful_note_spend_exact_v3::{
        FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT,
        FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES,
    };
    use crate::faithful_note_spend_exact_v3_anchor::derive_exact_fnsp_v3_durable_anchor;
    use dregg_cell::commitment::{RotationCarrierMaterial, V9RotationContext, digest8_to_bytes32};
    use dregg_cell::{Cell, CellId, FIELD_ZERO, Nullifier};
    use dregg_circuit::Faithful8;
    use dregg_circuit::exact_nullifier_aafi::{
        Digest8, ExactNullifierAafi, validate_exact_aafi_witness,
    };
    use dregg_circuit::field::BabyBear;

    const INNER_PROOF: &[u8] = &[0xde, 0xad, 0xbe, 0xef];

    fn actor() -> Cell {
        let mut cell = Cell::new([7u8; 32], [9u8; 32]);
        assert!(cell.state.credit_balance(500));
        cell.state.set_nonce(11);
        cell
    }

    fn context(prior_fns3: Digest8) -> V9RotationContext {
        V9RotationContext {
            cells_root: BabyBear::new(101),
            nullifier_root: Faithful8::from_bytes32(&digest8_to_bytes32(prior_fns3)),
            commitments_root: Faithful8::ZERO,
            revoked_root: Faithful8::ZERO,
            iroot: BabyBear::new(202),
            material: RotationCarrierMaterial::default(),
        }
    }

    fn canonical_note_spend(nullifier: [u8; 32], value: u64, proof: Vec<u8>) -> Effect {
        let mut note_tree_root = [0u8; 32];
        for lane in 0..8 {
            note_tree_root[lane * 4..lane * 4 + 4]
                .copy_from_slice(&(100 + lane as u32).to_le_bytes());
        }
        Effect::NoteSpend {
            nullifier: Nullifier(nullifier),
            note_tree_root,
            value,
            asset_type: 0x0123_4567_89ab_cdef,
            spending_proof: proof,
            value_commitment: None,
        }
    }

    fn fixture(
        key: [u8; 32],
        value: u64,
    ) -> (
        ValidatedExactAafiTransition,
        ExactFnspV3DurableAnchor,
        Effect,
    ) {
        let witness = ExactNullifierAafi::new()
            .prepare_insert(key, value)
            .expect("fresh exact insertion");
        let transition = validate_exact_aafi_witness(&witness).expect("valid transition");
        let anchor = derive_exact_fnsp_v3_durable_anchor(
            &actor(),
            &context(witness.prior_state_commit),
            witness.prior_state_commit,
            witness.successor_state_commit,
        )
        .expect("durable anchor");
        let carrier =
            FaithfulNoteSpendExactV3ProofCarrier::new(0x1122_3344_5566_7788, INNER_PROOF.to_vec())
                .expect("carrier");
        (
            transition,
            anchor,
            canonical_note_spend(key, value, carrier.encode()),
        )
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct VerificationCall {
        predicate: String,
        proof: Vec<u8>,
        action: String,
        resource: String,
        public: Vec<u8>,
    }

    #[derive(Default)]
    struct RecordingVerifier {
        calls: Mutex<Vec<VerificationCall>>,
        accept: bool,
    }

    impl RecordingVerifier {
        fn accepting() -> Self {
            Self {
                calls: Mutex::new(Vec::new()),
                accept: true,
            }
        }

        fn calls(&self) -> Vec<VerificationCall> {
            self.calls.lock().expect("recording verifier lock").clone()
        }
    }

    impl ProofVerifier for RecordingVerifier {
        fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
            panic!("exact v3 acceptance must not use generic verification")
        }

        fn verify_with_predicate(
            &self,
            predicate: &str,
            proof: &[u8],
            action: &str,
            resource: &str,
            public: &[u8],
        ) -> bool {
            self.calls
                .lock()
                .expect("recording verifier lock")
                .push(VerificationCall {
                    predicate: predicate.to_owned(),
                    proof: proof.to_vec(),
                    action: action.to_owned(),
                    resource: resource.to_owned(),
                    public: public.to_vec(),
                });
            self.accept
        }
    }

    #[test]
    fn acceptance_passes_only_inner_proof_and_exact_durable_76_lanes() {
        let (transition, anchor, effect) = fixture([0x5a; 32], 0x8877_6655_4433_2211);
        let verifier = RecordingVerifier::accepting();

        assert_eq!(
            verify_with_code_owned_identity(&verifier, &effect, &transition, &anchor),
            Ok(())
        );
        let calls = verifier.calls();
        assert_eq!(calls.len(), 1);
        let call = &calls[0];
        assert_eq!(call.predicate, FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE);
        assert_eq!(call.action, FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION);
        assert_eq!(call.resource, FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE);
        assert_eq!(call.proof, INNER_PROOF);
        assert_ne!(
            call.proof,
            match &effect {
                Effect::NoteSpend { spending_proof, .. } => spending_proof.as_slice(),
                _ => unreachable!(),
            }
        );
        assert_eq!(
            call.public.len(),
            FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES
        );

        let lanes: Vec<u32> = call
            .public
            .chunks_exact(4)
            .map(|chunk| u32::from_le_bytes(chunk.try_into().expect("public lane")))
            .collect();
        assert_eq!(lanes.len(), FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT);
        assert_eq!(&lanes[60..76], &anchor.expected_outer_public_inputs());
        assert_eq!(
            &lanes[36..44],
            &transition.successor_root().map(|felt| felt.as_u32())
        );
        assert_eq!(
            &lanes[44..52],
            &transition.prior_root().map(|felt| felt.as_u32())
        );
    }

    #[test]
    fn acceptance_refuses_non_note_malformed_and_v2_before_verification() {
        let (transition, anchor, _) = fixture([0x5a; 32], 7);
        let verifier = RecordingVerifier::accepting();
        let non_note = Effect::EmitEvent {
            cell: CellId::from_bytes([0; 32]),
            event: Event {
                topic: [0; 32],
                data: vec![FIELD_ZERO],
            },
        };
        assert!(matches!(
            verify_with_code_owned_identity(&verifier, &non_note, &transition, &anchor),
            Err(FaithfulNoteSpendExactV3AcceptanceError::Statement(
                FaithfulNoteSpendExactV3Error::NotNoteSpend
            ))
        ));

        let malformed = canonical_note_spend([0x5a; 32], 7, b"not-an-fnsp-carrier".to_vec());
        assert!(matches!(
            verify_with_code_owned_identity(&verifier, &malformed, &transition, &anchor),
            Err(FaithfulNoteSpendExactV3AcceptanceError::Statement(
                FaithfulNoteSpendExactV3Error::Truncated { .. }
            ))
        ));

        let v2 = FaithfulNoteSpendProofCarrier::new(7, Faithful8::ZERO.to_bytes32(), vec![9])
            .expect("v2 carrier")
            .encode();
        assert!(matches!(
            verify_with_code_owned_identity(
                &verifier,
                &canonical_note_spend([0x5a; 32], 7, v2),
                &transition,
                &anchor,
            ),
            Err(FaithfulNoteSpendExactV3AcceptanceError::Statement(
                FaithfulNoteSpendExactV3Error::UnsupportedVersion(2)
            ))
        ));
        assert!(verifier.calls().is_empty());
    }

    #[test]
    fn signed_nullifier_and_value_must_join_transition_before_carrier_or_verifier() {
        let (transition, anchor, effect) = fixture([0x5a; 32], 7);
        let verifier = RecordingVerifier::accepting();

        let mut wrong_nullifier = effect.clone();
        if let Effect::NoteSpend {
            nullifier,
            spending_proof,
            ..
        } = &mut wrong_nullifier
        {
            *nullifier = Nullifier([0x99; 32]);
            *spending_proof = b"malformed is never parsed".to_vec();
        }
        assert_eq!(
            verify_with_code_owned_identity(&verifier, &wrong_nullifier, &transition, &anchor,),
            Err(FaithfulNoteSpendExactV3AcceptanceError::SignedNullifierMismatch)
        );

        let mut wrong_value = effect;
        if let Effect::NoteSpend {
            value,
            spending_proof,
            ..
        } = &mut wrong_value
        {
            *value = 8;
            *spending_proof = b"malformed is never parsed".to_vec();
        }
        assert_eq!(
            verify_with_code_owned_identity(&verifier, &wrong_value, &transition, &anchor),
            Err(
                FaithfulNoteSpendExactV3AcceptanceError::SignedValueMismatch {
                    signed: 8,
                    transition: 7,
                }
            )
        );
        assert!(verifier.calls().is_empty());
    }

    #[test]
    fn mixed_transition_and_anchor_refuses_before_proof_verification() {
        let (transition_a, _, effect) = fixture([0x31; 32], 31);
        let (_, anchor_b, _) = fixture([0x32; 32], 32);
        let verifier = RecordingVerifier::accepting();

        assert!(matches!(
            verify_with_code_owned_identity(&verifier, &effect, &transition_a, &anchor_b),
            Err(FaithfulNoteSpendExactV3AcceptanceError::Statement(
                FaithfulNoteSpendExactV3Error::StateProducerMismatch { .. }
            ))
        ));
        assert!(verifier.calls().is_empty());
    }

    #[test]
    fn dummy_inner_proof_is_rejected_by_code_owned_exact_verifier() {
        let (transition, anchor, effect) = fixture([0x5a; 32], 0x8877_6655_4433_2211);
        assert_eq!(
            verify_faithful_note_spend_exact_v3_acceptance(&effect, &transition, &anchor),
            Err(FaithfulNoteSpendExactV3AcceptanceError::ProofRejected)
        );
    }
}

//! ⚑ The exact-FNSP-v3 SEAM, armed: with `dregg-turn-prover`'s code-owned
//! verifier installed as the process proof authority, the core mint reaches the
//! REAL HidingFRI verifier and gets a real refusal.
//!
//! Its twin `exact_v3_authority_fail_closed.rs` is a SEPARATE test binary that
//! never installs — that separation is load-bearing, because the authority slot is
//! a process-wide install-once `OnceLock`, so "installed" and "not installed"
//! cannot be observed in the same process.
//!
//! What this pins:
//! - the authority slot goes false → true on install, and a SECOND install is
//!   REFUSED (proof authority cannot be downgraded mid-run);
//! - with it installed, `verify_faithful_note_spend_exact_v3_acceptance` no longer
//!   short-circuits — it runs the joins and hands the carrier's inner bytes to
//!   `FaithfulNoteSpendExactV3Verifier`, which REJECTS a bogus proof
//!   (`ProofRejected`, not `ProofAuthorityNotInstalled`). Accept-side authority
//!   therefore genuinely rides the crate boundary, and it is fail-closed.

use std::sync::Arc;

use dregg_cell::commitment::{RotationCarrierMaterial, V9RotationContext, digest8_to_bytes32};
use dregg_cell::{AuthRequired, Cell, Nullifier, Permissions};
use dregg_circuit::Faithful8;
use dregg_circuit::exact_nullifier_aafi::{
    Digest8, ExactNullifierAafi, ValidatedExactAafiTransition, validate_exact_aafi_witness,
};
use dregg_circuit::field::BabyBear;
use dregg_turn::action::Effect;
use dregg_turn::faithful_note_spend_exact_v3::FaithfulNoteSpendExactV3ProofCarrier;
use dregg_turn::faithful_note_spend_exact_v3_anchor::{
    ExactFnspV3DurableAnchor, derive_exact_fnsp_v3_durable_anchor,
};
use dregg_turn::{
    FaithfulNoteSpendExactV3AcceptanceError, exact_fnsp_v3_proof_authority_installed,
    install_exact_fnsp_v3_proof_authority, verify_faithful_note_spend_exact_v3_acceptance,
};
use dregg_turn_prover::{
    FaithfulNoteSpendExactV3Verifier, install_code_owned_exact_fnsp_v3_verifier,
};

fn actor() -> Cell {
    let mut cell = Cell::new([7u8; 32], [9u8; 32]);
    assert!(cell.state.credit_balance(500));
    cell.state.set_nonce(11);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

fn context(prior_fns3: Digest8) -> V9RotationContext {
    V9RotationContext {
        // wound #23: `cells_root` is a `Faithful8` group; a fixture names a faithful constructor.
        cells_root: dregg_circuit::heap_root::empty_heap_root_8(),
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
        note_tree_root[lane * 4..lane * 4 + 4].copy_from_slice(&(100 + lane as u32).to_le_bytes());
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
    // A structurally valid carrier whose INNER bytes are not a proof of anything:
    // it must reach, and be refused by, the real verifier.
    let carrier = FaithfulNoteSpendExactV3ProofCarrier::new(
        0x1122_3344_5566_7788,
        vec![0xde, 0xad, 0xbe, 0xef],
    )
    .expect("carrier");
    (
        transition,
        anchor,
        canonical_note_spend(key, value, carrier.encode()),
    )
}

#[test]
fn installed_authority_reaches_the_real_verifier_and_refuses_a_bogus_proof() {
    assert!(
        !exact_fnsp_v3_proof_authority_installed(),
        "the process must start with NO exact-v3 proof authority"
    );

    install_code_owned_exact_fnsp_v3_verifier().expect("first install must succeed");
    assert!(
        exact_fnsp_v3_proof_authority_installed(),
        "dregg-turn-prover installs the code-owned verifier across the crate boundary"
    );

    // Install-once: proof authority cannot be swapped after the fact.
    assert!(
        install_code_owned_exact_fnsp_v3_verifier().is_err(),
        "a second install must be REFUSED — no later crate may downgrade proof authority"
    );
    assert!(
        install_exact_fnsp_v3_proof_authority(Arc::new(FaithfulNoteSpendExactV3Verifier::new()))
            .is_err(),
        "the raw core installer is equally one-shot"
    );

    let (transition, anchor, effect) = fixture([0x11; 32], 4_242);
    let error = verify_faithful_note_spend_exact_v3_acceptance(&effect, &transition, &anchor)
        .expect_err("garbage inner proof bytes must not mint an acceptance token");
    assert_eq!(
        error,
        FaithfulNoteSpendExactV3AcceptanceError::ProofRejected,
        "with an authority installed the mint must reach the REAL HidingFRI verifier \
         and take its refusal — NOT short-circuit on a missing authority"
    );
}

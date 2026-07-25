//! ⚑ FAIL-CLOSED CANARY (exact-FNSP-v3): a process that never installs a proof
//! authority CANNOT mint an acceptance token — it refuses, it does not silently
//! succeed.
//!
//! This is a SEPARATE test binary from `exact_v3_authority_installed.rs` on
//! purpose: the authority is a process-wide install-once `OnceLock`, so the
//! not-installed state only exists in a process that never installs. Linking
//! `dregg-turn-prover` is NOT enough — the node has to actually call
//! `install_code_owned_exact_fnsp_v3_verifier()`. That is exactly the property
//! that replaces the deleted `#[cfg(not(feature = "prover"))]` build.
//!
//! Downstream consequence, pinned by construction: with no token mintable, no
//! token can be installed in the executor's admission slot, so the exact-v3
//! `NoteSpend` route in `apply` (which now dispatches at RUNTIME on
//! `slot.pending.is_some()`, not on a `#[cfg]`) can never be selected.

use dregg_cell::commitment::{RotationCarrierMaterial, V9RotationContext, digest8_to_bytes32};
use dregg_cell::{AuthRequired, Cell, Nullifier, Permissions};
use dregg_circuit::Faithful8;
use dregg_circuit::exact_nullifier_aafi::{
    Digest8, ExactNullifierAafi, validate_exact_aafi_witness,
};
use dregg_circuit::field::BabyBear;
use dregg_turn::action::Effect;
use dregg_turn::executor::{ComputronCosts, TurnExecutor};
use dregg_turn::faithful_note_spend_exact_v3::FaithfulNoteSpendExactV3ProofCarrier;
use dregg_turn::faithful_note_spend_exact_v3_anchor::derive_exact_fnsp_v3_durable_anchor;
use dregg_turn::{
    FaithfulNoteSpendExactV3AcceptanceError, exact_fnsp_v3_proof_authority_installed,
    verify_faithful_note_spend_exact_v3_acceptance,
};

// Linking the prover crate WITHOUT calling its installer must not arm anything.
use dregg_turn_prover as _;

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

#[test]
fn no_installed_authority_means_no_acceptance_token_can_be_minted() {
    assert!(
        !exact_fnsp_v3_proof_authority_installed(),
        "merely LINKING dregg-turn-prover must not install proof authority"
    );

    let key = [0x22; 32];
    let value = 7_777u64;
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
        FaithfulNoteSpendExactV3ProofCarrier::new(0x1122_3344_5566_7788, vec![0xde, 0xad])
            .expect("carrier");
    let mut note_tree_root = [0u8; 32];
    for lane in 0..8 {
        note_tree_root[lane * 4..lane * 4 + 4].copy_from_slice(&(100 + lane as u32).to_le_bytes());
    }
    let effect = Effect::NoteSpend {
        nullifier: Nullifier(key),
        note_tree_root,
        value,
        asset_type: 0x0123_4567_89ab_cdef,
        spending_proof: carrier.encode(),
        value_commitment: None,
    };

    let error = verify_faithful_note_spend_exact_v3_acceptance(&effect, &transition, &anchor)
        .expect_err("no proof authority ⇒ NO acceptance token, ever");
    assert_eq!(
        error,
        FaithfulNoteSpendExactV3AcceptanceError::ProofAuthorityNotInstalled,
        "the refusal must name the MISSING AUTHORITY, so a verify-only deployment is \
         never mistaken for a rejected proof"
    );
}

#[test]
fn the_admission_slot_exists_unconditionally_and_starts_empty() {
    // The executor's exact-v3 admission slot is no longer a `#[cfg]`'d struct
    // field: the struct's SHAPE is feature-independent now. A verify-only
    // deployment carries the slot, it is simply always empty because nothing can
    // mint a token to install.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    assert!(
        executor
            .take_consumed_exact_fnsp_v3_admission()
            .expect("the slot mutex is live in every build")
            .is_none(),
        "a fresh executor has no consumed exact-v3 acceptance"
    );
    assert!(
        !executor
            .promote_applied_exact_fnsp_v3_admission_after_commit()
            .expect("promotion is callable in every build"),
        "nothing was applied, so nothing promotes"
    );
}

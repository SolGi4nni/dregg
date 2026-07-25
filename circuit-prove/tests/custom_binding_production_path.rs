//! # THE PRODUCTION-PATH CUSTOM-BINDING LIGHT-CLIENT TOOTH.
//!
//! The sibling of `custom_binding_deployed_tooth.rs`, but proving the binding over the
//! PRODUCTION-POPULATED fold rather than a hand-attached witness. Where the deployed tooth calls
//! `RotatedParticipantLeg::with_custom_witness` directly (a test-only setter), this builds the leg
//! through the PRODUCTION recipe:
//!
//!   1. the genuine `BoundCustomProof` is built RETAINING the re-provable trace witness,
//!      prover-side (the direct-construction form that survived stark-kill — the hand
//!      `prove_custom_program` STARK engine is deleted; the fold path RE-PROVES the leaf from the
//!      retained witness, so the off-AIR bytes are not load-bearing here);
//!   2. `CustomWitnessBundle::from_bound_custom_proof` projects that retained witness into the bundle
//!      (the RETENTION SEAM) — `None`-fail-closed if the proof came off the wire;
//!   3. `dregg_turn_prover::rotation_witness::mint_custom_wide_rotated_participant_leg` drives `produce`
//!      over the real before/after `Cell`s and mints the `customVmDescriptor2R24` WIDE leg with the
//!      bundle ATTACHED — the production minter (not the test setter).
//!
//! The chain then folds through the SAME deployed prover (`prove_turn_chain_recursive`) and verifies
//! through the SAME light-client verifier (`verify_turn_chain_recursive`). This is the proof that
//! PRODUCTION populates the fold: a custom turn proven this way REJECTS a forged `proof_commitment`
//! for a pure light client, with no off-AIR re-execution.
//!
//! The fold is a real recursion (minutes), so both poles are `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test custom_binding_production_path -- --ignored --nocapture

mod binding_tooth;
use binding_tooth::assert_refused_by_binding_node;

use std::collections::HashMap;

use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::effect_vm::custom_state_binding::{
    CUSTOM_PI_STATE_PREFIX_LEN, custom_pi_state_prefix,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::refusal::must_refuse;
use dregg_circuit_prove::custom_proof_bind::BoundCustomProof;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, prove_turn_chain_recursive, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{CustomWitnessBundle, DescriptorParticipant};
use dregg_turn_prover::rotation_witness::mint_custom_wide_rotated_participant_leg;

// ============================================================================
// Fixtures (the same minimal-but-REAL custom program the adapter teeth use).
// ============================================================================

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn demo_program() -> CellProgram {
    let p_minus_1 = BabyBear::new(BABYBEAR_P - 1);
    let descriptor = CircuitDescriptor {
        name: "dregg-custom-demo-v1".to_string(),
        trace_width: 4,
        max_degree: 2,
        columns: vec![
            ColumnDef {
                name: "old".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "amt".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "new".into(),
                index: 2,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "dir".into(),
                index: 3,
                kind: ColumnKind::Binary,
            },
        ],
        constraints: vec![
            ConstraintExpr::Binary { col: 3 },
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![2],
                    },
                    PolyTerm {
                        coeff: p_minus_1,
                        col_indices: vec![0],
                    },
                    PolyTerm {
                        coeff: p_minus_1,
                        col_indices: vec![1],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(2),
                        col_indices: vec![3, 1],
                    },
                ],
            },
        ],
        boundaries: vec![],
        // THE STATE-BINDING ABI: `[old8 ‖ new8 ‖ old_bal, new_bal]` (18 PIs). The deployed prover
        // mints the 24-lane state leaf under the state-binding node, so a custom carrier MUST
        // publish this prefix — a 2-PI program is refused fail-closed (as the deployed executor
        // already refused it).
        public_input_count: CUSTOM_PI_STATE_PREFIX_LEN + 2,
        lookup_tables: vec![],
    };
    CellProgram::new(descriptor, 1)
}

fn honest_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
    let rows = 4;
    let mut w = HashMap::new();
    w.insert("old".into(), vec![BabyBear::new(10); rows]);
    w.insert("amt".into(), vec![BabyBear::new(5); rows]);
    w.insert("new".into(), vec![BabyBear::new(15); rows]);
    w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
    (w, rows)
}

/// The state-binding sub-proof's public inputs: `[old8 ‖ new8 ‖ 10, 15]` — the ABI prefix over the
/// leg's REAL wide rotated roots, then the app PIs.
fn custom_pis(old8: &[BabyBear; 8], new8: &[BabyBear; 8]) -> Vec<BabyBear> {
    let mut pis = custom_pi_state_prefix(old8, new8).to_vec();
    pis.push(BabyBear::new(10));
    pis.push(BabyBear::new(15));
    pis
}

const CHAIN_BALANCE: i64 = 1000i64;

/// **THE PRODUCTION LEG'S REAL ROTATED ROOTS.** Mint a probe leg through the PRODUCTION minter and
/// read its wide 8-felt anchors — what the deployed state fold connects the sub-proof's declared
/// prefix to. Sound because the wide roots come from the rotation witness (the cell's limbs +
/// iroot) and do not depend on the claimed commitment or on the attached bundle; the honest pole
/// asserts that independence.
fn leg_real_roots(nonce: u64) -> ([BabyBear; 8], [BabyBear; 8]) {
    let probe_pis = custom_pis(&[BabyBear::ZERO; 8], &[BabyBear::ZERO; 8]);
    let probe = mint_production_custom_leg(
        CHAIN_BALANCE,
        nonce,
        [BabyBear::ZERO; 8],
        &bound_over(probe_pis),
    );
    (
        probe
            .wide_old_root8()
            .expect("the production custom leg is wide-anchored"),
        probe
            .wide_new_root8()
            .expect("the production custom leg is wide-anchored"),
    )
}

/// Build the genuine `BoundCustomProof` exactly as the turn-build path does — RETAINING the
/// re-provable witness (the field the deployed fold needs). The hand-STARK
/// `prove_custom_program` died with stark-kill; the surviving production form constructs the
/// bound proof directly over the retained witness (the fold RE-PROVES the sub-proof as a
/// recursion leaf from `witness_values`/`num_rows`, so `proof_bytes` is not load-bearing on
/// this path — the wire projection is exercised by `wide_completeness_ledger`).
fn bound_over(pis: Vec<BabyBear>) -> BoundCustomProof {
    let program = demo_program();
    let (w, rows) = honest_witness();
    BoundCustomProof {
        program,
        proof_bytes: Vec::new(),
        public_inputs: pis,
        witness_values: Some(w),
        num_rows: Some(rows),
    }
}

/// The HONEST bound proof: it declares the leg's REAL rotated roots, so both teeth of the deployed
/// state-binding node are satisfiable.
fn honest_bound() -> BoundCustomProof {
    let (old8, new8) = leg_real_roots(0);
    bound_over(custom_pis(&old8, &new8))
}

/// Mint the PRODUCTION custom-wide leg (the `customVmDescriptor2R24` wide leg + the attached
/// re-provable bundle projected from `bound`) at `(balance, nonce)` whose claimed
/// `proof_commitment` is `commit`. Custom bumps the nonce by 1.
fn mint_production_custom_leg(
    balance: i64,
    nonce: u64,
    commit: [BabyBear; 8],
    bound: &BoundCustomProof,
) -> dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg {
    let st = CellState::new(balance as u64, nonce as u32);
    let effects = vec![Effect::Custom {
        program_vk_hash: [BabyBear::new(9); 8],
        proof_commitment: commit,
    }];
    let before_cell = producer_cell(balance, nonce);
    let after_cell = producer_cell(balance, nonce + 1);

    // THE RETENTION SEAM: project the retained witness into the bundle the production minter attaches.
    let bundle = CustomWitnessBundle::from_bound_custom_proof(bound)
        .expect("a freshly-proven BoundCustomProof retains its witness (not off the wire)");

    mint_custom_wide_rotated_participant_leg(
        &st,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[[3u8; 32]],
        None,
        bundle,
    )
    .expect("the production custom-wide minter mints the leg with the bundle attached")
}

/// A plain trailing custom turn (no bundle — the ordinary segment-leaf path) so the chain has >= 2
/// turns and links off the bundled turn's post-state.
fn plain_custom_turn(balance: i64, nonce: u64, bound: &BoundCustomProof) -> FinalizedTurn {
    let st = CellState::new(balance as u64, nonce as u32);
    let effects = vec![Effect::Custom {
        program_vk_hash: [BabyBear::new(9); 8],
        proof_commitment: [
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
            BabyBear::new(5),
            BabyBear::new(6),
            BabyBear::new(7),
            BabyBear::new(8),
        ],
    }];
    // Re-use the production NARROW recipe for a non-bundled custom turn? The narrow recipe rejects
    // Custom; build a bundled wide leg but DROP the binding by not threading a witness is not an
    // option through the public minter. Use the wide minter and then clear the witness so the chain
    // prover takes the ordinary segment-leaf branch for this trailing turn.
    let bundle = CustomWitnessBundle::from_bound_custom_proof(bound).expect("retained witness");
    let before_cell = producer_cell(balance, nonce);
    let after_cell = producer_cell(balance, nonce + 1);
    let mut leg = mint_custom_wide_rotated_participant_leg(
        &st,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[[3u8; 32]],
        None,
        bundle,
    )
    .expect("trailing custom-wide leg mints");
    leg.carrier_witness = None;
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

fn build_chain(commit: [BabyBear; 8]) -> Vec<FinalizedTurn> {
    build_chain_with(commit, &honest_bound())
}

/// Build the 2-turn chain from an EXPLICIT `(commit, bound)`, so each tooth forges exactly one
/// thing.
fn build_chain_with(commit: [BabyBear; 8], bound: &BoundCustomProof) -> Vec<FinalizedTurn> {
    let balance = CHAIN_BALANCE;
    let t0_leg = mint_production_custom_leg(balance, 0, commit, bound);
    // THE TWO-PHASE SAFETY ASSERT: the real leg publishes the SAME wide roots the probe leg did —
    // i.e. the roots do not depend on the claimed commitment or the attached bundle. If that ever
    // stops holding, the root-forgery teeth would be measuring the wrong thing.
    assert_eq!(
        (
            t0_leg.wide_old_root8().expect("wide"),
            t0_leg.wide_new_root8().expect("wide")
        ),
        leg_real_roots(0),
        "the production leg's wide rotated roots must not depend on the claimed commitment / bundle"
    );
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    let t1 = plain_custom_turn(balance, 1, bound);
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "custom turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE TEETH (over the PRODUCTION-populated fold).
// ============================================================================

/// POSITIVE POLE — an honest custom turn built through the PRODUCTION minter (claimed commitment ==
/// the genuine sub-proof commitment) folds and the LIGHT CLIENT ACCEPTS.
#[test]
#[ignore = "SLOW: real production-path custom-binding recursion fold (~minutes); run with --ignored"]
fn production_custom_turn_honest_accepts() {
    let bound = honest_bound();
    let real = bound.proof_commitment();
    let turns = build_chain(real);

    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest production custom-bearing chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk).expect(
        "the light client must ACCEPT the honest production custom-bound whole-chain artifact",
    );
    eprintln!(
        "PRODUCTION custom binding: honest custom turn FOLDED + light-client VERIFIED (commitment \
         bound in the recursion tree via the production minter)."
    );
}

/// THE TOOTH — a FORGED custom turn through the PRODUCTION minter: the leg claims a
/// `proof_commitment` no verifying sub-proof of the bundle's PIs backs. The segmented binding node's
/// in-circuit `connect` is a conflict ⇒ UNSAT ⇒ no root ⇒ the light client never receives a
/// verifying artifact (REJECTED). This is the PRODUCTION-path bite.
#[test]
#[ignore = "SLOW: real production-path custom-binding recursion fold (~minutes); run with --ignored"]
fn production_custom_turn_forged_rejected() {
    let bound = honest_bound();
    let real = bound.proof_commitment();
    let mut forged = real;
    forged[0] = BabyBear::new((real[0].0 + 1) % BABYBEAR_P);
    assert_ne!(forged, real);

    let turns = build_chain(forged);

    let err = must_refuse(
        "a FORGED proof_commitment folded into a verifying whole-chain artifact through the  PRODUCTION minter",
        || prove_turn_chain_recursive(&turns),
    );
    // ASSERT THE REASON, not merely that SOMETHING refused. Post-flip the deployed arm has a
    // FAIL-CLOSED PI-width check that fires BEFORE the fold: a tooth asserting only `Err` would
    // pass vacuously if this fixture ever drifted below the ABI width, testing nothing about the
    // forged commitment. `WitnessConflict` inside the binding node IS the forgery being caught.
    assert_refused_by_binding_node(&err, "state-binding custom-binding node failed");
    eprintln!(
        "PRODUCTION custom binding: forged custom commitment REJECTED by the production-populated \
         fold (no root)."
    );
}

/// **THE STATE TOOTH, THROUGH THE PRODUCTION MINTER.** The bound proof VERIFIES and the leg claims
/// ITS GENUINE commitment (so the commitment tooth passes and only the STATE tooth can bite), but
/// it declares an UNRELATED transition. The deployed state node's root `connect` is a conflict ⇒
/// UNSAT ⇒ no root ⇒ the light client never receives a verifying artifact.
///
/// This is the forgery the pre-flip production path ACCEPTED.
#[test]
#[ignore = "SLOW: real production-path custom-binding recursion fold (~minutes); run with --ignored"]
fn production_custom_turn_forged_root_rejected() {
    let (real_old8, real_new8) = leg_real_roots(0);
    let forged_old8: [BabyBear; 8] = core::array::from_fn(|k| BabyBear::new(900 + k as u32));
    let forged_new8: [BabyBear; 8] = core::array::from_fn(|k| BabyBear::new(950 + k as u32));
    assert_ne!(forged_old8, real_old8, "the forgery must be a real forgery");
    assert_ne!(forged_new8, real_new8, "the forgery must be a real forgery");

    // The bound proof is about a DIFFERENT transition; the leg claims its GENUINE commitment.
    let forged_bound = bound_over(custom_pis(&forged_old8, &forged_new8));
    let honest_commit_for_forged_pis = forged_bound.proof_commitment();

    let err = must_refuse(
        "a custom proof about a DIFFERENT transition folded into a verifying whole-chain artifact \
         through the PRODUCTION minter",
        || {
            prove_turn_chain_recursive(&build_chain_with(
                honest_commit_for_forged_pis,
                &forged_bound,
            ))
        },
    );
    // The refusal must be the STATE connect conflicting inside the binding node — NOT the PI-width
    // fail-closed check (the forged bundle is ABI-wide; only its declared roots are wrong).
    assert_refused_by_binding_node(&err, "state-binding custom-binding node failed");
    eprintln!(
        "PRODUCTION state binding: a forged-ROOT custom proof (verifying, honestly committed) \
         REJECTED by the production-populated state fold (no root)."
    );
}

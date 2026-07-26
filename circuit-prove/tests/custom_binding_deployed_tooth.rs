//! # THE DEPLOYED CUSTOM-BINDING LIGHT-CLIENT TOOTH.
//!
//! This is the integration tooth for the deployed custom-effect fold-wire (the close of the one
//! REAL deployed light-client vacuity). It builds a REAL 2-turn chain whose FIRST turn is an
//! `Effect::Custom` turn carrying a `customVmDescriptor2R24` wide leg (publishing its claimed
//! 8-felt `custom_proof_commitment` at IR2 PI 46..53 — the proof-bind flag-day rotation) PLUS the prover-side `CustomWitnessBundle` (the
//! re-provable `CellProgram` + trace witness + PIs), folds it through the DEPLOYED chain prover
//! (`prove_turn_chain_recursive` → `prove_chain_core_rotated`), and verifies the whole-chain
//! artifact through the light-client verifier (`verify_turn_chain_recursive`).
//!
//! The deployed wire mints, for the custom turn, a DUAL-EXPOSE leaf (segment ++ the claimed
//! commitment, `ivc_turn_chain::prove_descriptor_leaf_dual_expose`) and folds it against the
//! RE-PROVEN custom sub-proof leaf under a binding node. **Since the state-binding flip the
//! deployed pair is `custom_leaf_adapter::prove_custom_leaf_with_state_commitment` (the 24-lane
//! claim) under `joint_turn_recursive::prove_custom_binding_node_state_segmented`** — which welds
//! TWO things inside the recursion tree a pure light client folds:
//!
//!   1. the leg's CLAIMED commitment == the sub-proof's GENUINE in-circuit commitment, and
//!   2. the sub-proof's DECLARED `[old8 ‖ new8]` == the leg's REAL rotated roots.
//!
//! THE POLES:
//!   * HONEST — the sub-proof declares the leg's real roots and the leg claims the genuine
//!     commitment: the chain folds and the light client ACCEPTS.
//!   * FORGED COMMITMENT — the leg claims a commitment NO verifying sub-proof of the bundle's PIs
//!     backs: the commitment `connect` conflicts ⇒ UNSAT ⇒ no root ⇒ REJECTED.
//!   * FORGED ROOT (the flip's headline) — the sub-proof VERIFIES and its commitment is honest,
//!     but it is about a DIFFERENT transition: the state `connect` conflicts ⇒ UNSAT ⇒ REJECTED.
//!     Before the flip this folded and the light client accepted it; `canary__*` proves that by
//!     folding the same forgery through the pre-flip pair.
//!   * NON-ABI PROGRAM — a sub-program too narrow to express the prefix is refused fail-closed
//!     (the deployed executor already refused it; the prover now agrees).
//!
//! This makes the premise of Lean `CustomBindingFromFold.custom_binding_from_fold` TRUE on the
//! DEPLOYED path, and closes the `custom_state_binding` "tooth 2" remainder. The folds are real
//! recursions (minutes), so those poles are `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test custom_binding_deployed_tooth -- --ignored --nocapture

mod binding_tooth;
use binding_tooth::assert_refused_by_binding_node;

use std::collections::HashMap;

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::UMemBoundaryWitness;
use dregg_circuit::descriptor_ir2::prove_vm_descriptor2_for_config;
use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::effect_vm::custom_state_binding::{
    CUSTOM_PI_STATE_PREFIX_LEN, custom_pi_state_prefix,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::refusal::{must_accept, must_refuse};
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CustomWitnessBundle, DescriptorParticipant, RotatedParticipantLeg,
};
use dregg_turn::rotation_witness as rw;

// ============================================================================
// Fixtures
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

/// The actor cell at `(balance, nonce)` with open permissions.
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

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// The minimal-but-REAL custom program the custom-leaf adapter tests use: one boolean column
/// (`dir`) + one conservation polynomial (`new − old − amt + 2·dir·amt == 0`).
///
/// `public_input_count` is a PARAMETER because the deployed prover now REQUIRES the
/// `custom_state_binding` ABI: `state_binding_program()` (18 PIs = `[old8 ‖ new8 ‖ old_bal,
/// new_bal]`) is what a deployed custom carrier must publish; `narrow_demo_program()` (2 PIs) is
/// retained ONLY to drive the fail-closed refusal. The constraint shape is identical in both, so
/// the refusal is attributable to the PI width and nothing else.
fn demo_program_with_pi_count(public_input_count: usize) -> CellProgram {
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
        public_input_count,
        lookup_tables: vec![],
    };
    CellProgram::new(descriptor, 1)
}

/// **THE ABI-COMPLIANT PROGRAM** — publishes `[old8 ‖ new8 ‖ old_bal, new_bal]` (18 PIs), the
/// `custom_state_binding` prefix the deployed prover and the deployed executor both require.
fn state_binding_program() -> CellProgram {
    demo_program_with_pi_count(CUSTOM_PI_STATE_PREFIX_LEN + 2)
}

/// The pre-flip 2-PI program. NOT a state-binding program: it cannot express the prefix, so the
/// deployed prover refuses it fail-closed (as the deployed executor already did).
fn narrow_demo_program() -> CellProgram {
    demo_program_with_pi_count(2)
}

/// Honest witness for a credit (dir=0): new = old + amt, constant across rows.
fn honest_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
    let rows = 4;
    let mut w = HashMap::new();
    w.insert("old".into(), vec![BabyBear::new(10); rows]);
    w.insert("amt".into(), vec![BabyBear::new(5); rows]);
    w.insert("new".into(), vec![BabyBear::new(15); rows]);
    w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
    (w, rows)
}

/// The state-binding sub-proof's public inputs: `[old8 ‖ new8 ‖ 10, 15]`.
///
/// `old8`/`new8` are the leg's REAL wide rotated roots (its last 16 descriptor PIs) — the SAME
/// 8-felt v9 chip commit the deployed executor enforces this prefix against
/// (`enforce_custom_proof_state_binding` compares it to `bytes32_to_felt8(stored)` /
/// `bytes32_to_felt8(claimed)`, and the executor writes those into exactly these tail PIs).
fn state_pis(old8: &[BabyBear; 8], new8: &[BabyBear; 8]) -> Vec<BabyBear> {
    let mut pis = custom_pi_state_prefix(old8, new8).to_vec();
    pis.push(BabyBear::new(10));
    pis.push(BabyBear::new(15));
    pis
}

/// Mint a REAL `customVmDescriptor2R24` wide leg whose claimed 8-felt `custom_proof_commitment`
/// (IR2 PI 46..53 — limbs 0..4 from the param cols, limbs 4..8 from the commit teeth) is `commit`. Custom bumps nonce by 1, balance unchanged: `before=(b,nonce)`,
/// `after=(b,nonce+1)`. Optionally attach the prover-side `bundle` (the deployed custom-binding
/// thread the chain prover reads).
fn mint_custom_leg(
    balance: i64,
    nonce: u64,
    commit: [BabyBear; 8],
    bundle: Option<CustomWitnessBundle>,
) -> RotatedParticipantLeg {
    let st = CellState::new(balance as u64, nonce as u32);
    let effects = vec![Effect::Custom {
        program_vk_hash: [BabyBear::new(9); 8],
        proof_commitment: commit,
    }];
    let before_cell = producer_cell(balance, nonce);
    let after_cell = producer_cell(balance, nonce + 1);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = bridge(&rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));
    let after_w = bridge(&rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));

    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &before_w,
        &after_w,
        &empty_caveat_manifest(),
        None,
        None,
        None,
        None,
    )
    .expect("custom wide dispatch");
    assert!(
        dpis.len() >= 54,
        "custom leg PI vector must carry the 8-felt commitment slice at 46..53 (got {})",
        dpis.len()
    );
    // The leg PUBLISHES the claimed 8-felt commitment at PI 46..53 (== the effect's
    // proof_commitment — both squeeze blocks, the flag-day rotation).
    assert_eq!(
        &dpis[46..54],
        &commit[..],
        "custom leg must publish the claimed 8-felt commitment at PI 46..53"
    );

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &mb,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("custom wide leg proves under the leaf-wrap config");

    let leg = RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: None,
    };
    match bundle {
        Some(b) => leg.with_custom_witness(b),
        None => leg,
    }
}

/// A trailing custom turn starting at `(b, nonce)`, so the chain has >= 2 turns and the first
/// custom turn's `new_root` links to this one's `old_root`. GENUINELY BOUND — the same recipe as
/// turn 0, one nonce later.
///
/// ⚠ **THIS TURN USED TO BE UNBOUND, AND THAT WAS THE HOLE, NOT A HARMLESS FILLER.** It was
/// `mint_custom_leg(.., None)` claiming a fabricated `[1..8]` commitment: a custom-member leg
/// riding the fold's NO-CARRIER arm, publishing a prover-chosen `custom_proof_commitment` at PI
/// 46..53 that neither the deployed AIR (`Ir2Air::Main` has no `ProofBind` arm) nor any connect
/// constrained. The honest pole below therefore used to fold and light-client-VERIFY a chain that
/// contained exactly the forgery its sibling tooth forges — the difference being only which turn
/// carried it. The deployed prover now refuses that arm outright
/// (`require_no_unbacked_proof_bind`), so the honest pole must be honest all the way down.
///
/// The witness here is NOT a dummy handed over to make a red test green: it is a REAL sub-proof
/// over THIS turn's own rotated roots, whose GENUINE commitment the leg claims — turn 0's
/// construction at `nonce`, verbatim.
fn bound_trailing_custom_turn(balance: i64, nonce: u64) -> FinalizedTurn {
    // `leg_real_roots` probes at `CHAIN_BALANCE`; a different balance would give this turn a
    // sub-proof declaring some OTHER leg's roots and the state node would be UNSAT for the wrong
    // reason. Pin it rather than let the fixture drift into a false negative.
    assert_eq!(
        balance, CHAIN_BALANCE,
        "the root probe is fixed at CHAIN_BALANCE"
    );
    let (old8, new8) = leg_real_roots(nonce);
    let pis = state_pis(&old8, &new8);
    let commit = custom_proof_pi_commitment(&pis);
    let leg = mint_custom_leg(
        balance,
        nonce,
        commit,
        Some(bundle_of(state_binding_program(), pis)),
    );
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// A bundle over `program` proving `pis`.
fn bundle_of(program: CellProgram, pis: Vec<BabyBear>) -> CustomWitnessBundle {
    let (w, rows) = honest_witness();
    CustomWitnessBundle {
        program,
        witness_values: w,
        num_rows: rows,
        public_inputs: pis,
        app_root_binding: None,
        descriptor_state_leaf: None,
    }
}

const CHAIN_BALANCE: i64 = 1000i64;

/// The number of lanes a leaf/node exposes through its `expose_claim` table — read by op_type, the
/// SAME way `prove_custom_binding_node_state_segmented`'s fail-closed width check reads it (NOT via
/// `expose_claim_instance_index`, which is an index into the in-circuit `air_public_targets` and is
/// offset by the primitive-table count).
fn exposed_claim_lanes(
    out: &p3_recursion::RecursionOutput<
        dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig,
    >,
) -> usize {
    out.0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map(|e| e.public_values.len())
        .unwrap_or(0)
}

/// **THE LEG'S REAL ROTATED ROOTS.** Mint a probe leg and read its wide 8-felt anchors (the last
/// 16 descriptor PIs) — what the state fold connects the sub-proof's declared prefix to.
///
/// Two-phase is REQUIRED and SOUND: the sub-proof's PIs must carry the leg's roots, its commitment
/// hashes those PIs, and the leg publishes that commitment — so the roots must be read before the
/// real leg is minted. It is sound because the wide roots are computed from the rotation witness
/// (the cell's limbs + iroot) and do NOT depend on the claimed commitment. `honest_state_chain`
/// ASSERTS that independence rather than assuming it.
fn leg_real_roots(nonce: u64) -> ([BabyBear; 8], [BabyBear; 8]) {
    let probe = mint_custom_leg(CHAIN_BALANCE, nonce, [BabyBear::ZERO; 8], None);
    (
        probe
            .wide_old_root8()
            .expect("deployed custom leg is wide-anchored"),
        probe
            .wide_new_root8()
            .expect("deployed custom leg is wide-anchored"),
    )
}

/// Build the 2-turn chain from an EXPLICIT `(commit, bundle)`, so each tooth can forge exactly one
/// thing. Turn 1 is an HONESTLY BOUND trailing custom turn (see
/// [`bound_trailing_custom_turn`] — it used to be an unbacked one, which quietly put a forgery
/// inside the honest pole) linking off turn 0's post-state, so the ONLY thing a tooth forges is
/// what it passes in here.
fn build_chain_with(commit: [BabyBear; 8], bundle: CustomWitnessBundle) -> Vec<FinalizedTurn> {
    let t0_leg = mint_custom_leg(CHAIN_BALANCE, 0, commit, Some(bundle));
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    let t1 = bound_trailing_custom_turn(CHAIN_BALANCE, 1);
    // Continuity sanity (host check also enforces this; assert early for a clear failure).
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "custom turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

/// **THE HONEST STATE-BOUND CHAIN.** The sub-proof declares the leg's REAL roots, and the leg
/// claims the sub-proof's GENUINE commitment. Both teeth of the deployed state node are satisfied.
fn honest_state_chain() -> Vec<FinalizedTurn> {
    let (old8, new8) = leg_real_roots(0);
    let pis = state_pis(&old8, &new8);
    let commit = custom_proof_pi_commitment(&pis);
    let turns = build_chain_with(commit, bundle_of(state_binding_program(), pis));

    // THE TWO-PHASE SAFETY ASSERT: the real leg (minted with the genuine commitment) publishes the
    // SAME wide roots the probe leg did. If a claimed commitment ever fed back into the rotated
    // limbs, this fires — and every root-forgery tooth below would be measuring the wrong thing.
    let real_leg = &turns[0].participant.rotated;
    assert_eq!(
        (
            real_leg.wide_old_root8().expect("wide"),
            real_leg.wide_new_root8().expect("wide")
        ),
        (old8, new8),
        "the leg's wide rotated roots must NOT depend on the claimed commitment — the two-phase \
         fixture (probe the roots, then mint with the commitment over them) assumes exactly this"
    );
    turns
}

// ============================================================================
// THE TEETH
// ============================================================================

/// POSITIVE POLE — an honest custom turn (claimed commitment == the genuine sub-proof commitment)
/// folds through the DEPLOYED chain prover and the LIGHT CLIENT ACCEPTS. The custom binding is now
/// witnessed by a pure light client folding the recursion tree.
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn deployed_custom_turn_honest_accepts() {
    let turns = honest_state_chain();

    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest custom-bearing chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest custom-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED custom binding: honest custom turn FOLDED + light-client VERIFIED (commitment \
         bound in the recursion tree)."
    );
}

/// THE TOOTH — a FORGED custom turn: the leg claims a `custom_proof_commitment` no verifying
/// sub-proof of the bundle's PIs backs. The segmented binding node's in-circuit `connect` to the
/// genuine commitment is a conflict ⇒ the aggregate is UNSAT ⇒ no root. The light client never
/// receives a verifying artifact (REJECTED). This is the deployed bite that makes the binding REAL.
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn deployed_custom_turn_forged_rejected() {
    let (old8, new8) = leg_real_roots(0);
    let pis = state_pis(&old8, &new8);
    let real = custom_proof_pi_commitment(&pis);

    // ── S1 HONEST POLE FIRST, in THIS test. The forged chain below differs from this one by a
    //    SINGLE FELT, so without an accept here the refusal proves nothing: an arm that refuses
    //    every chain of this shape (a drifted descriptor, a mis-shaped bundle) would satisfy the
    //    assertion below exactly as well as a working binding does.
    must_accept("the HONEST custom-commitment chain", || {
        prove_turn_chain_recursive(&honest_state_chain())
    });

    // A claim NO verifying sub-proof of `pis` backs (lane 0 perturbed by +1 mod p). The bundle
    // still proves the HONEST PIs, so the genuine in-circuit commitment is `real` ≠ `forged` — the
    // binding `connect` conflicts.
    let mut forged = real;
    forged[0] = BabyBear::new((real[0].0 + 1) % BABYBEAR_P);
    assert_ne!(forged, real);

    let err = must_refuse(
        "a FORGED custom_proof_commitment folded into a verifying deployed whole-chain artifact",
        || {
            prove_turn_chain_recursive(&build_chain_with(
                forged,
                bundle_of(state_binding_program(), state_pis(&old8, &new8)),
            ))
        },
    );
    assert_refused_by_binding_node(&err, "state-binding custom-binding node failed");
    eprintln!(
        "DEPLOYED custom binding: forged custom commitment REJECTED by the deployed fold's \
         binding connect (WitnessConflict; honest pole accepted the same shape): {err:?}"
    );
}

/// **THE HEADLINE TOOTH OF THE FLIP — a forged-ROOT custom proof, refused through the DEPLOYED
/// prover entry.**
///
/// The sub-proof is about an entirely DIFFERENT transition (roots `900/950`, not the leg's real
/// rotated roots). It VERIFIES on its own, and the leg claims ITS GENUINE commitment — so the
/// commitment tooth PASSES and only the STATE tooth can bite. This is the exact forgery
/// `custom_state_binding`'s doc describes: "a custom AIR could prove a beautiful transition
/// `R1 -> R2` while the turn commits `S1 -> S2`, and every existing gate passed."
///
/// Before the flip this chain FOLDED and the light client ACCEPTED it (see the canary below).
/// Now the deployed prover's state `connect` is a conflict ⇒ UNSAT ⇒ no root ⇒ the light client
/// never receives a verifying artifact.
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn deployed_custom_turn_forged_root_rejected() {
    // S1 HONEST POLE FIRST — the forged chain differs only in the declared roots.
    must_accept("the HONEST state-bound chain", || {
        prove_turn_chain_recursive(&honest_state_chain())
    });

    let (real_old8, real_new8) = leg_real_roots(0);
    let forged_old8: [BabyBear; 8] = core::array::from_fn(|k| BabyBear::new(900 + k as u32));
    let forged_new8: [BabyBear; 8] = core::array::from_fn(|k| BabyBear::new(950 + k as u32));
    assert_ne!(forged_old8, real_old8, "the forgery must be a real forgery");
    assert_ne!(forged_new8, real_new8, "the forgery must be a real forgery");

    let forged_pis = state_pis(&forged_old8, &forged_new8);
    // The leg claims the sub-proof's GENUINE commitment: the commitment tooth is SATISFIED, so a
    // refusal here is attributable to the STATE connect alone.
    let honest_commit_for_forged_pis = custom_proof_pi_commitment(&forged_pis);

    let err = must_refuse(
        "a custom proof about a DIFFERENT transition folded into a verifying deployed whole-chain \
         artifact — the deployed path does not bind the sub-proof's declared roots",
        || {
            prove_turn_chain_recursive(&build_chain_with(
                honest_commit_for_forged_pis,
                bundle_of(state_binding_program(), forged_pis.clone()),
            ))
        },
    );
    assert_refused_by_binding_node(&err, "state-binding custom-binding node failed");
    eprintln!(
        "DEPLOYED state binding: a forged-ROOT custom proof (verifying, honestly committed) \
         REJECTED by the deployed fold's state connect (WitnessConflict): {err:?}"
    );
}

/// **THE CANARY — the state connects are load-bearing on the DEPLOYED path, shown without editing
/// code.**
///
/// The SAME forged-root inputs the deployed prover refuses above are ACCEPTED by the pre-flip
/// deployed pair (the commitment-only leaf + `prove_custom_binding_node_segmented`), assembled
/// here from the REAL deployed leg — not a stand-in. That is not a bug in the old node; it is
/// precisely its documented reach ("binds WHICH public inputs the sub-proof used ... does NOT bind
/// what those public inputs SAY"). Running both over one forgery measures exactly what the flip
/// bought: revert the deployed mint to the commitment-only node and this forgery folds cleanly.
///
/// (The in-lib `custom_state_fold_wire_tests::canary__*` makes the same measurement over a
/// stand-in leg. This one makes it through the REAL `customVmDescriptor2R24` wide leg, so it also
/// witnesses that the deployed leg's segment anchors are what the connects reach.)
#[test]
#[ignore = "SLOW: folds the same forgery through two deployed-shape node pairs; run with --ignored"]
fn canary__the_pre_flip_deployed_pair_accepts_the_forged_root_the_state_node_refuses() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, prove_custom_leaf_with_state_commitment,
    };
    use dregg_circuit_prove::ivc_turn_chain::prove_descriptor_leaf_dual_expose;
    use dregg_circuit_prove::joint_turn_recursive::{
        prove_custom_binding_node_segmented, prove_custom_binding_node_state_segmented,
    };

    let config = ir2_leaf_wrap_config();
    let (real_old8, real_new8) = leg_real_roots(0);
    let forged_old8: [BabyBear; 8] = core::array::from_fn(|k| BabyBear::new(900 + k as u32));
    let forged_new8: [BabyBear; 8] = core::array::from_fn(|k| BabyBear::new(950 + k as u32));
    let forged_pis = state_pis(&forged_old8, &forged_new8);
    let commit = custom_proof_pi_commitment(&forged_pis);

    // The REAL deployed leg, claiming the forged sub-proof's genuine commitment.
    let leg = mint_custom_leg(CHAIN_BALANCE, 0, commit, None);
    assert_eq!(
        (
            leg.wide_old_root8().expect("wide"),
            leg.wide_new_root8().expect("wide")
        ),
        (real_old8, real_new8),
        "the leg under test must carry the REAL roots the sub-proof is lying about"
    );
    let dual =
        prove_descriptor_leaf_dual_expose(&leg.descriptor, &leg.proof, &leg.public_inputs, &config)
            .expect("the deployed dual-expose leg leaf mints");

    let (w, rows) = honest_witness();
    let program = state_binding_program();

    // THE CANARY: the PRE-FLIP deployed pair (8-lane leaf + commitment-only node) => the
    // forged-root proof FOLDS.
    let thin_leaf = prove_custom_leaf_with_commitment(&program, &w, rows, &forged_pis, &config)
        .expect("the commitment-only leaf proves");
    prove_custom_binding_node_segmented(&dual, &thin_leaf, &config).expect(
        "CANARY BROKEN: the pre-flip deployed pair was expected to ACCEPT this forged-root proof \
         (that acceptance is the gap the flip closes). If this now refuses, the forged-root tooth \
         is passing for some OTHER reason and no longer measures the state connects.",
    );

    // THE FLIP: the deployed pair (24-lane leaf + state node) => the same forgery is UNSAT.
    let state_leaf =
        prove_custom_leaf_with_state_commitment(&program, &w, rows, &forged_pis, &config).expect(
            "the state-binding leaf proves — the forged-root sub-proof still PROVES, that is \
                 the whole problem",
        );
    must_refuse(
        "the DEPLOYED state node accepted a forged-root proof the canary proves is forgeable",
        || prove_custom_binding_node_state_segmented(&dual, &state_leaf, &config),
    );
    eprintln!(
        "DEPLOYED CANARY: the pre-flip pair ACCEPTS the forged-root fold; the deployed state pair \
         REFUSES it. The 16 state connects are load-bearing on the real leg."
    );
}

/// **THE BUDGET OF THE FLIP.** What the state weld costs, measured on HONEST inputs where BOTH
/// pairs accept (an UNSAT fold is not a fair cost comparison — it fails early).
///
/// Reports, for the same real deployed leg + the same sub-proof:
///   * the pre-flip pair: 8-lane leaf  + commitment-only node (8 connects)
///   * the deployed pair: 24-lane leaf + state node           (24 connects)
/// with exposed claim-lane counts and wall-clock per stage. The node's PARENT shape is identical in
/// both (it re-exposes only the `SEG_WIDTH` segment) — ASSERTED below — so any delta is the leaf's
/// 16 extra exposed lanes + the node's 16 extra connects, NOT a change to what folds onward.
///
/// ⚠ ONE SAMPLE, COLD. The stage timings are a single un-warmed run in the same process, so the
/// FIRST pair pays cache/codegen costs the second does not: a measured "the 24-lane leaf proves
/// faster than the 8-lane leaf" is warmup noise, not a speedup. Trust the LANE COUNTS (exact) and
/// the node-fold order of magnitude; re-run with warm repeats before quoting a leaf number.
#[test]
#[ignore = "SLOW: mints both node pairs on honest inputs to measure the delta; run with --ignored"]
fn budget__the_state_weld_costs_this_much() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, prove_custom_leaf_with_state_commitment,
    };
    use dregg_circuit_prove::ivc_turn_chain::prove_descriptor_leaf_dual_expose;
    use dregg_circuit_prove::joint_turn_recursive::{
        prove_custom_binding_node_segmented, prove_custom_binding_node_state_segmented,
    };
    use std::time::Instant;

    let config = ir2_leaf_wrap_config();
    let (old8, new8) = leg_real_roots(0);
    let pis = state_pis(&old8, &new8);
    let commit = custom_proof_pi_commitment(&pis);
    let leg = mint_custom_leg(CHAIN_BALANCE, 0, commit, None);
    let dual =
        prove_descriptor_leaf_dual_expose(&leg.descriptor, &leg.proof, &leg.public_inputs, &config)
            .expect("dual-expose leg leaf mints");
    let (w, rows) = honest_witness();
    let program = state_binding_program();

    let t = Instant::now();
    let thin = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        .expect("8-lane leaf proves");
    let thin_leaf_ms = t.elapsed().as_millis();
    let t = Instant::now();
    let thin_node = prove_custom_binding_node_segmented(&dual, &thin, &config)
        .expect("commitment-only node folds the honest pair");
    let thin_node_ms = t.elapsed().as_millis();

    let t = Instant::now();
    let wide = prove_custom_leaf_with_state_commitment(&program, &w, rows, &pis, &config)
        .expect("24-lane leaf proves");
    let wide_leaf_ms = t.elapsed().as_millis();
    let t = Instant::now();
    let wide_node = prove_custom_binding_node_state_segmented(&dual, &wide, &config)
        .expect("the state node folds the HONEST pair — the honest pole of the budget");
    let wide_node_ms = t.elapsed().as_millis();

    eprintln!(
        "\n=== BUDGET OF THE STATE WELD (honest inputs; both pairs accept) ===\n\
         leaf claim lanes : {} -> {}  (+{})\n\
         node connects    : {} -> {}  (+{})\n\
         leaf prove  (ms) : {thin_leaf_ms} -> {wide_leaf_ms}\n\
         node fold   (ms) : {thin_node_ms} -> {wide_node_ms}\n\
         total       (ms) : {} -> {}\n\
         parent claim lanes (what folds onward): {} -> {}  (MUST be equal — the node re-exposes \
         only the segment)\n",
        exposed_claim_lanes(&thin),
        exposed_claim_lanes(&wide),
        exposed_claim_lanes(&wide).saturating_sub(exposed_claim_lanes(&thin)),
        8,
        24,
        16,
        thin_leaf_ms + thin_node_ms,
        wide_leaf_ms + wide_node_ms,
        exposed_claim_lanes(&thin_node),
        exposed_claim_lanes(&wide_node),
    );
    assert_eq!(
        exposed_claim_lanes(&thin_node),
        exposed_claim_lanes(&wide_node),
        "the state node must fold onward with the IDENTICAL parent shape as the commitment-only \
         node — if this differs, the flip changed what `aggregate_tree` consumes, not just what the \
         node checks"
    );
}

/// **THE FLIP'S FAIL-CLOSED CONSEQUENCE, made explicit.** A custom carrier whose sub-program
/// cannot express the ABI prefix (the pre-flip 2-PI demo) is REFUSED by the deployed prover — it
/// is never zero-padded into a false prefix, and never silently degraded to a commitment-only
/// connect that would LOOK state-bound and not be.
///
/// This is not new reach. The deployed EXECUTOR already refuses such a turn at
/// `enforce_custom_proof_state_binding` (`PublicInputsTooShort`), so the pre-flip prover was
/// minting chains no executor would ever accept. The flip makes the prover agree with the
/// verifier — the refusal moves EARLIER, it does not appear from nowhere.
///
/// FAST: the refusal fires at the sub-proof leaf mint, before any fold.
#[test]
fn deployed_custom_turn_with_a_non_abi_program_is_refused() {
    let err = must_refuse(
        "a 2-PI sub-program (too narrow for the state-binding prefix) folded through the deployed \
         prover",
        || {
            prove_turn_chain_recursive(&build_chain_with(
                custom_proof_pi_commitment(&[BabyBear::new(10), BabyBear::new(15)]),
                bundle_of(
                    narrow_demo_program(),
                    vec![BabyBear::new(10), BabyBear::new(15)],
                ),
            ))
        },
    );
    let TurnChainError::TurnProofInvalid { index, reason } = &err else {
        panic!("expected a TurnProofInvalid refusal from the deployed custom arm, got: {err:?}")
    };
    assert_eq!(*index, 0, "the custom carrier is turn 0");
    assert!(
        reason.contains("custom state-binding sub-proof leaf mint failed")
            && reason.contains("state-binding ABI requires at least"),
        "the refusal must be the state-binding leaf's FAIL-CLOSED width check, not some other \
         failure that would leave the ABI requirement untested.\n  got: {reason}"
    );
    eprintln!("DEPLOYED state binding: a non-ABI (2-PI) custom carrier is REFUSED: {reason}");
}

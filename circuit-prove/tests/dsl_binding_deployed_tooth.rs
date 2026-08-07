//! # THE DEPLOYED DSL/Dfa-BINDING LIGHT-CLIENT TOOTH (the dsl twin of
//! `custom_binding_deployed_tooth.rs` — the 6th carrier goes live).
//!
//! Builds a REAL 2-turn chain whose FIRST turn is a `Witnessed{Dfa}`-GATED `Transfer` turn
//! carrying the deployed wide transfer leg — the 4-felt DFA route-commitment
//! (`dfa_route_commitment(DfaProofWire.public_inputs)`) PUBLISHED at the rc claim PIs the
//! cohort-wide `withDfaRcPins` emit pinned (transfer: 46..49, DERIVED per member by
//! `ivc_turn_chain::dsl_rc_claim_pi_lo` from the committed registry row) — PLUS the
//! prover-side `DslWitnessBundle` (the re-provable predicate-transition `CellProgram` + trace
//! witness + the wire PIs), folds it through the DEPLOYED chain prover's Dsl arm, and
//! verifies through the light-client verifier.
//!
//! The Dfa predicate is a PRECONDITION CAVEAT (no op on the deployed turn at all —
//! `DslBackingAttack.deployed_admits_unwitnessed`), so the ONLY light-client witnessing is
//! this fold: the arm mints the DUAL-EXPOSE leg leaf (segment ++ the published rc), re-proves
//! the predicate transition as a DSL leaf exposing its PI-commitment IN-CIRCUIT
//! (`dsl_leaf_adapter::prove_dsl_leaf_with_commitment`, custom-machinery reuse), and
//! `connect`s the two under the segment-preserving binding node
//! (`prove_dsl_binding_node_segmented`).
//!
//! THE POLES:
//!   * HONEST — the leg's published rc EQUALS `custom_proof_pi_commitment(bundle.pis)`
//!     (which IS `dfa_route_commitment` — pinned by
//!     `dsl_rc_emit::dfa_route_commitment_is_the_custom_proof_pi_commitment`): the chain
//!     folds and the light client ACCEPTS. The chain's SECOND turn is a plain no-Dfa
//!     transfer (zero rc sentinel, `carrier_witness: None`) — the sanctioned re-exec rung
//!     proving alongside, so the sentinel never blocks the fleet.
//!   * FORGED — the leg publishes an rc NO verifying DSL sub-proof of the bundle's PIs
//!     backs: the in-circuit `connect` is a conflict ⇒ UNSAT ⇒ no root ⇒ REJECTED.
//!   * ZERO SENTINEL — a Dsl witness attached to a NO-Dfa leg (rc = 0, the absent sentinel)
//!     is REFUSED by the arm before any fold: a vacuous claim is never folded.
//!
//! This makes the premise of Lean `DslBindingFromFold.dsl_binding_from_fold` TRUE on the
//! deployed path. The folds are real recursion (minutes), so those poles are `#[ignore]`:
//!   cargo test -p dregg-circuit-prove --test dsl_binding_deployed_tooth -- --ignored --nocapture

mod binding_tooth;
use binding_tooth::assert_refused_by_binding_node;

use std::collections::HashMap;

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, UMemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::effect_vm::trace_rotated::{
    DFA_RC_LEN, RotatedBlockWitness, RotatedCaveatManifest, dfa_route_commitment,
    generate_rotated_effect_vm_descriptor_and_trace_wide, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{must_accept, must_refuse};
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, dsl_rc_claim_pi_lo, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DescriptorParticipant, DslWitnessBundle, RotatedParticipantLeg,
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

/// A genuine ALGEBRAIC DFA transition predicate (the `dsl_leaf_adapter` fixture): a toy
/// "advance" DFA — `next == state + symbol` per row, cross-row continuity
/// `next_row.state == this.next`, boolean symbol. Exercises `Polynomial` + `Transition` +
/// `Binary` — the mapped algebraic DSL fragment that reuses the custom leaf machinery
/// directly.
fn dfa_advance_program() -> CellProgram {
    let p_minus_1 = BabyBear::new(dregg_circuit::field::BABYBEAR_P - 1);
    let descriptor = CircuitDescriptor {
        name: "dregg-dfa-advance-algebraic-v1".to_string(),
        trace_width: 3,
        max_degree: 2,
        columns: vec![
            ColumnDef {
                name: "state".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "symbol".into(),
                index: 1,
                kind: ColumnKind::Binary,
            },
            ColumnDef {
                name: "next".into(),
                index: 2,
                kind: ColumnKind::Value,
            },
        ],
        constraints: vec![
            ConstraintExpr::Binary { col: 1 },
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
                ],
            },
            ConstraintExpr::Transition {
                next_col: 0,
                local_col: 2,
            },
        ],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };
    CellProgram::new(descriptor, 1)
}

/// Honest run over symbols [1,0,1,0] from state 0: state [0,1,1,2], next [1,1,2,2].
fn honest_dfa_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
    let rows = 4;
    let mut w = HashMap::new();
    w.insert(
        "state".into(),
        vec![
            BabyBear::new(0),
            BabyBear::new(1),
            BabyBear::new(1),
            BabyBear::new(2),
        ],
    );
    w.insert(
        "symbol".into(),
        vec![
            BabyBear::new(1),
            BabyBear::new(0),
            BabyBear::new(1),
            BabyBear::new(0),
        ],
    );
    w.insert(
        "next".into(),
        vec![
            BabyBear::new(1),
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(2),
        ],
    );
    (w, rows)
}

/// The `DfaProofWire.public_inputs` of the honest run: `[initial_state=0, final_state=2]`.
fn dfa_wire_pis() -> Vec<BabyBear> {
    vec![BabyBear::new(0), BabyBear::new(2)]
}

fn honest_bundle() -> DslWitnessBundle {
    let (w, rows) = honest_dfa_witness();
    DslWitnessBundle {
        program: dfa_advance_program(),
        witness_values: w,
        num_rows: rows,
        public_inputs: dfa_wire_pis(),
    }
}

fn deployed_wide_descriptor(wire: &str) -> EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(wire) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{wire} not in WIDE_REGISTRY_STAGED_TSV"));
    parse_vm_descriptor2(json).expect("deployed wide descriptor parses")
}

/// Mint the Dfa-carrying wide `Transfer` leg on the NATIVE committed transfer row
/// (`transferV3MembershipWide`), the published rc coming from `caveat.dfa_rc` (the rotated
/// generator fills the carrier columns AND pushes the rc PIs from the manifest — the emit
/// contract `dsl_rc_emit.rs` pins). The membership teeth columns/PIs the native row also
/// carries are filled with inert constants (no membership witness attached — one carrier
/// lane per leg).
fn mint_dfa_leg(
    before_balance: i64,
    amount: u64,
    nonce: u64,
    caveat: &RotatedCaveatManifest,
    witness: Option<CarrierWitness>,
) -> RotatedParticipantLeg {
    let st = CellState::new(before_balance as u64, nonce as u32);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(before_balance, nonce);
    let after_cell = producer_cell(before_balance - amount as i64, nonce);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    // Mint through the PRODUCTION WIDE DISPATCHER, never a hand-rolled twin. The deployed
    // `transferVmDescriptor2R24` is the AVAILABILITY-HARDENED member
    // (`dregg-effectvm-transfer-v1-avail-…`, pad 10): its 15-bit weld-witness limbs ride
    // `[V1_WIDTH, V1_WIDTH + pad)` — wire 188 is `BEF0`, the low 15-bit limb of `before.bal_lo` —
    // and EVERY rotated appendix base shifts up by the pad. The dispatcher derives that pad from
    // the descriptor name (`avail_pad_for_descriptor_name`), resolves the committed row from
    // `WIDE_REGISTRY_STAGED_TSV`, lays the membership teeth at the member's OWN teeth column, and
    // splices their claim PIs. Rebuilding that geometry here is what broke this leg: the bare
    // pad-0 producer laid a ~31-bit rotated-appendix felt at wire 188 and the descriptor's 15-bit
    // range refused it in prover pre-flight ("range wire 188 value 1230416006 >= 2^15"), and the
    // hand-rolled teeth column assumed a fixed 48-column refuse aux where the deployed transfer
    // row widens by 45 (`refuse_weld_widen` is PER-MEMBER, read off the committed gates).
    // The membership teeth are inert constants — this leg exercises the DSL lane only.
    let teeth = (BabyBear::new(0x5E4D), BabyBear::new(0xA07));
    let (twin, trace, twin_dpis, map_heaps, mb) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            caveat,
            None,
            None,
            None,
            Some(teeth),
        )
        .expect("deployed transfer wide dispatch (avail-hardened, teeth-carrying)");
    assert_eq!(
        twin.name,
        "dregg-effectvm-transfer-v1-avail-rot24-v3-staged-gentian-deployed-bare-refuse"
    );
    assert_eq!(twin_dpis.len(), twin.public_input_count);

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &twin,
        &trace,
        &twin_dpis,
        &mb,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the Dfa-carrying transfer wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: twin,
        public_inputs: twin_dpis,
        carrier_witness: witness,
    }
}

/// The transfer caveat manifest with `dfa_rc` = `rc` (a Dfa-gated turn's manifest).
fn dfa_manifest(rc: [BabyBear; DFA_RC_LEN]) -> RotatedCaveatManifest {
    let mut caveat = transfer_caveat_manifest();
    caveat.dfa_rc = rc;
    caveat
}

/// Build the 2-turn chain: turn 0 = the Dfa-gated transfer publishing `leg_rc` and carrying
/// the honest `DslWitnessBundle`; turn 1 = a PLAIN no-Dfa transfer (zero rc sentinel,
/// `carrier_witness: None` — the re-exec rung riding the same chain) linking off turn 0's
/// post-state.
fn build_chain(leg_rc: [BabyBear; DFA_RC_LEN]) -> Vec<FinalizedTurn> {
    let t0_leg = mint_dfa_leg(
        1000,
        7,
        0,
        &dfa_manifest(leg_rc),
        Some(CarrierWitness::Dsl(honest_bundle())),
    );
    // The published rc PIs are the manifest's carrier values (the emit contract).
    let rc_lo = dsl_rc_claim_pi_lo(&t0_leg.descriptor).expect("native row carries the rc pins");
    assert_eq!(
        &t0_leg.public_inputs[rc_lo..rc_lo + DFA_RC_LEN],
        &leg_rc[..],
        "the Dfa-gated leg publishes the manifest rc at its derived claim slots"
    );
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    // The rotated generator TICKS the AFTER-block nonce on a transfer turn, so t1's BEFORE
    // state carries nonce 1 for the 8-felt anchors to chain lane-by-lane.
    let t1_leg = mint_dfa_leg(993, 7, 1, &transfer_caveat_manifest(), None);
    let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(t1_leg));
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "transfer turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE TEETH
// ============================================================================

/// FAST (no recursion) — the rc slot DERIVATION is registry-grounded: on the committed wide
/// rows the `withDfaRcPins` pins sit at per-member PI indices, and `dsl_rc_claim_pi_lo` reads
/// them off the descriptor. Transfer (post-membership-exposure): rc at 46..49 (teeth 50..51,
/// anchors 52..67, 68 PIs). Sovereign (post-KEY_COMMIT-exposure): rc at 54..57 (teeth 58..61,
/// anchors 62..77, 78 PIs).
#[test]
fn rc_slot_derivation_is_registry_grounded() {
    let transfer = deployed_wide_descriptor("transferVmDescriptor2R24");
    assert_eq!(
        dsl_rc_claim_pi_lo(&transfer).expect("transfer row carries the rc pins"),
        46,
        "wide transfer publishes rc at PI 46..49"
    );
    assert_eq!(transfer.public_input_count, 68);

    let sovereign = deployed_wide_descriptor("makeSovereignVmDescriptor2R24");
    assert_eq!(
        dsl_rc_claim_pi_lo(&sovereign).expect("sovereign row carries the rc pins"),
        54,
        "wide makeSovereign publishes rc at PI 54..57 (record-pin8 first, teeth after)"
    );
    assert_eq!(sovereign.public_input_count, 78);
}

/// POSITIVE POLE — an honest Dfa-gated transfer (published rc ==
/// `custom_proof_pi_commitment(wire pis)` == `dfa_route_commitment(wire pis)`) folds through
/// the DEPLOYED chain prover's Dsl arm and the LIGHT CLIENT ACCEPTS; the chain's second turn
/// is the no-Dfa zero-sentinel re-exec rung, proving alongside.
#[test]
#[ignore = "SLOW: real deployed dsl-binding recursion fold (~minutes); run with --ignored"]
fn deployed_dfa_turn_honest_accepts() {
    let rc = dfa_route_commitment(&dfa_wire_pis());
    // The proof-bind flag day widened `custom_proof_pi_commitment` to the full 8-felt squeeze;
    // the deployed 4-felt rc carrier stays byte-identical to its FIRST squeeze block (the
    // connect's two sides: the leg's 4 rc lanes vs the sub-proof leaf's commitment lanes 0..4).
    assert_eq!(
        rc[..],
        custom_proof_pi_commitment(&dfa_wire_pis())[..4],
        "the rc derivation is the first squeeze block of the custom proof-bind commitment"
    );
    let turns = build_chain(rc);

    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest Dfa-gated chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest dsl-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED dsl binding: honest Dfa-gated transfer FOLDED + light-client VERIFIED \
         (route-commitment bound in the recursion tree; the no-Dfa zero-sentinel turn rode \
         the re-exec rung alongside)."
    );
}

/// THE TOOTH — a FORGED rc: the leg publishes a route-commitment NO verifying DSL sub-proof
/// of the bundle's wire PIs backs (lane 0 perturbed). The binding `connect` conflicts ⇒
/// UNSAT ⇒ no root ⇒ REJECTED.
#[test]
#[ignore = "SLOW: real deployed dsl-binding recursion fold (~minutes); run with --ignored"]
fn deployed_dfa_turn_forged_rc_rejected() {
    let real = dfa_route_commitment(&dfa_wire_pis());

    // ── S1 HONEST POLE FIRST, in THIS test. The forged chain below differs from this one by a
    //    SINGLE FELT, so without an accept here the refusal proves nothing: an arm that refuses
    //    every chain of this shape would satisfy the assertion below just as well.
    must_accept("the HONEST Dfa-gated route-commitment chain", || {
        prove_turn_chain_recursive(&build_chain(real))
    });

    let mut forged = real;
    forged[0] += BabyBear::ONE;
    assert_ne!(forged, real);
    let turns = build_chain(forged);

    let err = must_refuse(
        "a FORGED route-commitment (no verifying DSL sub-proof backs it) folded into a  verifying deployed whole-chain artifact",
        || prove_turn_chain_recursive(&turns),
    );
    assert_refused_by_binding_node(&err, "segmented dsl-binding node failed");
    eprintln!(
        "DEPLOYED dsl binding: forged route-commitment REJECTED by the deployed fold's binding \
         connect (WitnessConflict; honest pole accepted the same shape): {err:?}"
    );
}

/// THE ZERO-SENTINEL POLE — a Dsl witness attached to a NO-Dfa leg (published rc = the zero
/// sentinel) is REFUSED by the arm (fail-closed): a vacuous claim is never folded. The
/// sanctioned path for such a turn is `carrier_witness: None` (exercised by the honest
/// pole's second turn).
#[test]
#[ignore = "SLOW: mints two real wide legs (~minutes); run with --ignored"]
fn deployed_dfa_zero_sentinel_witness_refused() {
    let t0_leg = mint_dfa_leg(
        1000,
        7,
        0,
        &transfer_caveat_manifest(), // NO Dfa caveat: rc = the zero sentinel
        Some(CarrierWitness::Dsl(honest_bundle())),
    );
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    let t1_leg = mint_dfa_leg(993, 7, 1, &transfer_caveat_manifest(), None);
    let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(t1_leg));
    let turns = vec![t0, t1];

    let err = match prove_turn_chain_recursive(&turns) {
        Err(e) => e,
        Ok(_) => panic!("a Dsl witness against the zero rc sentinel must be REFUSED"),
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains("ZERO sentinel"),
        "the refusal names the zero sentinel (got: {msg})"
    );
    eprintln!("DEPLOYED dsl binding: Dsl witness on a no-Dfa (zero-sentinel) leg REFUSED: {msg}");
}

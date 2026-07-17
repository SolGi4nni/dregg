//! **THE 11×11 MILESTONE** — the REAL deployed-size two-player automatafl turn, proven
//! end-to-end. The stock two-player opening (`reference::stock_two_player`), a real legal
//! m=2 turn on it, the C.5 fold-leg split (Leg R `old→mid`, Leg A `mid→new`), the K=2
//! two-sub-turn fold + light-client `verify_history` ACCEPT, and the mid-seam soundness
//! probe (mismatched-mid).
//!
//! FAST tests (run in CI): the n=11 width census, the differential vs the reference oracle,
//! and the STRUCTURAL seam gap (the mismatched-mid is not caught by the cell-continuity
//! tooth — a PI-level demonstration, no proving).
//!
//! SLOW tests are `#[ignore]` (a real n=11 custom-leaf prove is minutes+, the fold tens of
//! minutes). Run on the build box:
//!   cargo test -p dregg-automatafl --test prove_11x11 -- --ignored --nocapture
//!
//! The turn (both seats move an attractor):
//!   Seat 0:  ATT (7,1) → (7,5)   — lands two east of the automaton at (5,5), an
//!                                   UnbalancedPair (ATT east dist 2, REP west dist 4).
//!   Seat 1:  ATT (0,4) → (0,2)   — an independent survivor on the far left column.
//! Resolution places the ATT at (7,5); the automaton is then PULLED east into (6,5).

use dregg_automatafl::reference::{
    Board, GOAL_CORNERS_2P, Move, apply_turn, automaton_step, resolve_mid, stock_two_player,
    win_owner,
};
use dregg_automatafl::{
    Builder, build_a_honest, build_a_honest_bound, build_r_honest, build_r_honest_bound,
};
use dregg_circuit::dsl::circuit::MAX_TRACE_WIDTH;
use dregg_circuit::field::BabyBear;

/// The real legal two-player turn on the stock 11×11 opening (see module docs).
fn turn() -> (Board, Move, Move) {
    let old = stock_two_player();
    let a = Move {
        who: 0,
        frm: (7, 1),
        to: (7, 5),
    };
    let b = Move {
        who: 1,
        frm: (0, 4),
        to: (0, 2),
    };
    (old, a, b)
}

// ============================================================================
// FAST — the n=11 differential vs the reference oracle, and the width census.
// (No proving; runs in CI.)
// ============================================================================

/// The chosen turn is genuinely legal, m=2, on the real stock board, and its composed
/// legs equal `apply_turn`. Pins the concrete resolution + automaton move + win verdict.
#[test]
fn honest_11x11_turn_matches_oracle() {
    let (old, a, b) = turn();
    assert_eq!(old.n, 11, "the real deployed board edge");
    assert_eq!(old.auto, (5, 5), "the stock automaton sits dead centre");

    // resolve_mid: both attractors journey to their destinations.
    let mid = resolve_mid(&old, &[a, b]);
    assert_eq!(
        mid.cell_at((7, 5)),
        2,
        "seat 0's ATT lands two east of the auto"
    );
    assert_eq!(mid.cell_at((7, 1)), 0, "seat 0's source cleared");
    assert_eq!(
        mid.cell_at((0, 2)),
        2,
        "seat 1's ATT lands on the left column"
    );
    assert_eq!(mid.cell_at((0, 4)), 0, "seat 1's source cleared");
    assert_eq!(mid.auto, (5, 5), "resolve_mid does not move the automaton");

    // Leg A: the automaton is pulled east into (6,5) by the fresh unbalanced pair.
    let new = automaton_step(&mid);
    assert_eq!(
        new.auto,
        (6, 5),
        "the automaton steps east onto the vacuum (6,5)"
    );
    assert_eq!(new.cell_at((6, 5)), 3, "AUTO now at (6,5)");
    assert_eq!(
        new.cell_at((5, 5)),
        0,
        "the automaton's old square is vacuum"
    );

    // The composed legs equal the whole-turn oracle.
    assert_eq!(
        new,
        apply_turn(&old, &[a, b]),
        "automaton_step ∘ resolve_mid == apply_turn on the real 11×11 turn"
    );

    // Win verdict: (6,5) is not a goal corner — no winner this turn.
    assert_eq!(
        win_owner(&new, &GOAL_CORNERS_2P),
        None,
        "the automaton is not in a goal corner"
    );

    // Both legs' honest witnesses SELF-ACCEPT (the AIR re-checks the oracle in-circuit).
    assert!(
        build_r_honest(&old, &a, &b).air_accepts(),
        "Leg R (old→mid) honest witness must self-accept at n=11"
    );
    assert!(
        build_a_honest(&mid).air_accepts(),
        "Leg A (mid→new) honest witness must self-accept at n=11"
    );
}

/// A FORGED move (illegal: from == to) has no satisfying Leg R — the validity gates reject it.
#[test]
fn forged_illegal_move_self_rejects_11x11() {
    let (old, _a, b) = turn();
    let illegal = Move {
        who: 0,
        frm: (7, 1),
        to: (7, 1), // from == to — not a move
    };
    // Drive the honest witness for the filtered resolution but hand Leg R the illegal move.
    let mid = resolve_mid(&old, &[illegal, b]);
    let prog = dregg_automatafl::build_r(&old, &illegal, &b, &mid);
    assert!(
        !prog.air_accepts(),
        "an illegal (from==to) move must have no satisfying Leg R leaf at n=11"
    );
}

/// A FORGED resolution (wrong mid) has no satisfying Leg R — the per-cell rewrite rejects it.
#[test]
fn forged_mid_self_rejects_11x11() {
    let (old, a, b) = turn();
    let honest_mid = resolve_mid(&old, &[a, b]);
    let mut forged = honest_mid.clone();
    // Flip a non-auto cell.
    forged.cells[0] = if forged.cells[0] == 0 { 2 } else { 0 };
    assert_ne!(forged, honest_mid, "the forged mid must differ");
    let prog = dregg_automatafl::build_r(&old, &a, &b, &forged);
    assert!(
        !prog.air_accepts(),
        "a forged mid must have no satisfying Leg R leaf at n=11"
    );
}

/// The n=11 width census. BOTH legs FIT under `MAX_TRACE_WIDTH = 1024` (hard gates, provable).
/// Leg A was formerly width-blocked (~1121 cols); the prefix-sum in-bounds reduction in the ray
/// scan (deriving each step's in-bounds bit as a prefix sum of the proven auto one-hot instead of
/// an independent per-step range gadget) drops the 5 range bits/step and lands Leg A at 901 cols,
/// so the real 11×11 automaton leaf now proves and the fold + light-client tests below are live.
#[test]
fn legs_width_census_11x11() {
    let (old, a, b) = turn();
    let mid = resolve_mid(&old, &[a, b]);
    let dr = build_r_honest(&old, &a, &b).descriptor();
    let da = build_a_honest(&mid).descriptor();
    eprintln!(
        "LEG R n=11: width={} constraints={} max_degree={} pis={}  [{}]",
        dr.trace_width,
        dr.constraints.len(),
        dr.max_degree,
        dr.public_input_count,
        if dr.trace_width <= MAX_TRACE_WIDTH {
            "FITS"
        } else {
            "EXCEEDS"
        },
    );
    eprintln!(
        "LEG A n=11: width={} constraints={} max_degree={} pis={}  [{}]",
        da.trace_width,
        da.constraints.len(),
        da.max_degree,
        da.public_input_count,
        if da.trace_width <= MAX_TRACE_WIDTH {
            "FITS"
        } else {
            "EXCEEDS"
        },
    );
    // Leg R is provable at n=11 (hard gate).
    assert!(
        dr.trace_width <= MAX_TRACE_WIDTH,
        "Leg R n=11 width {} exceeds {}",
        dr.trace_width,
        MAX_TRACE_WIDTH
    );
    assert!(
        dr.max_degree <= 8,
        "Leg R degree {} exceeds cap 8",
        dr.max_degree
    );
    assert!(
        da.max_degree <= 8,
        "Leg A degree {} exceeds cap 8",
        da.max_degree
    );
    // Leg A now FITS (hard gate) after the prefix-sum in-bounds ray-scan reduction (901 cols).
    assert!(
        da.trace_width <= MAX_TRACE_WIDTH,
        "Leg A n=11 width {} exceeds {}",
        da.trace_width,
        MAX_TRACE_WIDTH
    );
}

/// **THE STRUCTURAL SEAM GAP (fast, PI-level).** A mismatched mid (Leg A fed a DIFFERENT
/// board than Leg R produced) diverges the two legs' board roots at the app-PI level
/// (`Leg R.PI[24..32] != Leg A.PI[16..24]`), BUT the cross-turn tooth the deployed fold
/// enforces is the CELL rotated-root continuity, not the board content. This test pins
/// the divergence (so the residual is precisely located) and documents that catching it
/// in-fold requires the cross-turn board-root weld (see `mismatched_mid_fold_probe`).
#[test]
fn mismatched_mid_diverges_board_roots_but_not_cell_continuity_11x11() {
    let (old, a, b) = turn();
    let honest_mid = resolve_mid(&old, &[a, b]);
    let mut forged_mid = honest_mid.clone();
    forged_mid.cells[0] = if forged_mid.cells[0] == 0 { 2 } else { 0 };
    assert_ne!(forged_mid, honest_mid);

    let leg_r = build_r_honest(&old, &a, &b);
    // Leg A on the forged mid is itself a genuine automaton step — it self-accepts.
    let leg_a_forged = build_a_honest(&forged_mid);
    assert!(
        leg_a_forged.air_accepts(),
        "Leg A on the forged mid self-accepts (the seam, not Leg A, must catch it)"
    );
    // The board roots DIVERGE at the app-PI level: Leg R's published mid_root (PI[24..32])
    // no longer equals Leg A's consumed old-root (PI[16..24]).
    assert_ne!(
        &leg_r.pis[24..32],
        &leg_a_forged.pis[16..24],
        "a forged mid MUST diverge the two legs' board roots"
    );
    eprintln!(
        "SEAM GAP (n=11): forged-mid diverges board roots (R.mid_root={:?} != A.old_root={:?}); \
         the deployed cross-turn tooth binds CELL roots, so this divergence is NOT a fold conflict \
         — the cross-turn board-root weld is the open residual.",
        leg_r.pis[24].0, leg_a_forged.pis[16].0
    );
}

// ============================================================================
// SLOW — real STARK proving + fold. `#[ignore]`; run on the build box.
// ============================================================================

#[test]
#[ignore = "SLOW: real n=11 Leg R (old→mid resolution) leaf prove"]
fn leg_r_leaf_proves_11x11() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let (old, a, b) = turn();
    let prog = build_r_honest(&old, &a, &b);
    assert!(
        prog.air_accepts(),
        "sanity: honest n=11 Leg R must self-accept"
    );
    let program = prog.cellprogram();
    let w = prog.trace_witness(2);
    let pis = prog.pis.clone();
    let config = ir2_leaf_wrap_config();
    let out = prove_custom_leaf_with_commitment(&program, &w, 2, &pis, &config)
        .expect("the honest n=11 Leg R AIR must prove as a commitment-exposing foldable leaf");
    let exposed =
        read_exposed_pi_commitment(&out).expect("Leg R leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "Leg R commitment must byte-match the host binding"
    );
    eprintln!(
        "LEG R n=11 LEAF: resolution AIR (w={}, {} constraints) PROVED; publishes mid_root PI[24..32]={:?}",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        pis[24..32].iter().map(|f| f.0).collect::<Vec<_>>(),
    );
}

#[test]
#[ignore = "SLOW: real n=11 Leg A (mid→new automaton) leaf prove (unblocked: 901 ≤ 1024)"]
fn leg_a_leaf_proves_11x11() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let (old, a, b) = turn();
    let mid = resolve_mid(&old, &[a, b]);

    // The byte-identical seam: Leg A's consumed old-root == Leg R's published mid_root.
    let leg_r = build_r_honest(&old, &a, &b);
    let prog = build_a_honest(&mid);
    assert!(
        prog.air_accepts(),
        "sanity: honest n=11 Leg A must self-accept"
    );
    assert_eq!(
        &leg_r.pis[24..32],
        &prog.pis[16..24],
        "Leg A consumes the byte-identical mid_root Leg R published"
    );

    let program = prog.cellprogram();
    let w = prog.trace_witness(2);
    let pis = prog.pis.clone();
    let config = ir2_leaf_wrap_config();
    let out = prove_custom_leaf_with_commitment(&program, &w, 2, &pis, &config)
        .expect("the honest n=11 Leg A AIR must prove as a commitment-exposing foldable leaf");
    let exposed =
        read_exposed_pi_commitment(&out).expect("Leg A leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "Leg A commitment must byte-match the host binding"
    );
    eprintln!(
        "LEG A n=11 LEAF: automaton AIR (w={}, {} constraints) PROVED; consumes mid_root PI[16..24]={:?}",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        pis[16..24].iter().map(|f| f.0).collect::<Vec<_>>(),
    );
}

// ============================================================================
// The deployed fold — the two sub-turns (Leg R then Leg A) fold as a K=2 chain and the
// light client ACCEPTS the honest 11×11 turn. Scaffolding mirrors prove_fold.rs::fold.
// ============================================================================
mod fold {
    use super::*;
    use dregg_cell::Ledger;
    use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, prove_vm_descriptor2_for_config};
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, empty_caveat_manifest,
        generate_rotated_effect_vm_descriptor_and_trace_wide,
    };
    use dregg_circuit::effect_vm::{CellState, Effect};
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::{
        FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    };
    use dregg_circuit_prove::joint_turn_aggregation::{
        CustomWitnessBundle, DescriptorParticipant, RotatedParticipantLeg,
    };
    use dregg_lightclient::verify_history;
    use dregg_turn::rotation_witness as rw;

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

    fn leg_real_roots(balance: i64, nonce: u64) -> ([BabyBear; 8], [BabyBear; 8]) {
        let probe = mint_custom_leg(balance, nonce, [BabyBear::ZERO; 8], None);
        (
            probe.wide_old_root8().expect("wide-anchored"),
            probe.wide_new_root8().expect("wide-anchored"),
        )
    }

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

        let (desc, trace, dpis, map_heaps, mb) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
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
        assert_eq!(
            &dpis[46..54],
            &commit[..],
            "custom leg publishes the commitment"
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

    /// Bundle a co-built `Builder` into a foldable custom-witness leg + its PIs.
    fn bundle_of(b: &Builder) -> (Vec<BabyBear>, CustomWitnessBundle) {
        let program = b.cellprogram();
        let rows = 2usize;
        let w = b.trace_witness(rows);
        let pis = b.pis.clone();
        (
            pis.clone(),
            CustomWitnessBundle {
                program,
                witness_values: w,
                num_rows: rows,
                public_inputs: pis,
                app_root_binding: None,
            },
        )
    }

    /// **THE HEADLINE — the honest 11×11 turn folds and the light client ACCEPTS.**
    /// Turn 0 = Leg R (old→mid), turn 1 = Leg A (mid→new), both on the SAME cell; the
    /// deployed continuity tooth sequences them (nonce 0→1). Leg R's published mid_root
    /// (PI[24..32]) is byte-identical to Leg A's consumed old-root (PI[16..24]) — the seam.
    #[test]
    #[ignore = "SLOW: the honest 11×11 two-sub-turn fold + light-client accept (unblocked: Leg A \
                901 ≤ 1024). Run on the build box with --ignored"]
    fn honest_11x11_two_subturn_folds_and_lightclient_accepts() {
        let balance = 1000i64;
        let (old, a, b) = super::turn();
        let mid = resolve_mid(&old, &[a, b]);

        let (r_old8, r_new8) = leg_real_roots(balance, 0);
        let (r_pis, r_bundle) = bundle_of(&build_r_honest_bound(&old, &a, &b, r_old8, r_new8));
        let (a_old8, a_new8) = leg_real_roots(balance, 1);
        let (a_pis, a_bundle) = bundle_of(&build_a_honest_bound(&mid, a_old8, a_new8));

        // THE SEAM (byte-identity): Leg R's mid_root welds Leg A's consumed old-root.
        assert_eq!(
            &r_pis[24..32],
            &a_pis[16..24],
            "Leg R's published mid_root must weld Leg A's consumed old-root"
        );

        let r_commit = custom_proof_pi_commitment(&r_pis);
        let a_commit = custom_proof_pi_commitment(&a_pis);
        let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(mint_custom_leg(
            balance,
            0,
            r_commit,
            Some(r_bundle),
        )));
        let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(mint_custom_leg(
            balance,
            1,
            a_commit,
            Some(a_bundle),
        )));
        assert_eq!(t0.new_root(), t1.old_root(), "cell continuity 0→1");
        let turns = vec![t0, t1];
        let whole = prove_turn_chain_recursive(&turns)
            .expect("the honest 11×11 two-sub-turn chain must fold through the deployed prover");
        let vk = whole.root_vk_fingerprint();
        let attested = verify_history(&whole, &vk)
            .expect("the REAL light client must ACCEPT the honest 11×11 turn");
        assert_eq!(attested.num_turns, 2);
        eprintln!(
            "11×11 ACCEPT: Leg R (old→mid) then Leg A (mid→new) -> fold(K=2) -> verify_history OK. \
             num_turns={}, mid_root[0]={}",
            attested.num_turns, r_pis[24].0,
        );
    }

    /// **THE SOUNDNESS PROBE (residual 2) — the mismatched-mid fold.** Turn 0 = Leg R
    /// (old→mid1); turn 1 = Leg A (mid2→new2) with mid2 ≠ mid1. Each leaf is a genuine
    /// transition on its own board, so both prove; the cell-continuity tooth binds the CELL
    /// rotated roots (nonce 0→1), independent of board content, so it does NOT catch the
    /// board mismatch. If `verify_history` ACCEPTS, the cross-turn board-root weld is MISSING
    /// (the residual). If it REJECTS, the seam is enforced in-fold. This test RECORDS which.
    #[test]
    #[ignore = "SLOW: the mismatched-mid soundness probe at 11×11 (unblocked: Leg A 901 ≤ 1024). \
                The n=5 twin `mismatched_mid_fold_probe_n5` runs the SAME probe faster"]
    fn mismatched_mid_fold_probe_11x11() {
        let balance = 1000i64;
        let (old, a, b) = super::turn();
        let mid1 = resolve_mid(&old, &[a, b]);
        let mut mid2 = mid1.clone();
        // Flip a non-auto cell so Leg A steps a DIFFERENT board than Leg R produced.
        for i in 0..mid2.cells.len() {
            let coord = ((i % mid2.n) as i32, (i / mid2.n) as i32);
            if coord != mid2.auto {
                mid2.cells[i] = if mid2.cells[i] == 0 { 2 } else { 0 };
                break;
            }
        }
        assert_ne!(mid2, mid1, "the mismatched mid must differ");

        let (r_old8, r_new8) = leg_real_roots(balance, 0);
        let (r_pis, r_bundle) = bundle_of(&build_r_honest_bound(&old, &a, &b, r_old8, r_new8));
        let (a_old8, a_new8) = leg_real_roots(balance, 1);
        let (a_pis, a_bundle) = bundle_of(&build_a_honest_bound(&mid2, a_old8, a_new8));

        // The board roots DIVERGE (this is the whole point) — but the cell tooth is blind.
        assert_ne!(
            &r_pis[24..32],
            &a_pis[16..24],
            "the mismatched mid diverges the board roots"
        );

        let r_commit = custom_proof_pi_commitment(&r_pis);
        let a_commit = custom_proof_pi_commitment(&a_pis);
        let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(mint_custom_leg(
            balance,
            0,
            r_commit,
            Some(r_bundle),
        )));
        let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(mint_custom_leg(
            balance,
            1,
            a_commit,
            Some(a_bundle),
        )));
        // The cell continuity STILL holds despite the board mismatch — the gap in one line.
        assert_eq!(
            t0.new_root(),
            t1.old_root(),
            "cell continuity holds regardless of board content (the gap)"
        );
        assert_mismatched_mid_rejects(vec![t0, t1], "11×11");
    }

    // ------------------------------------------------------------------------
    // The n=5 twin — Leg A FITS at n=5 (538 cols), so this runs the SAME residual-2
    // soundness probe on the deployed prover TODAY (the n=11 twin is width-blocked).
    // ------------------------------------------------------------------------

    use dregg_automatafl::reference::{ATT, AUTO, REP, VAC};

    fn mk5(placed: &[((i32, i32), u8)], auto: (i32, i32)) -> Board {
        let n = 5;
        let mut cells = vec![VAC; n * n];
        for &(c, p) in placed {
            cells[(c.1 as usize) * n + (c.0 as usize)] = p;
        }
        cells[(auto.1 as usize) * n + (auto.0 as usize)] = AUTO;
        Board {
            n,
            cells,
            auto,
            col_rule: true,
        }
    }

    /// Two independent survivors at n=5 (mid != old): ATT (0,0)→(0,3), REP (4,4)→(4,1).
    fn n5_turn() -> (Board, Move, Move) {
        (
            mk5(&[((0, 0), ATT), ((4, 4), REP)], (2, 2)),
            Move {
                who: 0,
                frm: (0, 0),
                to: (0, 3),
            },
            Move {
                who: 1,
                frm: (4, 4),
                to: (4, 1),
            },
        )
    }

    /// **RESIDUAL 2 — the runnable soundness verdict.** A mismatched-mid fold at n=5: Leg R
    /// produces mid1, Leg A steps a corrupted mid2 (≠ mid1). Both leaves prove (each is a
    /// genuine transition on its own board). The gate ASSERTS the deployed fold REJECTS it.
    /// It PASSES only if the seam is truly enforced in-fold; it FAILS (loudly) if the mismatch
    /// slips through — i.e. if the cross-turn board-root weld is missing. This is the gate that
    /// settles whether the seam is closed. `#[ignore]` (real fold is minutes+).
    #[test]
    #[ignore = "SLOW: the RUNNABLE residual-2 mismatched-mid soundness verdict at n=5"]
    fn mismatched_mid_fold_probe_n5() {
        let balance = 1000i64;
        let (old, a, b) = n5_turn();
        let mid1 = resolve_mid(&old, &[a, b]);
        let mut mid2 = mid1.clone();
        for i in 0..mid2.cells.len() {
            let coord = ((i % mid2.n) as i32, (i / mid2.n) as i32);
            if coord != mid2.auto {
                mid2.cells[i] = if mid2.cells[i] == VAC { ATT } else { VAC };
                break;
            }
        }
        assert_ne!(mid2, mid1, "the mismatched mid must differ");

        let (r_old8, r_new8) = leg_real_roots(balance, 0);
        let (r_pis, r_bundle) = bundle_of(&build_r_honest_bound(&old, &a, &b, r_old8, r_new8));
        let (a_old8, a_new8) = leg_real_roots(balance, 1);
        let (a_pis, a_bundle) = bundle_of(&build_a_honest_bound(&mid2, a_old8, a_new8));

        assert_ne!(
            &r_pis[24..32],
            &a_pis[16..24],
            "the mismatched mid diverges the board roots"
        );
        // Both leaves self-accept (genuine transitions on their own boards).
        let _ = REP; // (particle codes referenced for the n=5 case documentation)

        let r_commit = custom_proof_pi_commitment(&r_pis);
        let a_commit = custom_proof_pi_commitment(&a_pis);
        let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(mint_custom_leg(
            balance,
            0,
            r_commit,
            Some(r_bundle),
        )));
        let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(mint_custom_leg(
            balance,
            1,
            a_commit,
            Some(a_bundle),
        )));
        assert_eq!(
            t0.new_root(),
            t1.old_root(),
            "cell continuity holds regardless of board content (the gap, if present)"
        );
        assert_mismatched_mid_rejects(vec![t0, t1], "n=5");
    }

    /// Fold the mismatched-mid chain and ASSERT the deployed light client REJECTS it. Passes
    /// only if the seam is enforced in-fold; panics (documenting the open soundness residual)
    /// if the mismatch is accepted.
    fn assert_mismatched_mid_rejects(turns: Vec<FinalizedTurn>, size: &str) {
        match prove_turn_chain_recursive(&turns) {
            Err(_) => eprintln!(
                "{size} MISMATCHED-MID REJECTED at fold assembly — the seam is enforced in-fold."
            ),
            Ok(whole) => {
                let vk = whole.root_vk_fingerprint();
                match verify_history(&whole, &vk) {
                    Err(_) => eprintln!(
                        "{size} MISMATCHED-MID REJECTED at verify_history — the seam is enforced in-fold."
                    ),
                    Ok(_) => panic!(
                        "{size} SOUNDNESS GAP: the mismatched-mid fold was ACCEPTED by verify_history \
                         — the cross-turn board-root weld is MISSING. Close it by connecting turn i's \
                         published mid_root (Leg R app PI[24..32]) to turn i+1's consumed old-root \
                         (Leg A app PI[16..24]) in the recursion aggregation."
                    ),
                }
            }
        }
    }
}

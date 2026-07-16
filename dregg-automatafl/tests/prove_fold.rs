//! SLOW: the automaton-step (D1) AIR PROVES as a real recursion-foldable custom
//! leaf, its in-circuit commitment byte-matches the host binding, folds into a real
//! turn chain, and the light client `verify_history` ACCEPTS — the HARD GATE.
//!
//! Custom-leaf proving is minutes+; every test here is `#[ignore]`. Run on persvati:
//!   cargo test -p dregg-automatafl --test prove_fold -- --ignored --nocapture

use dregg_automatafl::build_d1_honest;
use dregg_automatafl::reference::{ATT, AUTO, Board, REP, VAC, automaton_step};

use dregg_circuit::field::BabyBear;

fn mk(n: usize, placed: &[((i32, i32), u8)], auto: (i32, i32)) -> Board {
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

/// The driven D1 board for the PROVABLE leaf/fold gates: a WIDTH-FITTING (≤1024) n=3 board whose
/// automaton is pulled by an attractor (auto at `(1,0)`, ATT at `(1,2)` → the automaton steps
/// south). n=3 is the size that fits the deployed prover TODAY (`tests/size.rs`: D1 n3 = 470 cols);
/// the n=5 deployed board is width-gated until the 4n³ ray-scan redesign lands (D1 n5 = 1038 > 1024,
/// pushed over by the two `MerkleHash8` board roots — the honest cost of the state commitment).
fn demo() -> Board {
    mk(3, &[((1, 2), ATT)], (1, 0))
}

// ============================================================================
// The leaf boundary (runnable in THIS tree — no rotated-witness path).
// ============================================================================

#[test]
#[ignore = "SLOW: real leaf prove of the ~989-col automaton-step AIR + in-circuit commitment expose"]
fn d1_leaf_proves_and_binds_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let old = demo();
    let b = build_d1_honest(&old);
    assert!(
        b.air_accepts(),
        "sanity: honest D1 must self-accept before proving"
    );
    let program = b.cellprogram();
    let rows = 2usize;
    let w = b.trace_witness(rows);
    let pis = b.pis.clone();
    let config = ir2_leaf_wrap_config();

    let out = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        .expect("the honest automaton-step AIR must prove as a commitment-exposing foldable leaf");
    let exposed = read_exposed_pi_commitment(&out).expect("leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "in-circuit commitment must byte-match the host WideHash binding"
    );
    eprintln!(
        "D1 LEAF: automaton-step AIR (w={}, {} constraints) PROVED as a foldable leaf; \
         in-circuit commitment == host binding {:?}",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        host.map(|f| f.0)
    );
}

#[test]
#[ignore = "SLOW: real leaf prove attempt on a FORGED next board"]
fn d1_forged_next_does_not_prove() {
    use dregg_automatafl::build_d1;
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let old = demo();
    // demo() steps the automaton north; forge next == old (claim it did NOT move).
    let forged_next = old.clone();
    assert_ne!(
        forged_next,
        automaton_step(&old),
        "the forgery must differ from the truth"
    );
    let b = build_d1(&old, &forged_next);
    // The witness self-check already rejects; a real prove must ALSO fail to assemble.
    assert!(!b.air_accepts(), "sanity: forged next must self-reject");
    let program = b.cellprogram();
    let rows = 2usize;
    let w = b.trace_witness(rows);
    let pis = b.pis.clone();
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
    }));
    match res {
        Err(_) | Ok(Err(_)) => {
            eprintln!("D1 LEAF REJECT: a forged automaton-step (no-move) had no satisfying leaf.");
        }
        Ok(Ok(_)) => panic!("a FORGED automaton-step minted a foldable leaf — soundness OPEN"),
    }
}

// ============================================================================
// D2 / D3 leaf boundary — the single-move apply (D2) and the n=2 resolution (D3)
// prove as foldable custom leaves, just like D1. MEASURED (tests/size.rs): D2/D3
// run the automaton gadget a SECOND time (on the move-resolved `mid`), plus the two
// `MerkleHash8` board roots, so at n=5 they EXCEED MAX_TRACE_WIDTH=1024 — the honest
// width residual the 4n³ ray-scan redesign must close before the n=5 leaves prove.
// They FIT at n=3 (the tests below drive that size); `tests/size.rs` is the width
// GATE (RED at n=5 until the scan lands), and these fold tests are `#[ignore]` because
// a real STARK fold is minutes+ (run `-- --ignored` on the build box), NOT because
// they would false-green: with the state-binding ABI now satisfied (32 PIs, PI[0..16]
// == the leg's real rotated roots) they PROVE-FOLD-VERIFY when run at n=3.
// ============================================================================

use dregg_automatafl::reference::Move;
use dregg_automatafl::{
    SealedMove, build_d2, build_d2_honest, build_d2_honest_bound, build_d3, build_d3_honest,
    build_d3_honest_bound, build_sealed, build_sealed_honest, build_sealed_honest_bound,
};

/// A width-fitting (≤1024) D2 board at n=3: a single move, corner-parked daemon.
fn d2_case() -> (Board, Move) {
    let old = mk(3, &[((0, 0), ATT)], (2, 2));
    let m = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 1),
    };
    (old, m)
}

/// A width-fitting (≤1024) D3 board at n=3: two non-vacuum sources onto one cell (a
/// dest-collision → both dropped), so the n=2 selection truth-table fires in-circuit.
fn d3_case() -> (Board, Move, Move) {
    let old = mk(3, &[((0, 0), ATT), ((2, 2), REP)], (2, 0));
    let a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 2),
    };
    let b = Move {
        who: 1,
        frm: (2, 2),
        to: (0, 2),
    };
    (old, a, b)
}

fn sealed_case() -> (Board, SealedMove, SealedMove) {
    let old = mk(5, &[((0, 0), ATT), ((4, 4), REP)], (2, 2));
    let a = SealedMove {
        seat: 0,
        mv: Move {
            who: 0,
            frm: (0, 0),
            to: (0, 3),
        },
        nonce: 0xABCD,
    };
    let b = SealedMove {
        seat: 1,
        mv: Move {
            who: 1,
            frm: (4, 4),
            to: (4, 1),
        },
        nonce: 0x1234,
    };
    (old, a, b)
}

#[test]
#[ignore = "SLOW: real leaf prove of the D2 single-move-apply AIR (n=3) + commitment expose"]
fn d2_leaf_proves_and_binds_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let (old, m) = d2_case();
    let b = build_d2_honest(&old, &m);
    assert!(b.air_accepts(), "sanity: honest D2 must self-accept");
    let program = b.cellprogram();
    let rows = 2usize;
    let w = b.trace_witness(rows);
    let pis = b.pis.clone();
    let config = ir2_leaf_wrap_config();
    let out = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        .expect("the honest D2 apply AIR must prove as a commitment-exposing foldable leaf");
    let exposed = read_exposed_pi_commitment(&out).expect("D2 leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "D2 in-circuit commitment must byte-match the host binding"
    );
    eprintln!(
        "D2 LEAF: single-move-apply AIR (w={}, {} constraints) PROVED as a foldable leaf; \
         commitment == host {:?}",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        host.map(|f| f.0)
    );
}

#[test]
#[ignore = "SLOW: real leaf prove attempt on a FORGED D2 next board"]
fn d2_forged_next_does_not_prove() {
    use dregg_automatafl::reference::apply_turn;
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let (old, m) = d2_case();
    let honest = apply_turn(&old, &[m]);
    let forged_next = old.clone();
    assert_ne!(
        forged_next, honest,
        "the forgery must differ from the truth"
    );
    let b = build_d2(&old, &m, &forged_next);
    assert!(!b.air_accepts(), "sanity: forged D2 next must self-reject");
    let program = b.cellprogram();
    let w = b.trace_witness(2);
    let pis = b.pis.clone();
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w, 2, &pis, &config)
    }));
    match res {
        Err(_) | Ok(Err(_)) => {
            eprintln!("D2 LEAF REJECT: a forged single-move apply had no satisfying leaf.")
        }
        Ok(Ok(_)) => panic!("a FORGED D2 apply minted a foldable leaf — soundness OPEN"),
    }
}

#[test]
#[ignore = "SLOW: real leaf prove of the D3 n=2-resolution AIR (n=3) + commitment expose"]
fn d3_leaf_proves_and_binds_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let (old, a, bmv) = d3_case();
    let prog = build_d3_honest(&old, &a, &bmv);
    assert!(prog.air_accepts(), "sanity: honest D3 must self-accept");
    let program = prog.cellprogram();
    let rows = 2usize;
    let w = prog.trace_witness(rows);
    let pis = prog.pis.clone();
    let config = ir2_leaf_wrap_config();
    let out = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        .expect("the honest D3 resolution AIR must prove as a commitment-exposing foldable leaf");
    let exposed = read_exposed_pi_commitment(&out).expect("D3 leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "D3 in-circuit commitment must byte-match the host binding"
    );
    eprintln!(
        "D3 LEAF: n=2-resolution AIR (w={}, {} constraints) PROVED as a foldable leaf; \
         commitment == host {:?}",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        host.map(|f| f.0)
    );
}

#[test]
#[ignore = "SLOW: real leaf prove attempt on a FORGED D3 resolution"]
fn d3_forged_next_does_not_prove() {
    use dregg_automatafl::reference::apply_turn;
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let (old, a, bmv) = d3_case();
    let honest = apply_turn(&old, &[a, bmv]);
    let forged_next = old.clone();
    assert_ne!(
        forged_next, honest,
        "the forgery must differ from the truth"
    );
    let prog = build_d3(&old, &a, &bmv, &forged_next);
    assert!(
        !prog.air_accepts(),
        "sanity: forged D3 resolution must self-reject"
    );
    let program = prog.cellprogram();
    let w = prog.trace_witness(2);
    let pis = prog.pis.clone();
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w, 2, &pis, &config)
    }));
    match res {
        Err(_) | Ok(Err(_)) => {
            eprintln!("D3 LEAF REJECT: a forged n=2 resolution had no satisfying leaf.")
        }
        Ok(Ok(_)) => panic!("a FORGED D3 resolution minted a foldable leaf — soundness OPEN"),
    }
}

// ============================================================================
// THE IN-PROOF SEALED MOVE — the Poseidon2 commit→reveal enforced INSIDE the AIR.
// The sealed-move leaf carries `Hash4to1` chip sites (the automatafl analogue of the
// multiway-tug hidden-hand membership leaf); it PROVES a committed+opened pair, and a
// forged reveal (opening a move ≠ the committed one) has no satisfying leaf.
// ============================================================================

#[test]
#[ignore = "SLOW: real leaf prove of the sealed-move reveal AIR (two Poseidon2 Hash4to1 sites)"]
fn sealed_leaf_proves_and_binds_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let (old, a, bmv) = sealed_case();
    let prog = build_sealed_honest(&old, &a, &bmv);
    assert!(
        prog.air_accepts(),
        "sanity: honest sealed reveal must self-accept"
    );
    // The published PI commitments ARE the host Poseidon2 commitments.
    assert!(prog.pis.contains(&a.commit(old.n)) && prog.pis.contains(&bmv.commit(old.n)));
    let program = prog.cellprogram();
    let rows = 2usize;
    let w = prog.trace_witness(rows);
    let pis = prog.pis.clone();
    let config = ir2_leaf_wrap_config();
    let out = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config).expect(
        "the honest sealed-move reveal AIR (Poseidon2 Hash4to1 commit sites) must prove as a leaf",
    );
    let exposed =
        read_exposed_pi_commitment(&out).expect("sealed leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "sealed in-circuit commitment must byte-match the host binding"
    );
    eprintln!(
        "SEALED LEAF: reveal AIR (w={}, {} constraints, 2 Hash4to1 sites) PROVED; the committed \
         moves are opened IN-PROOF; commitment == host {:?}",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        host.map(|f| f.0)
    );
}

#[test]
#[ignore = "SLOW: real leaf prove attempt on a FORGED sealed reveal (opening a move ≠ committed)"]
fn sealed_forged_reveal_does_not_prove() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let (old, a, bmv) = sealed_case();
    // Seat A committed (0,0)->(0,3) but OPENS (0,0)->(0,4) after seeing the board — a valid
    // move, but not the committed one. The in-AIR Hash4to1 (commit == hash(opened)) rejects.
    let forged_open = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 4),
    };
    assert_ne!(forged_open, a.mv, "the forged opening must differ");
    let prog = build_sealed(&old, &a, &forged_open, &bmv, &bmv.mv);
    assert!(
        !prog.air_accepts(),
        "sanity: a forged reveal must self-reject"
    );
    let program = prog.cellprogram();
    let w = prog.trace_witness(2);
    let pis = prog.pis.clone();
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w, 2, &pis, &config)
    }));
    match res {
        Err(_) | Ok(Err(_)) => eprintln!(
            "SEALED LEAF REJECT: a reveal opening a move ≠ the committed one had no satisfying leaf."
        ),
        Ok(Ok(_)) => {
            panic!("a FORGED sealed reveal minted a foldable leaf — the commitment is not binding")
        }
    }
}

// ============================================================================
// The full deployed fold — D1 leaf binds to a Custom-effect turn, folds a K=2
// chain via prove_turn_chain_recursive, verify_history ACCEPTS. (Copies the
// audited game-turn-slice scaffolding, swapping the combat program for D1.)
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

    /// **THE PRODUCTION LEG'S REAL ROTATED ROOTS.** Mint a PROBE leg through the same minter at
    /// `(balance, nonce)` with a dummy commitment + no bundle, and read its wide 8-felt anchors —
    /// the values the deployed state fold `connect`s the sub-proof's declared `[old8 ‖ new8]`
    /// prefix to. Sound because the wide roots come from the rotation witness (the cell's limbs +
    /// iroot) and do NOT depend on the claimed commitment or the attached bundle. The automatafl
    /// leaf must publish EXACTLY these at PI[0..16] or the state tooth is UNSAT.
    fn leg_real_roots(balance: i64, nonce: u64) -> ([BabyBear; 8], [BabyBear; 8]) {
        let probe = mint_custom_leg(balance, nonce, [BabyBear::ZERO; 8], None);
        (
            probe
                .wide_old_root8()
                .expect("the custom wide leg is wide-anchored"),
            probe
                .wide_new_root8()
                .expect("the custom wide leg is wide-anchored"),
        )
    }

    /// Bundle the honest D1 leaf, BOUND to the leg's real cell-state roots (`old8`/`new8` at
    /// PI[0..16]), so the deployed state-binding node's second tooth (the roots connect) is
    /// satisfiable — not just the commitment tooth.
    fn d1_bundle(
        old8: [BabyBear; 8],
        new8: [BabyBear; 8],
    ) -> (super::build_helper::Prog, CustomWitnessBundle) {
        let old = demo();
        let b = dregg_automatafl::build_d1_honest_bound(&old, old8, new8);
        let program = b.cellprogram();
        let rows = 2usize;
        let w = b.trace_witness(rows);
        let pis = b.pis.clone();
        (
            super::build_helper::Prog { pis: pis.clone() },
            CustomWitnessBundle {
                program,
                witness_values: w,
                num_rows: rows,
                public_inputs: pis,
            },
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
            "custom leg publishes the 8-felt commitment"
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

    fn plain_custom_turn(balance: i64, nonce: u64) -> FinalizedTurn {
        let commit = core::array::from_fn(|i| BabyBear::new((i + 1) as u32));
        let leg = mint_custom_leg(balance, nonce, commit, None);
        FinalizedTurn::new(DescriptorParticipant::rotated(leg))
    }

    #[test]
    #[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes to tens of minutes)"]
    fn d1_turn_folds_and_lightclient_accepts() {
        let balance = 1000i64;
        // Read the leg's REAL rotated roots, then bind the D1 leaf to them (the state tooth).
        let (old8, new8) = leg_real_roots(balance, 0);
        let (prog, bundle) = d1_bundle(old8, new8);
        let real = custom_proof_pi_commitment(&prog.pis);
        let t0_leg = mint_custom_leg(balance, 0, real, Some(bundle));
        let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
        let t1 = plain_custom_turn(balance, 1);
        assert_eq!(
            t0.new_root(),
            t1.old_root(),
            "turn 0 post-state links to turn 1"
        );
        let turns = vec![t0, t1];

        let mut whole = prove_turn_chain_recursive(&turns)
            .expect("the honest D1-bearing chain must fold through the deployed prover");
        let vk = whole.root_vk_fingerprint();
        let attested = verify_history(&whole, &vk)
            .expect("the REAL light client must ACCEPT the honest D1 whole-chain artifact");
        assert_eq!(attested.num_turns, 2);
        eprintln!(
            "D1 ACCEPT: automaton-step CellProgram -> custom leaf -> fold(K=2) -> verify_history OK. \
             num_turns={}, final_root[0]={}",
            attested.num_turns, attested.final_root[0].0
        );
        // Non-vacuous bite: a relabeled final_root is REJECTED.
        let honest_final = whole.final_root;
        whole.final_root[0] = honest_final[0] + BabyBear::new(1);
        assert!(
            verify_history(&whole, &vk).is_err(),
            "a spliced final_root must be rejected"
        );
        whole.final_root = honest_final;
        verify_history(&whole, &vk).expect("restored honest artifact verifies again");
    }

    /// Bundle any co-built `Builder` into a foldable custom-witness leg + its PIs.
    fn bundle_of(b: &dregg_automatafl::Builder) -> (Vec<BabyBear>, CustomWitnessBundle) {
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
            },
        )
    }

    /// Drive the deployed fold: the leaf binds to a Custom-effect turn, folds a K=2 chain,
    /// and `verify_history` ACCEPTS; then a spliced `final_root` is REJECTED (non-vacuous).
    fn fold_and_accept(pis: Vec<BabyBear>, bundle: CustomWitnessBundle, label: &str) {
        let real = custom_proof_pi_commitment(&pis);
        let balance = 1000i64;
        let t0_leg = mint_custom_leg(balance, 0, real, Some(bundle));
        let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
        let t1 = plain_custom_turn(balance, 1);
        assert_eq!(t0.new_root(), t1.old_root(), "turn 0 links to turn 1");
        let turns = vec![t0, t1];
        let mut whole = prove_turn_chain_recursive(&turns)
            .expect("the honest chain must fold through the deployed prover");
        let vk = whole.root_vk_fingerprint();
        let attested = verify_history(&whole, &vk)
            .expect("the REAL light client must ACCEPT the honest whole-chain artifact");
        assert_eq!(attested.num_turns, 2);
        eprintln!(
            "{label} ACCEPT: CellProgram -> custom leaf -> fold(K=2) -> verify_history OK. \
             num_turns={}, final_root[0]={}",
            attested.num_turns, attested.final_root[0].0
        );
        let honest_final = whole.final_root;
        whole.final_root[0] = honest_final[0] + BabyBear::new(1);
        assert!(
            verify_history(&whole, &vk).is_err(),
            "a spliced final_root must be rejected"
        );
        whole.final_root = honest_final;
        verify_history(&whole, &vk).expect("restored honest artifact verifies again");
    }

    #[test]
    #[ignore = "SLOW: deployed D2 single-move-apply fold + light-client accept"]
    fn d2_turn_folds_and_lightclient_accepts() {
        let (old8, new8) = leg_real_roots(1000, 0);
        let (old, m) = super::d2_case();
        let (pis, bundle) = bundle_of(&super::build_d2_honest_bound(&old, &m, old8, new8));
        fold_and_accept(pis, bundle, "D2");
    }

    #[test]
    #[ignore = "SLOW: deployed D3 n=2-resolution fold + light-client accept"]
    fn d3_turn_folds_and_lightclient_accepts() {
        let (old8, new8) = leg_real_roots(1000, 0);
        let (old, a, b) = super::d3_case();
        let (pis, bundle) = bundle_of(&super::build_d3_honest_bound(&old, &a, &b, old8, new8));
        fold_and_accept(pis, bundle, "D3");
    }

    #[test]
    #[ignore = "SLOW: deployed in-proof sealed-move (Poseidon2 Hash4to1) fold + light-client accept"]
    fn sealed_turn_folds_and_lightclient_accepts() {
        let (old8, new8) = leg_real_roots(1000, 0);
        let (old, a, b) = super::sealed_case();
        let (pis, bundle) = bundle_of(&super::build_sealed_honest_bound(&old, &a, &b, old8, new8));
        fold_and_accept(pis, bundle, "SEALED");
    }
}

mod build_helper {
    use dregg_circuit::field::BabyBear;
    pub struct Prog {
        pub pis: Vec<BabyBear>,
    }
}

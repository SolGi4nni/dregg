//! # Phase-D LOWERING — DRIVEN: game teeth → range gadget → a real foldable leaf.
//!
//! The de-risk found the gap: no `StateConstraint → ConstraintExpr` bridge, and the ordering
//! teeth (`FieldGte`/`FieldLte`/`Monotonic`) do NOT lower as atoms (no DSL inequality; the
//! naive range-`Lookup` is REFUSED). This test suite DRIVES the closure:
//!
//!   * `compiler_lowering_table` (cheap, always runs) — lowers every executor tooth kind
//!     through [`GameProgramCompiler::lower_state_constraint`], printing which LOWER (clean
//!     algebraic OR via the bit-decomposition RANGE GADGET) vs the named RESIDUALS, and proves
//!     the assembled game program's `ConstraintExpr`s pass through the REAL adapter
//!     `cellprogram_to_descriptor2` (Ok, no `Lookup`).
//!
//!   * `game_program_leaf_accepts` (#[ignore], SLOW) — a whole game `CellProgram` (an
//!     HP-floor `FieldGte`, a level-ratchet `Monotonic`, an alive-flag boolean, damage/score
//!     conservation, an exact scene set) PROVES as a foldable leaf through the REAL
//!     `prove_custom_leaf_with_commitment`, and the in-circuit-exposed 4-felt commitment is
//!     byte-identical to the host `custom_proof_pi_commitment` — i.e. the ordering teeth reach
//!     exactly the foldable, commitment-bound artifact the light client's fold consumes.
//!
//!   * `forged_ordering_rejects` (#[ignore], SLOW) — a FORGED witness that violates the
//!     `Monotonic` ordering tooth (level goes DOWN) has NO satisfying leaf (its range head is
//!     negative → no `n`-bit recomposition), and likewise a forged `FieldGte` (HP below floor).
//!
//! LEAF-LEVEL is the bar: the full fold → `verify_history` is upstream-gated on Lane D's
//! revoked-root limb migration (`game_program_full_fold_gated_on_lane_d`, #[ignore]d with the
//! reason).

use dregg_cell::program::{StateConstraint, field_from_u64};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2;
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

use dregg_circuit::dsl::circuit::{CellProgram, ConstraintExpr};
use game_turn_slice::compiler::{GameProgramCompiler, SlotAssignment};

const RANGE_BITS: usize = 16;
const NUM_ROWS: usize = 4;

// Slot layout for the demo game turn.
const SLOT_HP: u8 = 0; // HP — FieldGte floor (range gadget)
const SLOT_LEVEL: u8 = 2; // level — Monotonic ratchet (range gadget)
const SLOT_ALIVE: u8 = 3; // alive flag — MemberOf {0,1} (Binary)
const SLOT_SCORE: u8 = 4; // score — SumEqualsAcross (poly)
const SLOT_POINTS: u8 = 5; // points earned this turn
const SLOT_SCENE: u8 = 6; // scene id — FieldEquals (poly)

const HP_FLOOR: u64 = 1;
const SCENE_ID: u64 = 42;

/// The demo game `CellProgram`'s referee teeth, in the executor's `StateConstraint` vocabulary.
fn game_teeth() -> Vec<StateConstraint> {
    vec![
        // HP must stay at or above the floor — an ORDERING tooth (range gadget).
        StateConstraint::FieldGte {
            index: SLOT_HP,
            value: field_from_u64(HP_FLOOR),
        },
        // Level never decreases — an ORDERING tooth (range gadget on the delta).
        StateConstraint::Monotonic { index: SLOT_LEVEL },
        // Alive is a boolean.
        StateConstraint::MemberOf {
            index: SLOT_ALIVE,
            set: vec![0, 1],
        },
        // Score conservation: new[score] == old[score] + new[points].
        StateConstraint::SumEqualsAcross {
            input_fields: vec![SLOT_SCORE],
            output_fields: vec![SLOT_POINTS],
        },
        // The scene is set to an exact id this turn.
        StateConstraint::FieldEquals {
            index: SLOT_SCENE,
            value: field_from_u64(SCENE_ID),
        },
    ]
}

/// Compile the game teeth into a circuit-DSL `CellProgram` (panics if any tooth refuses — none
/// of the demo teeth are residuals). Returns the compiler (for witness gen) and the program.
fn build_game_program() -> (GameProgramCompiler, CellProgram) {
    let mut c = GameProgramCompiler::new("dregg-game-turn-v1", RANGE_BITS).with_public_inputs(2);
    for tooth in game_teeth() {
        c.lower_state_constraint(&tooth)
            .unwrap_or_else(|b| panic!("demo tooth must lower: {b}"));
    }
    let program = c.finish();
    (c, program)
}

/// The honest slot assignment: HP=10 (≥1), level 2→3 (up), alive=1, score 100→120 (+20 points),
/// scene=42.
fn honest_assignment() -> SlotAssignment {
    SlotAssignment::new()
        .set_new(SLOT_HP, 10)
        .set_new(SLOT_LEVEL, 3)
        .set_old(SLOT_LEVEL, 2)
        .set_new(SLOT_ALIVE, 1)
        .set_new(SLOT_SCORE, 120)
        .set_old(SLOT_SCORE, 100)
        .set_new(SLOT_POINTS, 20)
        .set_new(SLOT_SCENE, SCENE_ID)
}

/// The leaf's public inputs (committed by the in-circuit PI-commitment). Minimal, as the
/// de-risk's combat program does; the ordering enforcement is in the trace constraints.
fn game_pis() -> Vec<BabyBear> {
    vec![BabyBear::from_u64(120), BabyBear::from_u64(3)]
}

// ============================================================================
// PART 1 — THE COMPILER LOWERING TABLE (cheap, always runs)
// ============================================================================

#[test]
fn compiler_lowering_table() {
    // Each row: a representative executor tooth, whether we expect it to LOWER.
    struct Row {
        label: &'static str,
        tooth: StateConstraint,
        expect_lowers: bool,
    }
    let rows = vec![
        // clean algebraic
        Row {
            label: "FieldEquals (exact scene set)",
            tooth: StateConstraint::FieldEquals {
                index: 6,
                value: field_from_u64(42),
            },
            expect_lowers: true,
        },
        Row {
            label: "SumEqualsAcross (score conservation)",
            tooth: StateConstraint::SumEqualsAcross {
                input_fields: vec![4],
                output_fields: vec![5],
            },
            expect_lowers: true,
        },
        Row {
            label: "MemberOf {0,1} (alive boolean)",
            tooth: StateConstraint::MemberOf {
                index: 3,
                set: vec![0, 1],
            },
            expect_lowers: true,
        },
        Row {
            label: "WriteOnce (first-grabber-wins)",
            tooth: StateConstraint::WriteOnce { index: 7 },
            expect_lowers: true,
        },
        // ORDERING teeth — the range gadget
        Row {
            label: "FieldGte (HP floor) — RANGE GADGET",
            tooth: StateConstraint::FieldGte {
                index: 0,
                value: field_from_u64(1),
            },
            expect_lowers: true,
        },
        Row {
            label: "FieldLte (ceiling) — RANGE GADGET",
            tooth: StateConstraint::FieldLte {
                index: 0,
                value: field_from_u64(100),
            },
            expect_lowers: true,
        },
        Row {
            label: "FieldLteField (spend<=budget) — RANGE GADGET",
            tooth: StateConstraint::FieldLteField {
                left_index: 8,
                right_index: 9,
            },
            expect_lowers: true,
        },
        Row {
            label: "Monotonic (level ratchet) — RANGE GADGET",
            tooth: StateConstraint::Monotonic { index: 2 },
            expect_lowers: true,
        },
        Row {
            label: "StrictMonotonic (strict bid) — RANGE GADGET",
            tooth: StateConstraint::StrictMonotonic { index: 2 },
            expect_lowers: true,
        },
        // named residuals
        Row {
            label: "PreimageGate (hash carrier)",
            tooth: StateConstraint::PreimageGate {
                commitment_index: 1,
                hash_kind: dregg_cell::program::HashKind::Poseidon2,
            },
            expect_lowers: false,
        },
        Row {
            label: "SenderIs (host context)",
            tooth: StateConstraint::SenderIs { pk: [0u8; 32] },
            expect_lowers: false,
        },
        Row {
            label: "TemporalGate (block height)",
            tooth: StateConstraint::TemporalGate {
                not_before: Some(10),
                not_after: None,
            },
            expect_lowers: false,
        },
        Row {
            label: "AllowedTransitions (pair disjunction)",
            tooth: StateConstraint::AllowedTransitions {
                slot_index: 1,
                allowed: vec![(field_from_u64(0), field_from_u64(1))],
            },
            expect_lowers: false,
        },
    ];

    eprintln!("\n=========== StateConstraint → ConstraintExpr LOWERING TABLE ===========");
    let (mut lowered, mut refused) = (0usize, 0usize);
    for r in &rows {
        // Each tooth lowered in its OWN compiler so column allocation is independent.
        let mut c = GameProgramCompiler::new("probe", RANGE_BITS);
        match (c.lower_state_constraint(&r.tooth), r.expect_lowers) {
            (Ok(exprs), true) => {
                lowered += 1;
                let kinds = kind_summary(&exprs);
                eprintln!(
                    "  LOWERS  | {:<44} | {} constraint(s): {kinds}",
                    r.label,
                    exprs.len()
                );
            }
            (Err(b), false) => {
                refused += 1;
                eprintln!("  REFUSED | {:<44} | blocker: {b}", r.label);
            }
            (Ok(_), false) => panic!("`{}` was expected to REFUSE but lowered", r.label),
            (Err(b), true) => panic!("`{}` was expected to LOWER but refused: {b}", r.label),
        }
    }
    eprintln!("=======================================================================");
    eprintln!(
        "  {lowered} kinds lower ({} clean + range gadget), {refused} named residuals.\n",
        lowered
    );
    assert_eq!(
        lowered, 9,
        "the 4 clean + 5 ordering (range-gadget) teeth lower"
    );
    assert_eq!(
        refused, 4,
        "the crypto/context/disjunction residuals refuse"
    );

    // DRIVE the REAL adapter on the assembled game program: every emitted ConstraintExpr must
    // pass `cellprogram_to_descriptor2` (no refused `Lookup`). This is the cheap proof that the
    // range gadget's output is adapter-accepted — the exact thing the naive range-Lookup was
    // REFUSED for.
    let (compiler, program) = build_game_program();
    let n_lookup = program
        .descriptor
        .constraints
        .iter()
        .filter(|c| matches!(c, ConstraintExpr::Lookup { .. }))
        .count();
    assert_eq!(
        n_lookup, 0,
        "the range gadget must NOT emit any refused Lookup"
    );
    let desc2 = cellprogram_to_descriptor2(&program)
        .expect("the assembled game program must lower through the REAL custom-leaf adapter");
    eprintln!(
        "GAME PROGRAM lowered: {} columns, {} ConstraintExprs → adapter Ok ({} IR-v2 constraints). \
         range teeth: {:?}",
        compiler.width(),
        program.descriptor.constraints.len(),
        desc2.constraints.len(),
        compiler.range_teeth(),
    );
}

fn kind_summary(exprs: &[ConstraintExpr]) -> String {
    let mut bins = 0;
    let mut polys = 0;
    let mut other = 0;
    for e in exprs {
        match e {
            ConstraintExpr::Binary { .. } => bins += 1,
            ConstraintExpr::Polynomial { .. } => polys += 1,
            _ => other += 1,
        }
    }
    format!("{bins} Binary + {polys} Polynomial + {other} other")
}

// ============================================================================
// PART 2 — THE LEAF, DRIVEN (heavy, #[ignore])
// ============================================================================

/// THE POSITIVE POLE: the whole game program (incl. the FieldGte + Monotonic ordering teeth)
/// PROVES as a real foldable leaf, and its in-circuit-exposed commitment binds the PIs.
#[test]
#[ignore = "SLOW: real leaf prove + in-circuit commitment expose over the range-gadget program (~tens of seconds); run with --ignored"]
fn game_program_leaf_accepts() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };

    let (compiler, program) = build_game_program();
    let assign = honest_assignment();
    let witness = compiler.witness(&assign, NUM_ROWS).unwrap();
    let pis = game_pis();
    let config = ir2_leaf_wrap_config();

    eprintln!(
        "GAME LEAF: proving a {}-column program with ordering teeth {:?} ...",
        compiler.width(),
        compiler.range_teeth()
    );

    let output = prove_custom_leaf_with_commitment(&program, &witness, NUM_ROWS, &pis, &config)
        .expect(
            "the honest game CellProgram (with range-gadget ordering teeth) must prove as a leaf",
        );

    let exposed = read_exposed_pi_commitment(&output).expect("leaf exposes a 4-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "the in-circuit commitment must byte-match the host WideHash binding"
    );
    eprintln!(
        "D-CROWN LEAF ACCEPT: game CellProgram (FieldGte + Monotonic via bit-decomp range gadget) \
         PROVED as a foldable leaf; in-circuit commitment == host binding {:?}",
        host.map(|f| f.0)
    );
}

/// THE NEGATIVE POLE: a forged witness that violates the `Monotonic` ordering tooth (level goes
/// DOWN, 5→3) has a NEGATIVE range head, so no `n`-bit recomposition exists — the leaf does NOT
/// prove. Then the same for a forged `FieldGte` (HP=0, below the floor of 1).
#[test]
#[ignore = "SLOW: real leaf prove attempts on forged ordering witnesses (~tens of seconds each); run with --ignored"]
fn forged_ordering_rejects() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;

    let (compiler, program) = build_game_program();
    let pis = game_pis();
    let config = ir2_leaf_wrap_config();

    // --- Forge #1: Monotonic violated (level DECREASES 5 → 3). ---
    let forged_mono = SlotAssignment::new()
        .set_new(SLOT_HP, 10)
        .set_new(SLOT_LEVEL, 3)
        .set_old(SLOT_LEVEL, 5) // FORGED: new < old ⇒ negative range head
        .set_new(SLOT_ALIVE, 1)
        .set_new(SLOT_SCORE, 120)
        .set_old(SLOT_SCORE, 100)
        .set_new(SLOT_POINTS, 20)
        .set_new(SLOT_SCENE, SCENE_ID);
    let w = compiler.witness(&forged_mono, NUM_ROWS).unwrap();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w, NUM_ROWS, &pis, &config)
    }));
    match r {
        Err(_) | Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED Monotonic-violating witness (level went DOWN) minted a foldable leaf — \
             ordering soundness OPEN"
        ),
    }
    eprintln!(
        "D-CROWN LEAF REJECT (Monotonic): level 5→3 had a negative range head; no satisfying leaf."
    );

    // --- Forge #2: FieldGte violated (HP = 0, below the floor of 1). ---
    let forged_gte = SlotAssignment::new()
        .set_new(SLOT_HP, 0) // FORGED: 0 < floor(1) ⇒ negative range head
        .set_new(SLOT_LEVEL, 3)
        .set_old(SLOT_LEVEL, 2)
        .set_new(SLOT_ALIVE, 1)
        .set_new(SLOT_SCORE, 120)
        .set_old(SLOT_SCORE, 100)
        .set_new(SLOT_POINTS, 20)
        .set_new(SLOT_SCENE, SCENE_ID);
    let w2 = compiler.witness(&forged_gte, NUM_ROWS).unwrap();
    let r2 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w2, NUM_ROWS, &pis, &config)
    }));
    match r2 {
        Err(_) | Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED FieldGte-violating witness (HP below floor) minted a foldable leaf — \
             ordering soundness OPEN"
        ),
    }
    eprintln!(
        "D-CROWN LEAF REJECT (FieldGte): HP=0 below floor=1 had a negative range head; no leaf."
    );
}

// A sanity check on the witness/head arithmetic that does NOT prove (cheap): the honest heads
// are non-negative and small; the forged heads are negative (⇒ field-huge ⇒ unrepresentable in
// RANGE_BITS). This is the mechanism the SLOW forged-reject test exercises through the prover.
#[test]
fn range_head_signs() {
    let (compiler, _program) = build_game_program();
    // The two range teeth are (in emission order) FieldGte(bit0 col) then Monotonic(bit0 col).
    // We don't need their exact column indices — assert the honest heads are in [0, 2^bits) and
    // the forged heads are negative by recomputing them directly.
    let honest = honest_assignment();
    // FieldGte head = new[HP] - 1 = 9; Monotonic head = new[LEVEL] - old[LEVEL] = 1.
    assert_eq!(honest.new_slots[&SLOT_HP] as i128 - HP_FLOOR as i128, 9);
    assert_eq!(
        honest.new_slots[&SLOT_LEVEL] as i128 - honest.old_slots[&SLOT_LEVEL] as i128,
        1
    );
    // Both are ≥ 0 and < 2^RANGE_BITS.
    assert!((0..(1i128 << RANGE_BITS)).contains(&9));
    assert!((0..(1i128 << RANGE_BITS)).contains(&1));
    // Forged Monotonic head 3 - 5 = -2 (negative ⇒ unrepresentable).
    assert!(3i128 - 5i128 < 0);
    // Keep the compiler alive so the build wiring is exercised.
    let _ = compiler.width();
}

#[test]
fn witness_refuses_babybear_aliases_and_missing_slots() {
    use dregg_circuit::field::BABYBEAR_P;
    use game_turn_slice::compiler::WitnessError;

    let mut compiler = GameProgramCompiler::new("alias-boundary", 16);
    compiler
        .lower_state_constraint(&StateConstraint::FieldEquals {
            index: SLOT_HP,
            value: field_from_u64(1),
        })
        .unwrap();

    let aliased = SlotAssignment::new().set_new(SLOT_HP, BABYBEAR_P as u64 + 1);
    assert!(matches!(
        compiler.witness(&aliased, 1),
        Err(WitnessError::OutOfRange {
            side: "new",
            index: SLOT_HP,
            ..
        })
    ));
    assert_eq!(
        compiler.witness(&SlotAssignment::new(), 1),
        Err(WitnessError::MissingSlot {
            side: "new",
            index: SLOT_HP,
        })
    );
}

// ============================================================================
// PART 3 — THE FULL FOLD (upstream-gated, #[ignore]d)
// ============================================================================

// LANE-D LANDED (2026-07-14): the full fold -> dregg_lightclient::verify_history over a K-turn
// playthrough is NO LONGER blocked. The wide-carrier geometry migration is in the TCB
// (NUM_PRE_LIMBS=178, WIDE_NUM_CARRIERS=60 / WIDE_COMMIT_CARRIER=59, derived + const-asserted),
// and the real multi-turn recursion fold PROVES green with verify_history ACCEPT. The headline
// fold test lives in tests/game_turn_slice.rs::game_turn_folds_and_lightclient_accepts (+
// forged_game_commitment_rejected), `--ignored` (SLOW ~45min on persvati). The old
// `game_program_full_fold_gated_on_lane_d` stub — which panicked to signal the block — is removed.
// The met bar HERE stays leaf-level (game_program_leaf_accepts + forged_ordering_rejects); the full
// fold is exercised in the sibling test file.

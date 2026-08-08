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
    // ⚑ THE HEADS ARE COMPUTED, NOT RETYPED. Until 2026-08-08 the three sign checks below read
    // `contains(&9)`, `contains(&1)` and `assert!(3i128 - 5i128 < 0)` — literals standing in for
    // the heads, so the range legs re-checked two numbers this file had typed and the FORGED leg
    // was `-2 < 0`, a statement with no free variable at all. It could not have gone red for any
    // assignment, including one where the forged level went UP. `assertions_on_constants` was
    // printing it, at warn level, in every build.
    let honest_gte_head = honest.new_slots[&SLOT_HP] as i128 - HP_FLOOR as i128;
    let honest_mono_head =
        honest.new_slots[&SLOT_LEVEL] as i128 - honest.old_slots[&SLOT_LEVEL] as i128;
    assert_eq!(honest_gte_head, 9, "FieldGte head = new[HP] - floor");
    assert_eq!(
        honest_mono_head, 1,
        "Monotonic head = new[LEVEL] - old[LEVEL]"
    );
    // Both honest heads are ≥ 0 and < 2^RANGE_BITS, so both recompose.
    let window = 0..(1i128 << RANGE_BITS);
    assert!(window.contains(&honest_gte_head));
    assert!(window.contains(&honest_mono_head));

    // …and the FORGED head is negative, computed from the same forgery
    // `forged_ordering_rejects` drives through the prover (level DECREASES 5 → 3).
    let forged_mono = SlotAssignment::new()
        .set_new(SLOT_HP, 10)
        .set_new(SLOT_LEVEL, 3)
        .set_old(SLOT_LEVEL, 5)
        .set_new(SLOT_ALIVE, 1)
        .set_new(SLOT_SCORE, 120)
        .set_old(SLOT_SCORE, 100)
        .set_new(SLOT_POINTS, 20)
        .set_new(SLOT_SCENE, SCENE_ID);
    let forged_mono_head =
        forged_mono.new_slots[&SLOT_LEVEL] as i128 - forged_mono.old_slots[&SLOT_LEVEL] as i128;
    assert!(
        forged_mono_head < 0,
        "the forged Monotonic head must be NEGATIVE (⇒ no {RANGE_BITS}-bit recomposition); got \
         {forged_mono_head}"
    );
    assert!(!window.contains(&forged_mono_head));
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

// ============================================================================
// PART 4 — THE Witnessed { MerkleMembership } HIDDEN-HAND TOOTH → A FOLDABLE LEAF
//
// Phase 3 of multiway-tug: the executor's hidden-hand membership tooth
// (`StateConstraint::Witnessed { MerkleMembership }`, checked in the clear by
// `dregg_multiway_tug::hidden_hand`) lowers to its OWN foldable custom leaf via
// `lower_witnessed_merkle_membership` — the LEAN-EMITTED wide 4-ary `node8` membership
// descriptor, the SAME `node8_4ary` recurrence the clear-side verifier folds. An honest
// in-committed-hand play PROVES as a leaf; a fabricated card / tampered path is refused at
// lowering OR is UNSAT against the descriptor. The played cards NEVER enter the PIs (only
// [leaf8 | root8]) — the hand is private-in-fold.
// ============================================================================

use dregg_cell::{InputRef, WitnessedPredicate};
use dregg_circuit::membership_descriptor_4ary::{
    DIGEST_W, Digest8, absorb16, membership_root_4ary,
};
use game_turn_slice::compiler::{
    LoweredMembership, MembershipLevel, MerkleMembershipWitness, lower_witnessed_merkle_membership,
    root_digest_from_commitment,
};

/// Encode an 8-felt root as the 32-byte `Witnessed { MerkleMembership }` commitment form (the
/// exact shape `hidden_hand::root_to_bytes` / the deployed verifier use: EIGHT canonical u32
/// LE limbs filling the slot exactly).
fn root_to_commitment(root: Digest8) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, felt) in root.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&felt.as_u32().to_le_bytes());
    }
    out
}

/// A blinded 8-felt leaf commitment — the SAME `absorb16` construction `hidden_hand::card_leaf`
/// uses (kept local so this crate does not depend on multiway-tug).
fn card_leaf(card_id: u64, nonce: u64) -> Digest8 {
    let limbs = |v: u64| {
        [
            BabyBear::new_canonical((v & ((1u64 << 30) - 1)) as u32),
            BabyBear::new_canonical(((v >> 30) & ((1u64 << 30) - 1)) as u32),
            BabyBear::new_canonical((v >> 60) as u32),
        ]
    };
    let mut pre = [BabyBear::ZERO; DIGEST_W];
    pre[0] = BabyBear::new_canonical(0x6d746c66);
    pre[1..4].copy_from_slice(&limbs(card_id));
    pre[4..7].copy_from_slice(&limbs(nonce));
    absorb16(&pre, &[BabyBear::ZERO; DIGEST_W])
}

/// Build an honest depth-2 (4^2 = 16-leaf) `node8` membership witness + the tooth that commits
/// its root — the exact 4-ary shape multiway-tug's `HandTree` (HAND_TREE_DEPTH = 2) produces.
/// Returns `(wp, witness)`.
fn honest_membership() -> (WitnessedPredicate, MerkleMembershipWitness) {
    let leaf = card_leaf(7, 4242);
    let sib = |base: u32| -> Digest8 { core::array::from_fn(|k| BabyBear::new(base + k as u32)) };
    let levels = vec![
        MembershipLevel {
            position: 1,
            siblings: [sib(11), sib(112), sib(213)],
        },
        MembershipLevel {
            position: 3,
            siblings: [sib(321), sib(422), sib(523)],
        },
    ];
    let siblings: Vec<[Digest8; 3]> = levels.iter().map(|l| l.siblings).collect();
    let positions: Vec<u8> = levels.iter().map(|l| l.position).collect();
    let root = membership_root_4ary(leaf, &siblings, &positions);
    let wp = WitnessedPredicate::merkle_membership(
        root_to_commitment(root),
        InputRef::Witness { index: 0 },
        1,
    );
    (wp, MerkleMembershipWitness { leaf, levels, root })
}

/// The tooth lowers to a foldable leaf of the right shape (cheap): the LEAN-EMITTED wide
/// membership descriptor, sixteen PIs `[leaf8 ‖ root8]` (no cards), and a depth-2 base trace of
/// the descriptor's own width.
///
/// ⚑ It used to lower to the Rust circuit-DSL `merkle_poseidon2_descriptor` — 13 columns, TWO
/// PIs, one felt of leaf and one felt of root. That node was `hash_4_to_1` truncated to
/// `state[0]`: ~31 bits, birthday-collided in 2^15.5, so a second authentication path to the
/// same committed hand root existed for a card never dealt. There is no Rust AIR on this path
/// any more.
#[test]
fn witnessed_membership_lowers_to_foldable_leaf() {
    let (wp, witness) = honest_membership();
    let LoweredMembership {
        descriptor,
        base_trace,
        num_rows,
        public_inputs,
    } = lower_witnessed_merkle_membership(&wp, &witness).expect("honest play lowers");

    assert_eq!(num_rows, 2, "depth-2 hand tree ⇒ a 2-row membership trace");
    let mut expect: Vec<BabyBear> = witness.leaf.to_vec();
    expect.extend_from_slice(&witness.root);
    assert_eq!(
        public_inputs, expect,
        "the PIs are [leaf8 ‖ root8] — the played cards are NOT in the proof (private-in-fold)"
    );
    assert_eq!(public_inputs.len(), 16);
    assert_eq!(
        descriptor.public_input_count,
        public_inputs.len(),
        "the leaf publishes exactly the emitted descriptor's PIs"
    );
    // The AIR is the Lean-emitted artifact, by name — not a Rust-built descriptor.
    assert_eq!(
        descriptor.name,
        "dregg-merkle-membership-4ary-wide-general::v1"
    );
    assert_eq!(base_trace.len(), 2, "one row per Merkle level");
    assert_eq!(base_trace[0].len(), descriptor.trace_width);
    assert_eq!(descriptor.trace_width, 90, "the WIDE node8 layout");
    eprintln!(
        "MEMBERSHIP LEAF: Witnessed{{MerkleMembership}} lowered onto the Lean-emitted {} — \
         PIs=[leaf8‖root8] (no cards), {} IR-v2 constraints, {} trace columns.",
        descriptor.name,
        descriptor.constraints.len(),
        descriptor.trace_width
    );
}

/// The lowering is NON-VACUOUS (cheap): a wrong committed root, a tampered path that no
/// longer climbs to the root, and a non-MerkleMembership kind are each REFUSED.
#[test]
fn witnessed_membership_lowering_is_non_vacuous() {
    let (wp, witness) = honest_membership();

    // (1) A tooth whose committed root disagrees with the witness root is refused — in ANY
    // lane, not just lane 0 (which is the whole of what the retired encoding committed).
    for lane in 0..DIGEST_W {
        let mut wrong = witness.clone();
        wrong.root[lane] += BabyBear::ONE;
        assert!(
            lower_witnessed_merkle_membership(&wp, &wrong).is_err(),
            "a committed-root ≠ witness-root mismatch in lane {lane} must refuse"
        );
    }

    // (2) A fabricated play: corrupt a sibling so the path no longer climbs to the committed
    // root (leaf/root PIs unchanged) — refused (Poseidon2 collision-resistance). EVERY lane of
    // a co-path node is load-bearing, including the seven the one-felt fold discarded.
    for lane in 0..DIGEST_W {
        let mut tampered = witness.clone();
        tampered.levels[0].siblings[0][lane] += BabyBear::ONE;
        assert!(
            lower_witnessed_merkle_membership(&wp, &tampered).is_err(),
            "a lane-{lane}-only sibling change must refuse — the one-felt fold saw only lane 0"
        );
    }

    // (1b) A NON-CANONICAL committed root is refused, never reduced into an alias.
    let mut noncanonical = wp.clone();
    noncanonical.commitment[0..4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(
        lower_witnessed_merkle_membership(&noncanonical, &witness).is_err(),
        "a non-canonical root limb must refuse"
    );
    assert_eq!(root_digest_from_commitment(&noncanonical.commitment), None);

    // (3) A non-MerkleMembership predicate is refused.
    let dfa = WitnessedPredicate::dfa(wp.commitment, InputRef::Witness { index: 0 }, 1);
    assert!(
        lower_witnessed_merkle_membership(&dfa, &witness).is_err(),
        "only MerkleMembership lowers to the Poseidon2 membership leaf"
    );

    // The honest one still lowers (the negatives are the lie, not collateral).
    assert!(lower_witnessed_merkle_membership(&wp, &witness).is_ok());
}

/// **THE PI-BINDING FIX — a published output is CONSTRAINED, not merely committed.** The demo
/// `build_game_program` publishes `[score, level]` as BARE public inputs (`with_public_inputs(2)`):
/// the in-circuit PI-commitment covers them, but NOTHING pins them to the trace, so a prover could
/// publish any score for the same constrained transition. `bind_public_input` cures this — it emits
/// a real `ConstraintExpr::PiBinding` tying the published PI to the constrained `new`-side slot
/// column, which the custom-leaf adapter lowers to `Base(PiBinding{First,..})` (the validated
/// foldable path). So "this turn published score = X" becomes "X is exactly what the constrained
/// transition produced" — the structural cure for `boundaries: vec![]`.
#[test]
fn bind_public_input_constrains_a_published_output() {
    let mut c = GameProgramCompiler::new("pi-binding-fix", RANGE_BITS);
    // A StrictMonotonic score tooth constrains SLOT_SCORE in the trace (new > old)...
    c.lower_state_constraint(&StateConstraint::StrictMonotonic { index: SLOT_SCORE })
        .expect("StrictMonotonic lowers via the range gadget");
    // ...and binding it publishes THAT constrained column as PI 0 (not a free value).
    let pi_index = c.bind_public_input(SLOT_SCORE);
    assert_eq!(pi_index, 0, "the first bound PI rides slot 0");

    let program = c.finish();
    assert_eq!(
        program.descriptor.public_input_count, 1,
        "one bound public input"
    );
    let bindings = program
        .descriptor
        .constraints
        .iter()
        .filter(|k| {
            matches!(
                k,
                ConstraintExpr::PiBinding {
                    col: _,
                    pi_index: 0
                }
            )
        })
        .count();
    assert_eq!(
        bindings, 1,
        "exactly one PiBinding pins the published output to its constrained trace column"
    );

    // The REAL custom-leaf adapter carries it into a genuine IR-v2 PI binding (the foldable path).
    let desc2 = cellprogram_to_descriptor2(&program)
        .expect("a PiBinding-bearing game program lowers through the real custom-leaf adapter");
    assert_eq!(desc2.public_input_count, 1);
    assert!(
        desc2
            .constraints
            .iter()
            .any(|k| format!("{k:?}").contains("PiBinding")),
        "the adapter must lower the binding to an IR-v2 PiBinding constraint"
    );
    eprintln!(
        "PI-BINDING FIX: a StrictMonotonic-constrained score is bind_public_input'd → a real \
         ConstraintExpr::PiBinding → IR-v2 Base(PiBinding) via the adapter. Published == derived."
    );
}

/// THE POSITIVE POLE: an honest in-committed-hand play PROVES against the LEAN-EMITTED
/// membership descriptor and VERIFIES through the deployed `verify_vm_descriptor2`, binding
/// the sixteen `[leaf8 ‖ root8]` PIs. The played cards are not among them — the membership is
/// proven while the hand stays private.
///
/// ⚑ This ran through `prove_custom_leaf_with_commitment` on the Rust circuit-DSL descriptor
/// and cost minutes (it was `#[ignore]`d). The lowering is descriptor-backed now, so the pole
/// is the base descriptor prove — fast enough to run on every `cargo test`, which is where a
/// soundness pole belongs.
#[test]
fn witnessed_membership_proves_and_verifies_on_the_emitted_descriptor() {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
    };

    let (wp, witness) = honest_membership();
    let leaf = lower_witnessed_merkle_membership(&wp, &witness).expect("honest play lowers");

    let proof = prove_vm_descriptor2(
        &leaf.descriptor,
        &leaf.base_trace,
        &leaf.public_inputs,
        &MemBoundaryWitness::default(),
        &[],
    )
    .expect("the honest hidden-hand play must prove against the emitted membership descriptor");
    verify_vm_descriptor2(&leaf.descriptor, &proof, &leaf.public_inputs)
        .expect("the honest membership proof must verify through the deployed verifier");

    // The host PI commitment the fold would bind is taken over all sixteen PIs.
    let host = custom_proof_pi_commitment(&leaf.public_inputs);
    assert_ne!(host, [BabyBear::ZERO; 8]);
    eprintln!(
        "MEMBERSHIP LEAF ACCEPT: an in-committed-hand play PROVED + VERIFIED on {}; \
         PIs=[leaf8‖root8] (no cards), host binding {:?}",
        leaf.descriptor.name,
        host.map(|f| f.0)
    );
}

/// THE NEGATIVE POLE: a FABRICATED-card leaf — the honest lowering's BASE TRACE corrupted at a
/// co-path sibling AFTER lowering (so the row's arity-16 `node8` chip lookups and the root PI
/// pins no longer hold) — has NO satisfying assembly: it does not prove, or the proof it
/// produces does not verify. A fabricated card is normally refused at lowering; this drives the
/// in-circuit soundness bite directly.
///
/// It perturbs the HIGH lane of a sibling group as well as the low one. The retired one-felt
/// AIR could not represent a high-lane change at all, so this negative is the widened tooth.
#[test]
fn forged_membership_play_does_not_prove() {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use dregg_circuit::membership_descriptor_4ary::SIB0;

    let (wp, witness) = honest_membership();
    let leaf = lower_witnessed_merkle_membership(&wp, &witness).expect("honest play lowers");

    for lane in [0usize, DIGEST_W - 1] {
        // FORGE: move one sibling felt in the retained trace WITHOUT recomputing the level's
        // children/stage digests/parent — the chip lookups have no serving row, and the PIs
        // still claim the honest leaf/root, so no witness satisfies the descriptor.
        let mut trace = leaf.base_trace.clone();
        trace[0][SIB0 + lane] += BabyBear::ONE;

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let proof = prove_vm_descriptor2(
                &leaf.descriptor,
                &trace,
                &leaf.public_inputs,
                &MemBoundaryWitness::default(),
                &[],
            )?;
            verify_vm_descriptor2(&leaf.descriptor, &proof, &leaf.public_inputs)
        }));
        match result {
            Err(_) | Ok(Err(_)) => {}
            Ok(Ok(())) => panic!(
                "a FABRICATED-card membership play (sibling lane {lane} moved) minted a \
                 VERIFYING proof — hidden-hand soundness OPEN"
            ),
        }
    }
    eprintln!(
        "MEMBERSHIP LEAF REJECT: a fabricated-card play (corrupted sibling, low AND high lane) \
         had no satisfying witness — the arity-16 node8 chip lookups / root pins bit."
    );
}

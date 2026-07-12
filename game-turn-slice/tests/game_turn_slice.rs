//! # THE D-CROWN DE-RISK VERTICAL SLICE (driven, not named).
//!
//! GOAL: prove, on ONE real turn, that a game's rules-as-a-`CellProgram` become a real
//! circuit-proven turn verified by the real recursive-fold light client
//! ([`dregg_lightclient::verify_history`]) re-witnessing nothing — and report HONESTLY
//! which of the game's constraint teeth lower onto this path today vs need new lowering.
//!
//! ## The two-language reality (the core de-risk finding)
//!
//! A game's *rules* are the executor referee `dregg_cell::program::CellProgram`
//! (`StateConstraint` teeth: `FieldGte`, `FieldLte`, `WriteOnce`, `Monotonic`,
//! `StrictMonotonic`, `FieldLteField`, `FieldDelta`, `SumEquals`). The circuit adapter
//! `cellprogram_to_descriptor2` does NOT consume that type — it consumes the SEPARATE
//! circuit-DSL `dregg_circuit::dsl::circuit::CellProgram` (a `CircuitDescriptor` of
//! `ConstraintExpr`). There is NO compiler between them in-tree (verified: no
//! `StateConstraint -> ConstraintExpr` bridge exists). So a game rule reaches the crown
//! ONLY by being HAND-AUTHORED as a `ConstraintExpr` circuit — the "scene → CellProgram
//! compiler" the plan (Phase D / Phase A) names as real substance.
//!
//! ## Part 1 — the teeth-lowering probe (cheap, always runs)
//!
//! `TEETH` drives `cellprogram_to_descriptor2` on the circuit encoding of each game
//! tooth and prints a table of lowered/REFUSED (+ the exact blocker). Verdict there:
//! arithmetic/equality/boolean/exact-transition teeth lower; the ORDERING teeth
//! (`FieldGte`/`FieldLte`/`Monotonic`/`StrictMonotonic`) have NO comparison primitive in
//! the DSL — their faithful single-atom encoding is a range `Lookup`, which is REFUSED —
//! so an HP-floor / scene-ratchet needs a hand-authored bit-decomposition range gadget
//! (which DOES lower — shown by `hp_floor_via_bits`). That is lowering WORK, not a wall.
//!
//! ## Part 2 — the crown, end-to-end (heavy, #[ignore])
//!
//! `game_turn_folds_and_lightclient_accepts` builds a real combat `CellProgram` (damage
//! conservation + an alive boolean), proves it as a foldable custom leaf, binds it to a
//! `Custom`-effect `FinalizedTurn`, folds a K=2 chain via `prove_turn_chain_recursive`,
//! and `verify_history` ACCEPTS — then a relabeled `final_root` is REJECTED.
//! `forged_game_commitment_rejected` shows a leg claiming a commitment no verifying
//! sub-proof backs produces NO root (the deployed binding bites).
//!
//! The heavy teeth are a real recursion fold (minutes) — `#[ignore]`. Run with:
//!   cargo test -p game-turn-slice --test game_turn_slice -- --ignored --nocapture

use std::collections::HashMap;

use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2;

// ============================================================================
// PART 1 — THE TEETH-LOWERING PROBE (cheap, always runs)
// ============================================================================

/// Wrap a bare constraint list into a `CellProgram` with `width` value columns so
/// `cellprogram_to_descriptor2` can lower it. (The adapter reads only the constraint
/// kinds + `trace_width`; column bounds are not checked here — this is a lowering probe,
/// not a prove.)
fn probe_program(name: &str, width: usize, constraints: Vec<ConstraintExpr>) -> CellProgram {
    let columns = (0..width)
        .map(|i| ColumnDef {
            name: format!("c{i}"),
            index: i,
            kind: ColumnKind::Value,
        })
        .collect();
    CellProgram::new(
        CircuitDescriptor {
            name: name.to_string(),
            trace_width: width,
            max_degree: 4,
            columns,
            constraints,
            boundaries: vec![],
            public_input_count: 2,
            lookup_tables: vec![],
        },
        1,
    )
}

/// `p - 1` as the field's faithful `-1`.
fn neg_one() -> BabyBear {
    BabyBear::new(BABYBEAR_P - 1)
}

/// THE TEETH-LOWERING TABLE. Each row is (a game rule, its circuit encoding, whether we
/// expect it to LOWER). Drives `cellprogram_to_descriptor2` and asserts the polarity,
/// printing the exact blocker for the refused ones. This is the primary de-risk output.
#[test]
fn teeth_lowering_table() {
    // (game rule, tooth-name, circuit encoding, expect_lowers)
    struct Row {
        rule: &'static str,
        game_tooth: &'static str,
        program: CellProgram,
        expect_lowers: bool,
    }

    let rows = vec![
        // ---- teeth that LOWER (arithmetic / equality / boolean / cross-row) ----
        Row {
            rule: "combat: hp_new = hp_old - dmg (damage conservation)",
            game_tooth: "SumEquals / FieldDelta",
            // hp_new - hp_old + dmg == 0  (cols old=0, dmg=1, new=2)
            program: probe_program(
                "damage-conservation",
                3,
                vec![ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![2],
                        },
                        PolyTerm {
                            coeff: neg_one(),
                            col_indices: vec![0],
                        },
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![1],
                        },
                    ],
                }],
            ),
            expect_lowers: true,
        },
        Row {
            rule: "combat: alive in {0,1}",
            game_tooth: "boolean flag",
            program: probe_program("alive-flag", 1, vec![ConstraintExpr::Binary { col: 0 }]),
            expect_lowers: true,
        },
        Row {
            rule: "scene: staged_scene == committed_scene (exact set)",
            game_tooth: "FieldEquals (exact write)",
            program: probe_program(
                "exact-set",
                2,
                vec![ConstraintExpr::Equality { col_a: 0, col_b: 1 }],
            ),
            expect_lowers: true,
        },
        Row {
            rule: "scene: cross-row continuity (next.cursor == cur.cursor)",
            game_tooth: "transition carry",
            program: probe_program(
                "cross-row-carry",
                2,
                vec![ConstraintExpr::Transition {
                    next_col: 0,
                    local_col: 1,
                }],
            ),
            expect_lowers: true,
        },
        Row {
            rule: "HP floor hp>=0 via a HAND-AUTHORED 4-bit range gadget",
            game_tooth: "FieldGte (lowered as bit-decomp)",
            // 4 boolean bits + a reconstruction poly: diff - (b0 + 2b1 + 4b2 + 8b3) == 0.
            // cols: diff=0, b0=1, b1=2, b2=3, b3=4.
            program: probe_program(
                "hp-floor-via-bits",
                5,
                vec![
                    ConstraintExpr::Binary { col: 1 },
                    ConstraintExpr::Binary { col: 2 },
                    ConstraintExpr::Binary { col: 3 },
                    ConstraintExpr::Binary { col: 4 },
                    ConstraintExpr::Polynomial {
                        terms: vec![
                            PolyTerm {
                                coeff: BabyBear::ONE,
                                col_indices: vec![0],
                            },
                            PolyTerm {
                                coeff: neg_one(),
                                col_indices: vec![1],
                            },
                            PolyTerm {
                                coeff: BabyBear::new(BABYBEAR_P - 2),
                                col_indices: vec![2],
                            },
                            PolyTerm {
                                coeff: BabyBear::new(BABYBEAR_P - 4),
                                col_indices: vec![3],
                            },
                            PolyTerm {
                                coeff: BabyBear::new(BABYBEAR_P - 8),
                                col_indices: vec![4],
                            },
                        ],
                    },
                ],
            ),
            expect_lowers: true,
        },
        // ---- teeth that are REFUSED (need new lowering) ----
        Row {
            rule: "HP floor hp>=min via a range Lookup (the naive FieldGte encoding)",
            game_tooth: "FieldGte (as range Lookup)",
            program: probe_program(
                "hp-floor-via-lookup",
                1,
                vec![ConstraintExpr::Lookup {
                    table_id: "u16-range".to_string(),
                    query_columns: vec![0],
                }],
            ),
            expect_lowers: false,
        },
        Row {
            rule: "scene ratchet new>=old via range Lookup on the delta (Monotonic)",
            game_tooth: "Monotonic / StrictMonotonic (as range Lookup)",
            program: probe_program(
                "monotonic-via-lookup",
                1,
                vec![ConstraintExpr::Lookup {
                    table_id: "nonneg-range".to_string(),
                    query_columns: vec![0],
                }],
            ),
            expect_lowers: false,
        },
        Row {
            rule: "event: bind narration fact into state (fact-sponge)",
            game_tooth: "Hash (capacity-tagged fact-sponge)",
            program: probe_program(
                "event-factsponge",
                3,
                vec![ConstraintExpr::Hash {
                    output_col: 0,
                    input_cols: vec![1, 2],
                }],
            ),
            expect_lowers: false,
        },
        Row {
            rule: "inventory: 8-felt Merkle loot-tree node",
            game_tooth: "MerkleHash8 (native 8-felt cap_node8)",
            program: probe_program(
                "loot-merkle8",
                24,
                vec![ConstraintExpr::MerkleHash8 {
                    output_cols: [0, 1, 2, 3, 4, 5, 6, 7],
                    left_cols: [8, 9, 10, 11, 12, 13, 14, 15],
                    right_cols: [16, 17, 18, 19, 20, 21, 22, 23],
                }],
            ),
            expect_lowers: false,
        },
        Row {
            rule: "replay: unseeded running-hash chain",
            game_tooth: "ChainedHash2to1 (no paired seed)",
            program: probe_program(
                "unseeded-chain",
                3,
                vec![ConstraintExpr::ChainedHash2to1 {
                    output_next_col: 0,
                    seed_local_col: 1,
                    input_next_col: 2,
                }],
            ),
            expect_lowers: false,
        },
    ];

    eprintln!(
        "\n================ TEETH-LOWERING TABLE (driven cellprogram_to_descriptor2) ================"
    );
    let mut lowered = 0usize;
    let mut refused = 0usize;
    for r in &rows {
        let res = cellprogram_to_descriptor2(&r.program);
        match (&res, r.expect_lowers) {
            (Ok(desc), true) => {
                lowered += 1;
                eprintln!(
                    "  LOWERS  | {:<40} | {:<38} | {} constraints",
                    r.game_tooth,
                    r.rule,
                    desc.constraints.len()
                );
            }
            (Err(blocker), false) => {
                refused += 1;
                eprintln!(
                    "  REFUSED | {:<40} | {:<38}\n            blocker: {}",
                    r.game_tooth, r.rule, blocker
                );
            }
            (Ok(_), false) => panic!(
                "tooth `{}` was expected to be REFUSED but lowered — the probe is stale",
                r.game_tooth
            ),
            (Err(e), true) => panic!(
                "tooth `{}` was expected to LOWER but was refused: {e}",
                r.game_tooth
            ),
        }
    }
    eprintln!(
        "========================================================================================"
    );
    eprintln!("  {lowered} teeth lower, {refused} teeth refused (need new lowering).\n");
    assert_eq!(
        lowered, 5,
        "the arithmetic/equality/boolean/transition/bit-decomp teeth lower"
    );
    assert_eq!(
        refused, 5,
        "the two range-Lookup / fact-sponge / merkle8 / unseeded-chain teeth are refused"
    );
}

// ============================================================================
// PART 2 — THE CROWN, END TO END (heavy, #[ignore])
//
// The fixtures mirror the audited deployed-custom-binding pattern
// (`circuit-prove/tests/custom_binding_deployed_tooth.rs`), specialized to a GAME
// program: a combat turn whose rule is damage conservation + an alive boolean.
// ============================================================================

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, prove_vm_descriptor2_for_config};
use dregg_circuit::effect_vm::trace_rotated::{
    NUM_PRE_LIMBS, RotatedBlockWitness, WIDE_COMMIT_CARRIER, WIDE_NUM_CARRIERS,
    empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
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

/// THE GAME `CellProgram` — a combat turn's referee, authored in the circuit DSL:
///   * `hp_new - hp_old + dmg == 0`  (damage conservation — the `SumEquals`/`FieldDelta` tooth)
///   * `alive in {0,1}`              (a boolean flag — the `Binary` tooth)
/// cols: hp_old=0, dmg=1, hp_new=2, alive=3. PIs: [hp_old, hp_new].
fn combat_program() -> CellProgram {
    let descriptor = CircuitDescriptor {
        name: "dregg-game-combat-v1".to_string(),
        trace_width: 4,
        max_degree: 2,
        columns: vec![
            ColumnDef {
                name: "hp_old".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "dmg".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "hp_new".into(),
                index: 2,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "alive".into(),
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
                        coeff: neg_one(),
                        col_indices: vec![0],
                    },
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![1],
                    },
                ],
            },
        ],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };
    CellProgram::new(descriptor, 1)
}

/// Honest combat witness: hp_old=20, dmg=5 => hp_new=15, alive=1 (constant across rows).
fn combat_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
    let rows = 4;
    let mut w = HashMap::new();
    w.insert("hp_old".into(), vec![BabyBear::new(20); rows]);
    w.insert("dmg".into(), vec![BabyBear::new(5); rows]);
    w.insert("hp_new".into(), vec![BabyBear::new(15); rows]);
    w.insert("alive".into(), vec![BabyBear::new(1); rows]);
    (w, rows)
}

/// The combat program's public inputs (the commitment preimage): [hp_old, hp_new].
fn combat_pis() -> Vec<BabyBear> {
    vec![BabyBear::new(20), BabyBear::new(15)]
}

fn honest_bundle() -> CustomWitnessBundle {
    let (w, rows) = combat_witness();
    CustomWitnessBundle {
        program: combat_program(),
        witness_values: w,
        num_rows: rows,
        public_inputs: combat_pis(),
    }
}

/// Mint a REAL `customVmDescriptor2R24` wide leg whose claimed `custom_proof_commitment`
/// (IR2 PI 46..53, the 8-felt flag-day shape) is `commit`; Custom bumps nonce by 1, balance unchanged. Optionally
/// attach the prover-side `bundle` the deployed chain prover re-proves + binds.
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
        "custom leg PI vector must carry the 8-felt commitment slice at 46..53"
    );
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

/// A trailing plain custom turn (no bundle) so the chain has >= 2 turns and links.
fn plain_custom_turn(balance: i64, nonce: u64) -> FinalizedTurn {
    let commit = [
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(3),
        BabyBear::new(4),
        BabyBear::new(5),
        BabyBear::new(6),
        BabyBear::new(7),
        BabyBear::new(8),
    ];
    let leg = mint_custom_leg(balance, nonce, commit, None);
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// Build the K=2 chain: turn 0 is the bundled combat turn claiming `commit`; turn 1 is a
/// plain custom turn linking off turn 0's post-state `(b, nonce+1)`.
fn build_chain(commit: [BabyBear; 8]) -> Vec<FinalizedTurn> {
    let balance = 1000i64;
    let t0_leg = mint_custom_leg(balance, 0, commit, Some(honest_bundle()));
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    let t1 = plain_custom_turn(balance, 1);
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "combat turn 0's post-state must link to turn 1"
    );
    vec![t0, t1]
}

// ============================================================================
// THE WIDE-CARRIER GEOMETRY GATE (the exact Lane D block, DRIVEN)
//
// The full multi-turn fold (`game_turn_folds_and_lightclient_accepts`) routes each
// game turn's `Custom` leg through `generate_rotated_effect_vm_descriptor_and_trace_wide`,
// which lays a wide 8-felt commitment chain over the rotated block's `NUM_PRE_LIMBS`
// pre-iroot limbs. That chain's length is a FIXED FUNCTION of `NUM_PRE_LIMBS`:
//
//   carriers(L) = 1 (arity-4 head)                         // limbs 0..3
//               + full3 + rem  (arity-11 body groups)      // limbs 4..L, 3 at a time,
//                                                           //   leftovers 1 at a time
//               + 1 (arity-11 iroot-final carrier)
//     where  full3 = (L - 4) / 3 ,  rem = (L - 4) % 3
//
// `fill_wide_block` asserts the final carrier index == `WIDE_COMMIT_CARRIER`
// (= `WIDE_NUM_CARRIERS - 1`). So the invariant the fold REQUIRES is:
//
//     WIDE_NUM_CARRIERS == carriers(NUM_PRE_LIMBS)
//
// This is entirely a `circuit/` (Lane D) constant relationship — game-turn-slice only
// CALLS the wide generator; it cannot change the carrier count. When Lane D's
// revoked-root base widen bumped NUM_PRE_LIMBS 169 -> 178 it did NOT re-derive the wide
// carrier constants, so the invariant is currently BROKEN and the fold panics deep inside
// `fill_wide_block` ("wide chain must end on carrier 56"). This section makes that block
// EXPLICIT + self-updating: the guard characterizes it at the top of the fold tests, and
// the tripwire census fires GREEN while blocked and RED the moment Lane D lands the fix.

/// The wide-commitment-chain carrier count for `L` pre-iroot limbs — the exact shape
/// `fill_wide_block` lays (head + 3-at-a-time body with 1-at-a-time leftovers + iroot-final).
fn required_wide_carriers(l: usize) -> usize {
    let body = (l - 4) / 3 + (l - 4) % 3;
    1 + body + 1
}

/// Is the deployed wide-carrier geometry internally consistent with `NUM_PRE_LIMBS`? When
/// this is `true`, the game-turn-slice fold wiring below runs UNCHANGED; when `false`, the
/// fold is upstream-blocked on Lane D's carrier migration and the guarded tests characterize
/// exactly the violation instead of panicking deep in `fill_wide_block`.
fn wide_geometry_consistent() -> bool {
    let required = required_wide_carriers(NUM_PRE_LIMBS);
    WIDE_NUM_CARRIERS == required && WIDE_COMMIT_CARRIER == required - 1
}

/// The precise, evidenced characterization of the current Lane D block (numbers computed
/// from the live constants, not narrated). Panics from inside the guarded fold tests so a
/// `--ignored` run shows the exact violation at the TOP of the stack, not the raw
/// `fill_wide_block` debug-assert; auto-clears (guard returns, fold proceeds) once Lane D
/// re-derives the wide carrier constants.
fn gate_full_fold_on_geometry() {
    if wide_geometry_consistent() {
        return;
    }
    let required = required_wide_carriers(NUM_PRE_LIMBS);
    panic!(
        "FULL-FOLD BLOCKED on Lane D wide-carrier geometry (game-turn-slice side is correct \
         and needs NO change):\n\
         \x20 NUM_PRE_LIMBS            = {NUM_PRE_LIMBS}\n\
         \x20 required carriers        = {required}  (1 head + {} body + 1 iroot-final)\n\
         \x20 WIDE_NUM_CARRIERS (decl) = {WIDE_NUM_CARRIERS}\n\
         \x20 WIDE_COMMIT_CARRIER      = {WIDE_COMMIT_CARRIER}  (fill_wide_block ends on carrier {})\n\
         The wide commitment chain over {NUM_PRE_LIMBS} limbs ends on carrier {}, but the frozen \
         constants declare {WIDE_NUM_CARRIERS}/{WIDE_COMMIT_CARRIER} (the 169-limb geometry). \
         Lane D must re-derive WIDE_NUM_CARRIERS -> {required} and WIDE_COMMIT_CARRIER -> {}; \
         then this gate clears and the fold below runs unchanged.",
        required - 2,
        required - 1,
        required - 1,
        required - 1,
    );
}

/// TRIPWIRE (cheap, always runs): asserts the wide-carrier geometry is CURRENTLY
/// inconsistent with `NUM_PRE_LIMBS`. This is the honest, driven record of the Lane D block
/// — it reads the live constants, computes the required carrier count, and prints the
/// census. It is GREEN while the fold is blocked and flips RED the instant Lane D re-derives
/// the constants, which is the signal to un-`#[ignore]` the full-fold headline.
#[test]
fn wide_carrier_geometry_tripwire() {
    let required = required_wide_carriers(NUM_PRE_LIMBS);
    eprintln!(
        "\n=============== WIDE-CARRIER GEOMETRY CENSUS (driven from live constants) ===============\n\
         \x20 NUM_PRE_LIMBS            = {NUM_PRE_LIMBS}\n\
         \x20 required carriers        = {required}\n\
         \x20 WIDE_NUM_CARRIERS (decl) = {WIDE_NUM_CARRIERS}\n\
         \x20 WIDE_COMMIT_CARRIER      = {WIDE_COMMIT_CARRIER}\n\
         \x20 consistent               = {}\n\
         ========================================================================================\n",
        wide_geometry_consistent(),
    );
    assert!(
        !wide_geometry_consistent(),
        "Lane D wide-carrier migration LANDED (WIDE_NUM_CARRIERS now == {required}). \
         The full-fold block is CLEARED: un-#[ignore] `game_turn_folds_and_lightclient_accepts` \
         + `forged_game_commitment_rejected` (they now run the real game playthrough through \
         verify_history) and delete this tripwire."
    );
}

/// THE REAL-PROVING BOUNDARY (runnable in THIS tree — no rotated-witness path): the
/// combat `CellProgram` lowers via `cellprogram_to_descriptor2` and PROVES as a real
/// foldable recursion leaf through `prove_custom_leaf_with_commitment`, and the leaf's
/// IN-CIRCUIT-exposed 4-felt commitment is byte-identical to the host
/// `custom_proof_pi_commitment(pis)` — i.e. the game rule becomes exactly the foldable,
/// commitment-bound artifact the light client's recursion fold consumes. A pure light
/// client folding this leaf witnesses the binding. (Real proving; ~tens of seconds.)
#[test]
#[ignore = "SLOW: real leaf prove + in-circuit commitment expose (~tens of seconds); run with --ignored"]
fn game_rule_proves_as_foldable_leaf_with_bound_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };

    let program = combat_program();
    let (w, rows) = combat_witness();
    let pis = combat_pis();
    let config = ir2_leaf_wrap_config();

    // Real proving: the honest combat transition MUST prove as a foldable leaf.
    let output = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        .expect("the honest combat CellProgram must prove as a commitment-exposing foldable leaf");

    // The in-circuit-exposed commitment is byte-identical to the host binding — the value
    // the deployed effect-vm Custom row's `custom_proof_commitment` column must equal.
    let exposed = read_exposed_pi_commitment(&output).expect("leaf exposes a 4-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "the in-circuit commitment must byte-match the host WideHash binding"
    );
    eprintln!(
        "D-CROWN LEAF: combat CellProgram PROVED as a foldable leaf; in-circuit commitment == host binding {:?}",
        host.map(|f| f.0)
    );
}

/// THE NEGATIVE POLE (runnable): a FORGED combat transition (hp_new claims 16 where
/// conservation forces 15) has no satisfying assembly — the leaf does NOT prove. Real
/// proving; the unsatisfiable conservation gate makes the artifact impossible.
#[test]
#[ignore = "SLOW: real leaf prove attempt (~tens of seconds); run with --ignored"]
fn forged_combat_witness_does_not_prove() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;

    let program = combat_program();
    let rows = 4;
    let mut w: HashMap<String, Vec<BabyBear>> = HashMap::new();
    w.insert("hp_old".into(), vec![BabyBear::new(20); rows]);
    w.insert("dmg".into(), vec![BabyBear::new(5); rows]);
    w.insert("hp_new".into(), vec![BabyBear::new(16); rows]); // FORGED: conservation forces 15
    w.insert("alive".into(), vec![BabyBear::new(1); rows]);
    let pis = vec![BabyBear::new(20), BabyBear::new(16)];
    let config = ir2_leaf_wrap_config();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!("a FORGED combat transition minted a foldable leaf — soundness OPEN"),
    }
    eprintln!(
        "D-CROWN LEAF REJECT: a forged combat conservation had no satisfying leaf (no artifact)."
    );
}

/// THE HEADLINE: the combat `CellProgram` proves as a foldable custom leaf, binds to a
/// `Custom`-effect turn, folds a K=2 chain via `prove_turn_chain_recursive`, and the REAL
/// light client [`verify_history`] ACCEPTS at cost independent of K, re-witnessing
/// nothing — then a relabeled `final_root` is REJECTED (a non-vacuous light-client bite).
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn game_turn_folds_and_lightclient_accepts() {
    // GEOMETRY GATE: if Lane D's wide-carrier constants are stale vs NUM_PRE_LIMBS, characterize
    // the exact block at the top of the stack (instead of the raw fill_wide_block debug-assert);
    // clears automatically once Lane D re-derives the constants, and the fold below runs unchanged.
    gate_full_fold_on_geometry();

    // The honest claimed commitment IS the genuine sub-proof PI commitment.
    let real = custom_proof_pi_commitment(&combat_pis());
    let turns = build_chain(real);

    let mut whole = prove_turn_chain_recursive(&turns)
        .expect("the honest combat-bearing chain must fold through the deployed prover");

    // THE ANCHOR: a setup party self-anchors the VK fingerprint off its own honest fold
    // (exactly how an honest setup MINTS the anchor it then distributes; a remote client
    // instead calls verify_history with its CONFIGURED anchor).
    let vk = whole.root_vk_fingerprint();

    // THE LIGHT-CLIENT CHECK — re-witnessing nothing.
    let attested = verify_history(&whole, &vk)
        .expect("the REAL light client must ACCEPT the honest combat whole-chain artifact");
    assert_eq!(
        attested.num_turns, 2,
        "the attestation covers both folded turns"
    );
    eprintln!(
        "\nD-CROWN ACCEPT: combat CellProgram -> custom leaf -> fold(K=2) -> verify_history OK. \
         num_turns={}, genesis_root[0]={}, final_root[0]={}",
        attested.num_turns, attested.genesis_root[0].0, attested.final_root[0].0
    );

    // NON-VACUOUS FORGERY (verify_history bites): relabel the carried final_root; the
    // claimed-publics attestation reads the publics against the binding proof and REFUSES.
    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    let verdict = verify_history(&whole, &vk);
    assert!(
        verdict.is_err(),
        "a relabeled final_root must be REJECTED by verify_history; got {verdict:?}"
    );
    eprintln!("D-CROWN REJECT (relabel): verify_history refused a spliced final_root: {verdict:?}");
    // Restore + re-accept — the refusal was the lie, not collateral damage.
    whole.final_root = honest_final;
    verify_history(&whole, &vk).expect("the restored honest artifact verifies again");
}

/// THE DEPLOYED-BINDING BITE: a combat leg that CLAIMS a `custom_proof_commitment` no
/// verifying sub-proof of the honest PIs backs. The bundle still proves the HONEST PIs, so
/// the in-circuit `connect` to the genuine commitment is a conflict => the aggregate is
/// UNSAT => NO root. The light client never receives a verifying artifact (REJECTED).
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn forged_game_commitment_rejected() {
    gate_full_fold_on_geometry();

    let real = custom_proof_pi_commitment(&combat_pis());
    let mut forged = real;
    forged[0] = BabyBear::new((real[0].0 + 1) % BABYBEAR_P);
    assert_ne!(forged, real);

    let turns = build_chain(forged);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        Err(_) => {}     // the in-circuit connect conflict panicked the builder — rejected
        Ok(Err(_)) => {} // or the chain prover returned an error — rejected
        Ok(Ok(_)) => panic!(
            "a FORGED custom_proof_commitment folded into a verifying whole-chain artifact — \
             the deployed binding is OPEN"
        ),
    }
    eprintln!(
        "D-CROWN REJECT (forged commitment): no root produced for a leg claiming a \
               commitment no sub-proof backs."
    );
}

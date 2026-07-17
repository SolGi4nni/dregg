//! # The `.dungeon` → substrate compiler, DRIVEN on the REAL executor.
//!
//! The fixture is `attested-dm`'s hand-authored Clockwork Orchard (copied into
//! `tests/fixtures/` so this crate is self-contained; attested-dm is NOT a dep).
//! Teeth, in both polarities:
//! * port fidelity — the fixture parses to the exact room/exit/gate counts the
//!   attested-dm parser produces (hardcoded from reading the original), and the
//!   deliberately-broken fixture is refused with the dangling target NAMED;
//! * the LEGAL critical path commits real `TurnReceipt`s to the terminal room and
//!   re-verifies by replay;
//! * the ILLEGAL move (the gated exit without the key) is a real
//!   `WorldError::Refused` committing NOTHING (anti-ghost read-back);
//! * the translation-validation tooth BITES: a corrupted lowering (a dropped gate
//!   constraint / an injected phantom constraint) is refused by [`check_lowering`],
//!   never accepted;
//! * a stapled write / teleport onto a legit choice method is a real executor
//!   refusal (the augmentation is enforcement, not decoration);
//! * an unsupported construct (the Lantern Fen's `hostile`) is a NAMED
//!   `CompileError::Unsupported`, not a silent drop.

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, field_from_u64, symbol};
use dungeon_on_dregg::dsl::{
    ChoiceKind, CompileError, DUNGEON_WON_VAR, check_lowering, compile_world, parse_dungeon,
    parse_world, validate,
};
use dungeon_on_dregg::stash_effect;
use spween_dregg::{Driver, WorldError, choice_method, verify, verify_chain_linkage};

const ORCHARD: &str = include_str!("fixtures/clockwork_orchard.dungeon");
const BROKEN: &str = include_str!("fixtures/broken.dungeon");
const LANTERN_FEN: &str = include_str!("fixtures/lantern_fen.dungeon");

// ─────────────────────────────────────────────────────────────────────────────
// Port fidelity — the parser/validator behave as attested-dm's do.
// ─────────────────────────────────────────────────────────────────────────────

/// The orchard parses to EXACTLY the shape attested-dm's parser produces — counts
/// hardcoded from reading the original fixture (5 rooms; 8 exits of which 1 is
/// item-gated; 1 npc with 2 dialogue rules; 3 placed + 1 npc-granted item) — and
/// validates with zero errors (non-vacuity baseline for the refusal tests below).
#[test]
fn port_fidelity_orchard_parses_to_the_attested_dm_shape() {
    let world = parse_dungeon(ORCHARD).expect("the orchard parses");

    assert_eq!(world.rooms.len(), 5, "5 rooms");
    let exits: usize = world.rooms.values().map(|r| r.exits.len()).sum();
    assert_eq!(exits, 8, "8 exits");
    let gated: Vec<_> = world
        .rooms
        .values()
        .flat_map(|r| r.exits.iter())
        .filter(|(_, e)| e.gate.is_some())
        .collect();
    assert_eq!(gated.len(), 1, "exactly one gated exit");
    assert_eq!(
        world.rooms["rows"].exits["north"].gate,
        Some(dungeon_on_dregg::dsl::ir::Gate::NeedsItem(
            "winding_key".into()
        )),
        "the rows→greenhouse exit is gated on the winding key"
    );

    assert_eq!(world.npcs.len(), 1);
    assert_eq!(world.dialogue.len(), 2);
    let placed: usize = world.rooms.values().map(|r| r.items.len()).sum();
    assert_eq!(placed, 3, "oilcan + brass_apple + heartspring placed");
    assert_eq!(world.all_items().len(), 4, "+ the npc-granted winding_key");

    assert_eq!(world.start, "gate");
    assert_eq!(world.objective.room, "sundial");
    assert_eq!(world.objective.holding, "heartspring");

    let errors: Vec<_> = validate(&world)
        .into_iter()
        .filter(|i| i.is_error())
        .collect();
    assert!(
        errors.is_empty(),
        "a good authored source has zero validator errors, got {errors:?}"
    );
}

/// FAIL-CLOSED port fidelity: the deliberately-broken fixture is caught — refused at
/// parse with a source line, or flagged by the validator — and the dangling exit
/// target is NAMED (same tooth as attested-dm's own test).
#[test]
fn port_fidelity_broken_dungeon_is_caught_and_localized() {
    match parse_dungeon(BROKEN) {
        Err(e) => {
            assert!(
                e.line > 0,
                "a parse error carries its source line, got {e:?}"
            );
            assert!(
                e.message.contains("antechamer"),
                "the dangling target is NAMED: {e:?}"
            );
        }
        Ok(world) => {
            let errors: Vec<_> = validate(&world)
                .into_iter()
                .filter(|i| i.is_error())
                .collect();
            assert!(
                errors.iter().any(|i| i.message.contains("antechamer")),
                "the dangling exit target is NAMED in the errors: {errors:?}"
            );
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The compiler on the REAL executor.
// ─────────────────────────────────────────────────────────────────────────────

/// The gated exit lowers to a REAL executor tooth: a `FieldGte(has_winding_key, 1)`
/// on the case guarded by that choice's dispatch method, fully executor-enforced
/// (no handler-only clause).
#[test]
fn gate_lowers_to_a_real_fieldgte_tooth() {
    let world = parse_dungeon(ORCHARD).expect("parses");
    let d = compile_world(&world).expect("compiles + translation-validates");

    let north = d
        .exit_index("rows", "north")
        .expect("the gated exit lowered");
    let key_slot = *d
        .story
        .var_slots
        .get("has_winding_key")
        .expect("the key var has a compiled slot");

    let method = choice_method("rows", north);
    assert_eq!(
        d.story.fully_gated.get(&method),
        Some(&true),
        "the gate is fully executor-enforced"
    );
    let constraints = d.gate_constraints("rows", north);
    assert!(
        constraints.iter().any(|c| matches!(
            c,
            StateConstraint::FieldGte { index, value }
                if *index as usize == key_slot && *value == field_from_u64(1)
        )),
        "the gate is FieldGte(has_winding_key, 1); got {constraints:?}"
    );
}

/// THE LEGAL PATH, DRIVEN: parse → compile → deploy on a real `WorldCell` → walk the
/// critical path (gate → rows → shed → the Keeper's trade → greenhouse → sundial →
/// claim) as real committed `TurnReceipt`s, to the terminal END — then the whole
/// playthrough re-verifies by replay against a fresh identically-seeded deploy.
#[test]
fn legal_path_commits_real_receipts_to_the_terminal_room_and_reverifies() {
    let world = parse_dungeon(ORCHARD).expect("parses");
    let d = compile_world(&world).expect("compiles");

    let mut driver = Driver::start(d.deploy(7).expect("deploys"), &d.scene).expect("starts");
    let path = [
        d.exit_index("gate", "north").unwrap(),
        d.take_index("rows", "brass_apple").unwrap(),
        d.exit_index("rows", "east").unwrap(),
        d.talk_index("shed", 0).unwrap(), // topic `key`: apple → winding_key
        d.exit_index("shed", "west").unwrap(),
        d.exit_index("rows", "north").unwrap(), // the GATED exit — key now held
        d.take_index("greenhouse", "heartspring").unwrap(),
        d.exit_index("greenhouse", "west").unwrap(),
        d.objective_index("sundial").unwrap(),
    ];
    for (i, idx) in path.iter().enumerate() {
        driver
            .advance(*idx)
            .unwrap_or_else(|e| panic!("legal step {i} (choice {idx}) commits: {e}"));
    }
    assert!(driver.is_ended(), "the dungeon reached its terminal END");
    assert_eq!(driver.world().read_var("has_winding_key"), 1);
    assert_eq!(driver.world().read_var("has_heartspring"), 1);
    assert_eq!(
        driver.world().read_var(DUNGEON_WON_VAR),
        1,
        "the objective was claimed"
    );

    let play = driver.playthrough();
    assert_eq!(
        play.receipts().len(),
        10,
        "genesis + 9 moves, all real receipts"
    );
    for r in play.receipts() {
        assert_ne!(
            r.turn_hash, [0u8; 32],
            "every step is a genuine committed turn"
        );
    }
    verify_chain_linkage(&play).expect("the receipt chain links (pre == prev.post)");
    verify(d.deploy(7).expect("re-deploys"), &d.scene, &play)
        .expect("the honest playthrough re-verifies by replay");
}

/// THE ILLEGAL POLARITY, DRIVEN AT THE EXECUTOR: walking the gated exit WITHOUT the
/// winding key is a real `WorldError::Refused` — and nothing commits (anti-ghost:
/// same room, no key, no win).
#[test]
fn illegal_gated_exit_is_a_real_refusal_that_commits_nothing() {
    let world = parse_dungeon(ORCHARD).expect("parses");
    let d = compile_world(&world).expect("compiles");
    let cell = d.deploy(9).expect("deploys");

    // Walk to the rows (ungated) — a real committed turn.
    let north = d.exit_index("gate", "north").unwrap();
    cell.apply_choice("gate", north, &d.choice("gate", north).unwrap())
        .expect("the ungated step commits");
    assert_eq!(
        cell.read_passage(),
        Some(d.rooms["rows"]),
        "standing in the rows"
    );

    // Drive the GATED exit directly at the executor, keyless — REFUSED.
    let gated = d.exit_index("rows", "north").unwrap();
    let refused = cell.apply_choice("rows", gated, &d.choice("rows", gated).unwrap());
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a keyless walk through the wound-shut greenhouse door is refused, got {refused:?}"
    );

    // Anti-ghost read-back: the refused turn committed NOTHING.
    assert_eq!(
        cell.read_passage(),
        Some(d.rooms["rows"]),
        "still in the rows"
    );
    assert_eq!(cell.read_var("has_winding_key"), 0, "no key materialized");
    assert_eq!(cell.read_var(DUNGEON_WON_VAR), 0, "no win ghosted in");
}

/// The AUGMENTATION is enforcement, not decoration (driven): a `has_winding_key`
/// grant STAPLED onto another method's turn (the ungated take-oilcan choice) is a
/// real executor refusal, and a stapled passage-slot teleport on a legit exit method
/// is refused by that method's nav pin.
#[test]
fn stapled_grant_and_teleport_are_real_refusals() {
    let world = parse_dungeon(ORCHARD).expect("parses");
    let d = compile_world(&world).expect("compiles");
    let cell = d.deploy(11).expect("deploys");
    let id = cell.cell_id();

    // Staple a key grant onto the take-oilcan method: refused (write confinement).
    let take = d.take_index("gate", "oilcan").unwrap();
    let key_slot = d.story.var_slots["has_winding_key"] as u64;
    let refused = cell.apply_raw(
        &choice_method("gate", take),
        vec![stash_effect(id, key_slot, 1)],
    );
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a stapled key grant must be refused, got {refused:?}"
    );
    assert_eq!(cell.read_var("has_winding_key"), 0, "anti-ghost: no key");

    // Staple a teleport onto the legit gate→rows exit method: the nav pin forces the
    // turn to LAND on the declared target, so a jump to the sundial is refused.
    let north = d.exit_index("gate", "north").unwrap();
    let refused = cell.apply_raw(
        &choice_method("gate", north),
        vec![stash_effect(id, 0, d.rooms["sundial"] as u64)],
    );
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a stapled teleport must be refused by the nav pin, got {refused:?}"
    );
    assert_eq!(
        cell.read_passage(),
        Some(d.rooms["gate"]),
        "anti-ghost: still at the gate"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The translation-validation tooth — both polarities.
// ─────────────────────────────────────────────────────────────────────────────

/// A corrupted lowering with a DROPPED gate constraint is refused by
/// [`check_lowering`] with the missing tooth NAMED — a `CompiledDungeon` that lost a
/// tooth can never pass as validated.
#[test]
fn translation_validation_refuses_a_dropped_gate_tooth() {
    let world = parse_dungeon(ORCHARD).expect("parses");
    let mut d = compile_world(&world).expect("the honest compile validates");
    check_lowering(&world, &d).expect("the honest artifact re-checks clean");

    // Corrupt: drop the FieldGte gate tooth from the gated exit's case.
    let north = d.exit_index("rows", "north").unwrap();
    let m = symbol(&choice_method("rows", north));
    let key_slot = d.story.var_slots["has_winding_key"];
    let CellProgram::Cases(cases) = &mut d.story.program else {
        panic!("program is Cases");
    };
    let case = cases
        .iter_mut()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == m))
        .expect("the gated case exists");
    let before = case.constraints.len();
    case.constraints.retain(
        |c| !matches!(c, StateConstraint::FieldGte { index, .. } if *index as usize == key_slot),
    );
    assert_eq!(
        case.constraints.len(),
        before - 1,
        "exactly the gate tooth was dropped"
    );

    let out = check_lowering(&world, &d);
    match out {
        Err(CompileError::ValidationFailed { mismatch }) => assert!(
            mismatch.contains("MISSING"),
            "the dropped tooth is named as missing: {mismatch}"
        ),
        other => panic!("a de-toothed lowering must be refused, got {other:?}"),
    }
}

/// A corrupted lowering with an INJECTED constraint no source construct accounts for
/// (a phantom tooth) is refused too — the check is a biconditional, not a subset test.
#[test]
fn translation_validation_refuses_a_phantom_tooth() {
    let world = parse_dungeon(ORCHARD).expect("parses");
    let mut d = compile_world(&world).expect("compiles");

    // Inject a phantom gate onto the UNGATED take-oilcan choice.
    let take = d.take_index("gate", "oilcan").unwrap();
    let m = symbol(&choice_method("gate", take));
    let CellProgram::Cases(cases) = &mut d.story.program else {
        panic!("program is Cases");
    };
    let case = cases
        .iter_mut()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == m))
        .expect("the take case exists");
    case.constraints.push(StateConstraint::FieldGte {
        index: d.story.var_slots["has_heartspring"] as u8,
        value: field_from_u64(1),
    });

    let out = check_lowering(&world, &d);
    match out {
        Err(CompileError::ValidationFailed { mismatch }) => assert!(
            mismatch.contains("PHANTOM"),
            "the injected tooth is named as phantom: {mismatch}"
        ),
        other => panic!("a phantom-toothed lowering must be refused, got {other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Honest residuals + fail-closed inputs.
// ─────────────────────────────────────────────────────────────────────────────

/// An unsupported construct yields the NAMED `CompileError::Unsupported`, not a
/// silent drop: the Lantern Fen parses clean (it is a good attested-dm dungeon) but
/// carries a `hostile`, which this compiler does not lower yet.
#[test]
fn unsupported_construct_is_a_named_refusal_not_a_silent_drop() {
    let world = parse_dungeon(LANTERN_FEN).expect("the lantern fen parses clean");
    match compile_world(&world) {
        Err(CompileError::Unsupported { construct }) => assert!(
            construct.contains("hostile") && construct.contains("gargoyle"),
            "the unsupported construct is NAMED: {construct}"
        ),
        other => panic!("a world with a hostile must be refused by name, got {other:?}"),
    }
}

/// A validator-broken world never compiles: the broken fixture (parsed WITHOUT the
/// semantic gate, as an authoring tool would) is refused as `WorldInvalid` before any
/// lowering happens.
#[test]
fn a_validator_broken_world_is_refused_before_lowering() {
    let world = parse_world(BROKEN).expect("syntactically fine, semantically broken");
    match compile_world(&world) {
        Err(CompileError::WorldInvalid { first, errors }) => {
            assert!(errors >= 1);
            assert!(!first.is_empty());
        }
        other => panic!("a broken world must not compile, got {other:?}"),
    }
}

/// The mapping table is faithful: every source construct (take/talk/exit/objective)
/// has exactly one lowered choice, and the compiled scene mirrors the room count.
#[test]
fn mapping_table_covers_every_source_construct() {
    let world = parse_dungeon(ORCHARD).expect("parses");
    let d = compile_world(&world).expect("compiles");

    assert_eq!(d.rooms.len(), 5, "every room is a passage");
    assert_eq!(d.scene.passages.len(), 5);

    let takes = d
        .choices
        .iter()
        .filter(|c| matches!(c.kind, ChoiceKind::Take { .. }))
        .count();
    let talks = d
        .choices
        .iter()
        .filter(|c| matches!(c.kind, ChoiceKind::Talk { .. }))
        .count();
    let exits = d
        .choices
        .iter()
        .filter(|c| matches!(c.kind, ChoiceKind::Exit { .. }))
        .count();
    let claims = d
        .choices
        .iter()
        .filter(|c| matches!(c.kind, ChoiceKind::Objective))
        .count();
    assert_eq!((takes, talks, exits, claims), (3, 2, 8, 1));
}

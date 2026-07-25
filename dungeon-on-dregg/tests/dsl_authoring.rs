//! # The AUTHORING measurement — what a `.dungeon` author can actually express.
//!
//! `dsl_compile.rs` tests the compiler against a fixture written to fit it. This file
//! tests the LANGUAGE against a dungeon written to be worth playing
//! (`dungeons/salt_reliquary.dungeon`, authored blind against the grammar), and splits
//! into two halves that are each falsifiable:
//!
//! * **THE WALLS** — things the author wanted and could not say, pinned as assertions.
//!   Removing a wall must BREAK its test. They are not aspirational comments.
//! * **THE TEETH** — the constructs that landed (`once`, `requires A and B`,
//!   `requires flag F is v`, `oath`), driven on the REAL executor in BOTH polarities:
//!   the legal use commits a receipt, the illegal one is a `WorldError::Refused` that
//!   commits nothing. A test that only shows the happy path would prove nothing about
//!   whether the exclusion is a tooth or a convention.

use dregg_app_framework::StateConstraint;
use dungeon_on_dregg::dsl::{
    CompileError, DUNGEON_WON_VAR, compile_world, ir::Gate, once_var, parse_dungeon, parse_world,
    validate,
};
use spween_dregg::{Driver, WorldError};

const RELIQUARY: &str = include_str!("../dungeons/salt_reliquary.dungeon");

/// The authored dungeon parses and validates clean — the baseline that makes every
/// assertion below non-vacuous (a wall found in a broken file proves nothing).
#[test]
fn the_authored_dungeon_parses_and_validates_clean() {
    let world = parse_dungeon(RELIQUARY).expect("the salt reliquary parses");
    assert_eq!(world.rooms.len(), 6);
    assert_eq!(world.npcs.len(), 1);
    assert_eq!(world.dialogue.len(), 4, "four topics on Ferrun");
    assert_eq!(world.oaths.len(), 1, "one irreversible fork");
    assert_eq!(world.oaths[0].branches.len(), 2, "ledger / drowned");
    assert_eq!(world.objective.room, "reliquary");
    assert_eq!(world.objective.holding, "drowned_crown");
    let errors: Vec<_> = validate(&world)
        .into_iter()
        .filter(|i| i.is_error())
        .collect();
    assert!(errors.is_empty(), "clean authored source: {errors:?}");
}

/// It compiles and PLAYS on the real executor, through the LEDGER branch of the oath:
/// swear → ask what the toll is for → buy the gate (needs the tithe AND the oath) →
/// learn the name → open the bronze door → take the crown → claim it.
#[test]
fn the_ledger_branch_plays_to_a_win_on_the_real_executor() {
    let world = parse_dungeon(RELIQUARY).expect("parses");
    let d = compile_world(&world).expect("compiles + translation-validates");
    let mut driver = Driver::start(d.deploy(3).expect("deploys"), &d.scene).expect("starts");

    for (i, idx) in [
        d.take_index("strand", "salt_tithe").unwrap(),
        d.exit_index("strand", "down").unwrap(),
        d.swear_index("tidegate", 0, 0).unwrap(), // oath: ledger
        d.talk_index("tidegate", 0).unwrap(),     // topic `toll`  -> toll_asked
        d.talk_index("tidegate", 1).unwrap(),     // topic `pay`   -> toll_paid
        d.talk_index("tidegate", 2).unwrap(),     // topic `niche` -> door_answered
        d.exit_index("tidegate", "east").unwrap(), // the PAID gate
        d.exit_index("undervault", "north").unwrap(),
        d.exit_index("antechapel", "north").unwrap(), // the ANSWERED door
        d.take_index("reliquary", "drowned_crown").unwrap(),
        d.objective_index("reliquary").unwrap(),
    ]
    .into_iter()
    .enumerate()
    {
        driver
            .advance(idx)
            .unwrap_or_else(|e| panic!("ledger step {i} (choice {idx}) commits: {e}"));
    }
    assert!(driver.is_ended(), "the dungeon reached its terminal END");
    assert_eq!(driver.world().read_var("has_drowned_crown"), 1);
    assert_eq!(driver.world().read_var(DUNGEON_WON_VAR), 1);
    assert!(driver.playthrough().receipts().len() >= 12);
}

/// The DROWNED branch is a genuinely different playthrough on the same source: the paid
/// gate stays shut forever and the long stair — shut to the ledger's side — opens.
#[test]
fn the_drowned_branch_is_a_different_route_through_the_same_source() {
    let world = parse_dungeon(RELIQUARY).expect("parses");
    let d = compile_world(&world).expect("compiles");
    let mut driver = Driver::start(d.deploy(4).expect("deploys"), &d.scene).expect("starts");

    driver
        .advance(d.exit_index("strand", "down").unwrap())
        .unwrap();
    driver
        .advance(d.swear_index("tidegate", 0, 1).unwrap())
        .expect("swearing to the drowned commits");
    driver
        .advance(d.exit_index("tidegate", "west").unwrap())
        .expect("the long stair opens to the drowned's side");
    assert_eq!(driver.world().read_passage(), Some(d.rooms["longstair"]));
    assert_eq!(driver.world().read_var("flag_oath_allegiance_drowned"), 1);
    assert_eq!(driver.world().read_var("flag_oath_allegiance_ledger"), 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// THE TEETH — what landed, driven in BOTH polarities at the executor.
// ─────────────────────────────────────────────────────────────────────────────

/// **The oath is IRREVERSIBLE, executor-enforced.** After swearing to the ledger, the
/// drowned branch is a real `WorldError::Refused` that commits nothing — the shared
/// spend counter is a kernel predicate, not a convention the driver happens to respect.
/// This is the wall (`W2 — NO FORK`) that made every authored dungeon a checklist.
#[test]
fn an_oath_forecloses_its_siblings_at_the_executor() {
    let world = parse_dungeon(RELIQUARY).expect("parses");
    let d = compile_world(&world).expect("compiles");
    let cell = d.deploy(12).expect("deploys");
    cell.apply_choice(
        "strand",
        d.exit_index("strand", "down").unwrap(),
        &d.choice("strand", d.exit_index("strand", "down").unwrap())
            .unwrap(),
    )
    .expect("walk to the arch");

    let ledger = d.swear_index("tidegate", 0, 0).unwrap();
    let drowned = d.swear_index("tidegate", 0, 1).unwrap();
    cell.apply_choice("tidegate", ledger, &d.choice("tidegate", ledger).unwrap())
        .expect("the first oath commits");

    // The sibling branch: REFUSED at the kernel.
    let refused = cell.apply_choice("tidegate", drowned, &d.choice("tidegate", drowned).unwrap());
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "swearing the other branch must be refused, got {refused:?}"
    );
    // Re-swearing the SAME branch is refused too (the counter is spent, not per-branch).
    let again = cell.apply_choice("tidegate", ledger, &d.choice("tidegate", ledger).unwrap());
    assert!(
        matches!(again, Err(WorldError::Refused(_))),
        "re-swearing must be refused, got {again:?}"
    );
    // Anti-ghost read-back: no second allegiance materialized.
    assert_eq!(cell.read_var("flag_oath_allegiance_ledger"), 1);
    assert_eq!(cell.read_var("flag_oath_allegiance_drowned"), 0);
    assert_eq!(
        cell.read_var("flag_sworn_allegiance"),
        1,
        "spent exactly once"
    );
}

/// **`once` CLOSES a topic forever, executor-enforced.** Ferrun answers the niche
/// question on the first asking and refuses the second — the revelation cannot be
/// farmed. (Compare: before `once`, the identical source granted forever.)
#[test]
fn a_once_topic_is_refused_the_second_time() {
    let world = parse_dungeon(RELIQUARY).expect("parses");
    let d = compile_world(&world).expect("compiles");
    let cell = d.deploy(13).expect("deploys");
    let down = d.exit_index("strand", "down").unwrap();
    cell.apply_choice("strand", down, &d.choice("strand", down).unwrap())
        .unwrap();

    let toll = d.talk_index("tidegate", 0).unwrap(); // `topic toll once`
    cell.apply_choice("tidegate", toll, &d.choice("tidegate", toll).unwrap())
        .expect("the first asking commits");
    let second = cell.apply_choice("tidegate", toll, &d.choice("tidegate", toll).unwrap());
    assert!(
        matches!(second, Err(WorldError::Refused(_))),
        "a `once` topic must refuse the second asking, got {second:?}"
    );
    assert_eq!(
        cell.read_var(&once_var("talk_ferrun_toll")),
        1,
        "the spend counter moved exactly once"
    );

    // The UNGATED topic beside it still repeats — the refusal is the `once`, not a
    // blanket one-turn-per-topic rule (non-vacuity of the polarity above).
    let crown = d.talk_index("tidegate", 3).unwrap(); // `topic crown` (no `once`)
    for _ in 0..3 {
        cell.apply_choice("tidegate", crown, &d.choice("tidegate", crown).unwrap())
            .expect("an ordinary topic still repeats");
    }
}

/// **A CONJUNCTION installs EVERY conjunct as its own tooth.** `topic pay once requires
/// item salt_tithe and flag oath_allegiance_ledger` lowers to three real constraints,
/// and holding only ONE of them is a refusal. Before this, the tail of the requirement
/// was dropped on the floor and the choice deployed with a strictly weaker gate.
#[test]
fn a_conjunctive_requires_installs_every_conjunct_and_bites() {
    let world = parse_dungeon(RELIQUARY).expect("parses");
    let d = compile_world(&world).expect("compiles");

    // The source keeps both conjuncts.
    let pay = &world.dialogue[1];
    assert_eq!(
        pay.requires,
        Some(Gate::All(vec![
            Gate::NeedsItem("salt_tithe".into()),
            Gate::NeedsFlag("oath_allegiance_ledger".into(), 1),
        ])),
        "the conjunction survives parsing"
    );

    // Both conjuncts are real teeth on that one case, resolved by NAME.
    let idx = d.talk_index("tidegate", 1).unwrap();
    let cs = d.gate_constraints("tidegate", idx);
    for var in ["has_salt_tithe", "flag_oath_allegiance_ledger"] {
        let key = d.story.var_slots[var];
        assert!(
            cs.iter().any(|c| matches!(
                c,
                StateConstraint::FieldGte { index, .. } if *index as u64 == key
            )),
            "`{var}` is its own installed tooth; got {cs:?}"
        );
    }

    // DRIVEN, the half-satisfied polarity: holding the tithe but sworn to the DROWNED,
    // the toll is refused. (A dropped conjunct would have sold it.)
    let cell = d.deploy(14).expect("deploys");
    let take = d.take_index("strand", "salt_tithe").unwrap();
    cell.apply_choice("strand", take, &d.choice("strand", take).unwrap())
        .unwrap();
    let down = d.exit_index("strand", "down").unwrap();
    cell.apply_choice("strand", down, &d.choice("strand", down).unwrap())
        .unwrap();
    let drowned = d.swear_index("tidegate", 0, 1).unwrap();
    cell.apply_choice("tidegate", drowned, &d.choice("tidegate", drowned).unwrap())
        .unwrap();

    assert_eq!(cell.read_var("has_salt_tithe"), 1, "the tithe IS in hand");
    let refused = cell.apply_choice("tidegate", idx, &d.choice("tidegate", idx).unwrap());
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "one conjunct short must be refused, got {refused:?}"
    );
    assert_eq!(cell.read_var("flag_toll_paid"), 0, "anti-ghost: no toll");
}

/// **`requires flag F is v` is EXCLUSIVE**, where `>=` cannot be: it lowers to a real
/// `FieldEquals`, so a higher value is refused. This is what makes a fork gateable —
/// `>= 1` admits 2 and therefore can never say "this branch and not that one".
#[test]
fn an_is_gate_lowers_to_field_equals_not_field_gte() {
    let src = RELIQUARY.replace(
        "exit north -> reliquary requires flag door_answered",
        "exit north -> reliquary requires flag door_answered is 1",
    );
    let world = parse_dungeon(&src).expect("parses");
    assert_eq!(
        world.rooms["antechapel"].exits["north"].gate,
        Some(Gate::FlagIs("door_answered".into(), 1)),
        "`is` parses to the exclusive gate, not to `>=`"
    );
    let d = compile_world(&world).expect("compiles");
    let idx = d.exit_index("antechapel", "north").unwrap();
    let key = d.story.var_slots["flag_door_answered"];
    let cs = d.gate_constraints("antechapel", idx);
    assert!(
        cs.iter().any(|c| matches!(
            c,
            StateConstraint::FieldEquals { index, .. } if *index as u64 == key
        )),
        "`is` installs FieldEquals; got {cs:?}"
    );
    assert!(
        !cs.iter().any(|c| matches!(
            c,
            StateConstraint::FieldGte { index, .. } if *index as u64 == key
        )),
        "and NOT a FieldGte (which would admit every higher value); got {cs:?}"
    );
}

/// A dangling `and`, an unrecognized requirement tail, and a one-branch oath are all
/// REFUSALS with the offender named — the fail-closed polarity of the new grammar. The
/// tail case is the important one: it used to be silently ignored.
#[test]
fn malformed_new_grammar_is_refused_by_name() {
    let cases: [(&str, &str, &str); 4] = [
        (
            "dangling and",
            "exit north -> reliquary requires flag door_answered",
            "exit north -> reliquary requires flag door_answered and",
        ),
        (
            "unrecognized tail",
            "exit north -> reliquary requires flag door_answered",
            "exit north -> reliquary requires flag door_answered whenever",
        ),
        (
            "bad conjunct",
            "exit north -> reliquary requires flag door_answered",
            "exit north -> reliquary requires flag door_answered and nonsense",
        ),
        (
            "one-branch oath",
            "  branch drowned \"You look past him at the niches. He closes the ledger, and does not look at you again.\"",
            "",
        ),
    ];
    for (name, from, to) in cases {
        let src = RELIQUARY.replace(from, to);
        assert!(
            src != RELIQUARY,
            "the `{name}` mutation actually changed the source"
        );
        let err = parse_dungeon(&src)
            .err()
            .unwrap_or_else(|| panic!("`{name}` must be REFUSED, not accepted"));
        assert!(err.line > 0, "`{name}` carries its source line: {err}");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE WALLS THAT REMAIN. Removing one must break its test.
// ─────────────────────────────────────────────────────────────────────────────

/// **W1 — NO COST.** Paying the toll does not spend the tithe. Item possession is a
/// monotone boolean: no directive, and no lowered effect, moves an item var back down.
/// `once` buys "you may pay only one toll"; it does not buy "and now the coin is gone".
/// Every economy (tolls, offerings, ammunition, rations) is still unwritable.
#[test]
fn w1_items_are_monotone_no_directive_can_spend_one() {
    let world = parse_dungeon(RELIQUARY).expect("parses");
    let d = compile_world(&world).expect("compiles");
    let mut driver = Driver::start(d.deploy(5).expect("deploys"), &d.scene).expect("starts");
    driver
        .advance(d.take_index("strand", "salt_tithe").unwrap())
        .unwrap();
    driver
        .advance(d.exit_index("strand", "down").unwrap())
        .unwrap();
    driver
        .advance(d.swear_index("tidegate", 0, 0).unwrap())
        .unwrap();
    driver
        .advance(d.talk_index("tidegate", 1).unwrap())
        .unwrap(); // pay the toll
    assert_eq!(driver.world().read_var("flag_toll_paid"), 1, "toll paid");
    assert_eq!(
        driver.world().read_var("has_salt_tithe"),
        1,
        "W1: and the tithe is STILL in hand — nothing in the language can spend it"
    );
}

/// **W3 — ONE ENDING.** `objective:` is a single `reach ROOM holding ITEM`; the IR has
/// exactly one `Objective` field, so a second `objective:` line OVERWRITES rather than
/// adding an ending. The oath forks the MIDDLE of a dungeon and both branches still end
/// the same way.
#[test]
fn w3_the_ir_holds_exactly_one_objective() {
    let two = RELIQUARY.replace(
        "objective: reach reliquary holding drowned_crown",
        "objective: reach reliquary holding drowned_crown\nobjective: reach strand holding rimed_censer",
    );
    let w2 = parse_dungeon(&two).expect("a second objective parses");
    assert_eq!(
        (w2.objective.room.as_str(), w2.objective.holding.as_str()),
        ("strand", "rimed_censer"),
        "W3: the second `objective:` OVERWRITES the first — endings do not accumulate"
    );
}

/// **W4 — NO RISK.** Every construct that could hurt the player parses and is then
/// refused BY NAME at compile. A deployed authored dungeon is a puzzle box you cannot
/// die in. Named-refusal is the honest posture; the wall is that this list is this long.
#[test]
fn w4_every_dangerous_construct_is_refused_by_name() {
    let cases: [(&str, &str); 6] = [
        (
            "hostile",
            "\nhostile revenant in undervault defeated_by rimed_censer\n  victory flag revenant_broken\n  death flag slain\n",
        ),
        (
            "combat",
            "\ncombat revenant in undervault hp 6 attack 2\n  weapon rimed_censer damage 3\n  victory flag revenant_broken\n",
        ),
        (
            "spell",
            "\nspell unsalt innate\n  in antechapel -> flag door_answered \"The word takes the salt off the bronze.\"\n",
        ),
        (
            "consumable",
            "\nconsumable rimed_censer -> reveal \"Smoke.\"\n",
        ),
        ("light", "\nlight tide_lamp oil 8\n  dark: longstair\n"),
        ("lose", "\nlose: slain >= 1 -> \"the tide comes back\"\n"),
    ];
    for (name, snippet) in cases {
        let src = format!("{RELIQUARY}{snippet}");
        let world = parse_dungeon(&src)
            .unwrap_or_else(|e| panic!("`{name}` PARSES (the grammar has it): {e}"));
        match compile_world(&world) {
            Err(CompileError::Unsupported { construct }) => assert!(
                construct.contains(name),
                "W4: `{name}` is refused by name, got `{construct}`"
            ),
            other => panic!("W4: `{name}` must be a NAMED refusal, got {other:?}"),
        }
    }
}

/// **W7 — NO CHECK.** Nothing rolls. `skills.rs` has d20-vs-DC on the real substrate;
/// the grammar has no way to name an ability, a DC, or an outcome that differs on
/// success and failure — `check` is not a directive.
#[test]
fn w7_there_is_no_check_directive() {
    let src = format!(
        "{RELIQUARY}\ncheck nerve dc 12 in longstair -> flag steadied \"You hold.\" else \"You do not.\"\n"
    );
    let err = parse_dungeon(&src).expect_err("W7: `check` is not a directive");
    assert!(
        err.message.contains("unknown directive") && err.message.contains("check"),
        "W7: the refusal names it: {err}"
    );
}

/// The validator still sees through the new constructs: a conjunct naming an item that
/// exists nowhere is a blocking error, so `requires A and B` cannot smuggle an
/// unsatisfiable term past the lints that guard the single-gate form.
#[test]
fn a_conjunct_naming_a_nonexistent_item_is_still_a_validator_error() {
    let src = RELIQUARY.replace(
        "exit north -> reliquary requires flag door_answered",
        "exit north -> reliquary requires flag door_answered and item bishops_ring",
    );
    let world = parse_world(&src).expect("syntactically fine");
    let errors: Vec<_> = validate(&world)
        .into_iter()
        .filter(|i| i.is_error())
        .collect();
    assert!(
        errors.iter().any(|i| i.message.contains("bishops_ring")),
        "the unsatisfiable conjunct is NAMED: {errors:?}"
    );
}

/// **THE SPILL BOUNDARY — the automatafl-shaped risk for authored content.**
///
/// The compiled cell has 16 register slots; slot 0 is the passage, so 15 named vars fit.
/// The 16th and beyond SPILL to the ext plane, which is executor-enforced but (per
/// `compile.rs`'s own header) *in-circuit-projected only for register-plane
/// constraints*, and binds each value at ~31 bits rather than the register width.
///
/// This is not hypothetical for authoring: every `once`, every oath branch, and every
/// oath counter is a NEW var, so the constructs that make a dungeon worth playing are
/// exactly the ones that push it over the line. An author has no way to feel this — the
/// dungeon plays identically on either side of it.
///
/// The test does not forbid spilling (a real dungeon will exceed 15 vars). It pins the
/// boundary as MEASURED, so the cost is visible in the record rather than discovered
/// later, and it fails if the allocator's split ever moves.
#[test]
fn the_authored_dungeon_var_budget_against_the_15_register_ceiling() {
    let world = parse_dungeon(RELIQUARY).expect("parses");
    let d = compile_world(&world).expect("compiles");

    let total = d.story.var_slots.len();
    let spilled: Vec<&String> = d
        .story
        .var_slots
        .iter()
        .filter(|&(_, &key)| key >= 16)
        .map(|(name, _)| name)
        .collect();

    // The measurement, printed so the number is in the record, not just asserted.
    println!("authored vars = {total}; spilled to the ext plane = {spilled:?}");

    // Every var the compiler allocated below 16 is a register; the split is a suffix of
    // one sorted order, so `registers + spilled == total` must hold exactly.
    let registers = total - spilled.len();
    assert_eq!(
        registers + spilled.len(),
        total,
        "the allocator splits one order into registers then ext keys"
    );
    assert!(
        registers <= 15,
        "slot 0 is the passage — at most 15 named vars can be registers, got {registers}"
    );
    // Non-vacuity: this dungeon genuinely exercises the boundary rather than sitting
    // trivially under it. If a future edit shrinks it below the ceiling, this fires and
    // the spill assertions above stop meaning anything.
    assert!(
        total > 15,
        "the authored dungeon ({total} vars) is supposed to CROSS the 15-register \
         ceiling — that is the condition under which the ext-plane caveat applies"
    );
    assert!(
        !spilled.is_empty(),
        "crossing the ceiling must actually spill"
    );
}

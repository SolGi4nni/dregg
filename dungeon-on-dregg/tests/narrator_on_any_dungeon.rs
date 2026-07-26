//! # The narrator on a dungeon it has never heard of
//!
//! Until now `legal_commands` was a hardcoded `match view.room { "gatehall" | "hall" |
//! "sanctum" }`. Every other scene — including every `.dungeon` file the DSL compiles —
//! narrated into an EMPTY legal set, so the confined channel refused every command and the
//! narrator ran on exactly one dungeon.
//!
//! These tests drive the narrated path end to end on two AUTHORED dungeons that the
//! narrator has no knowledge of: `attested-dm`'s Clockwork Orchard and this crate's Salt
//! Reliquary. Nothing here names a room or a keyword the narrator was taught; every move is
//! looked up in the set the view derives from the compiled scene.
//!
//! The teeth, in both polarities:
//! * every room of both dungeons offers a NON-EMPTY, canonical, unique-per-room vocabulary;
//! * a model response naming one of those keywords COMMITS a real `TurnReceipt` with the
//!   narration bound into it, and the chain links;
//! * an invented keyword and a keyword from another room are REFUSED;
//! * a GATED exit is absent from the offered set while its gate is shut and present once it
//!   opens, so the model is never handed a move the executor would refuse.

use dungeon_on_dregg::dsl::{compile_world, parse_dungeon};
use dungeon_on_dregg::narrator::{
    BrainRefusal, Narrated, bound_narration_commit, keyword_is_canonical, legal_commands,
    narrate_turn, narration_commitment, parse_confined_response, scene_view,
};
use spween_dregg::{Driver, WorldCell, verify_chain_linkage};

const ORCHARD: &str = include_str!("fixtures/clockwork_orchard.dungeon");
const RELIQUARY: &str = include_str!("../dungeons/salt_reliquary.dungeon");

/// Compile a `.dungeon` source and hand back a post-genesis world plus its scene.
fn deployed(source: &str, seed: u8) -> (WorldCell, spween::Scene) {
    let authored = parse_dungeon(source).expect("the authored dungeon parses");
    let compiled = compile_world(&authored).expect("the authored dungeon compiles");
    let driver = Driver::start(compiled.deploy(seed).expect("deploys"), &compiled.scene)
        .expect("genesis commits");
    let (world, _no_steps) = driver.finish();
    (world, compiled.scene)
}

/// The keyword the live view gives `(current room, choice)`, or `None` if that choice is
/// not currently offered.
fn offered_keyword(world: &WorldCell, scene: &spween::Scene, choice: usize) -> Option<String> {
    legal_commands(&scene_view(world, scene))
        .iter()
        .find(|offered| offered.command.choice == choice)
        .map(|offered| offered.keyword.clone())
}

/// Narrate one move by NAMING a currently-offered keyword: exactly the round trip a
/// confined model makes (the tool schema's enum, the model's answer, the re-check).
fn narrate_keyword(world: &WorldCell, scene: &spween::Scene, keyword: &str, prose: &str) {
    let view = scene_view(world, scene);
    let narrated =
        parse_confined_response(&view, &format!("COMMAND: {keyword}\nNARRATION: {prose}"))
            .unwrap_or_else(|e| panic!("`{keyword}` should be admitted here: {e}"));
    let landed = narrate_turn(world, scene, &narrated)
        .unwrap_or_else(|e| panic!("`{keyword}` should commit here: {e}"));
    assert_eq!(
        bound_narration_commit(&landed.receipt),
        Some(narration_commitment(prose)),
        "the narration binds into the real receipt on an authored dungeon too"
    );
}

/// **THE FIX.** Every room of two dungeons the narrator was never taught offers a
/// non-empty, canonical, unique vocabulary derived from the scene's own authored labels.
#[test]
fn every_room_of_an_authored_dungeon_offers_a_derived_vocabulary() {
    for (source, seed, name) in [(ORCHARD, 11u8, "orchard"), (RELIQUARY, 12u8, "reliquary")] {
        let authored = parse_dungeon(source).expect("parses");
        let compiled = compile_world(&authored).expect("compiles");
        let mut rooms_with_moves = 0usize;
        for passage in &compiled.scene.passages {
            let room = passage.name.as_str();
            let view = dungeon_on_dregg::narrator::SceneView::in_room(&compiled.scene, room);
            assert_eq!(view.room.as_deref(), Some(room));
            let offered = legal_commands(&view);
            if offered.is_empty() {
                continue; // a terminal room with no authored choice at all
            }
            rooms_with_moves += 1;
            let mut seen = std::collections::BTreeSet::new();
            for command in offered {
                assert!(
                    keyword_is_canonical(&command.keyword),
                    "{name}/{room}: `{}` is not a canonical keyword",
                    command.keyword
                );
                assert!(
                    seen.insert(command.keyword.clone()),
                    "{name}/{room}: `{}` is not unique",
                    command.keyword
                );
                assert_eq!(command.command.room, room);
                assert!(
                    !command.prompt.is_empty(),
                    "{name}/{room}: no authored label"
                );
            }
            assert!(
                !view.prose.is_empty(),
                "{name}/{room}: the view carries no authored prose for the model to narrate"
            );
        }
        assert!(
            rooms_with_moves >= 4,
            "{name}: only {rooms_with_moves} rooms narrate, which is not a dungeon"
        );
    }
}

/// A narrated walk of the Clockwork Orchard's critical path, driven ENTIRELY through
/// derived keywords: the model names a token, the closed channel maps it to a coordinate,
/// the executor resolves it, and the narration binds into the receipt chain.
#[test]
fn a_confined_model_narrates_the_clockwork_orchard_to_its_objective() {
    let authored = parse_dungeon(ORCHARD).expect("parses");
    let compiled = compile_world(&authored).expect("compiles");
    let driver = Driver::start(compiled.deploy(13).expect("deploys"), &compiled.scene)
        .expect("genesis commits");
    let (world, _) = driver.finish();
    let scene = &compiled.scene;

    // The critical path as COORDINATES (the scene's own indices), narrated by keyword.
    let path: [(usize, &str); 9] = [
        (
            compiled.exit_index("gate", "north").unwrap(),
            "The gate groans aside and the rows swallow the light.",
        ),
        (
            compiled.take_index("rows", "brass_apple").unwrap(),
            "A brass apple comes away from the bough with a click.",
        ),
        (
            compiled.exit_index("rows", "east").unwrap(),
            "You follow the ruts east until a shed leans out of the mist.",
        ),
        (
            compiled.talk_index("shed", 0).unwrap(),
            "The Keeper turns the apple over twice and gives up a key.",
        ),
        (
            compiled.exit_index("shed", "west").unwrap(),
            "Back among the rows, the key is cold in your hand.",
        ),
        (
            compiled.exit_index("rows", "north").unwrap(),
            "The wound lock gives and the greenhouse breathes out.",
        ),
        (
            compiled.take_index("greenhouse", "heartspring").unwrap(),
            "The heartspring lifts free, still ticking.",
        ),
        (
            compiled.exit_index("greenhouse", "west").unwrap(),
            "You carry it west to where the sundial waits.",
        ),
        (
            compiled.objective_index("sundial").unwrap(),
            "The dial takes the spring and the orchard begins to keep time again.",
        ),
    ];

    for (step, (choice, prose)) in path.into_iter().enumerate() {
        let keyword = offered_keyword(&world, scene, choice)
            .unwrap_or_else(|| panic!("step {step}: choice {choice} is not offered"));
        narrate_keyword(&world, scene, &keyword, prose);
    }

    assert_eq!(world.read_var("has_winding_key"), 1);
    assert_eq!(world.read_var("has_heartspring"), 1);
    assert_eq!(
        world.read_var(dungeon_on_dregg::dsl::DUNGEON_WON_VAR),
        1,
        "the narrated run claimed the objective"
    );
    assert!(
        scene_view(&world, scene).room.is_none(),
        "the objective ends the scene"
    );
}

/// **The gate is visible in the OFFERED set, not just in the refusal.** The orchard's north
/// exit from `rows` is item-gated. While the key is unheld the derived view does not offer
/// it, so a paid model is never handed a move the executor would refuse; once the Keeper
/// trades for the key, the same coordinate appears.
#[test]
fn a_shut_gate_is_absent_from_the_offered_set_and_appears_when_it_opens() {
    let authored = parse_dungeon(ORCHARD).expect("parses");
    let compiled = compile_world(&authored).expect("compiles");
    let driver = Driver::start(compiled.deploy(14).expect("deploys"), &compiled.scene)
        .expect("genesis commits");
    let (world, _) = driver.finish();
    let scene = &compiled.scene;
    let gated = compiled.exit_index("rows", "north").unwrap();

    narrate_keyword(
        &world,
        scene,
        &offered_keyword(&world, scene, compiled.exit_index("gate", "north").unwrap())
            .expect("the opening exit is offered"),
        "You step through the gate into the rows.",
    );

    // The scene AUTHORS the gated exit; the live view withholds it.
    let authored_view = dungeon_on_dregg::narrator::SceneView::in_room(scene, "rows");
    assert!(
        authored_view
            .commands()
            .iter()
            .any(|c| c.command.choice == gated),
        "the rows author a north exit"
    );
    assert!(
        offered_keyword(&world, scene, gated).is_none(),
        "an exit whose gate is shut must not be offered to a paid narrator"
    );

    // Earn the key, and the same coordinate becomes offered.
    for (choice, prose) in [
        (
            compiled.take_index("rows", "brass_apple").unwrap(),
            "The brass apple is heavier than fruit has any right to be.",
        ),
        (
            compiled.exit_index("rows", "east").unwrap(),
            "The shed door hangs open on one hinge.",
        ),
        (
            compiled.talk_index("shed", 0).unwrap(),
            "The Keeper trades the apple for a winding key.",
        ),
        (
            compiled.exit_index("shed", "west").unwrap(),
            "You return to the rows with the key.",
        ),
    ] {
        let keyword = offered_keyword(&world, scene, choice).expect("an offered step");
        narrate_keyword(&world, scene, &keyword, prose);
    }
    assert_eq!(world.read_var("has_winding_key"), 1);
    assert!(
        offered_keyword(&world, scene, gated).is_some(),
        "the gate opened, so the move is offered again"
    );
}

/// The closed channel still holds on an authored dungeon: an invented keyword and a
/// keyword borrowed from another room are both refused, and the world does not move.
#[test]
fn the_closed_channel_holds_on_an_authored_dungeon() {
    let (world, scene) = deployed(RELIQUARY, 15);
    let view = scene_view(&world, &scene);
    let start = view.room.clone().expect("a fresh reliquary has a room");
    let before = world.read_passage();

    assert_eq!(
        parse_confined_response(
            &view,
            "COMMAND: grant_me_the_crown\nNARRATION: It is yours."
        ),
        Err(BrainRefusal::IllegalCommand(
            "grant_me_the_crown".to_string()
        )),
        "an invented keyword is refused on an authored dungeon"
    );

    // A keyword that is legal SOMEWHERE ELSE in this same scene is not legal here.
    let elsewhere = scene
        .passages
        .iter()
        .map(|passage| passage.name.as_str().to_string())
        .filter(|room| room != &start)
        .find_map(|room| {
            let other = dungeon_on_dregg::narrator::SceneView::in_room(&scene, &room);
            other
                .commands()
                .iter()
                .find(|c| view.command_for(&c.keyword).is_none())
                .map(|c| c.keyword.clone())
        })
        .expect("another room offers a keyword this one does not");
    assert_eq!(
        parse_confined_response(
            &view,
            &format!("COMMAND: {elsewhere}\nNARRATION: You reach.")
        ),
        Err(BrainRefusal::IllegalCommand(elsewhere)),
        "a legal move from another room is not legal here"
    );

    assert_eq!(world.read_passage(), before, "no refusal moved the world");
}

/// A narrated run on the Salt Reliquary produces a real linked receipt chain: the
/// narrated path is the ordinary turn path, on a dungeon nobody special-cased.
#[test]
fn a_narrated_run_on_the_salt_reliquary_chains() {
    let authored = parse_dungeon(RELIQUARY).expect("parses");
    let compiled = compile_world(&authored).expect("compiles");
    let mut driver = Driver::start(compiled.deploy(16).expect("deploys"), &compiled.scene)
        .expect("genesis commits");
    // One ordinary player move first, so the chain mixes player turns with narrated ones.
    driver
        .advance(compiled.take_index("strand", "salt_tithe").unwrap())
        .expect("taking the tithe commits");
    let genesis = driver.genesis().cloned().expect("a genesis receipt");
    let (world, steps) = driver.finish();
    let scene = &compiled.scene;

    let mut receipts = vec![genesis];
    receipts.extend(steps.into_iter().map(|step| step.receipt));

    for (choice, prose) in [
        (
            compiled.exit_index("strand", "down").unwrap(),
            "The stair drops you into the tidegate's held breath.",
        ),
        (
            compiled.swear_index("tidegate", 0, 0).unwrap(),
            "You give the ledger your word, and the water goes still to hear it.",
        ),
    ] {
        let keyword = offered_keyword(&world, scene, choice)
            .unwrap_or_else(|| panic!("choice {choice} is offered"));
        let view = scene_view(&world, scene);
        let narrated =
            parse_confined_response(&view, &format!("COMMAND: {keyword}\nNARRATION: {prose}"))
                .expect("the derived keyword is admitted");
        let landed = narrate_turn(&world, scene, &narrated).expect("the narrated move commits");
        assert_eq!(
            bound_narration_commit(&landed.receipt),
            Some(narration_commitment(prose))
        );
        receipts.push(landed.receipt);
    }

    let play = spween_dregg::Playthrough {
        genesis: receipts[0].clone(),
        genesis_state: Vec::new(),
        steps: receipts[1..]
            .iter()
            .map(|receipt| spween_dregg::StepReceipt {
                passage: String::new(),
                choice_index: 0,
                receipt: receipt.clone(),
                state: Vec::new(),
                decision_commitment: None,
            })
            .collect(),
    };
    verify_chain_linkage(&play).expect("player turns and narrated turns chain into ONE record");
    assert_eq!(world.read_var("flag_oath_allegiance_ledger"), 1);
}

/// A narration is prose, not power, on an authored dungeon too: a jailbroken narration
/// that claims a relic changes no committed var.
#[test]
fn prose_is_not_power_on_an_authored_dungeon() {
    let authored = parse_dungeon(ORCHARD).expect("parses");
    let compiled = compile_world(&authored).expect("compiles");
    let driver = Driver::start(compiled.deploy(17).expect("deploys"), &compiled.scene)
        .expect("genesis commits");
    let (world, _) = driver.finish();
    let scene = &compiled.scene;
    let keyword = offered_keyword(&world, scene, compiled.exit_index("gate", "north").unwrap())
        .expect("the opening room offers a move");
    narrate_keyword(
        &world,
        scene,
        &keyword,
        "You stride through holding the winding key, the heartspring, and the orchard itself.",
    );
    assert_eq!(
        world.read_var("has_winding_key"),
        0,
        "the claimed key was never granted"
    );
    assert_eq!(
        world.read_var("has_heartspring"),
        0,
        "the claimed heartspring was never granted"
    );
    assert_eq!(
        world.read_var(dungeon_on_dregg::dsl::DUNGEON_WON_VAR),
        0,
        "narrating a win is not winning"
    );
}

//! A consequential relic fork, driven through the real dungeon executor.
//!
//! The Reliquary of Two Oaths asks the player to take either the Sunblade or the
//! Thorn Crown.  That first choice is permanent: it selects how the guardian may
//! be overcome, how that encounter awakens the relic, and which ending can be
//! claimed. Every consequence is committed cell state and every branch edge is a
//! `StateConstraint` enforced by the real `WorldCell` executor. The hostile
//! polarities below drive premature/wrong resonance, encounter, and ending moves
//! directly at that executor and require an in-band refusal with no ghost write;
//! both honest branches finish as replay-verifiable receipt chains.

use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, StateConstraint, TransitionCase, TransitionGuard, field_from_u64, symbol,
};
use dungeon_on_dregg::stash_effect;
use spween::{Choice, PassageContent, Scene};
use spween_dregg::{
    CompiledStory, Driver, PASSAGE_ENDED, PASSAGE_SLOT, WorldCell, WorldError, choice_method,
    compile_scene, parse, verify, verify_chain_linkage,
};

const RELIQUARY: &str = r#"---
id: reliquary-of-two-oaths
title: The Reliquary of Two Oaths
weight: 1
---

=== reliquary

Two relics wait beneath the sleeping guardian: a sunblade wrapped in white linen and
a thorn crown resting in a bowl of old coins. The oath you take will wake the stone.

* [Lift the Sunblade and swear to free the valley]
  ~ oath = 1
  -> reliquary

* [Wear the Thorn Crown and claim the buried court]
  ~ oath = 2
  -> reliquary

* [Break the guardian's chains with the Sunblade]
  ~ guardian_defeated = 1
  ~ mercy = 1
  -> aftermath

* [Command the guardian to kneel to the Thorn Crown]
  ~ guardian_defeated = 1
  ~ curse = 1
  ~ tribute = 13
  -> aftermath

=== aftermath

The guardian is still. Dawn reaches the valley above; below, thirteen sealed coffers
wait around an empty throne. The relic in your hands remembers which promise you made.

* [Let the freed guardian kindle the Sunblade]
  ~ relic_awakened = 1
  -> aftermath

* [Feed thirteen seals of tribute to the Thorn Crown]
  ~ relic_awakened = 2
  -> aftermath

* [Carry the Sunblade home and free the valley]
  ~ village_saved = 1
  -> END

* [Descend crowned and claim the burial tribute]
  ~ vault_claimed = 1
  -> END
"#;

const ROOM_RELIQUARY: &str = "reliquary";
const ROOM_AFTERMATH: &str = "aftermath";

const TAKE_SUNBLADE: usize = 0;
const TAKE_THORN_CROWN: usize = 1;
const FREE_GUARDIAN: usize = 2;
const COMMAND_GUARDIAN: usize = 3;
const AWAKEN_SUNBLADE: usize = 0;
const AWAKEN_THORN_CROWN: usize = 1;
const SAVE_VALLEY: usize = 2;
const CLAIM_TRIBUTE: usize = 3;

fn scene() -> Scene {
    parse(RELIQUARY, "reliquary-of-two-oaths.scene").expect("the relic fork parses")
}

fn choice(scene: &Scene, room: &str, index: usize) -> Choice {
    scene
        .passages
        .iter()
        .find(|passage| passage.name.as_str() == room)
        .unwrap_or_else(|| panic!("room `{room}` exists"))
        .content
        .iter()
        .filter_map(|content| match content {
            PassageContent::Choice(choice) => Some(choice),
            _ => None,
        })
        .nth(index)
        .cloned()
        .unwrap_or_else(|| panic!("room `{room}` has choice {index}"))
}

fn slot(story: &CompiledStory, name: &str) -> u8 {
    let key = *story
        .var_slots
        .get(name)
        .unwrap_or_else(|| panic!("relic fork has `{name}` state"));
    u8::try_from(key).expect("the relic-fork vars fit the register plane")
}

fn append_method_teeth(
    program: &mut CellProgram,
    method: &str,
    constraints: impl IntoIterator<Item = StateConstraint>,
) {
    let wanted = symbol(method);
    let CellProgram::Cases(cases) = program else {
        panic!("compiled story uses Cases");
    };
    let case = cases
        .iter_mut()
        .find(
            |case| matches!(&case.guard, TransitionGuard::MethodIs { method } if *method == wanted),
        )
        .unwrap_or_else(|| panic!("compiled choice method `{method}` exists"));
    case.constraints.extend(constraints);
}

/// Freeze `slot` on every choice method except its declared writers.  This is the
/// write-confinement half of the mechanic: a client cannot staple a later reward
/// onto an earlier, otherwise-legitimate method.
fn confine_slot(program: &mut CellProgram, slot: u8, writers: &[&str]) {
    let writer_symbols: Vec<_> = writers.iter().map(|method| symbol(method)).collect();
    let CellProgram::Cases(cases) = program else {
        panic!("compiled story uses Cases");
    };
    for case in cases {
        let TransitionGuard::MethodIs { method } = &case.guard else {
            continue;
        };
        if !writer_symbols.contains(method) {
            case.constraints
                .push(StateConstraint::Immutable { index: slot });
        }
    }
}

fn eq(index: u8, value: u64) -> StateConstraint {
    StateConstraint::FieldEquals {
        index,
        value: field_from_u64(value),
    }
}

fn delta(index: u8, value: u64) -> StateConstraint {
    StateConstraint::FieldDelta {
        index,
        delta: field_from_u64(value),
    }
}

fn method(room: &str, index: usize) -> String {
    choice_method(room, index)
}

/// Compile the authored scene and install the relic-oath teeth.  The compiler
/// supplies dispatch and the genesis one-shot; this augmentation supplies the
/// branch state machine, exact effects, navigation pins, and write confinement.
fn compiled() -> CompiledStory {
    let mut story = compile_scene(&scene()).expect("the relic fork compiles");

    let oath = slot(&story, "oath");
    let guardian = slot(&story, "guardian_defeated");
    let mercy = slot(&story, "mercy");
    let curse = slot(&story, "curse");
    let tribute = slot(&story, "tribute");
    let awakened = slot(&story, "relic_awakened");
    let village = slot(&story, "village_saved");
    let vault = slot(&story, "vault_claimed");

    let take_sunblade = method(ROOM_RELIQUARY, TAKE_SUNBLADE);
    let take_crown = method(ROOM_RELIQUARY, TAKE_THORN_CROWN);
    let free_guardian = method(ROOM_RELIQUARY, FREE_GUARDIAN);
    let command_guardian = method(ROOM_RELIQUARY, COMMAND_GUARDIAN);
    let awaken_sunblade = method(ROOM_AFTERMATH, AWAKEN_SUNBLADE);
    let awaken_crown = method(ROOM_AFTERMATH, AWAKEN_THORN_CROWN);
    let save_valley = method(ROOM_AFTERMATH, SAVE_VALLEY);
    let claim_tribute = method(ROOM_AFTERMATH, CLAIM_TRIBUTE);

    let reliquary = story.passage_index[ROOM_RELIQUARY] as u64;
    let aftermath = story.passage_index[ROOM_AFTERMATH] as u64;

    // Taking either relic is an exact, first-and-only oath transition.
    append_method_teeth(
        &mut story.program,
        &take_sunblade,
        [
            eq(oath, 1),
            delta(oath, 1),
            StateConstraint::WriteOnce { index: oath },
            eq(PASSAGE_SLOT as u8, reliquary),
        ],
    );
    append_method_teeth(
        &mut story.program,
        &take_crown,
        [
            eq(oath, 2),
            delta(oath, 2),
            StateConstraint::WriteOnce { index: oath },
            eq(PASSAGE_SLOT as u8, reliquary),
        ],
    );

    // The relic selects the encounter verb.  Both defeat the guardian, but leave
    // different permanent consequences in the cell.
    append_method_teeth(
        &mut story.program,
        &free_guardian,
        [
            eq(oath, 1),
            eq(guardian, 1),
            delta(guardian, 1),
            eq(mercy, 1),
            delta(mercy, 1),
            eq(PASSAGE_SLOT as u8, aftermath),
        ],
    );
    append_method_teeth(
        &mut story.program,
        &command_guardian,
        [
            eq(oath, 2),
            eq(guardian, 1),
            delta(guardian, 1),
            eq(curse, 1),
            delta(curse, 1),
            eq(tribute, 13),
            delta(tribute, 13),
            eq(PASSAGE_SLOT as u8, aftermath),
        ],
    );

    // RELIC RESONANCE — the guardian encounter changes what the relic can become.
    // The mercy branch kindles the Sunblade; the curse+tribute branch feeds the
    // Crown.  AllowedTransitions pins these self-looping rites to an already-reached
    // aftermath, so their method cannot be used as a teleport from the reliquary.
    let aftermath_self_loop = || StateConstraint::AllowedTransitions {
        slot_index: PASSAGE_SLOT as u8,
        allowed: vec![(field_from_u64(aftermath), field_from_u64(aftermath))],
    };
    append_method_teeth(
        &mut story.program,
        &awaken_sunblade,
        [
            eq(oath, 1),
            eq(guardian, 1),
            eq(mercy, 1),
            eq(awakened, 1),
            delta(awakened, 1),
            StateConstraint::WriteOnce { index: awakened },
            aftermath_self_loop(),
        ],
    );
    append_method_teeth(
        &mut story.program,
        &awaken_crown,
        [
            eq(oath, 2),
            eq(guardian, 1),
            eq(curse, 1),
            eq(tribute, 13),
            eq(awakened, 2),
            delta(awakened, 2),
            StateConstraint::WriteOnce { index: awakened },
            aftermath_self_loop(),
        ],
    );

    // The ending must agree with the oath, encounter consequence, AND the relic
    // state derived from them.  An ending cannot skip the compositional mechanic.
    append_method_teeth(
        &mut story.program,
        &save_valley,
        [
            eq(oath, 1),
            eq(guardian, 1),
            eq(mercy, 1),
            eq(awakened, 1),
            eq(village, 1),
            delta(village, 1),
            eq(PASSAGE_SLOT as u8, PASSAGE_ENDED),
        ],
    );
    append_method_teeth(
        &mut story.program,
        &claim_tribute,
        [
            eq(oath, 2),
            eq(guardian, 1),
            eq(curse, 1),
            eq(tribute, 13),
            eq(awakened, 2),
            eq(vault, 1),
            delta(vault, 1),
            eq(PASSAGE_SLOT as u8, PASSAGE_ENDED),
        ],
    );

    // A slot may change only on its authored method.  These pins are what make
    // the mechanic hold against `apply_raw`, rather than only against the UI.
    confine_slot(&mut story.program, oath, &[&take_sunblade, &take_crown]);
    confine_slot(
        &mut story.program,
        guardian,
        &[&free_guardian, &command_guardian],
    );
    confine_slot(&mut story.program, mercy, &[&free_guardian]);
    confine_slot(&mut story.program, curse, &[&command_guardian]);
    confine_slot(&mut story.program, tribute, &[&command_guardian]);
    confine_slot(
        &mut story.program,
        awakened,
        &[&awaken_sunblade, &awaken_crown],
    );
    confine_slot(&mut story.program, village, &[&save_valley]);
    confine_slot(&mut story.program, vault, &[&claim_tribute]);

    // The oath invariant is slot-bound as well as method-bound.  It therefore
    // runs on a forged write no matter which legitimate method the attacker uses.
    let CellProgram::Cases(cases) = &mut story.program else {
        unreachable!();
    };
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: oath },
        constraints: vec![
            StateConstraint::MemberOf {
                index: oath,
                set: vec![1, 2],
            },
            StateConstraint::WriteOnce { index: oath },
        ],
    });
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: awakened },
        constraints: vec![
            StateConstraint::MemberOf {
                index: awakened,
                set: vec![1, 2],
            },
            StateConstraint::WriteOnce { index: awakened },
        ],
    });

    story
}

fn deploy(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(compiled()), seed).expect("the relic fork deploys")
}

fn refused(result: Result<dregg_app_framework::TurnReceipt, WorldError>) -> bool {
    matches!(result, Err(WorldError::Refused(_)))
}

/// Reproduce an honest prefix on a separate world for a hostile executor probe.
///
/// Executor-level refusals are ordered actions: Phase 1 deliberately burns the
/// submitter nonce even when the state-machine write is rejected. Consequently a
/// refused probe cannot be inserted into a receipt chain that records only
/// successful story moves -- the next success quite correctly starts from the
/// post-refusal nonce, not the preceding success's post-state. Replaying the honest
/// prefix here keeps each anti-ghost assertion real while leaving the honest branch
/// below as an actual contiguous receipt chain.
fn probe_after<'s>(seed: u8, scene: &'s Scene, choices: &[usize]) -> Driver<'s> {
    let mut driver = Driver::start(deploy(seed), scene).expect("probe genesis commits");
    for &choice in choices {
        driver
            .advance(choice)
            .expect("the honest prefix for a hostile probe commits");
    }
    driver
}

#[test]
fn the_sunblade_oath_refuses_the_crown_route_and_replays_to_mercy() {
    let scene = scene();
    let mut driver = Driver::start(deploy(61), &scene).expect("genesis commits");

    // Try to staple the whole merciful victory onto the first relic-taking
    // method.  The post-state would satisfy the later reward predicates, so the
    // refusal specifically exercises per-method write confinement.
    let stapled_probe = probe_after(61, &scene, &[]);
    let world = stapled_probe.world();
    let cell = world.cell_id();
    let story = world.story();
    let stapled_victory = world.apply_raw(
        &method(ROOM_RELIQUARY, TAKE_SUNBLADE),
        vec![
            stash_effect(cell, story.var_slots["oath"], 1),
            stash_effect(cell, story.var_slots["guardian_defeated"], 1),
            stash_effect(cell, story.var_slots["mercy"], 1),
        ],
    );
    assert!(
        refused(stapled_victory),
        "a later encounter result cannot ride the relic-taking method"
    );
    assert_eq!(world.read_var("oath"), 0);
    assert_eq!(world.read_var("guardian_defeated"), 0);
    assert_eq!(world.read_var("mercy"), 0);
    assert_eq!(
        world.read_passage(),
        Some(world.story().passage_index[ROOM_RELIQUARY])
    );

    driver
        .advance(TAKE_SUNBLADE)
        .expect("the Sunblade oath commits");
    assert_eq!(driver.world().read_var("oath"), 1);

    // Drive the WRONG encounter directly at the real executor.  It must not
    // produce even a partial curse/tribute/guardian write. The probe replays the
    // honest prefix on its own world because a refused submitted action burns its
    // nonce even though it commits no story-state write.
    let wrong_encounter_probe = probe_after(61, &scene, &[TAKE_SUNBLADE]);
    let wrong_encounter = wrong_encounter_probe.world().apply_choice(
        ROOM_RELIQUARY,
        COMMAND_GUARDIAN,
        &choice(&scene, ROOM_RELIQUARY, COMMAND_GUARDIAN),
    );
    assert!(
        refused(wrong_encounter),
        "the Crown verb is unavailable after the Sunblade oath"
    );
    assert_eq!(
        wrong_encounter_probe.world().read_var("guardian_defeated"),
        0
    );
    assert_eq!(wrong_encounter_probe.world().read_var("curse"), 0);
    assert_eq!(wrong_encounter_probe.world().read_var("tribute"), 0);
    assert_eq!(
        wrong_encounter_probe.world().read_passage(),
        Some(wrong_encounter_probe.world().story().passage_index[ROOM_RELIQUARY])
    );

    driver
        .advance(FREE_GUARDIAN)
        .expect("the Sunblade frees the guardian");
    assert_eq!(driver.world().read_var("mercy"), 1);

    let premature_ending_probe = probe_after(61, &scene, &[TAKE_SUNBLADE, FREE_GUARDIAN]);
    let premature_ending = premature_ending_probe.world().apply_choice(
        ROOM_AFTERMATH,
        SAVE_VALLEY,
        &choice(&scene, ROOM_AFTERMATH, SAVE_VALLEY),
    );
    assert!(
        refused(premature_ending),
        "the merciful ending still requires the Sunblade to be kindled"
    );
    assert_eq!(premature_ending_probe.world().read_var("village_saved"), 0);
    assert_eq!(premature_ending_probe.world().read_var("relic_awakened"), 0);

    let wrong_resonance_probe = probe_after(61, &scene, &[TAKE_SUNBLADE, FREE_GUARDIAN]);
    let wrong_resonance = wrong_resonance_probe.world().apply_choice(
        ROOM_AFTERMATH,
        AWAKEN_THORN_CROWN,
        &choice(&scene, ROOM_AFTERMATH, AWAKEN_THORN_CROWN),
    );
    assert!(
        refused(wrong_resonance),
        "mercy cannot awaken the Crown's curse resonance"
    );
    assert_eq!(wrong_resonance_probe.world().read_var("relic_awakened"), 0);

    driver
        .advance(AWAKEN_SUNBLADE)
        .expect("the freed guardian kindles the Sunblade");
    assert_eq!(driver.world().read_var("relic_awakened"), 1);

    let wrong_ending_probe =
        probe_after(61, &scene, &[TAKE_SUNBLADE, FREE_GUARDIAN, AWAKEN_SUNBLADE]);
    let wrong_ending = wrong_ending_probe.world().apply_choice(
        ROOM_AFTERMATH,
        CLAIM_TRIBUTE,
        &choice(&scene, ROOM_AFTERMATH, CLAIM_TRIBUTE),
    );
    assert!(
        refused(wrong_ending),
        "a merciful oath cannot claim the Crown's tribute"
    );
    assert_eq!(wrong_ending_probe.world().read_var("vault_claimed"), 0);
    assert_eq!(
        wrong_ending_probe.world().read_passage(),
        Some(wrong_ending_probe.world().story().passage_index[ROOM_AFTERMATH])
    );

    driver
        .advance(SAVE_VALLEY)
        .expect("the merciful ending commits");
    assert!(driver.is_ended());
    assert_eq!(driver.world().read_var("village_saved"), 1);
    assert_eq!(driver.world().read_var("vault_claimed"), 0);

    let play = driver.playthrough();
    assert_eq!(play.receipts().len(), 5, "genesis plus four real moves");
    verify_chain_linkage(&play).expect("the Sunblade receipt chain links");
    verify(deploy(61), &scene, &play).expect("the Sunblade branch replays");
}

#[test]
fn the_thorn_crown_oath_refuses_mercy_and_replays_to_a_cursed_tribute() {
    let scene = scene();
    let mut driver = Driver::start(deploy(62), &scene).expect("genesis commits");

    driver
        .advance(TAKE_THORN_CROWN)
        .expect("the Thorn Crown oath commits");
    assert_eq!(driver.world().read_var("oath"), 2);

    // The oath is irreversible: taking the other relic is a real WriteOnce
    // refusal, and the original oath remains committed.
    let second_relic_probe = probe_after(62, &scene, &[TAKE_THORN_CROWN]);
    let second_relic = second_relic_probe.world().apply_choice(
        ROOM_RELIQUARY,
        TAKE_SUNBLADE,
        &choice(&scene, ROOM_RELIQUARY, TAKE_SUNBLADE),
    );
    assert!(
        refused(second_relic),
        "the second relic cannot overwrite the oath"
    );
    assert_eq!(second_relic_probe.world().read_var("oath"), 2);

    let wrong_encounter_probe = probe_after(62, &scene, &[TAKE_THORN_CROWN]);
    let wrong_encounter = wrong_encounter_probe.world().apply_choice(
        ROOM_RELIQUARY,
        FREE_GUARDIAN,
        &choice(&scene, ROOM_RELIQUARY, FREE_GUARDIAN),
    );
    assert!(
        refused(wrong_encounter),
        "the Crown oath cannot take the merciful encounter"
    );
    assert_eq!(
        wrong_encounter_probe.world().read_var("guardian_defeated"),
        0
    );
    assert_eq!(wrong_encounter_probe.world().read_var("mercy"), 0);

    driver
        .advance(COMMAND_GUARDIAN)
        .expect("the Crown commands the guardian");
    assert_eq!(driver.world().read_var("guardian_defeated"), 1);
    assert_eq!(driver.world().read_var("curse"), 1);
    assert_eq!(driver.world().read_var("tribute"), 13);

    let premature_ending_probe = probe_after(62, &scene, &[TAKE_THORN_CROWN, COMMAND_GUARDIAN]);
    let premature_ending = premature_ending_probe.world().apply_choice(
        ROOM_AFTERMATH,
        CLAIM_TRIBUTE,
        &choice(&scene, ROOM_AFTERMATH, CLAIM_TRIBUTE),
    );
    assert!(
        refused(premature_ending),
        "the tribute ending still requires the Crown to be fed"
    );
    assert_eq!(premature_ending_probe.world().read_var("vault_claimed"), 0);
    assert_eq!(premature_ending_probe.world().read_var("relic_awakened"), 0);

    let wrong_resonance_probe = probe_after(62, &scene, &[TAKE_THORN_CROWN, COMMAND_GUARDIAN]);
    let wrong_resonance = wrong_resonance_probe.world().apply_choice(
        ROOM_AFTERMATH,
        AWAKEN_SUNBLADE,
        &choice(&scene, ROOM_AFTERMATH, AWAKEN_SUNBLADE),
    );
    assert!(
        refused(wrong_resonance),
        "the cursed guardian cannot kindle the mercy resonance"
    );
    assert_eq!(wrong_resonance_probe.world().read_var("relic_awakened"), 0);

    driver
        .advance(AWAKEN_THORN_CROWN)
        .expect("the tribute feeds the Thorn Crown");
    assert_eq!(driver.world().read_var("relic_awakened"), 2);

    let wrong_ending_probe = probe_after(
        62,
        &scene,
        &[TAKE_THORN_CROWN, COMMAND_GUARDIAN, AWAKEN_THORN_CROWN],
    );
    let wrong_ending = wrong_ending_probe.world().apply_choice(
        ROOM_AFTERMATH,
        SAVE_VALLEY,
        &choice(&scene, ROOM_AFTERMATH, SAVE_VALLEY),
    );
    assert!(
        refused(wrong_ending),
        "the Crown oath cannot retcon itself into the merciful ending"
    );
    assert_eq!(wrong_ending_probe.world().read_var("village_saved"), 0);

    driver
        .advance(CLAIM_TRIBUTE)
        .expect("the cursed tribute ending commits");
    assert!(driver.is_ended());
    assert_eq!(driver.world().read_var("vault_claimed"), 1);
    assert_eq!(driver.world().read_var("village_saved"), 0);

    let play = driver.playthrough();
    assert_eq!(play.receipts().len(), 5, "genesis plus four real moves");
    verify_chain_linkage(&play).expect("the Thorn Crown receipt chain links");
    verify(deploy(62), &scene, &play).expect("the Thorn Crown branch replays");
}

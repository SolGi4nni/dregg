//! `skills_spells` — DRIVE the RPG-depth teeth and print them.
//!
//! Skill checks (a d20 over a committed stat vs a DC, bound + reproduced, and a
//! check-GATED locked door) and class spells (class-locked + mana-costed + an
//! effect), all executor-enforced on the real substrate. Run:
//!
//! ```text
//! cargo run -p dungeon-on-dregg --example skills_spells
//! ```

use dungeon_on_dregg::progression::{MAGE, ROGUE, WARRIOR};
use dungeon_on_dregg::skills::{
    self, CHECK_TOTAL_SLOT, DC_SLOT, OPEN_DOOR_METHOD, SkillReplayError, adventurer_story,
    create_adventurer, deploy_adventurer, make_check, open_door, reverify_check, roll_check,
};
use dungeon_on_dregg::spells::{
    self, BACKSTAB, FIREBALL, MEND, RALLY, SPELLBOOK, cast, caster_story, create_caster,
    deploy_caster,
};
use spween_dregg::WorldError;

fn class_name(c: u64) -> &'static str {
    match c {
        x if x == WARRIOR => "Warrior",
        x if x == MAGE => "Mage",
        x if x == ROGUE => "Rogue",
        _ => "?",
    }
}

fn main() {
    println!("== dungeon-on-dregg: SKILL CHECKS + CLASS SPELLS (executor-enforced) ==\n");

    // ─────────────────────────── SKILL CHECKS ────────────────────────────
    println!("--- SKILL CHECKS (d20 + stat vs DC, verifiable + check-gated) ---\n");

    // The check-gate is a real tooth.
    let story = adventurer_story();
    println!("the door-open case's executor teeth:");
    for c in skills::case_constraints(&story, OPEN_DOOR_METHOD) {
        println!("    {c:?}");
    }
    println!(
        "  → FieldLteField(dc[{DC_SLOT}] <= check_total[{CHECK_TOTAL_SLOT}]) IS the check-gate.\n"
    );

    // A check rolls a verifiable d20 over the committed stat, bound + reproduced.
    let world = deploy_adventurer(10);
    create_adventurer(&world, 3, 15).expect("creation");
    let committed = make_check(&world, 0).expect("a skill check commits");
    println!(
        "a check: stat 3 + d20 roll {} = total {} (recorded in check_total)",
        committed.draw.roll, committed.draw.total
    );
    let rederived = reverify_check(&committed).expect("re-verifies");
    println!("  replay re-derives the SAME roll: {rederived} (bound into the real receipt)\n");

    // A forged pass is caught on replay.
    let mut forged = committed.clone();
    let topic = dregg_app_framework::symbol(skills::SKILL_TOPIC);
    let ev = forged
        .receipt
        .emitted_events
        .iter_mut()
        .find(|e| e.topic == topic)
        .unwrap();
    ev.data[2] = dregg_app_framework::field_from_u64(20);
    ev.data[3] = dregg_app_framework::field_from_u64(23);
    forged.draw.roll = 20;
    forged.draw.total = 23;
    match reverify_check(&forged) {
        Err(SkillReplayError::RollMismatch { bound, rederived }) => println!(
            "FORGED natural-20 caught on replay: receipt binds {bound} but seed re-derives {rederived}\n"
        ),
        other => println!("unexpected: {other:?}\n"),
    }

    // The check-gate: refused on a failed check, admitted on a passed one (same move).
    let probe = deploy_adventurer(12);
    create_adventurer(&probe, 3, 100).expect("probe");
    let total = 3 + roll_check(&probe, 0).roll;

    let fail = deploy_adventurer(12);
    create_adventurer(&fail, 3, total + 1).expect("fail world");
    make_check(&fail, 0).expect("check");
    match open_door(&fail) {
        Err(WorldError::Refused(_)) => println!(
            "FAILED check (total {total} < DC {}): the door-open is REFUSED (door stays locked: {})",
            total + 1,
            fail.read_var("door")
        ),
        other => println!("unexpected: {other:?}"),
    }

    let pass = deploy_adventurer(12);
    create_adventurer(&pass, 3, total).expect("pass world");
    make_check(&pass, 0).expect("check");
    open_door(&pass).expect("the passed check opens the door");
    println!(
        "PASSED check (total {total} >= DC {total}): the door-open COMMITS (door open: {})\n",
        pass.read_var("door")
    );

    // ─────────────────────────── CLASS SPELLS ────────────────────────────
    println!("--- CLASS SPELLS (class-locked + mana-costed + effect) ---\n");

    let cstory = caster_story();
    println!("the spellbook's executor teeth:");
    for s in SPELLBOOK {
        print!("  {} ({}, cost {}):", s.name, class_name(s.class), s.cost);
        for c in spells::case_constraints(&cstory, s.method) {
            print!(" {c:?};");
        }
        println!();
    }
    println!();

    // A valid cast commits with its effect.
    let mage = deploy_caster(20);
    create_caster(&mage, MAGE, 10, 30).expect("Mage");
    cast(&mage, FIREBALL).expect("Fireball");
    println!(
        "valid cast: a Mage casts Fireball → damage {} dealt, mana_spent {} (pool 10)",
        mage.read_var("damage"),
        mage.read_var("mana_spent")
    );
    cast(&mage, MEND).expect("Mend");
    println!(
        "  the same Mage casts Mend → hp {} (healed +6), mana_spent {}\n",
        mage.read_var("hp"),
        mage.read_var("mana_spent")
    );

    // Wrong class refused.
    let warrior = deploy_caster(21);
    create_caster(&warrior, WARRIOR, 10, 30).expect("Warrior");
    match cast(&warrior, FIREBALL) {
        Err(WorldError::Refused(_)) => println!(
            "WRONG CLASS: a Warrior casting the Mage's Fireball is REFUSED (damage {} — nothing committed)",
            warrior.read_var("damage")
        ),
        other => println!("unexpected: {other:?}"),
    }
    cast(&warrior, RALLY).expect("Rally");
    println!(
        "  the Warrior's own Rally COMMITS → buff {}\n",
        warrior.read_var("buff")
    );

    // Insufficient mana refused (cumulative).
    let rogue = deploy_caster(24);
    create_caster(&rogue, ROGUE, 3, 30).expect("Rogue, pool 3");
    match cast(&rogue, BACKSTAB) {
        Ok(_) => println!(
            "Rogue Backstab (cost 2 <= pool 3) commits → damage {}, mana_spent {}",
            rogue.read_var("damage"),
            rogue.read_var("mana_spent")
        ),
        other => println!("unexpected: {other:?}"),
    }
    match cast(&rogue, BACKSTAB) {
        Err(WorldError::Refused(_)) => println!(
            "INSUFFICIENT MANA: a second Backstab (would spend 4 > pool 3) is REFUSED (mana_spent still {})",
            rogue.read_var("mana_spent")
        ),
        other => println!("unexpected: {other:?}"),
    }

    println!("\nall executor-enforced: no app-code refereeing, no LARP ledger.");
}

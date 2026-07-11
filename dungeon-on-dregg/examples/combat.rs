//! A full turn-based TACTICAL fight, printed with real receipts.
//!
//! Run: `cargo run -p dungeon-on-dregg --example combat`
//!
//! A party of two heroes (Ranger, Cleric) battles two enemies (Warden, Hound) on ONE
//! real `spween-dregg` world-cell. Dice-rolled initiative sets the turn order; each
//! round every living combatant acts under the tactical AI. Every rule is an
//! executor-enforced `StateConstraint` tooth (HP floor, turn order, resource cost,
//! cooldown, weakened-only execute, write-once down); every attack's damage is a real
//! `dregg-dice` draw bound into its `TurnReceipt` and REPRODUCED on replay. The battle
//! resolves to victory (all enemies down), and we prove the whole record: the receipts
//! chain (`pre == prev.post`) and every dice blow re-verifies. Finally we show two real
//! executor REFUSALS (an out-of-turn move, and executing a healthy foe).

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, symbol};
use dungeon_on_dregg::combat::{
    ATTACK_DIE, Arena, HEAVY_DIE, INITIATIVE_DIE, N, Outcome, RANGER, WARDEN, bound_draw,
    initiative_rolls, is_hero, name, reverify_draw,
};
use spween_dregg::WorldError;

fn main() {
    println!("=== The Tactical Arena — turn-based combat on the real dregg substrate ===\n");

    let seed = 7;
    let mut arena = Arena::deploy(seed);

    // The teeth are real installed kernel predicates (not app code).
    print_teeth(&arena);

    // Dice-rolled initiative.
    println!("Initiative (a verifiable d{INITIATIVE_DIE} per combatant):");
    let mut rolls = initiative_rolls(seed);
    rolls.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    for (c, r) in &rolls {
        println!("  {:>6} rolled {r:>2}", name(*c));
    }
    let order: Vec<&str> = arena.order.iter().map(|&c| name(c)).collect();
    println!("  turn order: {}\n", order.join(" -> "));

    println!("The parties (heroes vs enemies), HP as real cell state:");
    print_hp(&arena);
    println!();

    // Play the whole fight.
    println!("--- the battle ---");
    let rec = arena.auto_fight(400);
    let mut last_round = 0;
    for e in &rec.log {
        if e.round != last_round {
            println!("\n  Round {}:", e.round);
            last_round = e.round;
        }
        let dice = match (e.roll, e.damage) {
            (Some(r), Some(d)) => format!("  [d roll {r} -> {d} dmg]"),
            _ => String::new(),
        };
        println!(
            "    {:<7} {:<7} {}{}",
            format!("[{}]", e.kind),
            name(e.actor),
            e.note,
            dice
        );
    }
    println!();

    match rec.outcome {
        Outcome::Victory => println!(">>> VICTORY — every enemy is downed.\n"),
        Outcome::Defeat => println!(">>> DEFEAT — the party has fallen.\n"),
        Outcome::Ongoing => println!(">>> (unresolved)\n"),
    }
    print_hp(&arena);
    println!();

    // Prove the record: the receipts chain and every dice blow re-verifies.
    println!("--- verifying the record ---");
    println!(
        "  committed turns: {} (each a real TurnReceipt), rooted at the setup turn",
        rec.receipts.len()
    );
    let mut prev = arena.genesis.post_state_hash;
    let mut chained = true;
    for r in &rec.receipts {
        if r.pre_state_hash != prev {
            chained = false;
            break;
        }
        prev = r.post_state_hash;
    }
    println!(
        "  receipt chain (pre == prev.post): {}",
        if chained { "LINKS CLEANLY" } else { "BROKEN" }
    );

    println!("  dice blows (d{ATTACK_DIE}/d{HEAVY_DIE}) reproduced on replay:");
    for h in &rec.blows {
        let bound = bound_draw(&h.receipt).expect("the draw is bound into the receipt");
        let rederived = reverify_draw(&h.receipt, &h.draw).expect("the honest blow re-verifies");
        println!(
            "    {:>6} -> {:<6} roll {:>2} (bound {:>2}) re-derives {:>2}  [OK]",
            name(h.draw.attacker),
            name(h.draw.target),
            h.draw.roll,
            bound.roll,
            rederived
        );
    }
    println!();

    // A forged (gentler) roll is caught on replay.
    println!("--- tamper-evidence: a forged roll is caught ---");
    if let Some(h) = rec.blows.first() {
        let mut receipt = h.receipt.clone();
        let mut draw = h.draw.clone();
        let topic = symbol(dungeon_on_dregg::combat::DICE_TOPIC);
        let ev = receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("the dice event");
        ev.data[2] = dregg_app_framework::field_from_u64(1);
        ev.data[3] = dregg_app_framework::field_from_u64(1);
        draw.roll = 1;
        draw.damage = 1;
        match reverify_draw(&receipt, &draw) {
            Err(e) => println!("  a forged 1-damage blow: CAUGHT — {e}\n"),
            Ok(_) => println!("  (unexpected: the forgery passed)\n"),
        }
    }

    // Two real executor refusals (illegal moves).
    println!("--- illegal moves are real executor refusals ---");
    let mut fresh = Arena::deploy(3);
    fresh.force_active(WARDEN); // not the Ranger's turn
    match fresh.attack(RANGER, WARDEN) {
        Err(WorldError::Refused(_)) => {
            println!("  Ranger attacks out of turn: REFUSED (AllowedTransitions turn-order tooth)")
        }
        other => println!("  (unexpected: {other:?})"),
    }
    fresh.force_active(RANGER);
    match fresh.finish(RANGER, WARDEN) {
        Err(WorldError::Refused(_)) => println!(
            "  Ranger executes a HEALTHY Warden: REFUSED (HeapField Lte weakened-only tooth)"
        ),
        other => println!("  (unexpected: {other:?})"),
    }
    println!("\nEvery rule was the kernel's, not the game's. (•_•) / (⌐■_■)");
}

fn print_teeth(arena: &Arena) {
    let CellProgram::Cases(cases) = &arena.story().program else {
        return;
    };
    let m = symbol("atk/0/2"); // Ranger -> Warden basic attack
    if let Some(case) = cases
        .iter()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
    {
        println!("Executor-enforced teeth on the Ranger's attack (a real CellProgram case):");
        for c in &case.constraints {
            let label = match c {
                StateConstraint::AllowedTransitions { .. } => "turn order (act only on your turn)",
                StateConstraint::UntilEvent { .. } => {
                    "status gate (stunned/downed cannot act; no attacking the dead)"
                }
                StateConstraint::HeapField { .. } => {
                    "HP floor (an overkill cannot underflow the ledger)"
                }
                _ => "constraint",
            };
            println!("  - {c:?}\n      = {label}");
        }
        println!();
    }
}

fn print_hp(arena: &Arena) {
    for c in 0..N {
        let team = if is_hero(c) { "hero " } else { "enemy" };
        let status = if arena.is_down(c) {
            "DOWNED".to_string()
        } else {
            let mut s = format!("hp {:>2}", arena.hp(c));
            if arena.poison(c) > 0 {
                s.push_str(&format!(" (poison {})", arena.poison(c)));
            }
            if arena.is_guarding(c) {
                s.push_str(" (guarding)");
            }
            if arena.is_stunned(c) {
                s.push_str(" (stunned)");
            }
            s
        };
        println!("  {team} {:>6}: {status}", name(c));
    }
}

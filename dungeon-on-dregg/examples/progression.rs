//! DRIVE RPG character progression on the REAL dregg executor and PRINT the proof:
//! a character earns XP, is GATED at a premature level-up (a real executor refusal),
//! levels up once the XP is earned, and uses a class-locked ability (admitted in-class,
//! refused out of class). Every step is a real `TurnReceipt`; every gate is a real
//! executor-enforced `StateConstraint` (printed verbatim).
//!
//! Run:  cargo run -p dungeon-on-dregg --example progression

use dungeon_on_dregg::progression::{
    CHOOSE_CLASS_METHOD, GAIN_XP_METHOD, MAGE, WARRIOR, arcane_bolt_method, case_constraints,
    choose_class, deploy_hero, gain_xp, hero_story, level_up, level_up_method, use_ability,
    xp_threshold,
};

fn hx(b: &[u8; 32]) -> String {
    b.iter().take(6).map(|x| format!("{x:02x}")).collect()
}

fn main() {
    let story = hero_story();

    println!("=== RPG CHARACTER PROGRESSION on the REAL dregg executor ===\n");
    println!("character-cell slot layout (progression state on real cell fields):");
    let mut slots: Vec<_> = story.var_slots.iter().collect();
    slots.sort_by_key(|(_, s)| **s);
    for (name, slot) in slots {
        println!("  {name:<14} -> slot {slot}");
    }
    println!();

    // The installed executor teeth, printed verbatim.
    println!("--- installed executor teeth (real StateConstraints) ---");
    println!(
        "  choose_class : {:?}",
        case_constraints(&story, CHOOSE_CLASS_METHOD)
    );
    println!(
        "  gain_xp      : {:?}",
        case_constraints(&story, GAIN_XP_METHOD)
    );
    for l in 2..=3 {
        println!(
            "  level_up_to_{l}: {:?}   (xp_threshold({l}) = {})",
            case_constraints(&story, &level_up_method(l)),
            xp_threshold(l)
        );
    }
    println!(
        "  arcane_bolt  : {:?}",
        case_constraints(&story, &arcane_bolt_method())
    );
    println!();

    // ── Create a Mage ────────────────────────────────────────────────────────────
    let world = deploy_hero(101);
    println!("--- create a character (choose class = Mage) ---");
    let r = choose_class(&world, MAGE).expect("choosing a class commits");
    println!(
        "  choose_class(Mage) COMMITTED  turn={} pre={} post={}",
        hx(&r.turn_hash),
        hx(&r.pre_state_hash),
        hx(&r.post_state_hash)
    );
    let r = level_up(&world).expect("reaching level 1 needs no XP");
    println!(
        "  level_up -> level {}  turn={}",
        world.read_var("level"),
        hx(&r.turn_hash)
    );
    println!();

    // ── Earn XP ──────────────────────────────────────────────────────────────────
    println!("--- earn XP (real monotone turns) ---");
    let r = gain_xp(&world, 50).expect("earn 50 XP");
    println!(
        "  gain_xp(50) COMMITTED  xp={}  turn={}",
        world.read_var("xp"),
        hx(&r.turn_hash)
    );
    println!();

    // ── GATED level-up: premature, then earned ───────────────────────────────────
    println!(
        "--- level-up GATE (FieldGte(xp, {}) on level_up_to_2) ---",
        xp_threshold(2)
    );
    println!(
        "  attempting level-up with xp={} (< {}):",
        world.read_var("xp"),
        xp_threshold(2)
    );
    match level_up(&world) {
        Err(e) => println!("  REFUSED by the executor: {e:?}"),
        Ok(_) => println!("  !! unexpectedly committed"),
    }
    println!(
        "  anti-ghost after refusal: level={} xp={} (nothing committed)",
        world.read_var("level"),
        world.read_var("xp")
    );

    let r = gain_xp(&world, 60).expect("earn 60 more XP");
    println!(
        "  gain_xp(60) COMMITTED  xp={}  turn={}",
        world.read_var("xp"),
        hx(&r.turn_hash)
    );
    println!(
        "  attempting the SAME level-up with xp={} (>= {}):",
        world.read_var("xp"),
        xp_threshold(2)
    );
    let r = level_up(&world).expect("with the earned XP, the level-up commits");
    println!(
        "  COMMITTED -> level {}  turn={} pre={} post={}",
        world.read_var("level"),
        hx(&r.turn_hash),
        hx(&r.pre_state_hash),
        hx(&r.post_state_hash)
    );
    println!();

    // ── Class-locked ability: admitted in-class, refused out of class ─────────────
    println!("--- class ability GATE (FieldEquals(class, MAGE) on the arcane bolt) ---");
    let r = use_ability(&world, MAGE).expect("a Mage may cast the arcane bolt");
    println!(
        "  Mage casts arcane bolt: COMMITTED  abilities_used={}  turn={}",
        world.read_var("abilities_used"),
        hx(&r.turn_hash)
    );

    let warrior = deploy_hero(102);
    choose_class(&warrior, WARRIOR).expect("Warrior");
    println!("  Warrior drives the SAME arcane-bolt method:");
    match use_ability(&warrior, MAGE) {
        Err(e) => println!("  REFUSED by the executor: {e:?}"),
        Ok(_) => println!("  !! unexpectedly committed"),
    }
    println!(
        "  anti-ghost: Warrior abilities_used={} (nothing committed)",
        warrior.read_var("abilities_used")
    );
    println!();
    println!("XP, LEVEL and CLASS are REAL cell state; the gates are REAL executor teeth.");
}

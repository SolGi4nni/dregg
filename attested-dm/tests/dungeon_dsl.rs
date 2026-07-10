//! Integration tests for the DUNGEON AUTHORING FORMAT — the readable text DSL and its
//! fail-closed loader/validator. These are purely additive to the 71 in-crate unit tests.
//!
//! What they pin:
//!   * an authored-in-text dungeon PLAYS to a WIN through the real `GameSession` + `verify()`;
//!   * every construct round-trips (a rich sampler parses into the expected `GameWorld` shape);
//!   * each validator error fires on a crafted-bad source — NON-VACUOUSLY (a good source has none);
//!   * a malformed source fails closed with a line number.

use attested_dm::game::{DialogueGrant, Gate, SpellEffect};
use attested_dm::{parse_dungeon, parse_world, validate, GameSession, GameStatus, PlayResult};

const LANTERN_FEN: &str = include_str!("../dungeons/lantern_fen.dungeon");
const EMBER_OBSERVATORY: &str = include_str!("../dungeons/ember_observatory.dungeon");
const BROKEN: &str = include_str!("../dungeons/broken.dungeon");

// ── 1. An authored dungeon plays to a WIN through the real engine, and re-verifies. ──

fn play_lantern_fen_to_win() -> GameSession {
    let world = parse_dungeon(LANTERN_FEN).expect("lantern_fen parses + validates clean");
    let mut game = GameSession::open(world);
    let script = [
        "take lantern",
        "go north",
        "go down",
        "take brass_key",
        "go north",
        "ask friar about charm",
        "go east",
        "use charm on mechanism",
        "go north",
        "attack gargoyle",
        "go north",
        "take fen_heart",
    ];
    for cmd in script {
        match game.command("pilgrim", cmd) {
            PlayResult::Landed { .. } => {}
            other => panic!("winning move `{cmd}` should land, got {other:?}"),
        }
    }
    game
}

#[test]
fn authored_dungeon_wins_through_gamesession() {
    let game = play_lantern_fen_to_win();
    assert_eq!(
        game.status(),
        GameStatus::Won,
        "the authored dungeon is winnable"
    );
    // Every landed move is authentic, well-formed, injection-free, and on-chain.
    game.verify()
        .expect("the authored playthrough re-verifies as a hash chain");
    assert_eq!(
        game.world().ledger.len(),
        12,
        "twelve verified turns landed"
    );
}

#[test]
fn authored_win_needs_the_forced_order() {
    // The same rules bite an out-of-order crawler: no lantern -> the dark stair is barred.
    let world = parse_dungeon(LANTERN_FEN).unwrap();
    let mut game = GameSession::open(world);
    assert!(matches!(
        game.command("hero", "go north"),
        PlayResult::Landed { .. }
    ));
    match game.command("hero", "go down") {
        PlayResult::Refused(reason) => {
            let msg = reason.to_string();
            assert!(
                msg.contains("barred") || msg.contains("locked"),
                "got: {msg}"
            );
        }
        other => panic!("descending without the lantern must be refused, got {other:?}"),
    }
}

// ── 2. Round-trip: every construct parses into the expected GameWorld shape. ──

#[test]
fn every_construct_round_trips() {
    let w = parse_dungeon(EMBER_OBSERVATORY).expect("the rich sampler parses + validates clean");

    // rooms + descriptions + items
    assert_eq!(w.rooms.len(), 5);
    let foyer = w.room("foyer").expect("foyer room");
    assert!(
        foyer.description.contains("dead braziers"),
        "prose lines join into description"
    );
    assert!(foyer.items.contains("lamp") && foyer.items.contains("primer"));

    // an item gate and a flag gate both parsed
    assert!(matches!(
        foyer.exits.get("down").and_then(|e| e.gate.clone()),
        None
    ));
    let hall = w.room("hall").unwrap();
    assert!(matches!(
        hall.exits.get("up").and_then(|e| e.gate.clone()),
        Some(Gate::NeedsFlag(f, 1)) if f == "span_mended"
    ));

    // use-rules (learn sources)
    assert!(w
        .use_rules
        .iter()
        .any(|u| u.item == "primer" && u.sets_flag.0 == "learned_mend"));
    assert_eq!(w.use_rules.len(), 3);

    // npc + dialogue (a conditional gift + a pure reveal)
    assert_eq!(w.npcs.len(), 1);
    assert!(w.dialogue.iter().any(
        |d| matches!(&d.grant, DialogueGrant::GivesItem(i) if i == "sigil")
            && matches!(&d.requires, Some(Gate::NeedsItem(i)) if i == "bark_shield")
    ));
    assert!(w
        .dialogue
        .iter()
        .any(|d| matches!(d.grant, DialogueGrant::Reveals)));

    // HP combat with armor
    let wraith = w.combat.get("belfry").expect("combat in belfry");
    assert_eq!(wraith.hp, 9);
    assert_eq!(wraith.attack, 4);
    assert_eq!(wraith.armed_by, "ember_blade");
    assert_eq!(wraith.weapon_damage, 3);
    assert_eq!(wraith.armor, Some(("bark_shield".to_string(), 1)));

    // all three spell effect kinds, each with a learn gate
    assert_eq!(w.spells.len(), 3);
    assert!(w
        .spell_rules
        .iter()
        .any(|r| matches!(&r.effect, SpellEffect::SetFlag(f, 1) if f == "span_mended")));
    assert!(w
        .spell_rules
        .iter()
        .any(|r| matches!(&r.effect, SpellEffect::Conjure(i) if i == "ember_blade")));
    assert!(w
        .spell_rules
        .iter()
        .any(|r| matches!(&r.effect, SpellEffect::Buff(f, 1) if f == "blessed")));
    // a spell rule carries its target + fizzle
    let mend = w.spell_rules.iter().find(|r| r.spell == "mend").unwrap();
    assert_eq!(mend.target.as_deref(), Some("bridge"));
    assert!(mend.fizzle_narration.contains("no broken thing"));

    // the LIGHT dimension: dark room, refuel, stranded lose
    let light = w.light.as_ref().expect("a light rule");
    assert_eq!(light.lamp, "lamp");
    assert_eq!(light.start, 8);
    assert_eq!(light.counter, "lamp_oil");
    assert!(light.dark_rooms.contains("cellar"));
    assert_eq!(light.refuels.len(), 1);
    assert_eq!(light.refuels[0].add, 6);
    assert_eq!(light.refuels[0].spent_flag, "spent_oil_flask");
    assert_eq!(light.stranded, Some(("stranded".to_string(), 1)));
    assert!(
        w.lose.iter().any(|l| l.flag == "stranded"),
        "the strand wires a lose condition"
    );

    // objective + lose
    assert_eq!(w.objective.room, "shrine");
    assert_eq!(w.objective.holding, "relic");
    assert!(w
        .lose
        .iter()
        .any(|l| l.flag == "player_wounds" && l.at_least == 12));
    assert_eq!(w.player_max_hp, 12);
}

// ── 3. The validator is NON-VACUOUS: good sources have zero errors; each bad one fires. ──

fn errors(src: &str) -> Vec<String> {
    let world = parse_world(src).expect("syntactically valid");
    validate(&world)
        .into_iter()
        .filter(|i| i.is_error())
        .map(|i| i.message)
        .collect()
}

fn assert_fires(src: &str, needle: &str) {
    let errs = errors(src);
    assert!(
        errs.iter().any(|m| m.contains(needle)),
        "expected an error containing {needle:?}, got: {errs:?}"
    );
    // And parse_dungeon fails closed on it.
    assert!(
        parse_dungeon(src).is_err(),
        "parse_dungeon must refuse this source"
    );
}

#[test]
fn good_sources_have_zero_errors() {
    // Non-vacuity anchor: both shipped-good dungeons validate clean.
    assert!(
        errors(LANTERN_FEN).is_empty(),
        "lantern_fen: {:?}",
        errors(LANTERN_FEN)
    );
    assert!(
        errors(EMBER_OBSERVATORY).is_empty(),
        "ember: {:?}",
        errors(EMBER_OBSERVATORY)
    );
    // And the hand-written Rust dungeons validate clean too (the validator is honest).
    assert!(validate(&attested_dm::sunken_vault())
        .iter()
        .all(|i| !i.is_error()));
    assert!(validate(&attested_dm::starfall_spire())
        .iter()
        .all(|i| !i.is_error()));
    assert!(validate(&attested_dm::deepdark_mine())
        .iter()
        .all(|i| !i.is_error()));
    assert!(validate(&attested_dm::bramble_keep())
        .iter()
        .all(|i| !i.is_error()));
}

const GOOD_BASE: &str = "\
name: T
start: a
objective: reach b holding prize
room a \"A\"
  exit east -> b
room b \"B\"
  items: prize
";

#[test]
fn validator_dangling_exit() {
    assert_fires(
        "start: a\nobjective: reach a holding x\nroom a \"A\"\n  items: x\n  exit north -> nowhere\n",
        "unknown room `nowhere`",
    );
    // The shipped broken.dungeon carries a dangling exit too.
    assert_fires(BROKEN, "unknown room `antechamer`");
}

#[test]
fn validator_win_item_never_placed() {
    assert_fires(
        "start: a\nobjective: reach a holding ghost\nroom a \"A\"\n  exit east -> a\n",
        "holding `ghost`",
    );
}

#[test]
fn validator_unreachable_objective() {
    let src = "\
start: a
objective: reach island holding prize
room a \"A\"
  exit east -> a
room island \"Island\"
  items: prize
  exit north -> island
";
    assert_fires(src, "unreachable");
}

#[test]
fn validator_gate_item_exists_nowhere() {
    let src = "\
start: a
objective: reach b holding prize
room a \"A\"
  exit east -> b requires item skeleton_key
room b \"B\"
  items: prize
";
    assert_fires(src, "skeleton_key");
}

#[test]
fn validator_actor_in_unknown_room() {
    let npc =
        format!("{GOOD_BASE}npc ghost \"Ghost\" in phantom_room\n  topic hi -> reveals \"boo\"\n");
    assert_fires(&npc, "npc `ghost` is placed in unknown room `phantom_room`");

    let combat = format!(
        "{GOOD_BASE}player_hp: 5\ncombat ogre in nowhere hp 3 attack 1\n  weapon prize damage 1\n  victory flag dead\n  victory \"x\"\n  hit \"y\"\n  flail \"z\"\n"
    );
    assert_fires(
        &combat,
        "combat foe `ogre` is placed in unknown room `nowhere`",
    );

    let spell = format!("{GOOD_BASE}spell zap innate\n  in voidroom -> flag lit \"x\"\n");
    assert_fires(&spell, "spell-rule for `zap` names unknown room `voidroom`");
}

#[test]
fn validator_spell_with_no_learn_source() {
    // Learned via a flag that nothing ever sets.
    let src = format!(
        "{GOOD_BASE}spell mend requires flag learned_mend\n  in a on bridge -> flag done \"x\"\n"
    );
    assert_fires(&src, "no rule ever sets that flag");
}

// ── 4. Malformed sources fail closed WITH a line number. ──

#[test]
fn malformed_fails_closed_with_line_number() {
    // An unknown top-level directive on line 3.
    let err = parse_dungeon("start: a\nroom a \"A\"\nwibble wobble\n").unwrap_err();
    assert_eq!(err.line, 3, "reports the offending line");
    assert!(err.message.contains("unknown directive"), "{}", err.message);

    // An unterminated quoted string.
    let err = parse_dungeon("start: a\nroom a \"A\n  exit e -> a\n").unwrap_err();
    assert_eq!(err.line, 2);
    assert!(err.message.contains("unterminated"), "{}", err.message);

    // A missing start: is a whole-file (line 0) error.
    let err = parse_dungeon("room a \"A\"\n  exit e -> a\n").unwrap_err();
    assert_eq!(err.line, 0);
    assert!(err.message.contains("start"), "{}", err.message);

    // An indented line with no open block.
    let err = parse_dungeon("start: a\n  stray indented line\n").unwrap_err();
    assert_eq!(err.line, 2);
    assert!(err.message.contains("indented"), "{}", err.message);
}

// ── 5. The Display of a DungeonError carries the line prefix. ──

#[test]
fn error_display_has_line_prefix() {
    let err = parse_dungeon("start: a\nroom a \"A\"\nwibble\n").unwrap_err();
    assert!(err.to_string().starts_with("line 3:"), "{}", err);
}

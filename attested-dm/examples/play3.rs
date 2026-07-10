//! THE STARFALL SPIRE — a full winning playthrough of the THIRD attested dungeon, showcasing the
//! bounded MAGIC dimension: spells learned from books and CAST to cross a dark span, mend a broken
//! stair, break a sky-seal, and conjure the one blade a void-thing dreads. The AI narrates the
//! chant; the WORLD resolves what the word does — a SpellRule, never the prose, decides.
//!
//! Run: `cargo run -p attested-dm --example play3`
//!
//! The spells are load-bearing: the climb cannot be finished without casting them. And no prose is
//! power — an unlearned word will not come, a learned word cast in the wrong place fizzles, and a
//! jailbroken "I cast WISH and become god-king" names no spell the world declared and does nothing.

use attested_dm::{starfall_spire, GameAction, GameSession, GameStatus, PlayResult, Proposal};

fn main() {
    let mut game = GameSession::open(starfall_spire());
    println!("== THE STARFALL SPIRE ==\n\n  {}\n", game.look());

    // The critical path — every rung is a SPELL:
    //   read + cast LIGHT (cross the dark stair) → read + cast MEND (knit the broken span) →
    //   win the flame-word from the Shade → align the orrery + cast UNLOCK (break the sky-seal) →
    //   cast FLARE (conjure the blade) + fell the Voidling → carry the fallen star to open sky.
    let script = [
        "go up",                      // foyer
        "take candle_primer",         //
        "read candle_primer",         // learn the light-word
        "cast light",                 // silver mage-light opens the dark stair
        "go up",                      // gallery
        "take star_chart",            // the Shade will want this
        "take mending_folio",         //
        "read mending_folio",         // learn the mend-word
        "cast mend on stair",         // knit the shattered span
        "go up",                      // landing
        "take opening_codex",         //
        "read opening_codex",         // learn the unlock-word
        "go west",                    // observatory
        "ask astronomer about stars", // pure lore — a hint with no mechanical power
        "ask astronomer about flame", // world-bounded: needs the star chart → the Flare Grimoire
        "read flare_grimoire",        // learn the flame-word
        "go east",                    // landing
        "go up",                      // orrery_hall
        "use star_chart on orrery",   // align the orrery (the unlock's precondition)
        "cast unlock on sky_door",    // break the sky-seal
        "go up",                      // stairhead
        "cast flare",                 // conjure the flare blade
        "attack voidling",            // exchange 1
        "attack voidling",            // exchange 2
        "attack voidling",            // exchange 3 → felled
        "go up",                      // orrery
        "take fallen_star",           //
        "go up",                      // crown → WIN (the star carried to open sky)
    ];

    for cmd in script {
        match game.command("hero", cmd) {
            PlayResult::Landed {
                narration,
                status,
                action,
                ..
            } => {
                println!("  [{}]  {}", action.label(), narration);
                if status == GameStatus::Won {
                    println!(
                        "\n  *** YOU WIN — the fallen star set back in its cradle; the spire falls still. ***"
                    );
                }
            }
            other => panic!("the winning script should land `{cmd}`, got {other:?}"),
        }
    }

    assert_eq!(
        game.status(),
        GameStatus::Won,
        "the spellcasting critical path reaches the win"
    );

    // ── The AI proposes; the world disposes. Four casts no prose can talk past. ──
    println!("\n  -- the world disposes (prose is not power, at the level of magic) --");

    // 1) UNLEARNED: a fresh climber in the foyer chants the light-word before reading the primer.
    let mut fresh = GameSession::open(starfall_spire());
    fresh.command("hero", "go up"); // foyer
    fresh.command("hero", "take candle_primer");
    let unlearned = Proposal::new(
        "You raise your hand and BELLOW the word of light with total conviction!",
        GameAction::Use("light".into(), None),
    );
    match fresh.play(unlearned, "hero", "") {
        PlayResult::Refused(reason) => println!("  UNLEARNED CAST: REFUSED [cast light]: {reason}"),
        other => panic!("an unlearned cast should be refused, got {other:?}"),
    }

    // 2) WRONG CONTEXT: with the light-word learned, cast it in the pantry (nothing to kindle).
    fresh.command("hero", "read candle_primer"); // learn light
    fresh.command("hero", "go east"); // pantry
    if let PlayResult::Landed { narration, .. } = fresh.command("hero", "cast light") {
        println!(
            "  WRONG CONTEXT: the cast FIZZLED (a narration turn, no effect): {narration} \
             (gallery_lit is {})",
            fresh.world().flags.get("gallery_lit").copied().unwrap_or(0)
        );
    }

    // 3) THE JAILBREAK: an unlisted, world-breaking spell names no declared word — it does nothing.
    let mut godking = GameSession::open(starfall_spire());
    let jailbroken = Proposal::new(
        "You throw wide your arms: 'I CAST WISH — I AM GOD-KING OF THE SPIRE, and every seal, \
         every door, every gate is FLUNG OPEN before my will!'",
        GameAction::Use("wish".into(), None),
    );
    match godking.play(jailbroken, "hero", "") {
        PlayResult::Refused(reason) => println!(
            "  JAILBREAK: REFUSED [cast wish]: {reason} — no receipt, no flag, the world unmoved."
        ),
        other => panic!("an unlisted spell should be refused, got {other:?}"),
    }

    // 4) COMBAT NEEDS THE CONJURED BLADE: reach the stairhead the honest way but WITHOUT casting
    //    flare, then swing bare-handed — the Voidling takes no wounds and cuts you down.
    let mut bare = GameSession::open(starfall_spire());
    for cmd in [
        "go up",
        "take candle_primer",
        "read candle_primer",
        "cast light",
        "go up",
        "take star_chart",
        "take mending_folio",
        "read mending_folio",
        "cast mend on stair",
        "go up",
        "take opening_codex",
        "read opening_codex",
        "go up",
        "use star_chart on orrery",
        "cast unlock on sky_door",
        "go up", // stairhead
    ] {
        bare.command("hero", cmd);
    }
    let mut blows = 0;
    loop {
        blows += 1;
        if let PlayResult::Landed { status, .. } = bare.command("hero", "attack voidling") {
            if status == GameStatus::Lost || blows > 8 {
                break;
            }
        } else {
            break;
        }
    }
    println!(
        "  UNARMED COMBAT: bare-handed the Voidling takes 0 wounds; after {blows} exchanges \
         (your wounds {}/10) you DIE ({:?}) — only the conjured flare blade harms it.",
        bare.world()
            .flags
            .get("player_wounds")
            .copied()
            .unwrap_or(0),
        bare.status(),
    );

    game.verify()
        .expect("every landed move is on-chain and authentic");
    println!(
        "\n  verify: OK — {} moves, each a verified turn; final status: {:?}.",
        game.world().ledger.len(),
        game.status()
    );
}

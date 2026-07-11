//! # overworld — play across a REGION, and watch a gate open on a verified win.
//!
//! The bundled dungeons are individually verifiable games. This example plays TWO of them as
//! LOCATIONS in one [`attested_dm::Region`] (THE DROWNED MARCHES), records each completion through
//! the verification-gated [`attested_dm::RegionProgress::record_completion`], and shows a travel
//! gate that stays SEALED until its prerequisite is cleared and OPENS the moment it is — plus a
//! forged/unfinished completion being REFUSED.
//!
//! Run it:
//!
//! ```text
//!   cargo run -p attested-dm --example overworld
//! ```

use attested_dm::{
    drowned_marches, starfall_spire, sunken_vault, CompletionError, GameSession, GameStatus,
    PlayResult, RegionProgress, TravelError,
};

const SUNKEN_SOLVE: &[&str] = &[
    "go north",
    "take lantern",
    "go down",
    "go down",
    "take rusted_key",
    "go north",
    "use rusted_key on iron_door",
    "go east",
    "take sword",
    "go north",
    "attack warden",
    "go east",
    "take amulet",
    "go up",
];

const STARFALL_SOLVE: &[&str] = &[
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
    "go west",
    "ask astronomer about flame",
    "read flare_grimoire",
    "go east",
    "go up",
    "use star_chart on orrery",
    "cast unlock on sky_door",
    "go up",
    "cast flare",
    "attack voidling",
    "attack voidling",
    "attack voidling",
    "go up",
    "take fallen_star",
    "go up",
];

fn solve(mut game: GameSession, script: &[&str], name: &str) -> GameSession {
    for cmd in script {
        match game.command("hero", cmd) {
            PlayResult::Landed { .. } => {}
            other => panic!("[{name}] `{cmd}` did not land: {other:?}"),
        }
    }
    assert_eq!(game.status(), GameStatus::Won, "[{name}] reaches the win");
    game
}

fn main() {
    let region = drowned_marches();
    assert!(
        region.is_well_formed(),
        "the region validates: {:?}",
        region.validate()
    );

    println!("╔══════════════════════════════════════════════════════════════════════════╗");
    println!("║  {} — {}", region.name, region.blurb);
    println!("╚══════════════════════════════════════════════════════════════════════════╝\n");

    let mut progress = RegionProgress::new(&region);
    println!(
        "You stand at: {}\n",
        region.location(&progress.location).unwrap().name
    );

    // ── The gate BEFORE you have earned the way ───────────────────────────────
    println!("── the map, before you have cleared anything ──");
    match progress.can_travel(&region, "starfall") {
        Ok(()) => println!("  the road to the Starfall Spire is open"),
        Err(TravelError::Locked { to, prerequisite }) => println!(
            "  the road to `{to}` is BARRED — clear `{prerequisite}` first (verified-completion-gated)"
        ),
        Err(e) => println!("  {e}"),
    }
    println!(
        "  (the open road to the Thornmarch Keep is travellable: {})\n",
        progress.can_travel(&region, "thornmarch").is_ok()
    );

    // ── A forged/unfinished completion is REFUSED ─────────────────────────────
    println!("── an UNFINISHED run cannot mint progress ──");
    let mut partial = GameSession::open(sunken_vault());
    partial.command("hero", "go north");
    partial.command("hero", "take lantern");
    match progress.record_completion(&region, "tidewater", &partial) {
        Ok(_) => panic!("an unfinished run must not be credited!"),
        Err(CompletionError::NotWon(s)) => {
            println!("  record_completion(tidewater, <unfinished>) → REFUSED (NotWon: {s:?})\n")
        }
        Err(e) => println!("  refused: {e}\n"),
    }

    // ── Clear the hub the honest way, and the gate OPENS ──────────────────────
    println!("── clear the Tidewater Vault (a genuine, verified win) ──");
    let vault = solve(
        GameSession::open(sunken_vault()),
        SUNKEN_SOLVE,
        "sunken-vault",
    );
    println!(
        "  won in {} landed, verified turns",
        vault.world().ledger.len()
    );
    println!("  chain integrity : {:?}", vault.verify().map(|_| "OK"));
    println!(
        "  re-execution    : {:?}",
        vault.verify_replay().map(|_| "OK")
    );

    // A win for the WRONG dungeon cannot credit the spire (a forged CLAIM).
    match progress.record_completion(&region, "starfall", &vault) {
        Err(CompletionError::WrongGame { expected_game, .. }) => println!(
            "  offering this vault win to clear `starfall` → REFUSED (WrongGame: it plays {expected_game})"
        ),
        other => panic!("a vault win must not credit the spire: {other:?}"),
    }

    progress = progress
        .record_completion(&region, "tidewater", &vault)
        .expect("a verified vault win clears the tidewater vault");
    println!(
        "  cleared `tidewater` ✓  ({}/{} of the region)\n",
        progress.cleared_count(),
        region.locations.len()
    );

    println!("── the map, AFTER clearing the tidewater vault ──");
    match progress.can_travel(&region, "starfall") {
        Ok(()) => println!(
            "  the road to the Starfall Spire is OPEN — the gate lifted on your verified win"
        ),
        Err(e) => panic!("the gate should have opened: {e}"),
    }
    progress = progress
        .travel(&region, "starfall")
        .expect("the gate is open");
    println!(
        "  travelled to: {}\n",
        region.location(&progress.location).unwrap().name
    );

    // ── Clear the spire, and the deep road opens ──────────────────────────────
    println!("── clear the Starfall Spire, and the deep road opens ──");
    let spire = solve(
        GameSession::open(starfall_spire()),
        STARFALL_SOLVE,
        "starfall-spire",
    );
    println!(
        "  won in {} landed, verified turns",
        spire.world().ledger.len()
    );
    progress = progress
        .record_completion(&region, "starfall", &spire)
        .expect("a verified spire win clears the starfall spire");
    println!(
        "  cleared `starfall` ✓  ({}/{} of the region)",
        progress.cleared_count(),
        region.locations.len()
    );
    match progress.can_travel(&region, "venomdeep") {
        Ok(()) => println!("  the deep road to the Venomous Deep is OPEN\n"),
        Err(e) => panic!("the deep road should have opened: {e}"),
    }

    println!(
        "Two dungeons, one world. Each independently verified; each credited ONLY on a re-verified"
    );
    println!(
        "Won chain. The map opens as you honestly clear it — travel is verified-completion-gated."
    );
}

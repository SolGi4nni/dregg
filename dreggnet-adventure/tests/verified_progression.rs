//! The Lean-native Descent crosses the same verifier-generic boundary into two
//! independent feature crates. Neither receives a UGC-shaped mirror.

use dreggnet_adventure::{PlayerIdentity, crowned_line_for, play_a_winning_descent};
use dreggnet_cheevo::{Achievement, CheevoError, CheevoLedger};
use dreggnet_guild::{ClearError, Guild};

/// The crowned run, plus the length of the DAY'S OWN crowned line — the tape is derived from the
/// drawn map (`dungeon_on_dregg::descent::crowned_line`), so a turn count pinned here as a literal
/// would be pinning one day's draw. It read `18` until 2026-07-29.
fn won_by(name: &str) -> (dreggnet_adventure::NativeDescentRun, usize) {
    let hero = PlayerIdentity::new(name);
    let (_, session, run) = play_a_winning_descent(&hero).expect("native crowned run");
    let turns = crowned_line_for(&session).len();
    (run, turns)
}

#[test]
fn one_native_replay_drives_shared_cheevo_and_guild_without_a_ugc_mirror() {
    let (run, turns) = won_by("Mira");

    let mut cheevos = CheevoLedger::new();
    let cheevo = cheevos
        .earn_verified(
            &run,
            Achievement::ReachedDepth {
                var: "depth".into(),
                min: 4,
            },
        )
        .expect("native replay earns through the real shared cheevo ledger");
    assert_eq!(cheevo.player, "Mira");
    assert_eq!(cheevo.turns, turns);
    cheevos
        .reverify_verified(&cheevo, &run)
        .expect("credential independently replays the same native completion");
    assert!(cheevo.seal_intact());
    assert!(cheevo.note == cheevos.minted()[0].note);
    assert!(matches!(
        cheevos.attempt_transfer(&cheevo, "badge-buyer"),
        Err(CheevoError::Soulbound)
    ));

    let who = PlayerIdentity::new("Mira").guild_member();
    let mut guild = Guild::form("Replay Vanguard");
    guild.admit(&who);
    assert_eq!(
        guild
            .board_mut()
            .record_verified_clear(&who, &run)
            .expect("native replay counts through the real shared guild board"),
        turns
    );
    assert_eq!(guild.board().stats().verified_clears, 1);
    assert_eq!(guild.board().stats().total_turns, turns);

    let replay = guild.board_mut().record_verified_clear(&who, &run);
    assert!(matches!(replay, Err(ClearError::AlreadyCounted(_))));
    assert_eq!(guild.board().stats().verified_clears, 1);
}

#[test]
fn actor_root_and_replay_substitution_advance_neither_downstream() {
    let (run, turns) = won_by("Mira");
    let who = PlayerIdentity::new("Mira").guild_member();
    let mallory = PlayerIdentity::new("Mallory").guild_member();

    let mut guild = Guild::form("Replay Vanguard");
    guild.admit(&who);
    guild.admit(&mallory);
    assert!(matches!(
        guild.board_mut().record_verified_clear(&mallory, &run),
        Err(ClearError::ActorMismatch { .. })
    ));
    assert_eq!(guild.board().stats().verified_clears, 0);

    let mut forged = run.clone();
    forged.completion.root[0] ^= 1;
    let mut cheevos = CheevoLedger::new();
    assert!(matches!(
        cheevos.earn_verified(&forged, Achievement::SpeedClear { max_turns: turns }),
        Err(CheevoError::VerifierRejected(_))
    ));
    assert!(matches!(
        guild.board_mut().record_verified_clear(&who, &forged),
        Err(ClearError::VerifierRejected(_))
    ));
    assert!(cheevos.minted().is_empty());
    assert_eq!(guild.board().stats().verified_clears, 0);

    let mut wrong_world = run.clone();
    wrong_world.world.root[0] ^= 1;
    assert!(matches!(
        cheevos.earn_verified(&wrong_world, Achievement::SpeedClear { max_turns: turns }),
        Err(CheevoError::VerifierRejected(_))
    ));
    assert!(matches!(
        guild.board_mut().record_verified_clear(&who, &wrong_world),
        Err(ClearError::VerifierRejected(_))
    ));
    assert!(cheevos.minted().is_empty());
    assert_eq!(guild.board().stats().verified_clears, 0);
}

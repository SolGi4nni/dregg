//! Phase 0 acceptance: the multiway-tug rules DRIVEN on the real executor.
//!
//! Every test commits real cap-bounded turns on a real `spween_dregg::WorldCell` (the
//! deployed `EmbeddedExecutor`). A legal play commits; an illegal play is a real
//! `WorldError::Refused` — and each refusal is paired with a committing legal play so the
//! bite is non-vacuous.

use dregg_multiway_tug::game::MultiwayTug;
use dregg_multiway_tug::reference::{
    ActionKind, Engine, INFLUENCE, Player, ResolvedMove, winner_of,
};
use dregg_multiway_tug::state::SCORE;

/// Deploy + seed a game from `seed`, returning the driver and the reference engine.
fn fresh(seed: u8) -> (MultiwayTug, Engine) {
    let eng = Engine::new(seed as u64);
    let game = MultiwayTug::deploy(seed).expect("deploy");
    let init = eng.projection();
    game.seed(&init).expect("genesis seeds");
    assert_eq!(
        game.read_projection(),
        init,
        "post-genesis matches reference"
    );
    assert_eq!(init.conservation_sum(), 21, "seed conserves 21 favors");
    (game, eng)
}

/// Play the full round on the executor, asserting the executor reproduces the reference
/// at every committed turn. Returns the (game, scored-engine, moves).
fn drive_full_round(seed: u8) -> (MultiwayTug, Engine, Vec<ResolvedMove>) {
    let (game, mut eng) = fresh(seed);
    let mut moves = Vec::new();
    while !eng.round_complete() {
        let mv = eng.play_next();
        let proj = eng.projection();
        game.commit_projection(mv.action().method(), &proj)
            .expect("legal play commits");
        // The executor reproduces the reference exactly.
        assert_eq!(game.read_projection(), proj, "executor matches reference");
        // Conservation holds on every committed post-state.
        assert_eq!(game.read_projection().conservation_sum(), 21);
        // Gap #2 witnessed on-cell: the opponent (not the actor) kept the strongest
        // favor(s) presented — an adversarial pick, not a pre-folded split.
        match &mv {
            ResolvedMove::Gift {
                self_guilds,
                opp_guild,
                ..
            } => {
                let strongest = [self_guilds[0], self_guilds[1], *opp_guild]
                    .into_iter()
                    .max_by_key(|&g| (INFLUENCE[g as usize], std::cmp::Reverse(g)))
                    .unwrap();
                assert_eq!(*opp_guild, strongest, "opponent kept the strongest of 3");
            }
            ResolvedMove::Competition {
                self_guilds,
                opp_guilds,
                ..
            } => {
                let opp_w = INFLUENCE[opp_guilds[0] as usize] + INFLUENCE[opp_guilds[1] as usize];
                let self_w =
                    INFLUENCE[self_guilds[0] as usize] + INFLUENCE[self_guilds[1] as usize];
                assert!(opp_w >= self_w, "opponent kept the heavier pair");
            }
            _ => {}
        }
        moves.push(mv);
    }
    let _ = eng.score();
    let scored = eng.projection();
    game.commit_score(&scored).expect("scoring commits");
    assert_eq!(
        game.read_projection(),
        scored,
        "scored state matches reference"
    );
    assert_eq!(
        scored.conservation_sum(),
        21,
        "conservation survives scoring"
    );
    (game, eng, moves)
}

#[test]
fn full_round_plays_and_matches_reference() {
    // Each of the four actions for each player is a real committed turn (8 action turns
    // + genesis + score), and the executor reproduces the reference throughout.
    let (game, eng, moves) = drive_full_round(7);
    assert_eq!(moves.len(), 8, "two players * four actions");
    // Every action was used exactly once per player (the used-flags carry the stamp).
    for p in [Player::A, Player::B] {
        for a in [
            ActionKind::Secret,
            ActionKind::Discard,
            ActionKind::Gift,
            ActionKind::Competition,
        ] {
            assert!(
                game.read_heap_key(game.dep().flag_key(p, a)) > 0,
                "{p:?}/{a:?} flag stamped"
            );
        }
    }
    // The Secret was scored (gap #1): the round placed 10 favors per player onto guilds +
    // out of play + secret-reveal; the scored winner is the reference winner.
    let proj = eng.projection();
    assert_eq!(proj.scored, 1);
    assert_eq!(game.read_reg("scored"), 1);
    // Scores are monotone and the win registers agree with the reference scoring fn.
    let expected = winner_of(proj.charm, proj.guilds_controlled)
        .map(|p| p as u64 + 1)
        .unwrap_or(0);
    assert_eq!(proj.winner, expected);
    assert_eq!(game.read_reg("winner"), expected);
}

#[test]
fn conservation_break_is_refused_non_vacuously() {
    let (game, mut eng) = fresh(3);
    // Craft an illegal play that CONJURES a favor: place a card on A's board (and its
    // guild score) without removing one from any hand — the conservation sum becomes 22.
    let mut bad = game.read_projection();
    bad.board[0] += 1;
    bad.score[0][0] += 1; // guild 0, player A
    bad.round_actions += 1; // satisfy StrictMonotonic so the ONLY failure is conservation
    assert_eq!(bad.conservation_sum(), 22);
    let err = game
        .commit_projection(ActionKind::Secret.method(), &bad)
        .expect_err("conjuring a favor is refused");
    assert!(
        format!("{err}").contains("sum") || format!("{err}").to_lowercase().contains("refus"),
        "refusal cites the conservation sum: {err}"
    );
    // The parallel LEGAL play commits (non-vacuous).
    let mv = eng.play_next();
    let proj = eng.projection();
    game.commit_projection(mv.action().method(), &proj)
        .expect("the legal play commits");
    assert_eq!(game.read_projection(), proj);
}

#[test]
fn reused_action_is_refused_via_write_once() {
    let (game, mut eng) = fresh(5);
    // A plays one legal action (its first scheduled action).
    let mv = eng.play_next();
    let used = mv.action();
    let player = mv.player();
    let proj = eng.projection();
    game.commit_projection(used.method(), &proj)
        .expect("first use commits");
    let stamp = game.read_heap_key(game.dep().flag_key(player, used));
    assert!(stamp > 0, "flag stamped on first use");

    // Attempt to REUSE the same action for the same player: the only change is a fresh
    // used-flag stamp + a round advance (counts unchanged ⇒ conservation + monotonicity
    // still hold). The write-once flag was already frozen ⇒ refused.
    let mut reuse = game.read_projection();
    reuse.flag[player.idx()][used.idx()] = stamp + 100;
    reuse.round_actions += 1;
    let err = game
        .commit_projection(used.method(), &reuse)
        .expect_err("re-using an action is refused");
    assert!(
        format!("{err}").to_lowercase().contains("write-once")
            || format!("{err}").to_lowercase().contains("refus"),
        "refusal cites write-once: {err}"
    );
    // A DIFFERENT legal action for the next player still commits (non-vacuous).
    let mv2 = eng.play_next();
    let proj2 = eng.projection();
    game.commit_projection(mv2.action().method(), &proj2)
        .expect("a fresh legal action commits");
    assert_eq!(game.read_projection(), proj2);
}

#[test]
fn un_placing_a_favor_is_refused_via_monotonic() {
    let (game, mut eng) = fresh(9);
    // Play until a favor has been placed on a guild.
    let mut placed_guild = None;
    while placed_guild.is_none() {
        let mv = eng.play_next();
        let proj = eng.projection();
        game.commit_projection(mv.action().method(), &proj)
            .expect("commit");
        for g in 0..7 {
            if proj.score[g][0] > 0 {
                placed_guild = Some(g);
                break;
            }
        }
    }
    let g = placed_guild.unwrap();
    // Craft a turn that UN-PLACES A's favor at guild g (score decreases) while leaving the
    // conservation counters untouched (so only Monotonic fails).
    let mut bad = game.read_projection();
    bad.score[g][0] -= 1;
    bad.round_actions += 1;
    let err = game
        .commit_projection(ActionKind::Gift.method(), &bad)
        .expect_err("un-placing a favor is refused");
    assert!(
        format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("refus"),
        "refusal cites monotonic: {err}"
    );
    // A legal play still commits.
    let mv = eng.play_next();
    let proj = eng.projection();
    game.commit_projection(mv.action().method(), &proj)
        .expect("legal commits");
    assert_eq!(game.read_projection(), proj);
}

#[test]
fn forged_method_is_refused_by_default_deny() {
    let (game, mut eng) = fresh(11);
    let proj0 = game.read_projection();
    // A turn under an unknown method matches no dispatch case ⇒ NoTransitionCaseMatched.
    let effects = vec![game.reg_effect("scored", 1)];
    let err = game
        .commit_raw("teleport", effects)
        .expect_err("an unknown method is refused");
    assert!(
        format!("{err}").to_lowercase().contains("refus")
            || format!("{err}").to_lowercase().contains("case"),
        "refusal cites default-deny: {err}"
    );
    // Nothing committed; a legal play still works.
    assert_eq!(game.read_projection(), proj0);
    let mv = eng.play_next();
    let proj = eng.projection();
    game.commit_projection(mv.action().method(), &proj)
        .expect("legal commits");
}

#[test]
fn win_fires_at_threshold_and_matches_reference() {
    // Find a seed the reference resolves to a real winner (>= 11 influence OR >= 4 guilds).
    let seed = (0u8..=255)
        .find(|&s| {
            let mut e = Engine::new(s as u64);
            while !e.round_complete() {
                e.play_next();
            }
            e.score().is_some()
        })
        .expect("some seed yields a winner");
    let (game, eng, _) = drive_full_round(seed);
    let proj = eng.projection();
    assert_ne!(proj.winner, 0, "a winner fired");
    assert!(
        proj.charm[(proj.winner - 1) as usize] >= 11
            || proj.guilds_controlled[(proj.winner - 1) as usize] >= 4,
        "the winner really met a threshold"
    );
    assert_eq!(
        game.read_reg("winner"),
        proj.winner,
        "executor recorded the winner"
    );
}

#[test]
fn false_win_claim_is_refused() {
    // Find a seed + a player who meets NEITHER win threshold, and forge them as winner.
    let mut chosen: Option<(u8, u64)> = None;
    for s in 0u8..=255 {
        let mut e = Engine::new(s as u64);
        while !e.round_complete() {
            e.play_next();
        }
        let _ = e.score();
        let p = e.projection();
        for who in 0..2usize {
            if p.charm[who] < 11 && p.guilds_controlled[who] < 4 {
                chosen = Some((s, who as u64 + 1));
                break;
            }
        }
        if chosen.is_some() {
            break;
        }
    }
    let (seed, forged_winner) = chosen.expect("a player failing both thresholds exists");

    // Drive the round to completion WITHOUT the score turn.
    let (game, mut eng) = fresh(seed);
    while !eng.round_complete() {
        let mv = eng.play_next();
        let proj = eng.projection();
        game.commit_projection(mv.action().method(), &proj)
            .expect("commit");
    }
    let honest = {
        let _ = eng.score();
        eng.projection()
    };
    // Forge: claim `forged_winner` won though they met no threshold.
    let mut forged = honest.clone();
    forged.winner = forged_winner;
    let err = game
        .commit_projection(SCORE, &forged)
        .expect_err("a false win claim is refused");
    assert!(
        format!("{err}").to_lowercase().contains("refus")
            || format!("{err}").to_lowercase().contains("any"),
        "refusal cites the win implication: {err}"
    );
    // The HONEST scoring commits (non-vacuous).
    game.commit_score(&honest).expect("honest scoring commits");
    assert_eq!(game.read_reg("winner"), honest.winner);
}

#[test]
fn opponent_pick_is_a_real_choice_not_pre_folded() {
    // Gap #2 at the reference level: the placement depends on the OPPONENT's decision, not
    // an actor pre-fold. Same three presented favors, the opponent keeps the strongest —
    // a different (weaker) pick would place differently.
    use dregg_multiway_tug::reference::{opponent_comp_pick, opponent_gift_pick};
    let present = [6u8, 5, 0]; // influence 5, 4, 2
    let opp = opponent_gift_pick(&present);
    assert_eq!(opp, 6, "opponent keeps the strongest presented favor");
    let weak = *present
        .iter()
        .min_by_key(|&&g| INFLUENCE[g as usize])
        .unwrap();
    assert_ne!(
        opp, weak,
        "the choice is not fixed to the actor's preference"
    );

    let pair0 = [6u8, 6]; // 10
    let pair1 = [0u8, 1]; // 4
    assert_eq!(
        opponent_comp_pick(pair0, pair1),
        pair0,
        "opponent keeps heavier pair"
    );
}

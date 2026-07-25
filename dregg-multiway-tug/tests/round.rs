//! Phase 0 acceptance: the multiway-tug rules DRIVEN on the real executor.
//!
//! Every test commits real cap-bounded turns on a real `spween_dregg::WorldCell` (the
//! deployed `EmbeddedExecutor`). A legal play commits; an illegal play is a real
//! `WorldError::Refused` — and each refusal is paired with a committing legal play so the
//! bite is non-vacuous.
//!
//! ⚑ **THE ROUND IS 12 TURNS NOW.** The engine is I-cut-you-choose: a Gift or a Competition
//! only PRESENTS favors into escrow, and the OTHER seat's RESPONSE places them. A response is
//! a real committed turn dispatched under the Lean-emitted `respond_gift` / `respond_comp`
//! case, which also carries the `pending_kind` `DeltaEquals{-1}` / `DeltaEquals{-2}` teeth —
//! so the escrow marker cannot be cleared except by answering the offer that opened it.
//!
//! The single-action tests below deliberately drive the two PRIVATE actions (Secret /
//! Discard), which open no offer, so their refusal/commit pair is one turn deep. That is a
//! legal opening line: Lean `every_action_order_is_feasible` proves all 24 orders are
//! card-feasible, and this engine has no schedule to obey.

use dregg_multiway_tug::game::MultiwayTug;
use dregg_multiway_tug::reference::{
    ActionKind, Decision, Engine, INFLUENCE, OfferShape, PendingOffer, Player, ResolvedMove,
    greedy_policy,
};
use dregg_multiway_tug::rules;

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

/// The first legal decision of `kind` for the seat to move.
fn first_of(eng: &Engine, kind: ActionKind) -> Decision {
    eng.legal_decisions()
        .into_iter()
        .find(|d| d.kind() == Some(kind))
        .unwrap_or_else(|| panic!("{kind:?} has no legal decision right now"))
}

/// Apply `d` on the reference and commit the resulting projection as one real executor turn.
fn commit(game: &MultiwayTug, eng: &mut Engine, d: Decision) -> ResolvedMove {
    let p = eng.current_player();
    let mv = eng.apply(p, d).expect("the decision is legal");
    let proj = eng.projection();
    game.commit_projection(mv.method(), &proj)
        .expect("a legal play commits");
    assert_eq!(game.read_projection(), proj, "executor matches reference");
    assert_eq!(game.read_projection().conservation_sum(), 21);
    mv
}

/// Play a whole round under the greedy example agent, committing all 12 turns (8 actions +
/// 4 responses) on the executor, then score.
fn drive_full_round(seed: u8) -> (MultiwayTug, Engine, Vec<ResolvedMove>) {
    let (game, mut eng) = fresh(seed);
    let mut moves = Vec::new();
    while !eng.round_complete() {
        let d = greedy_policy(&eng);
        moves.push(commit(&game, &mut eng, d));
    }
    eng.score().expect("the Lean oracle adjudicates the round");
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
    let (game, eng, moves) = drive_full_round(7);
    assert_eq!(moves.len(), 12, "8 action turns + 4 responses");
    assert_eq!(
        moves.iter().filter(|m| m.action_kind().is_some()).count(),
        8,
        "two players * four actions"
    );
    assert_eq!(
        moves
            .iter()
            .filter(|m| matches!(m, ResolvedMove::Respond { .. }))
            .count(),
        4,
        "each player answers the opponent's two offers"
    );
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
    let proj = eng.projection();
    assert_eq!(proj.scored, 1);
    assert_eq!(game.read_reg("scored"), 1);
    // ⚑ The expected winner is the PROVEN Lean's, asked independently of the engine. There is no
    // Rust rule left to compare against: `winner_of` is deleted.
    let expected = rules::adjudicate(&proj.score)
        .expect("the oracle answers")
        .winner_code;
    assert_eq!(proj.winner, expected);
    assert_eq!(game.read_reg("winner"), expected);
}

/// **THE GENESIS ONE-SHOT CANARY** (DELIVER #4): the permissive `genesis` write-hatch is
/// closed. `fresh` already commits the FIRST genesis (the sentinel `0 → 1` write the executor
/// injects — admitted exactly once, `Equals{1} ∧ DeltaEquals{1}` on `GENESIS_DONE_EXT_KEY`
/// with the sentinel still field-zero). A SECOND genesis staple re-hits `old == 1`, where the
/// injected `→ 1` write gives `Δ == 0 ≠ 1` and the two teeth are jointly UNSATISFIABLE — so it
/// is REFUSED. Without the one-shot teeth (the old `constraints: vec![]`), the re-staple would
/// commit and silently overwrite the whole board; this pair (admits once, refuses the restage)
/// is the canary.
#[test]
fn genesis_restaple_is_refused_one_shot() {
    let (game, eng) = fresh(9);
    let restage = eng.projection();
    let err = game
        .seed(&restage)
        .expect_err("a post-deploy genesis re-staple is refused (one-shot genesis)");
    assert!(
        format!("{err}").to_lowercase().contains("refus"),
        "the re-staple refusal is a real WorldError::Refused: {err}"
    );
    // NON-VACUOUS: the board still reads the seeded state (the refused re-staple wrote nothing),
    // and a legal play still commits off it.
    assert_eq!(
        game.read_projection(),
        restage,
        "the refused re-staple left the board untouched"
    );
    let mut eng2 = eng;
    let d = first_of(&eng2, ActionKind::Secret);
    commit(&game, &mut eng2, d);
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
    let d = first_of(&eng, ActionKind::Secret);
    commit(&game, &mut eng, d);
}

#[test]
fn reused_action_is_refused_via_write_once() {
    let (game, mut eng) = fresh(5);
    // A plays one legal PRIVATE action (Secret opens no offer, so play can continue without
    // a response turn).
    let d = first_of(&eng, ActionKind::Secret);
    let mv = commit(&game, &mut eng, d);
    let player = mv.player();
    let used = mv.action();
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
    // The OTHER seat's Secret still commits (non-vacuous — a different heap flag).
    assert_eq!(eng.current_player(), player.other());
    let d2 = first_of(&eng, ActionKind::Secret);
    commit(&game, &mut eng, d2);
}

#[test]
fn un_placing_a_favor_is_refused_via_monotonic() {
    let (game, mut eng) = fresh(9);
    let mut placed_guild = None;
    while placed_guild.is_none() {
        let d = greedy_policy(&eng);
        commit(&game, &mut eng, d);
        let proj = eng.projection();
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
    // (`secret` is the carrier method: its `pending_kind` teeth are `Equals{0} ∧
    // DeltaEquals{0}`, satisfied on a cleared table, so MONOTONIC is the only tooth left to
    // bite.)
    let mut bad = game.read_projection();
    assert_eq!(
        bad.pending_kind, 0,
        "a placement means the table was answered"
    );
    bad.score[g][0] -= 1;
    bad.round_actions += 1;
    let err = game
        .commit_projection(ActionKind::Secret.method(), &bad)
        .expect_err("un-placing a favor is refused");
    assert!(
        format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("refus"),
        "refusal cites monotonic: {err}"
    );
    // A legal play still commits.
    let d = greedy_policy(&eng);
    commit(&game, &mut eng, d);
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
    let d = first_of(&eng, ActionKind::Secret);
    commit(&game, &mut eng, d);
}

/// ⚑ **THE ESCROW MARKER IS DEPLOYED TEETH, NOT BOOKKEEPING.** A `gift` commits
/// `pending_kind` `0 → 1` (`Equals{1} ∧ DeltaEquals{1}`), and only a `respond_gift` may take
/// it back down (`DeltaEquals{-1}`). So: the cut commits; a `secret` that tries to walk away
/// from the table is REFUSED (it carries `Equals{0} ∧ DeltaEquals{0}`, jointly unsatisfiable
/// against a standing offer); and the honest `respond_gift` commits, placing the escrow.
#[test]
fn a_standing_offer_must_be_answered_before_play_continues() {
    let (game, mut eng) = fresh(13);
    // The cut commits: three favors leave the hand into escrow.
    let gift = first_of(&eng, ActionKind::Gift);
    let mv = commit(&game, &mut eng, gift);
    assert_eq!(mv.method(), "gift");
    assert_eq!(eng.projection().pending_kind, 1, "a gift is on the table");
    assert_eq!(
        game.read_heap_key(game.dep().pending_kind_key()),
        1,
        "the executor committed the escrow marker"
    );

    // DUCKING THE TABLE IS REFUSED. Forge the post-state of the responder taking their own
    // Secret instead of answering: counts conserve and the flag is fresh, but `secret`'s
    // pending_kind teeth demand the marker be 0 and unchanged, and it is 1.
    let responder = eng.current_player();
    let mut duck = game.read_projection();
    duck.round_actions += 1;
    duck.flag[responder.idx()][ActionKind::Secret.idx()] = duck.round_actions;
    duck.hand[responder.idx()] -= 1;
    duck.secret_count[responder.idx()] = 1;
    assert_eq!(duck.conservation_sum(), 21, "the forgery conserves");
    let err = game
        .commit_projection("secret", &duck)
        .expect_err("no action may be taken while an offer stands");
    assert!(
        format!("{err}").to_lowercase().contains("refus")
            || format!("{err}").to_lowercase().contains("heap"),
        "the refusal cites the escrow marker: {err}"
    );

    // THE ANSWER COMMITS (non-vacuous), and clears the marker.
    let resp = commit(&game, &mut eng, Decision::Respond { pick: 0 });
    assert_eq!(resp.method(), "respond_gift");
    assert!(
        matches!(&resp, ResolvedMove::Respond { taker_cards, cutter_cards, .. }
                 if taker_cards.len() == 1 && cutter_cards.len() == 2),
        "the responder takes one favor and leaves two: {resp:?}"
    );
    assert_eq!(
        resp.played_cards(),
        Vec::<u8>::new(),
        "a response spends no card"
    );
    assert_eq!(
        game.read_heap_key(game.dep().pending_kind_key()),
        0,
        "the answered offer clears the marker"
    );
    // The escrow really landed on the two boards.
    let proj = eng.projection();
    assert_eq!(proj.board[0] + proj.board[1], 3, "all three favors placed");
    assert_eq!(proj.conservation_sum(), 21);
}

#[test]
fn win_fires_at_threshold_and_matches_reference() {
    // Find a seed the greedy agent resolves to a real THRESHOLD winner (>= 11 influence OR >= 4
    // guilds) — clause 0..3 of the terminal rule, the region the old gate could express.
    let seed = (0u8..=255)
        .find(|&s| {
            let (mut e, _) = dregg_multiway_tug::reference::play_round(s as u64);
            e.score().expect("oracle").is_some() && e.win_branch() <= 3
        })
        .expect("some seed yields a threshold winner");
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

/// ⚑ **THE FALSIFIER FOR THE WHOLE LANE, AT THE EXECUTOR.** A round where NEITHER seat cleared a
/// threshold used to be uncommittable as a win: the single `score` case's gate was
/// `AnyOf[not(winner==p), charm>=11, guilds>=4]`, and Lean's own `winTooth_admits_iff_Won` proved
/// that gate IS the predicate `Won`. So the adjudicated winner the proven `roundWinner` names was
/// refused BY THE DEPLOYED REFEREE, and the played game had to answer "draw" — 78.5% of the time.
///
/// This drives such a round on the real executor and requires the win to LAND, under the clause
/// method (`score_lead_*` / `score_rowlead_*`) the oracle named. If the teeth ever regress to the
/// absolute bar, this test goes red rather than the draw rate silently returning.
#[test]
fn an_adjudicated_sub_threshold_win_commits_on_the_executor() {
    let seed = (0u8..=255)
        .find(|&s| {
            let (mut e, _) = dregg_multiway_tug::reference::play_round(s as u64);
            let w = e.score().expect("oracle");
            // A tie-break clause (4..7): a real winner that cleared NO absolute bar.
            w.is_some() && e.win_branch() >= 4
        })
        .expect("some seed is decided by a tie-break clause, not a threshold");

    let (game, eng, _) = drive_full_round(seed);
    let proj = eng.projection();
    let who = (proj.winner - 1) as usize;
    assert_ne!(proj.winner, 0, "the round has an adjudicated winner");
    assert!(
        proj.charm[who] < 11 && proj.guilds_controlled[who] < 4,
        "the winner cleared NEITHER absolute bar (charm {} rows {}) — this is exactly the round \
         the old gate refused",
        proj.charm[who],
        proj.guilds_controlled[who]
    );
    assert_eq!(
        game.read_reg("winner"),
        proj.winner,
        "the EXECUTOR committed the adjudicated winner"
    );
    assert!(
        eng.win_branch() >= 4 && eng.win_branch() <= 7,
        "decided by a tie-break clause, got {}",
        eng.win_branch()
    );
}

/// The old `score` method is GONE from the emitted program, so a stale caller that still names it
/// is DEFAULT-DENIED (`Cases` rejects when no case matches) rather than scoring under teeth that
/// no longer exist. This is the atomicity tooth: artifact and caller move together or nothing
/// commits.
#[test]
fn the_old_bare_score_method_is_default_denied() {
    let (game, mut eng) = fresh(7);
    while !eng.round_complete() {
        let d = greedy_policy(&eng);
        commit(&game, &mut eng, d);
    }
    eng.score().expect("oracle");
    let honest = eng.projection();
    let err = game
        .commit_projection("score", &honest)
        .expect_err("the retired `score` method no longer matches any case");
    assert!(
        format!("{err}").to_lowercase().contains("refus")
            || format!("{err}").to_lowercase().contains("case"),
        "refusal cites method dispatch: {err}"
    );
    // And the round DOES score under the clause method (non-vacuous).
    game.commit_score(&honest).expect("clause scoring commits");
    assert_eq!(game.read_reg("winner"), honest.winner);
}

/// A win claim the terminal rule does NOT make is refused by the deployed clause teeth. The claim
/// is forged under the clause the ORACLE named (so method dispatch cannot be what refuses it) —
/// the `winner == w` tooth of that clause is what bites. Win-safety survived the gate change.
#[test]
fn false_win_claim_is_refused() {
    // Drive the round to completion WITHOUT the score turn.
    let (game, mut eng) = fresh(11);
    while !eng.round_complete() {
        let d = greedy_policy(&eng);
        commit(&game, &mut eng, d);
    }
    eng.score().expect("oracle");
    let honest = eng.projection();
    let branch = eng.win_branch();
    let method = dregg_multiway_tug::state::score_method(branch);

    // Forge: claim a DIFFERENT seat won, under the very clause the model selected.
    let forged_winner = if honest.winner == 1 { 2 } else { 1 };
    let mut forged = honest.clone();
    forged.winner = forged_winner;
    let err = game
        .commit_projection(&method, &forged)
        .expect_err("a false win claim is refused by the clause's own winner tooth");
    assert!(
        format!("{err}").to_lowercase().contains("refus")
            || format!("{err}").to_lowercase().contains("any"),
        "refusal cites the clause win tooth: {err}"
    );

    // And naming a DIFFERENT clause for the honest winner is refused too (the clause guards
    // partition, so only the model's clause can admit).
    let other = if branch == 0 { 1 } else { 0 };
    let wrong_clause = dregg_multiway_tug::state::score_method(other);
    let err2 = game
        .commit_projection(&wrong_clause, &honest)
        .expect_err("naming the wrong clause is refused");
    assert!(!format!("{err2}").is_empty());

    // The HONEST scoring commits (non-vacuous).
    game.commit_score(&honest).expect("honest scoring commits");
    assert_eq!(game.read_reg("winner"), honest.winner);
}

/// The SPLIT is the other seat's, not the cutter's: over ONE pending offer the two answers
/// place different favors on the responder's side, and the cutter cannot answer at all. This
/// is the rule-level content the deleted `opponent_gift_pick` / `opponent_comp_pick`
/// `max_by_key`s only pretended to have — they were the ACTOR computing the opponent's move.
#[test]
fn the_split_belongs_to_the_other_seat() {
    // A cut of the three strongest favors: the responder's two answers are not equivalent.
    let offer = PendingOffer {
        proposer: Player::A,
        shape: OfferShape::Gift([20, 16, 0]), // guilds 6, 5, 0 -> influence 5, 4, 2
    };
    let weight = |cards: &[u8]| -> u8 {
        cards
            .iter()
            .map(|&c| INFLUENCE[dregg_multiway_tug::reference::deck_guild(u64::from(c)) as usize])
            .sum()
    };
    let (t0, c0) = offer.split(0).unwrap();
    let (t2, c2) = offer.split(2).unwrap();
    assert_eq!(weight(&t0), 5, "taking side 0 takes the 5-influence favor");
    assert_eq!(weight(&t2), 2, "taking side 2 takes a 2-influence favor");
    assert_ne!(
        (weight(&t0), weight(&c0)),
        (weight(&t2), weight(&c2)),
        "the responder's choice changes who gets what"
    );

    // And on the live engine the cutter is refused while the other seat lands.
    let mut eng = Engine::new(21);
    let gift = first_of(&eng, ActionKind::Gift);
    let cutter = eng.current_player();
    eng.apply(cutter, gift).expect("the cut is legal");
    assert!(
        eng.apply(cutter, Decision::Respond { pick: 0 }).is_err(),
        "the cutter may never answer their own cut"
    );
    eng.apply(cutter.other(), Decision::Respond { pick: 0 })
        .expect("the OTHER seat answers");
}

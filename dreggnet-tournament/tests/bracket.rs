//! The no-cheat tournament bracket, DRIVEN end-to-end (not named):
//!
//! * a REAL winning submission ADVANCES and a FORGED one does NOT — non-vacuous (the
//!   exact rejection is asserted, and the forger is absent from the advancers);
//! * ties break by FEWER TURNS (a 3-move win beats a 5-move win on the same universe);
//! * an EQUAL-turns tie breaks DETERMINISTICALLY by seed index (stable across runs);
//! * the bracket runs to a CHAMPION — the last verified survivor — over multiple rounds;
//! * a competitor CANNOT advance without a verified win: a match with no verified win
//!   advances NOBODY, and a bracket of only cheats/no-shows crowns NO champion;
//! * even a BYE requires a verified win (a lone entrant must win a qualifying round);
//! * round universes are FRESH + FAIR: each round is the beacon-derived universe every
//!   competitor shares, and the round seeds are a reproducible record;
//! * the succinct PROOF accept-path is wired + gated (a proof to a non-proof universe is
//!   refused).

use dreggnet_tournament::{
    Entrant, RoundUniverse, SideOutcome, Submission, Tournament, round_epoch,
};
use dungeon_on_dregg::{CH_CLAIM, CH_DESCEND, CH_RETREAT, CH_TAKE_LANTERN, DUNGEON};
use ugc_dregg::{ProofCompletion, Universe, WinCondition};

// ── round-universe providers ────────────────────────────────────────────────────

/// The fresh, fair, beacon-seeded PROCGEN world for a round: everyone derives the
/// identical daily universe from the round's epoch commitment.
fn procgen_rounds() -> RoundUniverse {
    Box::new(|_round, epoch| {
        Universe::daily("tournament-descent", epoch).expect("the daily universe publishes")
    })
}

/// A fixed AUTHORED world (the salt-shore dungeon) for every round — used to drive the
/// turns tiebreak, where two DIFFERENT-length valid winning lines exist. Still fair (the
/// same universe for all competitors that round).
fn salt_shore_rounds() -> RoundUniverse {
    Box::new(|_round, _epoch| {
        Universe::authored(
            "The Salt Shore Descent",
            "attested-dm-salvage",
            DUNGEON,
            WinCondition::ended_with(&[("gold", 500)]),
        )
        .expect("the salt-shore dungeon is a valid universe")
    })
}

/// The number of rooms in a generated linear dungeon (one winning move per room).
fn rooms(u: &Universe) -> usize {
    u.source().matches("=== room").count()
}

/// The honest winning move sequence for a generated procgen dungeon: choice 0 in every
/// room (take the key, press onward, descend the gate, seize the hoard).
fn procgen_win(u: &Universe) -> Vec<usize> {
    vec![0usize; rooms(u)]
}

/// An honest procgen competitor — plays the real winning line every round.
fn procgen_honest(name: &str) -> Entrant {
    Entrant::new(name, Box::new(|u| Submission::Play(procgen_win(u))))
}

/// A procgen FORGER — records the honest win, then retcons room-0's move to "press on
/// empty-handed" (choice 1). On replay the keyless descent diverges / is refused.
fn procgen_forger(name: &str) -> Entrant {
    Entrant::new(
        name,
        Box::new(|u| Submission::Forged {
            base_moves: procgen_win(u),
            tamper_step: 0,
            tamper_choice: 1,
        }),
    )
}

// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn a_real_win_advances_and_a_forged_run_does_not() {
    // One match: an honest player vs a forger, on a fresh beacon-seeded procgen round.
    let mut t = Tournament::new([0x11; 32], procgen_rounds());
    t.enter(procgen_honest("ada"))
        .enter(procgen_forger("mallory"));
    let out = t.run();

    let round0 = &out.rounds[0];
    let m = &round0.matches[0];

    // The honest run VERIFIED; the forged run was REJECTED by the no-cheat gate.
    assert!(
        matches!(m.a_outcome, SideOutcome::Verified { .. }),
        "the honest run must verify, got {:?}",
        m.a_outcome
    );
    match &m.b_outcome {
        SideOutcome::Rejected { reason } => assert!(
            reason.contains("re-verification"),
            "the forged run must be rejected on re-verification, got: {reason}"
        ),
        other => panic!("the forged run must be REJECTED, got {other:?}"),
    }

    // Non-vacuous: the honest player advanced; the forger is the champion of NOTHING.
    let champ = out.champion.expect("a verified survivor is champion");
    assert_eq!(champ.name, "ada", "only the verified win advances");
    assert_eq!(round0.advancers().len(), 1);
    assert_eq!(round0.advancers()[0].name, "ada");
    assert!(
        !round0.advancers().iter().any(|c| c.name == "mallory"),
        "a forged run NEVER advances"
    );
}

#[test]
fn ties_break_by_fewer_turns() {
    // Same authored universe for both; a 3-move win vs a valid 5-move detour win.
    let mut t = Tournament::new([0x22; 32], salt_shore_rounds());
    t.enter(Entrant::honest(
        "sprinter",
        vec![CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM],
    ))
    .enter(Entrant::honest(
        "wanderer",
        vec![
            CH_TAKE_LANTERN,
            CH_RETREAT,
            CH_TAKE_LANTERN,
            CH_DESCEND,
            CH_CLAIM,
        ],
    ));
    let out = t.run();

    let m = &out.rounds[0].matches[0];
    assert_eq!(
        m.a_outcome.verified_turns(),
        Some(3),
        "the sprinter won in 3"
    );
    assert_eq!(
        m.b_outcome.verified_turns(),
        Some(5),
        "the wanderer won in 5"
    );
    assert_eq!(
        out.champion.expect("a champion").name,
        "sprinter",
        "the FEWER-turns verified win advances"
    );
}

#[test]
fn equal_turns_break_deterministically_by_seed() {
    // Two identical honest wins (equal verified turns) — the tie breaks by seed index,
    // deterministically. Running twice yields the SAME champion.
    let champ_of = || {
        let mut t = Tournament::new([0x33; 32], procgen_rounds());
        t.enter(procgen_honest("seed0"))
            .enter(procgen_honest("seed1"));
        t.run().champion.expect("a champion").name
    };
    let a = champ_of();
    let b = champ_of();
    assert_eq!(a, "seed0", "equal turns → the lower seed advances");
    assert_eq!(a, b, "the deterministic tiebreak is stable across runs");
}

#[test]
fn the_bracket_runs_to_a_champion() {
    // Four honest competitors over a two-round single-elim bracket.
    let mut t = Tournament::new([0x44; 32], procgen_rounds());
    for name in ["ada", "bran", "cy", "del"] {
        t.enter(procgen_honest(name));
    }
    let out = t.run();

    assert_eq!(out.rounds.len(), 2, "4 competitors → 2 rounds");
    // Every advancement in the whole bracket is a VERIFIED win.
    for r in &out.rounds {
        for c in r.advancers() {
            let m = r
                .matches
                .iter()
                .find(|m| m.advanced.as_ref() == Some(&c))
                .unwrap();
            let side = if m.a.as_ref() == Some(&c) {
                &m.a_outcome
            } else {
                &m.b_outcome
            };
            assert!(
                matches!(side, SideOutcome::Verified { .. }),
                "an advancer must carry a verified win, got {side:?}"
            );
        }
    }
    // Round 1 halves the field (2 survivors); round 2 crowns 1.
    assert_eq!(out.rounds[0].advancers().len(), 2);
    assert_eq!(out.rounds[1].advancers().len(), 1);
    assert!(
        out.champion.is_some(),
        "the last verified survivor is champion"
    );
}

#[test]
fn cannot_advance_without_a_verified_win() {
    // A match of a forger vs a no-show: NEITHER posts a verified win → NOBODY advances.
    let mut t = Tournament::new([0x55; 32], procgen_rounds());
    t.enter(procgen_forger("mallory"))
        .enter(Entrant::no_show("ghost"));
    let out = t.run();

    let m = &out.rounds[0].matches[0];
    assert!(
        matches!(m.a_outcome, SideOutcome::Rejected { .. }),
        "the forger is rejected"
    );
    assert!(
        matches!(m.b_outcome, SideOutcome::Absent),
        "the no-show is absent"
    );
    assert!(
        m.advanced.is_none(),
        "with no verified win, NOBODY advances — the no-cheat gate bites"
    );
    assert!(
        out.champion.is_none(),
        "a bracket with no verified win crowns NO champion"
    );
}

#[test]
fn a_lone_entrant_must_win_a_qualifying_round() {
    // A bye is not a free pass: a single entrant plays a padded qualifying round and must
    // post a verified win to be champion.
    let mut honest = Tournament::new([0x66; 32], procgen_rounds());
    honest.enter(procgen_honest("solo"));
    assert_eq!(
        honest
            .run()
            .champion
            .expect("a verified solo is champion")
            .name,
        "solo"
    );

    let mut cheat = Tournament::new([0x66; 32], procgen_rounds());
    cheat.enter(procgen_forger("solo-cheat"));
    assert!(
        cheat.run().champion.is_none(),
        "a lone forger cannot win the qualifying round — no verified win, no champion"
    );
}

#[test]
fn rounds_are_fresh_and_fair() {
    let seed = [0x77; 32];
    let mut t = Tournament::new(seed, procgen_rounds());
    for name in ["ada", "bran", "cy", "del"] {
        t.enter(procgen_honest(name));
    }
    let out = t.run();

    // Each round's universe is the beacon-derived universe every competitor shares, and
    // anyone holding the base seed re-derives it from the round epoch.
    for (i, r) in out.rounds.iter().enumerate() {
        assert_eq!(r.round, i);
        assert_eq!(
            r.epoch,
            round_epoch(&seed, i),
            "the round epoch is reproducible"
        );
        let expected =
            Universe::daily("tournament-descent", &r.epoch).expect("re-derive the round universe");
        assert_eq!(
            r.universe_id,
            expected.id(),
            "the round universe is exactly the beacon-derived one — fair + re-derivable"
        );
    }
    // Fresh: successive rounds use DIFFERENT universes (a new beacon seed each round).
    assert_ne!(
        out.rounds[0].universe_id, out.rounds[1].universe_id,
        "each round is a fresh universe"
    );
}

#[test]
fn the_succinct_proof_path_is_wired_and_gated() {
    // The proof accept-path exists and is GATED: a proof submitted to a universe that is
    // not proof-backed is refused (NotProofBacked). (A real fold-proof round is the same
    // named frontier ugc-dregg documents — the run→leaves→fold glue.)
    let mut t = Tournament::new([0x88; 32], procgen_rounds());
    t.enter(Entrant::new(
        "prover",
        Box::new(|u: &Universe| {
            Submission::Proof(Box::new(ProofCompletion {
                universe: u.id(),
                player: "prover".into(),
                proof_bytes: vec![0u8; 32], // not a real proof; the point is the gate
                claimed_turns: 1,
            }))
        }),
    ))
    .enter(Entrant::no_show("bye"));
    let out = t.run();

    let m = &out.rounds[0].matches[0];
    match &m.a_outcome {
        SideOutcome::Rejected { reason } => assert!(
            reason.contains("does not accept succinct proof"),
            "a proof to a non-proof universe is refused, got: {reason}"
        ),
        other => panic!("the proof path must be gated, got {other:?}"),
    }
    assert!(
        out.champion.is_none(),
        "an ungated-away proof crowns no champion"
    );
}

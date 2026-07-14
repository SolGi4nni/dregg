//! `dreggnet-cheevo`, DRIVEN end-to-end (not named) — an achievement is a PROOF you
//! earned it, backed by a verified run, minted SOULBOUND:
//!
//! * a real verified run that satisfies the predicate EARNS the cheevo (depth / no-death /
//!   speed), and it mints a soulbound asset carrying the run's provenance;
//! * a real verified run that does NOT satisfy the predicate earns NOTHING (non-vacuous:
//!   a shallow win earns no reached-depth cheevo, a shield-broken win earns no no-death
//!   cheevo, a slow win earns no speed cheevo);
//! * a FORGED run (edited moves that no longer verify) earns NOTHING — the no-cheat gate
//!   bites before any predicate is evaluated;
//! * a cheevo is SOULBOUND — the transfer path is refused (it can't be sold), and a
//!   laundered record (re-bound onto a buyer) fails re-verification;
//! * an earned cheevo RE-VERIFIES independently (the run re-passes the no-cheat verify +
//!   the predicate re-holds + the note is still owner-bound);
//! * a season CHAMPION cheevo is earned over the season's no-cheat hall-of-fame; a
//!   non-champion earns nothing.

use dregg_season::{CarryForwardPolicy, Season};
use dungeon_on_dregg::{CH_CLAIM, CH_DESCEND, CH_RETREAT, CH_TAKE_LANTERN, DUNGEON};
use ugc_dregg::{Completion, Registry, Universe, WinCondition, record_playthrough};

use dreggnet_cheevo::{Achievement, CheevoError, CheevoLedger, Witness};

// ═══════════════════════════════════════════════════════════════════════════════
// Test worlds — authored spween scenes with a `depth` counter and a `shield_broken`
// hazard flag, each with a DEEP/reckless winning path and a SHALLOW/careful one, so a
// predicate genuinely distinguishes two REAL verified wins.
// ═══════════════════════════════════════════════════════════════════════════════

/// A descent world: the deep shaft increments `depth` three times; a side crack reaches
/// the same vault at `depth == 0`. Both routes seize the relic (`gold == 500`) and END.
const DESCENT: &str = r#"---
id: cheevo-descent
title: Cheevo Descent Trial
weight: 1
---

=== mouth

You stand at the mouth of a black pit. A shaft plunges down; a side crack hugs the wall.

* [Descend the deep shaft]
  ~ depth += 1
  -> deep1

* [Slip through the side crack]
  -> shallow

=== deep1

The shaft narrows. Cold air rises.

* [Descend deeper]
  ~ depth += 1
  -> deep2

=== deep2

Deeper still. The dark is total.

* [Descend to the vault floor]
  ~ depth += 1
  -> vault

=== shallow

The crack opens onto a ledge above the vault.

* [Creep along the ledge to the vault]
  -> vault

=== vault

A relic gleams on a plinth.

* [Seize the relic and escape]
  ~ gold += 500
  -> END
"#;

/// The deep winning route: descend, descend, descend, seize. Reaches `depth == 3` in 4
/// turns.
const DEEP_MOVES: [usize; 4] = [0, 0, 0, 0];
/// The shallow winning route: side crack, ledge, seize. Reaches `depth == 0` in 3 turns.
const SHALLOW_MOVES: [usize; 3] = [1, 0, 0];

fn descent() -> Universe {
    Universe::authored(
        "Cheevo Descent Trial",
        "cheevo-test",
        DESCENT,
        WinCondition::ended_with(&[("gold", 500)]),
    )
    .expect("the descent world is a valid, deployable universe")
}

/// A vault world: forcing the door trips `shield_broken`; picking the lock does not. Both
/// routes seize the hoard (`gold == 500`) and END in 2 turns.
const VAULT: &str = r#"---
id: cheevo-vault
title: Cheevo Vault Trial
weight: 1
---

=== gate

A vault door with a trapped lock.

* [Force the door open]
  ~ shield_broken = 1
  -> hoard

* [Pick the lock, patient and clean]
  -> hoard

=== hoard

The hoard glitters within.

* [Seize the hoard and escape]
  ~ gold += 500
  -> END
"#;

/// The careful route: pick the lock, seize. `shield_broken == 0`.
const CAREFUL_MOVES: [usize; 2] = [1, 0];
/// The reckless route: force the door, seize. `shield_broken == 1`.
const RECKLESS_MOVES: [usize; 2] = [0, 0];

fn vault() -> Universe {
    Universe::authored(
        "Cheevo Vault Trial",
        "cheevo-test",
        VAULT,
        WinCondition::ended_with(&[("gold", 500)]),
    )
    .expect("the vault world is a valid, deployable universe")
}

fn completion(
    universe: &Universe,
    id: ugc_dregg::UniverseId,
    player: &str,
    moves: &[usize],
) -> Completion {
    let play = record_playthrough(universe, moves).expect("the honest run drives cleanly");
    Completion {
        universe: id,
        player: player.into(),
        play,
        claimed_turns: moves.len(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// EARNED BY A REAL VERIFIED RUN.
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn a_deep_verified_run_earns_the_reached_depth_cheevo_and_mints_a_soulbound_asset() {
    let mut reg = Registry::new();
    let u = descent();
    let id = reg.publish(u.clone());
    let c = completion(&u, id, "ada", &DEEP_MOVES);
    // The run is a genuine accepted win on the no-cheat board.
    reg.submit(c.clone())
        .expect("the deep run is a verified win");

    let mut ledger = CheevoLedger::new();
    let cheevo = ledger
        .earn(
            &u,
            &c,
            Achievement::ReachedDepth {
                var: "depth".into(),
                min: 3,
            },
        )
        .expect("a real run reaching depth 3 earns the reached-depth cheevo");

    // The witness carries the provenance: the peak depth the run actually reached.
    assert_eq!(cheevo.witness, Witness::Depth { peak: 3, min: 3 });
    assert_eq!(cheevo.turns, 4);
    assert_eq!(cheevo.player, "ada");
    assert_eq!(cheevo.earner, ledger.earner_of("ada"));
    // The soulbound asset was minted, owned by the earner, content-addressed by the seal.
    assert!(cheevo.seal_intact());
    assert_eq!(ledger.minted().len(), 1);

    // It re-verifies independently: the run re-passes the no-cheat verify + the predicate
    // re-holds + the note is still owner-bound.
    ledger
        .reverify_run(&cheevo, &u, &c)
        .expect("the earned cheevo re-verifies against the public universe + the run");
}

#[test]
fn a_no_death_and_a_speed_cheevo_are_earned_by_real_runs() {
    let mut reg = Registry::new();
    let uv = vault();
    let vid = reg.publish(uv.clone());
    let careful = completion(&uv, vid, "bran", &CAREFUL_MOVES);

    let mut ledger = CheevoLedger::new();
    // NO-DEATH: the careful run never tripped `shield_broken`.
    let nod = ledger
        .earn(
            &uv,
            &careful,
            Achievement::NoDeathClear {
                flag: "shield_broken".into(),
            },
        )
        .expect("a clean careful win earns the no-death cheevo");
    assert_eq!(
        nod.witness,
        Witness::NoDeath {
            flag: "shield_broken".into()
        }
    );

    // SPEED: the careful win took 2 turns, under a max of 2.
    let spd = ledger
        .earn(&uv, &careful, Achievement::SpeedClear { max_turns: 2 })
        .expect("a 2-turn win earns the speed cheevo");
    assert_eq!(
        spd.witness,
        Witness::Speed {
            turns: 2,
            max_turns: 2
        }
    );
    assert_eq!(ledger.minted().len(), 2);
}

// ═══════════════════════════════════════════════════════════════════════════════
// NON-VACUOUS: a real verified win that does NOT satisfy the predicate earns NOTHING.
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn a_shallow_verified_win_earns_no_reached_depth_cheevo() {
    let mut reg = Registry::new();
    let u = descent();
    let id = reg.publish(u.clone());
    let shallow = completion(&u, id, "quinn", &SHALLOW_MOVES);
    // The shallow run IS a verified win (it reaches gold == 500 and ENDs)...
    reg.submit(shallow.clone())
        .expect("the shallow run is a verified win too");

    let mut ledger = CheevoLedger::new();
    // ...but it never descended, so a reached-depth(>=3) cheevo is REFUSED. Non-vacuous.
    let out = ledger.earn(
        &u,
        &shallow,
        Achievement::ReachedDepth {
            var: "depth".into(),
            min: 3,
        },
    );
    assert!(
        matches!(out, Err(CheevoError::PredicateNotMet(_))),
        "a shallow win must earn NO reached-depth cheevo, got {out:?}"
    );
    assert_eq!(ledger.minted().len(), 0, "nothing was minted");
}

#[test]
fn a_shield_broken_win_earns_no_no_death_cheevo() {
    let mut reg = Registry::new();
    let uv = vault();
    let vid = reg.publish(uv.clone());
    let reckless = completion(&uv, vid, "mallory", &RECKLESS_MOVES);
    reg.submit(reckless.clone())
        .expect("the reckless run is a verified win");

    let mut ledger = CheevoLedger::new();
    // The reckless run WON, but it tripped `shield_broken` — so no no-death cheevo.
    let out = ledger.earn(
        &uv,
        &reckless,
        Achievement::NoDeathClear {
            flag: "shield_broken".into(),
        },
    );
    assert!(
        matches!(out, Err(CheevoError::PredicateNotMet(_))),
        "a shield-broken win must earn NO no-death cheevo, got {out:?}"
    );
    assert_eq!(ledger.minted().len(), 0);
}

#[test]
fn a_slow_verified_win_earns_no_speed_cheevo() {
    let mut reg = Registry::new();
    let u = descent();
    let id = reg.publish(u.clone());
    let deep = completion(&u, id, "sloane", &DEEP_MOVES); // 4 turns

    let mut ledger = CheevoLedger::new();
    let out = ledger.earn(&u, &deep, Achievement::SpeedClear { max_turns: 3 });
    assert!(
        matches!(out, Err(CheevoError::PredicateNotMet(_))),
        "a 4-turn win must earn NO speed(<=3) cheevo, got {out:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// A FORGED run earns NOTHING — the no-cheat gate bites before any predicate.
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn a_forged_run_earns_no_cheevo() {
    let mut reg = Registry::new();
    let u = descent();
    let id = reg.publish(u.clone());

    // Record the honest deep win, then FORGE it: retcon the first move from "descend the
    // deep shaft" to "slip through the side crack". On replay the recorded depth-incremented
    // states diverge from the reproduced (shallow) states — the receipt chain fails to verify.
    let mut c = completion(&u, id, "cheater", &DEEP_MOVES);
    c.play.steps[0].choice_index = 1;

    let mut ledger = CheevoLedger::new();
    let out = ledger.earn(
        &u,
        &c,
        Achievement::ReachedDepth {
            var: "depth".into(),
            min: 3,
        },
    );
    assert!(
        matches!(out, Err(CheevoError::RunRejected(_))),
        "a forged run must be REFUSED by the no-cheat gate and earn nothing, got {out:?}"
    );
    assert_eq!(
        ledger.minted().len(),
        0,
        "no cheevo minted for a forged run"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// SOULBOUND — a cheevo can't be transferred/sold, and a laundered record is refused.
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn a_cheevo_is_soulbound_transfer_is_refused() {
    let mut reg = Registry::new();
    let u = descent();
    let id = reg.publish(u.clone());
    let c = completion(&u, id, "ada", &DEEP_MOVES);

    let mut ledger = CheevoLedger::new();
    let cheevo = ledger
        .earn(
            &u,
            &c,
            Achievement::ReachedDepth {
                var: "depth".into(),
                min: 3,
            },
        )
        .expect("earned");

    // THE SOULBOUND TOOTH: there is no transfer path. A cheevo can't be sold.
    let out = ledger.attempt_transfer(&cheevo, "buyer");
    assert!(
        matches!(out, Err(CheevoError::Soulbound)),
        "a cheevo transfer must be REFUSED (soulbound), got {out:?}"
    );
}

#[test]
fn a_laundered_cheevo_rebound_onto_a_buyer_fails_reverification() {
    let mut reg = Registry::new();
    let u = descent();
    let id = reg.publish(u.clone());
    let c = completion(&u, id, "ada", &DEEP_MOVES);

    let mut ledger = CheevoLedger::new();
    let cheevo = ledger
        .earn(
            &u,
            &c,
            Achievement::ReachedDepth {
                var: "depth".into(),
                min: 3,
            },
        )
        .expect("earned");

    // A buyer tries to LAUNDER the cheevo onto their own identity — re-bind the earner.
    let mut stolen = cheevo.clone();
    stolen.earner = ledger.earner_of("buyer");
    // The seal was sealed over ada's earner; the re-bound record no longer re-derives it.
    assert!(
        !stolen.seal_intact(),
        "the re-bound seal must not re-derive"
    );
    let out = ledger.reverify_run(&stolen, &u, &c);
    assert!(
        matches!(out, Err(CheevoError::Tampered(_))),
        "a laundered cheevo must FAIL re-verification, got {out:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// SEASON CHAMPION — a predicate over the season's no-cheat hall-of-fame.
// ═══════════════════════════════════════════════════════════════════════════════

/// The built-in salt-shore dungeon, for the season board.
fn salt_shore() -> Universe {
    Universe::authored(
        "The Salt Shore Descent",
        "attested-dm-salvage",
        DUNGEON,
        WinCondition::ended_with(&[("gold", 500)]),
    )
    .expect("valid dungeon universe")
}

#[test]
fn a_season_champion_cheevo_is_earned_over_the_no_cheat_hall_of_fame() {
    // A season with a no-cheat board; two real verified wins ranked by turns.
    let mut season = Season::genesis(
        1,
        dregg_epoch::local_manifest(),
        "the-descent:s1",
        1000,
        CarryForwardPolicy::hall_of_fame(8),
    );
    let u = salt_shore();
    let id = season.board.publish(u.clone());

    // alice: the minimal 3-move win. bran: a 5-move detour win.
    let alice = completion(&u, id, "alice", &[CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM]);
    let bran = completion(
        &u,
        id,
        "bran",
        &[
            CH_TAKE_LANTERN,
            CH_RETREAT,
            CH_TAKE_LANTERN,
            CH_DESCEND,
            CH_CLAIM,
        ],
    );
    season.board.submit(alice).expect("alice's win is accepted");
    season.board.submit(bran).expect("bran's win is accepted");

    // alice ranks first (fewer turns); bran second.
    let champs = season.champions(2);
    assert_eq!(champs[0].player, "alice");
    assert_eq!(champs[1].player, "bran");

    let mut ledger = CheevoLedger::new();

    // The top-1 champion (alice) earns the champion cheevo...
    let cheevo = ledger
        .earn_champion(&season, "alice", 1)
        .expect("the top-1 champion earns the season-champion cheevo");
    assert_eq!(
        cheevo.witness,
        Witness::Champion {
            top_n: 1,
            rank: 1,
            turns: 3
        }
    );
    assert!(cheevo.seal_intact());
    ledger
        .reverify_champion(&cheevo, &season)
        .expect("the champion cheevo re-verifies against the live hall-of-fame");

    // ...but bran, NOT in the top-1, earns nothing. Non-vacuous.
    let out = ledger.earn_champion(&season, "bran", 1);
    assert!(
        matches!(out, Err(CheevoError::NotAChampion)),
        "a non-top-1 player must earn NO top-1 champion cheevo, got {out:?}"
    );

    // With a top-2 cutoff, bran IS a champion (rank 2).
    let bran_cheevo = ledger
        .earn_champion(&season, "bran", 2)
        .expect("bran is a top-2 champion");
    assert_eq!(
        bran_cheevo.witness,
        Witness::Champion {
            top_n: 2,
            rank: 2,
            turns: 5
        }
    );
}

//! THE DESCENT — driven end to end on the real substrate.
//!
//! Seeds "today's dungeon" from a REAL published drand `quicknet` round (genuine beacon
//! interop), then drives:
//!   * a permadeath run that is genuinely LOST (a reckless line falls into a committed defeat,
//!     the hardcore character PERISHES) — verifies by replay, but the leaderboard refuses it;
//!   * a careful run that is WON (reaches the hoard) — verifies, ranks on the no-cheat board;
//!   * a FORGED run — refused by the board (non-vacuous, the honest run was accepted);
//!   * the persistent character carrying in + earning across days;
//!   * a different day's beacon giving a different dungeon.

use dreggnet_offerings::DreggIdentity;
use dreggnet_offerings::character::InMemoryCharacterStore;
use dreggnet_offerings::daily_descent::{
    CORRIDOR_ON, DailyDescentOffering, GATE_FALL, GATE_HEAL, GATE_MEASURED, GATE_PRESS,
    GATE_RECKLESS, HOARD_FORCE, HOARD_SEIZE, KEY_TAKE, daily_scene,
};
use dungeon_on_dregg::progression::WARRIOR;
use procgen_dregg::beacon::DailyBeacon;
use ugc_dregg::{Registry, RejectReason};

use dreggnet_offerings::daily_descent::DailyRun;

// A REAL, PUBLISHED drand `quicknet` round (round 1_000_000). Same vector `dregg-dice`'s
// interop test pins; here it is "today's beacon".
const DRAND_QUICKNET_ROUND: u64 = 1_000_000;
const DRAND_QUICKNET_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

fn todays_beacon() -> DailyBeacon {
    DailyBeacon::quicknet(
        DRAND_QUICKNET_ROUND,
        hex::decode(DRAND_QUICKNET_SIG_HEX).expect("the drand signature decodes"),
    )
}

fn player(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

/// Drive a CAREFUL winning line to the hoard: fight the warden down (healing once if the
/// beacon drew a tough warden), press past, take the key, walk the corridors, force the door,
/// seize the hoard. Works for any beacon-drawn warden HP / depth.
fn drive_win<S: dreggnet_offerings::character::CharacterStore>(
    off: &DailyDescentOffering<S>,
    run: &mut DailyRun,
) {
    for _ in 0..64 {
        let Some(room) = run.current_room() else {
            break;
        };
        let ci = match room.as_str() {
            "gate" => {
                if run.read_var("warden_hp") == 0 {
                    GATE_PRESS
                } else if run.read_var("hp") >= 16 {
                    GATE_MEASURED
                } else {
                    GATE_HEAL
                }
            }
            "keyroom" => KEY_TAKE,
            "hoardgate" => HOARD_FORCE,
            "hoard" => HOARD_SEIZE,
            r if r.starts_with("corridor") => CORRIDOR_ON,
            other => panic!("unexpected room in a winning line: {other}"),
        };
        let out = off.advance(run, ci);
        assert!(
            out.landed(),
            "a careful move was refused in {room}: {out:?}"
        );
    }
}

/// Drive a LOSING line: a reckless opener burns HP to the fall threshold, then fall into the
/// committed defeat passage — a real lost run.
fn drive_loss<S: dreggnet_offerings::character::CharacterStore>(
    off: &DailyDescentOffering<S>,
    run: &mut DailyRun,
) {
    // A reckless all-out blow (hp 50 → 20). Now hp <= 20: the warden still stands.
    assert!(
        off.advance(run, GATE_RECKLESS).landed(),
        "the reckless opener commits"
    );
    assert!(
        run.read_var("hp") <= 20,
        "the reckless line is at the brink"
    );
    assert!(run.read_var("warden_hp") > 0, "the warden still stands");
    // Fall into the defeat passage — a real committed loss.
    assert!(
        off.advance(run, GATE_FALL).landed(),
        "the fall into defeat commits"
    );
    assert_eq!(
        run.current_room().as_deref(),
        Some("downed"),
        "routed into the terminal defeat room"
    );
    // Close the defeat passage.
    assert!(off.advance(run, 0).landed(), "the defeat passage ends");
}

#[test]
fn a_forged_beacon_cannot_open_a_day() {
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    // Flip a signature bit — a forged reveal. open() must fail (the beacon does not verify).
    let mut sig = hex::decode(DRAND_QUICKNET_SIG_HEX).unwrap();
    sig[0] ^= 0x01;
    let forged = DailyBeacon::quicknet(DRAND_QUICKNET_ROUND, sig);
    assert!(
        off.open(player("p"), &forged).is_err(),
        "a forged beacon must not open a day (fail-closed)"
    );
    // The honest beacon opens.
    assert!(off.open(player("p"), &todays_beacon()).is_ok());
}

#[test]
fn the_field_dressing_is_one_shot() {
    // Probe the one-shot heal tooth (a `{ heals_used <= 0 } ~ heals_used += 1` lift to a real
    // FieldLte(heals_used, 1)) directly, independent of what warden HP the beacon drew.
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    let mut run = off.open(player("healer"), &todays_beacon()).expect("open");
    // Two measured blows drop hp 50 → 20 (each gated only on { hp >= 16 }).
    assert!(off.advance(&mut run, GATE_MEASURED).landed());
    assert!(off.advance(&mut run, GATE_MEASURED).landed());
    let hp_before = run.read_var("hp");
    assert!(hp_before <= 30, "hurt enough to heal: hp={hp_before}");
    // Bind wounds once: it lands and raises HP.
    assert!(
        off.advance(&mut run, GATE_HEAL).landed(),
        "the one field-dressing binds wounds"
    );
    assert!(run.read_var("hp") > hp_before, "healing raised hp");
    assert_eq!(run.read_var("heals_used"), 1);
    // A SECOND heal is refused — the field-dressing is one-shot.
    let again = off.advance(&mut run, GATE_HEAL);
    assert!(
        !again.landed(),
        "the field-dressing is one-shot, got {again:?}"
    );
}

#[test]
fn a_run_can_be_genuinely_lost_hardcore_death_is_final() {
    let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    let who = player("player-loser-key");
    let mut run = off.open(who.clone(), &todays_beacon()).expect("open today");
    assert!(!run.is_dead(), "alive at the start");

    drive_loss(&off, &mut run);
    assert!(run.is_ended(), "the run is over — lost");
    assert!(!run.is_won(), "a lost run did not reach the hoard");
    assert_eq!(run.read_var("gold"), 0, "no hoard for a lost run");
    assert_eq!(run.read_var("downed"), 1, "the downed flag is set");

    // HARDCORE: the character perished, and the death is un-undoable.
    assert!(run.is_dead(), "a hardcore defeat perishes the character");
    assert!(
        run.character().attempt_resurrect().is_err(),
        "a hardcore death is final — resurrection refused"
    );

    // The LOST run is an honest, replay-verifiable record.
    assert!(
        off.verify(&run).verified,
        "the lost run re-verifies by replay"
    );

    // The death PERSISTS across the day boundary.
    off.save(&run);
    let reopened = off
        .open(who, &todays_beacon())
        .expect("reopen the same identity");
    assert!(
        reopened.is_dead(),
        "a saved-dead hardcore character loads dead — the no-death streak is broken forever"
    );
}

#[test]
fn a_careful_run_is_won_earns_xp_and_ranks_on_the_no_cheat_board() {
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    let who = player("player-winner-key");
    let mut run = off.open(who, &todays_beacon()).expect("open today");
    off.choose_class(&run, WARRIOR).expect("choose a class");

    drive_win(&off, &mut run);
    assert!(run.is_won(), "the careful line reached the hoard — a win");
    assert_eq!(run.read_var("gold"), 500, "the hoard is seized");
    assert!(!run.is_dead(), "a winner did not perish");
    // Earned XP: the warden (50) + the hoard (150).
    assert_eq!(
        run.character().xp(),
        dreggnet_offerings::daily_descent::XP_FELL_WARDEN
            + dreggnet_offerings::daily_descent::XP_SEIZE_HOARD,
        "XP earned from real landed outcomes"
    );
    assert!(
        off.verify(&run).verified,
        "the won run re-verifies by replay"
    );

    // THE NO-CHEAT LEADERBOARD: publish today's world, submit the verified run → ranked.
    let mut registry = Registry::new();
    let universe = run
        .day()
        .universe("the-descent")
        .expect("publish today's world");
    let uid = registry.publish(universe);

    let completion = off
        .completion(&run, "the-descent", "winner")
        .expect("build the completion");
    assert_eq!(
        completion.universe, uid,
        "the completion is for today's world"
    );
    let accepted = registry
        .submit(completion)
        .expect("the verified win is accepted + ranked");
    assert_eq!(accepted.rank, 1, "first verified completion ranks #1");
    // Anyone can independently re-verify the ranked entry.
    registry
        .reverify_entry(uid, &accepted.completion_id)
        .expect("the ranked entry independently re-verifies");
}

#[test]
fn a_forged_run_is_refused_and_a_lost_run_does_not_rank() {
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());

    // A winning run → today's world + a verified completion.
    let mut win = off.open(player("honest"), &todays_beacon()).expect("open");
    drive_win(&off, &mut win);
    assert!(win.is_won());

    let mut registry = Registry::new();
    let uid = registry.publish(win.day().universe("the-descent").expect("publish"));

    // FORGE: mutate the first committed step's choice — the recorded chain no longer replays.
    let honest = off
        .completion(&win, "the-descent", "honest")
        .expect("completion");
    let mut forged = honest.clone();
    if let Some(first) = forged.play.steps.first_mut() {
        // Swap the opening measured blow for a reckless one — the state chain diverges.
        first.choice_index = GATE_RECKLESS;
    }
    forged.player = "cheater".to_string();
    let out = registry.submit(forged);
    assert!(
        matches!(
            out,
            Err(RejectReason::FailedVerification(_)) | Err(RejectReason::DidNotWin)
        ),
        "a forged run must be refused by the no-cheat board, got {out:?}"
    );

    // Non-vacuous: the HONEST run is accepted on the same board.
    assert!(
        registry.submit(honest).is_ok(),
        "the honest run is accepted"
    );

    // A LOST run re-verifies as an honest record but does NOT rank (it never reached the win).
    let mut lost = off.open(player("faller"), &todays_beacon()).expect("open");
    drive_loss(&off, &mut lost);
    assert!(
        off.verify(&lost).verified,
        "the lost run is an honest record"
    );
    let lost_completion = off
        .completion(&lost, "the-descent", "faller")
        .expect("completion");
    assert_eq!(lost_completion.universe, uid);
    let out = registry.submit(lost_completion);
    assert!(
        matches!(out, Err(RejectReason::DidNotWin)),
        "a lost run does not rank (did not reach the hoard), got {out:?}"
    );
}

#[test]
fn the_character_carries_across_days() {
    let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    let alice = player("player-alice-key");

    // Day 1: fresh Warrior wins, earns XP, levels up, saves.
    {
        let mut run = off
            .open(alice.clone(), &todays_beacon())
            .expect("open day 1");
        assert!(!off.store().has(&alice), "alice is new");
        assert_eq!(
            run.character().level(),
            1,
            "a new adventurer begins at level 1"
        );
        off.choose_class(&run, WARRIOR).expect("class");
        drive_win(&off, &mut run);
        assert_eq!(run.character().xp(), 200, "earned the warden + the hoard");
        off.level_up(&run).expect("level 2 (xp 200 >= 100)");
        assert_eq!(run.character().level(), 2);
        off.save(&run);
    }
    assert!(off.store().has(&alice), "alice's character is persisted");

    // Day 2: the SAME identity RESUMES the carried character (level / XP / class carry in).
    {
        let run = off.open(alice, &todays_beacon()).expect("open day 2");
        assert_eq!(
            run.character().level(),
            2,
            "carried level across the day boundary"
        );
        assert_eq!(run.character().xp(), 200, "carried XP");
        assert_eq!(run.character().class(), WARRIOR, "carried class");
    }

    // A DIFFERENT identity is a fresh character.
    let bob = off
        .open(player("player-bob-key"), &todays_beacon())
        .expect("open bob");
    assert_eq!(bob.character().level(), 1, "a different identity is fresh");
    assert_eq!(bob.character().xp(), 0);
}

#[test]
fn a_different_days_beacon_gives_a_different_dungeon() {
    // Today's real drand seed vs a counterfactual day's seed (a different beacon output): the
    // day's world SOURCE differs — a fresh dungeon each day.
    let today_seed = todays_beacon().seed().expect("today's seed");
    // A different day's beacon output → a different daily seed (via the crate's daily_seed).
    let other_seed = procgen_dregg::daily_seed(&[0x5c; 32]);
    assert_ne!(today_seed.as_bytes(), other_seed.as_bytes());

    let today = daily_scene(&today_seed);
    let other = daily_scene(&other_seed);
    assert_ne!(
        today.source, other.source,
        "a different day's beacon gives a different dungeon world"
    );
    // Both are real permadeath worlds (a warden fight + a fall-to-defeat + a hoard).
    for d in [&today, &other] {
        assert!(d.source.contains("=== downed"), "has a defeat passage");
        assert!(d.source.contains("warden_hp ="), "has a warden fight");
        assert!(d.source.contains("gold += 500"), "has the hoard win");
    }
}

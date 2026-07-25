//! The coherent campaign, driven — including the thing it could not do before: a SECOND
//! expedition.
//!
//! Every line here is generated from the day the campaign actually drew, never from a
//! transcribed day-0 tape. A campaign now redraws its map each time you go out, so a test
//! that hard-codes eighteen moves is testing a dungeon that is no longer deployed.

use std::collections::BTreeSet;

use dungeon_on_dregg::campaign::{
    CROWN_XP, CampaignAction, CampaignConfig, CampaignError, CampaignRecord, CampaignSession,
    DEPTH_XP, DescentAction, ExpeditionOutcome, Phase, RELIC_XP, RelicState, RelicUse,
    bound_campaign_narration, bound_relic_context, max_campaign_xp, verify_expedition_seal,
};
use dungeon_on_dregg::descent::{
    ASCEND, BANKED, BREATH, CAP, CARRIED, DAYS, DELVE, FLEE, FLOORS, LOOT, RELICS, SMITE, Sim,
    UNLOCK, crowned_line, day_world,
};
use dungeon_on_dregg::progression::MAGE;

// ── Lines generated from the drawn map, not transcribed ──────────────────────────

/// The day's own crowned line, as campaign actions.
fn crowned_actions(day: usize) -> Vec<DescentAction> {
    crowned_line(day)
        .into_iter()
        .map(|(verb, argument)| match verb {
            DELVE => DescentAction::Delve,
            ASCEND => DescentAction::Ascend,
            SMITE => DescentAction::Smite,
            LOOT => DescentAction::Loot {
                relic: argument as u8,
            },
            UNLOCK => DescentAction::Unlock {
                way: argument as u64,
            },
            FLEE => DescentAction::Flee,
            other => panic!("crowned_line emitted unknown verb `{other}`"),
        })
        .collect()
}

/// **A treasure run**: walk down to the shallowest treasure the reliquary is still
/// MISSING (relics `FLOORS..RELICS` — the ones the crowned line deliberately leaves
/// lying), take it, and walk out. Picks up exactly the way-keys needed to get that deep
/// and nothing else. This is the shape of run the settlement's board asks for.
fn treasure_actions(day: usize, held: &[RelicState; RELICS]) -> (usize, Vec<DescentAction>) {
    let world = day_world(day);
    let target = (FLOORS as usize..RELICS)
        .filter(|&relic| held[relic] == RelicState::Unbanked)
        .min_by_key(|&relic| world.homes[relic])
        .expect("some treasure is still down there");
    let target_floor = world.homes[target];
    let mut line = Vec::new();
    for floor in 1..=target_floor {
        line.push(DescentAction::Delve);
        // Way `w` is opened by relic `w - 1`; getting to `target_floor` needs keys
        // `1..target_floor`, and the draw guarantees each is minted above its own door.
        let mut wanted: Vec<usize> = (1..target_floor as usize)
            .filter(|&key| world.homes[key] == floor)
            .collect();
        if floor == target_floor {
            wanted.push(target);
        }
        if !wanted.is_empty() {
            for _ in 0..world.guard_hp(floor) {
                line.push(DescentAction::Smite);
            }
            for relic in wanted {
                line.push(DescentAction::Loot { relic: relic as u8 });
            }
        }
        if floor < target_floor {
            line.push(DescentAction::Unlock { way: floor + 1 });
        }
    }
    // ⚑ AND WALK OUT. `flee` demands the surface; the climb is one light per floor.
    for _ in 0..target_floor {
        line.push(DescentAction::Ascend);
    }
    line.push(DescentAction::Flee);
    (target, line)
}

// ── Driving helpers ──────────────────────────────────────────────────────────────

fn open(seed: u8) -> CampaignSession {
    CampaignSession::open(CampaignConfig::new(seed, "cmr://hero", MAGE))
        .expect("the coherent campaign deploys")
}

fn run_line(session: &mut CampaignSession, line: Vec<DescentAction>) {
    for (index, command) in line.into_iter().enumerate() {
        let event = session
            .advance(
                CampaignAction::Descent(command),
                format!("The expedition advances through beat {index}."),
            )
            .unwrap_or_else(|error| panic!("move {index} ({command:?}) refused: {error}"));
        let primary = event.receipts.first().expect("every move has a receipt");
        assert_eq!(
            bound_campaign_narration(primary),
            Some(event.narration_commitment),
            "narration is carried by the exact Descent turn"
        );
    }
}

/// ⚑ THE WAY OUT IS A CLIMB. `flee` demands the surface, so ending a live expedition is
/// `depth` ascends and then the bank. Any test that used to say "fleeing is always
/// affordable while the light burns" was relying on the teleport `flee` that made the
/// Descent deathless; there is no such move now, and a run that cannot afford the climb
/// cannot end at all (`Dungeon.doomed_never_banks`).
fn walk_out(session: &mut CampaignSession) {
    while session.expedition().depth > 0 {
        session
            .advance(CampaignAction::Descent(DescentAction::Ascend), "Climbing.")
            .expect("the climb home is unconditional but for the light");
    }
    session
        .advance(CampaignAction::Descent(DescentAction::Flee), "Out.")
        .expect("at the mouth, the bank is one breath");
}

fn come_home(session: &mut CampaignSession) -> ExpeditionOutcome {
    let outcome = session.expedition();
    let event = session
        .advance(CampaignAction::Return, "The traveller walks back up.")
        .expect("a finished expedition may be sealed");
    let seal = event
        .receipts
        .first()
        .expect("the seal is the first receipt");
    assert!(
        verify_expedition_seal(seal, &outcome),
        "the chronicle seal names the committed expedition it claims"
    );
    outcome
}

fn go_out(session: &mut CampaignSession) {
    session
        .advance(CampaignAction::Embark, "The traveller descends again.")
        .expect("the settlement admits a fresh expedition");
}

/// Replay a prefix of a day's move tape through the pure mover.
fn drive_prefix(day: usize, tape: &[(&'static str, i64)]) -> Sim {
    let mut sim = Sim::genesis_on_day(day);
    for (verb, argument) in tape {
        sim = match *verb {
            DELVE => sim.delve(),
            ASCEND => sim.ascend(),
            SMITE => sim.smite(),
            LOOT => sim.loot(*argument as usize),
            UNLOCK => sim.unlock(*argument as u64),
            FLEE => sim.flee(),
            other => panic!("day {day}: unknown verb `{other}`"),
        }
        .unwrap_or_else(|error| panic!("day {day}: {verb}({argument}) refused: {error}"));
    }
    sim
}

fn xp(session: &CampaignSession) -> u64 {
    session.projection().unwrap().hero_xp
}

fn record(session: &CampaignSession, id: &str) -> dungeon_on_dregg::campaign::LocationRecord {
    session
        .records()
        .into_iter()
        .find(|record| record.id == id)
        .expect("a place on the map")
}

// ── THE DRIVING TEST — one player, many expeditions ──────────────────────────────

/// **One player, seven expeditions, and a world that is different at the end of them.**
///
/// This is the test the campaign could not previously host at all: before the run
/// boundary existed, the descent froze on its terminal turn and every remaining action
/// refused forever, so "campaign" meant "one lucky first-try crown per location".
#[test]
fn one_player_across_seven_expeditions_the_map_opens_and_the_collection_fills() {
    let mut campaign = open(41);
    let start = campaign.projection().unwrap();
    assert_eq!(start.location, "keep");
    assert_eq!(
        start.phase,
        Phase::Expedition,
        "the campaign opens underway"
    );
    assert_eq!(start.expedition_ordinal, 1);
    assert_eq!(start.hero_xp, 0);
    assert_eq!(start.relics, [RelicState::Unbanked; RELICS]);

    let mut drawn = BTreeSet::new();

    // ── EXPEDITION 1 — crown the Keep. ───────────────────────────────────────────
    let day = campaign.descent().day();
    drawn.insert(day);
    run_line(&mut campaign, crowned_actions(day));

    // Coming home is what pays. Standing on the surface with the Crown in the pack has
    // moved nothing persistent yet.
    let banked_but_unsealed = campaign.projection().unwrap();
    assert_eq!(banked_but_unsealed.hero_xp, 0, "the run is not yet cashed");
    assert!(banked_but_unsealed.cleared_locations.is_empty());
    assert_eq!(record(&campaign, "keep").runs, 0);

    let first = come_home(&mut campaign);
    assert!(first.crowned());
    // ⚑ A BANKED RUN STANDS AT THE MOUTH (`Dungeon.banked_at_the_surface`). `depth` is the
    // floor standing at the END, and the end of a successful run is the surface — it used
    // to read `FLOORS` only because `flee` was a teleport out of the bottom.
    assert_eq!(first.depth, 0);
    assert!(first.lost().is_empty(), "a fled run loses nothing");

    let sealed = campaign.projection().unwrap();
    assert_eq!(sealed.phase, Phase::Settlement);
    assert_eq!(sealed.cleared_locations, ["keep"]);
    for relic in 0..=3 {
        assert_eq!(
            sealed.relics[relic],
            RelicState::Banked,
            "a crowned run banks the prize and the three keys"
        );
    }
    // First crown + four first relics + four floors of new deepest reach.
    assert_eq!(xp(&campaign), CROWN_XP + 4 * RELIC_XP + 4 * DEPTH_XP);
    let keep = record(&campaign, "keep");
    assert_eq!((keep.runs, keep.deepest, keep.crowns), (1, FLOORS, 1));

    // The settlement is where a level lands.
    campaign
        .advance(CampaignAction::LevelUp, "The lesson settles into instinct.")
        .expect("the crowned XP admits level two");
    assert_eq!(campaign.projection().unwrap().hero_level, 2);

    // ── EXPEDITION 2 — the same place, a DIFFERENT dungeon, for a treasure. ───────
    go_out(&mut campaign);
    let second = campaign.projection().unwrap();
    assert_eq!(second.phase, Phase::Expedition);
    assert_eq!(second.expedition_ordinal, 2);
    assert_eq!(second.location, "keep", "still the Keep");

    // NOTHING carries into the dungeon. The fresh expedition is at the Lean genesis of
    // its own drawn world — depth, light, wounds, ways and custody all reset.
    let day = campaign.descent().day();
    drawn.insert(day);
    assert_eq!(second.descent_depth, 0);
    assert_eq!(second.descent_spent, 0);
    assert_eq!(second.descent_wounds, 0);
    assert!(!second.descent_terminal);
    assert_eq!(
        second.expedition_custody,
        day_world(day).homes,
        "custody is the drawn map's mint, not the last run's leftovers"
    );

    let (treasure, line) = treasure_actions(day, &second.relics);
    assert!(treasure >= FLOORS as usize, "a treasure, not a key");
    run_line(&mut campaign, line);
    let outcome = come_home(&mut campaign);
    assert!(!outcome.crowned(), "a treasure run gives up the Crown");
    assert!(outcome.banked().contains(&treasure));

    let after = campaign.projection().unwrap();
    assert_eq!(
        after.relics[treasure],
        RelicState::Banked,
        "a run that banks NO prize still fills the reliquary — this is the whole reason \
         a treasure run is worth walking"
    );
    assert_eq!(
        xp(&campaign),
        CROWN_XP + 5 * RELIC_XP + 4 * DEPTH_XP,
        "exactly one new relic was paid for; the keep was already cleared and bottomed"
    );
    let keep = record(&campaign, "keep");
    assert_eq!(
        (keep.runs, keep.crowns),
        (2, 1),
        "two runs, still one crown — `crowns <= runs` is an executor tooth"
    );

    // ── EXPEDITION 3 — re-crowning a cleared place pays NOTHING. ─────────────────
    go_out(&mut campaign);
    let day = campaign.descent().day();
    drawn.insert(day);
    let before = xp(&campaign);
    run_line(&mut campaign, crowned_actions(day));
    let outcome = come_home(&mut campaign);
    assert!(outcome.crowned());
    assert_eq!(
        xp(&campaign),
        before,
        "THE ANTI-GRIND RULE: XP is paid for facts that have never happened. A third run \
         at a cleared, bottomed-out place with nothing new in the pack pays zero."
    );
    let keep = record(&campaign, "keep");
    assert_eq!((keep.runs, keep.crowns), (3, 2));

    // ── THE ROAD — travel is settlement business, and it is earned. ──────────────
    campaign
        .advance(
            CampaignAction::Travel {
                destination: "vault".to_string(),
            },
            "The Crown opens the sunken road.",
        )
        .expect("the executor-cleared road admits travel");
    let travelled = campaign.projection().unwrap();
    assert_eq!(travelled.location, "vault");
    assert_eq!(
        travelled.phase,
        Phase::Settlement,
        "arriving somewhere does not start a run for you"
    );
    assert_eq!(
        travelled.expedition_location, "keep",
        "the last expedition still belongs to the place it was run"
    );

    // ── EXPEDITION 4 — a shallow bail at the Vault. Records the reach, opens nothing.
    go_out(&mut campaign);
    let day = campaign.descent().day();
    drawn.insert(day);
    run_line(
        &mut campaign,
        // One floor down, one floor back up, and out — banking demands the surface.
        vec![
            DescentAction::Delve,
            DescentAction::Ascend,
            DescentAction::Flee,
        ],
    );
    let bail = come_home(&mut campaign);
    assert!(!bail.crowned());
    assert_eq!(
        bail.deepest, 1,
        "a bail that touched floor 1 REACHED floor 1, though it stands at the mouth"
    );
    let vault = record(&campaign, "vault");
    assert_eq!((vault.runs, vault.deepest, vault.crowns), (1, 1, 0));
    assert!(!vault.cleared, "a bail opens no road");
    assert!(matches!(
        campaign.advance(
            CampaignAction::Travel {
                destination: "crypt".to_string()
            },
            "A road that has not been earned."
        ),
        Err(CampaignError::Refused(_))
    ));

    // ── EXPEDITION 5 — crown the Vault; the deep road opens. ─────────────────────
    go_out(&mut campaign);
    let day = campaign.descent().day();
    drawn.insert(day);
    let before = xp(&campaign);
    run_line(&mut campaign, crowned_actions(day));
    come_home(&mut campaign);
    assert_eq!(
        xp(&campaign),
        before + CROWN_XP + (FLOORS - 1) * DEPTH_XP,
        "a first crown here, plus three floors of NEW deepest reach; the relics were \
         already in the reliquary so they are not paid twice"
    );
    let vault = record(&campaign, "vault");
    assert_eq!((vault.runs, vault.deepest, vault.crowns), (2, FLOORS, 1));
    assert!(vault.cleared);

    // ── EXPEDITION 6/7 — the Crypt, and the collection keeps filling. ────────────
    campaign
        .advance(
            CampaignAction::Travel {
                destination: "crypt".to_string(),
            },
            "The way down is open at last.",
        )
        .expect("the Vault's crown unbars the Crypt");
    go_out(&mut campaign);
    let day = campaign.descent().day();
    drawn.insert(day);
    let (treasure, line) = treasure_actions(day, &campaign.projection().unwrap().relics);
    let before = xp(&campaign);
    run_line(&mut campaign, line);
    come_home(&mut campaign);
    assert_eq!(
        campaign.projection().unwrap().relics[treasure],
        RelicState::Banked
    );
    assert!(
        xp(&campaign) >= before + RELIC_XP,
        "a relic the reliquary had never seen is paid for"
    );

    go_out(&mut campaign);
    let day = campaign.descent().day();
    drawn.insert(day);
    run_line(&mut campaign, crowned_actions(day));
    come_home(&mut campaign);

    // ── The campaign is a different world than the one it started in. ────────────
    let head = campaign.projection().unwrap();
    assert_eq!(head.expedition_ordinal, 7);
    assert_eq!(campaign.sealed_expeditions(), 7);
    assert_eq!(head.cleared_locations, ["crypt", "keep", "vault"]);
    assert!(
        head.relics
            .iter()
            .filter(|state| **state != RelicState::Unbanked)
            .count()
            >= 6,
        "six of the eight relics are home: {:?}",
        head.relics
    );
    assert!(
        drawn.len() > 1,
        "consecutive expeditions draw DIFFERENT maps of the Lean-checked family; a \
         memorised line does not survive the walk home (saw {drawn:?})"
    );
    assert!(xp(&campaign) < max_campaign_xp(4), "the supply is finite");

    // ── And the whole thing replays, seven expeditions deep. ─────────────────────
    let stored = campaign.export_record().unwrap();
    let bytes = stored.to_json().expect("the campaign is durable");
    let restored = CampaignRecord::from_json(&bytes).expect("durable bytes decode");
    CampaignSession::verify(&restored).expect("a seven-expedition campaign replays exactly");
    assert_eq!(restored.root, campaign.root());
    assert_eq!(restored.projection, head);
}

// ── The phase boundary is real in both directions ────────────────────────────────

#[test]
fn the_settlement_and_the_expedition_are_closed_to_each_other() {
    let mut campaign = open(17);
    let head = campaign.root();

    // Underway: settlement business is shut.
    for action in [
        CampaignAction::Embark,
        CampaignAction::LevelUp,
        CampaignAction::Travel {
            destination: "vault".to_string(),
        },
    ] {
        assert!(
            matches!(
                campaign.advance(action.clone(), "Settlement business, mid-descent."),
                Err(CampaignError::Refused(_))
            ),
            "{action:?} must not land during an expedition"
        );
        assert_eq!(campaign.root(), head, "a refusal is anti-ghost");
    }

    // You cannot come home from a run that is still underway.
    campaign
        .advance(
            CampaignAction::Descent(DescentAction::Delve),
            "One step down.",
        )
        .expect("one real move lands");
    let live = campaign.expedition();
    assert!(!live.over());
    assert!(matches!(
        campaign.advance(CampaignAction::Return, "Home early."),
        Err(CampaignError::Refused(_))
    ));

    // The climb, then the bank, ends it; now home is open and the expedition is closed.
    walk_out(&mut campaign);
    come_home(&mut campaign);
    assert_eq!(campaign.projection().unwrap().phase, Phase::Settlement);
    assert!(matches!(
        campaign.advance(
            CampaignAction::Descent(DescentAction::Delve),
            "A move with no dungeon under it."
        ),
        Err(CampaignError::Refused(_))
    ));
    // And a run seals exactly once.
    assert!(matches!(
        campaign.advance(CampaignAction::Return, "Home twice."),
        Err(CampaignError::Refused(_))
    ));
}

// ── The chronicle's teeth, driven ────────────────────────────────────────────────

/// A mark can never fall, a seal cannot mint a crown it did not earn, and a seal at one
/// place cannot touch another place's marks. These are executor refusals, not host `if`s:
/// the falsifiers go through [`CampaignSession::resume`], which re-executes every input
/// against fresh cells.
#[test]
fn a_forged_history_does_not_replay() {
    let mut campaign = open(5);
    let day = campaign.descent().day();
    run_line(&mut campaign, crowned_actions(day));
    come_home(&mut campaign);
    go_out(&mut campaign);
    run_line(
        &mut campaign,
        // One floor down, one floor back up, and out — banking demands the surface.
        vec![
            DescentAction::Delve,
            DescentAction::Ascend,
            DescentAction::Flee,
        ],
    );
    come_home(&mut campaign);

    let authentic = campaign.export_record().unwrap();
    CampaignSession::verify(&authentic).expect("the authentic record replays");

    // Inflate the run count.
    let mut more_runs = authentic.clone();
    more_runs.projection.records[0].runs += 40;
    assert!(CampaignSession::resume(&more_runs).is_err());

    // Claim a crown the second, shallow expedition did not earn — at the summary AND
    // inside the sealed event itself, so this is not just a head comparison.
    let mut more_crowns = authentic.clone();
    more_crowns.projection.records[0].crowns += 1;
    assert!(CampaignSession::resume(&more_crowns).is_err());

    let mut event_crowns = authentic.clone();
    let last = event_crowns.events.len() - 1;
    event_crowns.events[last].projection.records[0].crowns += 1;
    assert!(CampaignSession::resume(&event_crowns).is_err());

    // Drop a Return: the run it sealed simply never happened, and everything the seal
    // paid for goes with it.
    let mut unsealed = authentic.clone();
    unsealed
        .events
        .retain(|event| event.action != CampaignAction::Return);
    assert!(CampaignSession::resume(&unsealed).is_err());

    // Claim a reach that was never stood on.
    let mut deeper = authentic.clone();
    deeper.projection.records[1].deepest = FLOORS;
    assert!(CampaignSession::resume(&deeper).is_err());

    // Relabel which map an expedition was played on.
    let mut wrong_day = authentic.clone();
    wrong_day.projection.expedition_day = (wrong_day.projection.expedition_day + 1) % DAYS;
    assert!(CampaignSession::resume(&wrong_day).is_err());

    // Stand in the settlement while claiming an expedition is live.
    let mut wrong_phase = authentic.clone();
    wrong_phase.projection.phase = Phase::Expedition;
    assert!(CampaignSession::resume(&wrong_phase).is_err());

    // Retcon a seal into a different run ordinal.
    let mut wrong_ordinal = authentic.clone();
    wrong_ordinal.projection.expedition_ordinal += 1;
    assert!(CampaignSession::resume(&wrong_ordinal).is_err());

    // Swap a Return for an Embark: a different action tape, a different history.
    let mut retape = authentic.clone();
    if let Some(index) = retape
        .events
        .iter()
        .position(|event| event.action == CampaignAction::Return)
    {
        retape.events[index].action = CampaignAction::Embark;
        assert!(CampaignSession::resume(&retape).is_err());
    }
}

// ── The tension that persistence must never soften ───────────────────────────────

/// **The Crown or a treasure — never both, on any drawn map.** At the bottom the pack is
/// already the three way-keys plus the prize, exactly the `CAP - FLOORS` the Lean
/// capacity law leaves; one extra relic and the Crown cannot be lifted. This is why a
/// filled reliquary costs a player MORE expeditions rather than fewer, and why banking a
/// treasure is a real sacrifice instead of a bonus.
#[test]
fn the_crown_and_a_treasure_never_come_home_together() {
    for day in 0..DAYS {
        let world = day_world(day);
        assert_eq!(
            world.homes[0], FLOORS,
            "day {day}: the prize lies at the bottom (Dungeon.drawFamily_wf)"
        );

        // Walk the day's own crowned line to the lip of the last loot — the state is
        // DRIVEN through the mover, never hand-assembled, so this test does not couple to
        // the Lean register file's shape.
        let line = crowned_line(day);
        // Stop at the lip of the last loot: the tail is now `loot 0` + `FLOORS` climbs +
        // `flee`, so the prefix drops `FLOORS + 2` moves rather than 2.
        let at_the_bottom = drive_prefix(day, &line[..line.len() - (FLOORS as usize + 2)]);
        assert_eq!(at_the_bottom.depth, FLOORS);
        assert_eq!(
            at_the_bottom.pack(),
            FLOORS - 1,
            "day {day}: at the bottom the pack is exactly the three way-keys — they are \
             never dropped, and each way `w` is opened by exercising relic `w - 1`"
        );
        assert!(
            at_the_bottom.loot(0).is_ok(),
            "day {day}: the honest crowned pack CAN lift the Crown (non-vacuity)"
        );

        // One more relic in the pack and it cannot. `pack + 1 + FLOORS <= CAP` with the
        // three keys already aboard leaves exactly zero spare capacity.
        for treasure in FLOORS as usize..RELICS {
            let mut laden = at_the_bottom.clone();
            laden.custody[treasure] = CARRIED;
            assert_eq!(laden.pack(), FLOORS);
            assert!(
                laden.loot(0).is_err(),
                "day {day}: treasure {treasure} in the pack must price the Crown out \
                 (pack {} + 1 + depth {FLOORS} > CAP {CAP})",
                laden.pack()
            );
        }
    }
}

/// The same law, DRIVEN through the real executor-backed campaign rather than the mover:
/// a run that stops for the floor-one hoard never brings the Crown home.
#[test]
fn a_greedy_run_driven_on_the_executor_does_not_crown() {
    let mut campaign = open(23);
    let day = campaign.descent().day();
    let world = day_world(day);

    campaign
        .advance(CampaignAction::Descent(DescentAction::Delve), "Down.")
        .expect("the first step lands");
    for _ in 0..world.guard_hp(1) {
        campaign
            .advance(CampaignAction::Descent(DescentAction::Smite), "Strike.")
            .expect("the first guardian falls");
    }
    let greedy: Vec<usize> = (0..RELICS).filter(|&r| world.homes[r] == 1).collect();
    assert!(!greedy.is_empty(), "day {day} mints something on floor one");
    for relic in greedy {
        campaign
            .advance(
                CampaignAction::Descent(DescentAction::Loot { relic: relic as u8 }),
                "Everything that is not nailed down.",
            )
            .expect("the felled floor gives up its hoard");
    }

    // Now try to finish the day's crowned line anyway. It runs out — of capacity, or of
    // light — before the Crown can be lifted.
    for command in crowned_actions(day) {
        if campaign
            .advance(CampaignAction::Descent(command), "Pressing on.")
            .is_err()
        {
            break;
        }
    }
    if !campaign.expedition().over() {
        walk_out(&mut campaign);
    }
    let outcome = come_home(&mut campaign);
    assert!(
        !outcome.crowned(),
        "a greedy run does not crown: {:?}",
        outcome.custody
    );
    assert!(
        !outcome.banked().is_empty(),
        "but it does bring the hoard home — that is the trade"
    );
    assert_eq!(record(&campaign, "keep").crowns, 0);
}

/// The expedition record reads the descent CELL, and it remembers what was in the pack
/// when the light went out — the one thing a run can lose that the chronicle still keeps.
#[test]
fn the_outcome_reads_the_cell_and_remembers_what_was_lost() {
    let mut custody = [0u64; RELICS];
    custody[0] = CARRIED;
    custody[4] = BANKED;
    let dead = ExpeditionOutcome {
        location: "keep".into(),
        ordinal: 3,
        day: 2,
        // A run whose light died STANDS where it fell, so the two agree here — unlike a
        // run that came home, which always stands at the surface whatever it reached.
        depth: 4,
        deepest: 4,
        spent: BREATH,
        wounds: 0,
        fate: 0,
        custody,
        commitment: [0; 32],
    };
    assert!(dead.light_died(), "spent light with no banking is a death");
    assert!(dead.over(), "and the expedition is finished either way");
    assert!(!dead.crowned(), "a carried prize is not a banked prize");
    assert_eq!(dead.lost(), vec![0], "the Crown went out with the light");
    assert_eq!(dead.banked(), vec![4]);

    let live = ExpeditionOutcome { spent: 3, ..dead };
    assert!(!live.over());
    assert!(!live.light_died());
}

// ── The relic vow still holds, over the new loop ─────────────────────────────────

#[test]
fn one_campaign_persists_character_world_relics_and_bazaar_vow() {
    let mut campaign = open(41);
    let day = campaign.descent().day();
    run_line(&mut campaign, crowned_actions(day));
    come_home(&mut campaign);

    campaign
        .advance(CampaignAction::LevelUp, "Practiced instinct.")
        .expect("the crowned XP admits level two");
    let travel = campaign
        .advance(
            CampaignAction::Travel {
                destination: "bazaar".to_string(),
            },
            "The Crown opens the old road to the Ossuary Bazaar.",
        )
        .expect("the executor-cleared road admits travel");
    assert_eq!(
        bound_campaign_narration(&travel.receipts[0]),
        Some(travel.narration_commitment)
    );

    let use_ = RelicUse::BazaarOrder {
        market: [0xBA; 32],
        order: [0x0D; 32],
    };
    let vowed = campaign
        .advance(
            CampaignAction::BindRelic {
                relic: 0,
                use_: use_.clone(),
            },
            "The Crown is placed in escrow beneath the bone chandeliers.",
        )
        .expect("a banked relic may make one Bazaar vow");
    let grant = vowed.grant.as_ref().expect("the vow exports a grant");
    assert_eq!(grant.use_, use_);
    assert_eq!(
        grant.reliquary_receipt_hash,
        vowed.receipts[0].receipt_hash()
    );
    assert_ne!(bound_relic_context(&vowed.receipts[0]), Some([0; 32]));

    let head = campaign.projection().unwrap();
    assert_eq!(head.location, "bazaar");
    assert_eq!(head.hero_level, 2);
    assert_eq!(head.relics[0], RelicState::BazaarBound);
    assert_eq!(head.relics[1], RelicState::Banked);

    let bound_head = campaign.root();
    let bound_revision = campaign.revision();
    for substituted in [
        use_.clone(),
        RelicUse::BazaarOrder {
            market: [0xBA; 32],
            order: [0x0E; 32],
        },
        RelicUse::RaidSeat {
            session: [8; 32],
            seat: 2,
        },
    ] {
        assert!(matches!(
            campaign.advance(
                CampaignAction::BindRelic {
                    relic: 0,
                    use_: substituted,
                },
                "A second claim on one relic."
            ),
            Err(CampaignError::Refused(_))
        ));
        assert_eq!(campaign.root(), bound_head, "a refusal is anti-ghost");
        assert_eq!(campaign.revision(), bound_revision);
    }

    let stored = campaign.export_record().unwrap();
    let bytes = stored.to_json().expect("the complete campaign is durable");
    let restored = CampaignRecord::from_json(&bytes).expect("durable bytes decode");
    assert_eq!(restored.root, campaign.root());
    assert_eq!(restored.projection, head);
}

#[test]
fn replay_and_every_progress_substitution_refuse_without_minting() {
    let mut campaign = open(73);
    let untouched = campaign.root();
    assert!(matches!(
        campaign.advance(
            CampaignAction::BindRelic {
                relic: 0,
                use_: RelicUse::RaidSeat {
                    session: [7; 32],
                    seat: 2,
                },
            },
            "A counterfeit vow."
        ),
        Err(CampaignError::Refused(_))
    ));
    assert_eq!(campaign.root(), untouched);
    assert_eq!(campaign.revision(), 0);
    assert_eq!(
        campaign.projection().unwrap().relics[0],
        RelicState::Unbanked
    );

    campaign
        .advance(
            CampaignAction::Descent(DescentAction::Delve),
            "The first step descends into the Keep.",
        )
        .expect("one real move lands");

    let authentic = campaign.export_record().unwrap();
    CampaignSession::verify(&authentic).expect("the authentic record replays");

    let mut wrong_move = authentic.clone();
    wrong_move.events[0].action = CampaignAction::Descent(DescentAction::Flee);
    assert!(CampaignSession::resume(&wrong_move).is_err());

    let mut wrong_narration = authentic.clone();
    wrong_narration.events[0].narration.push_str(" Retconned.");
    assert!(CampaignSession::resume(&wrong_narration).is_err());

    let mut wrong_receipt = authentic.clone();
    wrong_receipt.events[0].receipts[0].turn_hash[0] ^= 1;
    assert!(CampaignSession::resume(&wrong_receipt).is_err());

    let mut forged_xp = authentic.clone();
    forged_xp.projection.hero_xp += 10_000;
    assert!(CampaignSession::resume(&forged_xp).is_err());

    let mut forged_event_xp = authentic.clone();
    forged_event_xp.events[0].projection.hero_xp += 10_000;
    assert!(CampaignSession::resume(&forged_event_xp).is_err());
}

#[test]
fn a_failed_expedition_mints_nothing_but_no_longer_ends_the_campaign() {
    let mut campaign = open(99);
    campaign
        .advance(
            CampaignAction::Descent(DescentAction::Flee),
            "The traveller banks an empty pack and returns alive.",
        )
        .expect("an empty retreat is a lawful terminal turn");
    let empty = come_home(&mut campaign);
    assert!(!empty.crowned());
    assert_eq!(empty.depth, 0);

    let settled = campaign.projection().unwrap();
    assert!(settled.cleared_locations.is_empty());
    assert_eq!(settled.hero_xp, 0, "nothing new happened, nothing was paid");
    assert_eq!(settled.hero_level, 1);
    assert_eq!(settled.relics, [RelicState::Unbanked; RELICS]);
    let keep = record(&campaign, "keep");
    assert_eq!((keep.runs, keep.deepest, keep.crowns), (1, 0, 0));

    // Progress claims without their cause still refuse.
    let head = campaign.root();
    for action in [
        CampaignAction::LevelUp,
        CampaignAction::Travel {
            destination: "bazaar".to_string(),
        },
        CampaignAction::BindRelic {
            relic: 0,
            use_: RelicUse::BazaarOrder {
                market: [1; 32],
                order: [2; 32],
            },
        },
    ] {
        assert!(matches!(
            campaign.advance(action, "A progress claim without its cause."),
            Err(CampaignError::Refused(_))
        ));
        assert_eq!(campaign.root(), head);
    }

    // But the campaign is NOT over. This is the whole point of the run boundary: before
    // it existed, the descent froze terminal and every action above refused forever.
    go_out(&mut campaign);
    let day = campaign.descent().day();
    run_line(&mut campaign, crowned_actions(day));
    come_home(&mut campaign);
    assert_eq!(campaign.projection().unwrap().cleared_locations, ["keep"]);

    let stored = campaign.export_record().unwrap();
    CampaignSession::verify(&stored).expect("a campaign with a failed first run replays");
}

#[test]
fn the_settlement_board_names_where_the_missing_relics_lie() {
    let mut campaign = open(41);
    let day = campaign.descent().day();
    run_line(&mut campaign, crowned_actions(day));
    come_home(&mut campaign);

    let standing = campaign.standing().expect("the board builds");
    assert_eq!(standing.phase, Phase::Settlement);
    assert_eq!(standing.sealed_expeditions, 1);
    assert_eq!(
        standing.missing_relics(),
        (FLOORS as usize..RELICS).collect::<Vec<_>>(),
        "a crowned run brings home the prize and the keys; every treasure is still down there"
    );
    assert!(
        (20..=BREATH).contains(&standing.map.perfect_line_cost),
        "the next map's perfect line is as tense as every drawn map is proven to be: {}",
        standing.map.perfect_line_cost
    );
    for relic in standing.missing_relics() {
        assert!(
            standing
                .asks
                .iter()
                .any(|ask| ask.contains(&format!("Relic {relic}"))),
            "the board says where relic {relic} lies: {:?}",
            standing.asks
        );
    }
    let text = standing.briefing();
    assert!(text.contains("THE RECORD"));
    assert!(text.contains("THE RELIQUARY"));
    assert!(text.contains("WHY GO BACK"));
}

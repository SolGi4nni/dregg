//! End-to-end teeth for `spween-dregg`: a spween story runs on a dregg world-cell as
//! verifiable turns; a forged/tampered playthrough is refused; a condition-gated
//! choice is refused by the executor when its gate fails; the collective-vote loop
//! resolves a branch.

use spween_dregg::{
    CompiledStory, Driver, StepPos, StubVoteEngine, Value, VerifyBreak, WorldCell, WorldError,
    compile_scene, parse, run_collective, value_to_u64, verify, verify_by_replay,
    verify_chain_linkage,
};

/// A small branching quest exercising a numeric gate (`strength >= 5`), a membership
/// gate (`inventory.key`), effects (`strength -= 1`, `gold += …`, `has_key = true`),
/// navigation, and multiple passages.
const QUEST: &str = r#"---
id: quest
title: A Small Quest
weight: 1
---

=== gate

You face a heavy locked door.

* [Force it open] { strength >= 5 }
  ~ strength -= 1
  -> hall

* [Look for a key]
  -> search

=== search

You rummage in the dust and find something useful.

* [Grab the key]
  ~ has_key = true
  -> hall

=== hall

You are through, into the great hall.

* [Open the chest] { inventory.key }
  ~ gold += 100
  -> END

* [Rest by the fire]
  ~ gold += 10
  -> END
"#;

fn scene() -> spween::Scene {
    parse(QUEST, "quest.scene").expect("quest scene parses")
}

fn deploy_strong(seed: u8) -> WorldCell {
    let s = scene();
    let mut w = WorldCell::deploy(&s, seed).expect("deploy");
    w.seed_var("strength", Value::Int(6));
    w
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. The compiler lowers the scene to a world-cell descriptor.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn compiler_lays_out_slots_and_passages() {
    let s = scene();
    let story: CompiledStory = compile_scene(&s).expect("compile");

    // Passages indexed in scene order (matches spween::Runtime).
    assert_eq!(story.passage_index.get("gate"), Some(&0));
    assert_eq!(story.passage_index.get("search"), Some(&1));
    assert_eq!(story.passage_index.get("hall"), Some(&2));

    // Every touched variable got a distinct non-passage slot.
    for v in ["strength", "gold", "has_key"] {
        let slot = *story.var_slots.get(v).unwrap_or_else(|| panic!("{v} slot"));
        assert!(slot >= 1, "{v} is not the passage slot");
    }
    // The membership atom got a slot.
    assert!(
        story
            .has_slots
            .contains_key(&("inventory".into(), "key".into()))
    );

    // The `strength >= 5` choice fully lowered to an executor gate.
    let m = spween_dregg::choice_method("gate", 0);
    assert_eq!(story.fully_gated.get(&m), Some(&true));
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. Single-player verifiable CYOA — the stock runtime, each choice a real turn.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn single_player_playthrough_runs_and_reverifies() {
    let s = scene();
    let world = deploy_strong(7);
    let mut driver = Driver::start(world, &s).expect("start");

    // At the gate, strength 6 makes "Force it open" available.
    let choices = driver.choices();
    assert_eq!(choices.len(), 2);
    assert!(
        choices[0].available,
        "Force it open is available at strength 6"
    );

    // Force the door (a real turn), arrive in the hall.
    driver.advance(0).expect("force the door commits as a turn");
    assert_eq!(driver.current_passage().as_deref(), Some("hall"));
    // strength was spent (6 - 1) on the committed turn.
    assert_eq!(driver.world().read_var("strength"), 5);

    // No key ⇒ "Open the chest" is unavailable; rest by the fire (index 1).
    let hall = driver.choices();
    assert!(!hall[0].available, "no key ⇒ chest is unavailable");
    assert!(hall[1].available);
    driver.advance(1).expect("rest commits");
    assert!(driver.is_ended(), "the scene ended");
    assert_eq!(driver.world().read_var("gold"), 10);

    // Three committed turns: genesis + 2 choices.
    let playthrough = driver.playthrough();
    assert_eq!(playthrough.steps.len(), 2);
    assert_eq!(playthrough.receipts().len(), 3);
    for r in playthrough.receipts() {
        assert_ne!(
            r.turn_hash, [0u8; 32],
            "each step is a genuine committed turn"
        );
    }

    // The playthrough re-verifies against a fresh, identically-seeded world.
    let fresh = deploy_strong(7);
    verify(fresh, &s, &playthrough).expect("the honest playthrough re-verifies");
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. A condition-gated choice is refused by the EXECUTOR when its gate fails.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn gated_choice_refused_by_executor_when_ineligible() {
    let s = scene();
    let force = force_the_door_choice(&s);

    // strength 3: the executor REFUSES the "Force it open" choice-turn (its gate
    // FieldGte fails on the post-state). Nothing about the runtime is involved — this
    // is the kernel predicate biting on a directly-submitted (forged) choice-turn.
    let mut weak = WorldCell::deploy(&s, 11).expect("deploy");
    weak.seed_var("strength", Value::Int(3));
    let refused = weak.apply_choice("gate", 0, &force);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "an ineligible gated choice is refused in-band, got {refused:?}"
    );
    // Anti-ghost: nothing committed — still at the gate, strength untouched.
    assert_eq!(weak.read_passage(), Some(0));
    assert_eq!(weak.read_var("strength"), 3);

    // strength 6: the SAME choice commits (post-state 5 ≥ gate 4).
    let mut strong = WorldCell::deploy(&s, 12).expect("deploy");
    strong.seed_var("strength", Value::Int(6));
    strong
        .apply_choice("gate", 0, &force)
        .expect("an eligible gated choice commits");
    assert_eq!(strong.read_passage(), Some(2), "advanced into the hall");
    assert_eq!(strong.read_var("strength"), 5);
}

/// The membership gate bites the same way: no `inventory.key` ⇒ the chest choice is
/// refused; seeding membership makes it commit.
#[test]
fn membership_gated_choice_bites() {
    let s = scene();
    let chest = open_the_chest_choice(&s);

    // Deploy directly into the hall (skip navigation) to isolate the membership gate.
    let mut no_key = WorldCell::deploy(&s, 21).expect("deploy");
    warp_to_hall(&mut no_key);
    let refused = no_key.apply_choice("hall", 0, &chest);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "no key ⇒ chest refused, got {refused:?}"
    );

    let mut with_key = WorldCell::deploy(&s, 22).expect("deploy");
    warp_to_hall(&mut with_key);
    with_key.seed_membership("inventory", "key");
    with_key
        .apply_choice("hall", 0, &chest)
        .expect("with the key, the chest opens");
    assert_eq!(with_key.read_var("gold"), 100);
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. A tampered / forged playthrough is refused.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn forged_playthrough_is_refused() {
    let s = scene();
    let world = deploy_strong(31);
    let mut driver = Driver::start(world, &s).expect("start");
    driver.advance(0).expect("force"); // gate -> hall
    driver.advance(1).expect("rest"); // hall -> END
    let genuine = driver.playthrough();

    // (a) Baseline: the genuine record verifies.
    verify(deploy_strong(31), &s, &genuine).expect("genuine verifies");

    // (b) Receipt-chain break: corrupt a recorded post-state hash — the hash chain no
    //     longer links.
    {
        let mut tampered = genuine.clone();
        tampered.steps[0].receipt.post_state_hash = [0xAB; 32];
        assert!(
            matches!(
                verify_chain_linkage(&tampered),
                Err(VerifyBreak::LinkageBroken { .. })
            ),
            "a spliced receipt breaks the chain"
        );
    }

    // (c) Retcon a choice: swap the first choice to "Look for a key" (a different
    //     branch). Replay reproduces a DIFFERENT committed state than recorded.
    {
        let mut retconned = genuine.clone();
        retconned.steps[0].choice_index = 1; // was 0 (Force it open)
        let out = verify_by_replay(deploy_strong(31), &s, &retconned);
        assert!(
            matches!(
                out,
                Err(VerifyBreak::StateMismatch {
                    step: StepPos::Step(0)
                }) | Err(VerifyBreak::PassageOutOfOrder { .. })
            ),
            "a retconned choice fails replay, got {out:?}"
        );
    }

    // (d) Fabricate a turn: forge a zero-hash receipt into the chain.
    {
        let mut fake = genuine.clone();
        fake.steps[0].receipt.turn_hash = [0u8; 32];
        assert!(
            matches!(
                verify_chain_linkage(&fake),
                Err(VerifyBreak::ZeroTurnHash { .. })
            ),
            "a fabricated (hash-less) turn is not a genuine committed turn"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. Collective CYOA — the crowd votes each branch.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn collective_vote_resolves_each_branch() {
    let s = scene();
    let world = deploy_strong(41);
    let mut driver = Driver::start(world, &s).expect("start");
    let mut engine = StubVoteEngine::new();

    // The audience: at the gate the crowd overwhelmingly forces the door (option 0);
    // in the hall (no key) they rest (the only available option resolves).
    let rounds = run_collective(&mut driver, &mut engine, |ctx| {
        if ctx.passage == "gate" {
            // 3 voters for "Force it open" (option 0), 1 for "Look for a key".
            vec![
                ("alice".into(), 0),
                ("bob".into(), 0),
                ("carol".into(), 0),
                ("dave".into(), 1),
                // A double vote by alice is rejected by the engine (one ballot each).
                ("alice".into(), 1),
            ]
        } else {
            // In the hall the chest is gated (no key) so only "Rest" is offered.
            vec![("alice".into(), 0), ("bob".into(), 0)]
        }
    })
    .expect("the collective run resolves each branch");

    assert_eq!(rounds.len(), 2, "two collective branches resolved");
    // Round 1: the crowd forced the door.
    assert_eq!(rounds[0].passage, "gate");
    assert_eq!(rounds[0].winning_choice, 0);
    assert_eq!(rounds[0].winner_label(), "Force it open");
    assert_eq!(rounds[0].tally.get("Force it open"), Some(&3));
    // The double vote did not count — Look for a key got exactly its one honest vote.
    assert_eq!(rounds[0].tally.get("Look for a key"), Some(&1));

    assert!(driver.is_ended(), "the crowd walked the story to its end");
    // And the crowd-authored playthrough is itself un-retconnable.
    let playthrough = driver.playthrough();
    verify(deploy_strong(41), &s, &playthrough)
        .expect("the collectively-authored playthrough re-verifies");
}

/// The SAME branch loop, driven by the REAL cell-backed engine: every ballot and
/// tally is a verified turn on the `collective-choice` substrate.
#[test]
fn collective_vote_resolves_with_the_real_engine() {
    use spween_dregg::CollectiveChoiceEngine;

    let s = scene();
    let world = deploy_strong(51);
    let mut driver = Driver::start(world, &s).expect("start");
    // A four-voter electorate; a branch resolves once one vote lands (quorum 1).
    let mut engine = CollectiveChoiceEngine::new(&["alice", "bob", "carol", "dave"], 1);

    let rounds = run_collective(&mut driver, &mut engine, |ctx| {
        if ctx.passage == "gate" {
            vec![
                ("alice".into(), 0),
                ("bob".into(), 0),
                ("carol".into(), 0),
                ("dave".into(), 1),
                ("alice".into(), 1), // a double vote — refused host-side by the ballot nullifier.
            ]
        } else {
            vec![("alice".into(), 0), ("bob".into(), 0)]
        }
    })
    .expect("the real engine resolves each branch");

    assert_eq!(rounds.len(), 2);
    assert_eq!(rounds[0].winner_label(), "Force it open");
    assert_eq!(rounds[0].tally.get("Force it open"), Some(&3));
    assert_eq!(rounds[0].tally.get("Look for a key"), Some(&1));
    assert!(driver.is_ended());

    // The crowd-authored (real-engine) playthrough is itself un-retconnable.
    verify(deploy_strong(51), &s, &driver.playthrough())
        .expect("the real-engine playthrough re-verifies");
}

// ─────────────────────────────────────────────────────────────────────────────
// Small helpers: pull specific choices out of the parsed scene.
// ─────────────────────────────────────────────────────────────────────────────

fn nth_choice(scene: &spween::Scene, passage: &str, idx: usize) -> spween::Choice {
    let p = scene
        .passages
        .iter()
        .find(|p| p.name.as_str() == passage)
        .expect("passage exists");
    p.content
        .iter()
        .filter_map(|c| match c {
            spween::PassageContent::Choice(ch) => Some(ch),
            _ => None,
        })
        .nth(idx)
        .cloned()
        .expect("choice exists")
}

fn force_the_door_choice(scene: &spween::Scene) -> spween::Choice {
    nth_choice(scene, "gate", 0)
}

fn open_the_chest_choice(scene: &spween::Scene) -> spween::Choice {
    nth_choice(scene, "hall", 0)
}

/// Move a world-cell directly into the hall passage (index 2) for isolated gate tests.
fn warp_to_hall(world: &mut WorldCell) {
    // `search -> Grab the key -> hall` is ungated; drive it, or just set the passage.
    // We drive the ungated "Look for a key" then "Grab the key" so it is a genuine
    // navigation, not a hand-set slot.
    let s = scene();
    let look = nth_choice(&s, "gate", 1);
    world
        .apply_choice("gate", 1, &look)
        .expect("look for a key");
    let grab = nth_choice(&s, "search", 0);
    world
        .apply_choice("search", 0, &grab)
        .expect("grab the key");
    assert_eq!(world.read_passage(), Some(2));
    // sanity: value_to_u64 of a Bool is 1 (has_key was set).
    assert_eq!(value_to_u64(&Value::Bool(true)), 1);
}

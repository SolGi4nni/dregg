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

// ─────────────────────────────────────────────────────────────────────────────
// The federation seam: a committed choice-turn optionally routes to a real node.
// ─────────────────────────────────────────────────────────────────────────────

/// With a `Federation` target, each committed choice-turn is submitted to the node and
/// confirmed landed — the turn's `turn_hash` shows up on the node's finalized log.
#[test]
fn federation_target_lands_committed_choice_turns() {
    use dregg_node_target::{NodeTarget, StubNode};

    let s = scene();
    let force = force_the_door_choice(&s);
    let node = StubNode::new();

    let mut strong = WorldCell::deploy(&s, 41)
        .expect("deploy")
        .with_node_target(NodeTarget::federation(node.clone()));
    strong.seed_var("strength", Value::Int(6));

    let receipt = strong
        .apply_choice("gate", 0, &force)
        .expect("an eligible choice commits AND lands on the federation node");
    // The committed turn's hash landed on the node's finalized log — cross-node-verifiable.
    assert!(node.contains(&receipt.turn_hash));
    assert_eq!(node.len(), 1);
    // Local state advanced exactly as in Local mode (no regression from routing).
    assert_eq!(strong.read_passage(), Some(2));
    assert_eq!(strong.read_var("strength"), 5);
}

/// A federation node that refuses the submit makes the choice fail-closed: the caller
/// learns the turn did not replicate (`WorldError::Federation`).
#[test]
fn federation_reject_refuses_the_choice() {
    use dregg_node_target::{NodeTarget, StubNode};

    let s = scene();
    let force = force_the_door_choice(&s);
    let node = StubNode::rejecting();

    let mut strong = WorldCell::deploy(&s, 42)
        .expect("deploy")
        .with_node_target(NodeTarget::federation(node.clone()));
    strong.seed_var("strength", Value::Int(6));

    let refused = strong.apply_choice("gate", 0, &force);
    assert!(
        matches!(refused, Err(WorldError::Federation(_))),
        "a node that refuses the submit fails the choice, got {refused:?}"
    );
    assert_eq!(node.len(), 0, "nothing landed — fail-closed");
}

// ─────────────────────────────────────────────────────────────────────────────
// The clamp-defeats-the-lift fix (compiler) + the re-entry-reseed fix (runtime).
//
// A gate on a var the SAME choice DECREMENTS (`{gold>=50} ~ gold-=50`) used to lift
// to a VACUOUS `FieldGte(gold, 0)` (always true): the executor CLAMPS the Modify at
// zero, so a broke buyer's purchase committed with the purse silently zeroed and the
// goods delivered. The compiler now pins the delta with a companion
// `FieldDelta{gold, -50}`, so the clamp cannot vacate the gate. A gate on a var the
// choice does NOT touch still lifts to a bare comparison. And a passage's entry
// effects run once per passage, ever — a retreat into a seed room does not re-seed.
// ─────────────────────────────────────────────────────────────────────────────

const BAZAAR_MINI: &str = r#"---
id: bazaar-mini
title: Bazaar Mini
weight: 1
---

=== road

~ gold = 100

The coast road; a purse on your hip.

* [Step under the awning]
  -> shop

=== shop

The merchant's awning. Prices posted, no credit.

* [Buy the charm for 50 gold] { gold >= 50 }
  ~ gold -= 50
  -> shop

* [Pay into the counting room] { gold >= 100 }
  -> counting

* [Step back out to the road]
  -> road

=== counting

The counting room.

* [Seize the takings]
  ~ gold += 500
  -> END
"#;

fn bazaar_mini() -> spween::Scene {
    parse(BAZAAR_MINI, "bazaar-mini.scene").expect("bazaar-mini parses")
}

/// The constraint list installed for a choice's gate case (by dispatch method).
fn case_constraints<'a>(
    story: &'a CompiledStory,
    method: &str,
) -> &'a [dregg_app_framework::StateConstraint] {
    use dregg_app_framework::{CellProgram, TransitionGuard, symbol};
    let CellProgram::Cases(cases) = &story.program else {
        panic!("compiled program is a Cases table");
    };
    let want = symbol(method);
    cases
        .iter()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: m } if *m == want))
        .map(|c| c.constraints.as_slice())
        .expect("a case for the method")
}

/// The compiler shape: a same-var DECREMENT gate carries an exact-delta companion;
/// an UNTOUCHED-slot gate stays a bare comparison (no companion).
#[test]
fn decrement_gate_gets_exact_delta_companion_untouched_stays_bare() {
    use dregg_app_framework::{StateConstraint, field_from_u64};
    let s = bazaar_mini();
    let story = compile_scene(&s).expect("compile");
    let gold = *story.var_slots.get("gold").expect("gold slot") as u8;

    // BUY `{gold>=50} ~ gold-=50`: the lifted comparison collapses to FieldGte(gold, 0)
    // (always true) — but the companion FieldDelta(gold, -50) pins the delta so the
    // executor clamp cannot vacate the gate.
    let buy = case_constraints(&story, &spween_dregg::choice_method("shop", 0));
    assert!(
        buy.iter().any(|c| matches!(
            c,
            StateConstraint::FieldDelta { index, delta }
                if *index == gold && *delta == field_from_u64((-50i64) as u64)
        )),
        "the decrement gate carries a FieldDelta(gold, -50) companion; got {buy:?}"
    );

    // COUNTING `{gold>=100}` — the choice does not touch gold, so it stays a bare
    // FieldGte(gold, 100) with NO exact-delta companion (the correct lift is preserved).
    let door = case_constraints(&story, &spween_dregg::choice_method("shop", 1));
    assert!(
        door.iter().any(|c| matches!(
            c,
            StateConstraint::FieldGte { index, value }
                if *index == gold && *value == field_from_u64(100)
        )),
        "the untouched-slot gate lifts to a bare FieldGte(gold, 100); got {door:?}"
    );
    assert!(
        !door
            .iter()
            .any(|c| matches!(c, StateConstraint::FieldDelta { .. })),
        "an untouched-slot gate must NOT get an exact-delta companion; got {door:?}"
    );
}

/// The executor tooth, DRIVEN: a broke buyer's `{gold>=50} ~ gold-=50` purchase is
/// REFUSED (not a clamped commit); a solvent buyer commits paying EXACTLY the price;
/// spending the last coin commits to zero. (Directly-submitted choice-turns — the
/// kernel predicate biting, no runtime involved.)
#[test]
fn broke_buyer_refused_solvent_and_last_coin_commit() {
    let s = bazaar_mini();
    let buy = nth_choice(&s, "shop", 0);

    // BROKE (gold 30, charm 50): the Modify clamps the purse to 0. Without the companion
    // the gate is `FieldGte(gold, 0)` (always true) and this would commit — the bug.
    // With it, `FieldDelta(gold, -50)` sees 0 != 30 - 50 and REFUSES.
    let mut broke = WorldCell::deploy(&s, 21).expect("deploy");
    broke.seed_var("gold", Value::Int(30));
    let refused = broke.apply_choice("shop", 0, &buy);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a broke buyer's purchase is REFUSED, not a clamped commit; got {refused:?}"
    );
    assert_eq!(
        broke.read_var("gold"),
        30,
        "anti-ghost: the purse is untouched"
    );
    assert_eq!(
        broke.read_passage(),
        Some(0),
        "anti-ghost: nothing committed — the world never advanced"
    );

    // SOLVENT (gold 60): commits, purse falls by EXACTLY the price.
    let mut solvent = WorldCell::deploy(&s, 22).expect("deploy");
    solvent.seed_var("gold", Value::Int(60));
    solvent
        .apply_choice("shop", 0, &buy)
        .expect("a solvent purchase commits");
    assert_eq!(solvent.read_var("gold"), 10, "the purse fell by exactly 50");

    // BOUNDARY (gold == 50): the last coin buys exactly, to zero.
    let mut exact = WorldCell::deploy(&s, 23).expect("deploy");
    exact.seed_var("gold", Value::Int(50));
    exact
        .apply_choice("shop", 0, &buy)
        .expect("spending the last coin commits (new == 0 == old - price)");
    assert_eq!(exact.read_var("gold"), 0, "the purse is empty, to the coin");
}

/// The UNTOUCHED-slot gate still bites, DRIVEN: `{gold>=100}` on a choice that does
/// not touch gold refuses below the toll and admits at/above it (the correct lift is
/// preserved by the fix).
#[test]
fn untouched_slot_gate_still_bites() {
    let s = bazaar_mini();
    let pay = nth_choice(&s, "shop", 1);

    let mut poor = WorldCell::deploy(&s, 24).expect("deploy");
    poor.seed_var("gold", Value::Int(80));
    assert!(
        matches!(
            poor.apply_choice("shop", 1, &pay),
            Err(WorldError::Refused(_))
        ),
        "below the toll, the counting-room door is refused"
    );
    assert_eq!(
        poor.read_passage(),
        Some(0),
        "nothing committed — did not advance"
    );

    let mut rich = WorldCell::deploy(&s, 25).expect("deploy");
    rich.seed_var("gold", Value::Int(120));
    rich.apply_choice("shop", 1, &pay)
        .expect("at/above the toll, the door opens");
    assert_eq!(
        rich.read_passage(),
        Some(2),
        "advanced into the counting room"
    );
}

/// The re-entry fix, DRIVEN through the stock runtime: `road` seeds the purse on entry.
/// Buy the charm (100 → 50), step back out to `road` (a RE-ENTRY), then back into the
/// shop. The `~ gold = 100` seed must NOT re-run — the purse stays 50, not refilled.
// BUG 2 (the passage re-entry re-run) is fixed in the EXTERNAL spween runtime
// (~/dev/spween: `effects_executed: HashSet`). It lands in breadstuffs only when
// emberian/spween is committed + pushed + the rev bumped in spween-dregg/Cargo.toml.
// Ignored until that rev-bump so the currently-pinned spween (afb5b1f) stays green.
#[test]
#[ignore = "needs the spween runtime re-entry fix wired via a spween rev-bump (BUG 2)"]
fn retreat_into_seed_room_does_not_reseed() {
    let s = bazaar_mini();
    let world = WorldCell::deploy(&s, 26).expect("deploy");
    let mut driver = Driver::start(world, &s).expect("start");

    // Genesis ran `road`'s entry seed once.
    assert_eq!(driver.current_passage().as_deref(), Some("road"));
    assert_eq!(driver.world().read_var("gold"), 100);

    // road → shop, then BUY the charm (gold 100 → 50).
    driver.advance(0).expect("step under the awning");
    assert_eq!(driver.current_passage().as_deref(), Some("shop"));
    driver.advance(0).expect("buy the charm");
    assert_eq!(driver.world().read_var("gold"), 50, "paid exactly 50");

    // shop → road: a RE-ENTRY of the seed room. The seed must not re-run.
    driver.advance(2).expect("step back out to the road");
    assert_eq!(driver.current_passage().as_deref(), Some("road"));
    assert_eq!(
        driver.world().read_var("gold"),
        50,
        "re-entering `road` must NOT re-seed the purse to 100"
    );

    // And back into the shop — still 50, not refilled.
    driver.advance(0).expect("back under the awning");
    assert_eq!(
        driver.world().read_var("gold"),
        50,
        "no refill on the round trip"
    );
}

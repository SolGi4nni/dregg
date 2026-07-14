//! # `dreggnet-quest` — a QUEST is a gated committed cell, and a completion is a receipt.
//!
//! A quest-giver hands you a multi-step gated objective; each step is a real cap-bounded
//! turn that advances a [`WriteOnce`] step-flag; the steps are ORDER-gated (a deep step
//! cannot be raised until its prerequisite is set); you return and TURN IN for a reward
//! that opens only once the committed step-flags clear a [`FieldGte`] gate; and a
//! completion is a [`Playthrough`](spween_dregg::Playthrough) **re-executed to a declared
//! WIN** — never a self-reported "I did the steps."
//!
//! This is the **dialogue idiom generalized** (docs/GAME-INFRA-ROADMAP.md, world #1 — the
//! biggest world unlock). It re-homes [`dungeon_on_dregg::dialogue`]'s proven quest-giver
//! shape (`WriteOnce` topic step-flags, `BoundedBy` step-ordering, the `FieldGte`-gated
//! grant) onto a longer, ordered CHAIN with a return-and-turn-in reward, and binds the
//! completion to [`ugc_dregg`]'s no-cheat re-execution model.
//!
//! ## The failure mode this exists to kill
//!
//! The recurring LARP (docs roadmap, "FAILURE MODE"): quest state kept as **host
//! bookkeeping** — a client `steps_done += 1`, a turn-in that trusts a self-reported
//! count. Here **quest state is a gated committed cell**: every step-flag is real cell
//! state advanced by a real turn the verified executor admits IFF the step's gate passes,
//! the turn-in reward is a real [`FieldGte`] tooth on the committed `steps_done`, and the
//! completion is re-executed by a stranger — a forged / out-of-order record fails on
//! replay. Nothing here trusts the player's word.
//!
//! ## The quest — "The Loremaster's Errand" (a 3-step ordered chain)
//!
//! The [`ERRAND`] scene is one board room where each step is a self-looping choice (a real
//! turn that advances a step-flag and returns to the board), a turn-in choice gated on the
//! committed progress, and a hall reached once the reward is granted:
//!
//! | slot          | the quest cell remembers        | tooth (executor-enforced `StateConstraint`)                       |
//! |---------------|---------------------------------|-------------------------------------------------------------------|
//! | `step_1`      | the first ward is lit           | [`WriteOnce`] + [`FieldDelta`]`(+1)` — set once, only `0 -> 1`     |
//! | `step_2`      | the second ward is lit          | `WriteOnce` + `FieldDelta(+1)` + [`BoundedBy`]`(step_2 <- step_1)` |
//! | `step_3`      | the third ward is lit           | `WriteOnce` + `FieldDelta(+1)` + `BoundedBy(step_3 <- step_2)`     |
//! | `steps_done`  | how many wards are lit          | [`FieldDelta`]`(+1)` per step — moves in lockstep with the flags   |
//! | `reward`      | the errand is turned in         | [`FieldGte`]`(steps_done, 3)` + `WriteOnce` — the GATED turn-in    |
//!
//! The load-bearing details:
//!
//! * **A step is a real committed turn** advancing a [`WriteOnce`] flag; a step, once done,
//!   stays done, and **re-lighting a lit ward is REFUSED** (`FieldDelta(step_k, +1)` wants
//!   `0 -> 1`; a `1 -> 1` re-write has delta `0`) — so `steps_done` cannot be inflated by
//!   spamming one step. It moves in lockstep with the DISTINCT flags.
//! * **Order-gating** ([`BoundedBy`]): step 2 cannot be raised until step 1 is set, step 3
//!   until step 2 — "step B requires step A." An out-of-order step is a real
//!   [`WorldError::Refused`](spween_dregg::WorldError) that commits nothing (anti-ghost).
//! * **The turn-in reward is gated on the committed steps** ([`FieldGte`]`(steps_done, 3)`,
//!   compiler-emitted from `{ steps_done >= 3 }`, plus a [`WriteOnce`] `reward`): a turn-in
//!   without the steps is refused; with them it commits. Never an ungated grant.
//! * **A completion is a re-executed receipt** ([`verify_quest`] / [`quest_win`]): a
//!   recorded [`Playthrough`](spween_dregg::Playthrough) is re-driven against a fresh,
//!   identically-seeded quest cell and must reproduce the committed state chain AND reach
//!   the declared [`WinCondition`](ugc_dregg::WinCondition) (`reward == 1`). A forged record
//!   — an out-of-order step retconned in — fails [`verify_by_replay`](spween_dregg::verify_by_replay)
//!   on the `BoundedBy` tooth. This is the ugc-dregg no-cheat model, on a quest.
//!
//! ## The cross-cell quest-giver ([`giver`])
//!
//! The turn-in reward above is a SAME-CELL gate (the reward lives on the quest cell). The
//! [`giver`] module adds the CROSS-CELL half (the multicell idiom, [`dungeon_on_dregg::multicell`]):
//! a quest-giver cell whose grant is a real [`StateConstraint::ObservedFieldEquals`] reading
//! the quest cell's committed `reward` slot at its post-turn-in finalized root — the giver
//! hands over its reward only because the objective was completed on ANOTHER cell. The grant
//! is refused before the quest is turned in and commits after.
//!
//! ## Honest scope + named residuals
//!
//! * A completion is a **re-executed receipt**, not a client counter — the whole point.
//! * The quest is a FIXED 3-step ordered chain authored here (the concrete slice, like
//!   [`dungeon_on_dregg::dialogue`]'s Vigil). A **durable per-character quest LOG** (this
//!   crate's live cell is in-process; the persistent per-identity store is the character
//!   store's job, exactly as [`dungeon_on_dregg::progression`]'s sheet is), **branching
//!   quests gated on faction standing** (a `FieldGte` on a per-faction reputation slot — the
//!   faction whitespace the roadmap names), and **quests as authorable spween objects via
//!   the `/gallery` publish-scene flywheel** (an author writes the quest scene as text; the
//!   ordering teeth ride an attenuated `TransitionCase`, exactly [`ugc_dregg`]'s
//!   `authored_signed` path) are named seams over this real core, not gaps in it.
//! * The reward AMOUNT / the objective content are quest-design; the teeth guarantee the
//!   LEDGER invariant (ordered once-set step-flags, a step-gated turn-in, an un-fakeable
//!   completion), not the game-balance.
//!
//! [`WriteOnce`]: dregg_app_framework::StateConstraint::WriteOnce
//! [`BoundedBy`]: dregg_app_framework::StateConstraint::BoundedBy
//! [`FieldGte`]: dregg_app_framework::StateConstraint::FieldGte
//! [`FieldDelta`]: dregg_app_framework::StateConstraint::FieldDelta

pub mod giver;

use std::sync::Arc;

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, field_from_u64, symbol};
use spween::Scene;
use spween_dregg::{
    CompiledStory, PASSAGE_ENDED, PASSAGE_SLOT, Playthrough, VerifyBreak, WorldCell, choice_method,
    compile_scene, parse,
};
use ugc_dregg::WinCondition;

// ── The quest topology — rooms + line coordinates the driver/verifier speak in ─────

/// The board room where the quest is taken and its steps advanced (each step a
/// self-looping choice).
pub const ROOM_BOARD: &str = "board";
/// The hall reached once the errand is turned in (the reward is granted).
pub const ROOM_HALL: &str = "hall";

/// `board`: light the first ward — advances `step_1` (the first chain step, no prereq).
pub const LN_LIGHT_1: usize = 0;
/// `board`: light the second ward — advances `step_2`. Order-gated [`BoundedBy`]`(step_2
/// <- step_1)`: refused until the first ward is lit.
///
/// [`BoundedBy`]: dregg_app_framework::StateConstraint::BoundedBy
pub const LN_LIGHT_2: usize = 1;
/// `board`: light the third ward — advances `step_3`. Order-gated `BoundedBy(step_3 <-
/// step_2)`.
pub const LN_LIGHT_3: usize = 2;
/// `board`: turn in the errand — the GATED reward. Gated on the committed progress
/// (`FieldGte(steps_done, `[`TURN_IN_THRESHOLD`]`)`, compiled) + [`WriteOnce`] `reward`.
///
/// [`WriteOnce`]: dregg_app_framework::StateConstraint::WriteOnce
pub const LN_TURN_IN: usize = 3;
/// `hall`: accept the sealed writ (ends the quest).
pub const HALL_ACCEPT: usize = 0;

/// The number of ordered steps in the errand chain.
pub const NUM_STEPS: usize = 3;
/// The committed-progress floor the turn-in requires (`steps_done >= 3`).
pub const TURN_IN_THRESHOLD: u64 = NUM_STEPS as u64;
/// The value the `reward` slot lands at on a turn-in (the completion marker).
pub const REWARD_VALUE: u64 = 1;

/// The step var name for chain step `k` (1-based: `step_1`, `step_2`, `step_3`).
pub fn step_var(k: usize) -> String {
    format!("step_{k}")
}

// ── The Errand scene — the quest as a real spween scene ────────────────────────────

/// **"The Loremaster's Errand" — the quest, in the spween narrative DSL.** One board room
/// where each step is a self-looping choice (a real turn that advances a step-flag and
/// returns to the board), a turn-in choice the compiler CAN gate directly (`{ steps_done
/// >= 3 }` becomes a real [`FieldGte`](dregg_app_framework::StateConstraint::FieldGte)
/// tooth), and a hall reached once the reward is granted. [`errand_compiled`] AUGMENTS the
/// richer teeth the v0 compiler does not emit (the `WriteOnce`/`FieldDelta` on each step,
/// the `BoundedBy` ordering, the `WriteOnce` on the reward) — exactly the
/// [`dungeon_on_dregg::dialogue`] `vigil_compiled` idiom.
pub const ERRAND: &str = r#"---
id: loremasters-errand
title: The Loremaster's Errand
weight: 1
---

=== board

~ steps_done = 0

The Loremaster sets three cold wards along the cloister wall and folds her hands.
"Light them in their proper order," she says, "then return to me, and the writ is
yours." The board holds your tasks; the sealed writ waits under her palm.

* [Light the first ward]
  ~ step_1 = 1
  ~ steps_done += 1
  -> board

* [Light the second ward]
  ~ step_2 = 1
  ~ steps_done += 1
  -> board

* [Light the third ward]
  ~ step_3 = 1
  ~ steps_done += 1
  -> board

* [Return and turn in the errand] { steps_done >= 3 }
  ~ reward = 1
  -> hall

=== hall

The Loremaster lifts her palm from the writ and presses the sealed vellum into your
hands. The wax bears the mark of a task truly done.

* [Accept the writ]
  ~ gold += 1
  -> END
"#;

/// Parse the Errand scene.
pub fn errand_scene() -> Scene {
    parse(ERRAND, "loremasters-errand.scene").expect("the errand scene parses")
}

// ── Compiling the quest teeth (the dialogue `augment_case` idiom) ──────────────────

/// Look up a var's compiled cell slot (panics on an unnamed var — every var below is named
/// by an effect/condition in [`ERRAND`], so it always resolves). Mirrors
/// [`dungeon_on_dregg::dialogue`]'s `vigil_slot`.
fn quest_slot(story: &CompiledStory, name: &str) -> u8 {
    (*story
        .var_slots
        .get(name)
        .unwrap_or_else(|| panic!("quest var `{name}` has a compiled slot"))) as u8
}

/// Append `extra` constraints onto the compiled method-guarded case for `method` (a quest
/// tooth the v0 compiler does not emit). Panics on a coordinate typo (no such case).
/// Mirrors the dialogue crate's `augment_case`; an augmented case is enforced identically
/// to a compiled one — the executor never distinguishes who authored a `TransitionCase`.
fn augment_case(program: &mut CellProgram, method: &str, extra: Vec<StateConstraint>) {
    let m = symbol(method);
    let CellProgram::Cases(cases) = program else {
        panic!("errand program is Cases");
    };
    let case = cases
        .iter_mut()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
        .unwrap_or_else(|| panic!("no compiled case for method `{method}`"));
    case.constraints.extend(extra);
}

/// **Compile the Errand AND augment its program with the quest teeth.** The turn-in's
/// progress gate (`FieldGte(steps_done, 3)`) is already compiler-emitted from the scene
/// condition `{ steps_done >= 3 }`; this adds the shapes the v0 compiler does not express:
///
/// * each `LN_LIGHT_k` — [`WriteOnce`] `step_k` (a step, once done, stays done) +
///   [`FieldDelta`]`(step_k, +1)` (only a genuine `0 -> 1`, so re-lighting a lit ward is
///   refused and `steps_done` cannot be inflated) + `FieldDelta(steps_done, +1)` (the
///   counter moves in lockstep with the distinct flags);
/// * `LN_LIGHT_2` / `LN_LIGHT_3` — additionally [`BoundedBy`]`(step_k <- step_{k-1})` (the
///   ORDER gate: step `k` cannot be raised until step `k-1` is set);
/// * `LN_TURN_IN` — [`WriteOnce`] `reward` + [`FieldEquals`]`(reward, 1)` (the reward is
///   granted once, and lands the completion marker) on top of the compiled `FieldGte`.
///
/// The result is a [`CellProgram`] the real executor enforces line-for-line.
///
/// [`WriteOnce`]: dregg_app_framework::StateConstraint::WriteOnce
/// [`FieldDelta`]: dregg_app_framework::StateConstraint::FieldDelta
/// [`BoundedBy`]: dregg_app_framework::StateConstraint::BoundedBy
/// [`FieldEquals`]: dregg_app_framework::StateConstraint::FieldEquals
pub fn errand_compiled() -> CompiledStory {
    let mut story = compile_scene(&errand_scene()).expect("the errand compiles");

    let steps_done = quest_slot(&story, "steps_done");
    let reward = quest_slot(&story, "reward");
    let step: Vec<u8> = (1..=NUM_STEPS)
        .map(|k| quest_slot(&story, &step_var(k)))
        .collect();

    // Each step: a WriteOnce, single-increment flag, moving `steps_done` in lockstep. The
    // FieldDelta(step_k, +1) makes a re-light (a 1->1 write, delta 0) a real refusal, so
    // spamming one step cannot inflate the counter past the distinct flags.
    let step_lines = [LN_LIGHT_1, LN_LIGHT_2, LN_LIGHT_3];
    for (i, &line) in step_lines.iter().enumerate() {
        let mut extra = vec![
            StateConstraint::WriteOnce { index: step[i] },
            StateConstraint::FieldDelta {
                index: step[i],
                delta: field_from_u64(1),
            },
            StateConstraint::FieldDelta {
                index: steps_done,
                delta: field_from_u64(1),
            },
        ];
        // The ORDER gate: step k (k >= 2) may only be raised while step k-1 is set.
        if i > 0 {
            extra.push(StateConstraint::BoundedBy {
                index: step[i],
                witness_index: step[i - 1],
            });
        }
        augment_case(&mut story.program, &choice_method(ROOM_BOARD, line), extra);
    }

    // The turn-in: the compiled FieldGte(steps_done, 3) gate already bars an incomplete
    // errand; add the WriteOnce reward + the completion marker it lands.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BOARD, LN_TURN_IN),
        vec![
            StateConstraint::FieldEquals {
                index: reward,
                value: field_from_u64(REWARD_VALUE),
            },
            StateConstraint::WriteOnce { index: reward },
        ],
    );

    story
}

/// **Deploy the Errand as a real world-cell** (the quest teeth installed as executor
/// predicates). Deterministic in `seed` (re-deploy reproduces the same identity + state
/// hashes, what the replay verifier leans on). The quest begins with every ward cold; only
/// real, ordered step turns advance it.
pub fn deploy_quest(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(errand_compiled()), seed).expect("the quest deploys")
}

/// The executor-enforced constraints installed on the case guarded by `method` — proof each
/// quest rule is a real kernel predicate (for an audit to print verbatim). Mirrors the
/// dialogue crate's `case_constraints`.
pub fn case_constraints(story: &CompiledStory, method: &str) -> Vec<StateConstraint> {
    let m = symbol(method);
    let CellProgram::Cases(cases) = &story.program else {
        return Vec::new();
    };
    cases
        .iter()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
        .map(|c| c.constraints.clone())
        .unwrap_or_default()
}

/// The dispatch method for line `index` in the `board` room (the coordinate a driven line
/// presents). A thin re-export of [`choice_method`] pinned to the quest board.
pub fn board_method(index: usize) -> String {
    choice_method(ROOM_BOARD, index)
}

// ── The completion — a replay-verified receipt, not a self-reported count ──────────

/// The declared WIN of the errand: the scene ENDED **and** the reward was granted (`reward
/// == 1`). A completion counts only if a replay reaches this — the [`ugc_dregg`] no-cheat
/// model, on a quest. (The `reward == 1` var strengthens the scene-ended check: an
/// incomplete errand that never turned in is refused even if it somehow reached a terminal.)
pub fn quest_win() -> WinCondition {
    WinCondition::ended_with(&[("reward", REWARD_VALUE)])
}

/// Whether a final committed state vector satisfies [`quest_win`]: the scene reached its
/// terminal (`PASSAGE_SLOT == PASSAGE_ENDED`) and every declared win-var holds. Mirrors
/// [`ugc_dregg`]'s private `reached_win`, evaluated over the quest's var slots.
pub fn reached_quest_win(story: &CompiledStory, state: &[u64]) -> bool {
    let ended = state.get(PASSAGE_SLOT).is_some_and(|&p| p == PASSAGE_ENDED);
    if !ended {
        return false;
    }
    quest_win().vars.iter().all(|(name, want)| {
        story
            .var_slots
            .get(name)
            .and_then(|&slot| state.get(slot))
            .is_some_and(|&got| got == *want)
    })
}

/// Why a submitted quest completion was rejected (a real refusal — the board is no-cheat by
/// construction). The quest analogue of [`ugc_dregg::RejectReason`], over the quest's
/// augmented teeth.
#[derive(Clone, Debug)]
pub enum QuestReject {
    /// The recorded receipt chain did not re-verify — a forged / edited / out-of-order
    /// playthrough refused by the real executor on replay, or diverging from the reproduced
    /// committed state. The no-cheat tooth biting.
    FailedVerification(VerifyBreak),
    /// The playthrough re-verified, but it did not reach the declared WIN (the errand was
    /// not turned in — the reward is not `1`). An incomplete quest.
    DidNotWin,
    /// The playthrough won, but the claimed turn count did not equal the verified move
    /// count. A tampered result.
    ResultMismatch {
        /// What the submitter claimed.
        claimed: usize,
        /// The verified move count.
        actual: usize,
    },
}

/// **THE QUEST NO-CHEAT VERIFIER** — a completion is a re-executed receipt. Re-drives the
/// recorded `play` against a FRESH, identically-`seed`ed quest cell (its full augmented
/// teeth) and requires:
///
/// 1. the recorded receipt chain re-verifies ([`verify`](spween_dregg::verify) = chain
///    linkage + replay) — a forged / out-of-order record fails HERE on the real teeth (the
///    `BoundedBy` refuses a step raised before its prerequisite on replay);
/// 2. the replay reaches the declared WIN ([`quest_win`] — the errand was turned in);
/// 3. the claimed turns equal the verified move count.
///
/// On success returns the verified turns-to-completion. This is [`ugc_dregg`]'s
/// [`verify_completion`](ugc_dregg::verify_completion) model, applied to a quest whose teeth
/// include the ordering gate — so the completion cannot be forged, only earned.
pub fn verify_quest(
    seed: u8,
    play: &Playthrough,
    claimed_turns: usize,
) -> Result<usize, QuestReject> {
    let scene = errand_scene();
    // (1) Re-execute: chain-linkage + replay against a fresh, identically-seeded cell.
    spween_dregg::verify(deploy_quest(seed), &scene, play)
        .map_err(QuestReject::FailedVerification)?;

    // (2) Require the WIN off the final reproduced state (verify above guarantees the
    // recorded states are the faithful reproduced states).
    let story = errand_compiled();
    let Some(last) = play.steps.last() else {
        return Err(QuestReject::DidNotWin);
    };
    if !reached_quest_win(&story, &last.state) {
        return Err(QuestReject::DidNotWin);
    }

    // (3) Bind the claimed result to the verified move count.
    let actual = play.steps.len();
    if claimed_turns != actual {
        return Err(QuestReject::ResultMismatch {
            claimed: claimed_turns,
            actual,
        });
    }
    Ok(actual)
}

/// The canonical winning line of the errand — light the wards in order, return, turn in,
/// accept the writ. The choice indices driven START -> WIN through the real executor teeth
/// (mirrors the overworld crate's `win_script`). The first four are `board`-room lines; the
/// last is the `hall` accept.
pub fn winning_script() -> Vec<usize> {
    vec![
        LN_LIGHT_1,  // step_1 = 1, steps_done 0 -> 1
        LN_LIGHT_2,  // step_2 = 1 (step_1 set), steps_done 1 -> 2
        LN_LIGHT_3,  // step_3 = 1 (step_2 set), steps_done 2 -> 3
        LN_TURN_IN,  // reward = 1 (steps_done >= 3) -> hall
        HALL_ACCEPT, // accept the writ -> END
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use spween_dregg::{Driver, Value, WorldError, verify, verify_by_replay, verify_chain_linkage};

    fn scene() -> Scene {
        errand_scene()
    }

    fn line(s: &Scene, room: &str, index: usize) -> spween::Choice {
        dungeon_on_dregg::choice_at(s, room, index)
    }

    /// A fresh quest cell for the direct-executor tests (which bypass genesis, so they seed
    /// `steps_done = 0` exactly as the dialogue tests seed `disposition`).
    fn fresh_quest(seed: u8) -> WorldCell {
        let mut world = deploy_quest(seed);
        world.seed_var("steps_done", Value::Int(0));
        world
    }

    /// The quest gates lower to REAL executor teeth — a kernel predicate per line, not app
    /// bookkeeping. Reads the installed program back and asserts each tooth is present.
    #[test]
    fn quest_gates_lower_to_real_teeth() {
        let story = errand_compiled();
        let steps_done = quest_slot(&story, "steps_done");
        let reward = quest_slot(&story, "reward");
        let step2 = quest_slot(&story, "step_2");
        let step1 = quest_slot(&story, "step_1");

        // Step 1 is a WriteOnce, single-increment flag (no ordering prereq).
        let s1 = case_constraints(&story, &board_method(LN_LIGHT_1));
        assert!(
            s1.iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == step1)),
            "step 1 is WriteOnce; got {s1:?}"
        );
        assert!(
            !s1.iter()
                .any(|c| matches!(c, StateConstraint::BoundedBy { .. })),
            "step 1 has no ordering prereq; got {s1:?}"
        );

        // Step 2 carries the ORDER gate BoundedBy(step_2 <- step_1).
        let s2 = case_constraints(&story, &board_method(LN_LIGHT_2));
        assert!(
            s2.iter().any(|c| matches!(c,
                StateConstraint::BoundedBy { index, witness_index }
                    if *index == step2 && *witness_index == step1)),
            "step 2 gated BoundedBy(step_2 <- step_1); got {s2:?}"
        );

        // The turn-in carries the progress gate FieldGte(steps_done, 3) + WriteOnce(reward).
        let ti = case_constraints(&story, &board_method(LN_TURN_IN));
        assert!(
            ti.iter().any(|c| matches!(c,
                StateConstraint::FieldGte { index, value }
                    if *index == steps_done && *value == field_from_u64(TURN_IN_THRESHOLD))),
            "turn-in gated FieldGte(steps_done, {TURN_IN_THRESHOLD}); got {ti:?}"
        );
        assert!(
            ti.iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == reward)),
            "turn-in sets WriteOnce(reward); got {ti:?}"
        );
    }

    /// A step is a real committed turn that ADVANCES a WriteOnce step-flag, and the quest
    /// REMEMBERS: the raised flag + counter persist across turns (read off the committed
    /// ledger) and the receipts chain (`pre == prev.post`).
    #[test]
    fn a_step_advances_a_flag_and_the_quest_remembers() {
        let s = scene();
        let world = fresh_quest(20);
        assert_eq!(world.read_var("steps_done"), 0, "the errand begins cold");
        assert_eq!(world.read_var("step_1"), 0);

        let l1 = line(&s, ROOM_BOARD, LN_LIGHT_1);
        let r1 = world
            .apply_choice(ROOM_BOARD, LN_LIGHT_1, &l1)
            .expect("lighting the first ward is a real committed turn");
        assert_eq!(world.read_var("step_1"), 1, "the first ward is lit");
        assert_eq!(world.read_var("steps_done"), 1, "progress advanced");

        // The quest REMEMBERS across turns: a later read still sees the raised flag.
        assert_eq!(
            world.read_var("step_1"),
            1,
            "the lit ward persists on-ledger"
        );

        let l2 = line(&s, ROOM_BOARD, LN_LIGHT_2);
        let r2 = world
            .apply_choice(ROOM_BOARD, LN_LIGHT_2, &l2)
            .expect("the second ward lights (first is set)");
        assert_eq!(world.read_var("steps_done"), 2);
        assert_ne!(
            r1.turn_hash, [0u8; 32],
            "a step is a genuine committed turn"
        );
        assert_eq!(
            r2.pre_state_hash, r1.post_state_hash,
            "the quest receipts chain (pre == prev.post) — one serial ledger"
        );
    }

    /// THE ORDER GATE (`BoundedBy`), non-vacuous: an OUT-OF-ORDER step (the second ward
    /// before the first) is a real `WorldError::Refused` that commits nothing; the SAME step
    /// commits once the prerequisite is set. Identical line, refused then admitted — one
    /// step the only difference.
    #[test]
    fn out_of_order_step_is_refused_then_commits() {
        let s = scene();
        let world = fresh_quest(21);

        // Second ward before the first: BoundedBy(step_2 <- step_1) refuses (step_1 == 0).
        let l2 = line(&s, ROOM_BOARD, LN_LIGHT_2);
        let refused = world.apply_choice(ROOM_BOARD, LN_LIGHT_2, &l2);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "an out-of-order step is refused by BoundedBy, got {refused:?}"
        );
        assert_eq!(world.read_var("step_2"), 0, "anti-ghost: step 2 not set");
        assert_eq!(world.read_var("steps_done"), 0, "anti-ghost: no progress");

        // Light the first ward (the prerequisite), then the SAME second-ward step commits.
        world
            .apply_choice(ROOM_BOARD, LN_LIGHT_1, &line(&s, ROOM_BOARD, LN_LIGHT_1))
            .expect("the first ward lights");
        assert_eq!(world.read_var("step_1"), 1);
        world
            .apply_choice(ROOM_BOARD, LN_LIGHT_2, &l2)
            .expect("the second ward lights once the first is set");
        assert_eq!(world.read_var("step_2"), 1, "the order gate opened");
        assert_eq!(world.read_var("steps_done"), 2);
    }

    /// Re-lighting a lit ward is REFUSED (`FieldDelta(step_k, +1)` wants `0 -> 1`, a `1 -> 1`
    /// re-write has delta `0`), so `steps_done` cannot be inflated by spamming one step past
    /// the distinct flags — the anti-LARP tooth on the counter.
    #[test]
    fn a_relit_ward_is_refused_so_progress_cannot_be_spammed() {
        let s = scene();
        let world = fresh_quest(22);
        let l1 = line(&s, ROOM_BOARD, LN_LIGHT_1);
        world
            .apply_choice(ROOM_BOARD, LN_LIGHT_1, &l1)
            .expect("first light commits");
        assert_eq!(world.read_var("steps_done"), 1);

        // Re-light the SAME ward: refused (WriteOnce + FieldDelta(+1) bar a 1->1 re-write).
        let relit = world.apply_choice(ROOM_BOARD, LN_LIGHT_1, &l1);
        assert!(
            matches!(relit, Err(WorldError::Refused(_))),
            "re-lighting a lit ward is refused, got {relit:?}"
        );
        assert_eq!(
            world.read_var("steps_done"),
            1,
            "anti-ghost: progress not inflated by a re-light"
        );
    }

    /// THE GATED TURN-IN (both directions, non-vacuous): a turn-in WITHOUT the steps is
    /// refused by `FieldGte(steps_done, 3)` and grants nothing; after the chain is done the
    /// SAME turn-in commits and the reward lands as real committed state. The reward is gated
    /// on the committed steps — never an ungated grant.
    #[test]
    fn turn_in_is_gated_on_the_committed_steps() {
        let s = scene();
        let world = fresh_quest(23);

        // Turn in with no steps: refused (steps_done 0 < 3). Prose cannot move it.
        let ti = line(&s, ROOM_BOARD, LN_TURN_IN);
        let early = world.apply_choice(ROOM_BOARD, LN_TURN_IN, &ti);
        assert!(
            matches!(early, Err(WorldError::Refused(_))),
            "a turn-in without the steps is refused, got {early:?}"
        );
        assert_eq!(world.read_var("reward"), 0, "anti-ghost: no reward");

        // Do the chain in order.
        for k in [LN_LIGHT_1, LN_LIGHT_2, LN_LIGHT_3] {
            world
                .apply_choice(ROOM_BOARD, k, &line(&s, ROOM_BOARD, k))
                .unwrap_or_else(|e| panic!("step {k} commits: {e}"));
        }
        assert_eq!(world.read_var("steps_done"), 3);

        // The SAME turn-in now commits — the reward is real committed state.
        world
            .apply_choice(ROOM_BOARD, LN_TURN_IN, &ti)
            .expect("the turn-in commits once the steps are done");
        assert_eq!(world.read_var("reward"), 1, "the reward is granted");
    }

    /// THE FULL QUEST CHAIN as a real receipt chain that re-verifies (chain linkage +
    /// replay), the completion re-verifies to the WIN, and a FORGED completion (an
    /// out-of-order step retconned in) fails replay — the un-fakeable receipt.
    #[test]
    fn full_quest_reverifies_and_a_forged_completion_fails() {
        let s = scene();
        let script = winning_script();

        let mut driver = Driver::start(deploy_quest(30), &s).expect("start the quest");
        assert_eq!(
            driver.world().read_var("steps_done"),
            0,
            "genesis seeds a cold errand"
        );
        for &ln in &script {
            driver
                .advance(ln)
                .unwrap_or_else(|e| panic!("the winning line {ln} lands: {e}"));
        }
        assert!(
            driver.is_ended(),
            "the errand is turned in — the quest is won"
        );
        assert_eq!(driver.world().read_var("reward"), 1);
        assert_eq!(driver.world().read_var("steps_done"), 3);

        let play = driver.playthrough();
        assert_eq!(
            play.steps.len(),
            script.len(),
            "one committed step per line"
        );
        verify_chain_linkage(&play).expect("the quest receipt chain links");
        verify(deploy_quest(30), &s, &play).expect("the honest quest re-verifies by replay");

        // The completion re-verifies to the declared WIN in the claimed turns.
        let turns = verify_quest(30, &play, script.len()).expect("the completion is accepted");
        assert_eq!(turns, script.len());

        // FORGE the record: retcon the FIRST step from lighting ward 1 to lighting ward 2.
        // On replay the BoundedBy(step_2 <- step_1) refuses (step_1 is not yet set), so the
        // forged completion fails — you cannot claim the steps you did not earn.
        let mut forged = play.clone();
        forged.steps[0].choice_index = LN_LIGHT_2;
        let out = verify_by_replay(deploy_quest(30), &s, &forged);
        assert!(
            matches!(
                out,
                Err(VerifyBreak::StateMismatch { .. })
                    | Err(VerifyBreak::RefusedOnReplay { .. })
                    | Err(VerifyBreak::PassageOutOfOrder { .. })
            ),
            "a forged out-of-order completion fails replay, got {out:?}"
        );
        // And the quest verifier rejects it too (the no-cheat gate).
        let rejected = verify_quest(30, &forged, forged.steps.len());
        assert!(
            matches!(rejected, Err(QuestReject::FailedVerification(_))),
            "the forged completion is rejected by the quest verifier, got {rejected:?}"
        );
    }

    /// AN INCOMPLETE completion (the wards lit but never turned in) is rejected `DidNotWin`
    /// even though its receipt chain honestly re-verifies — the win requires the reward.
    #[test]
    fn an_incomplete_completion_did_not_win() {
        let s = scene();
        let mut driver = Driver::start(deploy_quest(31), &s).expect("start");
        for &ln in &[LN_LIGHT_1, LN_LIGHT_2, LN_LIGHT_3] {
            driver.advance(ln).expect("light the ward");
        }
        // No turn-in: honest but incomplete.
        let play = driver.playthrough();
        verify(deploy_quest(31), &s, &play).expect("the incomplete run honestly re-verifies");
        let rejected = verify_quest(31, &play, play.steps.len());
        assert!(
            matches!(rejected, Err(QuestReject::DidNotWin)),
            "an incomplete quest did not win, got {rejected:?}"
        );
    }
}

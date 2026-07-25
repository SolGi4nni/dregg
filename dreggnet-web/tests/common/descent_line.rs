//! **ASK THE GAME FOR A LEGAL NATIVE-DESCENT LINE — never author one.**
//!
//! A hand-written move tape for the native Descent is a fixture failure wearing a product
//! failure's clothes, and this repo has now paid for it three times: a literal tape died when
//! `harm`/`lunge` made a floor cost a second blow, a hand-written greedy line died on
//! `flee refused: the light dies` once `ascend` charged for the climb home, and
//! `descent_native_leaderboard`'s tape died the same way and stayed red.
//!
//! So no line is authored here either. [`plan_line`] is a shortest-`spent` search over the
//! MOVER's own transitions ([`Sim::delve`], [`Sim::smite`], [`Sim::lunge`], [`Sim::loot`],
//! [`Sim::unlock`], [`Sim::ascend`], [`Sim::flee`]) — every edge is a verb the game itself said
//! was legal, so a plan can never contain an illegal move, and the search finds a line whenever
//! one exists at all. It is not self-fulfilling: the planned verbs are then driven through the
//! REAL executor-backed `Offering` and the caller asserts the outcome it wanted actually happened.
//!
//! Shared by `descent_run_card` and `descent_native_leaderboard` so a rule change moves ONE
//! search, not two divergent tapes.

#![allow(dead_code)]

use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap};

use dreggnet_offerings::native_descent::{
    NativeDescentOffering, NativeDescentRecord, NativeDescentSession,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::descent::{BANKED, BREATH, FLOORS, RELICS, Sim};
use procgen_dregg::CommittedSeed;

/// The native day's seed input, taken from the committed day seed.
pub fn native_seed_input(seed: &CommittedSeed) -> u32 {
    let bytes = seed.as_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

/// Land one move through the REAL executor, or fail loudly naming the refusal.
pub fn land(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    actor: &str,
    turn: &str,
    arg: i64,
) {
    match offering.advance(
        session,
        Action::new(turn, turn, arg, true),
        DreggIdentity(actor.to_string()),
    ) {
        Outcome::Landed { .. } => {}
        Outcome::Refused(reason) => panic!("native fixture move {turn}({arg}) refused: {reason}"),
    }
}

/// The dungeon the run is actually being played in, taken from the executor's own post-state
/// rather than re-derived from the seed — so the plan is searched over the SAME drawn map.
pub fn current_sim(session: &NativeDescentSession) -> Sim {
    session
        .export_record()
        .events
        .last()
        .map(|event| event.post.clone())
        .expect("a move has landed, so the record carries a post-state")
}

/// A shortest-`spent` line from `start` to the first state satisfying `goal`.
pub fn plan_line(start: &Sim, goal: impl Fn(&Sim) -> bool) -> Vec<(&'static str, i64)> {
    fn successors(sim: &Sim) -> Vec<((&'static str, i64), Sim)> {
        let mut out: Vec<((&'static str, i64), Sim)> = Vec::new();
        // Cheap moves first so the search reaches a settlement quickly; correctness does not
        // depend on the order, only the speed does.
        for relic in 0..RELICS {
            if let Ok(next) = sim.loot(relic) {
                out.push((("loot", relic as i64), next));
            }
        }
        for way in 2..=FLOORS {
            if let Ok(next) = sim.unlock(way) {
                out.push((("unlock", way as i64), next));
            }
        }
        if let Ok(next) = sim.lunge() {
            out.push((("lunge", 0), next));
        }
        if let Ok(next) = sim.smite() {
            out.push((("smite", 0), next));
        }
        if let Ok(next) = sim.delve() {
            out.push((("delve", 0), next));
        }
        if let Ok(next) = sim.ascend() {
            out.push((("ascend", 0), next));
        }
        if let Ok(next) = sim.flee() {
            out.push((("flee", 0), next));
        }
        out
    }
    type Key = (u64, u64, u64, u64, u64, [u64; 3], [u64; RELICS]);
    fn key(sim: &Sim) -> Key {
        (
            sim.depth,
            sim.spent,
            sim.wounds,
            sim.harm,
            sim.fate,
            sim.ways,
            sim.custody,
        )
    }
    // Dijkstra on `spent`. `spent` is in the key, so a plain visited-set is sound.
    let mut seen: BTreeSet<Key> = BTreeSet::new();
    let mut frontier: BinaryHeap<Reverse<(u64, usize)>> = BinaryHeap::new();
    // (sim, the move that reached it, the index of its parent)
    let mut nodes: Vec<(Sim, Option<(&'static str, i64)>, usize)> = vec![(start.clone(), None, 0)];
    seen.insert(key(start));
    frontier.push(Reverse((start.spent, 0)));

    while let Some(Reverse((_, index))) = frontier.pop() {
        if goal(&nodes[index].0) {
            // Walk the parent chain back to the root.
            let mut line = Vec::new();
            let mut at = index;
            while let Some(step) = nodes[at].1 {
                line.push(step);
                at = nodes[at].2;
            }
            line.reverse();
            return line;
        }
        for (step, next) in successors(&nodes[index].0) {
            if seen.insert(key(&next)) {
                let spent = next.spent;
                nodes.push((next, Some(step), index));
                frontier.push(Reverse((spent, nodes.len() - 1)));
            }
        }
    }
    panic!(
        "no line reaching the goal exists on this day within {BREATH} breath — that is a GAME \
         balance claim failing, not a fixture one"
    );
}

/// A crown-and-bank line: the flagship's promise, and it is TIGHT — 24–30 of the 30 breath
/// depending on the drawn map, which is why it cannot be written by hand.
pub fn plan_crown_line(start: &Sim) -> Vec<(&'static str, i64)> {
    plan_line(start, |sim| sim.fate != 0 && sim.custody[0] == BANKED)
}

/// **A line that spends the last of the light with the pack still full.** Every verb costs at
/// least one breath, so a run at `spent == BREATH` can never move again: those relics are frozen
/// where they are and will never be anyone's.
pub fn plan_doomed_line(start: &Sim) -> Vec<(&'static str, i64)> {
    plan_line(start, |sim| {
        sim.fate == 0 && sim.spent == BREATH && sim.pack() > 0
    })
}

/// Drive a planned line through the REAL offering.
pub fn drive(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    actor: &str,
    line: &[(&'static str, i64)],
) {
    for (turn, arg) in line {
        land(offering, session, actor, turn, *arg);
    }
}

/// Open a session and take the one move that is forced at the mouth (`delve` — at depth 0 only
/// `delve` and a nothing-banked `flee` are legal), which also reveals the day's drawn dungeon.
pub fn opened(seed: &CommittedSeed, actor: &str) -> (NativeDescentOffering, NativeDescentSession) {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(u64::from(native_seed_input(seed))))
        .expect("the native day opens");
    land(&offering, &mut session, actor, "delve", 0);
    (offering, session)
}

/// A settled crown run: the searched line, ending in the proved exit that banks the pack.
pub fn crowned_record(seed: &CommittedSeed, actor: &str) -> NativeDescentRecord {
    let (offering, mut session) = opened(seed, actor);
    let line = plan_crown_line(&current_sim(&session));
    drive(&offering, &mut session, actor, &line);
    let record = session.export_record();
    assert!(
        record
            .completion
            .as_ref()
            .is_some_and(|completion| completion.crowned),
        "the searched line must actually crown, or every assertion about it is about a run that \
         did not happen"
    );
    record
}

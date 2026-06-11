//! CapTP PIPELINE-REGISTRY STATE-MACHINE ⟷ LEAN DIFFERENTIAL.
//!
//! `Dregg2/Exec/CapTPPipeline.lean`'s §1-§7 proved the *executable drain* (each delivered send
//! is a verified `exec` turn), but it never pinned the object the captp crate actually SHIPS and
//! runs: `pipeline.rs::PipelineRegistry` — the promise-state machine that decides, BEFORE any
//! executor, WHICH queued messages are delivered, in WHAT ORDER, and what a BREAK does to the
//! queue. That was the dark-mirror gap. The new `Dregg2/Exec/CapTPPipeline.lean::Registry`
//! section closes it with a faithful, total mirror (`createPromise`/`pipelineMessage`/
//! `resolvePromise`/`breakPromise`) and proves, by `decide`:
//!
//!   * `pipelineDifferentialCorpus_observable` — the per-step `(queuedCount, stateTag, ok)`
//!     observable column for a program: create → FIFO queue ×2 → resolve (drains+clears) →
//!     queue-on-fulfilled → break (clears+marks broken) → queue-on-broken (REJECTED).
//!   * `pipelineDifferentialCorpus_drain_order` — resolve returns messages OLDEST-FIRST
//!     `[100, 101]` (the FIFO tooth).
//!
//! This test drives the REAL `PipelineRegistry` over the IDENTICAL program and asserts the SAME
//! observables. A drift on EITHER side fails:
//!   * change the Rust state machine (e.g. drain LIFO, or fail to clear on resolve, or accept a
//!     queue-on-broken) → the runtime triples diverge from the Lean-proved column → FAIL;
//!   * change the Lean model → its `decide` trips at Lean build AND the rows copied here no
//!     longer match → re-exposing the Rust drift.
//!
//! The Lean `Reg` keys are `Nat` (the Rust `u64` promise ids); the message label is the Lean
//! `Nat` we stash in `PipelinedAction.method` so we can read it back from the drained `Vec`.

use dregg_captp::FederationId;
use dregg_captp::pipeline::{
    PipelineError, PipelinePromiseState, PipelineRegistry, PipelinedAction, PipelinedMessage,
};

/// 0 = pending/absent, 1 = fulfilled, 2 = broken — exactly Lean `stepObs.stateTag`.
fn state_tag(s: Option<&PipelinePromiseState>) -> u64 {
    match s {
        None => 0,
        Some(PipelinePromiseState::Pending) => 0,
        Some(PipelinePromiseState::Fulfilled { .. }) => 1,
        Some(PipelinePromiseState::Broken { .. }) => 2,
    }
}

/// A message labelled `msg` (stored in `method`) targeting `target`, optional result promise.
fn msg(target: u64, label: u64, result: Option<u64>) -> PipelinedMessage {
    PipelinedMessage {
        target_promise_id: target,
        action: PipelinedAction {
            method: label.to_string(),
            args: vec![],
            authorization: vec![],
        },
        result_promise_id: result,
        sender: FederationId([0xCC; 32]),
    }
}

/// THE STATE-MACHINE TOOTH: replay `pipelineDifferentialCorpus` against the REAL registry and
/// assert the `(queuedCount, stateTag, ok)` triple at each step equals the Lean-proved column.
#[test]
fn pipeline_registry_observable_matches_lean_corpus() {
    let mut reg = PipelineRegistry::new();

    // The Lean-proved observable column (`pipelineDifferentialCorpus_observable`):
    //   create → (0,0,t); queue100 → (1,0,t); queue101 → (2,0,t); resolve → (0,1,t);
    //   queue-on-fulfilled → (1,1,t); break → (0,2,t); queue-on-broken → (0,2,FALSE).
    let expected: Vec<(u64, u64, bool)> = vec![
        (0, 0, true),  // create id 0: empty queue, pending
        (1, 0, true),  // queue 100: qc 1, pending, ok
        (2, 0, true),  // queue 101: qc 2 (FIFO append), pending, ok
        (0, 1, true),  // resolve: drained, qc→0, fulfilled
        (1, 1, true),  // queue-on-fulfilled: qc 1, fulfilled, ok
        (0, 2, true),  // break: cleared, qc 0, broken
        (0, 2, false), // queue-on-broken: REJECTED (!ok)
    ];
    let mut got: Vec<(u64, u64, bool)> = Vec::new();

    // .create  (id 0)
    let id = reg.create_promise();
    assert_eq!(id, 0, "first allocated id is 0, like Lean `empty.nextId`");
    got.push((
        reg.queued_count(id) as u64,
        state_tag(reg.promise_state(id)),
        true,
    ));

    // .queue 0 100 none
    let ok = reg.pipeline_message(msg(0, 100, None)).is_ok();
    got.push((
        reg.queued_count(0) as u64,
        state_tag(reg.promise_state(0)),
        ok,
    ));

    // .queue 0 101 (some 7)
    let ok = reg.pipeline_message(msg(0, 101, Some(7))).is_ok();
    got.push((
        reg.queued_count(0) as u64,
        state_tag(reg.promise_state(0)),
        ok,
    ));

    // .resolve 0 42  — drains [100,101] in FIFO order, clears the queue, marks Fulfilled.
    let drained = reg.resolve_promise(0, dregg_types::CellId([42; 32]));
    let labels: Vec<u64> = drained
        .iter()
        .map(|m| m.action.method.parse::<u64>().unwrap())
        .collect();
    assert_eq!(
        labels,
        vec![100, 101],
        "resolve drains OLDEST-FIRST (FIFO) — Lean `pipelineDifferentialCorpus_drain_order`"
    );
    got.push((
        reg.queued_count(0) as u64,
        state_tag(reg.promise_state(0)),
        true,
    ));

    // .queue 0 102 none  — queue-on-fulfilled: accepted, requeues.
    let ok = reg.pipeline_message(msg(0, 102, None)).is_ok();
    got.push((
        reg.queued_count(0) as u64,
        state_tag(reg.promise_state(0)),
        ok,
    ));

    // .breakP 0 "remote gone" — marks Broken, clears the queue.
    let _notifs = reg.break_promise(0, "remote gone".to_string());
    got.push((
        reg.queued_count(0) as u64,
        state_tag(reg.promise_state(0)),
        true,
    ));

    // .queue 0 103 none — queue-on-broken: REJECTED (`PromiseAlreadyBroken`).
    let verdict = reg.pipeline_message(msg(0, 103, None));
    let ok = verdict.is_ok();
    assert!(
        matches!(verdict, Err(PipelineError::PromiseAlreadyBroken { .. })),
        "queueing onto a broken promise must be rejected (Lean `broken_target_rejects_queue`)"
    );
    got.push((
        reg.queued_count(0) as u64,
        state_tag(reg.promise_state(0)),
        ok,
    ));

    assert_eq!(
        got, expected,
        "REAL PipelineRegistry observable column drifted from the Lean-proved \
         `pipelineDifferentialCorpus_observable`"
    );
}

/// FIFO-ordering tooth in isolation: two queued sends drain oldest-first, and resolve CLEARS the
/// queue (a re-resolve drains nothing) — Lean `resolve_clears_queue` + `resolve_preserves_fifo`.
#[test]
fn resolve_is_fifo_and_clears() {
    let mut reg = PipelineRegistry::new();
    let p = reg.create_promise();
    reg.pipeline_message(msg(p, 1, None)).unwrap();
    reg.pipeline_message(msg(p, 2, None)).unwrap();
    reg.pipeline_message(msg(p, 3, None)).unwrap();

    let drained = reg.resolve_promise(p, dregg_types::CellId([9; 32]));
    let labels: Vec<u64> = drained
        .iter()
        .map(|m| m.action.method.parse::<u64>().unwrap())
        .collect();
    assert_eq!(labels, vec![1, 2, 3], "FIFO insertion order");
    assert_eq!(reg.queued_count(p), 0, "resolve clears the queue");

    // re-resolve drains nothing (queue already removed).
    let again = reg.resolve_promise(p, dregg_types::CellId([9; 32]));
    assert!(
        again.is_empty(),
        "a re-resolve drains nothing — the queue was cleared"
    );
}

/// Break-clears tooth: a broken promise delivers NOTHING and clears its queue — Lean
/// `break_freezes_state` lifted to the registry. The cascade notifications target result promises.
#[test]
fn break_clears_and_cascades() {
    let mut reg = PipelineRegistry::new();
    let upstream = reg.create_promise();
    let downstream = reg.create_promise();
    // a queued message whose result_promise_id is the (local) downstream promise.
    reg.pipeline_message(msg(upstream, 1, Some(downstream)))
        .unwrap();

    let notifs = reg.break_promise(upstream, "boom".to_string());
    assert_eq!(
        reg.queued_count(upstream),
        0,
        "break clears the queue (delivers nothing)"
    );
    assert!(
        matches!(
            reg.promise_state(upstream),
            Some(PipelinePromiseState::Broken { .. })
        ),
        "broken after break"
    );
    // the cascade broke the downstream result promise too (it was local to this registry).
    assert!(
        notifs.iter().any(|n| n.promise_id == downstream),
        "break cascades to the result promise (Lean `breakPromise` fold cascade arm)"
    );
    assert!(
        matches!(
            reg.promise_state(downstream),
            Some(PipelinePromiseState::Broken { .. })
        ),
        "the local downstream result promise is recursively broken"
    );
}

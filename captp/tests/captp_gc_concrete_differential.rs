//! CapTP DISTRIBUTED-GC SESSION-TOOTH ⟷ LEAN DIFFERENTIAL — the drift-catching tooth for
//! the byzantine session check across the FFI gap.
//!
//! `captp/src/gc.rs::ExportGcManager::process_drop_inner` decides, per `DropRef`, whether a
//! peer may decrement a holder's refcount: it rejects (`DropResult::Invalid`, NO mutation) on
//! an unknown holder, a zero count, OR — the byzantine tooth — a session id that does not match
//! the holder's stored session (`gc.rs:194`). The verified Lean model in
//! `Dregg2/Exec/CapTPGCConcrete.lean` reproduces `process_drop_inner` clause-for-clause as
//! `processDrop`, and PROVES `byzantine_cannot_drop_victim_ref`: a wrong-session drop on a
//! victim's slot returns `Invalid` and leaves `total_refs` UNCHANGED (`n = 2` holders).
//!
//! This test replays the IDENTICAL corpus rows the Lean `gcDifferentialCorpus` pins (and whose
//! `(verdict, post_total)` columns Lean's `gcDifferentialCorpus_faithful` proves by `decide`)
//! against the REAL `ExportGcManager::process_drop_with_session`, asserting the `DropResult` +
//! `ExportEntry.total_refs` agree row-for-row. A drift on EITHER side fails:
//!   * weaken the Rust session check → a byzantine row that should be `Invalid` succeeds → FAIL;
//!   * change the Lean model        → its `gcDifferentialCorpus_faithful` `decide` trips at Lean
//!     build, AND the rows copied here no longer match → re-exposing the Rust drift.
//!
//! The Lean `Fed`/`Session` are `Nat`; here we lift them into the concrete `FederationId`/
//! `SessionId` carriers. `total_refs` is the SUM of holder counts, exactly Lean's `totalRefs`.

use dregg_captp::{DropResult, ExportGcManager, SessionId};
use dregg_types::{CellId, FederationId};

/// Lift a small `Nat` federation id (Lean `Fed`) into a distinct `FederationId`.
fn fed(n: u8) -> FederationId {
    FederationId([n; 32])
}

/// The single cell every corpus row exports (the holder table is per-cell).
fn cell() -> CellId {
    CellId([0x11; 32])
}

/// A corpus row, mirroring Lean `gcDifferentialCorpus`:
/// `(holders: [(fed, count, session)], drop_fed, drop_session?, expected_verdict, expected_total)`.
struct Row {
    holders: Vec<(u8, u64, SessionId)>,
    drop_fed: u8,
    drop_session: Option<SessionId>,
    expected_verdict: DropResult,
    expected_total: u64,
}

/// Build an `ExportGcManager` whose single cell has the given holders, then process one drop.
/// Returns `(verdict, post_total_refs)` — the Rust analogue of Lean's `processDrop` outputs.
fn run(row: &Row) -> (DropResult, u64) {
    let mut mgr = ExportGcManager::new();
    let c = cell();
    // Build each holder's count by repeated session-scoped export (the only way to raise a count;
    // the LAST export's session becomes the holder's stored session — Lean's supersession too).
    for (f, count, sess) in &row.holders {
        for _ in 0..*count {
            mgr.record_export_with_session(c, fed(*f), 100, *sess);
        }
    }
    let verdict = match row.drop_session {
        Some(s) => mgr.process_drop_with_session(c, fed(row.drop_fed), s),
        // Lean's `expected = none` legacy path uses session 0 with the session-aware entry,
        // which `record_export` (session 0) installs; here we mirror by exporting on session 0.
        None => mgr.process_drop_with_session(c, fed(row.drop_fed), 0),
    };
    let total = mgr.get(&c).map(|e| e.total_refs).unwrap_or(0);
    (verdict, total)
}

/// The corpus — EXACTLY the rows of Lean `Dregg2.Exec.CapTPGCConcrete.gcDifferentialCorpus`.
/// demoTable = fed10@count1/session42 + fed20@count1/session99 ; supersededTable = fed10@count2/session7.
fn corpus() -> Vec<Row> {
    let demo = || vec![(10u8, 1u64, 42 as SessionId), (20u8, 1u64, 99 as SessionId)];
    let superseded = || vec![(10u8, 2u64, 7 as SessionId)];
    vec![
        // byzantine_node_different_session_cannot_drop_others_refs (gc.rs:670):
        // fed20's session (99) presented against fed10's slot ⇒ Invalid, total stays 2.
        Row { holders: demo(), drop_fed: 10, drop_session: Some(99), expected_verdict: DropResult::Invalid, expected_total: 2 },
        // honest drop on the CORRECT session (still held by the peer): total 2 → 1.
        Row { holders: demo(), drop_fed: 10, drop_session: Some(42), expected_verdict: DropResult::StillHeld, expected_total: 1 },
        // export_drop_rejected_from_wrong_session: re-export superseded the session ⇒ old session 1 fails.
        Row { holders: superseded(), drop_fed: 10, drop_session: Some(1), expected_verdict: DropResult::Invalid, expected_total: 2 },
        // current (superseding) session 7 succeeds: 2 → 1.
        Row { holders: superseded(), drop_fed: 10, drop_session: Some(7), expected_verdict: DropResult::StillHeld, expected_total: 1 },
        // legacy session-unaware path (Lean `expected = none`, modelled as session 0): 2 → 1.
        Row { holders: vec![(10u8, 1u64, 0 as SessionId), (20u8, 1u64, 99 as SessionId)], drop_fed: 10, drop_session: None, expected_verdict: DropResult::StillHeld, expected_total: 1 },
        // unknown federation ⇒ Invalid, total stays 2.
        Row { holders: demo(), drop_fed: 99, drop_session: Some(1), expected_verdict: DropResult::Invalid, expected_total: 2 },
    ]
}

#[test]
fn gc_session_tooth_matches_lean_corpus() {
    for (i, row) in corpus().iter().enumerate() {
        let (verdict, total) = run(row);
        assert_eq!(
            verdict, row.expected_verdict,
            "row {i}: DropResult drift vs Lean gcDifferentialCorpus"
        );
        assert_eq!(
            total, row.expected_total,
            "row {i}: total_refs drift vs Lean gcDifferentialCorpus"
        );
    }
}

/// The headline byzantine property as a standalone assertion (the Lean
/// `byzantine_cannot_drop_victim_ref` at `n = 2`): the wrong-session drop is BOTH rejected AND
/// leaves the victim's ref intact — the negative tooth on the real admission path.
#[test]
fn byzantine_wrong_session_is_a_no_op() {
    let mut mgr = ExportGcManager::new();
    let c = cell();
    // victim = fed10 on session 42; byzantine = fed20 on session 99. total_refs = 2.
    mgr.record_export_with_session(c, fed(10), 100, 42);
    mgr.record_export_with_session(c, fed(20), 100, 99);
    assert_eq!(mgr.get(&c).unwrap().total_refs, 2);

    // byzantine fed20 forges fed10's slot but can only present its OWN session 99 ⇒ rejected.
    let verdict = mgr.process_drop_with_session(c, fed(10), 99);
    assert_eq!(verdict, DropResult::Invalid);
    assert_eq!(mgr.get(&c).unwrap().total_refs, 2, "victim's ref must survive");

    // the victim, on its correct session 42, CAN drop its own ref (de-vacuity: not a blanket refusal).
    let verdict = mgr.process_drop_with_session(c, fed(10), 42);
    assert_eq!(verdict, DropResult::StillHeld);
    assert_eq!(mgr.get(&c).unwrap().total_refs, 1);
}

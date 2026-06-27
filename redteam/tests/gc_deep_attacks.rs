//! DEEP adversarial tests against distributed GC (Lean `CapTPGC` / B4), past the
//! first-pass `gc_attacks.rs` (wrong-session noop, legacy bypass FINDING,
//! re-export supersede FINDING, over-drop). These target refcount integrity
//! invariants: total_refs == sum(holder counts), no negative reclaim, holder
//! isolation, and the gc_sweep / resurrection boundary.
//!
//! Adversary model: a Byzantine peer trying to (a) desync total_refs from the
//! per-holder counts, (b) reclaim a still-held export, (c) cross-decrement
//! ANOTHER holder's refcount, or (d) resurrect a swept export.

use dregg_captp::gc::{DropResult, ExportGcManager};
use dregg_cell::CellId;
use dregg_types::FederationId;

fn cell(n: u8) -> CellId {
    CellId([n; 32])
}
fn fed(n: u8) -> FederationId {
    FederationId([n; 32])
}

/// Invariant the Lean model guarantees: an entry's `total_refs` equals the sum
/// of its per-holder `count`s. A divergence is a refcount-integrity break.
fn assert_total_refs_consistent(mgr: &ExportGcManager, c: &CellId) {
    if let Some(entry) = mgr.get(c) {
        let sum: u64 = entry.holders.values().map(|rc| rc.count).sum();
        assert_eq!(
            entry.total_refs, sum,
            "FINDING: total_refs ({}) != sum of holder counts ({})",
            entry.total_refs, sum
        );
    }
}

// ===========================================================================
// DEEP ATTACK 1 — holder ISOLATION: B dropping must never touch A's count.
//
// Two honest holders A, B each hold the same cell on their OWN sessions. B
// drops (legitimately, on B's session). A's count and the entry's total_refs
// must reflect ONLY B's decrement; A is untouched. We also assert the
// total_refs == sum invariant across every step.
// ===========================================================================

#[test]
fn deep_holder_isolation_drop_does_not_cross_decrement() {
    let mut mgr = ExportGcManager::new();
    let c = cell(1);
    mgr.record_export_with_session(c, fed(0xA), 100, 10); // A, session 10
    mgr.record_export_with_session(c, fed(0xA), 100, 10); // A, +1 = 2
    mgr.record_export_with_session(c, fed(0xB), 100, 20); // B, session 20
    assert_eq!(mgr.get(&c).unwrap().total_refs, 3);
    assert_total_refs_consistent(&mgr, &c);

    // B drops once on B's session.
    assert_eq!(
        mgr.process_drop_with_session(c, fed(0xB), 20),
        DropResult::StillHeld
    );
    // A still has exactly 2; total = 2.
    let entry = mgr.get(&c).unwrap();
    assert_eq!(
        entry.holders.get(&fed(0xA)).unwrap().count,
        2,
        "A cross-decremented!"
    );
    assert!(
        !entry.holders.contains_key(&fed(0xB)),
        "B should be cleaned up at count 0"
    );
    assert_eq!(entry.total_refs, 2);
    assert_total_refs_consistent(&mgr, &c);
    eprintln!("[GC DEEP 1] holder isolation: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 2 — no premature reclaim while another holder remains.
//
// A and B both hold. B drops to zero. The export is STILL held (by A), so the
// result must be StillHeld, NOT CanRevoke. A premature CanRevoke here would let
// the exporter revoke a cap A still depends on (denial of capability).
// ===========================================================================

#[test]
fn deep_no_premature_reclaim_with_remaining_holder() {
    let mut mgr = ExportGcManager::new();
    let c = cell(2);
    mgr.record_export_with_session(c, fed(0xA), 100, 10);
    mgr.record_export_with_session(c, fed(0xB), 100, 20);

    // B fully drops.
    assert_eq!(
        mgr.process_drop_with_session(c, fed(0xB), 20),
        DropResult::StillHeld
    );
    // A still holds → entry alive, total_refs == 1.
    assert_eq!(mgr.get(&c).unwrap().total_refs, 1);
    assert!(mgr.get(&c).unwrap().holders.contains_key(&fed(0xA)));
    assert_total_refs_consistent(&mgr, &c);
    eprintln!("[GC DEEP 2] no premature reclaim w/ remaining holder: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 3 — cross-CELL isolation: a drop on cell X must not affect cell Y.
//
// The same federation holds two DIFFERENT cells. Dropping one must leave the
// other's refcount intact. (The exports map is keyed by cell, so this should
// hold; we verify the running code keeps cells isolated.)
// ===========================================================================

#[test]
fn deep_cross_cell_isolation() {
    let mut mgr = ExportGcManager::new();
    let x = cell(3);
    let y = cell(4);
    mgr.record_export_with_session(x, fed(0xA), 100, 10);
    mgr.record_export_with_session(y, fed(0xA), 100, 10);

    // Reclaim X entirely.
    assert_eq!(
        mgr.process_drop_with_session(x, fed(0xA), 10),
        DropResult::CanRevoke
    );
    // Y untouched.
    assert_eq!(
        mgr.get(&y).unwrap().total_refs,
        1,
        "FINDING: cross-cell decrement"
    );
    assert_total_refs_consistent(&mgr, &y);
    eprintln!("[GC DEEP 3] cross-cell isolation: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 4 — over-drop never underflows total_refs or holder count.
//
// Drop more times than held, on a valid session, hammering the same holder.
// counts are u64; a naive `-= 1` past zero would underflow to u64::MAX (a
// catastrophic refcount inflation that would PIN the export alive forever, or
// crash in debug). The code must return Invalid at zero, never decrement below.
// ===========================================================================

#[test]
fn deep_overdrop_never_underflows() {
    let mut mgr = ExportGcManager::new();
    let c = cell(5);
    mgr.record_export_with_session(c, fed(0xA), 100, 10);

    // First drop reclaims.
    assert_eq!(
        mgr.process_drop_with_session(c, fed(0xA), 10),
        DropResult::CanRevoke
    );
    // 50 more drops: all Invalid, no underflow, no panic.
    for _ in 0..50 {
        assert_eq!(
            mgr.process_drop_with_session(c, fed(0xA), 10),
            DropResult::Invalid,
            "FINDING: over-drop past zero was accepted"
        );
    }
    // Entry either gone or zero; never an inflated count.
    if let Some(entry) = mgr.get(&c) {
        assert_eq!(entry.total_refs, 0);
        for rc in entry.holders.values() {
            assert!(rc.count <= 1, "FINDING: holder count inflated by underflow");
        }
    }
    eprintln!("[GC DEEP 4] over-drop underflow: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 5 — gc_sweep only reaps zero-ref exports; held ones survive.
//
// Build one live export and one fully-dropped export. gc_sweep must remove ONLY
// the dead one. A sweep that reaps a live export = premature reclaim.
// ===========================================================================

#[test]
fn deep_gc_sweep_spares_live_exports() {
    let mut mgr = ExportGcManager::new();
    let live = cell(6);
    let dead = cell(7);
    mgr.record_export_with_session(live, fed(0xA), 100, 10);
    mgr.record_export_with_session(dead, fed(0xB), 100, 20);
    // Kill `dead`.
    assert_eq!(
        mgr.process_drop_with_session(dead, fed(0xB), 20),
        DropResult::CanRevoke
    );

    let reaped = mgr.gc_sweep();
    assert!(reaped.contains(&dead), "dead export should be swept");
    assert!(
        !reaped.contains(&live),
        "FINDING: live export swept (premature reclaim)"
    );
    assert!(
        mgr.get(&live).is_some(),
        "live export must survive the sweep"
    );
    assert_total_refs_consistent(&mgr, &live);
    eprintln!("[GC DEEP 5] gc_sweep spares live exports: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 6 — wrong-session drop leaves the integrity invariant intact.
//
// A Byzantine drop on the wrong session is rejected (Invalid). Crucially, the
// REJECTION must be side-effect-free on the refcounts: total_refs and holder
// counts unchanged (no half-applied decrement). This is the GC analogue of the
// handoff "consume-on-reject" griefing FINDING — we check GC does NOT have it.
// ===========================================================================

#[test]
fn deep_wrong_session_reject_is_side_effect_free() {
    let mut mgr = ExportGcManager::new();
    let c = cell(8);
    mgr.record_export_with_session(c, fed(0xA), 100, 10);
    mgr.record_export_with_session(c, fed(0xA), 100, 10); // count 2
    let before = mgr.get(&c).unwrap().total_refs;

    // Byzantine: A's id but the WRONG session 999.
    assert_eq!(
        mgr.process_drop_with_session(c, fed(0xA), 999),
        DropResult::Invalid
    );
    let after = mgr.get(&c).unwrap().total_refs;
    assert_eq!(
        before, after,
        "FINDING: a rejected wrong-session drop still mutated the refcount"
    );
    assert_total_refs_consistent(&mgr, &c);
    eprintln!("[GC DEEP 6] wrong-session reject side-effect-free: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 7 — unknown-federation drop is rejected and side-effect-free.
//
// A federation that never held a ref tries to drop. Must be Invalid, and must
// not create a phantom holder entry or perturb total_refs.
// ===========================================================================

#[test]
fn deep_unknown_federation_drop_rejected_no_phantom() {
    let mut mgr = ExportGcManager::new();
    let c = cell(9);
    mgr.record_export_with_session(c, fed(0xA), 100, 10);
    let holders_before = mgr.get(&c).unwrap().holders.len();

    // A federation that holds nothing here.
    assert_eq!(
        mgr.process_drop_with_session(c, fed(0xC), 10),
        DropResult::Invalid
    );
    let entry = mgr.get(&c).unwrap();
    assert_eq!(entry.total_refs, 1);
    assert_eq!(
        entry.holders.len(),
        holders_before,
        "FINDING: a rejected unknown-federation drop created a phantom holder"
    );
    assert!(!entry.holders.contains_key(&fed(0xC)));
    assert_total_refs_consistent(&mgr, &c);
    eprintln!("[GC DEEP 7] unknown-federation drop: DEFENDED (no phantom)");
}

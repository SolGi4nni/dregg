//! Adversarial tests against distributed GC (Lean `CapTPGC` / B4): the
//! Byzantine-resistance claim is "a DropRef from the wrong session cannot
//! decrement another holder's refcount" (no premature reclaim). We attack it.
//!
//! Adversary model: a "Byzantine peer / capability holder" who tries to force a
//! premature revoke of someone else's still-held capability (a confused-deputy
//! revocation / denial of capability).

use dregg_captp::gc::{DropResult, ExportGcManager};
use dregg_cell::CellId;
use dregg_types::FederationId;

fn cell() -> CellId {
    CellId([1; 32])
}
fn fed_a() -> FederationId {
    FederationId([0xa; 32])
}
fn fed_b() -> FederationId {
    FederationId([0xb; 32])
}

// ===========================================================================
// ATTACK 1 — Byzantine B drops A's ref on B's own session (B4 core).
// Lean claims: rejected; A's count unchanged.
// ===========================================================================

#[test]
fn attack_byzantine_wrong_session_drop_is_noop() {
    let mut mgr = ExportGcManager::new();
    mgr.record_export_with_session(cell(), fed_a(), 100, 10); // A on session 10
    mgr.record_export_with_session(cell(), fed_b(), 100, 20); // B on session 20
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 2);

    // Byzantine: claim to be A but present B's session id.
    let r = mgr.process_drop_with_session(cell(), fed_a(), 20);
    assert_eq!(r, DropResult::Invalid);
    // EVIDENCE: A's ref survived; no premature reclaim.
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 2);
    eprintln!("[GC ATTACK 1] wrong-session drop: DEFENDED");
}

// ===========================================================================
// ATTACK 2 — DEFENDED (F-11 CLOSED): the legacy unauthenticated `process_drop`
// path is now DENIED (fail-closed). It can no longer reclaim a victim's ref: a
// DropRef with no session credential authorizes nothing. The attacker who knows
// (cell_id, victim_federation) but holds no session can no longer decrement the
// victim's refcount. (Was: BROKEN — the session-free path accepted the drop and
// forced CanRevoke, a premature reclaim out from under the holder.)
// ===========================================================================

#[test]
#[allow(deprecated)]
fn finding_legacy_process_drop_bypasses_session_byzantine_defense() {
    let mut mgr = ExportGcManager::new();
    // Honest A holds ONE ref under session 10. A still wants it.
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 1);

    // Attacker who never held the ref calls the SESSION-FREE drop with A's id.
    // No session is presented — the F-11 fix denies this path outright.
    let r = mgr.process_drop(cell(), fed_a());

    // DEFENDED: the drop is rejected; A's capability is NOT reclaimed.
    assert_eq!(
        r,
        DropResult::Invalid,
        "F-11 regressed: the session-free legacy drop was accepted again"
    );
    assert_eq!(
        mgr.get(&cell()).unwrap().total_refs,
        1,
        "F-11 regressed: the victim's ref was prematurely reclaimed by a session-free drop"
    );

    // And the attacker cannot reclaim by guessing a session either: only the
    // session that minted the ref (10) may drop it.
    assert_eq!(
        mgr.process_drop_with_session(cell(), fed_a(), 999),
        DropResult::Invalid,
        "a guessed session must not authorize a drop"
    );
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 1);

    eprintln!(
        "[GC ATTACK 2 / F-11] legacy session-free process_drop: DEFENDED (denied, fail-closed)"
    );
}

// ===========================================================================
// ATTACK 3 — DEFENDED (F-12 CLOSED): session id is now tracked PER-REF (per
// session bucket), not collapsed per-(cell, federation). A re-export under a new
// session adds a bucket for the new session and leaves every existing session's
// refs (and their drop rights) intact. So: the ORIGINAL session keeps the right
// to drop exactly the refs IT minted, and the NEW session can drop ONLY the refs
// it minted — neither can reach the other's. (Was: BROKEN-ish — a re-export
// overwrote the whole holder's session id, transferring drop rights for ALL refs
// to the most recent session.)
// ===========================================================================

#[test]
fn finding_reexport_supersedes_session_for_all_existing_refs() {
    let mut mgr = ExportGcManager::new();
    // A acquires 2 refs under the original session 10.
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 2);

    // A re-exports / reconnects under a DIFFERENT session 99. This adds a THIRD
    // ref in session 99's bucket; session 10's two refs are UNTOUCHED.
    mgr.record_export_with_session(cell(), fed_a(), 101, 99);
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 3);

    // DEFENDED: the ORIGINAL session (10) KEEPS its drop rights — it can drop the
    // two refs IT minted (previously this was wrongly rejected as Invalid).
    assert_eq!(
        mgr.process_drop_with_session(cell(), fed_a(), 10),
        DropResult::StillHeld,
        "F-12 regressed: a re-export stole the original session's drop rights"
    );
    assert_eq!(
        mgr.process_drop_with_session(cell(), fed_a(), 10),
        DropResult::StillHeld
    );
    // Session 10 has now spent its two refs; it CANNOT reach session 99's ref.
    assert_eq!(
        mgr.process_drop_with_session(cell(), fed_a(), 10),
        DropResult::Invalid,
        "F-12 regressed: session 10 reached a ref it never minted"
    );
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 1);

    // DEFENDED (the dual): the NEW session 99 can drop ONLY the one ref it minted.
    assert_eq!(
        mgr.process_drop_with_session(cell(), fed_a(), 99),
        DropResult::CanRevoke
    );
    eprintln!(
        "[GC ATTACK 3 / F-12] session is PER-REF; re-export keeps the original session's rights: DEFENDED"
    );
}

// ===========================================================================
// ATTACK 3b — DEFENDED (F-12 dual): the NEW session cannot drop refs the
// ORIGINAL session minted. The mirror image of ATTACK 3: a Byzantine reconnect
// that mints a single ref under a fresh session must not let that session reclaim
// the victim's pre-existing refs.
// ===========================================================================

#[test]
fn new_session_cannot_overdrop_into_original_sessions_refs() {
    let mut mgr = ExportGcManager::new();
    // Victim minted 2 refs under session 10.
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    // Byzantine reconnect mints 1 ref under session 99.
    mgr.record_export_with_session(cell(), fed_a(), 101, 99);
    assert_eq!(mgr.get(&cell()).unwrap().total_refs, 3);

    // Session 99 drops its own (only) ref → still held by session 10's two.
    assert_eq!(
        mgr.process_drop_with_session(cell(), fed_a(), 99),
        DropResult::StillHeld
    );
    // Session 99 has nothing left; it CANNOT reclaim session 10's refs.
    assert_eq!(
        mgr.process_drop_with_session(cell(), fed_a(), 99),
        DropResult::Invalid
    );
    assert_eq!(
        mgr.get(&cell()).unwrap().total_refs,
        2,
        "F-12 regressed: session 99 reclaimed the victim's session-10 refs"
    );
    eprintln!(
        "[GC ATTACK 3b / F-12] new session cannot over-drop into another session's refs: DEFENDED"
    );
}

// ===========================================================================
// ATTACK 4 — over-drop / underflow probe: drop more times than held.
// Lean claims counts never go negative (u64 saturating semantics matter).
// ===========================================================================

#[test]
fn attack_overdrop_does_not_underflow_or_overrevoke() {
    let mut mgr = ExportGcManager::new();
    mgr.record_export_with_session(cell(), fed_a(), 100, 10);
    // First drop is legitimate -> CanRevoke (count hits 0, holder removed).
    assert_eq!(
        mgr.process_drop_with_session(cell(), fed_a(), 10),
        DropResult::CanRevoke
    );
    // Second drop: holder gone -> Invalid (NOT an underflow panic, NOT a re-revoke).
    let r = mgr.process_drop_with_session(cell(), fed_a(), 10);
    assert_eq!(r, DropResult::Invalid);
    eprintln!("[GC ATTACK 4] over-drop: DEFENDED (no underflow)");
}

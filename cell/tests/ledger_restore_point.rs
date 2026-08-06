//! Restore-point rollback correctness.
//!
//! The commit path (`node/src/api.rs`) no longer clones the whole ledger before
//! executing a turn — it arms a per-turn undo journal and, on a rejected turn /
//! receipt-append failure, restores ONLY the touched cells. These tests pin the
//! load-bearing invariant that primitive must satisfy: a rolled-back turn leaves
//! the ledger BYTE-IDENTICAL to its pre-turn state (same root, same cells, the
//! newly-created cell gone, the removed cell back, the derived indices healed).
//! The pre-rollback assertions make the test NON-VACUOUS — the mutations really
//! landed, so the restore really does work.

use dregg_cell::{Cell, Ledger};

fn pk(n: u8) -> [u8; 32] {
    let mut a = [0u8; 32];
    a[0] = n;
    a
}
fn tok(n: u8) -> [u8; 32] {
    let mut a = [0u8; 32];
    a[31] = n;
    a
}

#[test]
fn rollback_restores_touched_cells_byte_identical() {
    let mut ledger = Ledger::new();
    let a = ledger
        .insert_cell(Cell::with_balance(pk(1), tok(1), 100))
        .unwrap();
    let b = ledger
        .insert_cell(Cell::with_balance(pk(2), tok(1), 50))
        .unwrap();
    let c = ledger
        .insert_cell(Cell::with_balance(pk(3), tok(1), 7))
        .unwrap();

    // Pre-turn snapshot: the root (materializes the lazy tree) + per-cell state.
    let root0 = ledger.root();
    let a0 = ledger.get(&a).cloned().unwrap();
    let b0 = ledger.get(&b).cloned().unwrap();
    let c0 = ledger.get(&c).cloned().unwrap();
    let len0 = ledger.len();

    // Arm the journal, then perform the mix a real turn can: an update (get_mut),
    // a structural removal, a creation, and a repeated touch (idempotent journal).
    ledger.begin_restore_point();
    assert!(ledger.has_restore_point());
    ledger.get_mut(&a).unwrap().state.set_balance(999);
    assert!(ledger.remove(&c).is_some());
    let d = ledger
        .insert_cell(Cell::with_balance(pk(4), tok(1), 1))
        .unwrap();
    ledger.get_mut(&b).unwrap().state.set_balance(0);
    ledger.get_mut(&b).unwrap().state.set_balance(123);

    // NON-VACUOUS: the ledger visibly changed before we roll back.
    assert_ne!(
        ledger.root(),
        root0,
        "the mutations must move the root pre-rollback"
    );
    assert_eq!(ledger.get(&a).unwrap().state.balance(), 999);
    assert_eq!(ledger.get(&b).unwrap().state.balance(), 123);
    assert!(ledger.get(&c).is_none());
    assert!(ledger.get(&d).is_some());
    assert_eq!(ledger.len(), len0, "one removed (c), one created (d)");

    // Reject the turn.
    ledger.rollback_restore_point();

    // Byte-identical to the pre-turn state.
    assert_eq!(
        ledger.root(),
        root0,
        "root must return to its pre-turn value"
    );
    assert_eq!(ledger.len(), len0);
    assert_eq!(ledger.get(&a).cloned().unwrap(), a0);
    assert_eq!(ledger.get(&b).cloned().unwrap(), b0);
    assert_eq!(ledger.get(&c).cloned().unwrap(), c0);
    assert!(
        ledger.get(&d).is_none(),
        "a turn-created cell must be gone on rollback"
    );
    assert!(!ledger.has_restore_point());

    // Derived pubkey index self-heals through the restore.
    assert!(
        ledger.cell_by_pubkey(&pk(4)).is_none(),
        "created cell's pubkey unresolvable"
    );
    assert_eq!(
        ledger.cell_by_pubkey(&pk(3)).map(|x| x.id()),
        Some(c),
        "removed cell resolvable again"
    );
}

#[test]
fn commit_keeps_mutations_and_drops_journal() {
    let mut ledger = Ledger::new();
    let a = ledger
        .insert_cell(Cell::with_balance(pk(1), tok(1), 100))
        .unwrap();
    let root0 = ledger.root();

    ledger.begin_restore_point();
    ledger.get_mut(&a).unwrap().state.set_balance(5);
    ledger.commit_restore_point();

    assert!(!ledger.has_restore_point());
    assert_ne!(ledger.root(), root0, "a committed turn keeps its mutations");
    assert_eq!(ledger.get(&a).unwrap().state.balance(), 5);
}

/// RE-ARMING WHILE ARMED MUST NOT PROMOTE THE STRANDED MUTATION.
///
/// A journal is only still armed at arm time when the turn that armed it never
/// resolved — which, given every caller arms/executes/resolves inside one held
/// write lock and there is no `CatchPanicLayer` in the tree, means an unwind. The
/// old behaviour (`self.restore_point = Some(..)` over the top) DISCARDED the
/// journal, so the half-applied turn's writes silently became the base state the
/// next turn built on. This test is that half-applied turn: it mutates, never
/// resolves, and then a second turn arms.
///
/// The canary: delete the rollback in `begin_restore_point` and this goes red on
/// a balance of 999 — the abandoned turn's write, adopted as authoritative.
#[test]
fn re_arming_rolls_back_an_unresolved_journal_instead_of_adopting_it() {
    let mut ledger = Ledger::new();
    let a = ledger
        .insert_cell(Cell::with_balance(pk(1), tok(1), 100))
        .unwrap();
    let root0 = ledger.root();

    // Turn 1: arms, mutates, creates a cell — and then never resolves.
    ledger.begin_restore_point();
    ledger.get_mut(&a).unwrap().state.set_balance(999);
    let orphan = ledger
        .insert_cell(Cell::with_balance(pk(8), tok(1), 42))
        .unwrap();
    // NON-VACUOUS: the abandoned turn really did land its writes.
    assert_eq!(ledger.get(&a).unwrap().state.balance(), 999);
    assert!(ledger.get(&orphan).is_some());

    // Turn 2 arms on the same ledger.
    ledger.begin_restore_point();

    assert_eq!(
        ledger.get(&a).unwrap().state.balance(),
        100,
        "the unresolved turn's write must be rolled back, not adopted"
    );
    assert!(
        ledger.get(&orphan).is_none(),
        "the unresolved turn's created cell must be gone, not inherited"
    );

    // And turn 2's own journal is armed and intact over the RESTORED base.
    assert!(ledger.has_restore_point());
    ledger.get_mut(&a).unwrap().state.set_balance(7);
    ledger.rollback_restore_point();
    assert_eq!(
        ledger.root(),
        root0,
        "rolling turn 2 back returns to the pre-turn-1 root — the stranded \
         mutation never entered the base state"
    );
}

#[test]
fn pre_turn_touched_ledger_exposes_prior_images_only_for_touched() {
    let mut ledger = Ledger::new();
    let a = ledger
        .insert_cell(Cell::with_balance(pk(1), tok(1), 100))
        .unwrap();
    let untouched = ledger
        .insert_cell(Cell::with_balance(pk(9), tok(1), 3))
        .unwrap();

    ledger.begin_restore_point();
    ledger.get_mut(&a).unwrap().state.set_balance(999);

    let pre = ledger.pre_turn_touched_ledger();
    // The touched cell's PRIOR image (100), not the live mutated value (999).
    assert_eq!(pre.get(&a).unwrap().state.balance(), 100);
    // Untouched cells never enter the minimal pre-image ledger.
    assert!(pre.get(&untouched).is_none());

    ledger.commit_restore_point();
}

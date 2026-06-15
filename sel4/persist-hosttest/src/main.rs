//! Host witness for the persist-PD's durable verified commit-log + the Tier-C
//! chain gate — the deos spine ("reads are free SQL, writes are verified turns,
//! durable") realized by the seL4 executor-PD / persist-PD PAIR.
//!
//! WHY A SEPARATE HOST CRATE (same reason as `sel4/crypto-floor-hosttest/`). The
//! persist PD is a `no_std` Microkit ELF whose load-bearing artifact runs on
//! aarch64 under `qemu-system-aarch64` in the 5-PD assembly. On a macOS host there
//! is **no user-mode `qemu-aarch64`** to run a PD's logic in isolation (only
//! `qemu-system-aarch64` for the full image boot). So this sibling crate INCLUDES
//! the SAME `commit_store` module the persist PD will carry (via `#[path]`) and
//! drives the executor→persist→read spine as a normal host binary + `#[test]`s — a
//! real, runnable witness on a box with no user-mode qemu-aarch64.
//!
//! WHAT IT PROVES (the deos spine, end to end):
//!   1. the "executor" produces a verified turn stamped with the (ordinal,
//!      prev_root) the store hands it (the producer contract,
//!      `pg-dregg/src/drainer.rs`'s `producer.produce(intent, ordinal, prev)`);
//!   2. the persist store COMMITS it — the `n = 1` synchronous commit, one
//!      transaction, cursor advanced, head moved (FIRMAMENT §3);
//!   3. a READ returns it — `lookup_by_ordinal` / `_by_turn_hash` / `_by_receipt_hash`
//!      (reads are free; the spine);
//!   4. turn N+1 CHAINS onto N (`prev_root == prior ledger_root`) and commits;
//!   5. the ANTI-SUBSTITUTION TEETH all bite: a wrong-`prev_root` turn is REFUSED
//!      (RootMismatch), an out-of-order turn is REFUSED (OrdinalGap / gap), a
//!      replay of a committed turn is an idempotent no-op, a different turn at a
//!      taken ordinal is REFUSED (Integrity).
//!
//! This is byte-for-byte the gate logic the seL4 persist PD runs and the EXACT
//! discipline the live pg-dregg + persist stack enforces (the chain gate is
//! `mirror::RootChain::extend`/`verify_chain_step`; the append is
//! `commit_finalized_turn_with_burns`). The in-qemu boot of the executor-PD /
//! persist-PD pair committing a turn over the `commit_out` channel is the named
//! wall (the macOS on-device checkpoint), exactly as the crypto floor's on-device
//! selftest-ELF run is — host-test here is the runnable witness.

#[path = "commit_store.rs"]
mod commit_store;

use commit_store::{ChainRefusal, CommitRecord, CommitStore, GENESIS_ROOT};

/// A faithful tiny stand-in for the executor PD's producer side. The REAL
/// executor is the verified Lean `execFullForestG` (`dregg_exec_full_forest_auth`)
/// — blocked on the §2 Lean ELF port for the bare target, refuted-and-booting per
/// `docs/EMBEDDABLE-LEAN-RUNTIME.md`. What the producer CONTRACT is, though, is
/// fixed (`pg-dregg/src/drainer.rs`): it receives `(ordinal, prev_root)` from the
/// chain head and stamps them onto the turn it returns; a stale or forged producer
/// is caught at the persist store's chain gate. This stand-in models exactly that
/// contract — it does NOT model the executor's verified compute (that is the
/// verifier-stark PD's / the embeddable-runtime lane's job), only the commit-record
/// shape the persist PD durably stores.
struct ProducerStub {
    creator: [u8; 32],
}

impl ProducerStub {
    /// Produce a verified-turn commit record for a transfer, stamped with the
    /// `(ordinal, prev_root)` the store handed us. `ledger_root` is a deterministic
    /// post-state digest stand-in (the executor's real post-state root on-device);
    /// here it just must be a stable function of the turn so the chain is testable.
    fn produce(&self, turn_id: u64, ordinal: u64, prev_root: [u8; 32]) -> CommitRecord {
        let turn_hash = digest32(0x01, turn_id, &prev_root);
        let receipt_hash = digest32(0x02, turn_id, &prev_root);
        // post-state root deterministically derived from (prev_root, turn) — stands
        // in for the executor's verified ledger fold.
        let ledger_root = digest32(0x03, turn_id, &prev_root);
        CommitRecord {
            ordinal,
            height: ordinal, // one turn per height in this witness
            block_id: digest32(0x04, turn_id, &prev_root),
            turn_hash,
            creator: self.creator,
            receipt_hash,
            prev_root,
            ledger_root,
            touched_cells: alloc_touched(turn_id),
        }
    }
}

/// A tiny deterministic 32-byte digest stand-in (NOT a cryptographic hash — the
/// real persist PD stores the executor's real `turn_hash`/`ledger_root`; this just
/// needs to be a stable, distinct function of its inputs so the chain + the indices
/// are exercisable in the host witness).
fn digest32(tag: u8, turn_id: u64, prev: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut acc = 0x9e37_79b9_7f4a_7c15u64 ^ ((tag as u64) << 56) ^ turn_id;
    for (i, b) in prev.iter().enumerate() {
        acc = acc
            .rotate_left(7)
            .wrapping_add(*b as u64)
            .wrapping_mul(0x0100_0000_01b3)
            ^ (i as u64);
    }
    for (i, slot) in out.iter_mut().enumerate() {
        acc = acc.rotate_left(11).wrapping_add(i as u64).wrapping_mul(0x0100_0000_01b3);
        *slot = (acc >> ((i % 8) * 8)) as u8;
    }
    out
}

fn alloc_touched(turn_id: u64) -> Vec<u8> {
    // opaque post-image bytes; the store does not interpret them.
    turn_id.to_le_bytes().to_vec()
}

use std::vec::Vec;

fn main() {
    println!("== persist-PD durable commit-log + Tier-C chain gate — host witness ==");
    println!("   (the deos spine: executor commits a verified turn -> persist stores it ->");
    println!("    a read returns it; a non-chaining / out-of-order / replayed turn is gated)\n");

    let producer = ProducerStub { creator: [0xA1; 32] };
    let mut store = CommitStore::new();

    // ---- the spine, end to end ------------------------------------------------

    // turn 0 — genesis. The store hands the producer (ordinal=0, prev=GENESIS_ROOT).
    let ord0 = store.commit_cursor();
    let prev0 = store.head_root().unwrap_or(GENESIS_ROOT);
    let turn0 = producer.produce(7000, ord0, prev0);
    let root0 = turn0.ledger_root;
    let a0 = store
        .commit_verified_turn(&turn0)
        .expect("genesis turn commits");
    println!("  [1] executor produced turn 7000 (ordinal {ord0}, prev=GENESIS); persist committed at ordinal {a0}");
    println!("      cursor now {} ; head -> {}", store.commit_cursor(), hexshort(&store.head_root().unwrap()));

    // READ it back three ways — reads are free.
    let by_ord = store.lookup_by_ordinal(a0).expect("read by ordinal");
    let by_th = store.lookup_by_turn_hash(&turn0.turn_hash).expect("read by turn_hash");
    let by_rh = store.lookup_by_receipt_hash(&turn0.receipt_hash).expect("read by receipt_hash");
    assert_eq!(by_ord, &turn0);
    assert_eq!(by_th, &turn0);
    assert_eq!(by_rh, &turn0);
    println!("  [2] read returns the committed turn (by ordinal / by turn_hash / by receipt_hash all agree)");

    // turn 1 — CHAINS onto turn 0: the store hands (ordinal=1, prev=root0).
    let ord1 = store.commit_cursor();
    let prev1 = store.head_root().unwrap();
    assert_eq!(prev1, root0, "the head IS turn 0's ledger_root (the chain)");
    let turn1 = producer.produce(7001, ord1, prev1);
    let root1 = turn1.ledger_root;
    let a1 = store.commit_verified_turn(&turn1).expect("turn 1 chains and commits");
    println!("  [3] turn 7001 chains onto turn 7000 (prev_root == prior ledger_root); committed at ordinal {a1}");
    println!("      cursor now {} ; head -> {}", store.commit_cursor(), hexshort(&store.head_root().unwrap()));

    // a light client walks the log and re-checks the root chain — the
    // self-checking projection (§10): prev_root[N+1] == ledger_root[N].
    let walk_ok = chain_is_intact(&store);
    println!("  [4] light-client walk re-checks the on-store root chain -> {}", if walk_ok { "INTACT" } else { "BROKEN" });
    assert!(walk_ok, "the committed log must form an intact hash chain");

    // ---- the anti-substitution teeth all bite ---------------------------------
    println!("\n== anti-substitution teeth (the chain gate is the persist PD's sole door) ==");

    // TOOTH 1 — a turn that does NOT chain (wrong prev_root) is REFUSED.
    let ord2 = store.commit_cursor();
    let mut forged = producer.produce(7002, ord2, [0xFF; 32]); // prev_root NOT the head
    forged.prev_root = [0xFF; 32];
    let r = store.commit_verified_turn(&forged);
    println!("  admit(turn w/ wrong prev_root)   -> {}", verdict(&r));
    assert!(matches!(r, Err(ChainRefusal::RootMismatch { .. })), "wrong prev_root must REFUSE");
    assert_eq!(store.commit_cursor(), ord2, "head/cursor must NOT move on a refusal");

    // TOOTH 2 — an OUT-OF-ORDER turn (ordinal gap) is REFUSED.
    let prev_now = store.head_root().unwrap();
    let mut gapped = producer.produce(7003, ord2 + 5, prev_now); // ordinal jumps ahead
    gapped.ordinal = ord2 + 5;
    let r = store.commit_verified_turn(&gapped);
    println!("  admit(turn w/ ordinal gap)       -> {}", verdict(&r));
    assert!(r.is_err(), "an ordinal gap must REFUSE (no holes in the log)");
    assert_eq!(store.commit_cursor(), ord2, "cursor must NOT move on a refusal");

    // TOOTH 3 — REPLAY of an already-committed turn is an idempotent NO-OP.
    let replay = store.commit_verified_turn(&turn0);
    println!("  admit(replay of committed turn0) -> {} (idempotent)", verdict(&replay));
    assert_eq!(replay, Ok(0), "replaying turn 0 returns its ordinal, no-op");
    assert_eq!(store.commit_cursor(), ord2, "a replay must NOT advance the cursor");

    // TOOTH 4 — a DIFFERENT turn at an already-taken ordinal is REFUSED (Integrity).
    let mut collision = producer.produce(9999, 0, GENESIS_ROOT); // ordinal 0, but a different turn
    collision.ordinal = 0;
    let r = store.commit_verified_turn(&collision);
    println!("  admit(different turn @ ordinal0) -> {}", verdict(&r));
    assert!(matches!(r, Err(ChainRefusal::Integrity(_))), "a collision at a taken ordinal must REFUSE");

    // the store is still exactly the two good turns — nothing forged slipped in.
    assert_eq!(store.commit_cursor(), 2, "exactly two turns committed");
    assert!(chain_is_intact(&store), "the chain is still intact after all refusals");
    println!("\n  store holds exactly {} committed turns; chain intact; no forged state admitted", store.commit_cursor());

    // ---- a persist-PD RESTART resumes from the durable head -------------------
    let resumed = CommitStore::resume(store.head_root(), store.commit_cursor());
    println!("  [5] persist-PD restart resumes at cursor {} head {} (no turn lost)",
        resumed.commit_cursor(), hexshort(&resumed.head_root().unwrap()));
    assert_eq!(resumed.commit_cursor(), 2);
    assert_eq!(resumed.head_root(), Some(root1));

    println!("\n== deos spine GREEN: a verified turn commits durably, a read returns it,");
    println!("== and the chain gate refuses every non-chaining / out-of-order / forged turn ( ◕‿◕ ) ==");
}

/// Walk the committed log in order and re-check `prev_root[N+1] == ledger_root[N]`
/// — the self-checking projection a light client performs (§10). genesis (ordinal
/// 0) must carry `prev_root == GENESIS_ROOT`.
fn chain_is_intact(store: &CommitStore) -> bool {
    let mut prev_ledger: Option<[u8; 32]> = None;
    for (ord, rec) in store.iter_ordered() {
        let expected_prev = prev_ledger.unwrap_or(GENESIS_ROOT);
        if rec.prev_root != expected_prev {
            return false;
        }
        if rec.ordinal != *ord {
            return false;
        }
        prev_ledger = Some(rec.ledger_root);
    }
    true
}

fn verdict(r: &Result<u64, ChainRefusal>) -> String {
    match r {
        Ok(ord) => format!("ADMIT (ordinal {ord})"),
        Err(e) => format!("REFUSE ({})", e.reason()),
    }
}

fn hexshort(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(8);
    for byte in b.iter().take(4) {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use commit_store::verify_chain_step;

    fn producer() -> ProducerStub {
        ProducerStub { creator: [0xA1; 32] }
    }

    /// The spine: a verified turn commits durably and a read returns it.
    #[test]
    fn commit_then_read_returns_the_turn() {
        let p = producer();
        let mut s = CommitStore::new();
        let t = p.produce(1, s.commit_cursor(), s.head_root().unwrap_or(GENESIS_ROOT));
        let ord = s.commit_verified_turn(&t).expect("commits");
        assert_eq!(ord, 0);
        assert_eq!(s.commit_cursor(), 1);
        assert_eq!(s.lookup_by_ordinal(0), Some(&t));
        assert_eq!(s.lookup_by_turn_hash(&t.turn_hash), Some(&t));
        assert_eq!(s.lookup_by_receipt_hash(&t.receipt_hash), Some(&t));
    }

    /// Turn N+1 chains onto N; the head IS N's ledger_root.
    #[test]
    fn turns_chain_through_the_head() {
        let p = producer();
        let mut s = CommitStore::new();
        let t0 = p.produce(1, 0, GENESIS_ROOT);
        s.commit_verified_turn(&t0).unwrap();
        let t1 = p.produce(2, s.commit_cursor(), s.head_root().unwrap());
        assert_eq!(t1.prev_root, t0.ledger_root, "prev_root == prior ledger_root");
        s.commit_verified_turn(&t1).unwrap();
        assert_eq!(s.commit_cursor(), 2);
        assert_eq!(s.head_root(), Some(t1.ledger_root));
        assert!(chain_is_intact(&s));
    }

    /// The anti-substitution tooth: a wrong-prev_root turn is REFUSED and the head
    /// does not move.
    #[test]
    fn wrong_prev_root_is_refused_root_mismatch() {
        let p = producer();
        let mut s = CommitStore::new();
        s.commit_verified_turn(&p.produce(1, 0, GENESIS_ROOT)).unwrap();
        let mut forged = p.produce(2, 1, [0xEE; 32]);
        forged.prev_root = [0xEE; 32];
        let r = s.commit_verified_turn(&forged);
        assert!(matches!(r, Err(ChainRefusal::RootMismatch { .. })));
        assert_eq!(s.commit_cursor(), 1, "cursor unmoved on refusal");
    }

    /// An ordinal gap is refused (no holes in the log).
    #[test]
    fn ordinal_gap_is_refused() {
        let p = producer();
        let mut s = CommitStore::new();
        s.commit_verified_turn(&p.produce(1, 0, GENESIS_ROOT)).unwrap();
        let mut gapped = p.produce(2, 9, s.head_root().unwrap());
        gapped.ordinal = 9;
        let r = s.commit_verified_turn(&gapped);
        assert!(r.is_err(), "gap refused");
        assert_eq!(s.commit_cursor(), 1);
    }

    /// Replaying an already-committed turn is an idempotent no-op success; a
    /// different turn at a taken ordinal is an Integrity refusal.
    #[test]
    fn replay_is_idempotent_collision_is_refused() {
        let p = producer();
        let mut s = CommitStore::new();
        let t0 = p.produce(1, 0, GENESIS_ROOT);
        s.commit_verified_turn(&t0).unwrap();
        s.commit_verified_turn(&p.produce(2, 1, s.head_root().unwrap())).unwrap();

        // replay turn0 -> no-op success, cursor unchanged.
        assert_eq!(s.commit_verified_turn(&t0), Ok(0));
        assert_eq!(s.commit_cursor(), 2);

        // a DIFFERENT turn claiming ordinal 0 -> Integrity refusal.
        let mut collision = p.produce(999, 0, GENESIS_ROOT);
        collision.ordinal = 0;
        assert!(matches!(
            s.commit_verified_turn(&collision),
            Err(ChainRefusal::Integrity(_))
        ));
        assert_eq!(s.commit_cursor(), 2);
    }

    /// A persist-PD restart resumes from the durable head + cursor, losing nothing.
    #[test]
    fn restart_resumes_from_durable_head() {
        let p = producer();
        let mut s = CommitStore::new();
        s.commit_verified_turn(&p.produce(1, 0, GENESIS_ROOT)).unwrap();
        let t1 = p.produce(2, 1, s.head_root().unwrap());
        s.commit_verified_turn(&t1).unwrap();

        let resumed = CommitStore::resume(s.head_root(), s.commit_cursor());
        assert_eq!(resumed.commit_cursor(), 2);
        assert_eq!(resumed.head_root(), Some(t1.ledger_root));

        // and the resumed store enforces the chain from the durable head.
        let mut resumed = resumed;
        let t2 = p.produce(3, resumed.commit_cursor(), resumed.head_root().unwrap());
        assert_eq!(t2.prev_root, t1.ledger_root);
        assert_eq!(resumed.commit_verified_turn(&t2), Ok(2));
    }

    /// `verify_chain_step` is exercisable in isolation (the pure gate lifted into
    /// SQL as `dregg_verify_turn`).
    #[test]
    fn pure_chain_step_gate() {
        // genesis: head None, ordinal 0, any prev passes the root check but the
        // ordinal must be 0.
        assert!(verify_chain_step(None, 0, GENESIS_ROOT, 0).is_ok());
        assert!(verify_chain_step(None, 0, GENESIS_ROOT, 1).is_err()); // wrong ordinal
        // non-genesis: prev must equal head.
        let head = [0x11; 32];
        assert!(verify_chain_step(Some(head), 5, head, 5).is_ok());
        assert!(matches!(
            verify_chain_step(Some(head), 5, [0x22; 32], 5),
            Err(ChainRefusal::RootMismatch { .. })
        ));
        assert!(matches!(
            verify_chain_step(Some(head), 5, head, 6),
            Err(ChainRefusal::OrdinalGap { .. })
        ));
    }
}

//! The offchain-coordination substrate, proven end to end.
//!
//! These tests are the executable form of the architecture-critique's §5.4 ask:
//! two parties accumulate I-confluent deltas on their own cell copies with **no
//! coordination**, merge to a single confluent state (commutative, idempotent,
//! order-independent — no consensus, no chain op), a non-confluent op pair is
//! refused (must settle at the boundary), and the merge's commitment is
//! re-witnessable — including, end-to-end, over the read face's MMR.

use std::collections::BTreeSet;

use dregg_merge::delta::OpKind;
use dregg_merge::{
    BoundedCounter, Delta, Escalation, GrowSet, MergeRuntime, MergeState, receipt::Provenance,
};
use dregg_query::{Blake3Mmr, CoordinationClass, Mmr, verify_range};

/// Build party A's and party B's copies of one grow-only cell, each having
/// applied its own I-confluent deltas **offchain, with no coordination**.
fn two_divergent_copies() -> (GrowSet, GrowSet) {
    // both start from a shared base delta (content-addressed: identical => same
    // id on both sides — the union will deduplicate it, witnessing idempotence).
    let base = Delta::assert("ledger-cell", b"genesis".to_vec(), "founder");

    let mut a = GrowSet::new("ledger-cell");
    a.apply(base.clone());
    a.apply(Delta::assert("ledger-cell", b"a-fact-1".to_vec(), "alice"));
    a.apply(Delta::assert("ledger-cell", b"a-fact-2".to_vec(), "alice"));

    let mut b = GrowSet::new("ledger-cell");
    b.apply(base);
    b.apply(Delta::assert("ledger-cell", b"b-fact-1".to_vec(), "bob"));

    (a, b)
}

#[test]
fn two_parties_merge_offchain_with_no_consensus() {
    let (a, b) = two_divergent_copies();

    let mut rt = MergeRuntime::new("GrowSet", "alice");
    let out = rt
        .merge(&a, &b)
        .expect("grow-only merge is coordination-free");

    // the merged state holds every party's deltas (union), deduplicated.
    let survivors: BTreeSet<Vec<u8>> = out.state.survivors().map(|d| d.payload.clone()).collect();
    assert!(survivors.contains(b"genesis".as_slice()));
    assert!(survivors.contains(b"a-fact-1".as_slice()));
    assert!(survivors.contains(b"a-fact-2".as_slice()));
    assert!(survivors.contains(b"b-fact-1".as_slice()));
    // the shared base appears once (idempotent union), not twice.
    assert_eq!(out.state.asserted.len(), 4);

    // a free merge is monotone — no consensus, no chain op was needed.
    assert_eq!(out.receipt.class, CoordinationClass::Monotone);
    assert_eq!(out.receipt.cell, "ledger-cell");
}

#[test]
fn merge_is_commutative_idempotent_and_order_independent() {
    let (a, b) = two_divergent_copies();

    // commutativity: a ⊔ b == b ⊔ a (same merged commitment).
    let ab = a.join(&b);
    let ba = b.join(&a);
    assert_eq!(ab.commitment(), ba.commitment(), "join must be commutative");
    assert_eq!(ab, ba);

    // idempotence: x ⊔ x == x.
    assert_eq!(
        a.join(&a).commitment(),
        a.commitment(),
        "join must be idempotent"
    );

    // associativity / order-independence with a third copy c.
    let mut c = GrowSet::new("ledger-cell");
    c.apply(Delta::assert("ledger-cell", b"c-fact".to_vec(), "carol"));
    let left = a.join(&b).join(&c);
    let right = a.join(&b.join(&c));
    assert_eq!(
        left.commitment(),
        right.commitment(),
        "join must be associative"
    );

    // determinism: the FINAL merged state is identical regardless of the order
    // the three copies are merged in — the whole point of coordination-freedom.
    let orders = [
        a.join(&b).join(&c),
        a.join(&c).join(&b),
        b.join(&a).join(&c),
        b.join(&c).join(&a),
        c.join(&a).join(&b),
        c.join(&b).join(&a),
    ];
    let first = orders[0].commitment();
    for o in &orders {
        assert_eq!(
            o.commitment(),
            first,
            "merge order must not change the result"
        );
    }
}

#[test]
fn non_confluent_bounded_counter_is_refused_must_settle() {
    // The `balance >= 0` clash (Confluence.lean `nonpairwise_escalation`): a cell
    // funded with 1 unit; two replicas each debit 1 offchain. Each copy is
    // LOCALLY valid (balance 0). The gate must REFUSE the free merge.
    let mut a = BoundedCounter::new("wallet");
    a.credit("mint", 1);
    a.debit("alice", 1);
    assert!(a.invariant(), "A is locally valid (balance 0)");

    let mut b = BoundedCounter::new("wallet");
    b.credit("mint", 1); // same funding contribution (G-Counter dedup by max)
    b.debit("bob", 1);
    assert!(b.invariant(), "B is locally valid (balance 0)");

    let mut rt = MergeRuntime::new("BoundedCounter", "alice");
    match rt.merge(&a, &b) {
        Err(Escalation::NonIConfluentKind { .. }) => {}
        other => panic!("expected refusal to merge (must settle), got {other:?}"),
    }

    // and the refusal is JUSTIFIED: had we merged anyway, the invariant breaks
    // (balance -1) — the concrete clash that forces settlement at the boundary.
    let merged_anyway = a.join(&b);
    assert_eq!(merged_anyway.balance(), -1);
    assert!(
        !merged_anyway.invariant(),
        "the bypassed merge overdrafts — why the gate refuses"
    );
}

#[test]
fn retraction_is_refused_must_settle() {
    // A negation (the one non-monotone reason) flips a grow-only cell to
    // finalized-dependent — the merge must settle.
    let mut a = GrowSet::new("c");
    let id = a.apply(Delta::assert("c", b"x".to_vec(), "alice"));
    a.apply(Delta::retract("c", id, "alice"));
    assert_eq!(
        a.coordination_class(),
        CoordinationClass::FinalizedDependent
    );

    let mut b = GrowSet::new("c");
    b.apply(Delta::assert("c", b"y".to_vec(), "bob"));

    let mut rt = MergeRuntime::new("GrowSet", "alice");
    match rt.merge(&a, &b) {
        Err(Escalation::NonMonotoneOp) => {}
        other => panic!("expected NonMonotoneOp refusal, got {other:?}"),
    }
}

#[test]
fn merged_commitment_is_rewitnessable_by_a_third_party() {
    let (a, b) = two_divergent_copies();
    let mut rt = MergeRuntime::new("GrowSet", "alice");
    let out = rt.merge(&a, &b).unwrap();

    // a third party who holds the two inputs re-witnesses the merge — no chain.
    out.receipt
        .rewitness(&a, &b)
        .expect("genuine merge re-witnesses");

    // provenance is accurate: the shared base is `Both`, each party's own deltas
    // are `A` / `B`.
    let base_id = Delta::assert("ledger-cell", b"genesis".to_vec(), "founder").id();
    let a1_id = Delta::assert("ledger-cell", b"a-fact-1".to_vec(), "alice").id();
    let b1_id = Delta::assert("ledger-cell", b"b-fact-1".to_vec(), "bob").id();
    let prov = |id| {
        out.receipt
            .provenance
            .iter()
            .find(|p| p.delta == id)
            .map(|p| p.from)
    };
    assert_eq!(prov(base_id), Some(Provenance::Both));
    assert_eq!(prov(a1_id), Some(Provenance::A));
    assert_eq!(prov(b1_id), Some(Provenance::B));

    // tamper teeth: a forged input, a forged merged commitment, both reject.
    let mut tampered = a.clone();
    tampered.apply(Delta::assert(
        "ledger-cell",
        b"sneaked".to_vec(),
        "attacker",
    ));
    assert!(
        out.receipt.rewitness(&tampered, &b).is_err(),
        "a tampered input must reject"
    );

    let mut forged = out.receipt.clone();
    forged.merged[0] ^= 0xff;
    assert!(
        forged.rewitness(&a, &b).is_err(),
        "a forged merged commitment must reject"
    );
}

#[test]
fn merge_receipts_chain_and_are_mmr_certified_over_the_read_face() {
    // A whole offchain-coordination SESSION: a sequence of free merges, each
    // emitting a chained receipt. The receipt stream composes as MMR leaves
    // (dregg_query::mmr — the READ face), so the trace carries a non-omission
    // certificate WITHOUT a chain op per merge.
    let mut rt = MergeRuntime::new("GrowSet", "coordinator");
    let mut log: Mmr<Blake3Mmr> = Mmr::new(Blake3Mmr);

    let mut acc = GrowSet::new("session-cell");
    acc.apply(Delta::assert(
        "session-cell",
        b"seed".to_vec(),
        "coordinator",
    ));

    let mut prev = rt.head();
    for i in 0..8u8 {
        // a peer contributes a delta on its own copy, then merges it in.
        let mut peer = GrowSet::new("session-cell");
        peer.apply(Delta::assert("session-cell", vec![b'p', i], "peer"));

        let out = rt.merge(&acc, &peer).expect("each merge is confluent");
        // the receipt chains: its prev-hash is the previous receipt's hash.
        assert_eq!(
            out.receipt.prev_receipt_hash, prev,
            "receipts form a prev-hash chain"
        );
        prev = out.receipt.receipt_hash();

        // the receipt hash is the MMR leaf — the read face commits the trace.
        log.push(out.receipt.receipt_hash());
        acc = out.state;
    }

    // the read face certifies the whole coordination trace: a verifier with only
    // the committed root accepts EXACTLY the genuine receipt range — no omission,
    // no forgery, no reorder (server_cannot_omit_position).
    let root = log.root();
    let (values, opening) = log.open_range(0, log.len() - 1);
    let len = verify_range(&Blake3Mmr, &root, 0, log.len() - 1, &values, &opening)
        .expect("the merge-receipt trace is non-omission-certified by the read face");
    assert_eq!(len, 8, "all eight merge receipts are in the certified log");
}

#[test]
fn would_merge_previews_the_gate_without_acting() {
    let (a, b) = two_divergent_copies();
    let rt = MergeRuntime::new("GrowSet", "alice");
    assert!(rt.would_merge(&a, &b).is_free());
    // previewing did not advance the chain head.
    assert_eq!(rt.head(), dregg_merge::runtime::GENESIS);
}

#[test]
fn delta_op_kinds_round_trip() {
    // a small guard that the OpKind tag the gate reads is what apply records.
    let mut g = GrowSet::new("c");
    let id = g.apply(Delta::assert("c", b"v".to_vec(), "a"));
    assert_eq!(g.asserted.get(&id).unwrap().kind, OpKind::Assert);
    let rid = g.apply(Delta::retract("c", id, "a"));
    assert_eq!(g.asserted.get(&rid).unwrap().kind, OpKind::Retract);
    assert!(g.negated.contains(&id));
}

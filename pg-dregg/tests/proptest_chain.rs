//! Property / fuzz tests for the `RootChain` anti-substitution discipline — the
//! spine invariant's load-bearing tooth (`docs/PG-DREGG.md` §10, §15). These
//! properties try to break the chain gate: accept a substituted root, accept a
//! gap/reorder, move the head on a refusal, or disagree between `RootChain::extend`
//! and the `revalidate_replicated_chain` subscriber sweep.
//!
//! Run: `cargo test --test proptest_chain`

use pg_dregg::mirror::{
    revalidate_replicated_chain, verify_chain_step, CellRow, ChainLink, ChainRefusal, Domain,
    MemCell, MirrorBatch, RootChain, TurnRow,
};
use proptest::prelude::*;

// ---- a faithful synthetic chain builder (the roots fold deterministically, so a
//      valid chain always links; same shape as src/synth.rs) -------------------

fn fold_root(prev: [u8; 32], ordinal: u64, balance: i64) -> [u8; 32] {
    let mut acc: u64 = 0xcbf29ce484222325 ^ ordinal.wrapping_mul(0x100000001b3);
    for b in prev {
        acc = (acc ^ b as u64).wrapping_mul(0x100000001b3);
    }
    acc = (acc ^ balance as u64).wrapping_mul(0x100000001b3);
    let mut out = [0u8; 32];
    for (i, chunk) in out.chunks_mut(8).enumerate() {
        let v = acc.wrapping_add((i as u64).wrapping_mul(0x9e3779b97f4a7c15));
        chunk.copy_from_slice(&v.to_le_bytes());
    }
    out
}

const GENESIS: [u8; 32] = [0u8; 32];

/// Build a well-formed chain of `n` batches from genesis, each touching one cell
/// with a per-turn balance. The roots fold so batch n+1's prev_root == batch n's
/// ledger_root by construction.
fn well_formed_chain(n: u64, balances: &[i64]) -> Vec<MirrorBatch> {
    let mut out = Vec::new();
    let mut prev = GENESIS;
    let id = {
        let mut x = [0x11u8; 32];
        x[0] = 0xab;
        x
    };
    for ord in 0..n {
        let bal = balances.get(ord as usize).copied().unwrap_or(0);
        let post = fold_root(prev, ord, bal);
        let cell = CellRow {
            cell_id: id,
            mode: "Hosted".into(),
            balance: bal,
            nonce: ord,
            fields: vec![],
            fields_json: None,
            heap: None,
            program: None,
            verification_key: None,
            permissions_json: None,
            delegate: None,
            lifecycle: "Active".into(),
            last_ordinal: ord,
            cell_root: id,
        };
        let mem = MemCell {
            domain: Domain::Registers,
            collection: id.to_vec(),
            key: b"balance".to_vec(),
            value: Some(bal.to_le_bytes().to_vec()),
            last_ordinal: ord,
        };
        let turn = TurnRow {
            ordinal: ord,
            height: ord,
            block_id: [0u8; 32],
            block_executed_up_to: ord,
            turn_hash: [0u8; 32],
            creator: id,
            receipt_hash: [0u8; 32],
            ledger_root: post,
            prev_root: prev,
        };
        out.push(MirrorBatch::from_parts(turn, vec![cell], vec![], vec![mem]).unwrap());
        prev = post;
    }
    out
}

fn links_of(chain: &[MirrorBatch]) -> Vec<ChainLink> {
    chain
        .iter()
        .map(|b| ChainLink {
            ordinal: b.turn.ordinal,
            prev_root: b.turn.prev_root,
            ledger_root: b.turn.ledger_root,
        })
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 512, ..ProptestConfig::default() })]

    /// A well-formed chain from genesis ALWAYS fully accepts, and the head ends at
    /// the last batch's ledger_root.
    #[test]
    fn well_formed_chain_always_accepts(balances in prop::collection::vec(0i64..1_000_000, 1..20)) {
        let n = balances.len() as u64;
        let chain = well_formed_chain(n, &balances);
        let mut rc = RootChain::resume(GENESIS, 0);
        for b in &chain {
            prop_assert!(rc.extend(b).is_ok(), "a well-formed batch was refused");
        }
        prop_assert_eq!(rc.next_ordinal(), n);
        prop_assert_eq!(rc.head(), Some(chain.last().unwrap().turn.ledger_root));
    }

    /// SUBSTITUTING any non-genesis batch's prev_root to a wrong value is REFUSED,
    /// and the head does NOT move on the refusal. (The core anti-substitution
    /// property — turn N's ledger_root must be turn N+1's prev_root.)
    #[test]
    fn substituting_a_prev_root_is_refused(
        balances in prop::collection::vec(0i64..1_000_000, 3..12),
        sub in any::<[u8;32]>(),
    ) {
        let n = balances.len() as u64;
        let chain = well_formed_chain(n, &balances);
        // Run cleanly up to ordinal 1, then offer a tampered ordinal-2 batch.
        let mut rc = RootChain::resume(GENESIS, 0);
        rc.extend(&chain[0]).unwrap();
        rc.extend(&chain[1]).unwrap();
        let head_before = rc.head();
        let next_before = rc.next_ordinal();

        let mut tampered = chain[2].clone();
        prop_assume!(sub != head_before.unwrap()); // the substitution must actually differ
        tampered.turn.prev_root = sub;

        match rc.extend(&tampered) {
            Ok(()) => prop_assert!(false, "a substituted prev_root was accepted — SPINE BROKEN"),
            Err(ChainRefusal::RootMismatch { .. }) => {}
            Err(other) => prop_assert!(false, "expected RootMismatch, got {:?}", other),
        }
        // The head must be unchanged after a refusal.
        prop_assert_eq!(rc.head(), head_before);
        prop_assert_eq!(rc.next_ordinal(), next_before);
    }

    /// REORDERING / GAPPING (submitting a batch whose ordinal is not next-expected)
    /// is refused as an OrdinalGap, head unchanged.
    #[test]
    fn out_of_order_ordinal_is_refused(
        balances in prop::collection::vec(0i64..1_000_000, 4..12),
        skip_to in 2u64..50,
    ) {
        let n = balances.len() as u64;
        let chain = well_formed_chain(n, &balances);
        let mut rc = RootChain::resume(GENESIS, 0);
        rc.extend(&chain[0]).unwrap(); // now expects ordinal 1
        let head_before = rc.head();

        // Offer a batch claiming ordinal `skip_to` (>=2) instead of 1.
        prop_assume!(skip_to != 1);
        let mut jumped = chain[1].clone();
        jumped.turn.ordinal = skip_to;
        // re-stamp the rows so check_ordinals passes and the ORDINAL gate is what bites
        let jumped = MirrorBatch::from_parts(jumped.turn, jumped.cells, jumped.caps, jumped.memory).unwrap();

        match rc.extend(&jumped) {
            Err(ChainRefusal::OrdinalGap { expected, got }) => {
                prop_assert_eq!(expected, 1);
                prop_assert_eq!(got, skip_to);
            }
            Ok(()) => prop_assert!(false, "an out-of-order ordinal was accepted"),
            Err(other) => prop_assert!(false, "expected OrdinalGap, got {:?}", other),
        }
        prop_assert_eq!(rc.head(), head_before);
    }

    /// The subscriber sweep `revalidate_replicated_chain` agrees with a fresh
    /// `RootChain` walk: a well-formed chain re-validates to the same head.
    #[test]
    fn subscriber_sweep_agrees_with_rootchain(balances in prop::collection::vec(0i64..1_000_000, 1..20)) {
        let n = balances.len() as u64;
        let chain = well_formed_chain(n, &balances);
        let links = links_of(&chain);

        // Publisher's RootChain head.
        let mut rc = RootChain::resume(GENESIS, 0);
        for b in &chain { rc.extend(b).unwrap(); }

        // Subscriber's local re-validation, with the truncation guard.
        let head = revalidate_replicated_chain(GENESIS, &links, Some(n))
            .expect("a well-formed replicated chain must re-validate");
        prop_assert_eq!(head, rc.head(), "subscriber head must equal publisher head");
    }

    /// The subscriber sweep CATCHES a substituted root in the replicated stream
    /// (the §15 property: re-validate, do not trust). Substitute one link's
    /// prev_root and assert a refusal.
    #[test]
    fn subscriber_sweep_catches_substitution(
        balances in prop::collection::vec(0i64..1_000_000, 3..12),
        at in 1usize..3,
        sub in any::<[u8;32]>(),
    ) {
        let n = balances.len() as u64;
        let chain = well_formed_chain(n, &balances);
        let mut links = links_of(&chain);
        let idx = at.min(links.len() - 1);
        prop_assume!(sub != links[idx].prev_root); // must actually differ
        links[idx].prev_root = sub;

        prop_assert!(
            revalidate_replicated_chain(GENESIS, &links, Some(n)).is_err(),
            "a substituted replicated root must be refused"
        );
    }

    /// The subscriber sweep CATCHES a TRUNCATED stream (fewer links than the
    /// published count) via the expect_count guard — a tail truncation the
    /// per-link chaining alone would not notice.
    #[test]
    fn subscriber_sweep_catches_truncation(balances in prop::collection::vec(0i64..1_000_000, 2..12)) {
        let n = balances.len() as u64;
        let chain = well_formed_chain(n, &balances);
        let mut links = links_of(&chain);
        links.pop(); // drop the tail — a truncation
        prop_assert!(
            revalidate_replicated_chain(GENESIS, &links, Some(n)).is_err(),
            "a truncated replicated stream must be refused by the count guard"
        );
    }

    /// `verify_chain_step` is the single source of truth and agrees with
    /// `RootChain::extend` on the accept decision for the FIRST step from a head.
    #[test]
    fn verify_chain_step_matches_extend(
        head in any::<[u8;32]>(),
        next in 0u64..1000,
        prev in any::<[u8;32]>(),
        ord in 0u64..1000,
    ) {
        // The pure step gate's verdict.
        let step_ok = verify_chain_step(Some(head), next, prev, ord).is_ok();
        // The same decision through RootChain (resume at `next` with `head`).
        let mut rc = RootChain::resume(head, next);
        // Build a minimal batch with the given ordinal/prev (post-root arbitrary).
        let id = [0x11u8; 32];
        let post = fold_root(prev, ord, 0);
        let turn = TurnRow {
            ordinal: ord, height: ord, block_id: [0u8;32], block_executed_up_to: ord,
            turn_hash: [0u8;32], creator: id, receipt_hash: [0u8;32],
            ledger_root: post, prev_root: prev,
        };
        let batch = MirrorBatch::from_parts(turn, vec![], vec![], vec![]).unwrap();
        let extend_ok = rc.extend(&batch).is_ok();
        prop_assert_eq!(step_ok, extend_ok, "the pure step gate must agree with extend");
    }
}

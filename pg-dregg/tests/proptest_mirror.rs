//! Property / fuzz tests for the `MirrorBatch` serde codec and the well-formedness
//! gate. The node ships a `MirrorBatch` over the wire (Tier B1); the pg side / the
//! recovery path decodes it. These properties hammer that boundary with arbitrary
//! inputs to find a decode that panics, a round-trip that loses data, or a gate
//! that admits a malformed batch.
//!
//! Run: `cargo test --test proptest_mirror`

use pg_dregg::mirror::{CapRow, CellRow, Domain, MemCell, MirrorBatch, TurnRow};
use proptest::prelude::*;

// ---- generators -----------------------------------------------------------

fn arb_root() -> impl Strategy<Value = [u8; 32]> {
    any::<[u8; 32]>()
}

prop_compose! {
    fn arb_cellrow()(
        cell_id in any::<[u8;32]>(),
        mode in "[A-Za-z]{0,8}",
        balance in any::<i64>(),
        nonce in any::<u64>(),
        fields in prop::collection::vec(any::<u8>(), 0..16),
        has_json in any::<bool>(),
        lifecycle in "[A-Za-z]{0,8}",
        cell_root in any::<[u8;32]>(),
        last_ordinal in any::<u64>(),
    ) -> CellRow {
        CellRow {
            cell_id, mode, balance, nonce, fields,
            // a VALID json object when present (the node only ever emits valid json)
            fields_json: if has_json { Some(format!("{{\"balance\":{balance}}}")) } else { None },
            heap: None, program: None, verification_key: None,
            permissions_json: None, delegate: None,
            lifecycle, last_ordinal, cell_root,
        }
    }
}

prop_compose! {
    fn arb_caprow()(
        holder in any::<[u8;32]>(),
        slot in any::<u32>(),
        target in any::<[u8;32]>(),
        expires in proptest::option::of(any::<u64>()),
        last_ordinal in any::<u64>(),
    ) -> CapRow {
        CapRow {
            holder, slot, target,
            permissions_json: "{}".into(),
            breadstuff: None,
            expires_at: expires,
            allowed_effects_json: None,
            stored_epoch: None,
            last_ordinal,
        }
    }
}

fn arb_domain() -> impl Strategy<Value = Domain> {
    prop_oneof![
        Just(Domain::Registers),
        Just(Domain::Heap),
        Just(Domain::Caps),
        Just(Domain::Nullifiers),
        Just(Domain::Index),
    ]
}

prop_compose! {
    fn arb_memcell()(
        domain in arb_domain(),
        collection in prop::collection::vec(any::<u8>(), 0..16),
        key in prop::collection::vec(any::<u8>(), 0..16),
        value in proptest::option::of(prop::collection::vec(any::<u8>(), 0..16)),
        last_ordinal in any::<u64>(),
    ) -> MemCell {
        MemCell { domain, collection, key, value, last_ordinal }
    }
}

prop_compose! {
    fn arb_turnrow()(
        ordinal in any::<u64>(),
        prev_root in arb_root(),
        ledger_root in arb_root(),
        creator in any::<[u8;32]>(),
    ) -> TurnRow {
        TurnRow {
            ordinal, height: ordinal,
            block_id: [0u8;32], block_executed_up_to: ordinal,
            turn_hash: [0u8;32], creator, receipt_hash: [0u8;32],
            ledger_root, prev_root,
        }
    }
}

prop_compose! {
    fn arb_batch()(
        turn in arb_turnrow(),
        cells in prop::collection::vec(arb_cellrow(), 0..6),
        caps in prop::collection::vec(arb_caprow(), 0..4),
        memory in prop::collection::vec(arb_memcell(), 0..6),
    ) -> MirrorBatch {
        MirrorBatch { turn, cells, caps, memory }
    }
}

// ---- properties -----------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig { cases: 512, ..ProptestConfig::default() })]

    /// The serde JSON round-trip is lossless for ANY well-formed batch: decode ∘
    /// encode == identity. (The node↔pg wire and the durable-log replay both rely
    /// on this.)
    #[test]
    fn batch_json_round_trips(batch in arb_batch()) {
        let bytes = serde_json::to_vec(&batch).expect("encode must not fail");
        let back: MirrorBatch = serde_json::from_slice(&bytes).expect("decode must not fail");
        prop_assert_eq!(batch, back);
    }

    /// Decoding ARBITRARY bytes never panics — it returns Err (fail-closed), not a
    /// crash. This is the real fuzz target: a hostile / corrupt wire payload must
    /// not be able to panic the decoder (which in a backend would abort the txn or
    /// worse).
    #[test]
    fn decoding_arbitrary_bytes_never_panics(bytes in prop::collection::vec(any::<u8>(), 0..512)) {
        // Must not panic. Ok or Err are both fine; a panic would fail the test.
        let _: Result<MirrorBatch, _> = serde_json::from_slice(&bytes);
    }

    /// Decoding arbitrary UTF-8 (more likely to reach deeper parser states than
    /// random bytes) never panics either.
    #[test]
    fn decoding_arbitrary_text_never_panics(s in ".{0,512}") {
        let _: Result<MirrorBatch, _> = serde_json::from_str(&s);
    }

    /// `from_parts` STAMPS every row with the turn's ordinal, so the resulting
    /// batch always passes `check_ordinals` regardless of what ordinals the caller
    /// put on the input rows. (The discipline that a node cannot ship a row stamped
    /// for a different turn.)
    #[test]
    fn from_parts_stamps_and_is_well_formed(
        turn in arb_turnrow(),
        cells in prop::collection::vec(arb_cellrow(), 0..6),
        caps in prop::collection::vec(arb_caprow(), 0..4),
        memory in prop::collection::vec(arb_memcell(), 0..6),
    ) {
        let o = turn.ordinal;
        let batch = MirrorBatch::from_parts(turn, cells, caps, memory)
            .expect("from_parts stamps, so it must always be well-formed");
        // Every row now carries the turn's ordinal.
        prop_assert!(batch.cells.iter().all(|c| c.last_ordinal == o));
        prop_assert!(batch.caps.iter().all(|c| c.last_ordinal == o));
        prop_assert!(batch.memory.iter().all(|m| m.last_ordinal == o));
        // And the well-formedness gate agrees.
        prop_assert!(batch.check_ordinals().is_ok());
    }

    /// `check_ordinals` REJECTS a batch with any row whose ordinal differs from the
    /// turn's (the anti-smuggling gate). We build a well-formed batch then corrupt
    /// one cell's ordinal and assert it is caught.
    #[test]
    fn check_ordinals_rejects_a_smuggled_row(
        turn in arb_turnrow(),
        cells in prop::collection::vec(arb_cellrow(), 1..6),
        bad in any::<u64>(),
    ) {
        let o = turn.ordinal;
        prop_assume!(bad != o); // the smuggled ordinal must actually differ
        let mut batch = MirrorBatch::from_parts(turn, cells, vec![], vec![]).unwrap();
        // Corrupt the first cell's ordinal to a different turn.
        batch.cells[0].last_ordinal = bad;
        prop_assert!(batch.check_ordinals().is_err(), "a row from a different turn must be rejected");
    }

    /// `cells_json` always produces VALID json that parses back to an array of the
    /// same length as the batch's cells (the Tier-C trigger payload must be
    /// parseable by the gate).
    #[test]
    fn cells_json_is_valid_and_complete(
        turn in arb_turnrow(),
        cells in prop::collection::vec(arb_cellrow(), 0..6),
    ) {
        let batch = MirrorBatch::from_parts(turn, cells, vec![], vec![]).unwrap();
        let json = batch.cells_json();
        let parsed: serde_json::Value = serde_json::from_str(&json)
            .expect("cells_json must be valid json");
        let arr = parsed.as_array().expect("cells_json must be a json array");
        prop_assert_eq!(arr.len(), batch.cells.len());
        // Every element carries the load-bearing keys the trigger reads.
        for el in arr {
            prop_assert!(el.get("cell_id").is_some());
            prop_assert!(el.get("balance").is_some());
            prop_assert!(el.get("cell_root").is_some());
        }
    }
}

/// Domain tag round-trips for every variant (the universal-memory address tag is
/// load-bearing — a wrong tag would alias domains).
#[test]
fn domain_tag_round_trips_for_every_variant() {
    for d in Domain::ALL {
        assert_eq!(Domain::from_tag(d.tag()), Some(d));
    }
    // An unknown tag fails closed.
    assert_eq!(Domain::from_tag("not-a-domain"), None);
    assert_eq!(Domain::from_tag(""), None);
}

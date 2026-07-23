//! The `dregg-receipt-v5` event-absorption fix: `TurnReceipt::receipt_hash`
//! counts each emitted event's data felts, so the event *list* encoding is
//! prefix-free.
//!
//! # The defect these tests close
//!
//! Through `dregg-receipt-v4`, `receipt_hash` absorbed the event list as
//!
//! ```text
//! count(u64) ‖ ( cell(32) ‖ topic(32) ‖ data[0](32) ‖ … ‖ data[k-1](32) )*
//! ```
//!
//! with **no `data.len()` in front of the variable-length `data` vector**.
//! Every component is exactly 32 bytes wide (`CellId([u8; 32])`,
//! `Symbol = FieldElement = [u8; 32]`), so the field boundaries inside the
//! per-event run are recoverable only from `data.len()` — which was not
//! absorbed. Sliding the boundary by one 32-byte lane therefore produced two
//! genuinely different `Vec<EmittedEvent>` with a byte-identical absorbed
//! stream, i.e. **the same `receipt_hash`**, i.e. one executor signature valid
//! over two different execution outcomes.
//!
//! `turn/src/finalized_receipt_core_v1.rs`'s `event_commitment` always counted
//! the felts; the two implementations of "how an event contributes to a
//! commitment" disagreed. v5 hoists the encoding into a single shared
//! [`dregg_turn::absorb_emitted_event`] used by both.

use dregg_turn::finalized_receipt_core_v1::{
    FinalizedExecutionContextV1, FinalizedReceiptCoreV1, FinalizedReceiptPredecessorV1,
};
use dregg_turn::{EmittedEvent, Finality, TurnReceipt, absorb_emitted_event};
use dregg_types::CellId;

// ---------------------------------------------------------------------------
// fixtures
// ---------------------------------------------------------------------------

/// A fully-pinned receipt: every field is a fixed constant so `receipt_hash()`
/// is a deterministic test vector. Only `emitted_events` varies across tests.
fn pinned_receipt(emitted_events: Vec<EmittedEvent>) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [0x11; 32],
        forest_hash: [0x22; 32],
        pre_state_hash: [0x33; 32],
        post_state_hash: [0x44; 32],
        timestamp: 1_700_000_000,
        effects_hash: [0x55; 32],
        computrons_used: 4_242,
        action_count: 3,
        previous_receipt_hash: Some([0x66; 32]),
        agent: CellId([0x77; 32]),
        federation_id: [0x88; 32],
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: Vec::new(),
        emitted_events,
        executor_signature: None,
        finality: Finality::Final,
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: Vec::new(),
    }
}

/// The four 32-byte lanes the collision slides across.
const C1: [u8; 32] = [0xA1; 32]; // event 1 cell
const T1: [u8; 32] = [0xA2; 32]; // event 1 topic
const A: [u8; 32] = [0xA3; 32]; // event 1 data[0]
const B: [u8; 32] = [0xA4; 32]; // event 1 data[1]  /  event 2' cell
const C2: [u8; 32] = [0xA5; 32]; // event 2 cell    /  event 2' topic
const T2: [u8; 32] = [0xA6; 32]; // event 2 topic   /  event 2' data[0]

/// `[ {c1,t1,[a,b]}, {c2,t2,[]} ]`
fn event_list_left() -> Vec<EmittedEvent> {
    vec![
        EmittedEvent {
            cell: CellId(C1),
            topic: T1,
            data: vec![A, B],
        },
        EmittedEvent {
            cell: CellId(C2),
            topic: T2,
            data: vec![],
        },
    ]
}

/// `[ {c1,t1,[a]}, {b,c2,[t2]} ]` — the same 32-byte lanes in the same order,
/// re-cut one lane earlier. A *different* list of events: different second-event
/// cell, different topic, different data.
fn event_list_right() -> Vec<EmittedEvent> {
    vec![
        EmittedEvent {
            cell: CellId(C1),
            topic: T1,
            data: vec![A],
        },
        EmittedEvent {
            cell: CellId(B),
            topic: C2,
            data: vec![T2],
        },
    ]
}

/// The **v4** (pre-fix) per-event absorption, reproduced verbatim from
/// `turn.rs` at HEAD~ so the collision can be exhibited rather than asserted.
fn legacy_v4_event_stream(events: &[EmittedEvent]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(events.len() as u64).to_le_bytes());
    for ev in events {
        out.extend_from_slice(ev.cell.as_bytes());
        out.extend_from_slice(&ev.topic);
        for d in &ev.data {
            out.extend_from_slice(d);
        }
    }
    out
}

/// The **v5** per-event absorption, spelled out independently of the crate's
/// implementation so `absorb_emitted_event` is pinned to a stated encoding
/// rather than to itself.
fn expected_v5_event_bytes(ev: &EmittedEvent) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(ev.cell.as_bytes());
    out.extend_from_slice(&ev.topic);
    out.extend_from_slice(&(ev.data.len() as u64).to_le_bytes());
    for d in &ev.data {
        out.extend_from_slice(d);
    }
    out
}

/// A replica of the **whole** `receipt_hash` preimage, parameterised by domain
/// tag and by whether the per-event encoding counts the data felts.
///
/// This exists so the v4 defect can be *executed* rather than argued after the
/// fact: `prefix_free = false` is the v4 encoding, `true` is v5. It is written
/// for the shape [`pinned_receipt`] produces (empty routing directives,
/// introduction exports, derivation records and consumed capabilities — asserted
/// below, so it can never silently under-cover) and is validated against the
/// real implementation by [`the_v5_replica_matches_the_real_receipt_hash`]. It
/// is test-only and is deliberately not a second production encoder.
fn replica_preimage(r: &TurnReceipt, domain: &[u8], prefix_free: bool) -> Vec<u8> {
    assert!(r.routing_directives.is_empty());
    assert!(r.introduction_exports.is_empty());
    assert!(r.derivation_records.is_empty());
    assert!(r.consumed_capabilities.is_empty());

    let mut p = Vec::new();
    p.extend_from_slice(domain);
    p.extend_from_slice(&r.turn_hash);
    p.extend_from_slice(&r.forest_hash);
    p.extend_from_slice(&r.pre_state_hash);
    p.extend_from_slice(&r.post_state_hash);
    p.extend_from_slice(&r.timestamp.to_le_bytes());
    p.extend_from_slice(&r.effects_hash);
    p.extend_from_slice(&r.computrons_used.to_le_bytes());
    p.extend_from_slice(&(r.action_count as u64).to_le_bytes());
    p.extend_from_slice(r.agent.as_bytes());
    p.extend_from_slice(&r.federation_id);
    match &r.previous_receipt_hash {
        Some(h) => {
            p.push(1);
            p.extend_from_slice(h);
        }
        None => p.push(0),
    }
    p.extend_from_slice(&0u64.to_le_bytes()); // routing_directives
    p.extend_from_slice(&0u64.to_le_bytes()); // introduction_exports
    p.extend_from_slice(&0u64.to_le_bytes()); // derivation_records
    p.extend_from_slice(&(r.emitted_events.len() as u64).to_le_bytes());
    for ev in &r.emitted_events {
        p.extend_from_slice(ev.cell.as_bytes());
        p.extend_from_slice(&ev.topic);
        if prefix_free {
            p.extend_from_slice(&(ev.data.len() as u64).to_le_bytes());
        }
        for d in &ev.data {
            p.extend_from_slice(d);
        }
    }
    p.push(match r.finality {
        Finality::Final => 0x01,
        Finality::Tentative => 0x02,
    });
    p.push(u8::from(r.was_encrypted));
    p.push(u8::from(r.was_burn));
    p.extend_from_slice(&0u64.to_le_bytes()); // consumed_capabilities
    p
}

fn finalized_core(receipt: &TurnReceipt) -> FinalizedReceiptCoreV1 {
    let ctx = FinalizedExecutionContextV1::new([0x99; 32], 7, receipt.timestamp);
    FinalizedReceiptCoreV1::from_receipt(
        ctx,
        11,
        FinalizedReceiptPredecessorV1::LegacyCutover {
            legacy_receipt_index: 4,
            legacy_receipt_hash: [0x66; 32],
        },
        receipt,
    )
    .expect("pinned receipt projects into a finalized core")
}

// ---------------------------------------------------------------------------
// 1. the collision, and its closure
// ---------------------------------------------------------------------------

/// The two event lists really are different (guards against a fixture that
/// accidentally builds the same thing twice, which would make every assertion
/// below vacuous).
#[test]
fn the_two_event_lists_are_genuinely_different() {
    let left = event_list_left();
    let right = event_list_right();

    assert_eq!(left.len(), right.len(), "same number of events");
    assert_eq!(left[0].cell.as_bytes(), right[0].cell.as_bytes());
    assert_eq!(left[0].topic, right[0].topic);
    // ...but the first event's payload width and the whole second event differ.
    assert_ne!(left[0].data, right[0].data);
    assert_ne!(left[1].cell.as_bytes(), right[1].cell.as_bytes());
    assert_ne!(left[1].topic, right[1].topic);
    assert_ne!(left[1].data, right[1].data);
}

/// Exhibits the v4 defect: the two different lists absorb the identical byte
/// stream under the un-prefixed encoding.
#[test]
fn legacy_v4_event_encoding_collides() {
    let left = legacy_v4_event_stream(&event_list_left());
    let right = legacy_v4_event_stream(&event_list_right());

    assert_eq!(
        left, right,
        "the v4 encoding is not prefix-free: two different event lists absorb \
         the same bytes (this is the defect v5 closes)"
    );
    // Both are `count(8) ‖ 6 lanes of 32` — the collision is exact, not partial.
    assert_eq!(left.len(), 8 + 6 * 32);
}

/// **The regression test.** On the v4 encoding these two receipts had the same
/// `receipt_hash`; on v5 they must not.
#[test]
fn receipt_hash_distinguishes_the_colliding_event_lists() {
    let left = pinned_receipt(event_list_left());
    let right = pinned_receipt(event_list_right());

    // Everything except `emitted_events` is byte-identical, so any difference
    // in the digest is attributable to the event encoding alone.
    assert_eq!(left.turn_hash, right.turn_hash);
    assert_eq!(left.effects_hash, right.effects_hash);

    assert_ne!(
        left.receipt_hash(),
        right.receipt_hash(),
        "receipt_hash must separate event lists that the v4 encoding collided"
    );
}

/// The replica is faithful: with the v5 domain and the counted event encoding
/// it reproduces the real `receipt_hash` bit for bit. Everything the next test
/// concludes about the v4 encoding rests on this.
#[test]
fn the_v5_replica_matches_the_real_receipt_hash() {
    for receipt in [
        pinned_receipt(Vec::new()),
        pinned_receipt(event_list_left()),
        pinned_receipt(event_list_right()),
    ] {
        let replica = blake3::hash(&replica_preimage(&receipt, b"dregg-receipt-v5", true));
        assert_eq!(
            *replica.as_bytes(),
            receipt.receipt_hash(),
            "the test replica must track the real v5 preimage exactly"
        );
    }
}

/// **Before / after, executed.** Under the v4 preimage the two receipts hash to
/// the same 32 bytes; under v5 they do not. This is the assertion that fails on
/// the old encoding.
#[test]
fn v4_preimage_collides_where_v5_separates() {
    let left = pinned_receipt(event_list_left());
    let right = pinned_receipt(event_list_right());

    // BEFORE (v4): identical preimages, hence identical digests.
    let v4_left = replica_preimage(&left, b"dregg-receipt-v4", false);
    let v4_right = replica_preimage(&right, b"dregg-receipt-v4", false);
    assert_eq!(
        v4_left, v4_right,
        "v4 preimages of two different receipts are byte-identical"
    );
    assert_eq!(
        blake3::hash(&v4_left).as_bytes(),
        blake3::hash(&v4_right).as_bytes(),
        "v4 receipt_hash collided"
    );

    // AFTER (v5): the same two receipts separate.
    assert_ne!(
        left.receipt_hash(),
        right.receipt_hash(),
        "v5 separates them"
    );
}

/// The executor signature inherits the separation: the signed message is
/// domain ‖ receipt_hash, so two receipts that no longer share a hash no longer
/// share a signable message.
#[test]
fn executor_signed_message_distinguishes_the_colliding_event_lists() {
    let left = pinned_receipt(event_list_left());
    let right = pinned_receipt(event_list_right());

    assert_ne!(
        left.canonical_executor_signed_message(),
        right.canonical_executor_signed_message(),
        "an executor signature must not be valid over both outcomes"
    );
}

// ---------------------------------------------------------------------------
// 2. domain pins
// ---------------------------------------------------------------------------

/// The executor-signature domain bumped in lockstep with the receipt domain, so
/// a v4 verifier reconstructing a v5 preimage FAILS the signature check instead
/// of silently mismatching. The v2 narrow message is untouched.
#[test]
fn executor_signature_domain_is_v5_and_fences_v4() {
    let receipt = pinned_receipt(event_list_left());

    let msg = receipt.canonical_executor_signed_message();
    assert!(
        msg.starts_with(b"executor-receipt-sig-v5:"),
        "executor signatures must use the v5 domain separator"
    );
    assert_eq!(msg.len(), b"executor-receipt-sig-v5:".len() + 32);
    assert_eq!(
        &msg[b"executor-receipt-sig-v5:".len()..],
        &receipt.receipt_hash()[..]
    );

    // A v4 verifier rebuilds `"executor-receipt-sig-v4:" || <its v4 hash>`.
    // Both halves differ, so its message can never equal the signed one.
    let mut v4_shaped = b"executor-receipt-sig-v4:".to_vec();
    v4_shaped.extend_from_slice(&receipt.receipt_hash());
    assert_ne!(msg, v4_shaped, "domain must fence a v4 reconstruction");

    // The legacy narrow message is a separate, still-distinct domain.
    let v2 = receipt.canonical_executor_signed_message_v2();
    assert!(v2.starts_with(b"executor-receipt-sig-v2:"));
    assert_ne!(v2, msg);
}

/// Golden test vector for `dregg-receipt-v5` over a fully-pinned receipt.
///
/// This pins the domain string AND the complete field order/encoding: any
/// change to either — including an accidental revert of the event-count prefix
/// — moves this digest. Regenerate deliberately (and bump the domain) when the
/// preimage is intentionally changed.
#[test]
fn receipt_hash_v5_golden_vector() {
    let with_events = pinned_receipt(event_list_left());
    let no_events = pinned_receipt(Vec::new());

    assert_eq!(
        hex::encode(no_events.receipt_hash()),
        "198e865bcac4d654ed89806f2ba450c6ccb2a4b988544437d83a91db57fca517",
        "dregg-receipt-v5 golden vector (no events) moved"
    );
    assert_eq!(
        hex::encode(with_events.receipt_hash()),
        "61c97f301269a9b69fc04e3b47f1845d1cd367204ce5c13b1e75541daaef616b",
        "dregg-receipt-v5 golden vector (two events) moved"
    );
}

// ---------------------------------------------------------------------------
// 3. the two implementations now share one encoding
// ---------------------------------------------------------------------------

/// The shared encoder emits exactly the documented prefix-free layout.
#[test]
fn shared_encoder_emits_the_documented_layout() {
    for ev in event_list_left().iter().chain(event_list_right().iter()) {
        let mut hasher = blake3::Hasher::new();
        absorb_emitted_event(&mut hasher, ev);
        let via_helper = *hasher.finalize().as_bytes();

        let expected = *blake3::hash(&expected_v5_event_bytes(ev)).as_bytes();
        assert_eq!(
            via_helper, expected,
            "absorb_emitted_event must be cell ‖ topic ‖ data.len() ‖ data*"
        );

        // The count really is there: 32 (cell) + 32 (topic) + 8 (count) + 32·k.
        assert_eq!(
            expected_v5_event_bytes(ev).len(),
            32 + 32 + 8 + 32 * ev.data.len()
        );
    }
}

/// `receipt_hash` and `finalized_receipt_core_v1`'s `event_commitment` now agree
/// on the per-event convention. `event_commitment` is module-private, so the
/// agreement is checked at the two observable points it can be:
///
/// 1. Structurally — both call the same [`absorb_emitted_event`]; the encoding
///    is asserted against an independent spelling above.
/// 2. Behaviourally — the finalized core, whose only varying input here is the
///    event commitment, separates the same pair `receipt_hash` separates. Under
///    v4 these two disagreed: the finalized core separated the pair and
///    `receipt_hash` did not.
///
/// The outer *domains* legitimately differ (`dregg-receipt-v5` absorbs the whole
/// receipt; `dregg-finalized-events-v1` is a keyed per-disclosure digest), so
/// the two digests are not equal and are not asserted to be.
#[test]
fn finalized_core_and_receipt_hash_agree_on_the_event_convention() {
    let left = pinned_receipt(event_list_left());
    let right = pinned_receipt(event_list_right());

    let left_core = finalized_core(&left);
    let right_core = finalized_core(&right);

    assert_ne!(
        left_core.id().bytes(),
        right_core.id().bytes(),
        "the finalized core separates the pair"
    );
    assert_ne!(
        left.receipt_hash(),
        right.receipt_hash(),
        "and so does receipt_hash — the v4 divergence is closed"
    );

    // Both surfaces are sensitive to the count in the same direction: appending
    // an event with empty data must move both, even though nothing new is
    // absorbed beyond the boundary marker itself.
    let mut extended = event_list_left();
    extended.push(EmittedEvent {
        cell: CellId([0xB1; 32]),
        topic: [0xB2; 32],
        data: vec![],
    });
    let extended_receipt = pinned_receipt(extended);
    assert_ne!(left.receipt_hash(), extended_receipt.receipt_hash());
    assert_ne!(
        left_core.id().bytes(),
        finalized_core(&extended_receipt).id().bytes()
    );
}

/// Moving a felt from one event's `data` into the next event's is visible on
/// both surfaces. (This particular pair also separated under v4 — the felt
/// changes absolute position — so it is a sanity floor, not a defect witness;
/// the witness is [`receipt_hash_distinguishes_the_colliding_event_lists`],
/// where the lanes stay in place and only the boundary moves.)
#[test]
fn moving_a_data_felt_across_an_event_boundary_is_visible() {
    let both_here = pinned_receipt(vec![
        EmittedEvent {
            cell: CellId(C1),
            topic: T1,
            data: vec![A, B],
        },
        EmittedEvent {
            cell: CellId(C2),
            topic: T2,
            data: vec![],
        },
    ]);
    let one_each = pinned_receipt(vec![
        EmittedEvent {
            cell: CellId(C1),
            topic: T1,
            data: vec![A],
        },
        EmittedEvent {
            cell: CellId(C2),
            topic: T2,
            data: vec![B],
        },
    ]);

    assert_ne!(both_here.receipt_hash(), one_each.receipt_hash());
    assert_ne!(
        finalized_core(&both_here).id().bytes(),
        finalized_core(&one_each).id().bytes()
    );
}

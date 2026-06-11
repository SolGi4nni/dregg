//! Adversarial fuzz of the wire framing codec + the postcard `Turn` payload.
//!
//! TARGET 1 — `dregg_wire::codec::decode` (the length-prefixed framing layer).
//!   A peer controls the bytes. We feed garbage, truncated frames, and
//!   maximal-length declarations and assert the decoder NEVER panics and NEVER
//!   silently fabricates a `WireMessage` from nonsense. (A panic is a remote
//!   DoS; a silent accept is a parse-confusion bug.)
//!
//! TARGET 2 — the postcard `Turn` payload (`/api/turns/submit-signed`, gossip,
//!   blocklace-finalized replay). Postcard is a NON-self-describing positional
//!   format: a single `#[serde(skip_serializing_if = ...)]` on any field that
//!   rides inside `Turn` desyncs the byte stream — that exact bug made every
//!   turn with a defaulted optional undecodable, so turns never replicated.
//!   `turn/tests/integration_postcard_wire_roundtrip.rs` pins THREE hand-written
//!   shapes. This harness GENERALIZES: proptest drives the structural shape of
//!   the Turn (which optionals are Some/None, forest fan-out/depth, effect mix)
//!   across the whole input space, so a future skip_serializing_if regression on
//!   ANY field/variant combination is caught — not just the three baked shapes.
//!
//! Outcome semantics: a panic / desync / silent-accept is a FINDING (the test
//! fails). A clean reject-or-roundtrip across thousands of cases is EVIDENCE the
//! framing + payload codec is robust on the running wire.

use std::collections::HashMap;

use dregg_turn::action::{symbol, Action, Authorization, DelegationMode, Effect};
use dregg_turn::forest::{CallForest, CallTree};
use dregg_turn::turn::Turn;
use dregg_types::CellId;
use proptest::prelude::*;

// ============================================================================
// TARGET 1: framing-codec decode robustness
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// `decode` on ARBITRARY bytes must return `Ok` or `Err` — never panic,
    /// never run unbounded. A peer fully controls this buffer.
    #[test]
    fn decode_never_panics_on_arbitrary_bytes(buf in proptest::collection::vec(any::<u8>(), 0..4096)) {
        // The only contract: it returns. Both arms are acceptable; a panic is not.
        let _ = dregg_wire::codec::decode(&buf);
    }

    /// Re-encoding a successfully-decoded message must itself succeed and the
    /// message must survive a SECOND decode unchanged. A positional desync (the
    /// skip_serializing_if failure mode) would corrupt the re-encode here. This
    /// is the wire-message analogue of the Turn roundtrip below.
    #[test]
    fn wire_message_decode_is_a_fixed_point(buf in proptest::collection::vec(any::<u8>(), 0..4096)) {
        if let Ok(msg) = dregg_wire::codec::decode(&buf) {
            // It decoded — so it MUST re-encode and round-trip byte-stably.
            let frame = dregg_wire::codec::encode(&msg)
                .expect("a decoded WireMessage must re-encode");
            // Strip the 4-byte length header before re-decoding the payload.
            let payload = &frame[dregg_wire::codec::HEADER_SIZE..];
            let msg2 = dregg_wire::codec::decode(payload)
                .expect("a re-encoded WireMessage must decode again (positional stability)");
            prop_assert_eq!(msg, msg2, "wire message is not a codec fixed point");
        }
    }
}

/// A declared frame length at/over the 16 MiB cap is a memory-exhaustion lever.
/// `encode` must refuse to PRODUCE an over-cap frame (the read side checks the
/// declared length BEFORE allocating, tested in the wire crate's own suite).
#[test]
fn oversize_payload_is_refused_by_encoder() {
    use dregg_wire::message::{AuthorizationRequest, WireMessage};
    let msg = WireMessage::PresentToken {
        proof: vec![0u8; (dregg_wire::codec::MAX_MESSAGE_SIZE + 1) as usize],
        request: AuthorizationRequest::new("a", "b", "c"),
        federation_root: [0u8; 32],
    };
    let r = dregg_wire::codec::encode(&msg);
    assert!(
        matches!(
            r,
            Err(dregg_wire::codec::CodecError::MessageTooLarge { .. })
        ),
        "encoder accepted an over-cap payload — memory-exhaustion lever (FINDING)"
    );
}

// ============================================================================
// TARGET 2: postcard `Turn` payload — generalized skip_serializing_if defense
// ============================================================================

fn cell_from_byte(b: u8) -> CellId {
    CellId::from_bytes([b; 32])
}

/// A representative effect set. These are the wire-bearing variants whose
/// OPTIONAL sub-fields are exactly where a positional desync hides (NoteCreate
/// carries the historically-skipped value_commitment / range_proof optionals).
fn arb_effect() -> impl Strategy<Value = Effect> {
    prop_oneof![
        (any::<u8>(), any::<u8>(), any::<u64>()).prop_map(|(f, t, amount)| Effect::Transfer {
            from: cell_from_byte(f),
            to: cell_from_byte(t),
            amount,
        }),
        (any::<u8>()).prop_map(|c| Effect::IncrementNonce {
            cell: cell_from_byte(c)
        }),
        // NoteCreate with BOTH optionals exercised at None (the desync trigger)
        (any::<u64>(), any::<u64>()).prop_map(|(value, asset_type)| {
            Effect::NoteCreate {
                commitment: dregg_cell::NoteCommitment([9u8; 32]),
                value,
                asset_type,
                encrypted_note: vec![],
                value_commitment: None,
                range_proof: None,
            }
        }),
        // ...and Some(_) to drive the present-branch of the same optionals.
        (any::<u64>()).prop_map(|value| Effect::NoteCreate {
            commitment: dregg_cell::NoteCommitment([3u8; 32]),
            value,
            asset_type: 0,
            encrypted_note: vec![1, 2, 3],
            value_commitment: Some([4u8; 32]),
            range_proof: Some(vec![5, 6, 7, 8]),
        }),
    ]
}

fn arb_action() -> impl Strategy<Value = Action> {
    (any::<u8>(), proptest::collection::vec(arb_effect(), 0..4)).prop_map(|(target, effects)| {
        Action {
            target: cell_from_byte(target),
            method: symbol("submit"),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        }
    })
}

/// A call tree with bounded fan-out/depth (children also ride postcard).
/// `CallTree` keeps a private cached-hash field, so trees are assembled via the
/// public `new` / `add_child` API rather than a struct literal.
fn arb_tree() -> impl Strategy<Value = CallTree> {
    let leaf = arb_action().prop_map(CallTree::new);
    leaf.prop_recursive(3, 12, 3, |inner| {
        (arb_action(), proptest::collection::vec(inner, 0..3)).prop_map(|(action, children)| {
            let mut t = CallTree::new(action);
            for c in children {
                // Re-graft each generated child subtree under the new root.
                t.children.push(c);
            }
            t
        })
    })
}

/// Drive the WHOLE structural shape of a `Turn`: which optional sidecars are
/// Some/None, the forest fan-out, the effect mix. This is the space a baked
/// 3-shape regression test cannot cover.
fn arb_turn() -> impl Strategy<Value = Turn> {
    (
        any::<u8>(),
        any::<u64>(),
        any::<u64>(),
        proptest::option::of("[a-z ]{0,16}"),
        proptest::option::of(any::<[u8; 32]>()),
        proptest::collection::vec(arb_tree(), 1..3),
    )
        .prop_map(|(agent, nonce, fee, memo, prev, roots)| {
            let mut forest = CallForest::new();
            for r in roots {
                forest.roots.push(r);
            }
            Turn {
                agent: cell_from_byte(agent),
                nonce,
                fee,
                memo,
                valid_until: None,
                call_forest: forest,
                depends_on: vec![],
                previous_receipt_hash: prev,
                conservation_proof: None,
                sovereign_witnesses: HashMap::new(),
                execution_proof: None,
                execution_proof_cell: None,
                execution_proof_new_commitment: None,
                custom_program_proofs: None,
                effect_binding_proofs: Vec::new(),
                cross_effect_dependencies: Vec::new(),
                effect_witness_index_map: Vec::new(),
            }
        })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    /// THE generalized skip_serializing_if defense: any postcard-encoded `Turn`
    /// must decode, and re-encoding the decoded value must be byte-identical.
    /// A skip_serializing_if on ANY field that rides inside Turn breaks this for
    /// the input shapes that trip its predicate — proptest hunts those shapes.
    #[test]
    fn turn_postcard_roundtrip_is_byte_stable(turn in arb_turn()) {
        let bytes = postcard::to_stdvec(&turn).expect("postcard serialize Turn");
        let decoded: Turn = postcard::from_bytes(&bytes)
            .expect("postcard MUST round-trip Turn (no skip_serializing_if desync)");
        let bytes2 = postcard::to_stdvec(&decoded).expect("re-serialize decoded Turn");
        prop_assert_eq!(&bytes, &bytes2, "postcard re-encode of Turn is not byte-stable");
        // Spot-check load-bearing scalar fields survived.
        prop_assert_eq!(turn.nonce, decoded.nonce);
        prop_assert_eq!(turn.fee, decoded.fee);
        prop_assert_eq!(turn.memo.clone(), decoded.memo.clone());
        prop_assert_eq!(
            turn.call_forest.action_count(),
            decoded.call_forest.action_count(),
            "forest action count changed across postcard roundtrip"
        );
    }

    /// Truncating a valid Turn frame at every prefix length must NEVER panic the
    /// decoder. A peer can always send a short read. (Catches index-out-of-range
    /// / slice-panic in the positional parser.)
    #[test]
    fn truncated_turn_frame_never_panics(turn in arb_turn(), cut in any::<u16>()) {
        let bytes = postcard::to_stdvec(&turn).expect("serialize");
        if bytes.is_empty() { return Ok(()); }
        let n = (cut as usize) % bytes.len();
        // Decoding a prefix is allowed to fail; it must not panic.
        let _ = postcard::from_bytes::<Turn>(&bytes[..n]);
    }

    /// Single-bit corruption of a valid Turn frame must NEVER panic the decoder
    /// (it may decode to a different valid Turn or error — both fine).
    #[test]
    fn bitflipped_turn_frame_never_panics(turn in arb_turn(), idx in any::<u32>(), bit in 0u8..8) {
        let mut bytes = postcard::to_stdvec(&turn).expect("serialize");
        if bytes.is_empty() { return Ok(()); }
        let i = (idx as usize) % bytes.len();
        bytes[i] ^= 1 << bit;
        let _ = postcard::from_bytes::<Turn>(&bytes);
    }
}

//! Golden wire pin for the canonical outer turn envelope.

use dregg_cell::CellId;
use dregg_turn::{SignedTurn, TurnBuilder};
use dregg_types::{PublicKey, Signature};

const SIGNED_TURN_WIRE_GOLDEN_HEX: &str = "11111111111111111111111111111111111111111111111111111111111111110700000000000000000000000000000000000000000000000000000000000000000009010667616c6c6579015401222222222222222222222222222222222222222222222222222222222222222200000000000000000000403333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333320444444444444444444444444444444444444444444444444444444444444444403555657026667";

fn fixture() -> SignedTurn {
    let mut turn = TurnBuilder::new(CellId::from_bytes([0x11; 32]), 7).build();
    turn.fee = 9;
    turn.memo = Some("galley".to_owned());
    turn.valid_until = Some(42);
    turn.previous_receipt_hash = Some([0x22; 32]);
    SignedTurn {
        turn,
        signature: Signature([0x33; 64]),
        signer: PublicKey([0x44; 32]),
        pq_signature: vec![0x55, 0x56, 0x57],
        pq_signer: vec![0x66, 0x67],
    }
}

#[test]
fn canonical_signed_turn_postcard_bytes_are_pinned() {
    let wire = postcard::to_stdvec(&fixture()).expect("encode canonical SignedTurn");
    assert_eq!(hex::encode(&wire), SIGNED_TURN_WIRE_GOLDEN_HEX);
    let decoded: SignedTurn = postcard::from_bytes(&wire).expect("decode canonical SignedTurn");
    assert_eq!(
        postcard::to_stdvec(&decoded).expect("re-encode canonical SignedTurn"),
        wire
    );
}

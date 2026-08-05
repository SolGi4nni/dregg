//! SDK compatibility pin for the `dregg-turn`-owned SignedTurn envelope.

use dregg_sdk::{CellId, SignedTurn};
use dregg_turn::TurnBuilder;
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

fn accepts_lower_turn(_: &dregg_turn::SignedTurn) {}

#[test]
fn sdk_root_and_legacy_cipherclerk_paths_are_the_lower_wire_type() {
    let signed: SignedTurn = fixture();
    accepts_lower_turn(&signed);
    let legacy_path: &dregg_sdk::cipherclerk::SignedTurn = &signed;
    accepts_lower_turn(legacy_path);

    let wire = postcard::to_stdvec(&signed).expect("encode SDK SignedTurn");
    assert_eq!(hex::encode(&wire), SIGNED_TURN_WIRE_GOLDEN_HEX);
    let decoded: dregg_turn::SignedTurn =
        postcard::from_bytes(&wire).expect("lower crate decodes SDK bytes");
    assert_eq!(
        postcard::to_stdvec(&decoded).expect("lower crate re-encodes SDK bytes"),
        wire
    );
}

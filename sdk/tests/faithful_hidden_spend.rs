use dregg_circuit::field::BABYBEAR_P;
use dregg_commit::poseidon2_tree::Poseidon2NoteProof16;
use dregg_sdk::privacy::{
    FaithfulHiddenSpendProof, FaithfulNoteOpening, FaithfulNoteSpendPublic,
    build_faithful_hidden_spend_proof,
};
use dregg_turn::Effect;
use dregg_turn::faithful_note_spend::FaithfulNoteSpendProofCarrier;

fn root8_bytes(root: [u32; 8]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (lane, value) in root.into_iter().enumerate() {
        bytes[4 * lane..4 * lane + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}

#[test]
fn faithful_hidden_spend_artifact_lowers_to_the_exact_strict_effect() {
    let public = FaithfulNoteSpendPublic {
        root_height: 0x1122_3344_5566_7788,
        historical_note_root: core::array::from_fn(|lane| 0x1000 + lane as u32),
        nullifier: core::array::from_fn(|lane| 0x80u8.wrapping_add(lane as u8)),
        value: 0x0123_4567_89ab_cdef,
        asset_type: 0x8899_aabb_ccdd_eeff,
        successor_nullifier_root: core::array::from_fn(|lane| 0x2000 + lane as u32),
    };
    let carrier = FaithfulNoteSpendProofCarrier::new(
        public.root_height,
        root8_bytes(public.successor_nullifier_root),
        vec![0xa5, 0x5a, 0x11],
    )
    .expect("canonical strict carrier");
    let encoded_carrier = carrier.encode();
    let artifact = FaithfulHiddenSpendProof { public, carrier };

    match artifact.into_note_spend_effect() {
        Effect::NoteSpend {
            nullifier,
            note_tree_root,
            value,
            asset_type,
            spending_proof,
            value_commitment,
        } => {
            assert_eq!(nullifier.0, public.nullifier);
            assert_eq!(note_tree_root, root8_bytes(public.historical_note_root));
            assert_eq!(value, public.value);
            assert_eq!(asset_type, public.asset_type);
            assert_eq!(spending_proof, encoded_carrier);
            assert_eq!(value_commitment, None);
        }
        other => panic!("faithful spend lowered to the wrong effect: {other:?}"),
    }
}

#[test]
fn faithful_hidden_spend_refuses_hostile_statement_before_proving() {
    let opening = FaithfulNoteOpening {
        owner: [0; 32],
        value: 7,
        asset_type: 9,
        creation_nonce: [0x44; 32],
        randomness: [0x55; 32],
        spending_key: [0x66; 32],
    };
    let membership = Poseidon2NoteProof16 {
        leaf: [dregg_circuit::BabyBear::ZERO; 16],
        siblings: vec![[[dregg_circuit::BabyBear::ZERO; 8]; 3]; 16],
        positions: vec![0; 16],
    };

    let error = build_faithful_hidden_spend_proof(&opening, &membership, (5, [0; 8]), [0; 8])
        .expect_err("an address unrelated to the hidden key must refuse before proving");
    assert!(error.to_string().contains("owner is not the FNO2 address"));

    let mut noncanonical = [0; 8];
    noncanonical[3] = BABYBEAR_P;
    let error = build_faithful_hidden_spend_proof(&opening, &membership, (5, noncanonical), [0; 8])
        .expect_err("a noncanonical historical root must refuse before proving");
    assert!(error.to_string().contains("noncanonical for BabyBear"));
}

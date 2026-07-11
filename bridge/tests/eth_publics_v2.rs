//! The V2 (25-lane) Ethereum public-input encoding seam, end-to-end over the
//! PUBLIC crate API.
//!
//! The live `WholeChainProof` claim is 25 BabyBear lanes
//! (`genesis_root[0..8] ++ final_root[0..8] ++ num_turns ++ chain_digest[0..8]`,
//! see `docs/FINDING-chain-participation-census.md` §1); [`EthPublicInputsV2`]
//! is the bridge-side encoding of that statement. These tests pin:
//!
//! 1. the fail-closed constructor (every lane canonical BabyBear, `num_turns`
//!    in `u32` range — REJECT polarity on each violation);
//! 2. the 800-byte ABI-word calldata tail + its exact-length, padding-checked,
//!    canonicality-re-validating inverse (round-trip + REJECT polarity);
//! 3. a GOLDEN pinned vector (fixed input → fixed 800-byte hex tail) so the
//!    Solidity side can cross-check the exact bytes;
//! 4. the [`WholeChainProofBytes`] seam (the real wire envelope feeds the
//!    constructor directly);
//! 5. reuse of the EXISTING [`EthBridgeState`] machine for V2 via the pinned
//!    `keccak256(abi.encodePacked(8 x big-endian uint32))` root key.
//!
//! All test names carry the `ethereum` prefix so the module gate
//! (`cargo test -p dregg-bridge ethereum`) runs them.

use dregg_bridge::ethereum::{
    BABYBEAR_MODULUS, ETH_PI_LANES_V2, ETH_PI_TAIL_BYTES_V2, EthBridgeError, EthBridgeState,
    EthPublicInputsV2, EthStateAdvance, SnarkSystem, root8_bridge_key, solidity_verifier_interface,
    solidity_verifier_interface_v2, submit_eth_settlement, wrap_for_ethereum,
};
use dregg_circuit_prove::ivc_turn_chain::{WHOLE_CHAIN_PROOF_ENVELOPE_V1, WholeChainProofBytes};

/// The pinned golden vector's four fields (every lane canonical; `final_root`
/// includes the maximal canonical residue `p - 1 = 0x7800_0000` to pin the
/// boundary).
const G_GENESIS: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
const G_FINAL: [u32; 8] = [
    2_013_265_920, // p - 1: the largest canonical residue
    0x1234_5678,
    0x0BAD_F00D,
    0x00C0_FFEE,
    1,
    0,
    123_456,
    1_234_567_890,
];
const G_NUM_TURNS: u64 = 42;
const G_DIGEST: [u32; 8] = [8, 7, 6, 5, 4, 3, 2, 1];

fn golden() -> EthPublicInputsV2 {
    EthPublicInputsV2::new(G_GENESIS, G_FINAL, G_NUM_TURNS, G_DIGEST)
        .expect("the golden vector is canonical")
}

/// Round-trip: construct → 800-byte tail → decode → identical publics, with
/// the 25-lane order pinned (genesis ++ final ++ num_turns ++ digest).
#[test]
fn ethereum_publics_v2_round_trips() {
    let p = golden();

    let lanes = p.lanes();
    assert_eq!(lanes.len(), ETH_PI_LANES_V2);
    assert_eq!(&lanes[0..8], &G_GENESIS, "lanes 0..8 = genesis_root");
    assert_eq!(&lanes[8..16], &G_FINAL, "lanes 8..16 = final_root");
    assert_eq!(lanes[16], G_NUM_TURNS as u32, "lane 16 = num_turns");
    assert_eq!(&lanes[17..25], &G_DIGEST, "lanes 17..25 = chain_digest");

    let tail = p.to_calldata_v2();
    assert_eq!(tail.len(), ETH_PI_TAIL_BYTES_V2, "25 x 32 = 800 bytes");
    assert_eq!(ETH_PI_TAIL_BYTES_V2, 800);

    let decoded = EthPublicInputsV2::from_tail_v2(&tail).expect("valid tail decodes");
    assert_eq!(decoded, p, "publics survive the round trip");
    assert_eq!(decoded.genesis_root(), G_GENESIS);
    assert_eq!(decoded.final_root(), G_FINAL);
    assert_eq!(decoded.num_turns(), G_NUM_TURNS as u32);
    assert_eq!(decoded.chain_digest(), G_DIGEST);
}

/// REJECT: a non-canonical lane (>= p) in ANY of the four fields refuses
/// construction — nothing is reduced.
#[test]
fn ethereum_publics_v2_rejects_non_canonical_lane() {
    // The modulus itself and u32::MAX, in each field position.
    for bad in [BABYBEAR_MODULUS, BABYBEAR_MODULUS + 1, u32::MAX] {
        let mut g = G_GENESIS;
        g[0] = bad;
        assert!(
            matches!(
                EthPublicInputsV2::new(g, G_FINAL, G_NUM_TURNS, G_DIGEST),
                Err(EthBridgeError::InvalidProof { .. })
            ),
            "genesis lane {bad} must be refused"
        );

        let mut f = G_FINAL;
        f[7] = bad;
        assert!(
            matches!(
                EthPublicInputsV2::new(G_GENESIS, f, G_NUM_TURNS, G_DIGEST),
                Err(EthBridgeError::InvalidProof { .. })
            ),
            "final lane {bad} must be refused"
        );

        let mut d = G_DIGEST;
        d[3] = bad;
        assert!(
            matches!(
                EthPublicInputsV2::new(G_GENESIS, G_FINAL, G_NUM_TURNS, d),
                Err(EthBridgeError::InvalidProof { .. })
            ),
            "digest lane {bad} must be refused"
        );

        // num_turns is a lane of the 25-lane claim: canonical too.
        assert!(
            matches!(
                EthPublicInputsV2::new(G_GENESIS, G_FINAL, u64::from(bad), G_DIGEST),
                Err(EthBridgeError::InvalidProof { .. })
            ),
            "num_turns {bad} must be refused"
        );
    }

    // The boundary is exact: p - 1 is accepted everywhere (G_FINAL[0] = p - 1
    // in the golden vector), and num_turns = p - 1 is accepted.
    EthPublicInputsV2::new(
        G_GENESIS,
        G_FINAL,
        u64::from(BABYBEAR_MODULUS - 1),
        G_DIGEST,
    )
    .expect("p - 1 is canonical");
}

/// REJECT: num_turns out of u32 range (the envelope carries u64).
#[test]
fn ethereum_publics_v2_rejects_num_turns_out_of_u32() {
    for bad in [u64::from(u32::MAX) + 1, u64::MAX] {
        assert!(
            matches!(
                EthPublicInputsV2::new(G_GENESIS, G_FINAL, bad, G_DIGEST),
                Err(EthBridgeError::InvalidProof { .. })
            ),
            "num_turns {bad} exceeds u32 and must be refused"
        );
    }
}

/// REJECT: a wrong-length tail (the format is pinned to exactly 800 bytes).
#[test]
fn ethereum_publics_v2_rejects_wrong_tail_length() {
    let tail = golden().to_calldata_v2();
    for bad_len in [0usize, 104, 799, 801] {
        let mut t = tail.clone();
        t.resize(bad_len, 0);
        assert!(
            EthPublicInputsV2::from_tail_v2(&t).is_err(),
            "a {bad_len}-byte tail must be refused"
        );
    }
}

/// REJECT: decode re-validates — a tail carrying a non-canonical lane or a
/// word with nonzero high padding (>= 2^32) is refused, never truncated.
#[test]
fn ethereum_publics_v2_rejects_bad_tail_words() {
    let tail = golden().to_calldata_v2();

    // Word 3 (genesis lane 3) rewritten to the modulus: correct uint32 shape,
    // non-canonical value.
    let mut t = tail.clone();
    t[3 * 32 + 28..3 * 32 + 32].copy_from_slice(&BABYBEAR_MODULUS.to_be_bytes());
    assert!(
        matches!(
            EthPublicInputsV2::from_tail_v2(&t),
            Err(EthBridgeError::InvalidProof { .. })
        ),
        "a non-canonical lane in the tail must be refused"
    );

    // Word 16 (num_turns) with a nonzero padding byte: the value is >= 2^32,
    // not a uint32 — must be refused, not truncated to the low 4 bytes.
    let mut t = tail.clone();
    t[16 * 32 + 27] = 1;
    assert!(
        matches!(
            EthPublicInputsV2::from_tail_v2(&t),
            Err(EthBridgeError::Internal { .. })
        ),
        "nonzero high-padding must be refused"
    );

    // Even padding byte 0 (the most significant) is checked.
    let mut t = tail;
    t[24 * 32] = 0xFF;
    assert!(
        EthPublicInputsV2::from_tail_v2(&t).is_err(),
        "nonzero most-significant padding must be refused"
    );
}

/// GOLDEN pinned vector: the fixed input above must produce EXACTLY this
/// 800-byte tail (hex, one 32-byte ABI word per lane, big-endian), so the
/// Solidity side can cross-check `abi.encode(uint32[8],uint32[8],uint32,
/// uint32[8])` byte-for-byte. Regenerating this constant from the code under
/// test would make the test vacuous — it is pinned literally.
#[test]
fn ethereum_publics_v2_golden_tail_pinned() {
    const GOLDEN_TAIL_HEX: &str = concat!(
        // genesis_root[0..8] = [0,1,2,3,4,5,6,7]
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000001",
        "0000000000000000000000000000000000000000000000000000000000000002",
        "0000000000000000000000000000000000000000000000000000000000000003",
        "0000000000000000000000000000000000000000000000000000000000000004",
        "0000000000000000000000000000000000000000000000000000000000000005",
        "0000000000000000000000000000000000000000000000000000000000000006",
        "0000000000000000000000000000000000000000000000000000000000000007",
        // final_root[0..8] = [p-1, 0x12345678, 0x0badf00d, 0x00c0ffee, 1, 0,
        //                     123456, 1234567890]
        "0000000000000000000000000000000000000000000000000000000078000000",
        "0000000000000000000000000000000000000000000000000000000012345678",
        "000000000000000000000000000000000000000000000000000000000badf00d",
        "0000000000000000000000000000000000000000000000000000000000c0ffee",
        "0000000000000000000000000000000000000000000000000000000000000001",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000001e240",
        "00000000000000000000000000000000000000000000000000000000499602d2",
        // num_turns = 42
        "000000000000000000000000000000000000000000000000000000000000002a",
        // chain_digest[0..8] = [8,7,6,5,4,3,2,1]
        "0000000000000000000000000000000000000000000000000000000000000008",
        "0000000000000000000000000000000000000000000000000000000000000007",
        "0000000000000000000000000000000000000000000000000000000000000006",
        "0000000000000000000000000000000000000000000000000000000000000005",
        "0000000000000000000000000000000000000000000000000000000000000004",
        "0000000000000000000000000000000000000000000000000000000000000003",
        "0000000000000000000000000000000000000000000000000000000000000002",
        "0000000000000000000000000000000000000000000000000000000000000001",
    );
    assert_eq!(GOLDEN_TAIL_HEX.len(), 800 * 2);

    let tail = golden().to_calldata_v2();
    let tail_hex: String = tail.iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(
        tail_hex, GOLDEN_TAIL_HEX,
        "the golden 800-byte tail is pinned"
    );

    // And the golden tail decodes back to the golden publics (the pinned bytes
    // are themselves a valid wire input).
    let bytes: Vec<u8> = (0..GOLDEN_TAIL_HEX.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&GOLDEN_TAIL_HEX[i..i + 2], 16).unwrap())
        .collect();
    assert_eq!(
        EthPublicInputsV2::from_tail_v2(&bytes).expect("golden tail decodes"),
        golden()
    );
}

/// The real wire envelope ([`WholeChainProofBytes`] v3) feeds the constructor
/// directly; an envelope with a non-canonical lane or oversized num_turns is
/// refused at this seam.
#[test]
fn ethereum_publics_v2_from_whole_chain_bytes() {
    let env = WholeChainProofBytes {
        version: WHOLE_CHAIN_PROOF_ENVELOPE_V1,
        vk_fingerprint_hex: "cafe".to_string(),
        root_proof: vec![1, 2, 3],
        binding_proof: vec![4, 5, 6],
        genesis_root: G_GENESIS,
        final_root: G_FINAL,
        chain_digest: G_DIGEST,
        num_turns: G_NUM_TURNS,
    };
    let p = EthPublicInputsV2::from_whole_chain_bytes(&env).expect("canonical envelope converts");
    assert_eq!(p, golden(), "the envelope fields land in the pinned lanes");

    // REJECT: non-canonical anchor lane.
    let mut bad = env.clone();
    bad.final_root[0] = BABYBEAR_MODULUS;
    assert!(EthPublicInputsV2::from_whole_chain_bytes(&bad).is_err());

    // REJECT: num_turns beyond u32.
    let mut bad = env;
    bad.num_turns = u64::from(u32::MAX) + 1;
    assert!(EthPublicInputsV2::from_whole_chain_bytes(&bad).is_err());
}

/// Serde cannot smuggle a non-canonical value around the constructor: decode
/// is routed through the fail-closed validation, so wire bytes carrying a
/// lane >= p are refused; a canonical value round-trips.
#[test]
fn ethereum_publics_v2_serde_is_fail_closed() {
    let p = golden();
    let json = serde_json::to_string(&p).expect("serializes");
    let back: EthPublicInputsV2 = serde_json::from_str(&json).expect("canonical decodes");
    assert_eq!(back, p, "serde round-trips a canonical value");

    // Rewrite the golden JSON's num_turns to the modulus: decode must refuse.
    let bad = json.replace(
        "\"num_turns\":42",
        &format!("\"num_turns\":{BABYBEAR_MODULUS}"),
    );
    assert_ne!(bad, json, "the rewrite must have hit");
    assert!(
        serde_json::from_str::<EthPublicInputsV2>(&bad).is_err(),
        "a non-canonical num_turns must be refused at serde decode"
    );

    // And a non-canonical root lane likewise.
    let bad = json.replace("2013265920", &format!("{}", u32::MAX));
    assert_ne!(bad, json);
    assert!(
        serde_json::from_str::<EthPublicInputsV2>(&bad).is_err(),
        "a non-canonical root lane must be refused at serde decode"
    );
}

/// The V2 Solidity interface pins the 25-lane `settle` signature; the v1
/// interface is untouched (STAGED-ADDITIVE).
#[test]
fn ethereum_solidity_interface_v2_pinned_v1_untouched() {
    let v2 = solidity_verifier_interface_v2();
    assert!(v2.contains("IDreggSettlementV2"));
    assert!(v2.contains("uint32[8] calldata genesisRoot"));
    assert!(v2.contains("uint32[8] calldata finalRoot"));
    assert!(v2.contains("uint32 numTurns"));
    assert!(v2.contains("uint32[8] calldata chainDigest"));

    // v1 still emits the old 4-scalar shape, unchanged.
    let v1 = solidity_verifier_interface();
    assert!(v1.contains("bytes32 genesisRoot"));
    assert!(v1.contains("uint64  numTurns"));
    assert!(!v1.contains("uint32[8]"), "v1 must remain the 4-scalar ABI");
}

/// V2 reuses the EXISTING [`EthBridgeState`] machine: 8-lane roots are keyed by
/// `keccak256(abi.encodePacked(8 x big-endian uint32))` ([`root8_bridge_key`]),
/// so continuity + monotone-height logic is shared with v1. A v2 advance whose
/// genesis lanes differ from the proven root is refused through the SAME gate.
#[test]
fn ethereum_publics_v2_reuses_bridge_state_via_root_key() {
    let p = golden();
    let gk = p.genesis_bridge_key();
    let fk = p.final_bridge_key();
    assert_eq!(gk, root8_bridge_key(&G_GENESIS));
    assert_eq!(fk, root8_bridge_key(&G_FINAL));
    assert_ne!(gk, fk, "distinct roots key distinctly");
    // The key is the keccak of the 32 packed bytes, NOT the packed bytes
    // themselves: the genesis key must not simply be the big-endian lanes.
    let mut packed = [0u8; 32];
    for (i, lane) in G_GENESIS.iter().enumerate() {
        packed[i * 4..i * 4 + 4].copy_from_slice(&lane.to_be_bytes());
    }
    assert_ne!(gk, packed, "the key is keccak256(packed), not packed");
    // One lane flipped changes the key (injective keying in practice).
    let mut g2 = G_GENESIS;
    g2[7] ^= 1;
    assert_ne!(root8_bridge_key(&g2), gk);

    // Drive the shared state machine on the v2 keys end-to-end.
    let mut state = EthBridgeState::new(gk);
    let proof = wrap_for_ethereum(
        [0xAB; 32],
        dregg_bridge::ethereum::EthPublicInputs {
            genesis_root: gk,
            final_root: fk,
            num_turns: G_NUM_TURNS,
            chain_digest: root8_bridge_key(&G_DIGEST),
        },
        SnarkSystem::BindingOnly,
        None,
        [0; 32],
    )
    .expect("binding wrap over the v2 keys");
    submit_eth_settlement(
        &mut state,
        EthStateAdvance {
            old_root: gk,
            new_root: fk,
            height: 1,
            proof: proof.clone(),
            confirmed_at: None,
        },
    )
    .expect("a continuous v2-keyed advance queues");

    // REJECT: an advance whose old key does not chain (different genesis lanes)
    // is refused by the SAME continuity gate.
    let mut state2 = EthBridgeState::new(root8_bridge_key(&g2));
    assert!(
        matches!(
            submit_eth_settlement(
                &mut state2,
                EthStateAdvance {
                    old_root: gk, // != proven root key root8_bridge_key(&g2)
                    new_root: fk,
                    height: 1,
                    proof,
                    confirmed_at: None,
                },
            ),
            Err(EthBridgeError::InvalidAdvance { .. })
        ),
        "a discontinuous v2-keyed advance must be refused"
    );
}

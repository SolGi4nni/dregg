//! Teeth for the gnark witness exporter + Fiat-Shamir transcript fixture
//! (ETH-NATIVE-WRAP milestone 1).
//!
//! The exporter is PURE SERIALIZATION, so these teeth exercise it on a
//! minimal assembled [`WholeChainProofBytes`] envelope with VALID canonical
//! lanes (building a real recursive whole-chain proof is a multi-minute
//! proving job — deliberately not done in a unit tooth; milestone 3's spike
//! covers the real-proof path). Every accept has its REJECT twins:
//! non-canonical lanes, num_turns overflow, wrong envelope version, empty
//! root proof.
//!
//! The transcript tooth KAT-pins the squeezed challenges so any drift in the
//! challenger (permutation constants, duplex order, squeeze direction) BITES
//! here before it silently breaks gnark<->Rust transcript agreement.
//!
//! This test is also the fixture EMITTER: it deterministically (re)writes
//! `chain/gnark/fixtures/transcript_w16.json` and
//! `chain/gnark/fixtures/gnark_witness_minimal.json`.

use std::fs;
use std::path::PathBuf;

use dregg_circuit_prove::gnark_witness_export::{
    BABYBEAR_MODULUS, GNARK_PUBLIC_INPUT_LEN, GNARK_WITNESS_FORMAT_VERSION,
    GnarkWitnessExportError, TRANSCRIPT_FIXTURE_ABSORB_COUNT, TRANSCRIPT_FIXTURE_SQUEEZE_COUNT,
    export_gnark_witness_json, gnark_public_input_vector, transcript_fixture_w16,
    transcript_fixture_w16_json,
};
use dregg_circuit_prove::ivc_turn_chain::{
    RecursionVk, SEG_ANCHOR_WIDTH, SEG_DIGEST_WIDTH, WHOLE_CHAIN_PROOF_ENVELOPE_V1,
    WholeChainProofBytes,
};

// ============================================================================
// Helpers
// ============================================================================

fn test_anchor() -> RecursionVk {
    RecursionVk([0x5a; 32])
}

/// A minimal assembled envelope with VALID canonical lanes and per-position
/// sentinel values (every lane distinct, so any order/aliasing bug is visible).
fn minimal_envelope() -> WholeChainProofBytes {
    let mut genesis_root = [0u32; SEG_ANCHOR_WIDTH];
    let mut final_root = [0u32; SEG_ANCHOR_WIDTH];
    let mut chain_digest = [0u32; SEG_DIGEST_WIDTH];
    for i in 0..SEG_ANCHOR_WIDTH {
        genesis_root[i] = 1000 + i as u32;
        final_root[i] = 2000 + i as u32;
    }
    for (i, d) in chain_digest.iter_mut().enumerate() {
        *d = 3000 + i as u32;
    }
    WholeChainProofBytes {
        version: WHOLE_CHAIN_PROOF_ENVELOPE_V1,
        vk_fingerprint_hex: test_anchor().to_hex(),
        root_proof: vec![0xAB; 64],
        binding_proof: vec![0xCD; 32],
        genesis_root,
        final_root,
        chain_digest,
        num_turns: 4242,
    }
}

fn hex_decode(s: &str) -> Vec<u8> {
    assert!(
        s.len().is_multiple_of(2),
        "hex string must have even length"
    );
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex byte"))
        .collect()
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("chain")
        .join("gnark")
        .join("fixtures")
}

// ============================================================================
// The exporter: ACCEPT path
// ============================================================================

/// The modulus constant the exporter validates against IS the BabyBear field
/// order — pinned so the fail-closed bound can never drift from the field.
#[test]
fn modulus_constant_pins_the_field_order() {
    use p3_field::PrimeField32;
    assert_eq!(BABYBEAR_MODULUS, p3_baby_bear::BabyBear::ORDER_U32);
    assert_eq!(BABYBEAR_MODULUS, 2013265921);
    assert_eq!(GNARK_PUBLIC_INPUT_LEN, 25);
}

/// The emitted JSON is well-formed (parsed by REAL serde_json), carries every
/// documented key, and its values round-trip the envelope exactly.
#[test]
fn accept_minimal_envelope_full_shape() {
    let env = minimal_envelope();
    let anchor = test_anchor();
    let json = export_gnark_witness_json(&env, &anchor).expect("valid envelope must export");
    let v: serde_json::Value = serde_json::from_str(&json).expect("emitted JSON must parse");

    assert_eq!(v["version"], GNARK_WITNESS_FORMAT_VERSION);
    assert_eq!(v["envelope_version"], WHOLE_CHAIN_PROOF_ENVELOPE_V1);
    assert_eq!(v["vk_anchor_hex"], anchor.to_hex());
    assert_eq!(v["claimed_vk_fingerprint_hex"], env.vk_fingerprint_hex);

    let publics = &v["publics"];
    for i in 0..SEG_ANCHOR_WIDTH {
        assert_eq!(publics["genesis_root"][i], env.genesis_root[i]);
        assert_eq!(publics["final_root"][i], env.final_root[i]);
    }
    for i in 0..SEG_DIGEST_WIDTH {
        assert_eq!(publics["chain_digest"][i], env.chain_digest[i]);
    }
    assert_eq!(publics["num_turns"], env.num_turns as u32);

    // root_proof_hex round-trips to the exact postcard bytes.
    let hex = v["root_proof_hex"]
        .as_str()
        .expect("root_proof_hex is a string");
    assert_eq!(hex_decode(hex), env.root_proof);

    let vector = v["public_input_vector"]
        .as_array()
        .expect("public_input_vector is an array");
    assert_eq!(vector.len(), 25);
    for lane in vector {
        let value: u64 = lane
            .as_str()
            .expect("every lane is a decimal STRING")
            .parse()
            .expect("every lane parses as decimal");
        assert!(
            value < BABYBEAR_MODULUS as u64,
            "every emitted lane must be canonical, got {value}"
        );
    }
}

/// THE PINNED ORDER, by construction: with per-position sentinels,
/// `public_input_vector = genesis_root[0..8] ++ final_root[0..8] ++ num_turns
/// ++ chain_digest[0..8]` — position by position, both in the returned vector
/// and in the emitted JSON.
#[test]
fn public_input_vector_order_is_genesis_final_numturns_digest() {
    let env = minimal_envelope();
    let vector = gnark_public_input_vector(&env).expect("canonical lanes must validate");
    assert_eq!(vector.len(), 25);

    // Independent expected construction, straight from the pinned contract.
    let mut expected: Vec<u32> = Vec::with_capacity(25);
    expected.extend_from_slice(&env.genesis_root);
    expected.extend_from_slice(&env.final_root);
    expected.push(env.num_turns as u32);
    expected.extend_from_slice(&env.chain_digest);
    assert_eq!(vector.to_vec(), expected);

    // Sentinel spot-checks (an order swap of any two blocks CANNOT pass these).
    assert_eq!(vector[0], 1000);
    assert_eq!(vector[7], 1007);
    assert_eq!(vector[8], 2000);
    assert_eq!(vector[15], 2007);
    assert_eq!(vector[16], 4242);
    assert_eq!(vector[17], 3000);
    assert_eq!(vector[24], 3007);

    // And the emitted JSON carries the SAME vector (decimal strings).
    let json = export_gnark_witness_json(&env, &test_anchor()).expect("export");
    let v: serde_json::Value = serde_json::from_str(&json).expect("parse");
    let emitted: Vec<u32> = v["public_input_vector"]
        .as_array()
        .expect("array")
        .iter()
        .map(|lane| lane.as_str().expect("decimal string").parse().expect("u32"))
        .collect();
    assert_eq!(emitted, expected);
}

/// The canonical boundary VALUE `p - 1` is accepted in every lane position
/// (the reject twin below shows `p` itself is refused — an off-by-one in the
/// bound cannot pass both).
#[test]
fn accept_boundary_lane_p_minus_1() {
    let mut env = minimal_envelope();
    env.genesis_root[0] = BABYBEAR_MODULUS - 1;
    env.final_root[7] = BABYBEAR_MODULUS - 1;
    env.chain_digest[3] = BABYBEAR_MODULUS - 1;
    env.num_turns = (BABYBEAR_MODULUS - 1) as u64;
    let vector = gnark_public_input_vector(&env).expect("p-1 lanes are canonical");
    assert_eq!(vector[0], BABYBEAR_MODULUS - 1);
    assert_eq!(vector[15], BABYBEAR_MODULUS - 1);
    assert_eq!(vector[16], BABYBEAR_MODULUS - 1);
    assert_eq!(vector[20], BABYBEAR_MODULUS - 1);
    export_gnark_witness_json(&env, &test_anchor()).expect("boundary envelope must export");
}

// ============================================================================
// The exporter: REJECT teeth (fail-closed, never clamped)
// ============================================================================

/// A non-canonical lane (== p, and >= p up to u32::MAX) is REFUSED in every
/// public block, with the offending field/index named.
#[test]
fn reject_non_canonical_lanes_every_block() {
    for bad in [BABYBEAR_MODULUS, BABYBEAR_MODULUS + 1, u32::MAX] {
        // genesis_root
        let mut env = minimal_envelope();
        env.genesis_root[3] = bad;
        match gnark_public_input_vector(&env) {
            Err(GnarkWitnessExportError::NonCanonicalLane {
                field: "genesis_root",
                index: 3,
                value,
            }) => assert_eq!(value, bad),
            other => panic!("genesis_root[3]={bad} must be refused, got {other:?}"),
        }
        assert!(export_gnark_witness_json(&env, &test_anchor()).is_err());

        // final_root
        let mut env = minimal_envelope();
        env.final_root[0] = bad;
        match gnark_public_input_vector(&env) {
            Err(GnarkWitnessExportError::NonCanonicalLane {
                field: "final_root",
                index: 0,
                value,
            }) => assert_eq!(value, bad),
            other => panic!("final_root[0]={bad} must be refused, got {other:?}"),
        }

        // chain_digest
        let mut env = minimal_envelope();
        env.chain_digest[7] = bad;
        match gnark_public_input_vector(&env) {
            Err(GnarkWitnessExportError::NonCanonicalLane {
                field: "chain_digest",
                index: 7,
                value,
            }) => assert_eq!(value, bad),
            other => panic!("chain_digest[7]={bad} must be refused, got {other:?}"),
        }
    }
}

/// `num_turns` beyond u32 (would truncate) and at/above p (would wrap in the
/// field lane) are BOTH refused — no clamping, no silent reduction.
#[test]
fn reject_num_turns_overflow_and_wrap() {
    for bad in [
        BABYBEAR_MODULUS as u64,       // == p: wraps to 0 in the field lane
        (BABYBEAR_MODULUS as u64) + 5, // > p, still fits u32: wraps
        1u64 << 32,                    // u32 overflow: would truncate to 0
        u64::MAX,                      // way out
    ] {
        let mut env = minimal_envelope();
        env.num_turns = bad;
        match gnark_public_input_vector(&env) {
            Err(GnarkWitnessExportError::NumTurnsNotCanonical { value }) => {
                assert_eq!(value, bad)
            }
            other => panic!("num_turns={bad} must be refused, got {other:?}"),
        }
        assert!(export_gnark_witness_json(&env, &test_anchor()).is_err());
    }
}

/// A foreign envelope version is refused before any lane is read.
#[test]
fn reject_wrong_envelope_version() {
    let mut env = minimal_envelope();
    env.version = WHOLE_CHAIN_PROOF_ENVELOPE_V1 + 1;
    match export_gnark_witness_json(&env, &test_anchor()) {
        Err(GnarkWitnessExportError::UnsupportedEnvelopeVersion { found, expected }) => {
            assert_eq!(found, WHOLE_CHAIN_PROOF_ENVELOPE_V1 + 1);
            assert_eq!(expected, WHOLE_CHAIN_PROOF_ENVELOPE_V1);
        }
        other => panic!("wrong version must be refused, got {other:?}"),
    }
}

/// An envelope with no root proof bytes has nothing for the gnark circuit to
/// verify — refused.
#[test]
fn reject_empty_root_proof() {
    let mut env = minimal_envelope();
    env.root_proof = Vec::new();
    match export_gnark_witness_json(&env, &test_anchor()) {
        Err(GnarkWitnessExportError::EmptyRootProof) => {}
        other => panic!("empty root_proof must be refused, got {other:?}"),
    }
}

// ============================================================================
// The Fiat-Shamir transcript fixture
// ============================================================================

/// The KAT: the exact 8 challenges the verifier's challenger squeezes for the
/// documented absorb sequence. Pinned so ANY drift in the sponge — permutation
/// constants, duplex overwrite-vs-add, squeeze direction, rate/width — bites
/// here byte-for-byte. (Values recomputed live each run; this array is the
/// frozen reference the Go side must reproduce.)
const TRANSCRIPT_W16_CHALLENGE_KAT: [u32; 8] = [
    1917944385, 1028837269, 546488453, 341748543, 764831861, 1787535874, 260560799, 568621648,
];

#[test]
fn transcript_fixture_protocol_and_kat() {
    let fx = transcript_fixture_w16();

    // The absorb sequence IS the byte values 0..16.
    assert_eq!(fx.absorbed.len(), TRANSCRIPT_FIXTURE_ABSORB_COUNT);
    for (i, &a) in fx.absorbed.iter().enumerate() {
        assert_eq!(a, i as u32);
    }

    // 8 challenges, all canonical, not degenerate (all-distinct — a stuck or
    // zeroed sponge cannot pass).
    assert_eq!(fx.challenges.len(), TRANSCRIPT_FIXTURE_SQUEEZE_COUNT);
    for &c in &fx.challenges {
        assert!(c < BABYBEAR_MODULUS, "challenge {c} must be canonical");
    }
    let mut sorted = fx.challenges.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), 8, "challenges must be pairwise distinct");

    // The documented squeeze direction: sample pops from the END of the rate
    // prefix, so challenges[i] == final_sponge_state[RATE-1-i].
    for i in 0..8 {
        assert_eq!(
            fx.challenges[i],
            fx.final_sponge_state[7 - i],
            "squeeze direction drifted at challenge {i}"
        );
    }
    for &lane in &fx.final_sponge_state {
        assert!(lane < BABYBEAR_MODULUS);
    }

    // THE KAT.
    assert_eq!(
        fx.challenges, TRANSCRIPT_W16_CHALLENGE_KAT,
        "transcript KAT drift: the challenger no longer squeezes the pinned \
         challenges — gnark<->Rust transcript agreement is broken"
    );
}

/// The JSON rendering of the fixture parses, carries the documented keys, and
/// matches the struct values exactly.
#[test]
fn transcript_fixture_json_matches_struct() {
    let fx = transcript_fixture_w16();
    let json = transcript_fixture_w16_json();
    let v: serde_json::Value = serde_json::from_str(&json).expect("fixture JSON must parse");

    assert_eq!(v["field"], "BabyBear");
    assert_eq!(v["modulus"], BABYBEAR_MODULUS.to_string());
    assert_eq!(v["width"], 16);
    assert_eq!(v["rate"], 8);
    assert!(
        v["description"]
            .as_str()
            .expect("description present")
            .contains("POPS FROM THE END"),
        "the squeeze-direction gotcha must be documented in-band"
    );

    let parse_lanes = |key: &str| -> Vec<u32> {
        v[key]
            .as_array()
            .unwrap_or_else(|| panic!("{key} is an array"))
            .iter()
            .map(|s| s.as_str().expect("decimal string").parse().expect("u32"))
            .collect()
    };
    assert_eq!(parse_lanes("absorbed"), fx.absorbed.to_vec());
    assert_eq!(parse_lanes("challenges"), fx.challenges.to_vec());
    assert_eq!(
        parse_lanes("final_sponge_state"),
        fx.final_sponge_state.to_vec()
    );
}

// ============================================================================
// Fixture emission (chain/gnark/fixtures/)
// ============================================================================

/// Deterministically (re)write the two fixture files the Go side consumes.
/// Emission is itself gated on the teeth above passing in the same binary
/// (cargo runs them all); the write is byte-stable, so a re-run is a no-op
/// diff.
#[test]
fn emit_fixture_files() {
    let dir = fixtures_dir();
    fs::create_dir_all(&dir).expect("create chain/gnark/fixtures");

    // 1. The transcript fixture.
    let transcript = transcript_fixture_w16_json();
    let transcript_path = dir.join("transcript_w16.json");
    fs::write(&transcript_path, &transcript).expect("write transcript_w16.json");
    let readback = fs::read_to_string(&transcript_path).expect("read back");
    assert_eq!(readback, transcript, "fixture write must be byte-faithful");

    // 2. A minimal witness-shape example (sentinel lanes, NOT a real proof —
    //    the Go side uses it to lock the JSON schema; milestone 3's spike
    //    exports a real root).
    let witness = export_gnark_witness_json(&minimal_envelope(), &test_anchor())
        .expect("minimal envelope exports");
    let witness_path = dir.join("gnark_witness_minimal.json");
    fs::write(&witness_path, &witness).expect("write gnark_witness_minimal.json");
    let readback = fs::read_to_string(&witness_path).expect("read back");
    assert_eq!(readback, witness, "fixture write must be byte-faithful");
}

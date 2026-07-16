//! Proof round-trip integration test: prove → serialize → transmit → deserialize → verify.
//!
//! Tests that proofs survive serialization boundaries — this catches wire protocol
//! binding mismatches and format disagreements between prover and verifier.
//!
//! stark-kill (f04b2dd1e) deleted the hand-STARK engine and with it the legacy
//! `PredicateProof` (+ `prove_predicate`/`verify_predicate`) and
//! `stark::{proof_to_bytes, proof_from_bytes, verify}` these round-trips used to
//! ride. Dispositions:
//! - the predicate-proof postcard round-trips (GTE/LTE/GT/LT/NEQ) and the
//!   predicate proof-size bound died with the `PredicateProof` type — the
//!   descriptor-world predicate proofs live behind `dregg-circuit-prove`
//!   (not a dep of this crate) and their wire shape is exercised by the
//!   presentation-wire round-trip below plus the circuit-prove emit gates;
//! - the raw STARK bytes round-trip is ported onto the surviving Plonky3
//!   Merkle prover (same tooth: a serialized proof must deserialize and the
//!   DESERIALIZED proof must verify);
//! - the presentation-proof wire round-trip survives unchanged (its inner
//!   membership proof now rides the descriptor `DescriptorProofWire` path).

use dregg_circuit::BabyBear;
use dregg_sdk::AuthRequest;
use dregg_teasting::agent::{SimAgent, shared_root_key};

/// STARK proof bytes: prove → postcard bytes → deserialize → verify.
///
/// Builds a Poseidon2-compatible Merkle witness (real hashing), generates a real
/// Plonky3 STARK proof, serializes/deserializes it, then verifies the
/// deserialized proof (and that it still rejects wrong public inputs).
#[test]
fn test_stark_proof_bytes_round_trip() {
    // Retargeted onto the LAW-#1 path: the Merkle membership algebra is the byte-pinned IR2
    // descriptor emitted by `MerkleMembership4aryEmit.lean`, proved through the assured
    // interpreter. (This test previously drove `plonky3_prover::{prove,verify}_plonky3`, the
    // hand-authored `P3MerklePoseidon2Air` retired under law #1 — same inputs, same assertions.)
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::merkle_air::{
        MembershipP3Proof, membership_public_inputs, prove_membership_p3, verify_membership_p3,
    };

    // Build a Poseidon2-compatible Merkle path (depth 4).
    let leaf_hash = BabyBear::new(12345);
    let depth = 4;
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        positions.push((i % 4) as u8);
        siblings.push([
            BabyBear::new((i * 7 + 100) as u32),
            BabyBear::new((i * 7 + 200) as u32),
            BabyBear::new((i * 7 + 300) as u32),
        ]);
    }

    // The public inputs the descriptor pins: [leaf, root].
    let pis = membership_public_inputs(leaf_hash, &siblings, &positions)
        .expect("witness must yield public inputs");
    assert_eq!(pis[0], leaf_hash);

    // Prove membership through the Lean-emitted descriptor.
    let proof = prove_membership_p3(leaf_hash, &siblings, &positions)
        .expect("honest membership witness must prove");

    // Serialize to bytes (simulates wire transmission) and recover.
    let bytes = postcard::to_allocvec(&proof).expect("STARK proof should serialize");
    assert!(!bytes.is_empty(), "Serialized proof should be non-empty");
    let recovered: MembershipP3Proof =
        postcard::from_bytes(&bytes).expect("STARK proof should deserialize");

    // The deserialized proof must still verify against the honest public inputs.
    verify_membership_p3(&recovered, &pis).expect("deserialized STARK proof should verify");

    // ... and must still REJECT forged public inputs (the wrong-PI tooth this test exists for).
    let wrong_leaf = vec![BabyBear::new(0xBAD), pis[1]];
    assert!(
        verify_membership_p3(&recovered, &wrong_leaf).is_err(),
        "a proof must NOT verify against a forged leaf"
    );
    let wrong_root = vec![pis[0], BabyBear::new(0xBAD)];
    assert!(
        verify_membership_p3(&recovered, &wrong_root).is_err(),
        "a proof must NOT verify against a forged root"
    );
}

// RETIRED (2026-07-16): `test_presentation_proof_round_trip` targeted the API of the RETIRED
// `dregg_circuit::RealPresentationProof` — it called `real_stark.verify() ->
// PresentationVerification::Valid`, but the live `bridge::present::RealPresentationProof`
// (`bridge/src/present.rs:153`, which "replaced the retired dregg_circuit::RealPresentationProof"
// per its own docstring at :146) exposes only `total_proof_size_bytes`/`proof_size_display`;
// verification moved to the free fn `verify_presentation_full(&BridgePresentationProof,
// federation_root, expected_action, now, max_proof_age)`. So the test could not compile and
// therefore documented NOTHING — it was a comment wearing a #[test] hat, and it kept this whole
// file (including the STARK round-trip below/above) out of the build.
//
// ITS INTENT IS WORTH KEEPING and is recorded as a named residual in GOAL-STARK-KILL.md
// (`PresentationRoundTripResidual`): it asserted that a full bridge presentation proof survives
// postcard serialization, and was written to catch `DeserializeUnexpectedEnd` — "a real wire
// protocol bug (the prover and verifier disagree on the binary format)". Re-landing it means
// porting to `BridgePresentationProof` + `verify_presentation_full`. Related live coverage:
// `tests/src/wire_format_e2e.rs` (the presentation wire format e2e).

//! # CROSS-CRATE KAT — `cell Poseidon2 == circuit Poseidon2`
//!
//! The cell layer hashes Poseidon2-tagged commitments (the `PreimageGate` /
//! `KeyRotationGate` slot digests, and `Note` commitments / nullifiers) with the
//! STARK-native Poseidon2 sponge. This file is the conformance gate proving those
//! cell-side hashes are BIT-FOR-BIT the SAME function the circuit verifies —
//! `dregg_circuit::poseidon2`, the audited width-16 BabyBear permutation that is
//! itself KAT-locked to Plonky3's `default_babybear_poseidon2_16`
//! (see `poseidon2::tests::poseidon2_plonky3_cross_check_kat`).
//!
//! Before this, the cell used a `poseidon2-stub:`-prefixed BLAKE3 stand-in for
//! `HashKind::Poseidon2` and a domain-separated BLAKE3 for note commitments —
//! so a "Poseidon2" cell commitment could never equal an in-circuit Poseidon2
//! commitment. These tests fail loudly if that drift is ever reintroduced (e.g.
//! a constant/round/encoding change on either side, or a regression to BLAKE3).
//!
//! The cell's private `hash_preimage32` is exercised through its public
//! surfaces:
//!   - a `PreimageGate` evaluation (the digest the gate recomputes), and
//!   - `Note::commitment` (the 32-byte encoding of `Note::poseidon2_commitment`).

use dregg_cell::note::Note;
use dregg_cell::program::{CellProgram, HashKind, StateConstraint};
use dregg_cell::state::CellState;
use dregg_cell::{digest8_to_bytes32, felt_to_bytes32, preconditions::EvalContext};
use dregg_circuit::poseidon2::{hash_bytes_8, hash_many};

/// THE KAT: a `PreimageGate` tagged `Poseidon2` accepts exactly the slot word
/// `digest8_to_bytes32(dregg_circuit::poseidon2::hash_bytes_8(preimage))` and rejects
/// any other — i.e. the digest the gate recomputes internally IS the circuit's
/// `hash_bytes_8`. Checked over several preimages (including adversarial high-byte
/// mutations) so the agreement is structural, not a single lucky vector.
///
/// ⚑ The slot word was `felt_to_bytes32(hash_bytes(preimage))` until 2026-08-01 — ONE
/// felt in bytes 0..4, 28 bytes left zero, against the sibling BLAKE3 arm's full 32. See
/// `cell::program::eval::hash_preimage32` for what that handed an attacker and
/// `cell/tests/preimage_gate_wide_old_admits_new_rejects.rs` for the measured exhibit.
#[test]
fn preimage_gate_poseidon2_equals_circuit_hash_bytes_8() {
    let program = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: HashKind::Poseidon2,
    }]);

    let preimages: [[u8; 32]; 5] = [
        [0u8; 32],
        [0xFFu8; 32],
        [7u8; 32],
        {
            // a high-byte-only variation of [7;32] (bytes above the first chunk)
            let mut p = [7u8; 32];
            p[31] ^= 0xFF;
            p[16] ^= 0xA5;
            p
        },
        {
            // pseudo-random fixed vector
            let mut p = [0u8; 32];
            let mut s: u32 = 0xC0FFEE;
            for b in p.iter_mut() {
                s ^= s << 13;
                s ^= s >> 17;
                s ^= s << 5;
                *b = (s & 0xFF) as u8;
            }
            p
        },
    ];

    let ctx = |preimage: [u8; 32]| EvalContext {
        revealed_preimage: Some(preimage),
        ..EvalContext::default()
    };

    for preimage in preimages {
        // The circuit's Poseidon2-of-bytes, encoded to the 32-byte slot word.
        let circuit_digest = digest8_to_bytes32(hash_bytes_8(&preimage));

        let mut state = CellState::new(0);
        state.fields[0] = circuit_digest;

        // The cell's Poseidon2 gate accepts the real preimage against the
        // circuit-computed digest → the cell's internal hash == hash_bytes_8.
        assert!(
            program.evaluate(&state, None, Some(&ctx(preimage))).is_ok(),
            "cell Poseidon2 PreimageGate disagrees with circuit hash_bytes_8 for preimage {preimage:?}"
        );

        // A one-byte-flipped preimage must NOT satisfy the same slot.
        let mut wrong = preimage;
        wrong[0] ^= 0x01;
        assert!(
            program.evaluate(&state, None, Some(&ctx(wrong))).is_err(),
            "a wrong preimage must not open a circuit-computed Poseidon2 digest"
        );

        // Anti-vacuity: the BLAKE3 stand-in digest of the SAME preimage is a
        // different slot word (the gate genuinely uses Poseidon2, not BLAKE3).
        let blake_digest = *blake3::hash(&preimage).as_bytes();
        assert_ne!(
            circuit_digest, blake_digest,
            "Poseidon2 and BLAKE3 digests of {preimage:?} must differ (non-vacuous cutover)"
        );
    }
}

/// THE KAT for notes: the cell's 32-byte `NoteCommitment` equals the
/// `felt_to_bytes32` encoding of an INDEPENDENTLY-built circuit-side Poseidon2
/// hash over the IDENTICAL 28-limb preimage (owner ‖ value ‖ asset_type ‖
/// creation_nonce ‖ randomness). This is the real cell≡circuit differential for
/// the note commitment: the cell's encoding must agree with a from-scratch
/// circuit `hash_many`, not merely with `Note::poseidon2_commitment` itself.
#[test]
fn note_commitment_equals_circuit_poseidon2() {
    // A deterministic note (explicit randomness + nonce → reproducible).
    let owner = {
        let mut o = [0u8; 32];
        o[0] = 0x11;
        o[31] = 0x22;
        o[16] = 0x33;
        o
    };
    let randomness = [0x55u8; 32];
    let nonce = [0x66u8; 32];
    let note = Note::with_nonce(owner, [9u64, 1234, 0, 0, 0, 0, 0, 0], randomness, nonce);

    // INDEPENDENT circuit-side reconstruction of the 28-limb preimage, using
    // ONLY circuit primitives (the same limb decomposition the note documents:
    // 8 LE 4-byte chunks per 32-byte field; low/high 32 bits per u64).
    use dregg_circuit::field::{BABYBEAR_P, BabyBear};
    let bytes32_limbs = |b: &[u8; 32]| -> [BabyBear; 8] {
        let mut out = [BabyBear::ZERO; 8];
        for (i, limb) in out.iter_mut().enumerate() {
            let off = i * 4;
            let v = u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
            *limb = BabyBear::new(v % BABYBEAR_P);
        }
        out
    };
    let u64_limbs = |v: u64| -> [BabyBear; 2] {
        [
            BabyBear::new((v as u32) % BABYBEAR_P),
            BabyBear::new(((v >> 32) as u32) % BABYBEAR_P),
        ]
    };

    let mut preimage = Vec::with_capacity(28);
    preimage.extend_from_slice(&bytes32_limbs(&owner)); // 8
    preimage.extend_from_slice(&u64_limbs(1234)); // 2 (value = fields[1])
    preimage.extend_from_slice(&u64_limbs(9)); // 2 (asset_type = fields[0])
    preimage.extend_from_slice(&bytes32_limbs(&nonce)); // 8 (creation_nonce)
    preimage.extend_from_slice(&bytes32_limbs(&randomness)); // 8
    let circuit_commitment = felt_to_bytes32(hash_many(&preimage));

    assert_eq!(
        note.commitment().0,
        circuit_commitment,
        "cell NoteCommitment != independently-built circuit Poseidon2 commitment"
    );

    // And the underlying felt matches too (cell helper == circuit hash_many).
    assert_eq!(
        felt_to_bytes32(note.poseidon2_commitment()),
        circuit_commitment,
        "poseidon2_commitment felt encoding != circuit hash_many of the 28-limb preimage"
    );
}

/// THE KAT for nullifiers: the cell's 32-byte `Nullifier` equals the
/// `felt_to_bytes32` of an INDEPENDENTLY-built circuit Poseidon2
/// `hash_many(commitment_felt ‖ key[8 limbs] ‖ creation_nonce[8 limbs])` — the
/// same structure the note-spending AIR's `NoteSpendingWitness::nullifier`
/// uses (commitment ‖ key ‖ nonce).
#[test]
fn note_nullifier_equals_circuit_poseidon2() {
    use dregg_circuit::field::{BABYBEAR_P, BabyBear};
    let owner = [0x44u8; 32];
    let randomness = [0x77u8; 32];
    let nonce = [0x88u8; 32];
    let key = {
        let mut k = [0u8; 32];
        k[0] = 0x13;
        k[1] = 0xBB;
        k[30] = 0x99;
        k
    };
    let note = Note::with_nonce(owner, [5u64, 4321, 0, 0, 0, 0, 0, 0], randomness, nonce);

    let bytes32_limbs = |b: &[u8; 32]| -> [BabyBear; 8] {
        let mut out = [BabyBear::ZERO; 8];
        for (i, limb) in out.iter_mut().enumerate() {
            let off = i * 4;
            let v = u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
            *limb = BabyBear::new(v % BABYBEAR_P);
        }
        out
    };

    let mut preimage = Vec::with_capacity(17);
    preimage.push(note.poseidon2_commitment());
    preimage.extend_from_slice(&bytes32_limbs(&key)); // 8
    preimage.extend_from_slice(&bytes32_limbs(&nonce)); // 8 (creation_nonce)
    let circuit_nullifier = felt_to_bytes32(hash_many(&preimage));

    assert_eq!(
        note.nullifier(&key).0,
        circuit_nullifier,
        "cell Nullifier != independently-built circuit Poseidon2 nullifier"
    );
}

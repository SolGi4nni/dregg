//! M2-a: single-asset shielded transfer — both-polarity acceptance tests.
//!
//! The shielded transfer is a two-sided composite (see
//! `dregg_circuit_prove::shielded`):
//!   1. the **hidden STARK side** (`ShieldedTransfer::verify_stark_side`):
//!      per-input membership in the commitment tree + nullifier derivation,
//!      proved through `HidingFriPcs` so the owner/key/path are blind;
//!   2. the **hidden Pedersen side** (`dregg_cell_crypto::value_commitment`):
//!      homomorphic value-commitment conservation, so `Σ v_in = Σ v_out` is
//!      certified without revealing any amount.
//!
//! These tests live here (a `dregg-circuit` integration test, where
//! `dregg-cell` is a dev-dependency) because `circuit` is *upstream* of `cell`:
//! the circuit-side STARK half is library code in `dregg_circuit_prove::shielded`,
//! and the Pedersen value-balance half is composed at this layer.
//!
//! Both polarities, per half:
//!   STARK side    — balanced transfer VERIFIES (blind);
//!                   forged membership (wrong root) REJECTS;
//!                   duplicate / tampered nullifier REJECTS.
//!   Pedersen side — balanced value commitments VERIFY (blind);
//!                   an unbalanced set (inflation) REJECTS.

#![cfg(feature = "prover")]

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::shielded::{
    ShieldedError, ShieldedSpendWitness, ShieldedTransfer, ShieldedTransferWitness,
    ShieldedValueLeg,
};

use dregg_cell_crypto::value_commitment::{
    BulletproofRangeProof, FullConservationError, ValueCommitment, ValueLinkError,
    prove_conservation, scalar_from_blinding_bytes, verify_conservation,
    verify_full_conservation_bytes, verify_value_link,
};
use curve25519_dalek::scalar::Scalar;

const ASSET: u64 = 1;

/// Build a real Bulletproof range proof (serialized bytes) for one output value.
fn range_proof_bytes(value: u64, blinding: &[u8; 32]) -> Vec<u8> {
    BulletproofRangeProof::prove_range(value, &scalar_from_blinding_bytes(blinding)).proof_bytes
}

/// Build a shielded-spend witness with a genuine Poseidon2 Merkle path (leaf =
/// the input note commitment), plus the published value-commitment leg for it.
fn make_input(
    leaf_seed: u32,
    amount: u32,
    blinding: [u8; 32],
    key_seed: u32,
    depth: usize,
) -> ShieldedTransferWitness {
    let key = [
        BabyBear::new(key_seed),
        BabyBear::new(key_seed.wrapping_add(1)),
        BabyBear::new(key_seed.wrapping_add(2)),
        BabyBear::new(key_seed.wrapping_add(3)),
    ];

    // A small genuine Merkle path (deterministic siblings).
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        positions.push((i % 4) as u8);
        siblings.push([
            BabyBear::new((i as u32) * 7 + 1 + leaf_seed),
            BabyBear::new((i as u32) * 7 + 2 + leaf_seed),
            BabyBear::new((i as u32) * 7 + 3 + leaf_seed),
        ]);
    }

    // The leaf is now the C6-bound note commitment hash_fact(value,[asset,owner,
    // randomness]) — a real note whose preimage the spender knows, not a free
    // cell. (The leaf↔value-leg value link is the named residual; see the leg.)
    let spend = ShieldedSpendWitness {
        value: BabyBear::new(amount),
        asset_type: BabyBear::new(ASSET as u32),
        owner: BabyBear::new(0x5EED ^ leaf_seed),
        randomness: BabyBear::new(0xC0FFEE ^ key_seed),
        key,
        siblings,
        positions,
    };

    let commitment =
        ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&blinding));

    ShieldedTransferWitness {
        spend,
        leg: ShieldedValueLeg {
            asset_type: ASSET,
            commitment_bytes: commitment.to_bytes().0,
        },
    }
}

/// Construct a balanced shielded transfer (STARK side) from ONE input, pinned to
/// that input's real DSL Merkle root, with one output leg of equal value.
/// Returns (transfer, in_blinding, out_blinding, out_commitment) so the caller
/// can drive the Pedersen conservation proof.
fn balanced_transfer() -> (ShieldedTransfer, ValueCommitment, ValueCommitment) {
    let amount = 1_000_000u32;
    let in_blinding = [3u8; 32];
    let out_blinding = [7u8; 32];

    let w = make_input(11, amount, in_blinding, 0xABCD, 4);
    let merkle_root = w.spend.merkle_root();

    let in_commit =
        ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&in_blinding));
    let out_commit =
        ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&out_blinding));

    let output_legs = vec![ShieldedValueLeg {
        asset_type: ASSET,
        commitment_bytes: out_commit.to_bytes().0,
    }];
    let output_range_proofs = vec![range_proof_bytes(amount as u64, &out_blinding)];

    let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        merkle_root,
        &[w],
        output_legs,
        output_range_proofs,
    )
    .expect("prove balanced shielded transfer STARK side");

    (transfer, in_commit, out_commit)
}

#[test]
fn balanced_shielded_transfer_stark_side_verifies_blind() {
    let (transfer, _in_c, _out_c) = balanced_transfer();
    // The hidden membership+nullifier proof verifies against the published root,
    // revealing nothing about owner/key/path.
    transfer
        .verify_stark_side()
        .expect("balanced shielded transfer STARK side must verify");
    assert_eq!(transfer.nullifiers().len(), 1);
}

#[test]
fn balanced_shielded_transfer_pedersen_side_verifies_blind() {
    let (transfer, in_c, out_c) = balanced_transfer();
    // excess_blinding = r_in - r_out (the prover knows both).
    let r_in = scalar_from_blinding_bytes(&[3u8; 32]);
    let r_out = scalar_from_blinding_bytes(&[7u8; 32]);
    let excess = r_in - r_out;
    let msg = transfer.transfer_message();
    let proof = prove_conservation(&[in_c.clone()], &[out_c.clone()], &excess, &msg);
    // Value balance certified WITHOUT revealing the amount.
    verify_conservation(&[in_c], &[out_c], &proof, &msg)
        .expect("balanced value commitments must conserve");
}

#[test]
fn forged_membership_wrong_root_rejects() {
    let (mut transfer, _in_c, _out_c) = balanced_transfer();
    // Tamper the published root: the hidden proof was bound to the real root, so
    // verification against a different root MUST fail (no fake membership).
    transfer.merkle_root = transfer.merkle_root + BabyBear::ONE;
    let res = transfer.verify_stark_side();
    assert!(
        matches!(res, Err(ShieldedError::InputProofRejected { .. })),
        "a shielded transfer presented against the wrong root must reject, got {res:?}"
    );
}

#[test]
fn unbalanced_value_commitments_reject() {
    let (transfer, in_c, _out_c) = balanced_transfer();
    // Forge an output committing to MORE than the input (inflation). The excess
    // now has a nonzero V-component, so the Schnorr-on-R proof cannot answer.
    let inflated = 2_000_000u64;
    let r_out = [7u8; 32];
    let bad_out = ValueCommitment::commit(inflated, &scalar_from_blinding_bytes(&r_out));

    let r_in = scalar_from_blinding_bytes(&[3u8; 32]);
    let r_out_s = scalar_from_blinding_bytes(&r_out);
    let excess = r_in - r_out_s; // prover still uses the blinding excess
    let msg = transfer.transfer_message();
    let proof = prove_conservation(&[in_c.clone()], &[bad_out.clone()], &excess, &msg);
    let res = verify_conservation(&[in_c], &[bad_out], &proof, &msg);
    assert!(
        res.is_err(),
        "an inflating (unbalanced) value-commitment set must NOT conserve"
    );
}

// ── TRUE: a balanced, in-range transfer passes the FULL (conservation + range)
//          verifier ───────────────────────────────────────────────────────────

#[test]
fn balanced_in_range_transfer_full_verifies() {
    let (transfer, in_c, out_c) = balanced_transfer();

    // The structural gate: one range proof per output.
    transfer
        .check_range_proof_shape()
        .expect("balanced transfer has a range proof per output");

    // The Schnorr excess proof over the SAME message that binds the range proofs.
    let r_in = scalar_from_blinding_bytes(&[3u8; 32]);
    let r_out = scalar_from_blinding_bytes(&[7u8; 32]);
    let excess = r_in - r_out;
    let msg = transfer.transfer_message();
    let conservation = prove_conservation(&[in_c.clone()], &[out_c.clone()], &excess, &msg);

    // The COMPLETE value-side acceptance: conservation AND every output's range
    // proof. This is what closes the inflation hole.
    verify_full_conservation_bytes(
        &transfer.input_commitment_bytes(),
        &transfer.output_commitment_bytes(),
        &conservation,
        &transfer.output_range_proofs,
        &msg,
    )
    .expect("a balanced, in-range transfer must pass the full conservation+range verifier");
}

// ── FALSE: the NEGATIVE-VALUE (mod-order wrap) inflation attack the Schnorr
//           excess proof alone CANNOT catch — now REJECTED by the range proof ──

#[test]
fn negative_output_value_wraps_and_is_caught_by_range_proof() {
    // The attack: one honest input of `amount`. The attacker mints TWO outputs:
    //   out_big  = commit(amount + STEAL)         — real spendable value, inflated
    //   out_neg  = commit(-STEAL mod l)           — a scalar-field-WRAPPED negative
    // Σ C_out = commit(amount + STEAL) + commit(-STEAL) = commit(amount) (in the
    // group), so the Schnorr conservation proof BALANCES and ACCEPTS — yet the
    // attacker walks away with `amount + STEAL` of genuinely spendable value while
    // only putting in `amount`. This is hidden inflation, light-client-unfoolable.
    //
    // The range proof is the tooth: `out_neg`'s value is NOT in [0, 2^64), so its
    // Bulletproof cannot be produced for the true (wrapped) value, and verifying a
    // proof for any in-range value against `out_neg` FAILS the commitment check.
    let amount: u64 = 1_000_000;
    let steal: u64 = 5_000_000;

    let in_blinding = [3u8; 32];
    let bo_big = [7u8; 32];
    let bo_neg = [11u8; 32];

    let w = make_input(11, amount as u32, in_blinding, 0xABCD, 4);
    let merkle_root = w.spend.merkle_root();

    let in_c = ValueCommitment::commit(amount, &scalar_from_blinding_bytes(&in_blinding));

    // out_big commits to the inflated value; out_neg commits to the negative
    // (wrapped) value so the GROUP sum still balances.
    let neg_scalar = -Scalar::from(steal); // = (l - steal) mod l, a huge scalar
    let out_big = ValueCommitment::commit(amount + steal, &scalar_from_blinding_bytes(&bo_big));
    let out_neg = ValueCommitment {
        point: neg_scalar * dregg_cell_crypto::value_commitment::value_generator()
            + scalar_from_blinding_bytes(&bo_neg)
                * dregg_cell_crypto::value_commitment::randomness_generator(),
    };

    let output_legs = vec![
        ShieldedValueLeg { asset_type: ASSET, commitment_bytes: out_big.to_bytes().0 },
        ShieldedValueLeg { asset_type: ASSET, commitment_bytes: out_neg.to_bytes().0 },
    ];

    // The attacker CANNOT make a valid range proof for `out_neg`'s wrapped value
    // (it is not a 64-bit value). The best forgery available is a range proof for
    // SOME in-range value with `bo_neg` — but that proof's implicit commitment
    // (v'·V + bo_neg·R) does not equal `out_neg` (whose value is the wrapped
    // scalar), so the Bulletproof commitment binding rejects it. We hand it a
    // proof for value 0 with `bo_neg` (the most plausible forgery) and check it
    // still fails.
    let forged_neg_rp = range_proof_bytes(0, &bo_neg);
    let output_range_proofs =
        vec![range_proof_bytes(amount + steal, &bo_big), forged_neg_rp];

    let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        merkle_root,
        &[w],
        output_legs,
        output_range_proofs,
    )
    .expect("STARK proofs build even for an inflating transfer (caught at value verify)");

    // STARK side + range-proof shape are both fine — the attack is value-side only.
    transfer.verify_stark_side().expect("STARK membership still verifies");
    transfer.check_range_proof_shape().expect("shape ok: 2 outputs, 2 range proofs");

    // The Schnorr conservation proof BALANCES (the group sum is commit(amount)).
    let excess = scalar_from_blinding_bytes(&in_blinding)
        - (scalar_from_blinding_bytes(&bo_big) + scalar_from_blinding_bytes(&bo_neg));
    let msg = transfer.transfer_message();
    let conservation =
        prove_conservation(&[in_c.clone()], &[out_big.clone(), out_neg.clone()], &excess, &msg);
    // Demonstrate the hole the range proof closes: conservation ALONE accepts.
    verify_conservation(&[in_c.clone()], &[out_big.clone(), out_neg.clone()], &conservation, &msg)
        .expect("conservation alone is FOOLED by the wrapped-negative output (the hole)");

    // The FULL verifier (conservation + range) REJECTS — the range proof bites.
    let res = verify_full_conservation_bytes(
        &transfer.input_commitment_bytes(),
        &transfer.output_commitment_bytes(),
        &conservation,
        &transfer.output_range_proofs,
        &msg,
    );
    assert!(
        matches!(
            res,
            Err(FullConservationError::RangeProofFailed { output_index: 1, .. })
        ),
        "the wrapped-negative output must be REJECTED by its range proof, got {res:?}"
    );
}

// ── FALSE: a transfer that simply DROPS an output's range proof is rejected at
//           the structural shape gate (cannot escape the bound by omission) ────

#[test]
fn missing_output_range_proof_rejects() {
    let amount: u64 = 1_000_000;
    let in_blinding = [3u8; 32];
    let bo = [7u8; 32];
    let w = make_input(11, amount as u32, in_blinding, 0xABCD, 4);
    let merkle_root = w.spend.merkle_root();
    let out_c = ValueCommitment::commit(amount, &scalar_from_blinding_bytes(&bo));
    let output_legs = vec![ShieldedValueLeg { asset_type: ASSET, commitment_bytes: out_c.to_bytes().0 }];

    // Build with the proof present (valid), then strip it to model the attack.
    let mut transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        merkle_root,
        &[w],
        output_legs,
        vec![range_proof_bytes(amount, &bo)],
    )
    .expect("build");
    transfer.output_range_proofs.clear(); // attacker drops the range proof

    let res = transfer.check_range_proof_shape();
    assert!(
        matches!(res, Err(ShieldedError::RangeProofCountMismatch { outputs: 1, range_proofs: 0 })),
        "a transfer dropping an output's range proof must reject structurally, got {res:?}"
    );
}

#[test]
fn duplicate_nullifier_in_transfer_rejects() {
    // Two inputs that share a nullifier (same note spent twice in one transfer).
    let amount = 500_000u32;
    let in_blinding = [3u8; 32];
    let w1 = make_input(21, amount, in_blinding, 0x1111, 4);
    // Same owner/key/nonce/randomness -> same note -> same nullifier.
    let w2 = make_input(21, amount, in_blinding, 0x1111, 4);
    assert_eq!(
        w1.spend.nullifier(),
        w2.spend.nullifier(),
        "identical notes must produce identical nullifiers"
    );
    // Both pinned to the same root.
    let merkle_root = w1.spend.merkle_root();

    let out_leg = vec![ShieldedValueLeg {
        asset_type: ASSET,
        commitment_bytes: ValueCommitment::commit(
            (2 * amount) as u64,
            &scalar_from_blinding_bytes(&[9u8; 32]),
        )
        .to_bytes()
        .0,
    }];

    let out_rps = vec![range_proof_bytes((2 * amount) as u64, &[9u8; 32])];
    let transfer =
        dregg_circuit_prove::shielded::transfer_from_witnesses(merkle_root, &[w1, w2], out_leg, out_rps)
            .expect("STARK proofs build even for a double-spend (caught at verify)");

    let res = transfer.verify_stark_side();
    assert!(
        matches!(res, Err(ShieldedError::DuplicateNullifier { .. })),
        "a transfer spending the same nullifier twice must reject, got {res:?}"
    );
}

#[test]
fn no_inputs_rejects() {
    let res = dregg_circuit_prove::shielded::transfer_from_witnesses(BabyBear::ZERO, &[], vec![], vec![]);
    assert!(matches!(res, Err(ShieldedError::NoInputs)));
}

// ── THE LEAF↔LEG VALUE LINK (both polarities) ───────────────────────────────
//
// The shielded-spend STARK publishes `value_binding = hash_fact(value,
// [randomness, 0, 0])` (C7), bound into `transfer_message()`. The cell-layer
// `verify_value_link` ties that to the Pedersen leg by checking ONE `(value,
// randomness, blinding)` opening reproduces BOTH the STARK binding AND the leg.
// Before this, the STARK leaf value and the Pedersen leg value were unlinked: a
// spender could prove membership of a note worth V while the Pedersen leg balanced
// a DIFFERENT V'.

#[test]
fn leaf_leg_value_link_matches_verifies_mismatch_rejects() {
    // Build one input: the STARK witnesses value=amount/randomness; the leg is the
    // Pedersen commitment to the SAME amount.
    let amount = 1_000_000u32;
    let in_blinding = [3u8; 32];
    let w = make_input(11, amount, in_blinding, 0xABCD, 4);

    // The transfer surfaces the input's value_binding PI = the witness binding.
    let merkle_root = w.spend.merkle_root();
    let randomness = w.spend.randomness;
    let leg_bytes = w.leg.commitment_bytes;
    let out_blinding = [7u8; 32];
    let out_commit =
        ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&out_blinding));
    let output_legs = vec![ShieldedValueLeg {
        asset_type: ASSET,
        commitment_bytes: out_commit.to_bytes().0,
    }];
    let output_range_proofs = vec![range_proof_bytes(amount as u64, &out_blinding)];
    let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        merkle_root,
        &[w],
        output_legs,
        output_range_proofs,
    )
    .expect("build");
    transfer.verify_stark_side().expect("STARK side (incl. C7 value-binding PI) verifies");

    let value_binding = transfer.inputs[0].value_binding;

    // TRUE: the genuine opening (amount, randomness, in_blinding) reproduces BOTH
    // the STARK value-binding AND the Pedersen leg → the link holds.
    verify_value_link(
        value_binding,
        &leg_bytes,
        amount as u64,
        randomness,
        &scalar_from_blinding_bytes(&in_blinding),
    )
    .expect("the genuine leaf value and the leg value must link");

    // FALSE (the splice): a leg committing to a DIFFERENT value than the STARK leaf.
    // Whatever opening the attacker offers, it cannot satisfy both equations: an
    // opening matching the STARK binding (value=amount) does NOT commit to this
    // inflated leg, and an opening matching the inflated leg does NOT reproduce the
    // STARK binding. We exhibit both failing branches.
    let inflated = 2_000_000u64;
    let inflated_leg =
        ValueCommitment::commit(inflated, &scalar_from_blinding_bytes(&in_blinding))
            .to_bytes()
            .0;
    // Branch A: keep the STARK-consistent opening (value=amount) → leg mismatch.
    let res_a = verify_value_link(
        value_binding,
        &inflated_leg,
        amount as u64,
        randomness,
        &scalar_from_blinding_bytes(&in_blinding),
    );
    assert!(
        matches!(res_a, Err(ValueLinkError::LegMismatch)),
        "an inflated leg cannot link to the STARK leaf value (leg mismatch), got {res_a:?}"
    );
    // Branch B: switch the opening to the inflated leg's value → binding mismatch
    // (the STARK published value_binding is for `amount`, not `inflated`).
    let res_b = verify_value_link(
        value_binding,
        &inflated_leg,
        inflated,
        randomness,
        &scalar_from_blinding_bytes(&in_blinding),
    );
    assert!(
        matches!(res_b, Err(ValueLinkError::BindingMismatch)),
        "an opening for the inflated value cannot reproduce the STARK binding, got {res_b:?}"
    );
}

#[test]
fn tampered_nullifier_rejects() {
    // The published nullifier must match what the hidden proof derived. Swapping
    // it for any other value breaks the row-0 nullifier binding boundary.
    let (mut transfer, _in_c, _out_c) = balanced_transfer();
    transfer.inputs[0].nullifier = transfer.inputs[0].nullifier + BabyBear::ONE;
    let res = transfer.verify_stark_side();
    assert!(
        matches!(res, Err(ShieldedError::InputProofRejected { .. })),
        "a transfer presenting a nullifier the proof did not derive must reject, got {res:?}"
    );
}

#[test]
fn shielded_proof_is_hiding_independent_blinding() {
    // Two ZK proofs of the SAME shielded spend must differ (fresh blinding each
    // time) — if byte-identical, the blinding RNG would be deterministic and the
    // witness could leak via cross-proof comparison. Both still verify.
    use dregg_circuit::dsl::dsl_p3_air::prove_dsl_zk;
    use dregg_circuit_prove::shielded::{generate_shielded_spend_trace, shielded_spend_circuit};

    let w = make_input(99, 250_000, [5u8; 32], 0x2222, 4);
    let circuit = shielded_spend_circuit();
    let (trace, pis) = generate_shielded_spend_trace(&w.spend);

    let p1 = prove_dsl_zk(&circuit, &trace, &pis).expect("zk prove 1");
    let p2 = prove_dsl_zk(&circuit, &trace, &pis).expect("zk prove 2");

    let b1 = postcard::to_allocvec(&p1).expect("ser p1");
    let b2 = postcard::to_allocvec(&p2).expect("ser p2");
    assert_ne!(
        b1, b2,
        "two ZK proofs of the same shielded spend must use independent blinding (hiding)"
    );
}

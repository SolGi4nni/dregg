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
//!   STARK side    — balanced transfer VERIFIES (blind) under the COMMITTED root;
//!                   a spend judged under a root that is not the tree it folded to REJECTS
//!                   (seam #15 — `ShieldedMerkleRootPin.pin_rejects_root_substitution`);
//!                   duplicate / tampered nullifier REJECTS.
//!   Pedersen side — balanced value commitments VERIFY (blind);
//!                   an unbalanced set (inflation) REJECTS.

// NOTE: this file previously carried `#![cfg(feature = "prover")]`, the SAME vestigial
// gate `ivc_turn_chain_rotated.rs` / `joint_turn_recursive_rotated.rs` documented and
// removed — `dregg-circuit-prove` defines NO features at all, so the gate was
// UNSATISFIABLE: the entire file compiled out (0 tests) in every possible
// configuration and every shielded-transfer soundness tooth here was silently dead
// (found 2026-07-16, Lane 2 config-space audit). The prover is unconditional in this
// crate; the gate is removed so the teeth compile and run.

//! ⚑ FLAG DAY 2026-08-07 — the spend side is the Lean-emitted COMPLETE spend
//! (`dregg-shielded-spend-complete-fsi2::v1`, `ShieldedSpendCompleteEmit.lean`) over a REAL
//! `ShieldedNoteSet`, and `ShieldedTransfer` has no `merkle_root` field. The root is an argument
//! to `verify_stark_side`, supplied by the executor from `note_shielded.root8()`.

use dregg_cell::{ShieldedNoteCommitment, ShieldedNoteSet, felt_to_bytes32};
use dregg_circuit::exact_nullifier_aafi::{Digest8, TaggedKeyWire};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, ShieldedError, ShieldedSpendCompleteWitness, ShieldedSpendMembership,
    ShieldedTransfer, ShieldedTransferWitness, ShieldedValueLeg, TREE_DEPTH,
    WideValueBindingWitness,
};

use curve25519_dalek::scalar::Scalar;
use dregg_cell_crypto::value_commitment::{
    BulletproofRangeProof, FullConservationError, ValueCommitment, ValueLinkError,
    prove_conservation, scalar_from_blinding_bytes, verify_conservation,
    verify_full_conservation_bytes, verify_value_link,
};

const ASSET: u64 = 1;

/// Build a real Bulletproof range proof (serialized bytes) for one output value.
fn range_proof_bytes(value: u64, blinding: &[u8; 32]) -> Vec<u8> {
    BulletproofRangeProof::prove_range(value, &scalar_from_blinding_bytes(blinding)).proof_bytes
}

/// Build a COMPLETE-spend witness whose note is a GENUINE member of a fresh `ShieldedNoteSet`,
/// plus the published value-commitment leg for it — and return the set, because the tree the
/// spend folded to is now a verification argument rather than a payload field.
///
/// The leaf is `felt_to_bytes32(hash_fact(v mod p, [a mod p, owner, rand]))`, exactly the 32-byte
/// commitment a `dregg-shielded-shield::v1` mint appends. (The leaf↔value-leg value link remains
/// the named residual; see `leaf_leg_value_link_matches_verifies_mismatch_rejects`.)
fn make_input(
    leaf_seed: u32,
    amount: u32,
    blinding: [u8; 32],
    key_seed: u32,
) -> (ShieldedTransferWitness, ShieldedNoteSet) {
    let (witness, set) = spend_in_set(amount as u64, key_seed, leaf_seed);
    let commitment = ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&blinding));
    (
        ShieldedTransferWitness {
            spend: witness,
            leg: ShieldedValueLeg {
                asset_type: ASSET,
                commitment_bytes: commitment.to_bytes().0,
            },
        },
        set,
    )
}

/// A complete-spend witness genuinely committed in a fresh `ShieldedNoteSet` (one decoy + the
/// note), aimed at that set's real `root8()`.
fn spend_in_set(
    amount: u64,
    key_seed: u32,
    leaf_seed: u32,
) -> (ShieldedSpendCompleteWitness, ShieldedNoteSet) {
    let probe = ShieldedSpendCompleteWitness {
        value: amount,
        asset_type: ASSET,
        randomness: BabyBear::new(0xC0FFEE ^ key_seed),
        spending_key: [
            BabyBear::new(key_seed),
            BabyBear::new(key_seed.wrapping_add(1)),
            BabyBear::new(key_seed.wrapping_add(2)),
            BabyBear::new(key_seed.wrapping_add(3)),
        ],
        binding_blind: core::array::from_fn(|i| BabyBear::new(0x5EED ^ leaf_seed ^ i as u32)),
        membership: ShieldedSpendMembership {
            positions: [0; TREE_DEPTH],
            siblings: [[[BabyBear::ZERO; 8]; 3]; TREE_DEPTH],
            next_addr: TaggedKeyWire::top(),
        },
    };
    let commitment = ShieldedNoteCommitment(felt_to_bytes32(probe.note_commitment_felt()));
    let mut set = ShieldedNoteSet::new();
    set.insert(ShieldedNoteCommitment(felt_to_bytes32(BabyBear::new(
        0x0A0A_0000 + leaf_seed,
    ))))
    .expect("decoy inserts");
    set.insert(commitment).expect("the spent note is committed");
    let path = set
        .membership_path(&commitment)
        .expect("the committed note has a membership path");
    let witness = ShieldedSpendCompleteWitness {
        membership: ShieldedSpendMembership {
            positions: path.path.positions,
            siblings: path.path.siblings,
            next_addr: path.leaf.next_addr().wire(),
        },
        ..probe
    };
    (witness, set)
}

/// A committed root that is NOT the tree any of these spends folded to — the foreign root the
/// seam-#15 refusal is exhibited against.
fn foreign_root() -> Digest8 {
    ShieldedNoteSet::new().root8().limbs()
}

/// Construct a balanced shielded transfer (STARK side) from ONE input, pinned to
/// that input's real DSL Merkle root, with one output leg of equal value.
/// Returns (transfer, in_blinding, out_blinding, out_commitment) so the caller
/// can drive the Pedersen conservation proof.
fn balanced_transfer() -> (ShieldedTransfer, ValueCommitment, ValueCommitment, Digest8) {
    let amount = 1_000_000u32;
    let in_blinding = [3u8; 32];
    let out_blinding = [7u8; 32];

    let (w, set) = make_input(11, amount, in_blinding, 0xABCD);
    let committed_root = set.root8().limbs();

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
        &[w],
        output_legs,
        output_range_proofs,
    )
    .expect("prove balanced shielded transfer STARK side");

    (transfer, in_commit, out_commit, committed_root)
}

#[test]
fn balanced_shielded_transfer_stark_side_verifies_blind() {
    let (transfer, _in_c, _out_c, root) = balanced_transfer();
    // The hidden membership+nullifier proof verifies against the COMMITTED root,
    // revealing nothing about value/asset/owner/key/path.
    transfer
        .verify_stark_side(root)
        .expect("balanced shielded transfer STARK side must verify");
    assert_eq!(transfer.nullifiers().len(), 1);
}

#[test]
fn balanced_shielded_transfer_pedersen_side_verifies_blind() {
    let (transfer, in_c, out_c, root) = balanced_transfer();
    // excess_blinding = r_in - r_out (the prover knows both).
    let r_in = scalar_from_blinding_bytes(&[3u8; 32]);
    let r_out = scalar_from_blinding_bytes(&[7u8; 32]);
    let excess = r_in - r_out;
    let msg = transfer.transfer_message(root);
    let proof = prove_conservation(&[in_c.clone()], &[out_c.clone()], &excess, &msg);
    // Value balance certified WITHOUT revealing the amount.
    verify_conservation(&[in_c], &[out_c], &proof, &msg)
        .expect("balanced value commitments must conserve");
}

/// **⚑ SEAM #15 at the object layer.** There is no root to tamper — the retired test bumped
/// `transfer.merkle_root` by one, which `ShieldedMerkleRootPin.mutation_test_is_not_the_pin` names
/// as a LAUNDER: it rejects root-mutation-without-reproof, and the attacker never mutates.
///
/// The real shape: the SAME genuine, unmutated transfer is judged under a committed root that is
/// not the tree it folded to. Both poles in one test, so the accept is the non-vacuity guard for
/// the refusal.
#[test]
fn spend_judged_under_a_foreign_committed_root_rejects() {
    let (transfer, _in_c, _out_c, root) = balanced_transfer();
    transfer
        .verify_stark_side(root)
        .expect("ACCEPT POLE: under its own committed root the transfer verifies");
    assert_ne!(
        root,
        foreign_root(),
        "vacuity guard: the foreign root must genuinely differ from the committed one"
    );
    let res = transfer.verify_stark_side(foreign_root());
    assert!(
        matches!(res, Err(ShieldedError::InputProofRejected { .. })),
        "a spend judged under a root it did not fold to must reject — this is the pin, got {res:?}"
    );
}

#[test]
fn unbalanced_value_commitments_reject() {
    let (transfer, in_c, _out_c, root) = balanced_transfer();
    // Forge an output committing to MORE than the input (inflation). The excess
    // now has a nonzero V-component, so the Schnorr-on-R proof cannot answer.
    let inflated = 2_000_000u64;
    let r_out = [7u8; 32];
    let bad_out = ValueCommitment::commit(inflated, &scalar_from_blinding_bytes(&r_out));

    let r_in = scalar_from_blinding_bytes(&[3u8; 32]);
    let r_out_s = scalar_from_blinding_bytes(&r_out);
    let excess = r_in - r_out_s; // prover still uses the blinding excess
    let msg = transfer.transfer_message(root);
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
    let (transfer, in_c, out_c, root) = balanced_transfer();

    // The structural gate: one range proof per output.
    transfer
        .check_range_proof_shape()
        .expect("balanced transfer has a range proof per output");

    // The Schnorr excess proof over the SAME message that binds the range proofs.
    let r_in = scalar_from_blinding_bytes(&[3u8; 32]);
    let r_out = scalar_from_blinding_bytes(&[7u8; 32]);
    let excess = r_in - r_out;
    let msg = transfer.transfer_message(root);
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

    let (w, set) = make_input(11, amount as u32, in_blinding, 0xABCD);
    let committed_root = set.root8().limbs();

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
        ShieldedValueLeg {
            asset_type: ASSET,
            commitment_bytes: out_big.to_bytes().0,
        },
        ShieldedValueLeg {
            asset_type: ASSET,
            commitment_bytes: out_neg.to_bytes().0,
        },
    ];

    // The attacker CANNOT make a valid range proof for `out_neg`'s wrapped value
    // (it is not a 64-bit value). The best forgery available is a range proof for
    // SOME in-range value with `bo_neg` — but that proof's implicit commitment
    // (v'·V + bo_neg·R) does not equal `out_neg` (whose value is the wrapped
    // scalar), so the Bulletproof commitment binding rejects it. We hand it a
    // proof for value 0 with `bo_neg` (the most plausible forgery) and check it
    // still fails.
    let forged_neg_rp = range_proof_bytes(0, &bo_neg);
    let output_range_proofs = vec![range_proof_bytes(amount + steal, &bo_big), forged_neg_rp];

    let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        &[w],
        output_legs,
        output_range_proofs,
    )
    .expect("STARK proofs build even for an inflating transfer (caught at value verify)");

    // STARK side + range-proof shape are both fine — the attack is value-side only.
    transfer
        .verify_stark_side(committed_root)
        .expect("STARK membership still verifies");
    transfer
        .check_range_proof_shape()
        .expect("shape ok: 2 outputs, 2 range proofs");

    // The Schnorr conservation proof BALANCES (the group sum is commit(amount)).
    let excess = scalar_from_blinding_bytes(&in_blinding)
        - (scalar_from_blinding_bytes(&bo_big) + scalar_from_blinding_bytes(&bo_neg));
    let msg = transfer.transfer_message(committed_root);
    let conservation = prove_conservation(
        &[in_c.clone()],
        &[out_big.clone(), out_neg.clone()],
        &excess,
        &msg,
    );
    // Demonstrate the hole the range proof closes: conservation ALONE accepts.
    verify_conservation(
        &[in_c.clone()],
        &[out_big.clone(), out_neg.clone()],
        &conservation,
        &msg,
    )
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
            Err(FullConservationError::RangeProofFailed {
                output_index: 1,
                ..
            })
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
    let (w, _set) = make_input(11, amount as u32, in_blinding, 0xABCD);
    let out_c = ValueCommitment::commit(amount, &scalar_from_blinding_bytes(&bo));
    let output_legs = vec![ShieldedValueLeg {
        asset_type: ASSET,
        commitment_bytes: out_c.to_bytes().0,
    }];

    // Build with the proof present (valid), then strip it to model the attack.
    let mut transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        &[w],
        output_legs,
        vec![range_proof_bytes(amount, &bo)],
    )
    .expect("build");
    transfer.output_range_proofs.clear(); // attacker drops the range proof

    let res = transfer.check_range_proof_shape();
    assert!(
        matches!(
            res,
            Err(ShieldedError::RangeProofCountMismatch {
                outputs: 1,
                range_proofs: 0
            })
        ),
        "a transfer dropping an output's range proof must reject structurally, got {res:?}"
    );
}

#[test]
fn duplicate_nullifier_in_transfer_rejects() {
    // Two inputs that share a nullifier (same note spent twice in one transfer).
    let amount = 500_000u32;
    let in_blinding = [3u8; 32];
    let (w1, set) = make_input(21, amount, in_blinding, 0x1111);
    // Same key/randomness/value/asset -> same note commitment -> same nullifier. The SAME witness
    // is used twice, so this is one note presented twice in one transfer.
    let w2 = w1.clone();
    assert_eq!(
        w1.spend.note_commitment_felt(),
        w2.spend.note_commitment_felt(),
        "identical notes must produce identical commitments (hence identical nullifiers)"
    );
    let committed_root = set.root8().limbs();

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
        dregg_circuit_prove::shielded::transfer_from_witnesses(&[w1, w2], out_leg, out_rps)
            .expect("STARK proofs build even for a double-spend (caught at verify)");
    assert_eq!(
        transfer.inputs[0].nullifier, transfer.inputs[1].nullifier,
        "MUTATION PRESENT: both inputs really do reveal the same nullifier"
    );

    let res = transfer.verify_stark_side(committed_root);
    assert!(
        matches!(res, Err(ShieldedError::DuplicateNullifier { .. })),
        "a transfer spending the same nullifier twice must reject, got {res:?}"
    );
}

#[test]
fn no_inputs_rejects() {
    let res = dregg_circuit_prove::shielded::transfer_from_witnesses(&[], vec![], vec![]);
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
    let (w, set) = make_input(11, amount, in_blinding, 0xABCD);

    let committed_root = set.root8().limbs();
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
        &[w],
        output_legs,
        output_range_proofs,
    )
    .expect("build");
    transfer
        .verify_stark_side(committed_root)
        .expect("STARK side verifies under the committed root");

    // ⚑ The complete spend publishes no one-felt `value_binding` PI — the retired spend circuit's
    // C7 is gone, replaced by the sixteen-lane wide carrier. The one-felt tag this residual test is
    // about is now the WIDE SIDECAR's PI 0 (`legacy_binding`), which is the byte-identical
    // `hash_fact(v mod p, [a mod p, rand, 0])` that `value_link_binding` computes.
    let value_binding = WideValueBindingWitness {
        value: amount as u64,
        asset_type: ASSET,
        legacy_randomness: randomness,
        binding_blind: [BabyBear::ZERO; BINDING_BLIND_LANES],
    }
    .legacy_binding();

    // TRUE: the genuine opening (amount, randomness, in_blinding) reproduces BOTH
    // the STARK value-binding AND the Pedersen leg → the link holds.
    verify_value_link(
        value_binding,
        &leg_bytes,
        amount as u64,
        ASSET,
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
    let inflated_leg = ValueCommitment::commit(inflated, &scalar_from_blinding_bytes(&in_blinding))
        .to_bytes()
        .0;
    // Branch A: keep the STARK-consistent opening (value=amount) → leg mismatch.
    let res_a = verify_value_link(
        value_binding,
        &inflated_leg,
        amount as u64,
        ASSET,
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
        ASSET,
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
    // it for any other value breaks the Lean `nulPin` boundary.
    let (mut transfer, _in_c, _out_c, root) = balanced_transfer();
    transfer.inputs[0].nullifier = transfer.inputs[0].nullifier + BabyBear::ONE;
    let res = transfer.verify_stark_side(root);
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
    use dregg_circuit_prove::shielded::prove_shielded_spend_complete;

    let (w, _set) = make_input(99, 250_000, [5u8; 32], 0x2222);

    let p1 = prove_shielded_spend_complete(&w.spend).expect("zk prove 1");
    let p2 = prove_shielded_spend_complete(&w.spend).expect("zk prove 2");
    assert_eq!(p1.claim, p2.claim, "the public claim is deterministic");

    let b1 = postcard::to_allocvec(&p1.proof).expect("ser p1");
    let b2 = postcard::to_allocvec(&p2.proof).expect("ser p2");
    assert_ne!(
        b1, b2,
        "two ZK proofs of the same shielded spend must use independent blinding (hiding)"
    );
}

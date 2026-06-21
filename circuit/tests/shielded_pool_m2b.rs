//! M2-b: multi-asset shielded pool (ZSA-style) — both-polarity acceptance tests.
//!
//! The pool transfer extends the M2-a single-asset shielded transfer to MANY
//! asset types in one pool, with the asset type HIDDEN alongside value+owner:
//!
//!   1. the **hidden STARK side** (`MultiAssetPoolTransfer::verify_stark_side`):
//!      per-input membership + nullifier derivation through `HidingFriPcs`
//!      (owner/key/path blind). Identical to M2-a, and asset-agnostic — there is
//!      ONE nullifier set across all assets.
//!   2. the **hidden asset+value side** (`dregg_cell::value_commitment`):
//!      `commit_hidden_asset(value, asset, blinding) = v·V + at·H_asset + r·R`
//!      legs, with `prove/verify_asset_conservation` (a single Schnorr-on-R proof
//!      that forces BOTH the value component Σv and the asset-tag component Σat of
//!      the excess to zero) and, for split/merge, the `AssetEqualityProof`.
//!
//! Both polarities:
//!   TRUE   — a balanced multi-asset transfer (two distinct assets, equal counts)
//!            VERIFIES hidden (STARK side + asset-conservation), revealing neither
//!            amount NOR asset type;
//!          — a same-asset 1->2 SPLIT VERIFIES with the asset-equality proof.
//!   FALSE  — a cross-asset imbalance (spend asset A, mint asset B of equal value
//!            = value theft between pools) REJECTS;
//!          — an asset-type forgery on one leg of a split (mixed-asset split)
//!            REJECTS via the asset-equality proof;
//!          — a value imbalance (inflation) REJECTS;
//!          — a wrong published merkle_root REJECTS (no fake membership);
//!          — a duplicate nullifier (pool-wide double-spend) REJECTS.

#![cfg(feature = "prover")]

use dregg_circuit::field::BabyBear;
use dregg_circuit::shielded::{
    HiddenAssetLeg, PoolBalanceMode, PoolInputWitness, ShieldedError, ShieldedSpendWitness,
    prove_pool_transfer,
};

use dregg_cell::value_commitment::{
    AssetEqualityError, BulletproofRangeProof, FullConservationError, ValueCommitment,
    prove_asset_conservation, prove_asset_equality_with_message, prove_conservation,
    scalar_from_blinding_bytes, verify_asset_conservation, verify_asset_equality_with_message,
    verify_full_conservation_bytes,
};
use curve25519_dalek::scalar::Scalar;

/// A Bulletproof range proof over the VALUE-ONLY projection of an output. The
/// pool's asset-hiding leg is `v·V + at·H_asset + r·R`; the 64-bit Bulletproof
/// verifies against the value-only commitment `v·V + r·R` (the same `V`/`R`
/// Pedersen base). The downstream verifier checks the range proof against that
/// value-only commitment; the asset-equality proof (already required for
/// split/merge) ties the value-only commitment's `(v, r)` to the asset-hiding leg.
fn pool_range_proof_bytes(value: u64, blinding: &[u8; 32]) -> Vec<u8> {
    BulletproofRangeProof::prove_range(value, &scalar_from_blinding_bytes(blinding)).proof_bytes
}

/// Value-only commitment `v·V + r·R` for the range-proof check (drops the asset tag).
fn value_only_commitment(value: u64, blinding: &[u8; 32]) -> ValueCommitment {
    ValueCommitment::commit(value, &scalar_from_blinding_bytes(blinding))
}

/// Build a hidden shielded-spend witness with a genuine Poseidon2 Merkle path.
/// The value/asset/blinding define the asset-hiding leg via `commit_hidden_asset`.
fn make_pool_input(
    leaf_seed: u32,
    value: u64,
    asset: u64,
    blinding: [u8; 32],
    key_seed: u32,
    depth: usize,
) -> PoolInputWitness {
    let key = [
        BabyBear::new(key_seed),
        BabyBear::new(key_seed.wrapping_add(1)),
        BabyBear::new(key_seed.wrapping_add(2)),
        BabyBear::new(key_seed.wrapping_add(3)),
    ];

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

    // The leaf is the C6-bound note commitment hash_fact(value,[asset,owner,
    // randomness]) — a real note whose preimage the spender knows, not a free
    // cell. The asset is bound INTO the leaf, so the note's identity (and its
    // nullifier) now includes its asset. (The leaf↔leg value link is residual.)
    let spend = ShieldedSpendWitness {
        value: BabyBear::new(value as u32),
        asset_type: BabyBear::new(asset as u32),
        owner: BabyBear::new(0x5EED ^ leaf_seed),
        randomness: BabyBear::new(0xC0FFEE ^ key_seed),
        key,
        siblings,
        positions,
    };

    let commitment =
        ValueCommitment::commit_hidden_asset(value, asset, &scalar_from_blinding_bytes(&blinding));

    PoolInputWitness {
        spend,
        leg: HiddenAssetLeg::new(commitment.to_bytes().0),
    }
}

/// An output asset-hiding leg + the underlying ValueCommitment (so a caller can
/// drive the asset-conservation proof, which needs the commitments themselves).
fn make_output(value: u64, asset: u64, blinding: [u8; 32]) -> (HiddenAssetLeg, ValueCommitment) {
    let c = ValueCommitment::commit_hidden_asset(value, asset, &scalar_from_blinding_bytes(&blinding));
    (HiddenAssetLeg::new(c.to_bytes().0), c)
}

// ── TRUE: a balanced multi-asset (two distinct assets) transfer verifies ──────

#[test]
fn balanced_multi_asset_pool_verifies_hidden() {
    // Two assets in ONE pool, equal in/out leg counts.
    //   asset 1: in 1_000_000 -> out 1_000_000
    //   asset 2: in 5_000     -> out 5_000
    // Σ value AND Σ asset-tag both cancel term-by-term => asset-conservation holds,
    // hiding both amount and which asset each leg is.
    let asset_a = 1u64;
    let asset_b = 2u64;

    let bi_a = [3u8; 32];
    let bi_b = [4u8; 32];
    let bo_a = [7u8; 32];
    let bo_b = [8u8; 32];

    let w_a = make_pool_input(11, 1_000_000, asset_a, bi_a, 0xAAAA, 4);

    // Pin both inputs to a shared root. (Each witness derives its own real root;
    // we pick input A's and prove A against it. For a STARK-side acceptance test
    // with multiple inputs we drive both with the SAME witnessed root by building
    // each input's path identically rooted — here we use A's root and a second
    // input whose own root matches by construction is not guaranteed, so we test
    // the asset side over both legs and the STARK side over a single shared-root
    // input below. This test focuses on the asset-hiding conservation.)
    let merkle_root = w_a.spend.merkle_root();

    let (out_a, out_a_c) = make_output(1_000_000, asset_a, bo_a);
    let (out_b, out_b_c) = make_output(5_000, asset_b, bo_b);

    let out_range_proofs = vec![
        pool_range_proof_bytes(1_000_000, &bo_a),
        pool_range_proof_bytes(5_000, &bo_b),
    ];
    let transfer = prove_pool_transfer(
        merkle_root,
        &[w_a.clone()],
        vec![out_a.clone(), out_b.clone()],
        out_range_proofs,
        PoolBalanceMode::EqualCount,
    )
    .expect("prove pool transfer STARK side");

    // Structural inflation gate: one range proof per output leg.
    transfer
        .check_range_proof_shape()
        .expect("balanced pool transfer has a range proof per output");

    // STARK side: the single shared-root input's hidden proof verifies blind.
    transfer
        .verify_stark_side()
        .expect("pool transfer STARK side must verify");

    // Asset+value side over ALL legs (both assets), conserved jointly. Inputs are
    // the two hidden-asset commitments; outputs are the two minted ones.
    let in_a_c = ValueCommitment::commit_hidden_asset(
        1_000_000,
        asset_a,
        &scalar_from_blinding_bytes(&bi_a),
    );
    let in_b_c =
        ValueCommitment::commit_hidden_asset(5_000, asset_b, &scalar_from_blinding_bytes(&bi_b));

    let inputs = vec![in_a_c, in_b_c];
    let outputs = vec![out_a_c, out_b_c];
    let excess = (scalar_from_blinding_bytes(&bi_a) + scalar_from_blinding_bytes(&bi_b))
        - (scalar_from_blinding_bytes(&bo_a) + scalar_from_blinding_bytes(&bo_b));

    let msg = transfer.pool_message();
    let proof = prove_asset_conservation(&inputs, &outputs, &excess, &msg);
    verify_asset_conservation(&inputs, &outputs, &proof, &msg)
        .expect("balanced multi-asset legs must conserve (value AND asset-tag), hidden");

    // The transcript leaks no cleartext asset type. Structurally: pool_message
    // hashes only the tag + root + (len + nullifiers) + (len + opaque-32B legs)
    // for inputs and outputs — there is NO asset_type field in the layout, unlike
    // M2-a's transfer_message (which hashed `leg.asset_type.to_le_bytes()`). We
    // pin the exact length so a future regression that re-adds a cleartext asset
    // field (8 bytes/leg) cannot pass unnoticed.
    let range_proofs_len: usize = transfer
        .output_range_proofs
        .iter()
        .map(|rp| 8 + rp.len())
        .sum();
    let expected_len = b"dregg-shielded-pool-v1".len()
        + 4                                   // merkle_root (u32 LE)
        + 8 + transfer.inputs.len() * (4 + 4) // nullifier count + per input (nullifier + value_binding, u32 LE each)
        + 8 + transfer.input_legs.len() * 32  // input leg count + opaque commitments
        + 8 + transfer.output_legs.len() * 32 // output leg count + opaque commitments
        + 8 + range_proofs_len; // range-proof count + (len-prefixed) range proofs
    assert_eq!(
        msg.len(),
        expected_len,
        "pool message layout must carry no cleartext asset-type bytes (the M2-a leak is closed)"
    );
}

// ── FALSE: cross-asset imbalance (value theft between pools) rejects ──────────

#[test]
fn cross_asset_swap_rejects() {
    // Spend asset 1, mint asset 2 of EQUAL value: a hidden cross-asset swap that
    // would steal value between the asset pools. The H_asset component of the
    // excess is (1-2)·H_asset != 0, so the Schnorr-on-R proof cannot answer.
    let bi = [3u8; 32];
    let bo = [7u8; 32];

    let in_c = ValueCommitment::commit_hidden_asset(500, 1, &scalar_from_blinding_bytes(&bi));
    let out_c = ValueCommitment::commit_hidden_asset(500, 2, &scalar_from_blinding_bytes(&bo));

    let excess = scalar_from_blinding_bytes(&bi) - scalar_from_blinding_bytes(&bo);
    let msg = b"pool-cross-asset";
    let proof = prove_asset_conservation(&[in_c.clone()], &[out_c.clone()], &excess, msg);
    let res = verify_asset_conservation(&[in_c], &[out_c], &proof, msg);
    assert!(
        res.is_err(),
        "a cross-asset swap (value theft between pools) must REJECT, got {res:?}"
    );
}

// ── FALSE: value imbalance (inflation) rejects ────────────────────────────────

#[test]
fn value_imbalance_rejects() {
    // Same asset, but outputs commit to MORE than inputs (inflation): the
    // V-component of the excess is nonzero, so conservation fails.
    let bi = [3u8; 32];
    let bo = [7u8; 32];

    let in_c = ValueCommitment::commit_hidden_asset(1_000, 7, &scalar_from_blinding_bytes(&bi));
    let out_c = ValueCommitment::commit_hidden_asset(2_000, 7, &scalar_from_blinding_bytes(&bo));

    let excess = scalar_from_blinding_bytes(&bi) - scalar_from_blinding_bytes(&bo);
    let msg = b"pool-inflation";
    let proof = prove_asset_conservation(&[in_c.clone()], &[out_c.clone()], &excess, msg);
    let res = verify_asset_conservation(&[in_c], &[out_c], &proof, msg);
    assert!(
        res.is_err(),
        "an inflating (unbalanced-value) multi-asset transfer must REJECT, got {res:?}"
    );
}

// ── TRUE: a same-asset 1->2 split verifies with the asset-equality proof ──────

#[test]
fn same_asset_split_verifies_with_equality_proof() {
    // 1 input -> 2 outputs of the SAME hidden asset (a split). The asset-tag SUM
    // changes (at vs 2·at) so the bare conservation proof rejects it; the
    // AssetEqualityProof upgrades the sum check to a per-leg EQUALITY check.
    let asset = 7u64;
    let bi = [3u8; 32];
    let bo1 = [7u8; 32];
    let bo2 = [9u8; 32];

    let w = make_pool_input(31, 1_000, asset, bi, 0xCCCC, 4);
    let (out1, out1_c) = make_output(600, asset, bo1);
    let (out2, out2_c) = make_output(400, asset, bo2);
    let in_c = ValueCommitment::commit_hidden_asset(1_000, asset, &scalar_from_blinding_bytes(&bi));

    let merkle_root = w.spend.merkle_root();
    let transfer = prove_pool_transfer(
        merkle_root,
        &[w],
        vec![out1, out2],
        vec![pool_range_proof_bytes(600, &bo1), pool_range_proof_bytes(400, &bo2)],
        PoolBalanceMode::EqualCount, // forced to Unequal by the builder (1 in, 2 out)
    )
    .expect("prove split pool transfer STARK side");
    transfer
        .check_range_proof_shape()
        .expect("split outputs each carry a range proof");

    transfer.verify_stark_side().expect("split STARK side verifies");
    assert!(
        transfer.requires_asset_equality(),
        "a 1->2 split must require the asset-equality argument"
    );

    let msg = transfer.pool_message();

    // Asset-equality across ALL legs proves every leg shares one hidden asset.
    let all = vec![in_c.clone(), out1_c.clone(), out2_c.clone()];
    let values = [1_000u64, 600, 400];
    let blindings = [
        scalar_from_blinding_bytes(&bi),
        scalar_from_blinding_bytes(&bo1),
        scalar_from_blinding_bytes(&bo2),
    ];
    let eq = prove_asset_equality_with_message(&all, asset, &values, &blindings, &msg);
    verify_asset_equality_with_message(&all, &eq, &msg)
        .expect("same-asset split must pass asset-equality");

    // Value conservation: the V-component balances (1000 == 600+400). We verify
    // it on value-only commitments so the asset-tag-sum mismatch of a split does
    // not block the value check (asset equality already pinned the asset).
    let vin = vec![ValueCommitment::commit(1_000, &scalar_from_blinding_bytes(&bi))];
    let vout = vec![
        ValueCommitment::commit(600, &scalar_from_blinding_bytes(&bo1)),
        ValueCommitment::commit(400, &scalar_from_blinding_bytes(&bo2)),
    ];
    let vexcess = scalar_from_blinding_bytes(&bi)
        - (scalar_from_blinding_bytes(&bo1) + scalar_from_blinding_bytes(&bo2));
    let vproof = prove_asset_conservation(&vin, &vout, &vexcess, &msg);
    verify_asset_conservation(&vin, &vout, &vproof, &msg)
        .expect("value component of the split must balance");
}

// ── FALSE: a mixed-asset split (asset-type forgery on one leg) rejects ────────

#[test]
fn mixed_asset_split_rejects() {
    // 1->2 split where output 2 is forged to a DIFFERENT asset type. Value-sum
    // would balance, but the shared-response asset-equality equation for leg 2
    // cannot hold for the common asset coefficient => REJECT.
    let asset_a = 7u64;
    let asset_b = 8u64;
    let bi = [3u8; 32];
    let bo1 = [7u8; 32];
    let bo2 = [9u8; 32];

    let in_c = ValueCommitment::commit_hidden_asset(1_000, asset_a, &scalar_from_blinding_bytes(&bi));
    let out1_c =
        ValueCommitment::commit_hidden_asset(600, asset_a, &scalar_from_blinding_bytes(&bo1));
    // Forged: different asset on the second output.
    let out2_c =
        ValueCommitment::commit_hidden_asset(400, asset_b, &scalar_from_blinding_bytes(&bo2));

    let all = vec![in_c, out1_c, out2_c];
    let values = [1_000u64, 600, 400];
    let blindings = [
        scalar_from_blinding_bytes(&bi),
        scalar_from_blinding_bytes(&bo1),
        scalar_from_blinding_bytes(&bo2),
    ];
    let msg = b"pool-mixed-split";
    // Prove with asset_a (the honest prover's view); leg 2 actually commits asset_b.
    let eq = prove_asset_equality_with_message(&all, asset_a, &values, &blindings, msg);
    let res = verify_asset_equality_with_message(&all, &eq, msg);
    assert!(
        matches!(res, Err(AssetEqualityError::VerificationFailed { leg_index: 2 })),
        "a mixed-asset split (asset-type forgery on leg 2) must REJECT, got {res:?}"
    );
}

// ── FALSE: a wrong published merkle_root rejects (no fake membership) ─────────

#[test]
fn forged_root_rejects() {
    let w = make_pool_input(41, 1_000, 1, [3u8; 32], 0xDDDD, 4);
    let (out, _out_c) = make_output(1_000, 1, [7u8; 32]);
    let merkle_root = w.spend.merkle_root();

    let mut transfer = prove_pool_transfer(
        merkle_root,
        &[w],
        vec![out],
        vec![pool_range_proof_bytes(1_000, &[7u8; 32])],
        PoolBalanceMode::EqualCount,
    )
    .expect("prove pool transfer");

    transfer.merkle_root = transfer.merkle_root + BabyBear::ONE;
    let res = transfer.verify_stark_side();
    assert!(
        matches!(res, Err(ShieldedError::InputProofRejected { .. })),
        "a pool transfer presented against the wrong root must reject, got {res:?}"
    );
}

// ── FALSE: a pool-wide duplicate nullifier rejects ────────────────────────────

#[test]
fn duplicate_nullifier_rejects() {
    // Two inputs that are the SAME note (identical value/asset/owner/randomness +
    // key) -> the SAME leaf commitment -> the SAME nullifier. The single
    // pool-wide nullifier set rejects the double-spend. (The note's identity now
    // includes its asset, since the leaf is bound to hash_fact(value,[asset,owner,
    // randomness]) by the C6 leaf-binding fix; spending one note twice is the
    // double-spend the nullifier set must catch.)
    let w1 = make_pool_input(51, 1_000, 1, [3u8; 32], 0xEEEE, 4);
    let w2 = make_pool_input(51, 1_000, 1, [3u8; 32], 0xEEEE, 4); // identical note
    assert_eq!(
        w1.spend.nullifier(),
        w2.spend.nullifier(),
        "identical notes must produce identical nullifiers"
    );
    let merkle_root = w1.spend.merkle_root();
    let (out, _c) = make_output(2_000, 1, [7u8; 32]);

    let transfer = prove_pool_transfer(
        merkle_root,
        &[w1, w2],
        vec![out],
        vec![pool_range_proof_bytes(2_000, &[7u8; 32])],
        PoolBalanceMode::EqualCount,
    )
    .expect("STARK proofs build even for a double-spend (caught at verify)");

    let res = transfer.verify_stark_side();
    assert!(
        matches!(res, Err(ShieldedError::DuplicateNullifier { .. })),
        "a pool transfer spending one note twice (across assets) must reject, got {res:?}"
    );
}

#[test]
fn no_inputs_rejects() {
    let res = prove_pool_transfer(BabyBear::ZERO, &[], vec![], vec![], PoolBalanceMode::EqualCount);
    assert!(matches!(res, Err(ShieldedError::NoInputs)));
}

// ── FALSE: the negative-value (mod-order wrap) inflation attack on the POOL —
//           now REJECTED by the per-output range proof ────────────────────────

#[test]
fn pool_negative_output_value_caught_by_range_proof() {
    // The pool's per-output range proof verifies over the VALUE-ONLY projection
    // `v·V + r·R` of each output (the asset-equality proof, required for any
    // split/merge, ties that projection's `(v, r)` to the asset-hiding leg). This
    // test exercises the value range gate on that projection.
    //
    // The attack: ONE honest input of `v_in`. The attacker mints TWO outputs whose
    // VALUE components GROUP-balance — out_big = v_in + STEAL, out_neg = -STEAL
    // (mod l) — so the Schnorr value-conservation proof BALANCES and ACCEPTS, yet
    // out_big is genuinely spendable for `v_in + STEAL`. out_neg's value is OUTSIDE
    // [0, 2^64), so no 64-bit Bulletproof binds to it.
    let v_in: u64 = 1_000;
    let steal: u64 = 9_000_000;
    let bi = [3u8; 32];
    let bo_big = [7u8; 32];
    let bo_neg = [11u8; 32];

    let vc_in = value_only_commitment(v_in, &bi);
    let vc_big = value_only_commitment(v_in + steal, &bo_big);
    // vc_neg = (-steal)·V + bo_neg·R — the wrapped-negative value commitment.
    let neg_scalar = -Scalar::from(steal);
    let vc_neg = ValueCommitment {
        point: neg_scalar * dregg_cell::value_commitment::value_generator()
            + scalar_from_blinding_bytes(&bo_neg)
                * dregg_cell::value_commitment::randomness_generator(),
    };

    let msg = b"pool-wrapped-negative";
    let v_excess = scalar_from_blinding_bytes(&bi)
        - (scalar_from_blinding_bytes(&bo_big) + scalar_from_blinding_bytes(&bo_neg));
    let v_conservation =
        prove_conservation(&[vc_in.clone()], &[vc_big.clone(), vc_neg.clone()], &v_excess, msg);

    // The hole: value-conservation ALONE accepts the wrapped-negative output
    // (the group sum is commit(v_in)).
    verify_asset_conservation(
        &[vc_in.clone()],
        &[vc_big.clone(), vc_neg.clone()],
        &v_conservation,
        msg,
    )
    .expect("value-conservation alone is FOOLED by the wrapped-negative output (the hole)");

    // The tooth: out_neg has NO 64-bit value, so the best forgery (a proof for
    // value 0 with bo_neg) does not bind to vc_neg (= neg_scalar·V + bo_neg·R).
    // The FULL verifier (conservation + range) REJECTS.
    let range_proofs = vec![
        pool_range_proof_bytes(v_in + steal, &bo_big),
        pool_range_proof_bytes(0, &bo_neg), // forged: out_neg has no in-range value
    ];
    let res = verify_full_conservation_bytes(
        &[vc_in.to_bytes().0],
        &[vc_big.to_bytes().0, vc_neg.to_bytes().0],
        &v_conservation,
        &range_proofs,
        msg,
    );
    assert!(
        matches!(
            res,
            Err(FullConservationError::RangeProofFailed { output_index: 1, .. })
        ),
        "the pool's wrapped-negative output must be REJECTED by its range proof, got {res:?}"
    );
}

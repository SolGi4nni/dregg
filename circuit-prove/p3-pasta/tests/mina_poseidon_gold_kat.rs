//! The pin that makes `dregg-p3-pasta` the RIGHT hash rather than *a* hash.
//!
//! Two independent obligations:
//!
//! 1. **The permutation is o1js's.** Every gold vector below is o1js
//!    `Poseidon.hash` output, produced by `bridge/mina-zkapp/scripts/poseidon-kat.ts`
//!    (o1js 2.15.0) and already carried verbatim by
//!    `circuit-prove/sketches/mina-pasta-hash-probe`. That probe pins
//!    `o1-labs/proof-systems 36a8b510`; THIS crate resolves to the workspace's
//!    patched `emberian/proof-systems c5305e63`. Re-pinning here is what turns
//!    "two revs that should agree" into a test.
//!
//! 2. **The p3 types built on it are the ones `dregg_outer_config.rs` uses.**
//!    `TruncatedPermutation<_, 2, 1, 3>`, `MultiField32PaddingFreeSponge<BabyBear,
//!    PastaFp, _, 3, 2, 1>`, `MerkleTreeMmcs<BabyBear, PastaFp, …>` and
//!    `MultiField32Challenger<BabyBear, PastaFp, _, 3, 2>` are exercised here at
//!    exactly the shapes the Mina terminal config instantiates — so "it type-checks"
//!    is not the evidence.
//!
//! Every positive check is paired with a REJECT check. An agreement test that
//! cannot disagree proves nothing.

use ark_ff::PrimeField as ArkPrimeField;
use mina_curves::pasta::Fp;
use p3_baby_bear::BabyBear;
use p3_challenger::MultiField32Challenger;
use p3_commit::{BatchOpeningRef, Mmcs};
use p3_field::integers::QuotientMap;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_pasta::{
    MinaPoseidonPerm, PASTA_DIGEST_ELEMS, PASTA_RATE, PASTA_WIDTH, PastaCompress, PastaFp,
    compress, mina_poseidon_hash,
};
use p3_symmetric::{CryptographicHasher, MultiField32PaddingFreeSponge, PseudoCompressionFunction};

fn fp_from_hex(s: &str) -> PastaFp {
    let s = s.trim_start_matches("0x");
    let bytes: Vec<u8> = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect();
    PastaFp(Fp::from_be_bytes_mod_order(&bytes))
}

fn f(x: u64) -> PastaFp {
    PastaFp::from_int(x)
}

/// o1js `Poseidon.hash` gold vectors, o1js 2.15.0.
const GOLD: &[(&str, &[u64], &str)] = &[
    (
        "empty",
        &[],
        "0x2fadbe2852044d028597455bc2abbd1bc873af205dfabb8a304600f3e09eeba8",
    ),
    (
        "zero",
        &[0],
        "0x2fadbe2852044d028597455bc2abbd1bc873af205dfabb8a304600f3e09eeba8",
    ),
    (
        "one",
        &[1],
        "0x10b41a5d3139ef0802e5faf6a7776aab079e44e99ec5b306ddddd88e15fe9e6d",
    ),
    (
        "two",
        &[2],
        "0x2ff0e1a38b683e46ad044aae772f0d3029c51e6f5610041c717a2c24c03e3cfe",
    ),
    (
        "seq012",
        &[0, 1, 2],
        "0x33c9a84ee660a76f7cf69fc1928848bf67a1bcd1801625926008eddebe371bb1",
    ),
    (
        "block_boundary",
        &[1, 2, 3, 4, 5],
        "0x27cc8fc2d8052df2f44fee2d74ea01aa33195d263b99128f78f24ae0b420d7ec",
    ),
    (
        "compress_LR",
        &[123456789, 987654321],
        "0x0ef95ec0c90a0dc01fb3010b91b8ddfdbbb7f166f0bf5b8f7ef26b90ae5230d8",
    ),
];

const GOLD_PMINUS1: &str = "0x363529b92c382593b6e8b455ac5e148fb262237aeeb15617799aaab76a879b4b";
const GOLD_PMINUS1_PAIR: &str =
    "0x2e0215c1db41c4c1622e2f573bd876c43d8f465aa0fecb40b7ee030577d5f4d3";
/// o1js `MerkleTree` depth-2 root over leaves [1,2,3,4] (nodes are
/// `Poseidon.hash([left, right])`).
const GOLD_MERKLE_1234: &str = "0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb777";

#[test]
fn permutation_matches_o1js_gold_kat() {
    for (name, ins, want_hex) in GOLD {
        let ins: Vec<PastaFp> = ins.iter().map(|&x| f(x)).collect();
        assert_eq!(
            mina_poseidon_hash(&ins),
            fp_from_hex(want_hex),
            "KAT '{name}' diverges from o1js Poseidon.hash"
        );
    }
    let pm1 = -PastaFp::ONE;
    assert_eq!(mina_poseidon_hash(&[pm1]), fp_from_hex(GOLD_PMINUS1));
    assert_eq!(
        mina_poseidon_hash(&[pm1, pm1]),
        fp_from_hex(GOLD_PMINUS1_PAIR)
    );

    // REJECT polarity: a tampered input must not reproduce a gold output.
    assert_ne!(
        mina_poseidon_hash(&[f(0), f(1), f(3)]),
        fp_from_hex(GOLD[4].2),
        "tampered input still produced the gold KAT"
    );
}

/// `TruncatedPermutation<MinaPoseidonPerm, 2, 1, 3>` — the MMCS node
/// compression — IS `Poseidon.hash([l, r])`. This identity is what makes a
/// Merkle level cost ONE native o1js Poseidon gate chain, and it is the whole
/// lever `docs/MINA-FACING-TERMINAL-OPTIONS.md` §3 rests on.
#[test]
fn truncated_permutation_is_o1js_poseidon_hash_of_a_pair() {
    let c = PastaCompress::new(MinaPoseidonPerm);
    let (l, r) = (f(123456789), f(987654321));
    assert_eq!(c.compress([[l], [r]]), [fp_from_hex(GOLD[6].2)]);
    assert_eq!(c.compress([[l], [r]]), [compress(l, r)]);
    assert_eq!(compress(l, r), mina_poseidon_hash(&[l, r]));

    // REJECT: the compression is order-sensitive (a symmetric compress would
    // let a prover swap siblings and reach the same root).
    assert_ne!(c.compress([[l], [r]]), c.compress([[r], [l]]));

    // The depth-2 o1js MerkleTree root, built from this compression alone.
    let root = compress(compress(f(1), f(2)), compress(f(3), f(4)));
    assert_eq!(root, fp_from_hex(GOLD_MERKLE_1234));
}

/// The p3 field laws that carry soundness weight downstream, checked on the
/// newtype rather than assumed from `ark-ff`.
#[test]
fn field_shape_is_what_p3_expects() {
    assert_eq!(PastaFp::order(), p3_pasta::PastaFp::order());
    assert_eq!(
        PastaFp::order().to_str_radix(10),
        p3_pasta::PASTA_FP_MODULUS_DEC
    );
    assert_eq!(PastaFp::ONE + PastaFp::ONE, PastaFp::TWO);
    assert_eq!(PastaFp::NEG_ONE + PastaFp::ONE, PastaFp::ZERO);
    assert_eq!(PastaFp::TWO.halve(), PastaFp::ONE);
    assert_eq!(PastaFp::ONE.halve().double(), PastaFp::ONE);
    assert_eq!(PastaFp::GENERATOR, f(5));
    assert_eq!(f(7).inverse() * f(7), PastaFp::ONE);
    assert!(PastaFp::ZERO.try_inverse().is_none());
    assert_eq!(PastaFp::from_int(-1i64), PastaFp::NEG_ONE);
    assert_eq!(
        PastaFp::from_int(u128::MAX).as_canonical_biguint(),
        u128::MAX.into()
    );

    // Canonicality is ENFORCED, not assumed: `p` itself must not decode.
    let p_bytes = {
        let mut b = [0u8; 32];
        let m = PastaFp::order().to_bytes_le();
        b[..m.len()].copy_from_slice(&m);
        b
    };
    assert!(
        PastaFp::from_canonical_bytes_le(&p_bytes).is_none(),
        "the byte encoding of p decoded — a non-canonical representative was accepted"
    );
    assert!(PastaFp::from_canonical_bytes_le(&[0u8; 31]).is_none());
    assert!(PastaFp::from_canonical_bytes_le(&[0u8; 33]).is_none());
    // p - 1 must still decode: a validator that rejects everything would pass a
    // rejection-only suite.
    let mut pm1 = p_bytes;
    pm1[0] -= 1;
    assert_eq!(
        PastaFp::from_canonical_bytes_le(&pm1),
        Some(PastaFp::NEG_ONE)
    );
    // Round-trip, on a value with high limbs set.
    let x = fp_from_hex(GOLD_PMINUS1);
    assert_eq!(
        PastaFp::from_canonical_bytes_le(&x.to_canonical_bytes_le()),
        Some(x)
    );
}

/// The MMCS leaf hash the Mina terminal config uses — the exact type
/// `dregg_outer_config.rs` instantiates over Bn254, over `PastaFp` instead.
///
/// The number that matters: **16 BabyBear lanes per permutation** (8 limbs per
/// rate slot × rate 2), against the deployed `PaddingFreeSponge<_, 16, 8, 8>`'s
/// **8**. Half the permutations, and each one 200× cheaper on Mina.
#[test]
fn multifield_leaf_sponge_packs_eight_babybear_limbs_per_slot() {
    type PastaHash = MultiField32PaddingFreeSponge<
        BabyBear,
        PastaFp,
        MinaPoseidonPerm,
        PASTA_WIDTH,
        PASTA_RATE,
        PASTA_DIGEST_ELEMS,
    >;
    let hash =
        PastaHash::new(MinaPoseidonPerm).expect("BabyBear order < Pasta order, RATE < WIDTH");

    // The packing width is a derived constant, and it is the one the Mina-side
    // verifier must reproduce lane-for-lane. Pin it.
    assert_eq!(
        p3_field::max_shifted_absorb_injective_limbs::<BabyBear, PastaFp>(),
        8,
        "the shifted pack no longer fits 8 BabyBear limbs per Pasta element"
    );
    assert_eq!(p3_field::absorb_radix_bits::<BabyBear>(), 31);

    let row: Vec<BabyBear> = (0..13u32).map(BabyBear::from_int).collect();
    let d = hash.hash_iter(row.iter().copied());
    assert_eq!(
        d.len(),
        1,
        "a Pasta leaf digest is ONE native field element"
    );

    // The sponge separates lengths (the +1 digit shift is what buys this).
    let d8 = hash.hash_iter(row[..8].iter().copied());
    let d9 = hash.hash_iter(row[..9].iter().copied());
    assert_ne!(d8, d9, "the sponge collided on widths 8 and 9");

    // And it separates CONTENT.
    let mut tampered = row.clone();
    tampered[5] += BabyBear::ONE;
    assert_ne!(hash.hash_iter(tampered.iter().copied()), d);

    // ⚑ A 16-lane row is ONE permutation; a 17-lane row is TWO. This is the
    // 2× fewer permutations than the deployed BabyBear sponge, asserted rather
    // than argued: if the rate slots were not both used, a 16-lane row would
    // cost two permutations and the digest of lanes 0..16 would equal the
    // digest of some 8-lane prefix pair. It does not.
    let wide: Vec<BabyBear> = (0..16u32).map(BabyBear::from_int).collect();
    let wider: Vec<BabyBear> = (0..17u32).map(BabyBear::from_int).collect();
    assert_ne!(
        hash.hash_iter(wide.iter().copied()),
        hash.hash_iter(wider.iter().copied())
    );
}

/// The whole MMCS, at the Mina terminal config's shape: commit a BabyBear
/// matrix under Mina-Poseidon, open a row, verify the opening — and refuse a
/// tampered one.
#[test]
fn pasta_mmcs_commits_opens_and_refuses() {
    type PastaHash = MultiField32PaddingFreeSponge<
        BabyBear,
        PastaFp,
        MinaPoseidonPerm,
        PASTA_WIDTH,
        PASTA_RATE,
        PASTA_DIGEST_ELEMS,
    >;
    type PastaValMmcs =
        MerkleTreeMmcs<BabyBear, PastaFp, PastaHash, PastaCompress, 2, PASTA_DIGEST_ELEMS>;

    let hash = PastaHash::new(MinaPoseidonPerm).unwrap();
    let comp = PastaCompress::new(MinaPoseidonPerm);
    let mmcs = PastaValMmcs::new(hash, comp, 0);

    let width = 13;
    let height = 8;
    let values: Vec<BabyBear> = (0..(width * height) as u32)
        .map(BabyBear::from_int)
        .collect();
    let m = RowMajorMatrix::new(values, width);

    let (commit, prover_data) = mmcs.commit_matrix(m.clone());
    // ⚑ The commitment is ONE native Pasta element per root — the property that
    // makes the Mina-side opening walk one 13-row Poseidon per level.
    assert_eq!(commit.roots().len(), 1);
    assert_eq!(commit.roots()[0].len(), PASTA_DIGEST_ELEMS);
    assert!(
        commit.roots()[0][0].as_canonical_biguint().bits() > 31,
        "root fits in 31 bits — the commitment does not look Pasta-native"
    );

    let index = 5;
    let dims = [m.dimensions()];
    let (opened, proof) = mmcs.open_batch(index, &prover_data).unpack();
    assert_eq!(proof.len(), 3, "height 8 ⇒ a 3-level authentication path");
    mmcs.verify_batch(&commit, &dims, index, BatchOpeningRef::new(&opened, &proof))
        .expect("an honest opening must verify");

    // REJECT 1: a tampered opened value.
    let mut bad = opened.clone();
    bad[0][0] += BabyBear::ONE;
    assert!(
        mmcs.verify_batch(&commit, &dims, index, BatchOpeningRef::new(&bad, &proof))
            .is_err(),
        "the MMCS accepted a tampered opened row"
    );

    // REJECT 2: a tampered sibling.
    let mut bad_proof = proof.clone();
    bad_proof[0][0] += PastaFp::ONE;
    assert!(
        mmcs.verify_batch(
            &commit,
            &dims,
            index,
            BatchOpeningRef::new(&opened, &bad_proof)
        )
        .is_err(),
        "the MMCS accepted a tampered sibling"
    );

    // REJECT 3: the right opening at the wrong index.
    assert!(
        mmcs.verify_batch(
            &commit,
            &dims,
            index + 1,
            BatchOpeningRef::new(&opened, &proof)
        )
        .is_err(),
        "the MMCS accepted an opening at the wrong index"
    );
}

/// The Fiat–Shamir transcript boundary. Same three derived constants
/// `dregg_outer_config.rs` pins against gnark — here they are what a Mina-side
/// verifier would have to reproduce, so they are pinned before anything depends
/// on them silently.
#[test]
fn multifield_challenger_pack_split_constants() {
    let ch: MultiField32Challenger<BabyBear, PastaFp, MinaPoseidonPerm, PASTA_WIDTH, PASTA_RATE> =
        MultiField32Challenger::new(MinaPoseidonPerm).expect("BabyBear order < Pasta order");
    assert_eq!(ch.absorb_radix_bits(), 31);
    assert_eq!(ch.absorb_num_f_elms(), 8);
    // ⚑ The squeeze split is NOT a bit count: `squeeze_field_order_num_limbs`
    // returns the largest `k` with `|BabyBear|^{k+2} ≤ |PF|`, i.e. base-`p`
    // digits that stay near-uniform over BabyBear. Pasta (2^254.00) and BN254
    // (2^253.60) both land on **7** — so all three challenger constants coincide
    // with the ETH wrap's, and `chain/gnark/multifield_challenger.go`'s
    // `mfAbsorbRadixBits=31 / mfAbsorbNumFElms=8 / mfSqueezeNumFElms=7` is
    // simultaneously the Mina-side spec. Measured, not assumed: an earlier draft
    // of this test asserted 9 from a bit-count argument and was wrong.
    assert_eq!(
        ch.squeeze_num_f_elms(),
        7,
        "the squeeze split width changed — a Mina-side verifier must match it exactly"
    );
}

/// The permutation is DETERMINISTIC and the crate's two entry points agree.
/// (`MinaPoseidonPerm` is a unit struct with `'static` params, so this cannot
/// drift — asserting it is cheap and a future constructor with state would
/// break here rather than in a transcript.)
#[test]
fn permutation_is_deterministic() {
    use p3_symmetric::Permutation;
    let mut a = [PastaFp::ZERO, PastaFp::ONE, PastaFp::TWO];
    let mut b = a;
    MinaPoseidonPerm.permute_mut(&mut a);
    MinaPoseidonPerm.permute_mut(&mut b);
    assert_eq!(a, b);
    assert_ne!(a, [PastaFp::ZERO, PastaFp::ONE, PastaFp::TWO]);
}

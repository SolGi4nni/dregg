//! GO/NO-GO Part A: Mina-Poseidon-over-Pasta in Rust, gold-KAT-matched to o1js.
//!
//! The template is `dregg_outer_config.rs`'s
//! `dregg_outer_poseidon2_bn254_matches_gnark_gold_kat` (circuit-prove/src/
//! dregg_outer_config.rs:428-457): a Rust hash pinned bit-for-bit to the
//! external verifier's reference. Here the external reference is **o1js
//! `Poseidon.hash`** (Mina-Poseidon, kimchi params, over Pasta Fp) — the hash
//! an o1js/Kimchi verifier evaluates natively (~11 Kimchi rows/permutation).
//!
//! Gold vectors below were produced by
//! `bridge/mina-zkapp/scripts/poseidon-kat.ts` (`npm run kat`, o1js 2.15.0):
//! run it and compare — the values are pasted verbatim. The same table is
//! mirrored on the o1js side at `bridge/mina-zkapp/src/rust-gold-vectors.ts`,
//! and `scripts/check-mina-attestation.sh` (a `local-gates.sh` row and a `ci.yml`
//! job) fails if the two ever disagree.
//!
//! Rust side: `mina-poseidon` (o1-labs/proof-systems rev 36a8b510) —
//! `ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, 55>` with
//! `pasta::fp_kimchi::static_params()`. This is kimchi's own sponge, the same
//! params o1js compiles into its Poseidon gate.

use ark_ff::{BigInteger, PrimeField};
use mina_curves::pasta::Fp;
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::pasta::{fp_kimchi, FULL_ROUNDS};
use mina_poseidon::poseidon::{ArithmeticSponge, Sponge};

/// The o1js `Poseidon.hash` semantics: zero initial state, absorb at rate 2
/// (zero-padding a partial final block is a no-op because absorb ADDS into the
/// state), one squeeze = state[0] after the final permutation. The
/// `ArithmeticSponge` absorb/squeeze state machine reproduces this exactly for
/// every input length INCLUDING empty (o1js permutes the zero state once;
/// squeeze-from-Absorbed(0) does the same).
pub fn mina_poseidon_hash(inputs: &[Fp]) -> Fp {
    let mut sponge = ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(
        fp_kimchi::static_params(),
    );
    sponge.absorb(inputs);
    sponge.squeeze()
}

/// The MMCS 2->1 compression function (the Pasta twin of DreggOuterConfig's
/// `TruncatedPermutation<Poseidon2Bn254<3>, 2, 1, 3>`): one permutation,
/// digest = 1 native field element per Merkle node. On the o1js side this is
/// literally `Poseidon.hash([left, right])` — one Poseidon gate chain.
pub fn compress(left: Fp, right: Fp) -> Fp {
    mina_poseidon_hash(&[left, right])
}

/// The MMCS leaf hash (the Pasta twin of `MultiField32PaddingFreeSponge`):
/// sponge over an arbitrary-width row. Here the row is already Fp; a real
/// DreggPastaConfig would pack canonical BabyBear values 8×31-bit limbs per Fp
/// (Pasta Fp is 254.6 bits — the same 8-limb budget as Bn254) before
/// absorbing, exactly the outer config's shifted pack.
pub fn leaf_hash(row: &[Fp]) -> Fp {
    mina_poseidon_hash(row)
}

fn fp_hex(x: Fp) -> String {
    let bytes = x.into_bigint().to_bytes_be();
    format!("0x{}", hex_of(&bytes))
}

fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn fp_from_hex(s: &str) -> Fp {
    let s = s.trim_start_matches("0x");
    let bytes: Vec<u8> = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect();
    Fp::from_be_bytes_mod_order(&bytes)
}

fn main() {
    let cases: &[(&str, Vec<Fp>)] = &[
        ("empty", vec![]),
        ("zero", vec![Fp::from(0u64)]),
        ("one", vec![Fp::from(1u64)]),
        (
            "seq012",
            vec![Fp::from(0u64), Fp::from(1u64), Fp::from(2u64)],
        ),
        (
            "compress_LR",
            vec![Fp::from(123456789u64), Fp::from(987654321u64)],
        ),
    ];
    for (name, ins) in cases {
        println!("{name} = {}", fp_hex(mina_poseidon_hash(ins)));
    }
    // MMCS shape demo: a depth-2 Merkle root via 2->1 compress.
    let leaves = [1u64, 2, 3, 4].map(Fp::from);
    let root = compress(
        compress(leaves[0], leaves[1]),
        compress(leaves[2], leaves[3]),
    );
    println!("merkle_root_1234 = {}", fp_hex(root));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Gold KATs from o1js `Poseidon.hash` (bridge/mina-zkapp/scripts/
    /// poseidon-kat.ts) — the o1js side of the pin, pasted verbatim from its
    /// output; re-checked against o1js 2.15.0 on 2026-07-28, unchanged.
    /// `P` = Pasta Fp modulus (o1js `Field.ORDER`).
    const P_HEX: &str = "0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001";

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

    /// p-1 edge cases (can't be u64 literals).
    const GOLD_PMINUS1: &str = "0x363529b92c382593b6e8b455ac5e148fb262237aeeb15617799aaab76a879b4b";
    const GOLD_PMINUS1_PAIR: &str =
        "0x2e0215c1db41c4c1622e2f573bd876c43d8f465aa0fecb40b7ee030577d5f4d3";

    #[test]
    fn field_modulus_matches_o1js() {
        // Same field: mina-curves Pasta Fp == o1js Field.ORDER.
        use ark_ff::Zero;
        let p_minus_1 = -Fp::from(1u64);
        let expect = fp_from_hex(P_HEX); // reduces p mod p = 0... so check via -1
        assert!(
            expect.is_zero(),
            "o1js Field.ORDER is not this Fp's modulus"
        );
        // and -1 round-trips as p-1 in be-bytes:
        let mut want = fp_from_hex(P_HEX);
        want -= Fp::from(1u64);
        assert_eq!(p_minus_1, want);
    }

    #[test]
    fn mina_poseidon_matches_o1js_gold_kat() {
        for (name, ins, want_hex) in GOLD {
            let ins: Vec<Fp> = ins.iter().map(|&x| Fp::from(x)).collect();
            let got = mina_poseidon_hash(&ins);
            let want = fp_from_hex(want_hex);
            assert_eq!(
                got,
                want,
                "KAT '{name}' diverges from o1js Poseidon.hash: got {}",
                fp_hex(got)
            );
        }
        // p-1 edge cases.
        let pm1 = -Fp::from(1u64);
        assert_eq!(
            mina_poseidon_hash(&[pm1]),
            fp_from_hex(GOLD_PMINUS1),
            "KAT 'pminus1' diverges"
        );
        assert_eq!(
            mina_poseidon_hash(&[pm1, pm1]),
            fp_from_hex(GOLD_PMINUS1_PAIR),
            "KAT 'pminus1_pair' diverges"
        );
    }

    /// REJECT polarity (the KAT comparison is not vacuous): a tampered input
    /// must not reproduce the gold output — same discipline as the Bn254 KAT.
    #[test]
    fn tampered_input_rejects() {
        let want =
            fp_from_hex("0x33c9a84ee660a76f7cf69fc1928848bf67a1bcd1801625926008eddebe371bb1");
        let tampered = mina_poseidon_hash(&[Fp::from(0u64), Fp::from(1u64), Fp::from(3u64)]);
        assert_ne!(tampered, want, "tampered input still produced the gold KAT");
    }

    /// MMCS-shape: the hash supports the two operations an MMCS needs —
    /// 2->1 node compression and arbitrary-width leaf sponging — and a
    /// depth-2 root built from `compress` matches o1js `MerkleTree` (which
    /// hashes nodes as `Poseidon.hash([left, right])`). Gold value from
    /// poseidon-kat.ts's MerkleTree case.
    #[test]
    fn merkle_compress_matches_o1js_merkletree() {
        let leaves = [1u64, 2, 3, 4].map(Fp::from);
        let root = compress(
            compress(leaves[0], leaves[1]),
            compress(leaves[2], leaves[3]),
        );
        let want =
            fp_from_hex("0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb777");
        assert_eq!(
            root, want,
            "depth-2 Merkle root diverges from o1js MerkleTree"
        );
        // wide-leaf sponge is well-defined (multi-block absorb):
        let row: Vec<Fp> = (0..37u64).map(Fp::from).collect();
        let _ = leaf_hash(&row);
    }
}

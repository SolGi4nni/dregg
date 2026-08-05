//! `fp_kimchi` PARAMETER + SPONGE export — the upstream artifact the **phase-1** (Fp) transcript
//! leg is welded against.
//!
//! ⚑ **THE DEFECT THIS EXISTS TO CLOSE.** `PastaPoseidon.mdsN` / `PastaPoseidon.rcsN` carry the
//! 3×3 MDS and the 55×3 round constants of `fp_kimchi` as **decimal literals in a Lean file**.
//! They were copied — correctly, as it turns out — but *nothing compared the copy to the source*.
//! One wrong digit in 174 numbers would have given a self-consistent tree: Lean proving the
//! program computes ITS constants, the harness pinning ITS digest, every gate green, and the
//! object not being Kimchi's sponge. That is the exact hole the Fq lane closed for `fq_kimchi`
//! (`pasta_fq_sponge_proves.rs` §9, 660/660 emitted ROM immediates against `static_params()`);
//! this is its Fp twin, and the artifact it needs did not exist.
//!
//! Everything below is READ OUT OF `mina_poseidon::pasta::fp_kimchi::static_params()` — the
//! function o1-labs' own verifier calls — and the KATs are driven through the upstream
//! `ArithmeticSponge` state machine, never a re-implementation.
//!
//! Run:
//!   cd metatheory/fixtures/kimchi-extractors
//!   cargo run --release --bin fp_kimchi_export > ../../fp_kimchi_params.json

use ark_ff::{BigInteger, One, PrimeField, Zero};
use mina_curves::pasta::{Fp, Fq};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    pasta::{fp_kimchi, fq_kimchi, FULL_ROUNDS},
    poseidon::{ArithmeticSponge, Sponge as _},
};
use num_bigint::BigUint;

type FpPoseidon = ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

fn d(x: &Fp) -> String {
    BigUint::from_bytes_le(&x.into_bigint().to_bytes_le()).to_string()
}

fn dq(x: &Fq) -> String {
    BigUint::from_bytes_le(&x.into_bigint().to_bytes_le()).to_string()
}

/// `fp_kimchi` sponge hash: zero state, absorb `xs`, squeeze once — the UPSTREAM state machine.
fn fp_hash(xs: &[Fp]) -> Fp {
    let mut s = FpPoseidon::new(fp_kimchi::static_params());
    s.absorb(xs);
    s.squeeze()
}

/// The raw permutation (`poseidon_block_cipher`) applied to a 3-lane state.
fn fp_perm(st: [Fp; 3]) -> Vec<Fp> {
    let mut s = FpPoseidon::new(fp_kimchi::static_params());
    s.state = st.to_vec();
    s.poseidon_block_cipher();
    s.state.clone()
}

/// The double-permuting ANTI-VALUE: what a schedule that permutes once too often would return.
/// The Fq lane's own repair lived on exactly this branch, so the negative pin is not decoration.
fn fp_hash_double_permuted(xs: &[Fp]) -> Fp {
    let mut s = FpPoseidon::new(fp_kimchi::static_params());
    s.absorb(xs);
    let _ = s.squeeze();
    s.poseidon_block_cipher();
    s.state[0]
}

fn main() {
    let p = fp_kimchi::static_params();

    // ── (0) THE MODULE CHECK, MADE HERE RATHER THAN TRUSTED. Reading `static_params()` off the
    // wrong module is the failure mode the K3 audit named by name; assert the two families are
    // disjoint at the emitting end, not only at the consuming one.
    let q = fq_kimchi::static_params();
    assert_ne!(
        d(&p.mds[0][0]),
        dq(&q.mds[0][0]),
        "fp_kimchi and fq_kimchi MDS agree at [0][0] -- `static_params()` was read off one module"
    );
    assert_eq!(p.mds.len(), 3, "the MDS is 3x3");
    assert_eq!(
        p.round_constants.len(),
        FULL_ROUNDS,
        "{FULL_ROUNDS} full rounds"
    );

    let mds: Vec<String> = (0..3)
        .flat_map(|r| (0..3).map(move |c| d(&p.mds[r][c])))
        .collect();
    let rcs: Vec<String> = (0..FULL_ROUNDS)
        .flat_map(|r| (0..3).map(move |j| d(&p.round_constants[r][j])))
        .collect();

    // ── KATs at BOTH input parities. The Fp side's own absorb-loop defect lived exclusively on
    // the EVEN-length branch, so the even cases are the ones that were never exercised.
    let kat_inputs: Vec<(&str, Vec<Fp>)> = vec![
        ("empty", vec![]),
        ("zero", vec![Fp::zero()]),
        ("one", vec![Fp::one()]),
        ("two", vec![Fp::from(2u8)]),
        ("pair12", vec![Fp::from(1u8), Fp::from(2u8)]),
        ("pair01", vec![Fp::zero(), Fp::one()]),
        ("triple012", vec![Fp::zero(), Fp::one(), Fp::from(2u8)]),
        (
            "quad1234",
            vec![Fp::one(), Fp::from(2u8), Fp::from(3u8), Fp::from(4u8)],
        ),
        (
            "five12345",
            vec![
                Fp::one(),
                Fp::from(2u8),
                Fp::from(3u8),
                Fp::from(4u8),
                Fp::from(5u8),
            ],
        ),
        (
            "six123456",
            vec![
                Fp::one(),
                Fp::from(2u8),
                Fp::from(3u8),
                Fp::from(4u8),
                Fp::from(5u8),
                Fp::from(6u8),
            ],
        ),
        ("pmax", vec![Fp::zero() - Fp::one()]),
        (
            "pmaxpair",
            vec![Fp::zero() - Fp::one(), Fp::zero() - Fp::one()],
        ),
    ];

    println!("{{");
    println!(
        "  \"source\": \"o1-labs/proof-systems @ f6d958dc05; \
         mina_poseidon::pasta::fp_kimchi::static_params(); ArithmeticSponge<Fp, \
         PlonkSpongeConstantsKimchi, 55> driven directly\","
    );
    println!("  \"fp_kimchi\": {{");
    println!(
        "    \"source\": \"poseidon/src/pasta/fp_kimchi.rs @ f6d958dc05 via static_params(); \
         KATs from ArithmeticSponge\","
    );
    println!("    \"full_rounds\": {FULL_ROUNDS},");
    println!("    \"rate\": 2,");
    println!("    \"sbox_alpha\": 7,");
    println!(
        "    \"mds\": [{}],",
        mds.iter()
            .map(|s| format!("\"{s}\""))
            .collect::<Vec<_>>()
            .join(",")
    );
    println!(
        "    \"round_constants\": [{}],",
        rcs.iter()
            .map(|s| format!("\"{s}\""))
            .collect::<Vec<_>>()
            .join(",")
    );

    let kats: Vec<String> = kat_inputs
        .iter()
        .map(|(n, xs)| {
            format!(
                "{{\"name\":\"{n}\",\"input\":[{}],\"digest\":\"{}\"}}",
                xs.iter()
                    .map(|x| format!("\"{}\"", d(x)))
                    .collect::<Vec<_>>()
                    .join(","),
                d(&fp_hash(xs))
            )
        })
        .collect();
    println!("    \"kats\": [{}],", kats.join(","));

    let anti: Vec<String> = kat_inputs
        .iter()
        .filter(|(n, _)| ["pair12", "pair01", "triple012", "quad1234", "six123456"].contains(n))
        .map(|(n, xs)| {
            format!(
                "{{\"name\":\"{n}\",\"double_permuted\":\"{}\"}}",
                d(&fp_hash_double_permuted(xs))
            )
        })
        .collect();
    println!("    \"double_permute_antivalues\": [{}],", anti.join(","));

    let pm = fp_perm([Fp::from(100u8), Fp::zero(), Fp::zero()]);
    println!(
        "    \"perm_of_100\": [{}]",
        pm.iter()
            .map(|x| format!("\"{}\"", d(x)))
            .collect::<Vec<_>>()
            .join(",")
    );
    println!("  }}");
    println!("}}");
}

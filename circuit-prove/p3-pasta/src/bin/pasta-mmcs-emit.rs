//! The dregg-side EMITTER for the Mina-facing MMCS, so the o1js measurement is
//! taken against the REAL p3 objects rather than a transcription of them.
//!
//! `bridge/mina-zkapp/scripts/mina-poseidon-merkle-rows.ts` shells out to this
//! and must reproduce every value in circuit. Two subcommands:
//!
//! - `leaf <rowWidth> <nRows> <vals...>` — the MMCS leaf hash
//!   ([`MinaHash`]: `MultiField32PaddingFreeSponge<BabyBear, PastaFp, _, 3, 2,
//!   1>`) over BabyBear rows, plus the intermediate PACKED rate-slot values so
//!   the o1js side's shifted radix-2^31 Horner can be checked on its own rather
//!   than only through the permutation.
//! - `path <depth> <leafIndex> <leafHex...>` — a sparse Merkle path under
//!   [`PastaCompress`] (the MMCS's `TruncatedPermutation`), for the opening
//!   measurement.
//!
//! Values are printed as JSON with canonical big-endian hex for Pasta elements
//! and decimal for BabyBear.

use p3_baby_bear::BabyBear;
use p3_field::integers::QuotientMap;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_pasta::{MinaPoseidonPerm, PastaFp, compress};
use p3_symmetric::{CryptographicHasher, MultiField32PaddingFreeSponge};

/// The Mina terminal config's leaf hash, spelled out here so the emitter cannot
/// drift from `dregg_mina_config::MinaHash` without this file changing.
type MinaHash = MultiField32PaddingFreeSponge<BabyBear, PastaFp, MinaPoseidonPerm, 3, 2, 1>;

/// BabyBear lanes packed into one Pasta rate slot — `reduce_packed_shifted` at
/// radix 2^31. The o1js twin must produce the same value from witnessed lanes.
const LIMBS_PER_SLOT: usize = 8;
const RADIX_BITS: u32 = 31;

fn hex_be(x: PastaFp) -> String {
    let mut b = x.to_canonical_bytes_le();
    b.reverse();
    format!(
        "0x{}",
        b.iter().map(|x| format!("{x:02x}")).collect::<String>()
    )
}

fn pack_slot(lanes: &[BabyBear]) -> PastaFp {
    let base = PastaFp::from_int(1u128 << RADIX_BITS);
    lanes.iter().rev().fold(PastaFp::ZERO, |acc, v| {
        acc * base + PastaFp::from_int(v.as_canonical_u32() as u64 + 1)
    })
}

fn quote_all(v: &[String]) -> String {
    v.iter()
        .map(|s| format!("\"{s}\""))
        .collect::<Vec<_>>()
        .join(",")
}

/// `leaf <rowWidth> <nRows> <vals...>`
fn emit_leaf(args: &[String]) {
    let row_width: usize = args[0].parse().expect("rowWidth");
    let n_rows: usize = args[1].parse().expect("nRows");
    let vals: Vec<BabyBear> = args[2..]
        .iter()
        .map(|s| BabyBear::from_int(s.parse::<u32>().expect("BabyBear lane must be a u32")))
        .collect();
    assert_eq!(
        vals.len(),
        row_width * n_rows,
        "expected rowWidth*nRows values"
    );

    let hash = MinaHash::new(MinaPoseidonPerm).expect("BabyBear order < Pasta order");

    let mut rows_json = Vec::new();
    let mut digests = Vec::new();
    let mut packed = Vec::new();
    for r in 0..n_rows {
        let row = &vals[r * row_width..(r + 1) * row_width];
        rows_json.push(format!(
            "[{}]",
            row.iter()
                .map(|v| v.as_canonical_u32().to_string())
                .collect::<Vec<_>>()
                .join(",")
        ));
        digests.push(hex_be(hash.hash_iter(row.iter().copied())[0]));
        // The rate slots, in the order the sponge writes them.
        let slots: Vec<String> = row
            .chunks(LIMBS_PER_SLOT)
            .map(|c| hex_be(pack_slot(c)))
            .collect();
        packed.push(format!("[{}]", quote_all(&slots)));
    }

    println!("{{");
    println!(
        "  \"emitter\": \"dregg-p3-pasta MultiField32PaddingFreeSponge<BabyBear,PastaFp,MinaPoseidonPerm,3,2,1>\","
    );
    println!("  \"rowWidth\": {row_width},");
    println!("  \"nRows\": {n_rows},");
    println!("  \"limbsPerSlot\": {LIMBS_PER_SLOT},");
    println!("  \"radixBits\": {RADIX_BITS},");
    println!("  \"lanesPerPermutation\": {},", LIMBS_PER_SLOT * 2);
    println!("  \"rows\": [{}],", rows_json.join(","));
    println!("  \"packedSlots\": [{}],", packed.join(","));
    println!("  \"leafDigests\": [{}]", quote_all(&digests));
    println!("}}");
}

/// The node value of an all-zero subtree of height `h`, for `h` in `0..=depth`.
fn zero_at(depth: usize) -> Vec<PastaFp> {
    let mut z = vec![PastaFp::ZERO];
    for h in 1..=depth {
        z.push(compress(z[h - 1], z[h - 1]));
    }
    z
}

/// `path <depth> <leafIndex> <leafHexOrDec...>`
fn emit_path(args: &[String]) {
    let depth: usize = args[0].parse().expect("depth");
    let leaf_index: usize = args[1].parse().expect("leafIndex");
    let leaves: Vec<PastaFp> = args[2..]
        .iter()
        .map(|s| {
            let hex = s.trim_start_matches("0x");
            let mut b: Vec<u8> = (0..hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex leaf"))
                .collect();
            b.reverse();
            b.resize(32, 0);
            PastaFp::from_canonical_bytes_le(&b).expect("leaf must be canonical")
        })
        .collect();
    assert!(!leaves.is_empty() && leaf_index < leaves.len());

    let z = zero_at(depth);
    let mut level = leaves.clone();
    let mut index = leaf_index;
    let mut siblings = Vec::new();
    let mut is_right = Vec::new();
    for h in 0..depth {
        let sib = index ^ 1;
        siblings.push(if sib < level.len() { level[sib] } else { z[h] });
        is_right.push(index % 2 == 1);
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i < level.len() {
            let l = level[i];
            let r = if i + 1 < level.len() {
                level[i + 1]
            } else {
                z[h]
            };
            next.push(compress(l, r));
            i += 2;
        }
        level = next;
        index >>= 1;
    }
    let mut cur = leaves[leaf_index];
    let mut nodes = Vec::new();
    for h in 0..depth {
        cur = if is_right[h] {
            compress(siblings[h], cur)
        } else {
            compress(cur, siblings[h])
        };
        nodes.push(cur);
    }

    println!("{{");
    println!("  \"emitter\": \"dregg-p3-pasta TruncatedPermutation<MinaPoseidonPerm,2,1,3>\",");
    println!("  \"depth\": {depth},");
    println!("  \"leafIndex\": {leaf_index},");
    println!(
        "  \"siblings\": [{}],",
        quote_all(&siblings.iter().map(|x| hex_be(*x)).collect::<Vec<_>>())
    );
    println!(
        "  \"isRight\": [{}],",
        is_right
            .iter()
            .map(|b| b.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    println!(
        "  \"nodes\": [{}],",
        quote_all(&nodes.iter().map(|x| hex_be(*x)).collect::<Vec<_>>())
    );
    println!("  \"root\": \"{}\"", hex_be(nodes[depth - 1]));
    println!("}}");
}

fn main() {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    match argv.first().map(String::as_str) {
        Some("leaf") => emit_leaf(&argv[1..]),
        Some("path") => emit_path(&argv[1..]),
        other => {
            eprintln!("usage: pasta-mmcs-emit leaf <rowWidth> <nRows> <vals...>");
            eprintln!("       pasta-mmcs-emit path <depth> <leafIndex> <leafHex...>");
            panic!("unknown subcommand {other:?}");
        }
    }
}

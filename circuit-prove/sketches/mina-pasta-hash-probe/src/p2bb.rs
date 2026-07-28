//! The DEPLOYED BabyBear Poseidon2-w16 MMCS, as an EMITTER for the o1js side.
//!
//! WHY THIS IS HERE AND NOT A TRANSCRIPTION. `bridge/mina-zkapp/src/
//! Poseidon2BabyBearW16.ts` already carries an o1js circuit for the permutation,
//! pinned to two `#guard` vectors copied out of
//! `metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean`. Two fixed vectors pin
//! the PERMUTATION. They pin nothing about the objects a FRI verifier actually
//! hashes: the `TruncatedPermutation<Perm, 2, 8, 16>` node compression, the
//! `PaddingFreeSponge<Perm, 16, 8, 8>` leaf hash, and the authentication-path
//! fold that composes them. Those are where an off-by-one lands.
//!
//! So this module calls the DEPLOYED objects — `p3_baby_bear::
//! default_babybear_poseidon2_16`, `p3_symmetric::TruncatedPermutation`,
//! `p3_symmetric::PaddingFreeSponge`, at the same `82cfad73` rev the workspace
//! pins for every other p3 crate — and emits their outputs on inputs the o1js
//! side cannot have precomputed. o1js must reproduce them elementwise. Nothing
//! in this file re-implements a hash; every value it prints comes out of the
//! same functions `circuit-prove/src/plonky3_recursion_impl.rs:126-128`
//! instantiates for the root batch-STARK.

use p3_baby_bear::{default_babybear_poseidon2_16, BabyBear, Poseidon2BabyBear};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_symmetric::{
    CryptographicHasher, PaddingFreeSponge, PseudoCompressionFunction, TruncatedPermutation,
};

/// `WIDTH` / `RATE` / `DIGEST_ELEMS` — `plonky3_recursion_impl.rs:75-77`.
pub const WIDTH: usize = 16;
pub const RATE: usize = 8;
pub const DIGEST_ELEMS: usize = 8;

pub type Perm = Poseidon2BabyBear<WIDTH>;
/// The MMCS leaf hash — `plonky3_recursion_impl.rs:127`.
pub type MyHash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST_ELEMS>;
/// The MMCS node compression — `plonky3_recursion_impl.rs:128`. Arity 2:
/// EXACTLY ONE width-16 permutation per Merkle node.
pub type MyCompress = TruncatedPermutation<Perm, 2, DIGEST_ELEMS, WIDTH>;

/// An MMCS digest: 8 BabyBear elements.
pub type Digest = [BabyBear; DIGEST_ELEMS];

pub fn perm() -> Perm {
    default_babybear_poseidon2_16()
}
pub fn hasher() -> MyHash {
    PaddingFreeSponge::new(perm())
}
pub fn compressor() -> MyCompress {
    TruncatedPermutation::new(perm())
}

/// `compress(l, r)` — the deployed node compression.
pub fn compress(c: &MyCompress, l: Digest, r: Digest) -> Digest {
    c.compress([l, r])
}

/// `leaf_hash(row)` — the deployed leaf sponge over an arbitrary-width row.
pub fn leaf_hash(h: &MyHash, row: &[BabyBear]) -> Digest {
    h.hash_iter(row.iter().copied())
}

/// The digest of an all-zero subtree of height `h`, for `h` in `0..=depth`.
/// `zero_at[0]` is the empty leaf `[0; 8]`; the rest fold `compress` on itself.
/// The o1js twin must agree, or a sparse path diverges above the populated
/// leaves without any single hash being wrong.
pub fn zero_at(c: &MyCompress, depth: usize) -> Vec<Digest> {
    let mut z = vec![[BabyBear::ZERO; DIGEST_ELEMS]];
    for h in 1..=depth {
        let prev = z[h - 1];
        z.push(compress(c, prev, prev));
    }
    z
}

/// A depth-`depth` authentication path for `leaf_index` in a SPARSE tree whose
/// populated leaf digests are `leaves[0..n)` and whose remaining leaves are the
/// zero digest. Returns `(siblings, is_right, nodes)` with `nodes.last()` the
/// root, folded back up the emitted path rather than read off the level array —
/// so a path that does not reach the root cannot be emitted.
pub fn sparse_path(
    c: &MyCompress,
    leaves: &[Digest],
    leaf_index: usize,
    depth: usize,
) -> (Vec<Digest>, Vec<bool>, Vec<Digest>) {
    let z = zero_at(c, depth);
    let mut level: Vec<Digest> = leaves.to_vec();
    let mut index = leaf_index;
    let mut siblings = Vec::with_capacity(depth);
    let mut is_right = Vec::with_capacity(depth);

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
            next.push(compress(c, l, r));
            i += 2;
        }
        level = next;
        index >>= 1;
    }

    let mut nodes = Vec::with_capacity(depth);
    let mut cur = leaves[leaf_index];
    for h in 0..depth {
        cur = if is_right[h] {
            compress(c, siblings[h], cur)
        } else {
            compress(c, cur, siblings[h])
        };
        nodes.push(cur);
    }
    (siblings, is_right, nodes)
}

// ---------------------------------------------------------------------------
// The FRI fold, arity 2 — the other half of a query step.
// ---------------------------------------------------------------------------

/// The challenge extension degree — `RECURSION_EXT_DEGREE = 4`
/// (`plonky3_recursion_impl.rs`), i.e. `BinomialExtensionField<BabyBear, 4>`.
pub const EXT_D: usize = 4;
/// An extension element in coefficient basis, `a0 + a1 X + a2 X^2 + a3 X^3`.
pub type Ext = [BabyBear; EXT_D];

/// `X^4 = W` for BabyBear's degree-4 binomial extension. Read off p3 rather
/// than asserted: `ext_w_is_the_deployed_constant` below pins it against
/// `BinomialExtensionField`'s own multiplication, so a p3 bump that changed it
/// would fail here instead of silently re-defining the field.
pub const EXT_W: u32 = 11;

pub fn ext_add(a: Ext, b: Ext) -> Ext {
    core::array::from_fn(|i| a[i] + b[i])
}
pub fn ext_sub(a: Ext, b: Ext) -> Ext {
    core::array::from_fn(|i| a[i] - b[i])
}
/// Schoolbook multiply then reduce by `X^4 - W`.
pub fn ext_mul(a: Ext, b: Ext) -> Ext {
    let mut acc = [BabyBear::ZERO; 2 * EXT_D - 1];
    for i in 0..EXT_D {
        for j in 0..EXT_D {
            acc[i + j] += a[i] * b[j];
        }
    }
    let w = BabyBear::from_u32(EXT_W);
    core::array::from_fn(|i| {
        if i + EXT_D < 2 * EXT_D - 1 {
            acc[i] + w * acc[i + EXT_D]
        } else {
            acc[i]
        }
    })
}
/// Scale an extension element by a base element.
pub fn ext_scale(a: Ext, s: BabyBear) -> Ext {
    core::array::from_fn(|i| a[i] * s)
}
/// Embed a base element.
pub fn ext_of_base(s: BabyBear) -> Ext {
    let mut o = [BabyBear::ZERO; EXT_D];
    o[0] = s;
    o
}

/// One arity-2 FRI fold, as `p3_fri`'s `fold_row` computes it at `log_arity = 1`:
/// two-point Lagrange interpolation through `(x, e_even)` and `(-x, e_odd)`,
/// evaluated at `beta`.
///
///   `folded = [ e_even * (beta + x) - e_odd * (beta - x) ] / (2x)`
///
/// `x` is the base-field coset point for this row —
/// `g_{log_height+1} ^ reverse_bits_len(index, log_height)`. The formula is
/// the one the circuit implements; `fold_row_is_two_point_lagrange` checks it
/// against an independent evaluation of the interpolant.
pub fn fold_row_arity2(x: BabyBear, beta: Ext, e_even: Ext, e_odd: Ext) -> Ext {
    let bx_plus = ext_add(beta, ext_of_base(x));
    let bx_minus = ext_sub(beta, ext_of_base(x));
    let num = ext_sub(ext_mul(e_even, bx_plus), ext_mul(e_odd, bx_minus));
    let inv2x = (x + x).inverse();
    ext_scale(num, inv2x)
}

/// The coset point for row `index` of a domain of height `2^log_height`, as
/// `fold_row` derives it: `g_{log_height+1} ^ reverse_bits_len(index, log_height)`.
pub fn coset_point(index: usize, log_height: usize) -> BabyBear {
    let g = BabyBear::two_adic_generator(log_height + 1);
    g.exp_u64(reverse_bits_len(index, log_height) as u64)
}

/// The next layer's coset point, from this layer's. `fold_row` is called with
/// the ALREADY-SHIFTED index at the FOLDED height, so between consecutive
/// rounds
///
///   `x_{r+1} = (-1)^{b_r} * x_r^2`,   `b_r` = the low bit of round `r`'s index
///
/// (the same bit that says whether the folded value sat in the even or the odd
/// slot at round `r+1`). A circuit therefore pays ONE squaring and a
/// conditional negation per layer instead of an exponentiation — and it pays it
/// on a bit it has already witnessed. Pinned by
/// `coset_points_descend_by_squaring_and_a_sign`.
pub fn next_coset_point(x: BabyBear, bit: bool) -> BabyBear {
    let sq = x * x;
    if bit {
        -sq
    } else {
        sq
    }
}

fn reverse_bits_len(x: usize, bit_len: usize) -> usize {
    let mut out = 0usize;
    for i in 0..bit_len {
        out |= ((x >> i) & 1) << (bit_len - 1 - i);
    }
    out
}

// ---------------------------------------------------------------------------
// Emission (JSON, decimal canonical BabyBear) — what the o1js side consumes.
// ---------------------------------------------------------------------------

fn d(x: BabyBear) -> String {
    x.as_canonical_u32().to_string()
}
fn arr(v: &[BabyBear]) -> String {
    v.iter()
        .map(|x| format!("\"{}\"", d(*x)))
        .collect::<Vec<_>>()
        .join(",")
}
fn arr2(v: &[Digest]) -> String {
    v.iter()
        .map(|g| format!("[{}]", arr(g)))
        .collect::<Vec<_>>()
        .join(",")
}

/// `p2merkle <depth> <leafIndex> <rowWidth> <v...>` — hash `n = |v| / rowWidth`
/// rows into leaf digests with the deployed sponge, build the depth-`depth`
/// sparse authentication path for `leafIndex`, and print the whole object.
pub fn emit_p2_merkle(args: &[String]) {
    let depth: usize = args[0].parse().expect("depth");
    let leaf_index: usize = args[1].parse().expect("leafIndex");
    let row_width: usize = args[2].parse().expect("rowWidth");
    let vals: Vec<BabyBear> = args[3..]
        .iter()
        .map(|s| {
            let v: u64 = s
                .parse()
                .unwrap_or_else(|_| panic!("value '{s}' is not a u64"));
            BabyBear::from_u64(v)
        })
        .collect();
    assert!(row_width > 0, "rowWidth must be positive");
    assert!(
        !vals.is_empty() && vals.len() % row_width == 0,
        "need a whole number of rows of width {row_width}, got {}",
        vals.len()
    );
    let n = vals.len() / row_width;
    assert!(
        leaf_index < n,
        "leafIndex {leaf_index} out of range (n = {n})"
    );
    assert!(depth > 0, "depth must be positive");

    let h = hasher();
    let c = compressor();
    let rows: Vec<Vec<BabyBear>> = vals.chunks(row_width).map(|r| r.to_vec()).collect();
    let leaves: Vec<Digest> = rows.iter().map(|r| leaf_hash(&h, r)).collect();
    let (siblings, is_right, nodes) = sparse_path(&c, &leaves, leaf_index, depth);
    let z = zero_at(&c, depth);

    println!("{{");
    println!(
        "  \"emitter\": \"mina-pasta-hash-probe p2merkle (p3 default_babybear_poseidon2_16, TruncatedPermutation<.,2,8,16>, PaddingFreeSponge<.,16,8,8>)\","
    );
    println!("  \"depth\": {depth},");
    println!("  \"leafIndex\": {leaf_index},");
    println!("  \"rowWidth\": {row_width},");
    println!("  \"nRows\": {n},");
    println!(
        "  \"rows\": [{}],",
        rows.iter()
            .map(|r| format!("[{}]", arr(r)))
            .collect::<Vec<_>>()
            .join(",")
    );
    println!("  \"leafDigests\": [{}],", arr2(&leaves));
    println!("  \"leaf\": [{}],", arr(&leaves[leaf_index]));
    println!("  \"siblings\": [{}],", arr2(&siblings));
    println!(
        "  \"isRight\": [{}],",
        is_right
            .iter()
            .map(|b| b.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    println!("  \"nodes\": [{}],", arr2(&nodes));
    println!("  \"zeroAt\": [{}],", arr2(&z));
    println!("  \"root\": [{}]", arr(&nodes[depth - 1]));
    println!("}}");
}

/// `p2fold <index> <logHeight> <beta0..3> <even0..3> <odd0..3>` — emit one
/// arity-2 FRI fold step: the coset point, the folded value, and the extension
/// products the circuit has to reproduce.
pub fn emit_p2_fold(args: &[String]) {
    let index: usize = args[0].parse().expect("index");
    let log_height: usize = args[1].parse().expect("logHeight");
    let g = |o: usize| -> Ext {
        core::array::from_fn(|i| {
            BabyBear::from_u64(args[2 + o + i].parse::<u64>().expect("ext limb"))
        })
    };
    let beta = g(0);
    let e_even = g(4);
    let e_odd = g(8);

    let x = coset_point(index, log_height);
    let folded = fold_row_arity2(x, beta, e_even, e_odd);

    println!("{{");
    println!("  \"emitter\": \"mina-pasta-hash-probe p2fold (arity-2 two-point Lagrange, p3 fold_row)\",");
    println!("  \"index\": {index},");
    println!("  \"logHeight\": {log_height},");
    println!("  \"extW\": {EXT_W},");
    println!("  \"x\": \"{}\",", d(x));
    println!("  \"beta\": [{}],", arr(&beta));
    println!("  \"eEven\": [{}],", arr(&e_even));
    println!("  \"eOdd\": [{}],", arr(&e_odd));
    println!("  \"mulBetaEven\": [{}],", arr(&ext_mul(beta, e_even)));
    println!("  \"folded\": [{}]", arr(&folded));
    println!("}}");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The two vectors `metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean`
    /// `#guard`s, and which `bridge/mina-zkapp/src/Poseidon2BabyBearW16.ts`
    /// carries as `KAT_RANGE16` / `KAT_ZERO16`. If the p3 rev this crate
    /// resolves ever stopped being the one the Lean module models, this fails
    /// rather than emitting a different hash under the same name.
    const KAT_RANGE16: [u32; 16] = [
        1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788, 1726691001,
        1761127344, 1552405120, 417318995, 36799261, 1215172152, 614923223, 1300746575, 957311597,
        304856115,
    ];
    const KAT_ZERO16: [u32; 16] = [
        1168947398, 128782440, 747404447, 883925857, 360581875, 1704698758, 1878363991, 1054281681,
        682225194, 705839125, 1218819873, 41544645, 1095344608, 174996601, 1678438226, 11259290,
    ];

    fn permute(s: [BabyBear; 16]) -> [BabyBear; 16] {
        use p3_symmetric::Permutation;
        let p = perm();
        let mut s = s;
        p.permute_mut(&mut s);
        s
    }

    #[test]
    fn deployed_permutation_matches_the_lean_pinned_kat() {
        let range: [BabyBear; 16] = core::array::from_fn(|i| BabyBear::from_u64(i as u64));
        let got = permute(range).map(|x| x.as_canonical_u32());
        assert_eq!(got, KAT_RANGE16, "perm([0..15]) is not the deployed value");
        let zero = [BabyBear::ZERO; 16];
        let got0 = permute(zero).map(|x| x.as_canonical_u32());
        assert_eq!(got0, KAT_ZERO16, "perm(0^16) is not the deployed value");
        // Reject polarity: the KAT is discriminating.
        let mut t = [BabyBear::ZERO; 16];
        t[0] = BabyBear::ONE;
        assert_ne!(
            permute(t).map(|x| x.as_canonical_u32()),
            KAT_ZERO16,
            "a tampered input reproduced the zero-state KAT"
        );
    }

    /// `compress(l, r)` IS `perm(l || r)[..8]`. This is the identity the o1js
    /// `provableCompress` is built on; if `TruncatedPermutation` ever meant
    /// something else, the circuit would be verifying a different tree.
    #[test]
    fn compress_is_the_truncated_permutation() {
        let c = compressor();
        let l: Digest = core::array::from_fn(|i| BabyBear::from_u64(i as u64));
        let r: Digest = core::array::from_fn(|i| BabyBear::from_u64((i + 8) as u64));
        let got = compress(&c, l, r);
        let mut pre = [BabyBear::ZERO; 16];
        pre[..8].copy_from_slice(&l);
        pre[8..].copy_from_slice(&r);
        let want = permute(pre);
        assert_eq!(got, want[..8], "compress != perm(l||r)[..8]");
        // and on the range input it is exactly the first 8 lanes of the KAT.
        assert_eq!(
            got.map(|x| x.as_canonical_u32()).to_vec(),
            KAT_RANGE16[..8].to_vec(),
            "compress([0..7],[8..15]) is not the KAT prefix"
        );
    }

    /// The leaf sponge's block structure: `ceil(n/8)` permutations, with the
    /// partial-block case NOT padded. A row of exactly 8 must not permute
    /// twice, and a row of 9 must.
    #[test]
    fn leaf_hash_is_the_padding_free_sponge() {
        let h = hasher();
        let row8: Vec<BabyBear> = (0..8u64).map(BabyBear::from_u64).collect();
        // one full block, input then exhausted at i == 0 => exactly one permute.
        let mut state = [BabyBear::ZERO; 16];
        state[..8].copy_from_slice(&row8);
        let want = permute(state);
        assert_eq!(leaf_hash(&h, &row8).to_vec(), want[..8].to_vec());

        let row9: Vec<BabyBear> = (0..9u64).map(BabyBear::from_u64).collect();
        let mut s2 = want;
        s2[0] = BabyBear::from_u64(8);
        let want9 = permute(s2);
        assert_eq!(
            leaf_hash(&h, &row9).to_vec(),
            want9[..8].to_vec(),
            "the 9-element sponge is not overwrite-absorb + permute"
        );
        assert_ne!(
            leaf_hash(&h, &row8),
            leaf_hash(&h, &row9),
            "the sponge collided on lengths 8 and 9"
        );
    }

    /// The emitted path must fold to the emitted root, and a tampered sibling
    /// must not. Without the second half the first is satisfied by any constant.
    #[test]
    fn sparse_path_folds_to_its_root_and_rejects_tampering() {
        let h = hasher();
        let c = compressor();
        let leaves: Vec<Digest> = (0..5u64)
            .map(|i| leaf_hash(&h, &[BabyBear::from_u64(i), BabyBear::from_u64(i * 7 + 1)]))
            .collect();
        let (siblings, is_right, nodes) = sparse_path(&c, &leaves, 3, 22);
        assert_eq!(siblings.len(), 22);
        // leaf 3: RIGHT at level 0, RIGHT at level 1, LEFT above.
        assert!(is_right[0] && is_right[1] && !is_right[2]);

        let mut cur = leaves[3];
        for lev in 0..22 {
            cur = if is_right[lev] {
                compress(&c, siblings[lev], cur)
            } else {
                compress(&c, cur, siblings[lev])
            };
        }
        assert_eq!(
            cur, nodes[21],
            "the emitted path does not fold to the emitted root"
        );

        let mut bad = siblings.clone();
        bad[0][0] += BabyBear::ONE;
        let mut cur = leaves[3];
        for lev in 0..22 {
            cur = if is_right[lev] {
                compress(&c, bad[lev], cur)
            } else {
                compress(&c, cur, bad[lev])
            };
        }
        assert_ne!(cur, nodes[21], "a tampered sibling still reached the root");
    }

    /// `EXT_W` is not asserted, it is CHECKED: `X * X * X * X` in p3's own
    /// `BinomialExtensionField<BabyBear, 4>` must equal `W`.
    #[test]
    fn ext_w_is_the_deployed_constant() {
        use p3_field::extension::BinomialExtensionField;
        let x: BinomialExtensionField<BabyBear, 4> = BinomialExtensionField::new([
            BabyBear::ZERO,
            BabyBear::ONE,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ]);
        let x4 = x * x * x * x;
        let want: BinomialExtensionField<BabyBear, 4> =
            BinomialExtensionField::from(BabyBear::from_u32(EXT_W));
        assert_eq!(x4, want, "X^4 != {EXT_W} in the deployed extension field");
    }

    /// This module's schoolbook `ext_mul` must agree with p3's own extension
    /// multiplication on random-ish inputs — otherwise the fold it feeds is
    /// arithmetic in a field nothing else uses.
    #[test]
    fn ext_mul_matches_p3_binomial_extension() {
        use p3_field::extension::BinomialExtensionField;
        let mk = |v: [u64; 4]| -> Ext { core::array::from_fn(|i| BabyBear::from_u64(v[i])) };
        let to_p3 =
            |e: Ext| -> BinomialExtensionField<BabyBear, 4> { BinomialExtensionField::new(e) };
        for (a, b) in [
            ([1u64, 2, 3, 4], [5u64, 6, 7, 8]),
            ([0, 0, 0, 1], [0, 0, 0, 1]),
            ([2013265920, 1, 0, 999], [12345, 678910, 1112, 1314]),
        ] {
            let (a, b) = (mk(a), mk(b));
            let want = to_p3(a) * to_p3(b);
            assert_eq!(to_p3(ext_mul(a, b)), want, "ext_mul diverges from p3");
        }
    }

    /// `fold_row_arity2` must BE two-point Lagrange: the folded value is the
    /// unique degree-<2 interpolant through `(x, e_even)` and `(-x, e_odd)`,
    /// evaluated at beta. Checked by evaluating that interpolant independently
    /// (as `c0 + c1 * beta` with the coefficients solved directly), and by the
    /// two boundary cases `beta = x` and `beta = -x`.
    #[test]
    fn fold_row_is_two_point_lagrange() {
        let x = coset_point(5, 10);
        let beta: Ext = [
            BabyBear::from_u64(11),
            BabyBear::from_u64(22),
            BabyBear::from_u64(33),
            BabyBear::from_u64(44),
        ];
        let e_even: Ext = core::array::from_fn(|i| BabyBear::from_u64(100 + i as u64));
        let e_odd: Ext = core::array::from_fn(|i| BabyBear::from_u64(200 + i as u64));

        // c0 = (e_even + e_odd)/2, c1 = (e_even - e_odd)/(2x); f(b) = c0 + c1 b.
        let inv2 = (BabyBear::ONE + BabyBear::ONE).inverse();
        let c0 = ext_scale(ext_add(e_even, e_odd), inv2);
        let c1 = ext_scale(ext_sub(e_even, e_odd), (x + x).inverse());
        let want = ext_add(c0, ext_mul(c1, beta));
        assert_eq!(fold_row_arity2(x, beta, e_even, e_odd), want);

        // Boundary: at beta = x the fold returns e_even; at -x, e_odd.
        assert_eq!(fold_row_arity2(x, ext_of_base(x), e_even, e_odd), e_even);
        assert_eq!(fold_row_arity2(x, ext_of_base(-x), e_even, e_odd), e_odd);
    }

    /// The coset points descend by a SQUARING AND A SIGN, not by a squaring.
    /// `x^2 = (-1)^{b} * x_next` where `b` is the index's low bit, because
    /// `rbl(i, L) = b * 2^{L-1} + rbl(i >> 1, L-1)` and `g_L^{2^{L-1}} = -1`.
    /// Getting this wrong is invisible on even indices — half the test vectors
    /// — which is why it is tested across a bit pattern with both polarities.
    #[test]
    fn coset_points_descend_by_squaring_and_a_sign() {
        // Walk DOWN the layers the way `verify_query` does: shift the index by
        // one and drop the height by one, 16 times — the deployed root's
        // commit-phase schedule (`|D^0| = 2^22`, 16 arity-2 layers).
        let mut i = 0b1011_0110_1001_1100_0110usize;
        let mut log_height = 21usize;
        let mut saw_both = (false, false);
        for _ in 0..16 {
            let x = coset_point(i, log_height);
            let next = coset_point(i >> 1, log_height - 1);
            let bit = i & 1 == 1;
            if bit {
                saw_both.1 = true
            } else {
                saw_both.0 = true
            }
            assert_eq!(
                next_coset_point(x, bit),
                next,
                "the (-1)^b * x^2 descent is wrong at log_height {log_height}"
            );
            // and the naive squaring is WRONG exactly when the bit is set.
            assert_eq!(
                x * x == next,
                !bit,
                "the sign correction is not load-bearing"
            );
            i >>= 1;
            log_height -= 1;
        }
        assert!(
            saw_both.0 && saw_both.1,
            "the test never exercised both bit polarities"
        );
    }
}

//! wgpu/WGSL BN254 t=3 Poseidon2 permutation probe — THE decisive shrink-GPU number.
//!
//! The BN254-native shrink prover's dominant kernel (~60% of the ~95s shrink prove)
//! is the `Poseidon2Bn254<3>` permutation inside the outer MMCS
//! (`circuit-prove/src/dregg_outer_config.rs:139-156`: `OuterPerm = Poseidon2Bn254<3>`,
//! `MultiField32PaddingFreeSponge<..,3,2,1>`, `TruncatedPermutation<..,2,1,3>`).
//! CPU rate: 0.17-0.19 Mperm/s exact-outer-stack rayon-12 (GPU-PROVER-WIRING-PLAN.md §2;
//! 0.13 Mperm/s conservative). This probe answers: does 256-bit / 8×u32-limb Montgomery
//! arithmetic in 32-bit WGSL (no u64, no mulhi) keep enough throughput to make the
//! shrink's dominant hashing GPU-able (5-10x+ → ~2-2.5x e2e after Amdahl), or does it
//! collapse?
//!
//! Parity FIRST: (a) field mul/add KAT vs num-bigint; (b) the gnark gold KAT
//! `bn254KATOutHex` (permutation of [0,1,2] — `chain/gnark/poseidon2_bn254_test.go:19`,
//! same vector as `dregg_outer_config.rs` `GOLD_KAT_OUT`); (c) a 65536-perm batch
//! bit-exact vs the pinned plonky3 82cfad7 `Poseidon2Bn254<3>` (the SAME type the
//! shrink MMCS instantiates).
//!
//! Permutation (pinned p3 bn254/src/poseidon2.rs + chain/gnark/poseidon2_bn254.go):
//! t=3, α=5, R_F=8 (4 initial + 4 terminal), R_P=56;
//! extLinear = [[2,1,1],[1,2,1],[1,1,2]] (sum then s_i += sum);
//! intLinear = 1+diag([1,1,2]) (sum; s0+=sum; s1+=sum; s2=2*s2+sum);
//! schedule: extLinear; 4×{+RC_init; x^5 all; extLinear}; 56×{s0+=RC; s0=x^5; intLinear};
//! 4×{+RC_term; x^5 all; extLinear}.

use num_bigint::BigUint;
use p3_bn254::{Bn254, Poseidon2Bn254};
use p3_field::PrimeField;
use p3_poseidon2::ExternalLayerConstants;
use p3_symmetric::Permutation;
use rand::Rng;
use wgpu::util::DeviceExt;

// ============================================================================
// Round constants — HorizenLabs zkhash RC3, the exact table plonky3 pins and
// gnark splices (chain/gnark/poseidon2_bn254_constants.go rc3ExtInitial /
// rc3Internal / rc3ExtTerminal == dregg_outer_config.rs RC3_*).
// ============================================================================

const RC3_EXT_INITIAL: [[&str; 3]; 4] = [
    [
        "0x1d066a255517b7fd8bddd3a93f7804ef7f8fcde48bb4c37a59a09a1a97052816",
        "0x29daefb55f6f2dc6ac3f089cebcc6120b7c6fef31367b68eb7238547d32c1610",
        "0x1f2cb1624a78ee001ecbd88ad959d7012572d76f08ec5c4f9e8b7ad7b0b4e1d1",
    ],
    [
        "0x0aad2e79f15735f2bd77c0ed3d14aa27b11f092a53bbc6e1db0672ded84f31e5",
        "0x2252624f8617738cd6f661dd4094375f37028a98f1dece66091ccf1595b43f28",
        "0x1a24913a928b38485a65a84a291da1ff91c20626524b2b87d49f4f2c9018d735",
    ],
    [
        "0x22fc468f1759b74d7bfc427b5f11ebb10a41515ddff497b14fd6dae1508fc47a",
        "0x1059ca787f1f89ed9cd026e9c9ca107ae61956ff0b4121d5efd65515617f6e4d",
        "0x02be9473358461d8f61f3536d877de982123011f0bf6f155a45cbbfae8b981ce",
    ],
    [
        "0x0ec96c8e32962d462778a749c82ed623aba9b669ac5b8736a1ff3a441a5084a4",
        "0x292f906e073677405442d9553c45fa3f5a47a7cdb8c99f9648fb2e4d814df57e",
        "0x274982444157b86726c11b9a0f5e39a5cc611160a394ea460c63f0b2ffe5657e",
    ],
];

const RC3_INTERNAL: [&str; 56] = [
    "0x1a1d063e54b1e764b63e1855bff015b8cedd192f47308731499573f23597d4b5",
    "0x26abc66f3fdf8e68839d10956259063708235dccc1aa3793b91b002c5b257c37",
    "0x0c7c64a9d887385381a578cfed5aed370754427aabca92a70b3c2b12ff4d7be8",
    "0x1cf5998769e9fab79e17f0b6d08b2d1eba2ebac30dc386b0edd383831354b495",
    "0x0f5e3a8566be31b7564ca60461e9e08b19828764a9669bc17aba0b97e66b0109",
    "0x18df6a9d19ea90d895e60e4db0794a01f359a53a180b7d4b42bf3d7a531c976e",
    "0x04f7bf2c5c0538ac6e4b782c3c6e601ad0ea1d3a3b9d25ef4e324055fa3123dc",
    "0x29c76ce22255206e3c40058523748531e770c0584aa2328ce55d54628b89ebe6",
    "0x198d425a45b78e85c053659ab4347f5d65b1b8e9c6108dbe00e0e945dbc5ff15",
    "0x25ee27ab6296cd5e6af3cc79c598a1daa7ff7f6878b3c49d49d3a9a90c3fdf74",
    "0x138ea8e0af41a1e024561001c0b6eb1505845d7d0c55b1b2c0f88687a96d1381",
    "0x306197fb3fab671ef6e7c2cba2eefd0e42851b5b9811f2ca4013370a01d95687",
    "0x1a0c7d52dc32a4432b66f0b4894d4f1a21db7565e5b4250486419eaf00e8f620",
    "0x2b46b418de80915f3ff86a8e5c8bdfccebfbe5f55163cd6caa52997da2c54a9f",
    "0x12d3e0dc0085873701f8b777b9673af9613a1af5db48e05bfb46e312b5829f64",
    "0x263390cf74dc3a8870f5002ed21d089ffb2bf768230f648dba338a5cb19b3a1f",
    "0x0a14f33a5fe668a60ac884b4ca607ad0f8abb5af40f96f1d7d543db52b003dcd",
    "0x28ead9c586513eab1a5e86509d68b2da27be3a4f01171a1dd847df829bc683b9",
    "0x1c6ab1c328c3c6430972031f1bdb2ac9888f0ea1abe71cffea16cda6e1a7416c",
    "0x1fc7e71bc0b819792b2500239f7f8de04f6decd608cb98a932346015c5b42c94",
    "0x03e107eb3a42b2ece380e0d860298f17c0c1e197c952650ee6dd85b93a0ddaa8",
    "0x2d354a251f381a4669c0d52bf88b772c46452ca57c08697f454505f6941d78cd",
    "0x094af88ab05d94baf687ef14bc566d1c522551d61606eda3d14b4606826f794b",
    "0x19705b783bf3d2dc19bcaeabf02f8ca5e1ab5b6f2e3195a9d52b2d249d1396f7",
    "0x09bf4acc3a8bce3f1fcc33fee54fc5b28723b16b7d740a3e60cef6852271200e",
    "0x1803f8200db6013c50f83c0c8fab62843413732f301f7058543a073f3f3b5e4e",
    "0x0f80afb5046244de30595b160b8d1f38bf6fb02d4454c0add41f7fef2faf3e5c",
    "0x126ee1f8504f15c3d77f0088c1cfc964abcfcf643f4a6fea7dc3f98219529d78",
    "0x23c203d10cfcc60f69bfb3d919552ca10ffb4ee63175ddf8ef86f991d7d0a591",
    "0x2a2ae15d8b143709ec0d09705fa3a6303dec1ee4eec2cf747c5a339f7744fb94",
    "0x07b60dee586ed6ef47e5c381ab6343ecc3d3b3006cb461bbb6b5d89081970b2b",
    "0x27316b559be3edfd885d95c494c1ae3d8a98a320baa7d152132cfe583c9311bd",
    "0x1d5c49ba157c32b8d8937cb2d3f84311ef834cc2a743ed662f5f9af0c0342e76",
    "0x2f8b124e78163b2f332774e0b850b5ec09c01bf6979938f67c24bd5940968488",
    "0x1e6843a5457416b6dc5b7aa09a9ce21b1d4cba6554e51d84665f75260113b3d5",
    "0x11cdf00a35f650c55fca25c9929c8ad9a68daf9ac6a189ab1f5bc79f21641d4b",
    "0x21632de3d3bbc5e42ef36e588158d6d4608b2815c77355b7e82b5b9b7eb560bc",
    "0x0de625758452efbd97b27025fbd245e0255ae48ef2a329e449d7b5c51c18498a",
    "0x2ad253c053e75213e2febfd4d976cc01dd9e1e1c6f0fb6b09b09546ba0838098",
    "0x1d6b169ed63872dc6ec7681ec39b3be93dd49cdd13c813b7d35702e38d60b077",
    "0x1660b740a143664bb9127c4941b67fed0be3ea70a24d5568c3a54e706cfef7fe",
    "0x0065a92d1de81f34114f4ca2deef76e0ceacdddb12cf879096a29f10376ccbfe",
    "0x1f11f065202535987367f823da7d672c353ebe2ccbc4869bcf30d50a5871040d",
    "0x26596f5c5dd5a5d1b437ce7b14a2c3dd3bd1d1a39b6759ba110852d17df0693e",
    "0x16f49bc727e45a2f7bf3056efcf8b6d38539c4163a5f1e706743db15af91860f",
    "0x1abe1deb45b3e3119954175efb331bf4568feaf7ea8b3dc5e1a4e7438dd39e5f",
    "0x0e426ccab66984d1d8993a74ca548b779f5db92aaec5f102020d34aea15fba59",
    "0x0e7c30c2e2e8957f4933bd1942053f1f0071684b902d534fa841924303f6a6c6",
    "0x0812a017ca92cf0a1622708fc7edff1d6166ded6e3528ead4c76e1f31d3fc69d",
    "0x21a5ade3df2bc1b5bba949d1db96040068afe5026edd7a9c2e276b47cf010d54",
    "0x01f3035463816c84ad711bf1a058c6c6bd101945f50e5afe72b1a5233f8749ce",
    "0x0b115572f038c0e2028c2aafc2d06a5e8bf2f9398dbd0fdf4dcaa82b0f0c1c8b",
    "0x1c38ec0b99b62fd4f0ef255543f50d2e27fc24db42bc910a3460613b6ef59e2f",
    "0x1c89c6d9666272e8425c3ff1f4ac737b2f5d314606a297d4b1d0b254d880c53e",
    "0x03326e643580356bf6d44008ae4c042a21ad4880097a5eb38b71e2311bb88f8f",
    "0x268076b0054fb73f67cee9ea0e51e3ad50f27a6434b5dceb5bdde2299910a4c9",
];

const RC3_EXT_TERMINAL: [[&str; 3]; 4] = [
    [
        "0x1acd63c67fbc9ab1626ed93491bda32e5da18ea9d8e4f10178d04aa6f8747ad0",
        "0x19f8a5d670e8ab66c4e3144be58ef6901bf93375e2323ec3ca8c86cd2a28b5a5",
        "0x1c0dc443519ad7a86efa40d2df10a011068193ea51f6c92ae1cfbb5f7b9b6893",
    ],
    [
        "0x14b39e7aa4068dbe50fe7190e421dc19fbeab33cb4f6a2c4180e4c3224987d3d",
        "0x1d449b71bd826ec58f28c63ea6c561b7b820fc519f01f021afb1e35e28b0795e",
        "0x1ea2c9a89baaddbb60fa97fe60fe9d8e89de141689d1252276524dc0a9e987fc",
    ],
    [
        "0x0478d66d43535a8cb57e9c1c3d6a2bd7591f9a46a0e9c058134d5cefdb3c7ff1",
        "0x19272db71eece6a6f608f3b2717f9cd2662e26ad86c400b21cde5e4a7b00bebe",
        "0x14226537335cab33c749c746f09208abb2dd1bd66a87ef75039be846af134166",
    ],
    [
        "0x01fd6af15956294f9dfe38c0d976a088b21c21e4a1c2e823f912f44961f9a9ce",
        "0x18e5abedd626ec307bca190b8b2cab1aaee2e62ed229ba5a5ad8518d4e5f2a57",
        "0x0fc1bbceba0590f5abbdffa6d3b35e3297c021a3a409926d0e2d54dc1c84fda6",
    ],
];

/// Gold KAT: Poseidon2Bn254<3> permutation of [0,1,2] — bn254KATOutHex
/// (chain/gnark/poseidon2_bn254_test.go:19 == dregg_outer_config.rs GOLD_KAT_OUT).
const GOLD_KAT_OUT: [&str; 3] = [
    "0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033",
    "0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570",
    "0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8",
];

/// BN254 scalar field prime.
const P_HEX: &str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

// ============================================================================
// Host-side helpers
// ============================================================================

fn biguint_from_hex(s: &str) -> BigUint {
    BigUint::parse_bytes(s.trim_start_matches("0x").as_bytes(), 16).expect("bad hex")
}

fn limbs8(x: &BigUint) -> [u32; 8] {
    let d = x.to_u32_digits();
    assert!(d.len() <= 8, "value exceeds 256 bits");
    let mut out = [0u32; 8];
    out[..d.len()].copy_from_slice(&d);
    out
}

fn limbs_to_biguint(l: &[u32]) -> BigUint {
    BigUint::from_slice(l)
}

/// WGSL Fp literal (8 LE u32 limbs) for a canonical value already in the
/// desired representation.
fn fp_lit(x: &BigUint) -> String {
    let l = limbs8(x);
    format!(
        "Fp(0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u)",
        l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7]
    )
}

fn bn254_from_biguint(x: &BigUint) -> Bn254 {
    Bn254::from_biguint(x.clone()).expect("value not canonical")
}

/// Build the pinned Poseidon2Bn254<3> — the SAME construction as
/// `dregg_outer_config.rs::dregg_poseidon2_bn254()`.
fn build_p3_perm() -> Poseidon2Bn254<3> {
    let initial: Vec<[Bn254; 3]> = RC3_EXT_INITIAL
        .iter()
        .map(|row| row.map(|s| bn254_from_biguint(&biguint_from_hex(s))))
        .collect();
    let terminal: Vec<[Bn254; 3]> = RC3_EXT_TERMINAL
        .iter()
        .map(|row| row.map(|s| bn254_from_biguint(&biguint_from_hex(s))))
        .collect();
    let internal: Vec<Bn254> = RC3_INTERNAL
        .iter()
        .map(|s| bn254_from_biguint(&biguint_from_hex(s)))
        .collect();
    Poseidon2Bn254::<3>::new(ExternalLayerConstants::new(initial, terminal), internal)
}

// ============================================================================
// WGSL generation
// ============================================================================

/// Static WGSL prelude: 8×u32-limb BN254 Montgomery arithmetic.
/// mul64 = the 16-bit-split 32×32→64 (WGSL has no u64 / no mulhi), exactly the
/// wgpu-babybear-probe trick scaled to 8-limb schoolbook + SOS Montgomery
/// reduction (m = t[i]*N0INV mod 2^32; t += m*P<<32i; result = t>>256, one
/// conditional subtract — result < 2P).
const WGSL_PRELUDE: &str = r#"
alias Fp = array<u32, 8>;

// 32x32 -> 64 multiply via 16-bit split (WGSL has no u64).
fn mul64(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xffffu; let a1 = a >> 16u;
    let b0 = b & 0xffffu; let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = p01 + p10;
    let carry_mid = select(0u, 0x10000u, mid < p01);
    let mid_lo = mid << 16u;
    let lo = p00 + mid_lo;
    let carry_lo = select(0u, 1u, lo < p00);
    let hi = p11 + (mid >> 16u) + carry_mid + carry_lo;
    return vec2<u32>(lo, hi);
}

fn fp_p() -> Fp { return @P_FP@; }

// a >= P ? (lexicographic, high limb first; generated with literal P limbs)
fn fp_geq_p(a: Fp) -> bool {
@GEQ_BODY@
    return true;
}

fn fp_sub_p(a: Fp) -> Fp {
    let p = fp_p();
    var r: Fp;
    var borrow = 0u;
    for (var i = 0u; i < 8u; i++) {
        let d = a[i] - p[i];
        let b1 = select(0u, 1u, a[i] < p[i]);
        let d2 = d - borrow;
        let b2 = select(0u, 1u, d < borrow);
        r[i] = d2;
        borrow = b1 | b2;
    }
    return r;
}

// a + b mod P (operands < P, so the u32x8 sum never carries out of 2^256).
fn fp_add(a: Fp, b: Fp) -> Fp {
    var r: Fp;
    var c = 0u;
    for (var i = 0u; i < 8u; i++) {
        let s = a[i] + b[i];
        let c1 = select(0u, 1u, s < a[i]);
        let s2 = s + c;
        let c2 = select(0u, 1u, s2 < c);
        r[i] = s2;
        c = c1 | c2;
    }
    if (c != 0u || fp_geq_p(r)) { r = fp_sub_p(r); }
    return r;
}

// Montgomery product (R = 2^256): schoolbook 8x8 product then SOS reduction.
fn mont_mul(a: Fp, b: Fp) -> Fp {
    let p = fp_p();
    var t: array<u32, 17>; // zero-initialized
    // product phase: t[0..16] = a*b
    for (var i = 0u; i < 8u; i++) {
        var carry = 0u;
        let ai = a[i];
        for (var j = 0u; j < 8u; j++) {
            let pr = mul64(ai, b[j]);
            let lo1 = pr.x + t[i + j];
            var hi = pr.y + select(0u, 1u, lo1 < pr.x);
            let lo2 = lo1 + carry;
            hi = hi + select(0u, 1u, lo2 < carry);
            t[i + j] = lo2;
            carry = hi;
        }
        t[i + 8u] = carry;
    }
    // reduction phase: 8 x (m = t[i]*N0INV; t += m*P << 32i)
    for (var i = 0u; i < 8u; i++) {
        let m = t[i] * @N0INV@u;
        var carry = 0u;
        for (var j = 0u; j < 8u; j++) {
            let pr = mul64(m, p[j]);
            let lo1 = pr.x + t[i + j];
            var hi = pr.y + select(0u, 1u, lo1 < pr.x);
            let lo2 = lo1 + carry;
            hi = hi + select(0u, 1u, lo2 < carry);
            t[i + j] = lo2;
            carry = hi;
        }
        // ripple the block carry upward
        var k = i + 8u;
        loop {
            if (carry == 0u || k >= 17u) { break; }
            let s = t[k] + carry;
            carry = select(0u, 1u, s < carry);
            t[k] = s;
            k = k + 1u;
        }
    }
    var r: Fp;
    for (var i = 0u; i < 8u; i++) { r[i] = t[i + 8u]; }
    if (t[16] != 0u || fp_geq_p(r)) { r = fp_sub_p(r); }
    return r;
}

// x^5 = ((x^2)^2) * x — three Montgomery muls, matching bn254Sbox.
fn sbox(x: Fp) -> Fp {
    let x2 = mont_mul(x, x);
    let x4 = mont_mul(x2, x2);
    return mont_mul(x4, x);
}

// External linear layer, t=3: M_E = [[2,1,1],[1,2,1],[1,1,2]].
fn ext_linear(s: ptr<function, array<Fp, 3>>) {
    let sum = fp_add(fp_add((*s)[0], (*s)[1]), (*s)[2]);
    (*s)[0] = fp_add((*s)[0], sum);
    (*s)[1] = fp_add((*s)[1], sum);
    (*s)[2] = fp_add((*s)[2], sum);
}

// Internal diffusion, 1 + diag([1,1,2]) = [[2,1,1],[1,2,1],[1,1,3]].
fn int_linear(s: ptr<function, array<Fp, 3>>) {
    let sum = fp_add(fp_add((*s)[0], (*s)[1]), (*s)[2]);
    (*s)[0] = fp_add((*s)[0], sum);
    (*s)[1] = fp_add((*s)[1], sum);
    (*s)[2] = fp_add(fp_add((*s)[2], (*s)[2]), sum);
}

// Full Poseidon2Bn254<3> permutation, state in Montgomery form, RCs inlined in
// Montgomery form (generated below).
fn permute(s: ptr<function, array<Fp, 3>>) {
@PERM_BODY@
}

@group(0) @binding(0) var<storage, read> input: array<u32>;
@group(0) @binding(1) var<storage, read_write> output: array<u32>;

// One thread = one permutation. Canonical in -> Montgomery -> permute -> canonical out.
@compute @workgroup_size(@WG@)
fn perm_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let n = arrayLength(&input) / 24u;
    if (i >= n) { return; }
    let r2 = @R2_FP@;
    var s: array<Fp, 3>;
    for (var l = 0u; l < 3u; l++) {
        var x: Fp;
        for (var w = 0u; w < 8u; w++) { x[w] = input[(i * 3u + l) * 8u + w]; }
        s[l] = mont_mul(x, r2); // canonical -> Montgomery
    }
    permute(&s);
    var one: Fp;
    one[0] = 1u;
    for (var l = 0u; l < 3u; l++) {
        let x = mont_mul(s[l], one); // Montgomery -> canonical
        for (var w = 0u; w < 8u; w++) { output[(i * 3u + l) * 8u + w] = x[w]; }
    }
}

// Field-arithmetic KAT: per pair (a,b) emit (a*b mod P, a+b mod P).
@compute @workgroup_size(64)
fn mul_kat(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let n = arrayLength(&input) / 16u;
    if (i >= n) { return; }
    let r2 = @R2_FP@;
    var a: Fp;
    var b: Fp;
    for (var w = 0u; w < 8u; w++) {
        a[w] = input[i * 16u + w];
        b[w] = input[i * 16u + 8u + w];
    }
    let am = mont_mul(a, r2);
    let bm = mont_mul(b, r2);
    let cm = mont_mul(am, bm);
    var one: Fp;
    one[0] = 1u;
    let c = mont_mul(cm, one);
    let d = fp_add(a, b);
    for (var w = 0u; w < 8u; w++) {
        output[i * 16u + w] = c[w];
        output[i * 16u + 8u + w] = d[w];
    }
}
"#;

/// Generate the full shader for a given workgroup size, with the RC3 constants
/// inlined in Montgomery form.
fn shader_source(wg: u32, p: &BigUint, r: &BigUint, r2: &BigUint, n0inv: u32) -> String {
    let to_monty = |hex: &str| -> BigUint { (biguint_from_hex(hex) * r) % p };

    // geq body: lexicographic compare vs literal P limbs, high to low.
    let pl = limbs8(p);
    let mut geq = String::new();
    for i in (0..8).rev() {
        geq.push_str(&format!(
            "    if (a[{i}] != 0x{:08x}u) {{ return a[{i}] > 0x{:08x}u; }}\n",
            pl[i], pl[i]
        ));
    }

    // permutation body: fully generated round schedule with inline Montgomery RCs.
    let mut body = String::new();
    body.push_str("    ext_linear(s);\n");
    for r_idx in 0..4 {
        for l in 0..3 {
            body.push_str(&format!(
                "    (*s)[{l}] = fp_add((*s)[{l}], {});\n",
                fp_lit(&to_monty(RC3_EXT_INITIAL[r_idx][l]))
            ));
        }
        for l in 0..3 {
            body.push_str(&format!("    (*s)[{l}] = sbox((*s)[{l}]);\n"));
        }
        body.push_str("    ext_linear(s);\n");
    }
    for r_idx in 0..56 {
        body.push_str(&format!(
            "    (*s)[0] = fp_add((*s)[0], {});\n    (*s)[0] = sbox((*s)[0]);\n    int_linear(s);\n",
            fp_lit(&to_monty(RC3_INTERNAL[r_idx]))
        ));
    }
    for r_idx in 0..4 {
        for l in 0..3 {
            body.push_str(&format!(
                "    (*s)[{l}] = fp_add((*s)[{l}], {});\n",
                fp_lit(&to_monty(RC3_EXT_TERMINAL[r_idx][l]))
            ));
        }
        for l in 0..3 {
            body.push_str(&format!("    (*s)[{l}] = sbox((*s)[{l}]);\n"));
        }
        body.push_str("    ext_linear(s);\n");
    }

    WGSL_PRELUDE
        .replace("@P_FP@", &fp_lit(p))
        .replace("@R2_FP@", &fp_lit(r2))
        .replace("@N0INV@", &format!("0x{n0inv:08x}"))
        .replace("@GEQ_BODY@", &geq)
        .replace("@PERM_BODY@", &body)
        .replace("@WG@", &wg.to_string())
}

// ============================================================================
// GPU harness
// ============================================================================

struct Gpu {
    device: wgpu::Device,
    queue: wgpu::Queue,
}

impl Gpu {
    fn new() -> Self {
        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
        .expect("no adapter");
        let info = adapter.get_info();
        println!("adapter: {} ({:?})", info.name, info.backend);
        let (device, queue) =
            pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor::default(), None))
                .expect("no device");
        Self { device, queue }
    }

    fn pipeline(&self, source: &str, entry: &str) -> wgpu::ComputePipeline {
        let module = self
            .device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("bn254-poseidon2"),
                source: wgpu::ShaderSource::Wgsl(source.into()),
            });
        self.device
            .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: None,
                layout: None,
                module: &module,
                entry_point: Some(entry),
                compilation_options: Default::default(),
                cache: None,
            })
    }

    /// Upload `input`, dispatch `groups` workgroups, read back `out_len` u32s.
    fn run(
        &self,
        pipeline: &wgpu::ComputePipeline,
        input: &[u32],
        out_len: usize,
        groups: u32,
    ) -> (Vec<u32>, f64) {
        let buf_in = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: None,
                contents: bytemuck::cast_slice(input),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let buf_out = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size: (out_len * 4) as u64,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let buf_read = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size: (out_len * 4) as u64,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let bind = self.bind(pipeline, &buf_in, &buf_out);

        let t0 = std::time::Instant::now();
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut pass = enc.begin_compute_pass(&Default::default());
            pass.set_pipeline(pipeline);
            pass.set_bind_group(0, &bind, &[]);
            pass.dispatch_workgroups(groups, 1, 1);
        }
        queue_submit_wait(&self.device, &self.queue, enc);
        let dt = t0.elapsed().as_secs_f64();

        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(&buf_out, 0, &buf_read, 0, (out_len * 4) as u64);
        self.queue.submit([enc.finish()]);
        let slice = buf_read.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let out: Vec<u32> = bytemuck::cast_slice(&slice.get_mapped_range()).to_vec();
        (out, dt)
    }

    fn bind(
        &self,
        pipeline: &wgpu::ComputePipeline,
        buf_in: &wgpu::Buffer,
        buf_out: &wgpu::Buffer,
    ) -> wgpu::BindGroup {
        self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &pipeline.get_bind_group_layout(0),
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: buf_in.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: buf_out.as_entire_binding(),
                },
            ],
        })
    }
}

fn queue_submit_wait(device: &wgpu::Device, queue: &wgpu::Queue, enc: wgpu::CommandEncoder) {
    queue.submit([enc.finish()]);
    device.poll(wgpu::Maintain::Wait);
}

// ============================================================================
// main
// ============================================================================

fn main() {
    let p = biguint_from_hex(P_HEX);
    let one = BigUint::from(1u32);
    let r = (&one << 256u32) % &p; // Montgomery R
    let r2 = (&r * &r) % &p; // R^2 mod P (to-Montgomery multiplier)

    // n0inv = -P^{-1} mod 2^32 (Newton on the odd low limb).
    let p0 = limbs8(&p)[0];
    let mut inv: u32 = 1;
    for _ in 0..5 {
        inv = inv.wrapping_mul(2u32.wrapping_sub(p0.wrapping_mul(inv)));
    }
    assert_eq!(p0.wrapping_mul(inv), 1, "p0 inverse");
    let n0inv = inv.wrapping_neg();
    assert_eq!(p0.wrapping_mul(n0inv), u32::MAX - 0, "n0inv sanity");
    assert_eq!(
        p0.wrapping_mul(n0inv).wrapping_add(1),
        0,
        "-P*P^-1 = -1 mod 2^32"
    );

    // --- CPU oracle: pinned p3 Poseidon2Bn254<3> must reproduce the gold KAT ---
    let perm = build_p3_perm();
    let mut kat = [
        bn254_from_biguint(&BigUint::from(0u32)),
        bn254_from_biguint(&BigUint::from(1u32)),
        bn254_from_biguint(&BigUint::from(2u32)),
    ];
    perm.permute_mut(&mut kat);
    for i in 0..3 {
        assert_eq!(
            kat[i].as_canonical_biguint(),
            biguint_from_hex(GOLD_KAT_OUT[i]),
            "pinned p3 lane {i} diverges from bn254KATOutHex"
        );
    }
    println!("CPU oracle: pinned p3 Poseidon2Bn254<3> == gnark gold KAT (bn254KATOutHex) OK");

    let gpu = Gpu::new();
    let source = shader_source(256, &p, &r, &r2, n0inv);

    // --- Stage A: field mul/add KAT vs num-bigint ---
    let mut rng = rand::thread_rng();
    let rand_fp = |rng: &mut rand::rngs::ThreadRng| -> BigUint {
        let words: Vec<u32> = (0..8).map(|_| rng.gen::<u32>()).collect();
        limbs_to_biguint(&words) % &p
    };
    let mut pairs: Vec<(BigUint, BigUint)> = vec![
        (BigUint::from(0u32), BigUint::from(0u32)),
        (BigUint::from(1u32), BigUint::from(1u32)),
        (&p - 1u32, &p - 1u32),
        (&p - 1u32, BigUint::from(1u32)),
        (r.clone(), r2.clone()),
    ];
    for _ in 0..1019 {
        pairs.push((rand_fp(&mut rng), rand_fp(&mut rng)));
    }
    let mut kat_in = Vec::with_capacity(pairs.len() * 16);
    for (a, b) in &pairs {
        kat_in.extend_from_slice(&limbs8(a));
        kat_in.extend_from_slice(&limbs8(b));
    }
    let mul_pipe = gpu.pipeline(&source, "mul_kat");
    let (kat_out, _) = gpu.run(
        &mul_pipe,
        &kat_in,
        kat_in.len(),
        (pairs.len() as u32).div_ceil(64),
    );
    let mut bad = 0;
    for (i, (a, b)) in pairs.iter().enumerate() {
        let got_mul = limbs_to_biguint(&kat_out[i * 16..i * 16 + 8]);
        let got_add = limbs_to_biguint(&kat_out[i * 16 + 8..i * 16 + 16]);
        if got_mul != (a * b) % &p || got_add != (a + b) % &p {
            bad += 1;
            if bad <= 3 {
                println!("FIELD KAT MISMATCH pair {i}");
            }
        }
    }
    if bad > 0 {
        println!("FIELD KAT FAILED: {bad}/{} pairs", pairs.len());
        std::process::exit(1);
    }
    println!(
        "field KAT: {} mul+add pairs (incl. 0, 1, P-1 edges) bit-exact vs num-bigint OK",
        pairs.len()
    );

    // --- Stage B: permutation parity batch vs pinned p3 (lane 0 = gold KAT) ---
    const N_PAR: usize = 1 << 16;
    let mut par_inputs: Vec<[BigUint; 3]> = Vec::with_capacity(N_PAR);
    par_inputs.push([
        BigUint::from(0u32),
        BigUint::from(1u32),
        BigUint::from(2u32),
    ]);
    par_inputs.push([
        BigUint::from(0u32),
        BigUint::from(0u32),
        BigUint::from(0u32),
    ]);
    par_inputs.push([&p - 1u32, &p - 1u32, &p - 1u32]);
    while par_inputs.len() < N_PAR {
        par_inputs.push([rand_fp(&mut rng), rand_fp(&mut rng), rand_fp(&mut rng)]);
    }
    let mut par_in = Vec::with_capacity(N_PAR * 24);
    for s in &par_inputs {
        for l in s {
            par_in.extend_from_slice(&limbs8(l));
        }
    }
    let perm_pipe = gpu.pipeline(&source, "perm_main");
    let (par_out, cal_dt) = gpu.run(
        &perm_pipe,
        &par_in,
        par_in.len(),
        (N_PAR as u32).div_ceil(256),
    );

    // gold KAT straight off the GPU
    for i in 0..3 {
        assert_eq!(
            limbs_to_biguint(&par_out[i * 8..i * 8 + 8]),
            biguint_from_hex(GOLD_KAT_OUT[i]),
            "GPU gold-KAT lane {i} mismatch"
        );
    }
    println!("GPU gold KAT: permute([0,1,2]) == bn254KATOutHex OK");

    // full batch vs pinned p3 + CPU single-thread rate
    let t0 = std::time::Instant::now();
    let cpu_out: Vec<[Bn254; 3]> = par_inputs
        .iter()
        .map(|s| {
            let mut st = [
                bn254_from_biguint(&s[0]),
                bn254_from_biguint(&s[1]),
                bn254_from_biguint(&s[2]),
            ];
            perm.permute_mut(&mut st);
            st
        })
        .collect();
    let cpu_dt = t0.elapsed().as_secs_f64();
    let cpu_1t_mperm = N_PAR as f64 / cpu_dt / 1e6;
    let mut bad = 0;
    for i in 0..N_PAR {
        for l in 0..3 {
            let got = limbs_to_biguint(&par_out[(i * 3 + l) * 8..(i * 3 + l) * 8 + 8]);
            if got != cpu_out[i][l].as_canonical_biguint() {
                bad += 1;
                if bad <= 3 {
                    println!("PERM PARITY MISMATCH perm {i} lane {l}");
                }
            }
        }
    }
    if bad > 0 {
        println!("PERM PARITY FAILED: {bad}/{} lanes", N_PAR * 3);
        std::process::exit(1);
    }
    println!(
        "perm parity: {N_PAR} permutations bit-exact vs pinned p3 Poseidon2Bn254<3> OK  \
         (CPU 1-thread raw perm: {cpu_1t_mperm:.3} Mperm/s)"
    );

    // --- Stage C: throughput (one thread per permutation) ---
    // Calibrate batch size to ~0.4s/dispatch (Metal watchdog safety), cap 2^20.
    let cal_rate = N_PAR as f64 / cal_dt; // perms/s incl. first-touch overhead
    let n_perf = ((cal_rate * 0.4) as usize)
        .next_power_of_two()
        .clamp(1 << 16, 1 << 20);
    println!(
        "calibration: {:.3} Mperm/s on the parity dispatch -> perf batch {} perms",
        cal_rate / 1e6,
        n_perf
    );
    let mut perf_in: Vec<u32> = (0..n_perf * 24).map(|_| rng.gen::<u32>()).collect();
    for w in perf_in.chunks_exact_mut(8) {
        w[7] &= 0x0fff_ffff; // top limb < 2^28 < P's top limb -> canonical
    }

    let mut best_overall = 0.0f64;
    let mut best_wg = 0u32;
    for wg in [64u32, 128, 256] {
        let src = shader_source(wg, &p, &r, &r2, n0inv);
        let pipe = gpu.pipeline(&src, "perm_main");
        let buf_in = gpu
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: None,
                contents: bytemuck::cast_slice(&perf_in),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let buf_out = gpu.device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size: (n_perf * 24 * 4) as u64,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let bind = gpu.bind(&pipe, &buf_in, &buf_out);
        let dispatch = || -> f64 {
            let t0 = std::time::Instant::now();
            let mut enc = gpu.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                pass.set_pipeline(&pipe);
                pass.set_bind_group(0, &bind, &[]);
                pass.dispatch_workgroups((n_perf as u32).div_ceil(wg), 1, 1);
            }
            queue_submit_wait(&gpu.device, &gpu.queue, enc);
            t0.elapsed().as_secs_f64()
        };
        dispatch(); // warmup
        let mut best = f64::MAX;
        for run in 0..5 {
            let dt = dispatch();
            let mperm = n_perf as f64 / dt / 1e6;
            println!(
                "  wg={wg} run {run}: {:.1} ms  ({mperm:.3} Mperm/s)",
                dt * 1e3
            );
            best = best.min(dt);
        }
        let mperm = n_perf as f64 / best / 1e6;
        println!("wg={wg} best: {mperm:.3} Mperm/s");
        if mperm > best_overall {
            best_overall = mperm;
            best_wg = wg;
        }
    }

    // --- Verdict ---
    let cpu_stack_lo = 0.13; // conservative figure (task brief)
    let cpu_stack = 0.18; // measured exact-outer-stack rayon-12 (WIRING-PLAN §2: 0.17-0.19)
    let ratio = best_overall / cpu_stack;
    let ratio_lo = best_overall / cpu_stack_lo;
    let amdahl = |s: f64| 1.0 / (0.60 / s + 0.40);
    println!("\n=== RESULT (BN254 t=3 Poseidon2, wgpu/WGSL, one thread/perm) ===");
    println!(
        "GPU best: {best_overall:.3} Mperm/s (wg={best_wg}, batch {n_perf}); \
         CPU 1-thread raw perm {cpu_1t_mperm:.3} Mperm/s"
    );
    println!(
        "vs CPU MMCS-stack 0.17-0.19 Mperm/s (rayon-12): {ratio:.1}x   \
         (vs conservative 0.13: {ratio_lo:.1}x)"
    );
    println!(
        "Amdahl on the ~95s shrink (BN254 hash ~60%): e2e ~{:.2}x  \
         (hash-free ceiling 2.5x)",
        amdahl(ratio)
    );
    if ratio >= 5.0 {
        println!(
            "VERDICT: wgpu accelerates the shrink's dominant kernel {ratio:.1}x — \
             GPU-wiring the BN254 MMCS is worth it."
        );
    } else if ratio >= 2.0 {
        println!(
            "VERDICT: marginal ({ratio:.1}x) — the 8-limb Montgomery tax bites; \
             weigh against wiring cost."
        );
    } else {
        println!(
            "VERDICT: COLLAPSE ({ratio:.1}x) — 256-bit Montgomery in 32-bit WGSL \
             eats the parallelism; keep the shrink CPU-side, spend GPU effort on \
             the all-BabyBear inner fold."
        );
    }
}

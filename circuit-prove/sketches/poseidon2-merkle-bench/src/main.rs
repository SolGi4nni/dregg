//! Poseidon2-BabyBear-w16 + Merkle-commit head-to-head: native Metal vs wgpu/WGSL.
//!
//! WHY THIS PROBE DECIDES THE BACKEND: the NTT probes (siblings
//! `metal-babybear-ntt` / `wgpu-babybear-ntt`) came back a bandwidth-bound tie
//! (±15%) — the native ~3x ALU advantage on Montgomery mul (mulhi 320 Gmul/s vs
//! the WGSL 16-bit split's 60-106) bought nothing because the NTT hides all math
//! behind memory. Poseidon2 is the opposite: ~655 dependent Montgomery muls +
//! ~1300 modular adds per permutation against only 128 B of I/O — COMPUTE-BOUND —
//! and the shrink prover is HASH-DOMINATED (WRAP-NATIVE-HASH-DECISION.md: the
//! ~188M-constraint emulated wrap is ~185M hashing; the Rust-side shrink prove is
//! Merkle-commit heavy the same way). If the ALU gap translates here, native
//! Metal is worth a seam for the hash side even though the NTT said portable.
//!
//! WHAT RUNS:
//!   1. Bit-exact parity FIRST (both backends, every kernel): the pinned Plonky3
//!      82cfad7 `default_babybear_poseidon2_16` KAT (baby-bear/src/poseidon2.rs
//!      test_default_babybear_poseidon2_width_16), a 4096-state random batch, a
//!      16-chained batch, and full Merkle roots at every measured size vs the
//!      real p3 `PaddingFreeSponge<Perm,16,8,8>` + `TruncatedPermutation<Perm,2,8,16>`
//!      (the exact MMCS hash/compress pair from circuit-prove
//!      plonky3_recursion_impl.rs:70-78).
//!   2. Permutation throughput: one thread per state, SoA, CHAIN=1 (with I/O)
//!      and CHAIN=16 (ALU-bound, I/O amortized 16x).
//!   3. Merkle commit: N leaves (8 BabyBear elems each -> 1 sponge perm), then
//!      compress 2->1 up to the root (one w16 perm per node) — the MMCS commit
//!      pattern — at N = 2^18..2^21 (shrink-trace scale).
//!   4. Interleaved A/B measurement (native/wgpu alternating, best-of), CPU
//!      (rayon, scalar p3 perm) reference alongside.
//!
//! Permutation structure (pinned 82cfad7, verified against the crate source):
//!   x^7 S-box (BABYBEAR_S_BOX_DEGREE = 7 — NOT x^5), RF = 8 (4 initial + 4
//!   terminal external rounds), RP = 13 internal rounds; the external linear
//!   layer is the MDSMat4-based mds_light applied ONCE up front and then after
//!   every external round; the internal layer is 1 + Diag(V),
//!   V = [-2,1,2,1/2,3,4,-1/2,-3,-4,1/2^8,1/4,1/8,1/2^27,-1/2^8,-1/16,-1/2^27].
//!   Data stays in 32-bit Montgomery form end-to-end; division by 2^k is an
//!   exact Montgomery mul by 2^(32-k) mod P; round constants are baked into the
//!   shader source in Montgomery form, extracted from the p3 arrays at runtime
//!   (no transcription).
//!
//! Both backends run the IDENTICAL generated straight-line body (assignments to
//! predeclared u32 vars are syntactically identical in MSL and WGSL); only the
//! kernel wrappers and the mmul/addp/subp/halve prelude differ (native mulhi vs
//! the 16-bit-split emulation — exactly the thing being measured). The wgpu side
//! carries both measured probe fixes: zero_initialize_workgroup_memory=false
//! (moot here — no workgroup memory) and ShaderRuntimeChecks::unchecked().
//!
//! Run: `cargo run --release` (this crate opts out of the root workspace).

use metal::{
    Buffer as MtlBuffer, CommandQueue, CompileOptions, ComputePipelineState, Device as MtlDevice,
    MTLResourceOptions, MTLSize,
};
use objc::rc::autoreleasepool;
use p3_baby_bear::{
    default_babybear_poseidon2_16, BabyBear, Poseidon2BabyBear,
    BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL, BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
    BABYBEAR_POSEIDON2_RC_16_INTERNAL,
};
use p3_field::PrimeField32;
use p3_symmetric::{
    CryptographicHasher, PaddingFreeSponge, Permutation, PseudoCompressionFunction,
    TruncatedPermutation,
};
use rand::Rng;
use rayon::prelude::*;
use std::time::Instant;

const P: u32 = 0x7800_0001; // BabyBear prime
const MU: u32 = 0x8800_0001; // P^{-1} mod 2^32 (p3 MONTY_MU)

type Perm = Poseidon2BabyBear<16>;
type LeafHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;

// ---------- host-side BabyBear helpers (identical to the NTT probes) ----------

fn to_mont(a: u32) -> u32 {
    (((a as u64) << 32) % P as u64) as u32
}

fn montmul(a: u32, b: u32) -> u32 {
    let x = a as u64 * b as u64;
    let t = (x as u32).wrapping_mul(MU);
    let u = t as u64 * P as u64;
    let xhi = (x >> 32) as u32;
    let uhi = (u >> 32) as u32;
    let (r, borrow) = xhi.overflowing_sub(uhi);
    if borrow {
        r.wrapping_add(P)
    } else {
        r
    }
}

fn from_mont(a: u32) -> u32 {
    montmul(a, 1)
}

// ---------- permutation body codegen (backend-neutral straight-line code) ----------
//
// Emits ONLY assignment statements over predeclared u32 variables
// (s0..s15, t0..t6, m0..m3, sum, fsum) using the functions mmul/addp/subp/halve
// — valid, identical source text in both MSL and WGSL.

/// x -> x^7 (4 mmuls), in place on variable `v`; t5/t6 as scratch.
fn sbox(v: &str) -> String {
    format!(
        "t5 = mmul({v}, {v});\n\
         t6 = mmul(t5, {v});\n\
         t5 = mmul(t6, t6);\n\
         {v} = mmul(t5, {v});\n"
    )
}

/// The fast 4x4 MDS: [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]] (p3 apply_mat4).
fn mat4(a: &str, b: &str, c: &str, d: &str) -> String {
    format!(
        "t0 = addp({a}, {b});\n\
         t1 = addp({c}, {d});\n\
         t2 = addp(t0, t1);\n\
         t3 = addp(t2, {b});\n\
         t4 = addp(t2, {d});\n\
         {d} = addp(t4, addp({a}, {a}));\n\
         {b} = addp(t3, addp({c}, {c}));\n\
         {a} = addp(t3, t0);\n\
         {c} = addp(t4, t1);\n"
    )
}

/// External linear layer: mat4 per 4-chunk, then the circulant sums
/// (p3 mds_light_permutation with MDSMat4, WIDTH=16).
fn mds_light() -> String {
    let mut s = String::new();
    for ch in 0..4 {
        let i = 4 * ch;
        let v: Vec<String> = (i..i + 4).map(|k| format!("s{k}")).collect();
        s += &mat4(&v[0], &v[1], &v[2], &v[3]);
    }
    for k in 0..4 {
        s += &format!(
            "m{k} = addp(addp(s{}, s{}), addp(s{}, s{}));\n",
            k,
            k + 4,
            k + 8,
            k + 12
        );
    }
    for i in 0..16 {
        s += &format!("s{i} = addp(s{i}, m{});\n", i % 4);
    }
    s
}

/// One external round: add round constants (Montgomery form), x^7 each lane,
/// external linear layer.
fn ext_round(rc_mont: &[u32; 16]) -> String {
    let mut s = String::new();
    for i in 0..16 {
        s += &format!("s{i} = addp(s{i}, {}u);\n", rc_mont[i]);
        s += &sbox(&format!("s{i}"));
    }
    s += &mds_light();
    s
}

/// One internal round: rc + x^7 on lane 0, then 1 + Diag(V).
/// Division by 2^k is Montgomery-mul by 2^(32-k) mod P (exact — see module doc).
fn int_round(rc_mont: u32) -> String {
    let inv2_8 = 1u32 << 24;
    let inv2_2 = 1u32 << 30;
    let inv2_3 = 1u32 << 29;
    let inv2_4 = 1u32 << 28;
    let inv2_27 = 1u32 << 5;
    let mut s = format!("s0 = addp(s0, {rc_mont}u);\n");
    s += &sbox("s0");
    s += "sum = addp(addp(addp(addp(s1, s2), addp(s3, s4)), addp(addp(s5, s6), addp(s7, s8))), addp(addp(addp(s9, s10), addp(s11, s12)), addp(addp(s13, s14), s15)));\n";
    s += "fsum = addp(sum, s0);\n";
    s += "s0 = subp(sum, s0);\n"; // V[0] = -2: part_sum - s0 = full_sum - 2*s0
    s += "s1 = addp(s1, fsum);\n";
    s += "s2 = addp(addp(s2, s2), fsum);\n";
    s += "s3 = addp(halve(s3), fsum);\n";
    s += "t0 = addp(s4, s4);\ns4 = addp(fsum, addp(t0, s4));\n"; // 3x
    s += "t0 = addp(s5, s5);\ns5 = addp(fsum, addp(t0, t0));\n"; // 4x
    s += "s6 = subp(fsum, halve(s6));\n";
    s += "t0 = addp(s7, s7);\ns7 = subp(fsum, addp(t0, s7));\n"; // -3x
    s += "t0 = addp(s8, s8);\ns8 = subp(fsum, addp(t0, t0));\n"; // -4x
    s += &format!("s9 = addp(mmul(s9, {inv2_8}u), fsum);\n");
    s += &format!("s10 = addp(mmul(s10, {inv2_2}u), fsum);\n");
    s += &format!("s11 = addp(mmul(s11, {inv2_3}u), fsum);\n");
    s += &format!("s12 = addp(mmul(s12, {inv2_27}u), fsum);\n");
    s += &format!("s13 = subp(fsum, mmul(s13, {inv2_8}u));\n");
    s += &format!("s14 = subp(fsum, mmul(s14, {inv2_4}u));\n");
    s += &format!("s15 = subp(fsum, mmul(s15, {inv2_27}u));\n");
    s
}

/// The full width-16 permutation body: initial mds_light, 4 external, 13
/// internal, 4 external (p3 permute_mut order).
fn perm_body(rc_ei: &[[u32; 16]; 4], rc_ef: &[[u32; 16]; 4], rc_int: &[u32; 13]) -> String {
    let mut s = mds_light();
    for rc in rc_ei {
        s += &ext_round(rc);
    }
    for &rc in rc_int {
        s += &int_round(rc);
    }
    for rc in rc_ef {
        s += &ext_round(rc);
    }
    s
}

// ---------- MSL ----------

const MSL_PRELUDE: &str = r#"
#include <metal_stdlib>
using namespace metal;

constant uint P = 0x78000001u;
constant uint MU = 0x88000001u;

// Montgomery product, exactly the p3 monty-31 reduce, on NATIVE wide muls:
// 4 hardware 32-bit muls (the native lever under test).
inline uint mmul(uint a, uint b) {
    uint hi = mulhi(a, b);
    uint t = (a * b) * MU;
    uint tp = mulhi(t, P);
    uint r = hi - tp;
    return (hi < tp) ? r + P : r;
}

inline uint addp(uint a, uint b) { uint s = a + b; return (s >= P) ? s - P : s; }
inline uint subp(uint a, uint b) { return (a < b) ? a - b + P : a - b; }
// Exact halving of the Montgomery representative (field division by 2).
inline uint halve(uint a) { return (a & 1u) ? ((a >> 1) + 0x3C000001u) : (a >> 1); }
"#;

fn decls_msl() -> String {
    "    uint t0=0u,t1=0u,t2=0u,t3=0u,t4=0u,t5=0u,t6=0u,m0=0u,m1=0u,m2=0u,m3=0u,sum=0u,fsum=0u;\n"
        .into()
}

/// One thread per state, SoA (state lane j of thread i at [i + j*N]),
/// CHAIN permutations chained in-register.
fn msl_perm(body: &str, n: u32, chain: u32) -> String {
    let loads: String = (0..16)
        .map(|j| format!("    uint s{j} = src[i + {}u];\n", j * n))
        .collect();
    let stores: String = (0..16)
        .map(|j| format!("    data[i + {}u] = s{j};\n", j * n))
        .collect();
    format!(
        "{MSL_PRELUDE}
kernel void k_perm(device uint* data [[buffer(0)]],
                   const device uint* src [[buffer(1)]],
                   uint3 gid [[thread_position_in_grid]]) {{
    uint i = gid.x;
{loads}{}
    for (uint it = 0u; it < {chain}u; it++) {{
{body}
    }}
{stores}}}
",
        decls_msl()
    )
}

/// Leaf hash: 8 BabyBear elems (SoA in src) -> PaddingFreeSponge (one block,
/// zero capacity) -> digest into heap node N+i of the tree buffer (AoS x8).
fn msl_leaf(body: &str, n: u32) -> String {
    let loads: String = (0..8)
        .map(|j| format!("    uint s{j} = src[i + {}u];\n", j * n))
        .collect();
    let zeros: String = (8..16).map(|j| format!("    uint s{j} = 0u;\n")).collect();
    let stores: String = (0..8)
        .map(|j| format!("    data[ob + {j}u] = s{j};\n"))
        .collect();
    format!(
        "{MSL_PRELUDE}
kernel void k_leaf(device uint* data [[buffer(0)]],
                   const device uint* src [[buffer(1)]],
                   uint3 gid [[thread_position_in_grid]]) {{
    uint i = gid.x;
{loads}{zeros}{}
{body}
    uint ob = ({n}u + i) * 8u;
{stores}}}
",
        decls_msl()
    )
}

/// One tree level: node (nout+i) <- TruncatedPermutation of children
/// 2(nout+i), 2(nout+i)+1 (their digests are 16 contiguous u32).
fn msl_compress(body: &str) -> String {
    let loads: String = (0..16)
        .map(|j| format!("    uint s{j} = data[ib + {j}u];\n"))
        .collect();
    let stores: String = (0..8)
        .map(|j| format!("    data[ob + {j}u] = s{j};\n"))
        .collect();
    format!(
        "{MSL_PRELUDE}
kernel void k_compress(device uint* data [[buffer(0)]],
                       constant uint& nout [[buffer(2)]],
                       uint3 gid [[thread_position_in_grid]]) {{
    uint i = gid.x;
    if (i >= nout) {{ return; }}
    uint ib = (nout + i) * 16u;
{loads}{}
{body}
    uint ob = (nout + i) * 8u;
{stores}}}
",
        decls_msl()
    )
}

// ---------- WGSL ----------

const WGSL_PRELUDE: &str = r#"
const P: u32 = 0x78000001u;
const MU: u32 = 0x88000001u;

// 32x32 -> 64 multiply via 16-bit split (WGSL has no u64 and no mulhi) —
// the portable emulation tax under test.
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

fn mmul(a: u32, b: u32) -> u32 {
    let ab = mul64(a, b);
    let t = ab.x * MU;
    let tp = mul64(t, P);
    var r: u32 = ab.y - tp.y;
    if (ab.y < tp.y) { r += P; }
    return r;
}

fn addp(a: u32, b: u32) -> u32 {
    let s = a + b;
    return select(s, s - P, s >= P);
}

fn subp(a: u32, b: u32) -> u32 {
    var r = a - b;
    if (a < b) { r += P; }
    return r;
}

fn halve(a: u32) -> u32 {
    return select(a >> 1u, (a >> 1u) + 0x3C000001u, (a & 1u) != 0u);
}
"#;

fn decls_wgsl() -> String {
    [
        "t0", "t1", "t2", "t3", "t4", "t5", "t6", "m0", "m1", "m2", "m3", "sum", "fsum",
    ]
    .iter()
    .map(|v| format!("    var {v} = 0u;\n"))
    .collect()
}

fn wgsl_perm(body: &str, n: u32, chain: u32) -> String {
    let loads: String = (0..16)
        .map(|j| format!("    var s{j} = src[i + {}u];\n", j * n))
        .collect();
    let stores: String = (0..16)
        .map(|j| format!("    data[i + {}u] = s{j};\n", j * n))
        .collect();
    format!(
        "{WGSL_PRELUDE}
@group(0) @binding(0) var<storage, read_write> data: array<u32>;
@group(0) @binding(1) var<storage, read> src: array<u32>;
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {{
    let i = gid.x;
{loads}{}
    for (var it = 0u; it < {chain}u; it = it + 1u) {{
{body}
    }}
{stores}}}
",
        decls_wgsl()
    )
}

fn wgsl_leaf(body: &str, n: u32) -> String {
    let loads: String = (0..8)
        .map(|j| format!("    var s{j} = src[i + {}u];\n", j * n))
        .collect();
    let zeros: String = (8..16).map(|j| format!("    var s{j} = 0u;\n")).collect();
    let stores: String = (0..8)
        .map(|j| format!("    data[ob + {j}u] = s{j};\n"))
        .collect();
    format!(
        "{WGSL_PRELUDE}
@group(0) @binding(0) var<storage, read_write> data: array<u32>;
@group(0) @binding(1) var<storage, read> src: array<u32>;
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {{
    let i = gid.x;
{loads}{zeros}{}
{body}
    let ob = ({n}u + i) * 8u;
{stores}}}
",
        decls_wgsl()
    )
}

fn wgsl_compress(body: &str) -> String {
    let loads: String = (0..16)
        .map(|j| format!("    var s{j} = data[ib + {j}u];\n"))
        .collect();
    let stores: String = (0..8)
        .map(|j| format!("    data[ob + {j}u] = s{j};\n"))
        .collect();
    format!(
        "{WGSL_PRELUDE}
struct Params {{ nout: u32 }};
@group(0) @binding(0) var<storage, read_write> data: array<u32>;
@group(0) @binding(2) var<uniform> params: Params;
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {{
    let i = gid.x;
    if (i >= params.nout) {{ return; }}
    let ib = (params.nout + i) * 16u;
{loads}{}
{body}
    let ob = (params.nout + i) * 8u;
{stores}}}
",
        decls_wgsl()
    )
}

// ---------- Metal harness (mirrors metal-babybear-ntt) ----------

const DATA_U32S: usize = 1 << 25; // 128 MiB: tree heap for N=2^21 (2N nodes x 8)
const SRC_U32S: usize = 1 << 24; // 64 MiB: 2^20 states x16 SoA / 2^21 leaves x8 SoA

struct MGpu {
    device: MtlDevice,
    queue: CommandQueue,
    buf_data: MtlBuffer,
    buf_src: MtlBuffer,
}

impl MGpu {
    fn new() -> Self {
        let device = MtlDevice::system_default().expect("no Metal device");
        println!(
            "metal device: {} (unified memory: {})",
            device.name(),
            device.has_unified_memory()
        );
        let queue = device.new_command_queue();
        let opts = MTLResourceOptions::StorageModeShared;
        let buf_data = device.new_buffer((DATA_U32S * 4) as u64, opts);
        let buf_src = device.new_buffer((SRC_U32S * 4) as u64, opts);
        MGpu {
            device,
            queue,
            buf_data,
            buf_src,
        }
    }

    fn pipeline(&self, msl: &str, func: &str, label: &str) -> ComputePipelineState {
        let options = CompileOptions::new();
        let lib = self
            .device
            .new_library_with_source(msl, &options)
            .unwrap_or_else(|e| panic!("MSL compile failed for {label}: {e}"));
        let f = lib
            .get_function(func, None)
            .unwrap_or_else(|e| panic!("no function {func} in {label}: {e}"));
        self.device
            .new_compute_pipeline_state_with_function(&f)
            .unwrap_or_else(|e| panic!("pipeline failed for {label}: {e}"))
    }

    fn write_src(&self, data: &[u32]) {
        assert!(data.len() * 4 <= self.buf_src.length() as usize);
        unsafe {
            std::ptr::copy_nonoverlapping(
                data.as_ptr(),
                self.buf_src.contents() as *mut u32,
                data.len(),
            );
        }
    }

    fn read_data(&self, off_u32: usize, n_u32: usize) -> Vec<u32> {
        let mut out = vec![0u32; n_u32];
        unsafe {
            std::ptr::copy_nonoverlapping(
                (self.buf_data.contents() as *const u32).add(off_u32),
                out.as_mut_ptr(),
                n_u32,
            );
        }
        out
    }

    /// One command buffer with `iters` repetitions of the encoded plan;
    /// wall seconds per iteration.
    fn time_once(&self, encode: &dyn Fn(&metal::ComputeCommandEncoderRef), iters: u32) -> f64 {
        autoreleasepool(|| {
            let t0 = Instant::now();
            let cb = self.queue.new_command_buffer();
            let enc = cb.new_compute_command_encoder();
            enc.set_buffer(0, Some(&self.buf_data), 0);
            enc.set_buffer(1, Some(&self.buf_src), 0);
            for _ in 0..iters {
                encode(enc);
            }
            enc.end_encoding();
            cb.commit();
            cb.wait_until_completed();
            t0.elapsed().as_secs_f64() / iters as f64
        })
    }
}

fn mtl_dispatch(enc: &metal::ComputeCommandEncoderRef, pipe: &ComputePipelineState, threads: u32) {
    enc.set_compute_pipeline_state(pipe);
    let groups = (threads as u64).div_ceil(256).max(1);
    enc.dispatch_thread_groups(MTLSize::new(groups, 1, 1), MTLSize::new(256, 1, 1));
}

fn mtl_encode_tree(
    enc: &metal::ComputeCommandEncoderRef,
    leaf: &ComputePipelineState,
    compress: &ComputePipelineState,
    n: u32,
) {
    mtl_dispatch(enc, leaf, n);
    let mut nout = n / 2;
    loop {
        enc.set_compute_pipeline_state(compress);
        enc.set_bytes(2, 4, &nout as *const u32 as *const std::ffi::c_void);
        let groups = (nout as u64).div_ceil(256).max(1);
        enc.dispatch_thread_groups(MTLSize::new(groups, 1, 1), MTLSize::new(256, 1, 1));
        if nout == 1 {
            break;
        }
        nout /= 2;
    }
}

// ---------- wgpu harness (mirrors wgpu-babybear-ntt, incl. both probe fixes) ----------

struct WGpu {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipe_layout: wgpu::PipelineLayout,
    bind_main: wgpu::BindGroup,
    level_binds: Vec<wgpu::BindGroup>, // index k: nout = 1 << k
    buf_data: wgpu::Buffer,
    buf_read: wgpu::Buffer,
    buf_src: wgpu::Buffer,
}

impl WGpu {
    fn new() -> Self {
        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
        .expect("no adapter");
        let info = adapter.get_info();
        println!("wgpu adapter: {} ({:?})", info.name, info.backend);
        let lims = adapter.limits();
        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: None,
                required_features: wgpu::Features::empty(),
                required_limits: lims,
                memory_hints: Default::default(),
            },
            None,
        ))
        .expect("no device");

        let entry = |binding, ty| wgpu::BindGroupLayoutEntry {
            binding,
            visibility: wgpu::ShaderStages::COMPUTE,
            ty,
            count: None,
        };
        let storage = |ro| wgpu::BindingType::Buffer {
            ty: wgpu::BufferBindingType::Storage { read_only: ro },
            has_dynamic_offset: false,
            min_binding_size: None,
        };
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: None,
            entries: &[
                entry(0, storage(false)),
                entry(1, storage(true)),
                entry(
                    2,
                    wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Uniform,
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                ),
            ],
        });
        let pipe_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: None,
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });

        let mkbuf = |label, size, usage| {
            device.create_buffer(&wgpu::BufferDescriptor {
                label: Some(label),
                size,
                usage,
                mapped_at_creation: false,
            })
        };
        let buf_data = mkbuf(
            "data",
            (DATA_U32S * 4) as u64,
            wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_SRC
                | wgpu::BufferUsages::COPY_DST,
        );
        let buf_src = mkbuf(
            "src",
            (SRC_U32S * 4) as u64,
            wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        );
        let buf_read = mkbuf(
            "read",
            (DATA_U32S * 4) as u64,
            wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
        );

        // Per-level uniform param buffers (nout = 1 << k) + bind groups.
        let mut level_binds = Vec::new();
        let bind_for = |param: &wgpu::Buffer| {
            device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: None,
                layout: &bgl,
                entries: &[
                    wgpu::BindGroupEntry {
                        binding: 0,
                        resource: buf_data.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 1,
                        resource: buf_src.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 2,
                        resource: param.as_entire_binding(),
                    },
                ],
            })
        };
        let mut params = Vec::new();
        for k in 0..=20u32 {
            let b = mkbuf(
                "param",
                16,
                wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            );
            queue.write_buffer(&b, 0, bytemuck::cast_slice(&[1u32 << k, 0, 0, 0]));
            params.push(b);
        }
        for b in &params {
            level_binds.push(bind_for(b));
        }
        let bind_main = bind_for(&params[0]);
        WGpu {
            device,
            queue,
            pipe_layout,
            bind_main,
            level_binds,
            buf_data,
            buf_read,
            buf_src,
        }
    }

    fn pipeline(&self, wgsl: &str, label: &str) -> wgpu::ComputePipeline {
        // Trusted module: skip naga's per-access bounds checks (indices are
        // audited; parity vs p3 validates every run) — measured probe fix #2.
        let module = unsafe {
            self.device.create_shader_module_trusted(
                wgpu::ShaderModuleDescriptor {
                    label: Some(label),
                    source: wgpu::ShaderSource::Wgsl(wgsl.into()),
                },
                wgpu::ShaderRuntimeChecks::unchecked(),
            )
        };
        self.device
            .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(label),
                layout: Some(&self.pipe_layout),
                module: &module,
                entry_point: Some("main"),
                // Measured probe fix #1 (moot here — no workgroup memory —
                // but kept for protocol identity with the NTT probes).
                compilation_options: wgpu::PipelineCompilationOptions {
                    zero_initialize_workgroup_memory: false,
                    ..Default::default()
                },
                cache: None,
            })
    }

    fn write_src(&self, data: &[u32]) {
        self.queue
            .write_buffer(&self.buf_src, 0, bytemuck::cast_slice(data));
        self.device.poll(wgpu::Maintain::Wait);
    }

    fn time_once(&self, encode: &dyn Fn(&mut wgpu::ComputePass, &WGpu), iters: u32) -> f64 {
        let t0 = Instant::now();
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut pass = enc.begin_compute_pass(&Default::default());
            for _ in 0..iters {
                encode(&mut pass, self);
            }
        }
        self.queue.submit([enc.finish()]);
        self.device.poll(wgpu::Maintain::Wait);
        t0.elapsed().as_secs_f64() / iters as f64
    }

    fn read_data(&self, off_u32: usize, n_u32: usize) -> Vec<u32> {
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(
            &self.buf_data,
            (off_u32 * 4) as u64,
            &self.buf_read,
            0,
            (n_u32 * 4) as u64,
        );
        self.queue.submit([enc.finish()]);
        let slice = self.buf_read.slice(..(n_u32 * 4) as u64);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let out: Vec<u32> = bytemuck::cast_slice(&slice.get_mapped_range()).to_vec();
        self.buf_read.unmap();
        out
    }
}

fn wgpu_encode_tree(
    pass: &mut wgpu::ComputePass,
    gpu: &WGpu,
    leaf: &wgpu::ComputePipeline,
    compress: &wgpu::ComputePipeline,
    n: u32,
) {
    pass.set_bind_group(0, &gpu.bind_main, &[]);
    pass.set_pipeline(leaf);
    pass.dispatch_workgroups((n / 256).max(1), 1, 1);
    pass.set_pipeline(compress);
    let mut k = n.trailing_zeros() as i32 - 1; // nout = 2^k, from n/2 down to 1
    while k >= 0 {
        let nout = 1u32 << k;
        pass.set_bind_group(0, &gpu.level_binds[k as usize], &[]);
        pass.dispatch_workgroups(nout.div_ceil(256).max(1), 1, 1);
        k -= 1;
    }
}

// ---------- host oracle (the REAL pinned p3 types) ----------

fn host_perm_canonical(perm: &Perm, st: &[u32; 16]) -> [u32; 16] {
    let mut s = st.map(BabyBear::new);
    perm.permute_mut(&mut s);
    s.map(|x| x.as_canonical_u32())
}

/// Full host Merkle tree (rayon over the exact p3 hash/compress pair);
/// returns (root, leaf0 digest, build seconds).
fn host_tree(
    hasher: &LeafHash,
    compress: &Compress,
    leaves: &[[u32; 8]],
) -> ([u32; 8], [u32; 8], f64) {
    let t0 = Instant::now();
    let mut level: Vec<[BabyBear; 8]> = leaves
        .par_iter()
        .map(|l| hasher.hash_iter(l.map(BabyBear::new)))
        .collect();
    let leaf0 = level[0].map(|x| x.as_canonical_u32());
    while level.len() > 1 {
        level = level
            .par_chunks(2)
            .map(|p| compress.compress([p[0], p[1]]))
            .collect();
    }
    (
        level[0].map(|x| x.as_canonical_u32()),
        leaf0,
        t0.elapsed().as_secs_f64(),
    )
}

// ---------- data packing ----------

/// SoA Montgomery pack: lane j of state i at [i + j*n].
fn pack_soa<const W: usize>(states: &[[u32; W]], n: usize) -> Vec<u32> {
    assert_eq!(states.len(), n);
    let mut v = vec![0u32; W * n];
    for (i, st) in states.iter().enumerate() {
        for j in 0..W {
            v[i + j * n] = to_mont(st[j]);
        }
    }
    v
}

fn unpack_soa_state(buf: &[u32], n: usize, i: usize) -> [u32; 16] {
    core::array::from_fn(|j| from_mont(buf[i + j * n]))
}

// ---------- measurement ----------

/// Interleaved A/B: alternate native/wgpu timed submissions, best-of-REPS each.
fn interleave(
    reps: u32,
    mut native: impl FnMut() -> f64,
    mut wgpu_run: impl FnMut() -> f64,
) -> (f64, f64) {
    native();
    wgpu_run(); // warmup both
    let (mut bn, mut bw) = (f64::MAX, f64::MAX);
    for _ in 0..reps {
        bn = bn.min(native());
        bw = bw.min(wgpu_run());
    }
    (bn, bw)
}

fn main() {
    // ---- round constants from the pinned p3 arrays (no transcription) ----
    let rc_ei: [[u32; 16]; 4] = BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL
        .map(|row| row.map(|x| to_mont(x.as_canonical_u32())));
    let rc_ef: [[u32; 16]; 4] = BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL
        .map(|row| row.map(|x| to_mont(x.as_canonical_u32())));
    let rc_int: [u32; 13] =
        BABYBEAR_POSEIDON2_RC_16_INTERNAL.map(|x| to_mont(x.as_canonical_u32()));

    let body = perm_body(&rc_ei, &rc_ef, &rc_int);
    let mmuls = body.matches("mmul(").count();
    let adds = body.matches("addp(").count() + body.matches("subp(").count();
    println!("perm body: {mmuls} Montgomery muls + {adds} modular add/subs per permutation");

    // ---- host oracle sanity: the pinned KAT (baby-bear/src/poseidon2.rs:580) ----
    let perm = default_babybear_poseidon2_16();
    let hasher = LeafHash::new(perm.clone());
    let compress = Compress::new(perm.clone());
    let kat_in: [u32; 16] = [
        894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
        19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913,
    ];
    let kat_out: [u32; 16] = [
        516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026, 1788910906, 563338433,
        319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758, 1052633829,
        1344246938,
    ];
    assert_eq!(
        host_perm_canonical(&perm, &kat_in),
        kat_out,
        "host p3 oracle does not reproduce the pinned KAT"
    );
    println!("host p3 oracle reproduces the pinned width-16 KAT ✓");

    // ---- GPUs + pipelines ----
    let mg = MGpu::new();
    let wg = WGpu::new();

    const N_PERM: u32 = 1 << 20;
    const N_CHAIN: u32 = 1 << 18;
    const CHAIN: u32 = 16;
    let tree_sizes: Vec<u32> = vec![1 << 10, 1 << 18, 1 << 19, 1 << 20, 1 << 21];

    let t0 = Instant::now();
    let m_perm1 = mg.pipeline(&msl_perm(&body, N_PERM, 1), "k_perm", "m-perm1");
    let m_perm16 = mg.pipeline(&msl_perm(&body, N_CHAIN, CHAIN), "k_perm", "m-perm16");
    let m_compress = mg.pipeline(&msl_compress(&body), "k_compress", "m-compress");
    let m_leaf: Vec<ComputePipelineState> = tree_sizes
        .iter()
        .map(|&n| mg.pipeline(&msl_leaf(&body, n), "k_leaf", &format!("m-leaf{n}")))
        .collect();
    println!(
        "metal pipelines compiled in {:.1}s",
        t0.elapsed().as_secs_f64()
    );

    let t0 = Instant::now();
    let w_perm1 = wg.pipeline(&wgsl_perm(&body, N_PERM, 1), "w-perm1");
    let w_perm16 = wg.pipeline(&wgsl_perm(&body, N_CHAIN, CHAIN), "w-perm16");
    let w_compress = wg.pipeline(&wgsl_compress(&body), "w-compress");
    let w_leaf: Vec<wgpu::ComputePipeline> = tree_sizes
        .iter()
        .map(|&n| wg.pipeline(&wgsl_leaf(&body, n), &format!("w-leaf{n}")))
        .collect();
    println!(
        "wgpu pipelines compiled in {:.1}s",
        t0.elapsed().as_secs_f64()
    );

    // ================= PARITY GATE 1: permutation batch =================
    let mut rng = rand::thread_rng();
    let mut states: Vec<[u32; 16]> = (0..N_PERM as usize)
        .map(|_| core::array::from_fn(|_| rng.gen_range(0..P)))
        .collect();
    states[0] = kat_in; // slot 0 carries the KAT
    let soa = pack_soa(&states, N_PERM as usize);

    mg.write_src(&soa);
    wg.write_src(&soa);
    mg.time_once(&|enc| mtl_dispatch(enc, &m_perm1, N_PERM), 1);
    wg.time_once(
        &|pass, g| {
            pass.set_bind_group(0, &g.bind_main, &[]);
            pass.set_pipeline(&w_perm1);
            pass.dispatch_workgroups(N_PERM / 256, 1, 1);
        },
        1,
    );
    let m_out = mg.read_data(0, 16 * N_PERM as usize);
    let w_out = wg.read_data(0, 16 * N_PERM as usize);
    let n_check = 4096usize;
    let expected: Vec<[u32; 16]> = states[..n_check]
        .par_iter()
        .map(|s| host_perm_canonical(&perm, s))
        .collect();
    for i in 0..n_check {
        assert_eq!(
            unpack_soa_state(&m_out, N_PERM as usize, i),
            expected[i],
            "METAL perm parity FAILED at state {i}"
        );
        assert_eq!(
            unpack_soa_state(&w_out, N_PERM as usize, i),
            expected[i],
            "WGPU perm parity FAILED at state {i}"
        );
    }
    assert_eq!(unpack_soa_state(&m_out, N_PERM as usize, 0), kat_out);
    assert_eq!(unpack_soa_state(&w_out, N_PERM as usize, 0), kat_out);
    println!("parity ✓ permutation: KAT + {n_check} random states bit-exact vs p3, both backends");

    // ================= PARITY GATE 2: 16-chain =================
    let chain_states = &states[..N_CHAIN as usize];
    let soa_chain = pack_soa(chain_states, N_CHAIN as usize);
    mg.write_src(&soa_chain);
    wg.write_src(&soa_chain);
    mg.time_once(&|enc| mtl_dispatch(enc, &m_perm16, N_CHAIN), 1);
    wg.time_once(
        &|pass, g| {
            pass.set_bind_group(0, &g.bind_main, &[]);
            pass.set_pipeline(&w_perm16);
            pass.dispatch_workgroups(N_CHAIN / 256, 1, 1);
        },
        1,
    );
    let m_out = mg.read_data(0, 16 * N_CHAIN as usize);
    let w_out = wg.read_data(0, 16 * N_CHAIN as usize);
    for i in 0..256 {
        let mut s = chain_states[i];
        for _ in 0..CHAIN {
            s = host_perm_canonical(&perm, &s);
        }
        assert_eq!(
            unpack_soa_state(&m_out, N_CHAIN as usize, i),
            s,
            "METAL chain parity FAILED at state {i}"
        );
        assert_eq!(
            unpack_soa_state(&w_out, N_CHAIN as usize, i),
            s,
            "WGPU chain parity FAILED at state {i}"
        );
    }
    println!("parity ✓ 16-chained permutation: 256 states bit-exact vs p3, both backends");

    // ================= MEASURE: permutation throughput =================
    println!("\n== Poseidon2-BabyBear-w16 permutation (one thread/state, SoA, monty form) ==");
    mg.write_src(&soa);
    wg.write_src(&soa);
    let (tn, tw) = interleave(
        5,
        || mg.time_once(&|enc| mtl_dispatch(enc, &m_perm1, N_PERM), 10),
        || {
            wg.time_once(
                &|pass, g| {
                    pass.set_bind_group(0, &g.bind_main, &[]);
                    pass.set_pipeline(&w_perm1);
                    pass.dispatch_workgroups(N_PERM / 256, 1, 1);
                },
                10,
            )
        },
    );
    let report_perm = |label: &str, t: f64, perms: f64, io_bytes: f64| {
        println!(
            "  {label:<7} {:8.3} ms | {:7.1} Mperm/s | {:6.1} Gmul-equiv/s | I/O {:5.1} GB/s",
            t * 1e3,
            perms / t / 1e6,
            perms / t * mmuls as f64 / 1e9,
            io_bytes / t / 1e9,
        );
    };
    let (p1, io1) = (N_PERM as f64, N_PERM as f64 * 128.0);
    report_perm("native", tn, p1, io1);
    report_perm("wgpu", tw, p1, io1);
    println!(
        "  ratio native/wgpu: {:.2}x (CHAIN=1, 2^20 states)",
        tw / tn
    );
    let ratio_perm1 = tw / tn;

    mg.write_src(&soa_chain);
    wg.write_src(&soa_chain);
    let (tn16, tw16) = interleave(
        5,
        || mg.time_once(&|enc| mtl_dispatch(enc, &m_perm16, N_CHAIN), 4),
        || {
            wg.time_once(
                &|pass, g| {
                    pass.set_bind_group(0, &g.bind_main, &[]);
                    pass.set_pipeline(&w_perm16);
                    pass.dispatch_workgroups(N_CHAIN / 256, 1, 1);
                },
                4,
            )
        },
    );
    let (p16, io16) = (
        N_CHAIN as f64 * CHAIN as f64,
        N_CHAIN as f64 * 128.0, // I/O once per 16 perms
    );
    println!("  -- ALU-bound (CHAIN=16, 2^18 states; I/O amortized 16x) --");
    report_perm("native", tn16, p16, io16);
    report_perm("wgpu", tw16, p16, io16);
    println!("  ratio native/wgpu: {:.2}x (pure compute)", tw16 / tn16);
    let ratio_perm16 = tw16 / tn16;

    // ================= MERKLE COMMIT: parity + measure per size =================
    println!("\n== Merkle commit (leaf = 8 elems -> sponge; compress 2->1; to the root) ==");
    println!(
        "   (the MMCS pattern: PaddingFreeSponge<Perm,16,8,8> + TruncatedPermutation<Perm,2,8,16>)"
    );
    let max_n = *tree_sizes.iter().max().unwrap() as usize;
    let leaves: Vec<[u32; 8]> = (0..max_n)
        .map(|_| core::array::from_fn(|_| rng.gen_range(0..P)))
        .collect();

    let mut tree_rows: Vec<(u32, f64, f64, f64)> = Vec::new(); // (n, native, wgpu, cpu)
    for (si, &n) in tree_sizes.iter().enumerate() {
        let nl = n as usize;
        let soa_leaves = pack_soa(&leaves[..nl], nl);
        mg.write_src(&soa_leaves);
        wg.write_src(&soa_leaves);

        // host oracle root (the real p3 pair, rayon)
        let (root, leaf0, cpu_s) = host_tree(&hasher, &compress, &leaves[..nl]);

        // parity: one build on each backend, compare root (and leaf-0 digest)
        mg.time_once(&|enc| mtl_encode_tree(enc, &m_leaf[si], &m_compress, n), 1);
        wg.time_once(
            &|pass, g| wgpu_encode_tree(pass, g, &w_leaf[si], &w_compress, n),
            1,
        );
        for (name, out_root, out_leaf0) in [
            ("METAL", mg.read_data(8, 8), mg.read_data(nl * 8, 8)),
            ("WGPU", wg.read_data(8, 8), wg.read_data(nl * 8, 8)),
        ] {
            let got_root: [u32; 8] = core::array::from_fn(|j| from_mont(out_root[j]));
            let got_leaf0: [u32; 8] = core::array::from_fn(|j| from_mont(out_leaf0[j]));
            assert_eq!(got_leaf0, leaf0, "{name} leaf-hash parity FAILED at N={n}");
            assert_eq!(got_root, root, "{name} Merkle root parity FAILED at N={n}");
        }

        if n < (1 << 18) {
            println!(
                "  N=2^{:<2} parity ✓ (root + leaf digest, both backends)",
                n.trailing_zeros()
            );
            continue; // small size is parity-only
        }

        let iters = if n >= 1 << 21 { 3 } else { 5 };
        let (tn, tw) = interleave(
            5,
            || {
                mg.time_once(
                    &|enc| mtl_encode_tree(enc, &m_leaf[si], &m_compress, n),
                    iters,
                )
            },
            || {
                wg.time_once(
                    &|pass, g| wgpu_encode_tree(pass, g, &w_leaf[si], &w_compress, n),
                    iters,
                )
            },
        );
        let hashes = (2 * n - 1) as f64;
        println!(
            "  N=2^{:<2} parity ✓ | native {:8.2} ms ({:6.1} Mhash/s) | wgpu {:8.2} ms ({:6.1} Mhash/s) | cpu(rayon,scalar) {:7.1} ms | ratio native/wgpu {:.2}x",
            n.trailing_zeros(),
            tn * 1e3,
            hashes / tn / 1e6,
            tw * 1e3,
            hashes / tw / 1e6,
            cpu_s * 1e3,
            tw / tn,
        );
        tree_rows.push((n, tn, tw, cpu_s));
    }

    // ================= SUMMARY =================
    println!("\n== SUMMARY (M2 Max, interleaved A/B, best-of-5, parity-gated) ==");
    println!("  permutation ratio native/wgpu: {ratio_perm1:.2}x (with I/O), {ratio_perm16:.2}x (ALU-bound)");
    if !tree_rows.is_empty() {
        let rs: Vec<f64> = tree_rows.iter().map(|r| r.2 / r.1).collect();
        let rmin = rs.iter().cloned().fold(f64::MAX, f64::min);
        let rmax = rs.iter().cloned().fold(0.0f64, f64::max);
        println!(
            "  Merkle-commit ratio native/wgpu: {rmin:.2}x .. {rmax:.2}x across 2^18..2^21 leaves"
        );
    }
    println!("  ({mmuls} monty muls/perm; native mmul = 4 hw muls via mulhi, wgpu mmul = 16-bit-split emulation)");
}

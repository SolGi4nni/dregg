//! wgpu/WGSL BabyBear NTT probe — THE bandwidth measurement.
//!
//! Question answered empirically: how close does a portable wgpu/WGSL NTT get
//! to this machine's peak memory bandwidth? The NTT (LDE) is the shrink
//! prover's dominant, memory-bound kernel; the prior sibling probe
//! (wgpu-babybear-probe) showed the compute-bound mul kernel is near-peak.
//!
//! What it does:
//!   1. Locks DFT conventions: host reference radix-2 DIT vs pinned Plonky3
//!      rev 82cfad7 `Radix2DitParallel` (natural-order evaluations).
//!   2. Measures the device's achievable copy bandwidth (the honest ceiling,
//!      alongside the 400 GB/s M2 Max spec).
//!   3. Runs two GPU NTT strategies, both parity-checked against p3:
//!      - multipass: bitrev gather + one global dispatch per stage (logn+1
//!        roundtrips through memory);
//!      - fused: 2 roundtrips — pass 1 folds bit-reversal into the load and
//!        does stages 1..E in workgroup shared memory; pass 2 does stages
//!        E+1..logn on strided tiles in shared memory.
//!   4. Reports effective GB/s and %-of-peak, plus p3 CPU baselines (1 thread
//!      and full rayon).
//!
//! Data stays in Montgomery form on the GPU end-to-end (p3's in-memory repr IS
//! Montgomery form, so a real integration would pass &[BabyBear] as &[u32]
//! with zero conversion; host-side conversions here are for parity only and
//! are untimed).

use p3_baby_bear::BabyBear;
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::integers::QuotientMap;
use p3_field::{PrimeField32, TwoAdicField};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rand::Rng;
use wgpu::Features;

const P: u32 = 0x7800_0001; // BabyBear prime
const MU: u32 = 0x8800_0001; // P^{-1} mod 2^32 (p3 MONTY_MU)
const SPEC_BW: f64 = 400.0e9; // Apple spec: M2 Max unified memory bandwidth, 400 GB/s

// ---------- host-side BabyBear helpers (canonical + Montgomery) ----------

fn to_mont(a: u32) -> u32 {
    (((a as u64) << 32) % P as u64) as u32
}

/// Host Montgomery product, same algorithm as the shader / p3 monty-31 reduce.
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

fn mulmod(a: u64, b: u64) -> u64 {
    a * b % P as u64
}

fn powmod(mut b: u64, mut e: u64) -> u64 {
    let mut acc = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            acc = mulmod(acc, b);
        }
        b = mulmod(b, b);
        e >>= 1;
    }
    acc
}

fn bitrev(i: u32, bits: u32) -> u32 {
    i.reverse_bits() >> (32 - bits)
}

/// Reference radix-2 DIT NTT in canonical form: X[k] = sum_j x[j] w^{jk},
/// w = two_adic_generator(logn). Locks the convention against p3.
fn cpu_ref_ntt(x: &[u32], logn: u32) -> Vec<u32> {
    let n = 1usize << logn;
    assert_eq!(x.len(), n);
    let w = BabyBear::two_adic_generator(logn as usize).as_canonical_u32() as u64;
    let mut a: Vec<u64> = (0..n)
        .map(|i| x[bitrev(i as u32, logn) as usize] as u64)
        .collect();
    for s in 1..=logn {
        let m = 1usize << s;
        let wm = powmod(w, (n >> s) as u64);
        for k in (0..n).step_by(m) {
            let mut t = 1u64;
            for j in 0..m / 2 {
                let v = mulmod(t, a[k + j + m / 2]);
                let u = a[k + j];
                a[k + j] = (u + v) % P as u64;
                a[k + j + m / 2] = (u + P as u64 - v) % P as u64;
                t = mulmod(t, wm);
            }
        }
    }
    a.into_iter().map(|v| v as u32).collect()
}

// ---------- WGSL ----------

const PRELUDE: &str = r#"
const P: u32 = 0x78000001u;
const MU: u32 = 0x88000001u;

// 32x32 -> 64 multiply via 16-bit split (WGSL has no u64 and no mulhi).
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

// Montgomery product, exactly the p3 monty-31 reduce.
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

@group(0) @binding(0) var<storage, read_write> data: array<u32>;
@group(0) @binding(1) var<storage, read> src: array<u32>;
@group(0) @binding(2) var<storage, read> tw: array<u32>;
"#;

// vec4 copy: the achievable-bandwidth ceiling kernel. Each thread copies 4
// vec4s, grid-strided.
const COPY_V4: &str = r#"
@group(0) @binding(0) var<storage, read_write> data: array<vec4<u32>>;
@group(0) @binding(1) var<storage, read> src: array<vec4<u32>>;
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    data[i] = src[i];
    data[i + $STRIDE] = src[i + $STRIDE];
    data[i + 2u * $STRIDE] = src[i + 2u * $STRIDE];
    data[i + 3u * $STRIDE] = src[i + 3u * $STRIDE];
}
"#;

const COPY_U32: &str = r#"
@group(0) @binding(0) var<storage, read_write> data: array<u32>;
@group(0) @binding(1) var<storage, read> src: array<u32>;
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    data[i] = src[i];
    data[i + $STRIDE] = src[i + $STRIDE];
    data[i + 2u * $STRIDE] = src[i + 2u * $STRIDE];
    data[i + 3u * $STRIDE] = src[i + 3u * $STRIDE];
    data[i + 4u * $STRIDE] = src[i + 4u * $STRIDE];
    data[i + 5u * $STRIDE] = src[i + 5u * $STRIDE];
    data[i + 6u * $STRIDE] = src[i + 6u * $STRIDE];
    data[i + 7u * $STRIDE] = src[i + 7u * $STRIDE];
}
"#;

// Bit-reversal gather: data[i] = src[rev(i)]. One column per gid.y.
const K_BITREV: &str = r#"
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let off = gid.y * $NN;
    data[off + i] = src[off + (reverseBits(i) >> $RSH)];
}
"#;

// One global DIT stage (stage constants baked per pipeline). In-place on `data`.
const K_STAGE: &str = r#"
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let bf = gid.x;
    let off = gid.y * $NN;
    let j = bf & ($HALF - 1u);
    let i1 = off + ((bf >> ($SS - 1u)) << $SS) + j;
    let i2 = i1 + $HALF;
    let t = mmul(data[i2], TW(j << $TSH));
    let u = data[i1];
    data[i1] = addp(u, t);
    data[i2] = subp(u, t);
}
"#;

// Fused pass 1: fold the bit-reversal permutation into the load, run stages
// 1..E in workgroup shared memory, write contiguous tiles.
// Workgroup w handles output block g = rev(w); its bit-reversed loads then
// read src at u*W + w — so CONCURRENT workgroups read ADJACENT addresses.
const K_FUSED1: &str = r#"
var<workgroup> tile: array<u32, $TILE>;
@compute @workgroup_size($WGSZ)
fn main(@builtin(local_invocation_id) l: vec3<u32>, @builtin(workgroup_id) wg: vec3<u32>) {
    let lid = l.x;
    let off = wg.y * $NN;
    let w = wg.x;
    for (var k = 0u; k < $TPT; k++) {
        let u = lid + k * $WGSZ;
        tile[reverseBits(u) >> (32u - $EE)] = src[off + u * $WW + w];
    }
    workgroupBarrier();
    for (var s = 1u; s <= $EE; s++) {
        let half = 1u << (s - 1u);
        for (var k = 0u; k < $HBT; k++) {
            let bf = lid + k * $WGSZ;
            let j = bf & (half - 1u);
            let i1 = ((bf >> (s - 1u)) << s) + j;
            let i2 = i1 + half;
            let t = mmul(tile[i2], TW(j << ($LOGN - s)));
            let u2 = tile[i1];
            tile[i1] = addp(u2, t);
            tile[i2] = subp(u2, t);
        }
        workgroupBarrier();
    }
    let ga = reverseBits(w) >> (32u - ($LOGN - $EE));
    let base = off + ga * $TILE;
    for (var k = 0u; k < $TPT; k++) {
        let sl = lid + k * $WGSZ;
        data[base + sl] = tile[sl];
    }
}
"#;

// Fused mid/final pass: F DIT stages at bit offset B (stages B+1..B+F of the
// global DIT). A tile is 2^C low ("coalescing") bits x 2^F butterfly bits at
// offset B; global accesses are contiguous runs of 2^C u32. The workgroup id
// supplies the fixed bits: WLW = B-C low ones (bits [C..B)) and the rest above
// B+F ($BF = B+F).
const K_FUSED2: &str = r#"
var<workgroup> tile: array<u32, $TILE>;
@compute @workgroup_size($WGSZ)
fn main(@builtin(local_invocation_id) l: vec3<u32>, @builtin(workgroup_id) wg: vec3<u32>) {
    let lid = l.x;
    let off = wg.y * $NN;
    let wlo = wg.x & ((1u << $WLW) - 1u);
    let whi = wg.x >> $WLW;
    let base = off + (wlo << $CC) + (whi << $BF);
    for (var k = 0u; k < $TPT; k++) {
        let sl = lid + k * $WGSZ;
        let q = sl >> $CC;
        let lo = sl & ((1u << $CC) - 1u);
        tile[sl] = data[base + lo + (q << $BB)];
    }
    workgroupBarrier();
    for (var t = 1u; t <= $FF; t++) {
        for (var k = 0u; k < $HBT; k++) {
            let bf = lid + k * $WGSZ;
            let qb = bf >> $CC;
            let lo = bf & ((1u << $CC) - 1u);
            let jq = qb & ((1u << (t - 1u)) - 1u);
            let q1 = ((qb >> (t - 1u)) << t) + jq;
            let q2 = q1 + (1u << (t - 1u));
            let i1 = (q1 << $CC) + lo;
            let i2 = (q2 << $CC) + lo;
            let j = (wlo << $CC) + lo + (jq << $BB);
            let tt = mmul(tile[i2], TW(j << ($LOGN - $BB - t)));
            let u2 = tile[i1];
            tile[i1] = addp(u2, tt);
            tile[i2] = subp(u2, tt);
        }
        workgroupBarrier();
    }
    for (var k = 0u; k < $TPT; k++) {
        let sl = lid + k * $WGSZ;
        let q = sl >> $CC;
        let lo = sl & ((1u << $CC) - 1u);
        data[base + lo + (q << $BB)] = tile[sl];
    }
}
"#;

// 2D-tiled first pass: a workgroup handles BQ = 2^LB ADJACENT columns of the
// (2^E1 rows x W columns) strided view — i.e. stages [bitrev]+1..E1 of the
// global DIT for BQ output blocks at once. Global reads are runs of BQ u32
// (adjacent columns), global writes are BQ fully-contiguous 2^E1-element
// blocks: no 4-byte-granule scatter anywhere. Equivalent to the four-step
// column-NTT pass; twiddles are the global stage twiddles tw[j << (LOGN-s)].
const K_FUSED1B: &str = r#"
var<workgroup> tile: array<u32, $TILE>;
@compute @workgroup_size($WGSZ)
fn main(@builtin(local_invocation_id) l: vec3<u32>, @builtin(workgroup_id) wg: vec3<u32>) {
    let lid = l.x;
    let off = wg.y * $NN;
    let c0 = wg.x << $LB;
    // load BQ adjacent columns; fold the row bit-reversal into the shared write
    for (var k = 0u; k < $TPT; k++) {
        let slot = lid + k * $WGSZ;
        let u = slot >> $LB;
        let b = slot & ((1u << $LB) - 1u);
        tile[((reverseBits(u) >> (32u - $E1)) << $LB) + b] = src[off + u * $WW + c0 + b];
    }
    workgroupBarrier();
    for (var s = 1u; s <= $E1; s++) {
        let half = 1u << (s - 1u);
        for (var k = 0u; k < $HBT; k++) {
            let sb = lid + k * $WGSZ;
            let b = sb & ((1u << $LB) - 1u);
            let bf = sb >> $LB;
            let j = bf & (half - 1u);
            let i1 = ((((bf >> (s - 1u)) << s) + j) << $LB) + b;
            let i2 = i1 + (half << $LB);
            let t = mmul(tile[i2], TW(j << ($LOGN - s)));
            let u2 = tile[i1];
            tile[i1] = addp(u2, t);
            tile[i2] = subp(u2, t);
        }
        workgroupBarrier();
    }
    // store: column c goes to the contiguous output block g = rev(c)
    for (var b2 = 0u; b2 < (1u << $LB); b2++) {
        let g = reverseBits(c0 + b2) >> (32u - ($LOGN - $E1));
        let obase = off + (g << $E1);
        for (var k = 0u; k < ($TILE >> $LB) / $WGSZ; k++) {
            let u = lid + k * $WGSZ;
            data[obase + u] = tile[(u << $LB) + b2];
        }
    }
}
"#;

/// Register-tier radix-2^R kernel: R DIT stages (stages L+1..L+R of the global
/// DIT, L = low bit position) computed entirely in registers, fully unrolled —
/// no workgroup memory, no barriers. Each thread owns the closed 2^R-element
/// butterfly group {base + v<<L}. This is the shape native CUDA/Metal NTTs
/// use for their stage groups.
fn radix_kernel(n: u32, logn: u32, l: u32, r: u32, wgsz: u32) -> String {
    let m = 1u32 << r;
    let mut s = String::new();
    s.push_str(&format!(
        "@compute @workgroup_size({wgsz})\nfn main(@builtin(global_invocation_id) gid: vec3<u32>) {{\n    let t = gid.x;\n    let off = gid.y * {n}u;\n"
    ));
    if l == 0 {
        s.push_str(&format!(
            "    let tlow = 0u;\n    let base = off + (t << {r}u);\n"
        ));
    } else {
        s.push_str(&format!(
            "    let tlow = t & {}u;\n    let base = off + ((t >> {l}u) << {}u) + tlow;\n",
            (1u32 << l) - 1,
            l + r
        ));
    }
    for v in 0..m {
        s.push_str(&format!("    var r{v} = data[base + {}u];\n", v << l));
    }
    for st in 0..r {
        let lowmask = (1u32 << st) - 1;
        for p in 0..(m >> 1) {
            let v0 = ((p & !lowmask) << 1) | (p & lowmask);
            let v1 = v0 | (1 << st);
            let jlit = (p & lowmask) << l;
            let sh = logn - l - st - 1;
            s.push_str(&format!(
                "    {{ let tt = mmul(r{v1}, TW(({jlit}u + tlow) << {sh}u)); let uu = r{v0}; r{v0} = addp(uu, tt); r{v1} = subp(uu, tt); }}\n"
            ));
        }
    }
    for v in 0..m {
        s.push_str(&format!("    data[base + {}u] = r{v};\n", v << l));
    }
    s.push_str("}\n");
    s
}

fn subst(template: &str, pairs: &[(&str, u32)]) -> String {
    let mut s = template.to_string();
    for (k, v) in pairs {
        s = s.replace(k, &format!("{v}u"));
    }
    s
}

/// Twiddle accessor definition. Direct: TW(i) = tw[i] — byte-identical to the
/// original kernels. Split ("tw2"): TW(i) = mmul(tw_hi[i>>S], tw_lo[i&(2^S-1)])
/// = mont(w^(hi<<S)) *M mont(w^lo) = mont(w^i) EXACTLY (Montgomery product of
/// Montgomery forms), so parity is bit-identical. The point: stages whose
/// twiddle index is `j << big_shift` gather one distinct 128B line PER LANE
/// across the full n/2-entry table (4 MiB at n=2^21) — a 32x request
/// amplification that collapses RDNA2 to 14-19 GB/s. The split confines all
/// twiddle reads to two ~4 KiB cache-resident tables (lo = head of the main
/// table; hi = compact appendix at element offset n/2).
fn tw_def(split: bool, thi_off: u32, s: u32) -> String {
    if split {
        format!(
            "fn TW(i: u32) -> u32 {{ return mmul(tw[{thi_off}u + (i >> {s}u)], tw[i & {}u]); }}\n",
            (1u32 << s) - 1
        )
    } else {
        "fn TW(i: u32) -> u32 { return tw[i]; }\n".to_string()
    }
}

// ---------- GPU harness ----------

struct Gpu {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipe_layout: wgpu::PipelineLayout,
    bind: wgpu::BindGroup,
    buf_work: wgpu::Buffer,
    buf_src: wgpu::Buffer,
    buf_tw: wgpu::Buffer,
    buf_read: wgpu::Buffer,
}

const BUF_U32S: usize = 1 << 26; // 256 MiB working set (holds 2^21 x 32 — bigger than a 96 MB Infinity Cache)

impl Gpu {
    fn new() -> Self {
        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
        .expect("no adapter");
        let info = adapter.get_info();
        let feats = adapter.features();
        let lims = adapter.limits();
        println!("adapter: {} ({:?})", info.name, info.backend);
        println!(
            "  max workgroup storage: {} B, subgroup ops available: {} (sizes {}..{})",
            lims.max_compute_workgroup_storage_size,
            feats.contains(Features::SUBGROUP),
            lims.min_subgroup_size,
            lims.max_subgroup_size,
        );
        let mut want = Features::empty();
        if feats.contains(Features::SUBGROUP) {
            want |= Features::SUBGROUP;
        }
        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: None,
                required_features: want,
                required_limits: lims,
                memory_hints: Default::default(),
            },
            None,
        ))
        .expect("no device");

        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: None,
            entries: &[
                wgpu::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                wgpu::BindGroupLayoutEntry {
                    binding: 1,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: true },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                wgpu::BindGroupLayoutEntry {
                    binding: 2,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: true },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
            ],
        });
        let pipe_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: None,
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });

        let sz = (BUF_U32S * 4) as u64;
        let buf_work = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("work"),
            size: sz,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_SRC
                | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let buf_src = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("src"),
            size: sz,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let buf_tw = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("tw"),
            size: 5 << 20, // n/2 twiddles at n=2^21 (4 MiB) + compact tw_hi appendix
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let buf_read = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("read"),
            size: sz,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let bind = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: buf_work.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: buf_src.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: buf_tw.as_entire_binding(),
                },
            ],
        });
        Gpu {
            device,
            queue,
            pipe_layout,
            bind,
            buf_work,
            buf_src,
            buf_tw,
            buf_read,
        }
    }

    fn pipeline(&self, wgsl: &str, label: &str) -> wgpu::ComputePipeline {
        // Trusted module: skip naga's per-access bounds checks (probe kernels
        // are index-audited; parity vs p3 still validates every run). Bounds
        // checks are a real, measurable part of the wgpu-vs-native question.
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
                // CRITICAL (measured): the default WebGPU-mandated zero-init of
                // workgroup memory is emitted by naga/MSL as THREAD 0 SERIALLY
                // zeroing the whole tile (`if (all(lid==0)) tile = {};`) — a
                // 13-40x slowdown for 16-32 KiB tiles. Safe to disable here:
                // every tile slot is written before it is read.
                compilation_options: wgpu::PipelineCompilationOptions {
                    zero_initialize_workgroup_memory: false,
                    ..Default::default()
                },
                cache: None,
            })
    }

    /// Encode `iters` repetitions of the dispatch plan in one submit; return
    /// wall seconds per iteration (best of `reps` submits, after warmup).
    fn time_plan(
        &self,
        plan: &[(&wgpu::ComputePipeline, (u32, u32))],
        iters: u32,
        reps: u32,
    ) -> f64 {
        let run = || -> f64 {
            let t0 = std::time::Instant::now();
            let mut enc = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                pass.set_bind_group(0, &self.bind, &[]);
                for _ in 0..iters {
                    for (pipe, (x, y)) in plan {
                        pass.set_pipeline(pipe);
                        pass.dispatch_workgroups(*x, *y, 1);
                    }
                }
            }
            self.queue.submit([enc.finish()]);
            self.device.poll(wgpu::Maintain::Wait);
            t0.elapsed().as_secs_f64() / iters as f64
        };
        run(); // warmup
        (0..reps).map(|_| run()).fold(f64::MAX, f64::min)
    }

    fn read_work(&self, n_u32: usize) -> Vec<u32> {
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(&self.buf_work, 0, &self.buf_read, 0, (n_u32 * 4) as u64);
        self.queue.submit([enc.finish()]);
        let slice = self.buf_read.slice(..(n_u32 * 4) as u64);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let out: Vec<u32> = bytemuck::cast_slice(&slice.get_mapped_range()).to_vec();
        self.buf_read.unmap();
        out
    }
}

// ---------- shapes + plans ----------

struct ShapeResult {
    label: String,
    ntotal: usize,
    best_gpu_s: f64,
    best_plan: String,
    best_passes: u32,
    cpu1_s: Option<f64>,
    cpu12_s: Option<f64>,
}

fn main() {
    // 1. Convention lock: host reference DIT vs pinned p3.
    {
        let logn = 10u32;
        let n = 1usize << logn;
        let mut rng = rand::thread_rng();
        let x: Vec<u32> = (0..n).map(|_| rng.gen_range(0..P)).collect();
        let refv = cpu_ref_ntt(&x, logn);
        let dft = Radix2DitParallel::<BabyBear>::default();
        let p3v: Vec<u32> = dft
            .dft(x.iter().map(|&v| BabyBear::from_int(v)).collect())
            .iter()
            .map(|v| v.as_canonical_u32())
            .collect();
        assert_eq!(refv, p3v, "convention lock failed: host DIT != p3 dft");
        println!("convention lock: host radix-2 DIT == p3 Radix2DitParallel::dft (n=2^{logn}) ✓");
    }

    let gpu = Gpu::new();
    let max_wg_storage = {
        // re-query from device
        gpu.device.limits().max_compute_workgroup_storage_size
    };

    let mut rng = rand::thread_rng();
    let all_input: Vec<u32> = (0..BUF_U32S).map(|_| rng.gen_range(0..P)).collect();
    let all_mont: Vec<u32> = all_input.iter().map(|&v| to_mont(v)).collect();

    // 2. Copy ceiling.
    gpu.queue
        .write_buffer(&gpu.buf_src, 0, bytemuck::cast_slice(&all_mont));
    let nvec4 = (BUF_U32S / 4) as u32;
    let stride_v4 = nvec4 / 4;
    let copy_v4 = gpu.pipeline(&subst(COPY_V4, &[("$STRIDE", stride_v4)]), "copy_v4");
    let stride_u = (BUF_U32S / 8) as u32;
    let copy_u = gpu.pipeline(&subst(COPY_U32, &[("$STRIDE", stride_u)]), "copy_u32");
    let bytes_copy = (BUF_U32S * 8) as f64; // read + write
    let t_v4 = gpu.time_plan(&[(&copy_v4, (stride_v4 / 256, 1))], 30, 5);
    let t_u = gpu.time_plan(&[(&copy_u, (stride_u / 256, 1))], 30, 5);
    let bw_v4 = bytes_copy / t_v4;
    let bw_u = bytes_copy / t_u;
    let ceiling = bw_v4.max(bw_u);
    println!(
        "copy ceiling (64 MiB read+write): vec4 {:.1} GB/s, u32x4 {:.1} GB/s -> ceiling {:.1} GB/s ({:.0}% of 400 GB/s spec)",
        bw_v4 / 1e9,
        bw_u / 1e9,
        ceiling / 1e9,
        ceiling / SPEC_BW * 100.0
    );

    // 3. NTT shapes.
    let shapes: &[(u32, usize)] = &[(15, 64), (15, 256), (18, 16), (21, 1), (21, 8), (21, 32)];
    let mut results: Vec<ShapeResult> = Vec::new();

    for &(logn, ncols) in shapes {
        let n = 1usize << logn;
        let ntotal = n * ncols;
        assert!(ntotal <= BUF_U32S);
        println!(
            "\n=== NTT 2^{logn} x {ncols} cols ({} Melem, {} MiB) ===",
            ntotal >> 20,
            ntotal * 4 >> 20
        );

        // input: column c = all_input[c*n .. (c+1)*n] (column-contiguous on GPU)
        let input = &all_input[..ntotal];
        gpu.queue
            .write_buffer(&gpu.buf_src, 0, bytemuck::cast_slice(&all_mont[..ntotal]));

        // twiddles: mont(w^t), t < n/2; plus a compact tw_hi appendix at
        // element offset n/2: tw_hi[k] = tw[k << TWS] (for the split TW).
        // tw_lo IS the head of the main table (tw[i & (2^TWS - 1)]).
        let w = BabyBear::two_adic_generator(logn as usize).as_canonical_u32() as u64;
        let mut twv = Vec::with_capacity(n / 2 + (n / 2 >> (logn / 2)));
        let mut acc = 1u64;
        for _ in 0..n / 2 {
            twv.push(to_mont(acc as u32));
            acc = mulmod(acc, w);
        }
        let tws = logn / 2; // split point: lo table 2^TWS entries, hi table (n/2)>>TWS
        let thi_off = (n / 2) as u32;
        for k in 0..(n / 2) >> tws {
            twv.push(twv[k << tws]);
        }
        gpu.queue
            .write_buffer(&gpu.buf_tw, 0, bytemuck::cast_slice(&twv));
        let twd_direct = tw_def(false, 0, 0);
        let twd_split = tw_def(true, thi_off, tws);
        let twd_for = |tw2: bool| -> &str {
            if tw2 {
                &twd_split
            } else {
                &twd_direct
            }
        };
        // tw modes: 0 = direct everywhere, 1 = split everywhere, 2 = MIXED —
        // direct in pass1 (its twiddle reads are already near-wave-uniform;
        // the split only adds a dependent-load chain there) and split in the
        // strided later passes (where the direct per-lane gather collapses).
        const TW_MODES: [u32; 3] = [0, 1, 2];
        let tw_suffix = |mode: u32| match mode {
            1 => " +tw2",
            2 => " +tw2m",
            _ => "",
        };

        // p3 expected (also the full-rayon CPU baseline timing target)
        let mat_vals: Vec<BabyBear> = (0..ntotal)
            .map(|i| {
                let (r, c) = (i / ncols, i % ncols);
                BabyBear::from_int(input[c * n + r])
            })
            .collect();
        let mat = RowMajorMatrix::new(mat_vals, ncols);
        let dft = Radix2DitParallel::<BabyBear>::default();
        let m1 = mat.clone();
        let t0 = std::time::Instant::now();
        let expected_m = dft.dft_batch(m1).to_row_major_matrix();
        let cpu12_first = t0.elapsed().as_secs_f64();
        // best of 2 for the parallel baseline (2nd run has warm twiddle caches)
        let m2 = mat.clone();
        let t0 = std::time::Instant::now();
        let _ = dft.dft_batch(m2).to_row_major_matrix();
        let cpu12_s = cpu12_first.min(t0.elapsed().as_secs_f64());
        // single-thread baseline (warm twiddle caches -> favors the CPU; fine)
        let pool1 = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        let m3 = mat.clone();
        let t0 = std::time::Instant::now();
        let _ = pool1.install(|| dft.dft_batch(m3).to_row_major_matrix());
        let cpu1_s = t0.elapsed().as_secs_f64();
        println!(
            "p3 CPU Radix2DitParallel: 1 thread {:.1} ms ({:.0} Melem/s), full rayon {:.1} ms ({:.0} Melem/s)",
            cpu1_s * 1e3,
            ntotal as f64 / cpu1_s / 1e6,
            cpu12_s * 1e3,
            ntotal as f64 / cpu12_s / 1e6
        );
        let expected: Vec<u32> = {
            let mut e = vec![0u32; ntotal];
            for r in 0..n {
                for c in 0..ncols {
                    e[c * n + r] = expected_m.values[r * ncols + c].as_canonical_u32();
                }
            }
            e
        };

        let check_parity = |label: &str| -> bool {
            let got = gpu.read_work(ntotal);
            let mut bad = 0usize;
            for i in 0..ntotal {
                if from_mont(got[i]) != expected[i] {
                    bad += 1;
                    if bad <= 3 {
                        println!(
                            "  MISMATCH [{label}] idx {i} (col {}, row {}): gpu {} expected {}",
                            i / n,
                            i % n,
                            from_mont(got[i]),
                            expected[i]
                        );
                    }
                }
            }
            if bad == 0 {
                println!("  PARITY [{label}]: all {ntotal} values match p3 ✓");
                true
            } else {
                println!("  PARITY FAILED [{label}]: {bad}/{ntotal} mismatches");
                false
            }
        };

        let mut best: Option<(f64, String, u32)> = None;
        let mut parity_all = true;

        // --- multipass plan ---
        {
            let rsh = 32 - logn;
            let p_bitrev = gpu.pipeline(
                &format!(
                    "{}{}",
                    PRELUDE,
                    subst(K_BITREV, &[("$NN", n as u32), ("$RSH", rsh)])
                ),
                "bitrev",
            );
            let mut stage_pipes = Vec::new();
            for s in 1..=logn {
                let wgsl = format!(
                    "{}{}{}",
                    PRELUDE,
                    twd_direct,
                    subst(
                        K_STAGE,
                        &[
                            ("$NN", n as u32),
                            ("$HALF", 1 << (s - 1)),
                            ("$SS", s),
                            ("$TSH", logn - s)
                        ],
                    )
                );
                stage_pipes.push(gpu.pipeline(&wgsl, &format!("stage{s}")));
            }
            let mut plan: Vec<(&wgpu::ComputePipeline, (u32, u32))> =
                vec![(&p_bitrev, ((n as u32).div_ceil(256), ncols as u32))];
            for p in &stage_pipes {
                plan.push((p, ((n as u32 / 2).div_ceil(256), ncols as u32)));
            }
            // parity once
            gpu.time_plan(&plan, 1, 0); // run once (warmup call inside runs it once)
            parity_all &= check_parity("multipass");
            let iters = (1 << 24) / ntotal as u32 * 2;
            let t = gpu.time_plan(&plan, iters.max(4), 3);
            let passes = logn + 1;
            report_plan("multipass", t, ntotal, passes, ceiling, &mut best);
        }

        // --- fused plans: (E, workgroup size) sweep ---
        for (e, wgsz) in [(11u32, 256u32), (12, 256), (13, 256)] {
            let tile = 1u32 << e;
            if tile * 4 > max_wg_storage || e >= logn || logn > 2 * e || tile / 2 < wgsz {
                continue;
            }
            let f = logn - e;
            let c = e - f;
            let wgroups = 1u32 << (logn - e);
            let p1 = gpu.pipeline(
                &format!(
                    "{}{}{}",
                    PRELUDE,
                    twd_direct,
                    subst(
                        K_FUSED1,
                        &[
                            ("$TILE", tile),
                            ("$TPT", tile / wgsz),
                            ("$HBT", tile / 2 / wgsz),
                            ("$WGSZ", wgsz),
                            ("$NN", n as u32),
                            ("$LOGN", logn),
                            ("$EE", e),
                            ("$WW", wgroups),
                        ],
                    )
                ),
                &format!("fused1_e{e}_w{wgsz}"),
            );
            let p2 = gpu.pipeline(
                &format!(
                    "{}{}{}",
                    PRELUDE,
                    twd_direct,
                    subst(
                        K_FUSED2,
                        &[
                            ("$TILE", tile),
                            ("$TPT", tile / wgsz),
                            ("$HBT", tile / 2 / wgsz),
                            ("$WGSZ", wgsz),
                            ("$NN", n as u32),
                            ("$LOGN", logn),
                            ("$BB", e),
                            ("$FF", f),
                            ("$CC", c),
                            ("$WLW", e - c),
                            ("$BF", e + f),
                        ],
                    )
                ),
                &format!("fused2_e{e}_w{wgsz}"),
            );
            let plan: Vec<(&wgpu::ComputePipeline, (u32, u32))> = vec![
                (&p1, (wgroups, ncols as u32)),
                (&p2, (wgroups, ncols as u32)),
            ];
            gpu.time_plan(&plan, 1, 0);
            parity_all &= check_parity(&format!("fused E={e} wg={wgsz}"));
            let iters = ((1 << 26) / ntotal as u32).clamp(8, 256);
            let t = gpu.time_plan(&plan, iters, 3);
            report_plan(
                &format!("fused E={e} wg={wgsz} (F={f},C={c})"),
                t,
                ntotal,
                2,
                ceiling,
                &mut best,
            );
            // per-pass attribution
            let t1 = gpu.time_plan(&[(&p1, (wgroups, ncols as u32))], iters, 3);
            let t2 = gpu.time_plan(&[(&p2, (wgroups, ncols as u32))], iters, 3);
            let bytes1 = ntotal as f64 * 8.0;
            println!(
                "    pass1 {:.3} ms ({:.0} GB/s, {:.0}% ceil) + pass2 {:.3} ms ({:.0} GB/s, {:.0}% ceil)",
                t1 * 1e3,
                bytes1 / t1 / 1e9,
                bytes1 / t1 / ceiling * 100.0,
                t2 * 1e3,
                bytes1 / t2 / 1e9,
                bytes1 / t2 / ceiling * 100.0
            );
        }

        // --- fused 2D plans: coalesced pass1 (BQ adjacent columns per
        // workgroup) + generalized mid passes with C-bit run coalescing.
        // Descriptor: (E1, LB, [(b, F, C), ...]) with E1 + sum(F) == logn.
        let plans2d: &[(u32, u32, &[(u32, u32, u32)])] = match logn {
            15 => &[
                (10, 3, &[(10, 5, 7)]),
                (9, 4, &[(9, 6, 6)]),
                (8, 4, &[(8, 7, 5)]),
                (8, 3, &[(8, 7, 4)]),
                (11, 3, &[(11, 4, 10)]), // 64 KiB LDS tiles (skipped where LDS < 64 KiB)
            ],
            18 => &[
                (10, 3, &[(10, 8, 5)]),
                (9, 4, &[(9, 9, 4)]),
                (8, 4, &[(8, 5, 7), (13, 5, 7)]),
                (11, 3, &[(11, 7, 7)]), // 64 KiB LDS, 2 passes
            ],
            21 => &[
                (10, 3, &[(10, 6, 7), (16, 5, 8)]),
                (9, 4, &[(9, 7, 6), (16, 5, 8)]),
                (9, 3, &[(9, 6, 6), (15, 6, 6)]),
                (8, 4, &[(8, 7, 5), (15, 6, 6)]),
                (8, 3, &[(8, 7, 4), (15, 6, 5)]),
                (11, 2, &[(11, 10, 3)]),
                (11, 3, &[(11, 10, 4)]), // 64 KiB LDS both passes — 2-pass 2^21
                (10, 4, &[(10, 11, 3)]), // 64 KiB mid — 2-pass alt
                (9, 5, &[(9, 6, 8), (15, 6, 8)]), // every global access a 128B+ run
                (11, 3, &[(11, 5, 8), (16, 5, 8)]), // 64 KiB pass1 + two wide-run mids
            ],
            _ => &[],
        };
        for &(e1, lb, mids) in plans2d {
            for mode in TW_MODES {
                let (tw_p1, tw_rest) = (mode == 1, mode >= 1);
                let wgsz = 256u32;
                let tile1 = 1u32 << (e1 + lb);
                if tile1 * 4 > max_wg_storage || (1u32 << e1) < wgsz {
                    continue;
                }
                if mids.iter().any(|&(b, ff, cc)| {
                    let tilem = 1u32 << (cc + ff);
                    tilem * 4 > max_wg_storage || b < cc || tilem / 2 < wgsz
                }) {
                    continue;
                }
                // structural sanity: contiguous stage coverage
                assert_eq!(e1 + mids.iter().map(|m| m.1).sum::<u32>(), logn);
                let mut b_expect = e1;
                for m in mids {
                    assert_eq!(m.0, b_expect);
                    b_expect += m.1;
                }
                let mut pipes: Vec<(wgpu::ComputePipeline, (u32, u32))> = Vec::new();
                pipes.push((
                    gpu.pipeline(
                        &format!(
                            "{}{}{}",
                            PRELUDE,
                            twd_for(tw_p1),
                            subst(
                                K_FUSED1B,
                                &[
                                    ("$TILE", tile1),
                                    ("$TPT", tile1 / wgsz),
                                    ("$HBT", tile1 / 2 / wgsz),
                                    ("$WGSZ", wgsz),
                                    ("$NN", n as u32),
                                    ("$LOGN", logn),
                                    ("$E1", e1),
                                    ("$LB", lb),
                                    ("$WW", (n as u32) >> e1),
                                ],
                            )
                        ),
                        &format!("fused1b_e{e1}_b{lb}"),
                    ),
                    ((n as u32) >> (e1 + lb), ncols as u32),
                ));
                for &(b, ff, cc) in mids {
                    let tilem = 1u32 << (cc + ff);
                    pipes.push((
                        gpu.pipeline(
                            &format!(
                                "{}{}{}",
                                PRELUDE,
                                twd_for(tw_rest),
                                subst(
                                    K_FUSED2,
                                    &[
                                        ("$TILE", tilem),
                                        ("$TPT", tilem / wgsz),
                                        ("$HBT", tilem / 2 / wgsz),
                                        ("$WGSZ", wgsz),
                                        ("$NN", n as u32),
                                        ("$LOGN", logn),
                                        ("$BB", b),
                                        ("$FF", ff),
                                        ("$CC", cc),
                                        ("$WLW", b - cc),
                                        ("$BF", b + ff),
                                    ],
                                )
                            ),
                            &format!("fused2g_b{b}_f{ff}_c{cc}"),
                        ),
                        ((n as u32) >> (cc + ff), ncols as u32),
                    ));
                }
                let plan: Vec<(&wgpu::ComputePipeline, (u32, u32))> =
                    pipes.iter().map(|(p, d)| (p, *d)).collect();
                let label = format!(
                    "fused2d E1={e1} B={} {:?}{}",
                    1 << lb,
                    mids,
                    tw_suffix(mode)
                );
                gpu.time_plan(&plan, 1, 0);
                parity_all &= check_parity(&label);
                let iters = ((1 << 26) / ntotal as u32).clamp(8, 256);
                let t = gpu.time_plan(&plan, iters, 3);
                report_plan(&label, t, ntotal, plan.len() as u32, ceiling, &mut best);
                // per-pass attribution
                let bytes1 = ntotal as f64 * 8.0;
                let mut attribution = String::new();
                for (i, (p, d)) in pipes.iter().enumerate() {
                    let tp = gpu.time_plan(&[(p, *d)], iters, 3);
                    attribution.push_str(&format!(
                        "pass{} {:.3} ms ({:.0} GB/s, {:.0}% ceil)  ",
                        i + 1,
                        tp * 1e3,
                        bytes1 / tp / 1e9,
                        bytes1 / tp / ceiling * 100.0
                    ));
                }
                println!("    {attribution}");
            }
        }

        // --- register-tier radix-2^R plans: bitrev pass + logn/R global
        // roundtrips of R fully-unrolled register stages. No workgroup memory,
        // no barriers — occupancy limited only by registers.
        for rr in [4u32, 5] {
            for tw2 in [false, true] {
                let wgsz = 256u32;
                let rsh = 32 - logn;
                let p_bitrev = gpu.pipeline(
                    &format!(
                        "{}{}",
                        PRELUDE,
                        subst(K_BITREV, &[("$NN", n as u32), ("$RSH", rsh)])
                    ),
                    "bitrev",
                );
                let mut pipes: Vec<(wgpu::ComputePipeline, (u32, u32))> = Vec::new();
                let mut l = 0u32;
                while l < logn {
                    let r = rr.min(logn - l);
                    let threads = (n as u32) >> r;
                    pipes.push((
                        gpu.pipeline(
                            &format!(
                                "{}{}{}",
                                PRELUDE,
                                twd_for(tw2),
                                radix_kernel(n as u32, logn, l, r, wgsz)
                            ),
                            &format!("radix_l{l}_r{r}"),
                        ),
                        (threads.div_ceil(wgsz), ncols as u32),
                    ));
                    l += r;
                }
                let mut plan: Vec<(&wgpu::ComputePipeline, (u32, u32))> =
                    vec![(&p_bitrev, ((n as u32).div_ceil(wgsz), ncols as u32))];
                plan.extend(pipes.iter().map(|(p, d)| (p, *d)));
                let label = format!(
                    "regradix R={rr} ({} passes){}",
                    plan.len(),
                    if tw2 { " +tw2" } else { "" }
                );
                gpu.time_plan(&plan, 1, 0);
                parity_all &= check_parity(&label);
                let iters = ((1 << 26) / ntotal as u32).clamp(8, 256);
                let t = gpu.time_plan(&plan, iters, 3);
                report_plan(&label, t, ntotal, plan.len() as u32, ceiling, &mut best);
                // per-pass attribution (bitrev first)
                let bytes1 = ntotal as f64 * 8.0;
                let tb = gpu.time_plan(
                    &[(&p_bitrev, ((n as u32).div_ceil(wgsz), ncols as u32))],
                    iters,
                    3,
                );
                let mut attribution = format!(
                    "bitrev {:.3} ms ({:.0} GB/s, {:.0}% ceil)  ",
                    tb * 1e3,
                    bytes1 / tb / 1e9,
                    bytes1 / tb / ceiling * 100.0
                );
                for (p, d) in pipes.iter() {
                    let tp = gpu.time_plan(&[(p, *d)], iters, 3);
                    attribution.push_str(&format!(
                        "radix {:.3} ms ({:.0} GB/s, {:.0}% ceil)  ",
                        tp * 1e3,
                        bytes1 / tp / 1e9,
                        bytes1 / tp / ceiling * 100.0
                    ));
                }
                println!("    {attribution}");
            }
        }

        // --- hybrid plans: fused2d pass1 (folds bitrev + E1 stages, small
        // coalesced tile) followed by register-radix chunks. No standalone
        // bitrev roundtrip, no occupancy-killing 32 KiB tiles.
        let hybrids: &[(u32, u32, &[u32])] = match logn {
            15 => &[
                (8, 3, &[4, 3]),
                (9, 3, &[3, 3]),
                (8, 4, &[4, 3]),
                (11, 3, &[4]), // 64 KiB pass1 tile, single radix tail
            ],
            18 => &[
                (8, 3, &[5, 5]),
                (8, 3, &[4, 3, 3]),
                (10, 3, &[4, 4]),
                (11, 3, &[4, 3]), // 64 KiB pass1 tile
                (12, 2, &[3, 3]),
            ],
            21 => &[
                (8, 3, &[5, 4, 4]),
                (8, 3, &[4, 4, 5]),
                (9, 3, &[4, 4, 4]),
                (10, 3, &[4, 4, 3]),
                (8, 4, &[5, 4, 4]),
                (11, 3, &[5, 5]), // 64 KiB pass1 tile
                (11, 3, &[4, 3, 3]),
                (12, 2, &[5, 4]),
                (9, 5, &[4, 4, 4]), // 128B-run pass1 loads
            ],
            _ => &[],
        };
        for &(e1, lb, chunks) in hybrids {
            for mode in TW_MODES {
                let (tw_p1, tw_rest) = (mode == 1, mode >= 1);
                let wgsz = 256u32;
                let tile1 = 1u32 << (e1 + lb);
                if tile1 * 4 > max_wg_storage || (1u32 << e1) < wgsz {
                    continue;
                }
                assert_eq!(e1 + chunks.iter().sum::<u32>(), logn);
                let mut pipes: Vec<(wgpu::ComputePipeline, (u32, u32))> = Vec::new();
                pipes.push((
                    gpu.pipeline(
                        &format!(
                            "{}{}{}",
                            PRELUDE,
                            twd_for(tw_p1),
                            subst(
                                K_FUSED1B,
                                &[
                                    ("$TILE", tile1),
                                    ("$TPT", tile1 / wgsz),
                                    ("$HBT", tile1 / 2 / wgsz),
                                    ("$WGSZ", wgsz),
                                    ("$NN", n as u32),
                                    ("$LOGN", logn),
                                    ("$E1", e1),
                                    ("$LB", lb),
                                    ("$WW", (n as u32) >> e1),
                                ],
                            )
                        ),
                        &format!("hyb1b_e{e1}_b{lb}"),
                    ),
                    ((n as u32) >> (e1 + lb), ncols as u32),
                ));
                let mut l = e1;
                for &r in chunks {
                    pipes.push((
                        gpu.pipeline(
                            &format!(
                                "{}{}{}",
                                PRELUDE,
                                twd_for(tw_rest),
                                radix_kernel(n as u32, logn, l, r, wgsz)
                            ),
                            &format!("hybrad_l{l}_r{r}"),
                        ),
                        (((n as u32) >> r).div_ceil(wgsz), ncols as u32),
                    ));
                    l += r;
                }
                let plan: Vec<(&wgpu::ComputePipeline, (u32, u32))> =
                    pipes.iter().map(|(p, d)| (p, *d)).collect();
                let label = format!(
                    "hybrid E1={e1} B={} +radix{:?}{}",
                    1 << lb,
                    chunks,
                    tw_suffix(mode)
                );
                gpu.time_plan(&plan, 1, 0);
                parity_all &= check_parity(&label);
                let iters = ((1 << 26) / ntotal as u32).clamp(8, 256);
                let t = gpu.time_plan(&plan, iters, 3);
                report_plan(&label, t, ntotal, plan.len() as u32, ceiling, &mut best);
                let bytes1 = ntotal as f64 * 8.0;
                let mut attribution = String::new();
                for (i, (p, d)) in pipes.iter().enumerate() {
                    let tp = gpu.time_plan(&[(p, *d)], iters, 3);
                    attribution.push_str(&format!(
                        "pass{} {:.3} ms ({:.0} GB/s, {:.0}% ceil)  ",
                        i + 1,
                        tp * 1e3,
                        bytes1 / tp / 1e9,
                        bytes1 / tp / ceiling * 100.0
                    ));
                }
                println!("    {attribution}");
            }
        }

        if !parity_all {
            println!("PARITY FAILURE — aborting");
            std::process::exit(1);
        }
        let (bt, bl, bp) = best.unwrap();
        results.push(ShapeResult {
            label: format!("2^{logn} x {ncols}"),
            ntotal,
            best_gpu_s: bt,
            best_plan: bl,
            best_passes: bp,
            cpu1_s: Some(cpu1_s),
            cpu12_s: Some(cpu12_s),
        });
    }

    // 4. Summary.
    println!("\n================= SUMMARY =================");
    println!(
        "copy ceiling: {:.1} GB/s measured ({:.0}% of 400 GB/s M2 Max spec)",
        ceiling / 1e9,
        ceiling / SPEC_BW * 100.0
    );
    for r in &results {
        let traffic = r.best_passes as f64 * 8.0 * r.ntotal as f64;
        let gbps = traffic / r.best_gpu_s;
        let melems = r.ntotal as f64 / r.best_gpu_s / 1e6;
        println!(
            "{:>10}  best {:<22} {:>8.3} ms  {:>6.0} Melem/s  {:>5.1} GB/s eff  {:>3.0}% of ceiling  {:>3.0}% of spec | cpu1 {:>7.1} ms, cpu-rayon {:>6.1} ms  (gpu = {:>5.1}x cpu1, {:>4.1}x rayon)",
            r.label,
            r.best_plan,
            r.best_gpu_s * 1e3,
            melems,
            gbps / 1e9,
            gbps / ceiling * 100.0,
            gbps / SPEC_BW * 100.0,
            r.cpu1_s.unwrap() * 1e3,
            r.cpu12_s.unwrap() * 1e3,
            r.cpu1_s.unwrap() / r.best_gpu_s,
            r.cpu12_s.unwrap() / r.best_gpu_s,
        );
    }
    println!("\nnote: 'GB/s eff' counts passes x (read+write) actually performed; ");
    println!("'%-of-ceiling' is vs the measured copy kernel, the honest achievable peak.");
}

fn report_plan(
    label: &str,
    t: f64,
    ntotal: usize,
    passes: u32,
    ceiling: f64,
    best: &mut Option<(f64, String, u32)>,
) {
    let traffic = passes as f64 * 8.0 * ntotal as f64;
    let gbps = traffic / t;
    println!(
        "  {label}: {:.3} ms  ({:.0} Melem/s, {passes} passes, eff {:.1} GB/s = {:.0}% of ceiling, {:.0}% of 400 GB/s spec)",
        t * 1e3,
        ntotal as f64 / t / 1e6,
        gbps / 1e9,
        gbps / ceiling * 100.0,
        gbps / SPEC_BW * 100.0
    );
    if best.as_ref().map_or(true, |(bt, _, _)| t < *bt) {
        *best = Some((t, label.to_string(), passes));
    }
}

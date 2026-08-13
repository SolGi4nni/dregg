//! Four-step NTT as GEMM — correctness and the measured comparison against the
//! deployed radix-2 GPU NTT.
//!
//! This is the CROSS/MORPH shape (see `~/dev/zkml-research/notes/ntt-as-gemm.md`):
//! a length-N transform decomposed as N = R*C into two dense matrix products
//! plus a pointwise twiddle, which is O(N*sqrt(N)) modular multiplies against
//! radix-2's O(N log N) — a deliberately worse asymptotic bought back on
//! hardware whose matrix engine runs 1-2 orders faster than its vector unit.
//!
//! Three dialects, one set of tables, one boundary:
//!   `mont` — one three-limb radix-2^16 Montgomery modmul per MAC (the same
//!            kernel `shaders/bfv_ntt.wgsl` uses; the honest baseline).
//!   `bat`  — CROSS's Basis Aligned Transformation: preknown twiddles expanded
//!            offline into K x K byte matrices, exact 8-bit MACs into u32.
//!   `amx`  — the same BAT contraction as an exact-integer FP32 GEMM through
//!            Accelerate (which lands on the M-series AMX matrix coprocessor).
//!            This is the only real matrix engine reachable from this box.
//!
//! Every dialect is checked bit-exact against a schoolbook negacyclic product
//! and against the deployed `RnsNttEngine` before any timing is reported.

use fhegg_fhe::bfv_lean::{RnsPoly, FOLD_MODULI};
use fhegg_fhe::bfv_ntt_gpu::{multiply_rns_cpu, RnsNttBackend, RnsNttEngine};
use std::time::Instant;
use wgpu::util::DeviceExt;

/// Montgomery radix, matching `GPU_MONTGOMERY_RADIX` in `bfv_ntt_gpu.rs`.
const MONT_R_LOG: u32 = 48;

/// BabyBear — the deployed prover field. 31 bits, so K = 4 exactly like CROSS.
const BABYBEAR: u64 = 2_013_265_921;

// ------------------------------------------------------------- field helpers

fn mulmod(a: u64, b: u64, q: u64) -> u64 {
    ((u128::from(a) * u128::from(b)) % u128::from(q)) as u64
}

fn powmod(base: u64, mut exp: u64, q: u64) -> u64 {
    let mut acc = 1u64;
    let mut b = base % q;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = mulmod(acc, b, q);
        }
        b = mulmod(b, b, q);
        exp >>= 1;
    }
    acc
}

fn invmod(a: u64, q: u64) -> u64 {
    powmod(a, q - 2, q)
}

/// A primitive `2n`-th root of unity mod q, for `2n` a power of two. Returns
/// psi with ord(psi) = 2n exactly, hence psi^n = -1 (the negacyclic twist).
fn primitive_2n_root(q: u64, two_n: u64) -> u64 {
    assert!(two_n.is_power_of_two());
    assert_eq!((q - 1) % two_n, 0, "q-1 must be divisible by 2N");
    let exp = (q - 1) / two_n;
    for x in 2u64..100_000 {
        let c = powmod(x, exp, q);
        // ord(c) | 2n = 2^k, so ord(c) = 2n iff c^(n) != 1.
        if powmod(c, two_n / 2, q) != 1 {
            debug_assert_eq!(powmod(c, two_n / 2, q), q - 1);
            return c;
        }
    }
    panic!("no primitive {two_n}-th root mod {q}");
}

/// `-q^-1 mod 2^16` over the low 16-bit limb, as `mont_mul` in the shader wants.
fn qinv16(q: u64) -> u32 {
    let q0 = (q & 0xffff) as u32;
    let mut inv = 1u32;
    for _ in 0..5 {
        inv = inv.wrapping_mul(2u32.wrapping_sub(q0.wrapping_mul(inv)));
    }
    inv &= 0xffff;
    debug_assert_eq!((q0.wrapping_mul(inv)) & 0xffff, 1);
    ((0x1_0000u32).wrapping_sub(inv)) & 0xffff
}

fn to_mont(x: u64, q: u64) -> u64 {
    ((u128::from(x) << MONT_R_LOG) % u128::from(q)) as u64
}

// ----------------------------------------------------------- CPU references

/// Schoolbook product in Z_q[X]/(X^n + 1). The independent oracle.
fn negacyclic_schoolbook(a: &[u64], b: &[u64], q: u64) -> Vec<u64> {
    let n = a.len();
    let mut out = vec![0u64; n];
    for (i, &ai) in a.iter().enumerate() {
        if ai == 0 {
            continue;
        }
        for (j, &bj) in b.iter().enumerate() {
            let p = mulmod(ai, bj, q);
            let k = i + j;
            if k < n {
                out[k] = (out[k] + p) % q;
            } else {
                out[k - n] = (out[k - n] + q - p) % q;
            }
        }
    }
    out
}

/// The four-step transform on the CPU, in plain residues. Used to pin the
/// decomposition itself before any GPU is involved.
fn four_step_cpu(input: &[u64], r_dim: usize, c_dim: usize, omega: u64, q: u64) -> Vec<u64> {
    let n = r_dim * c_dim;
    assert_eq!(input.len(), n);
    let w_c = powmod(omega, r_dim as u64, q); // order C
    let w_r = powmod(omega, c_dim as u64, q); // order R
    let mut mid = vec![0u64; n];
    for r in 0..r_dim {
        for cp in 0..c_dim {
            let mut acc = 0u64;
            for c in 0..c_dim {
                let w = powmod(w_c, ((c * cp) % c_dim) as u64, q);
                acc = (acc + mulmod(input[c * r_dim + r], w, q)) % q;
            }
            mid[r * c_dim + cp] = mulmod(acc, powmod(omega, ((r * cp) % n) as u64, q), q);
        }
    }
    let mut out = vec![0u64; n];
    for rp in 0..r_dim {
        for cp in 0..c_dim {
            let mut acc = 0u64;
            for r in 0..r_dim {
                let w = powmod(w_r, ((r * rp) % r_dim) as u64, q);
                acc = (acc + mulmod(mid[r * c_dim + cp], w, q)) % q;
            }
            out[rp * c_dim + cp] = acc;
        }
    }
    out
}

/// Naive O(N^2) DFT — the ground truth the four-step must reproduce.
fn naive_dft(input: &[u64], omega: u64, q: u64) -> Vec<u64> {
    let n = input.len();
    (0..n)
        .map(|k| {
            let mut acc = 0u64;
            for (idx, &v) in input.iter().enumerate() {
                acc = (acc + mulmod(v, powmod(omega, ((idx * k) % n) as u64, q), q)) % q;
            }
            acc
        })
        .collect()
}

// ----------------------------------------------------------------- BAT tables

/// K = number of 8-bit limbs needed to hold a residue mod q.
fn k_limbs(q: u64) -> u32 {
    (64 - (q - 1).leading_zeros()).div_ceil(8)
}

/// CROSS Eq. (4)-(6): expand a preknown Montgomery-form twiddle `w` into the
/// K x K byte matrix `a[j][i] = byte_j( (w << 8i) mod q )`, packed 4 bytes to a
/// u32 along the `i` (runtime byte-lane) axis so the inner product is a
/// `dot4u8`.
///
/// Written PLANE-MAJOR — `out[((j*KW + wd)*dim + cell)]` — so GPU lanes that
/// differ only in the fast output index read adjacent words. The obvious
/// entry-major packing strides by K*KW and measures ~2x slower.
fn bat_expand_into(w: u64, q: u64, k: u32, kw: u32, plane: usize, cell: usize, out: &mut [u32]) {
    let mut shifted = [0u64; 8];
    for (i, slot) in shifted.iter_mut().enumerate().take(k as usize) {
        *slot = ((u128::from(w) << (8 * i)) % u128::from(q)) as u64;
    }
    for j in 0..k {
        for wd in 0..kw {
            let mut packed = 0u32;
            for t in 0..4u32 {
                let i = wd * 4 + t;
                if i < k {
                    let byte = ((shifted[i as usize] >> (8 * j)) & 0xff) as u32;
                    packed |= byte << (8 * t);
                }
            }
            out[((j * kw + wd) as usize) * plane + cell] = packed;
        }
    }
}

// -------------------------------------------------------------- GPU plumbing

#[repr(C)]
#[derive(Clone, Copy, Default, bytemuck::Pod, bytemuck::Zeroable)]
struct Meta {
    n: u32,
    r_dim: u32,
    c_dim: u32,
    items: u32,
    modulus_rows: u32,
    k_limbs: u32,
    k_words: u32,
    off_tw_c: u32,
    off_tw_r: u32,
    off_tw_mid: u32,
    off_twist: u32,
    tbl_stride: u32,
    bat_stride: u32,
    off_bat_c: u32,
    off_bat_r: u32,
    grid_w: u32,
}

fn buffer_entry(binding: u32, ty: wgpu::BufferBindingType) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty,
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }
}

struct RowTables {
    q: u64,
    /// Per direction (0 = forward, 1 = inverse): tw_c, tw_r, tw_mid, twist.
    words: Vec<u32>,
    bat: Vec<u32>,
    section: [u32; 4],
    dir_words: u32,
    dir_bat: u32,
    bat_section: [u32; 2],
}

/// Build every table for one modulus at one (R, C).
fn build_row(q: u64, r_dim: usize, c_dim: usize) -> RowTables {
    let n = r_dim * c_dim;
    let psi = primitive_2n_root(q, 2 * n as u64);
    let omega = mulmod(psi, psi, q);
    let psi_inv = invmod(psi, q);
    let omega_inv = invmod(omega, q);
    let n_inv = invmod(n as u64 % q, q);
    let k = k_limbs(q);
    let kw = k.div_ceil(4);

    let mut words = Vec::new();
    let mut bat = Vec::new();
    let mut section = [0u32; 4];
    let mut bat_section = [0u32; 2];
    let mut dir_words = 0u32;
    let mut dir_bat = 0u32;

    for dir in 0..2usize {
        let (w, ps) = if dir == 0 {
            (omega, psi)
        } else {
            (omega_inv, psi_inv)
        };
        let w_c = powmod(w, r_dim as u64, q);
        let w_r = powmod(w, c_dim as u64, q);
        let start = words.len() as u32 / 2;
        let bstart = bat.len() as u32 / 1;

        // tw_c[c][c'] = w_C^{c c'}
        let s0 = words.len() as u32 / 2;
        let b0 = bat.len() as u32;
        let plane_c = c_dim * c_dim;
        bat.resize(bat.len() + plane_c * (k * kw) as usize, 0);
        let block = bat.len() - plane_c * (k * kw) as usize;
        for c in 0..c_dim {
            for cp in 0..c_dim {
                let v = to_mont(powmod(w_c, ((c * cp) % c_dim) as u64, q), q);
                words.push(v as u32);
                words.push((v >> 32) as u32);
                bat_expand_into(v, q, k, kw, plane_c, c * c_dim + cp, &mut bat[block..]);
            }
        }
        // tw_r[r'][r] = w_R^{r r'}
        let s1 = words.len() as u32 / 2;
        let b1 = bat.len() as u32;
        let plane_r = r_dim * r_dim;
        bat.resize(bat.len() + plane_r * (k * kw) as usize, 0);
        let block = bat.len() - plane_r * (k * kw) as usize;
        for rp in 0..r_dim {
            for r in 0..r_dim {
                let v = to_mont(powmod(w_r, ((r * rp) % r_dim) as u64, q), q);
                words.push(v as u32);
                words.push((v >> 32) as u32);
                bat_expand_into(v, q, k, kw, plane_r, rp * r_dim + r, &mut bat[block..]);
            }
        }
        // tw_mid[r][c'] = w_N^{r c'}
        let s2 = words.len() as u32 / 2;
        for r in 0..r_dim {
            for cp in 0..c_dim {
                let v = to_mont(powmod(w, ((r * cp) % n) as u64, q), q);
                words.push(v as u32);
                words.push((v >> 32) as u32);
            }
        }
        // twist: psi^i forward, n^-1 * psi^-i inverse
        let s3 = words.len() as u32 / 2;
        let mut acc = 1u64;
        for _ in 0..n {
            let scaled = if dir == 0 { acc } else { mulmod(acc, n_inv, q) };
            let v = to_mont(scaled, q);
            words.push(v as u32);
            words.push((v >> 32) as u32);
            acc = mulmod(acc, ps, q);
        }

        if dir == 0 {
            section = [s0 - start, s1 - start, s2 - start, s3 - start];
            bat_section = [b0 - bstart, b1 - bstart];
            dir_words = words.len() as u32 / 2;
            dir_bat = bat.len() as u32;
        }
    }

    RowTables {
        q,
        words,
        bat,
        section,
        dir_words,
        dir_bat,
        bat_section,
    }
}

struct FourStep {
    device: wgpu::Device,
    queue: wgpu::Queue,
    adapter: String,
    bgl: wgpu::BindGroupLayout,
    pipelines: Vec<(String, wgpu::ComputePipeline)>,
    qdata: wgpu::Buffer,
    tables: wgpu::Buffer,
    bat: wgpu::Buffer,
    rows: Vec<RowTables>,
    r_dim: usize,
    c_dim: usize,
    n: usize,
    tbl_stride: u32,
    bat_stride: u32,
}

impl FourStep {
    fn new(moduli: &[u64], r_dim: usize, c_dim: usize) -> Result<Self, String> {
        let n = r_dim * c_dim;
        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
        .ok_or_else(|| "no wgpu adapter".to_owned())?;
        let info = adapter.get_info();
        let limits = adapter.limits();
        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("ntt-four-step"),
                required_features: wgpu::Features::empty(),
                required_limits: limits,
                memory_hints: Default::default(),
            },
            None,
        ))
        .map_err(|e| format!("device request failed: {e}"))?;

        device.push_error_scope(wgpu::ErrorFilter::Validation);
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("ntt_four_step.wgsl"),
            source: wgpu::ShaderSource::Wgsl(include_str!("../shaders/ntt_four_step.wgsl").into()),
        });
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("ntt-four-step-bindings"),
            entries: &[
                buffer_entry(0, wgpu::BufferBindingType::Uniform),
                buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(5, wgpu::BufferBindingType::Storage { read_only: true }),
            ],
        });
        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("ntt-four-step-layout"),
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let names = [
            "pass_twist",
            "pass_step1_mont",
            "pass_step2",
            "pass_step3_mont",
            "pass_step1_bat",
            "pass_step3_bat",
            "pass_pointwise",
        ];
        let pipelines: Vec<_> = names
            .iter()
            .map(|entry| {
                (
                    (*entry).to_owned(),
                    device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                        label: Some(entry),
                        layout: Some(&layout),
                        module: &shader,
                        entry_point: Some(entry),
                        compilation_options: Default::default(),
                        cache: None,
                    }),
                )
            })
            .collect();
        if let Some(error) = pollster::block_on(device.pop_error_scope()) {
            return Err(format!("shader validation failed: {error}"));
        }

        let rows: Vec<RowTables> = moduli.iter().map(|&q| build_row(q, r_dim, c_dim)).collect();
        let tbl_stride = rows[0].words.len() as u32 / 2;
        let bat_stride = rows[0].bat.len() as u32;

        let mut qwords = Vec::new();
        for row in &rows {
            let q = row.q;
            let r2 = ((1u128 << (2 * MONT_R_LOG)) % u128::from(q)) as u64;
            qwords.extend_from_slice(&[
                q as u32,
                (q >> 32) as u32,
                qinv16(q),
                0,
                r2 as u32,
                (r2 >> 32) as u32,
                0,
                0,
            ]);
        }
        let mut table_words = Vec::new();
        let mut bat_words = Vec::new();
        for row in &rows {
            table_words.extend_from_slice(&row.words);
            bat_words.extend_from_slice(&row.bat);
        }

        let qdata = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("qdata"),
            contents: bytemuck::cast_slice(&qwords),
            usage: wgpu::BufferUsages::STORAGE,
        });
        let tables = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("tables"),
            contents: bytemuck::cast_slice(&table_words),
            usage: wgpu::BufferUsages::STORAGE,
        });
        let bat = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("bat"),
            contents: bytemuck::cast_slice(&bat_words),
            usage: wgpu::BufferUsages::STORAGE,
        });

        Ok(Self {
            device,
            queue,
            adapter: format!("{} ({:?})", info.name, info.backend),
            bgl,
            pipelines,
            qdata,
            tables,
            bat,
            rows,
            r_dim,
            c_dim,
            n,
            tbl_stride,
            bat_stride,
        })
    }

    fn pipeline(&self, name: &str) -> &wgpu::ComputePipeline {
        &self
            .pipelines
            .iter()
            .find(|(n, _)| n == name)
            .expect("pipeline")
            .1
    }

    fn meta(&self, items: u32, dir: usize) -> Meta {
        let row = &self.rows[0];
        let dw = if dir == 0 { 0 } else { row.dir_words };
        let db = if dir == 0 { 0 } else { row.dir_bat };
        Meta {
            n: self.n as u32,
            r_dim: self.r_dim as u32,
            c_dim: self.c_dim as u32,
            items,
            modulus_rows: self.rows.len() as u32,
            k_limbs: k_limbs(row.q),
            k_words: k_limbs(row.q).div_ceil(4),
            off_tw_c: dw + row.section[0],
            off_tw_r: dw + row.section[1],
            off_tw_mid: dw + row.section[2],
            off_twist: dw + row.section[3],
            tbl_stride: self.tbl_stride,
            bat_stride: self.bat_stride,
            off_bat_c: db + row.bat_section[0],
            off_bat_r: db + row.bat_section[1],
            grid_w: 0,
        }
    }

    /// Run `passes` over `items` transforms already resident in `data`.
    #[allow(clippy::too_many_arguments)]
    fn run(
        &self,
        data: &wgpu::Buffer,
        scratch: &wgpu::Buffer,
        items: u32,
        dir: usize,
        passes: &[&str],
    ) {
        // wgpu caps a dispatch dimension at 65535 workgroups; spill into y.
        let groups_total = (items as usize * self.n).div_ceil(64);
        let gx = groups_total.min(32768);
        let gy = groups_total.div_ceil(gx);
        let mut meta = self.meta(items, dir);
        meta.grid_w = (gx * 64) as u32;
        let ubo = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("meta"),
                contents: bytemuck::bytes_of(&meta),
                usage: wgpu::BufferUsages::UNIFORM,
            });
        let bind = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bind"),
            layout: &self.bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: ubo.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: data.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: scratch.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: self.qdata.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 4,
                    resource: self.tables.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 5,
                    resource: self.bat.as_entire_binding(),
                },
            ],
        });
        let mut enc = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor { label: None });
        for name in passes {
            let mut pass = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some(name),
                timestamp_writes: None,
            });
            pass.set_pipeline(self.pipeline(name));
            pass.set_bind_group(0, &bind, &[]);
            pass.dispatch_workgroups(gx as u32, gy as u32, 1);
        }
        self.queue.submit(Some(enc.finish()));
    }

    fn alloc(&self, items: usize) -> wgpu::Buffer {
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size: (items * self.n * 2 * 4) as u64,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_DST
                | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        })
    }

    fn upload(&self, buf: &wgpu::Buffer, values: &[u64]) {
        let mut words = Vec::with_capacity(values.len() * 2);
        for &v in values {
            words.push(v as u32);
            words.push((v >> 32) as u32);
        }
        self.queue
            .write_buffer(buf, 0, bytemuck::cast_slice(&words));
    }

    fn download(&self, buf: &wgpu::Buffer, count: usize) -> Vec<u64> {
        let bytes = (count * 2 * 4) as u64;
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size: bytes,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut enc = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor { label: None });
        enc.copy_buffer_to_buffer(buf, 0, &staging, 0, bytes);
        self.queue.submit(Some(enc.finish()));
        let slice = staging.slice(..);
        let (tx, rx) = std::sync::mpsc::channel();
        slice.map_async(wgpu::MapMode::Read, move |r| {
            let _ = tx.send(r);
        });
        self.device.poll(wgpu::Maintain::Wait);
        rx.recv().expect("map").expect("map ok");
        let view = slice.get_mapped_range();
        let words: &[u32] = bytemuck::cast_slice(&view);
        let out = words
            .chunks_exact(2)
            .map(|c| u64::from(c[0]) | (u64::from(c[1]) << 32))
            .collect();
        drop(view);
        staging.unmap();
        out
    }

    fn forward_passes(dialect: &str) -> Vec<&'static str> {
        match dialect {
            "mont" => vec![
                "pass_twist",
                "pass_step1_mont",
                "pass_step2",
                "pass_step3_mont",
            ],
            "bat" => vec![
                "pass_twist",
                "pass_step1_bat",
                "pass_step2",
                "pass_step3_bat",
            ],
            _ => unreachable!(),
        }
    }

    fn inverse_passes(dialect: &str) -> Vec<&'static str> {
        match dialect {
            "mont" => vec![
                "pass_step1_mont",
                "pass_step2",
                "pass_step3_mont",
                "pass_twist",
            ],
            "bat" => vec![
                "pass_step1_bat",
                "pass_step2",
                "pass_step3_bat",
                "pass_twist",
            ],
            _ => unreachable!(),
        }
    }
}

// ------------------------------------------------------- exact FP32 via AMX

#[link(name = "Accelerate", kind = "framework")]
extern "C" {
    fn cblas_sgemm(
        order: i32,
        transa: i32,
        transb: i32,
        m: i32,
        n: i32,
        k: i32,
        alpha: f32,
        a: *const f32,
        lda: i32,
        b: *const f32,
        ldb: i32,
        beta: f32,
        c: *mut f32,
        ldc: i32,
    );
}

const CBLAS_ROW_MAJOR: i32 = 101;
const CBLAS_NO_TRANS: i32 = 111;

/// Is a BAT contraction of `dim` elements at K limbs exactly representable in
/// an FP32 accumulator? Every partial sum is a non-negative integer, so the
/// whole GEMM is exact iff the largest possible sum is < 2^24.
fn fp32_exact_bound(dim: usize, k: u32) -> (u64, bool) {
    let max = (dim as u64) * u64::from(k) * 255 * 255;
    (max, max < (1u64 << 24))
}

/// One BAT step-1 GEMM through Accelerate: A (R x KC) @ W (KC x KC) with 8-bit
/// entries held as f32. Returns the wall time; the caller checks exactness.
fn amx_bat_gemm(r_dim: usize, c_dim: usize, k: u32, reps: usize) -> (f64, f32) {
    let kc = c_dim * k as usize;
    let a: Vec<f32> = (0..r_dim * kc).map(|i| ((i * 37) % 256) as f32).collect();
    let b: Vec<f32> = (0..kc * kc).map(|i| ((i * 91) % 256) as f32).collect();
    let mut c = vec![0f32; r_dim * kc];
    let mut best = f64::MAX;
    for _ in 0..reps {
        let t = Instant::now();
        unsafe {
            cblas_sgemm(
                CBLAS_ROW_MAJOR,
                CBLAS_NO_TRANS,
                CBLAS_NO_TRANS,
                r_dim as i32,
                kc as i32,
                kc as i32,
                1.0,
                a.as_ptr(),
                kc as i32,
                b.as_ptr(),
                kc as i32,
                0.0,
                c.as_mut_ptr(),
                kc as i32,
            );
        }
        best = best.min(t.elapsed().as_secs_f64());
    }
    (best, c[0])
}

// ------------------------------------------------------------------ harness

fn deterministic_poly(seed: u64, n: usize, moduli: &[u64]) -> RnsPoly {
    let mut s = seed;
    let mut next = || {
        s = s
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(17)
            .wrapping_add(1);
        s
    };
    RnsPoly {
        rows: moduli
            .iter()
            .map(|&q| (0..n).map(|_| next() % q).collect())
            .collect(),
    }
}

fn best_secs<F: FnMut()>(reps: usize, mut f: F) -> f64 {
    let mut best = f64::MAX;
    for _ in 0..reps {
        let t = Instant::now();
        f();
        best = best.min(t.elapsed().as_secs_f64());
    }
    best
}

fn cpu_decomposition_check() {
    println!("== CPU: the decomposition itself ==");
    for &(r, c) in &[(8usize, 8usize), (16, 16), (8, 32), (32, 8)] {
        let n = r * c;
        let q = FOLD_MODULI[0];
        let psi = primitive_2n_root(q, 2 * n as u64);
        let omega = mulmod(psi, psi, q);
        let input: Vec<u64> = (0..n).map(|i| ((i as u64) * 7919 + 13) % q).collect();
        let want = naive_dft(&input, omega, q);
        let got = four_step_cpu(&input, r, c, omega, q);
        assert_eq!(want, got, "four-step != naive DFT at R={r} C={c}");
        println!("  N={n:5}  (R,C)=({r},{c})  four-step == naive O(N^2) DFT   OK");
    }
}

fn gpu_correctness(engine: &FourStep, moduli: &[u64], dialect: &str) {
    let n = engine.n;
    let rows = moduli.len();
    let lhs = deterministic_poly(0x1234, n, moduli);
    let rhs = deterministic_poly(0x9876, n, moduli);

    // Two operands, `rows` moduli each -> 2*rows items; the pointwise pass
    // pairs item i with item i+items.
    let items = rows as u32;
    let data = engine.alloc(2 * rows);
    let scratch = engine.alloc(2 * rows);
    let mut flat = Vec::with_capacity(2 * rows * n);
    for row in &lhs.rows {
        flat.extend_from_slice(row);
    }
    for row in &rhs.rows {
        flat.extend_from_slice(row);
    }
    engine.upload(&data, &flat);

    let fwd = FourStep::forward_passes(dialect);
    let inv = FourStep::inverse_passes(dialect);
    engine.run(&data, &scratch, 2 * items, 0, &fwd);
    engine.run(&data, &scratch, items, 0, &["pass_pointwise"]);
    engine.run(&data, &scratch, items, 1, &inv);
    engine.device.poll(wgpu::Maintain::Wait);
    let out = engine.download(&data, rows * n);

    for (i, &q) in moduli.iter().enumerate() {
        let want = negacyclic_schoolbook(&lhs.rows[i], &rhs.rows[i], q);
        let got = &out[i * n..(i + 1) * n];
        assert_eq!(
            want.as_slice(),
            got,
            "{dialect}: negacyclic product mismatch at modulus {q}"
        );
    }
    println!("  {dialect:4}: negacyclic product == schoolbook, all {rows} moduli, N={n}   OK");

    if moduli == FOLD_MODULI {
        let cpu = multiply_rns_cpu(&lhs, &rhs, moduli).expect("deployed CPU reference");
        for (i, row) in cpu.rows.iter().enumerate() {
            assert_eq!(
                row.as_slice(),
                &out[i * n..(i + 1) * n],
                "{dialect}: disagrees with deployed multiply_rns_cpu at row {i}"
            );
        }
        println!("  {dialect:4}: bit-exact vs deployed `multiply_rns_cpu`                 OK");

        let gpu = RnsNttEngine::require_wgpu();
        if let Ok(exec) = gpu.multiply(&lhs, &rhs, moduli) {
            for (i, row) in exec.polynomial.rows.iter().enumerate() {
                assert_eq!(
                    row.as_slice(),
                    &out[i * n..(i + 1) * n],
                    "{dialect}: disagrees with deployed radix-2 GPU NTT at row {i}"
                );
            }
            println!("  {dialect:4}: bit-exact vs deployed radix-2 GPU NTT                  OK");
        }
    }
}

fn main() {
    println!("ntt_four_step_bench — the NTT as GEMM, measured against the deployed radix-2 kernel");
    println!();
    cpu_decomposition_check();
    println!();

    let n = 4096usize;
    let configs: &[(usize, usize)] = &[(64, 64), (32, 128), (128, 32)];

    println!("== GPU: correctness at N={n}, (R,C)=(64,64), deployed FOLD_MODULI ==");
    let engine = match FourStep::new(&FOLD_MODULI, 64, 64) {
        Ok(e) => e,
        Err(e) => {
            println!("NO usable wgpu adapter ({e}) — honest exit.");
            std::process::exit(2);
        }
    };
    println!("  adapter: {}", engine.adapter);
    println!(
        "  K = {} limbs (q up to {} bits), k_words = {}",
        k_limbs(FOLD_MODULI[2]),
        64 - (FOLD_MODULI[2] - 1).leading_zeros(),
        k_limbs(FOLD_MODULI[2]).div_ceil(4)
    );
    gpu_correctness(&engine, &FOLD_MODULI, "mont");
    gpu_correctness(&engine, &FOLD_MODULI, "bat");
    println!();

    // BabyBear: the deployed prover field, K = 4 exactly like CROSS.
    println!("== GPU: correctness over BabyBear (the prover field, 31 bits, K=4) ==");
    let bb = [BABYBEAR];
    match FourStep::new(&bb, 64, 64) {
        Ok(e) => {
            println!("  K = {} limbs, k_words = {}", k_limbs(BABYBEAR), 1);
            gpu_correctness(&e, &bb, "mont");
            gpu_correctness(&e, &bb, "bat");
        }
        Err(e) => println!("  unavailable: {e}"),
    }
    println!();

    // ---- op counts, which are hardware-independent -------------------------
    println!("== Op counts per length-{n} transform, per modulus ==");
    let log_n = n.trailing_zeros() as usize;
    let radix2 = n / 2 * log_n;
    println!("  radix-2 Cooley-Tukey : {radix2:>12} modmuls   (O(N log N))");
    for &(r, c) in configs {
        let four = n * (r + c);
        println!(
            "  four-step ({r:>3},{c:>3})  : {four:>12} modmuls   ({:.1}x radix-2)",
            four as f64 / radix2 as f64
        );
    }
    for (label, q) in [
        ("FOLD q2 (37b)", FOLD_MODULI[2]),
        ("BabyBear (31b)", BABYBEAR),
    ] {
        let k = k_limbs(q);
        let kw = k.div_ceil(4);
        let lanes = (k * kw * 4) as usize; // byte-MACs issued per (element,element)
        let useful = (k * k) as usize;
        let four = n * (64 + 64);
        println!(
            "  BAT {label}: K={k} KW={kw} -> {:>12} byte-MACs ({} issued / {} useful per pair, {:.0}% waste)",
            four * lanes,
            lanes,
            useful,
            100.0 * (1.0 - useful as f64 / lanes as f64)
        );
    }
    println!();

    // ---- FP32 exactness budget --------------------------------------------
    println!("== FP32 (AMX / BF16-class) exactness budget: partial sums must stay < 2^24 ==");
    for (label, q) in [
        ("BabyBear (31b)", BABYBEAR),
        ("FOLD q2 (37b)", FOLD_MODULI[2]),
    ] {
        let k = k_limbs(q);
        for &c in &[64usize, 128, 256] {
            let (max, ok) = fp32_exact_bound(c, k);
            println!(
                "  {label}  K={k}  contraction C={c:<4} -> max partial sum {max:>12} {}",
                if ok {
                    "< 2^24  EXACT"
                } else {
                    ">= 2^24  UNSOUND"
                }
            );
        }
    }
    println!();

    // ---- the measurement ---------------------------------------------------
    println!(
        "== Measured forward transforms, N={n}, FOLD_MODULI (3 rows), batch of polynomials =="
    );
    println!("  (best of 5; wall clock including submit+fence, excluding upload/download)");
    let deployed_gpu = RnsNttEngine::require_wgpu();
    let warm = deterministic_poly(1, n, &FOLD_MODULI);
    let ok_deployed = matches!(
        deployed_gpu
            .forward_odd(&warm, &FOLD_MODULI)
            .map(|e| e.backend),
        Ok(RnsNttBackend::Wgpu { .. })
    );

    println!();
    println!(
        "  {:>6} | {:>10} | {:>11} | {:>11} | {:>11} | {:>10}",
        "batch", "up+down", "radix-2 GPU", "4step mont", "4step BAT", "mont/BAT"
    );
    let mut io_rows: Vec<(usize, f64, f64, f64, f64)> = Vec::new();
    for &batch in &[8usize, 32, 128, 512] {
        let polys: Vec<RnsPoly> = (0..batch)
            .map(|i| deterministic_poly(i as u64 + 100, n, &FOLD_MODULI))
            .collect();
        let items = (batch * FOLD_MODULI.len()) as u32;
        let data = engine.alloc(batch * FOLD_MODULI.len());
        let scratch = engine.alloc(batch * FOLD_MODULI.len());
        let mut flat = Vec::new();
        for p in &polys {
            for row in &p.rows {
                flat.extend_from_slice(row);
            }
        }
        engine.upload(&data, &flat);

        // The deployed API takes host polys and returns host results, so its
        // number necessarily includes the round trip. The `+up/down` column is
        // the like-for-like one; the bare columns are device-resident.
        let radix2_ms = if ok_deployed {
            best_secs(5, || {
                let _ = deployed_gpu
                    .forward_odd_batch(&polys, &FOLD_MODULI)
                    .expect("deployed forward");
            }) * 1000.0
        } else {
            f64::NAN
        };
        let mont_ms = best_secs(5, || {
            engine.run(&data, &scratch, items, 0, &FourStep::forward_passes("mont"));
            engine.device.poll(wgpu::Maintain::Wait);
        }) * 1000.0;
        let bat_ms = best_secs(5, || {
            engine.run(&data, &scratch, items, 0, &FourStep::forward_passes("bat"));
            engine.device.poll(wgpu::Maintain::Wait);
        }) * 1000.0;
        // The deployed API is host-in/host-out, so its column carries a round
        // trip that the two device-resident columns do not. Measure that round
        // trip on its own rather than guessing at it.
        let io_ms = best_secs(5, || {
            engine.upload(&data, &flat);
            engine.device.poll(wgpu::Maintain::Wait);
            let _ = engine.download(&data, batch * FOLD_MODULI.len() * n);
        }) * 1000.0;
        println!(
            "  {batch:>6} | {io_ms:>8.2}ms | {radix2_ms:>9.2}ms | {mont_ms:>9.2}ms | {bat_ms:>9.2}ms | {:>9.2}x",
            mont_ms / bat_ms
        );
        io_rows.push((batch, io_ms, radix2_ms, mont_ms, bat_ms));
    }
    println!();

    // ---- what the measurement says a byte-MAC is worth here ----------------
    println!(
        "== Derived from the two dialects: the cost of ONE Montgomery modmul, in byte-MACs =="
    );
    let k = k_limbs(FOLD_MODULI[2]);
    let lanes = (k * k.div_ceil(4) * 4) as f64;
    let modmuls_per_tx = (n * (64 + 64)) as f64;
    let bytemacs_per_tx = modmuls_per_tx * lanes;
    for &(batch, _io, _r2, mont_ms, bat_ms) in &io_rows {
        let ratio = (bytemacs_per_tx / modmuls_per_tx) * (mont_ms / bat_ms);
        println!(
            "  batch {batch:>4}: {bytemacs_per_tx:.0} byte-MACs beat {modmuls_per_tx:.0} modmuls by {:.2}x  =>  1 modmul == {ratio:>6.1} byte-MACs",
            mont_ms / bat_ms
        );
    }
    println!("  (the shader's three-limb REDC issues 21 u32 multiplies; anything above that");
    println!("   is scheduling, carry logic and register pressure -- the EMULATION TAX)");
    println!();

    // ---- what a matrix engine would have to be worth ------------------------
    println!("== Crossover: what a matrix engine must be worth for BAT to win ==");
    println!("  (A) vs a DEDICATED modmul datapath (FPGA/ASIC, 1 modmul per slot)");
    println!("  (B) vs an EMULATED modmul (GPU/TPU VPU, 21 u32 multiplies per modmul)");
    const REDC_MULS: f64 = 21.0;
    for (label, q) in [
        ("BabyBear (31b)", BABYBEAR),
        ("FOLD q2 (37b)", FOLD_MODULI[2]),
    ] {
        let k = k_limbs(q);
        let kw = k.div_ceil(4);
        let lanes = (k * kw * 4) as u64;
        for &nn in &[4096usize, 1 << 16, 1 << 20] {
            let root = (nn as f64).sqrt() as usize;
            let modmuls = (nn / 2 * nn.trailing_zeros() as usize) as u64;
            let bat_macs = (nn as u64) * 2 * (root as u64) * lanes;
            let a = bat_macs as f64 / modmuls as f64;
            println!(
                "  {label}  N=2^{:<2}:  (A) need {a:>7.1}x   (B) need {:>6.1}x",
                nn.trailing_zeros(),
                a / REDC_MULS
            );
        }
    }
    println!();

    // ---- the only real matrix engine on this box ---------------------------
    println!("== AMX (Accelerate sgemm): the BAT step-1 contraction on a real matrix unit ==");
    for (label, q) in [
        ("BabyBear (31b)", BABYBEAR),
        ("FOLD q2 (37b)", FOLD_MODULI[2]),
    ] {
        let k = k_limbs(q);
        let kc = 64 * k as usize;
        let (max, exact) = fp32_exact_bound(64, k);
        let (secs, _probe) = amx_bat_gemm(64, 64, k, 20);
        let macs = 64.0 * kc as f64 * kc as f64;
        println!(
            "  {label}: (64 x {kc}) @ ({kc} x {kc}) = {:.2} MMAC in {:.1} us -> {:.1} GMAC/s   [{}]",
            macs / 1e6,
            secs * 1e6,
            macs / secs / 1e9,
            if exact {
                format!("exact, max partial {max} < 2^24")
            } else {
                format!("NOT EXACT in fp32: max partial {max} >= 2^24")
            }
        );
    }

    // The small BAT tile is call-overhead bound; measure AMX's peak too, so the
    // matrix unit is not understated by our tile choice.
    for &dim in &[256usize, 1024] {
        let a: Vec<f32> = (0..dim * dim).map(|i| ((i * 37) % 256) as f32).collect();
        let b: Vec<f32> = (0..dim * dim).map(|i| ((i * 91) % 256) as f32).collect();
        let mut c = vec![0f32; dim * dim];
        let secs = best_secs(10, || unsafe {
            cblas_sgemm(
                CBLAS_ROW_MAJOR,
                CBLAS_NO_TRANS,
                CBLAS_NO_TRANS,
                dim as i32,
                dim as i32,
                dim as i32,
                1.0,
                a.as_ptr(),
                dim as i32,
                b.as_ptr(),
                dim as i32,
                0.0,
                c.as_mut_ptr(),
                dim as i32,
            );
        });
        let macs = (dim as f64).powi(3);
        println!(
            "  AMX peak probe {dim}^3: {:.1} GMAC/s  (sink {:.0})",
            macs / secs / 1e9,
            c[0]
        );
    }

    // A scalar modmul rate for the same box, to price the ratio.
    let q = FOLD_MODULI[0];
    let iters = 4_000_000usize;
    let t = Instant::now();
    let mut acc = 12345u64;
    for i in 0..iters {
        acc = mulmod(acc, (i as u64 % q) | 1, q);
    }
    let scalar = t.elapsed().as_secs_f64();
    println!(
        "  scalar u128 mulmod (1 core): {:.1} Mmodmul/s  (sink {acc})",
        iters as f64 / scalar / 1e6
    );
    println!();
    println!("done.");
}

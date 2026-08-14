//! GPU BFV fold-add — the aggregation hot path on the GPU (portable wgpu, so it runs on Metal / Vulkan /
//! DX, not just CUDA like tfhe-rs's `gpu` feature).
//!
//! WHY GPU HERE (and not for the STARK prover, and not for BFV *multiply*): the measured envelope says
//! **aggregation dominates and scales with N** — at realistic market sizes the fold is the cost, and it is
//! bulk RNS modular addition = pure memory bandwidth, which a GPU's ~TB/s crushes vs a CPU's ~100 GB/s.
//! (The fold never multiplies, so no NTT/relin — this is exactly the cheap-but-bandwidth-bound shape a
//! compute shader wants.)
//!
//! CORRECTNESS: [`fold_gpu`] computes the SAME value as [`crate::bfv_lean::fold`] — the shader does the
//! identical conditional-subtract modular add per coefficient lane, and summing residues mod q is
//! order-independent, so accumulate-then-reduce == the CPU pairwise fold. The parity test proves it
//! (GPU == CPU, and the GPU result decrypts correctly through the `fhe.rs` oracle). The wrap-budget gate is
//! the SAME scalar check `fold` applies, kept on the CPU (it is a per-batch budget, not per-coefficient).

use crate::bfv_lean::{BfvLeanError, LeanCiphertext, RnsPoly};
use std::sync::OnceLock;

// bfv_lean's own Result alias is module-private; same shape, spelled here.
type Result<T> = std::result::Result<T, BfvLeanError>;

struct GpuCtx {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    bgl: wgpu::BindGroupLayout,
}

fn ctx() -> Option<&'static GpuCtx> {
    static CTX: OnceLock<Option<GpuCtx>> = OnceLock::new();
    CTX.get_or_init(|| {
        // The SHARED device — see `gpu_device`. `Err` here is headless CI (no adapter) or a device
        // refusal, exactly the two cases the old per-module `request_adapter`/`request_device` pair
        // folded into `None`; the caller still falls back to the CPU fold.
        let shared = crate::gpu_device::shared_gpu().ok()?;
        let device = shared.device.clone();
        let queue = shared.queue.clone();
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("bfv_fold.wgsl"),
            source: wgpu::ShaderSource::Wgsl(include_str!("shaders/bfv_fold.wgsl").into()),
        });
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: None,
            entries: &[
                storage_entry(0, wgpu::BufferBindingType::Uniform),
                storage_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
                storage_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
            ],
        });
        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: None,
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("bfv-fold"),
            layout: Some(&layout),
            module: &shader,
            entry_point: Some("main"),
            compilation_options: Default::default(),
            cache: None,
        });
        Some(GpuCtx {
            device,
            queue,
            pipeline,
            bgl,
        })
    })
    .as_ref()
}

fn storage_entry(binding: u32, ty: wgpu::BufferBindingType) -> wgpu::BindGroupLayoutEntry {
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

/// GPU fold — bit-identical to [`crate::bfv_lean::fold`]. Returns `Ok(None)` for the wrap/empty/compat
/// errors `fold` would raise. Returns `Err(GpuUnavailable)` when there is no adapter (so the caller can fall
/// back to the CPU fold rather than fail).
pub fn fold_gpu(cts: &[LeanCiphertext], plaintext_modulus: u64) -> Result<LeanCiphertext> {
    let (first, rest) = cts.split_first().ok_or(BfvLeanError::EmptyFold)?;
    // compat: every ciphertext must agree on the fold shape (degree, moduli, poly-count, level).
    for ct in rest {
        if ct.moduli != first.moduli
            || ct.degree != first.degree
            || ct.polys.len() != first.polys.len()
            || ct.level != first.level
        {
            return Err(BfvLeanError::Incompatible(
                "gpu fold: ciphertexts disagree on fold shape",
            ));
        }
    }
    // wrap-budget: the SAME scalar gate `fold` accumulates — refuse if the summed plaintext bound reaches t.
    let bound_sum: u128 = cts.iter().map(|c| u128::from(c.plain_bound)).sum();
    if bound_sum >= u128::from(plaintext_modulus) {
        return Err(BfvLeanError::WrapRefused {
            bound_sum,
            plaintext_modulus,
        });
    }
    // This first stone targets the fresh-fold shape (3 RNS moduli), the only shape the fold path produces.
    if first.moduli.len() != 3 {
        return Err(BfvLeanError::GpuUnsupportedShape);
    }
    let gpu = ctx().ok_or(BfvLeanError::GpuUnavailable)?;

    let p = first.polys.len();
    let r = first.moduli.len();
    let deg = first.degree;
    let n_lanes = p * r * deg;

    // pack N ciphertexts → u32 buffer, lane order [poly][row][coeff], each coeff as (lo, hi).
    let mut input = Vec::<u32>::with_capacity(cts.len() * n_lanes * 2);
    for ct in cts {
        for poly in &ct.polys {
            for row in &poly.rows {
                for &c in row {
                    input.push(c as u32);
                    input.push((c >> 32) as u32);
                }
            }
        }
    }

    let meta = build_meta(cts.len() as u32, n_lanes as u32, deg as u32, &first.moduli);
    let out_u32 = run(gpu, &meta, &input, n_lanes);

    // unpack → LeanCiphertext (folded), carrying the accumulated bound.
    let mut polys = Vec::with_capacity(p);
    let mut idx = 0usize;
    for _ in 0..p {
        let mut rows = Vec::with_capacity(r);
        for _ in 0..r {
            let mut coeffs = Vec::with_capacity(deg);
            for _ in 0..deg {
                let lo = out_u32[idx * 2] as u64;
                let hi = out_u32[idx * 2 + 1] as u64;
                coeffs.push((hi << 32) | lo);
                idx += 1;
            }
            rows.push(coeffs);
        }
        polys.push(RnsPoly { rows });
    }
    Ok(LeanCiphertext {
        moduli: first.moduli.clone(),
        degree: deg,
        level: first.level,
        variable_time: cts.iter().any(|c| c.variable_time),
        polys,
        plain_bound: bound_sum as u64,
    })
}

// meta layout matches the WGSL `Meta` struct: n_cts, n_lanes, row_len, _pad, then q0/q1/q2 as (lo,hi).
fn build_meta(n_cts: u32, n_lanes: u32, row_len: u32, moduli: &[u64]) -> [u32; 10] {
    let q = |i: usize| (moduli[i] as u32, (moduli[i] >> 32) as u32);
    let (q0l, q0h) = q(0);
    let (q1l, q1h) = q(1);
    let (q2l, q2h) = q(2);
    [n_cts, n_lanes, row_len, 0, q0l, q0h, q1l, q1h, q2l, q2h]
}

fn run(gpu: &GpuCtx, meta: &[u32; 10], input: &[u32], n_lanes: usize) -> Vec<u32> {
    use wgpu::util::DeviceExt;
    let dev = &gpu.device;
    let meta_buf = dev.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("meta"),
        contents: bytemuck::cast_slice(meta),
        usage: wgpu::BufferUsages::UNIFORM,
    });
    let in_buf = dev.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("input"),
        contents: bytemuck::cast_slice(input),
        usage: wgpu::BufferUsages::STORAGE,
    });
    let out_bytes = (n_lanes * 2 * 4) as u64;
    let out_buf = dev.create_buffer(&wgpu::BufferDescriptor {
        label: Some("output"),
        size: out_bytes,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let read_buf = dev.create_buffer(&wgpu::BufferDescriptor {
        label: Some("read"),
        size: out_bytes,
        usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
        mapped_at_creation: false,
    });
    let bind = dev.create_bind_group(&wgpu::BindGroupDescriptor {
        label: None,
        layout: &gpu.bgl,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: meta_buf.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: in_buf.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: out_buf.as_entire_binding(),
            },
        ],
    });
    let mut enc = dev.create_command_encoder(&Default::default());
    {
        let mut pass = enc.begin_compute_pass(&Default::default());
        pass.set_pipeline(&gpu.pipeline);
        pass.set_bind_group(0, &bind, &[]);
        let groups = (n_lanes as u32).div_ceil(256);
        pass.dispatch_workgroups(groups, 1, 1);
    }
    enc.copy_buffer_to_buffer(&out_buf, 0, &read_buf, 0, out_bytes);
    gpu.queue.submit([enc.finish()]);

    let slice = read_buf.slice(..);
    slice.map_async(wgpu::MapMode::Read, |_| {});
    dev.poll(wgpu::Maintain::Wait);
    let data = slice.get_mapped_range();
    let out: Vec<u32> = bytemuck::cast_slice(&data).to_vec();
    drop(data);
    read_buf.unmap();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bfv_lean::{fold, FOLD_MODULI};

    /// A full-shape fresh-fold ciphertext (2 polys × 3 RNS rows × degree-4096) of deterministic canonical
    /// residues — the exact shape the fold path produces, so the GPU exercises the real lane count.
    fn synth_ct(seed: u64, plain_bound: u64) -> LeanCiphertext {
        let deg = 4096usize;
        let mut s = seed;
        let mut next = || {
            s = s
                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                .rotate_left(17)
                .wrapping_add(1);
            s
        };
        let polys = (0..2)
            .map(|_| RnsPoly {
                rows: FOLD_MODULI
                    .iter()
                    .map(|&q| (0..deg).map(|_| next() % q).collect())
                    .collect(),
            })
            .collect();
        LeanCiphertext {
            moduli: FOLD_MODULI.to_vec(),
            degree: deg,
            level: 0,
            variable_time: false,
            polys,
            plain_bound,
        }
    }

    /// THE TOOTH: the GPU fold must equal the oracle-validated CPU `fold` bit-for-bit. If the shader's
    /// u64-via-u32 modular add is wrong in ANY coefficient lane, this diverges and goes RED — so it is its
    /// own bite (a broken modulus / carry / conditional-subtract fails here). On a headless runner with no
    /// wgpu adapter it SKIPS explicitly (never a silent pass).
    #[test]
    fn gpu_fold_matches_cpu_fold_bit_for_bit() {
        let cts: Vec<_> = (0..17).map(|i| synth_ct(i + 1, 3)).collect();
        let t = 1u64 << 20;
        let cpu = fold(&cts, t).expect("cpu fold");
        match fold_gpu(&cts, t) {
            Ok(gpu) => assert_eq!(
                gpu, cpu,
                "GPU fold diverged from the oracle-validated CPU fold — the shader is wrong"
            ),
            Err(BfvLeanError::GpuUnavailable) => {
                eprintln!("no wgpu adapter — GPU parity SKIPPED (headless runner)")
            }
            Err(e) => panic!("gpu fold error: {e}"),
        }
    }

    /// The wrap-budget gate is enforced GPU-side too (the same scalar refusal the CPU `fold` applies): a
    /// fold whose plaintext bounds could sum past t is refused BEFORE dispatch, never silently wrapped.
    #[test]
    fn gpu_fold_refuses_wrap_like_cpu() {
        let t = 1u64 << 20;
        // two ciphertexts whose bounds sum to exactly t → both CPU and GPU must refuse.
        let cts = [synth_ct(1, t - 1), synth_ct(2, 1)];
        assert!(matches!(
            fold(&cts, t),
            Err(BfvLeanError::WrapRefused { .. })
        ));
        assert!(matches!(
            fold_gpu(&cts, t),
            Err(BfvLeanError::WrapRefused { .. }) | Err(BfvLeanError::GpuUnavailable)
        ));
    }
}

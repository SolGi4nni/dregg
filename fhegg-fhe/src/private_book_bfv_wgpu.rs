//! Exact wgpu precomputation for the large public-coefficient block in the
//! private-book BFV Bulletproof relation.
//!
//! This is deliberately narrower than a "GPU Bulletproof prover". The pinned
//! zkcrypto fork hard-codes its Ristretto MSMs inside `Prover::prove` and
//! `InnerProductProof::create`; it exposes no backend trait. Replacing those
//! operations requires a fork-level Ristretto255 MSM seam (including 255-bit
//! limb arithmetic), not an fhegg callback.
//!
//! The relation code *does* own one large, independent operation before those
//! MSMs: 128 legal message polynomials are dotted with every transcript-derived
//! Rademacher row. At N4K4 this is 196,608 dots of length 4096, or 805,306,368
//! exact sign/add operations. [`precompute_signed_dots_wgpu`] batches that
//! operation in one portable WGSL dispatch. It uses only exact u64-via-u32
//! addition, returns i128 integers, and is parity-checked against the CPU
//! definition. The verifier remains on its original CPU path.

use std::sync::OnceLock;

/// Shape of one batched public message-table evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedDotShape {
    /// Ring degree (4096 for the fixed private-book relation).
    pub degree: usize,
    /// Number of RNS moduli (3 for the deployed fold set).
    pub modulus_count: usize,
    /// Number of legal private-order message polynomials (128 for N4K4).
    pub option_count: usize,
    /// Number of sign rows belonging to each modulus (128 rounds × 4 orders).
    pub sign_rows_per_modulus: usize,
}

impl SignedDotShape {
    fn sign_words(self) -> Option<usize> {
        self.degree.checked_add(31).map(|n| n / 32)
    }

    fn sign_rows(self) -> Option<usize> {
        self.modulus_count.checked_mul(self.sign_rows_per_modulus)
    }

    fn dot_count(self) -> Option<usize> {
        self.sign_rows()?.checked_mul(self.option_count)
    }

    fn message_count(self) -> Option<usize> {
        self.option_count
            .checked_mul(self.modulus_count)?
            .checked_mul(self.degree)
    }
}

struct GpuCtx {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    bind_group_layout: wgpu::BindGroupLayout,
    adapter_name: String,
    max_storage_bytes: u64,
}

enum GpuCtxState {
    Ready(GpuCtx),
    Unavailable(String),
}

fn gpu_ctx() -> &'static GpuCtxState {
    static CTX: OnceLock<GpuCtxState> = OnceLock::new();
    CTX.get_or_init(|| {
        let instance = wgpu::Instance::default();
        let Some(adapter) =
            pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                ..Default::default()
            }))
        else {
            return GpuCtxState::Unavailable("no wgpu adapter".to_owned());
        };
        let adapter_name = adapter.get_info().name;
        let adapter_limits = adapter.limits();
        let max_storage_bytes = adapter_limits
            .max_buffer_size
            .min(u64::from(adapter_limits.max_storage_buffer_binding_size));
        let requested_limits = adapter_limits.clone();
        let Ok((device, queue)) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("private-book-bfv-signed-dot"),
                required_features: wgpu::Features::empty(),
                required_limits: requested_limits,
                memory_hints: Default::default(),
            },
            None,
        )) else {
            return GpuCtxState::Unavailable(format!(
                "wgpu device request failed for {adapter_name}"
            ));
        };

        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("private_book_signed_dot.wgsl"),
            source: wgpu::ShaderSource::Wgsl(
                include_str!("shaders/private_book_signed_dot.wgsl").into(),
            ),
        });
        let bind_group_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("private-book-bfv-signed-dot-bindings"),
            entries: &[
                buffer_entry(0, wgpu::BufferBindingType::Uniform),
                buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: false }),
            ],
        });
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("private-book-bfv-signed-dot-layout"),
            bind_group_layouts: &[&bind_group_layout],
            push_constant_ranges: &[],
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("private-book-bfv-signed-dot-pipeline"),
            layout: Some(&pipeline_layout),
            module: &shader,
            entry_point: Some("main"),
            compilation_options: Default::default(),
            cache: None,
        });
        GpuCtxState::Ready(GpuCtx {
            device,
            queue,
            pipeline,
            bind_group_layout,
            adapter_name,
            max_storage_bytes,
        })
    })
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

/// Whether the private-book prover should use the exact wgpu precompute.
///
/// It is intentionally opt-in. `DREGG_PRIVATE_BOOK_BFV_WGPU=1`, `true`,
/// `yes`, or `required` requests it; a requested but unavailable GPU is an
/// error rather than a silently renamed CPU proof.
pub fn requested_by_environment() -> bool {
    std::env::var("DREGG_PRIVATE_BOOK_BFV_WGPU")
        .map(|value| {
            matches!(
                value.to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "required"
            )
        })
        .unwrap_or(false)
}

/// Return the adapter selected by the same context used for the batch kernel.
pub fn adapter_name() -> Result<&'static str, String> {
    match gpu_ctx() {
        GpuCtxState::Ready(ctx) => Ok(&ctx.adapter_name),
        GpuCtxState::Unavailable(error) => Err(error.clone()),
    }
}

/// Compute exact signed dots on the selected wgpu adapter.
///
/// `packed_signs` is `[sign_row][ceil(degree/32)]`, little-bit-order, where a
/// set bit means `+1` and a clear bit means `-1`. `messages` is
/// `[option][modulus][coefficient]` in u64s. Results are
/// `[sign_row][option]` as exact signed i128 integers.
pub fn precompute_signed_dots_wgpu(
    shape: SignedDotShape,
    packed_signs: &[u32],
    messages: &[u64],
) -> Result<Vec<i128>, String> {
    let sign_words = shape
        .sign_words()
        .ok_or_else(|| "signed-dot shape overflow".to_owned())?;
    let sign_rows = shape
        .sign_rows()
        .ok_or_else(|| "signed-dot shape overflow".to_owned())?;
    let dot_count = shape
        .dot_count()
        .ok_or_else(|| "signed-dot shape overflow".to_owned())?;
    let message_count = shape
        .message_count()
        .ok_or_else(|| "signed-dot shape overflow".to_owned())?;
    if shape.degree == 0
        || shape.modulus_count == 0
        || shape.option_count == 0
        || shape.sign_rows_per_modulus == 0
        || packed_signs.len() != sign_rows.saturating_mul(sign_words)
        || messages.len() != message_count
    {
        return Err("invalid signed-dot shape or buffer length".to_owned());
    }

    let to_u32 = |value: usize, name: &str| {
        u32::try_from(value).map_err(|_| format!("{name} exceeds wgpu u32 dimensions"))
    };
    let sign_rows_u32 = to_u32(sign_rows, "sign row count")?;
    let options_u32 = to_u32(shape.option_count, "option count")?;
    let degree_u32 = to_u32(shape.degree, "degree")?;
    let sign_words_u32 = to_u32(sign_words, "sign word count")?;
    let rows_per_modulus_u32 = to_u32(shape.sign_rows_per_modulus, "sign rows per modulus")?;
    let moduli_u32 = to_u32(shape.modulus_count, "modulus count")?;

    let ctx = match gpu_ctx() {
        GpuCtxState::Ready(ctx) => ctx,
        GpuCtxState::Unavailable(error) => return Err(error.clone()),
    };
    let limits = ctx.device.limits();
    if options_u32 > limits.max_compute_workgroups_per_dimension
        || sign_rows_u32 > limits.max_compute_workgroups_per_dimension
    {
        return Err("signed-dot dispatch exceeds adapter workgroup dimensions".to_owned());
    }

    let mut message_words = Vec::with_capacity(message_count.saturating_mul(2));
    for &value in messages {
        message_words.push(value as u32);
        message_words.push((value >> 32) as u32);
    }
    let output_words = dot_count
        .checked_mul(4)
        .ok_or_else(|| "signed-dot output length overflow".to_owned())?;
    let message_bytes = (message_words.len() as u64)
        .checked_mul(4)
        .ok_or_else(|| "signed-dot message byte length overflow".to_owned())?;
    let sign_bytes = (packed_signs.len() as u64)
        .checked_mul(4)
        .ok_or_else(|| "signed-dot sign byte length overflow".to_owned())?;
    let output_bytes = (output_words as u64)
        .checked_mul(4)
        .ok_or_else(|| "signed-dot output byte length overflow".to_owned())?;
    if [message_bytes, sign_bytes, output_bytes]
        .into_iter()
        .any(|bytes| bytes > ctx.max_storage_bytes)
    {
        return Err(format!(
            "signed-dot buffer exceeds {} adapter storage bytes",
            ctx.max_storage_bytes
        ));
    }

    use wgpu::util::DeviceExt;
    let meta = [
        sign_rows_u32,
        options_u32,
        degree_u32,
        sign_words_u32,
        rows_per_modulus_u32,
        moduli_u32,
        0,
        0,
    ];
    let meta_buffer = ctx
        .device
        .create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("private-book-bfv-signed-dot-meta"),
            contents: bytemuck::cast_slice(&meta),
            usage: wgpu::BufferUsages::UNIFORM,
        });
    let sign_buffer = ctx
        .device
        .create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("private-book-bfv-signed-dot-signs"),
            contents: bytemuck::cast_slice(packed_signs),
            usage: wgpu::BufferUsages::STORAGE,
        });
    let message_buffer = ctx
        .device
        .create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("private-book-bfv-signed-dot-messages"),
            contents: bytemuck::cast_slice(&message_words),
            usage: wgpu::BufferUsages::STORAGE,
        });
    let output_buffer = ctx.device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("private-book-bfv-signed-dot-output"),
        size: output_bytes,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let read_buffer = ctx.device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("private-book-bfv-signed-dot-readback"),
        size: output_bytes,
        usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
        mapped_at_creation: false,
    });
    let bind_group = ctx.device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("private-book-bfv-signed-dot-bind-group"),
        layout: &ctx.bind_group_layout,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: meta_buffer.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: sign_buffer.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: message_buffer.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 3,
                resource: output_buffer.as_entire_binding(),
            },
        ],
    });

    let mut encoder = ctx
        .device
        .create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("private-book-bfv-signed-dot-commands"),
        });
    {
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some("private-book-bfv-signed-dot-pass"),
            timestamp_writes: None,
        });
        pass.set_pipeline(&ctx.pipeline);
        pass.set_bind_group(0, &bind_group, &[]);
        pass.dispatch_workgroups(options_u32, sign_rows_u32, 1);
    }
    encoder.copy_buffer_to_buffer(&output_buffer, 0, &read_buffer, 0, output_bytes);
    ctx.queue.submit([encoder.finish()]);

    let slice = read_buffer.slice(..);
    slice.map_async(wgpu::MapMode::Read, |_| {});
    ctx.device.poll(wgpu::Maintain::Wait);
    let mapping = slice.get_mapped_range();
    let words: &[u32] = bytemuck::cast_slice(&mapping);
    if words.len() != output_words {
        return Err("signed-dot GPU readback length mismatch".to_owned());
    }
    let mut dots = Vec::with_capacity(dot_count);
    for limbs in words.chunks_exact(4) {
        let positive = u64::from(limbs[0]) | (u64::from(limbs[1]) << 32);
        let negative = u64::from(limbs[2]) | (u64::from(limbs[3]) << 32);
        dots.push(i128::from(positive) - i128::from(negative));
    }
    drop(mapping);
    read_buffer.unmap();
    Ok(dots)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cpu_dots(shape: SignedDotShape, signs: &[u32], messages: &[u64]) -> Vec<i128> {
        let words = shape.sign_words().unwrap();
        let rows = shape.sign_rows().unwrap();
        let mut out = Vec::with_capacity(rows * shape.option_count);
        for row in 0..rows {
            let modulus = row / shape.sign_rows_per_modulus;
            for option in 0..shape.option_count {
                let mut dot = 0i128;
                for coefficient in 0..shape.degree {
                    let positive =
                        signs[row * words + coefficient / 32] & (1 << (coefficient % 32)) != 0;
                    let value = messages
                        [(option * shape.modulus_count + modulus) * shape.degree + coefficient];
                    dot += if positive {
                        i128::from(value)
                    } else {
                        -i128::from(value)
                    };
                }
                out.push(dot);
            }
        }
        out
    }

    #[test]
    fn signed_dot_kernel_matches_exact_cpu_integer_definition() {
        let shape = SignedDotShape {
            degree: 513,
            modulus_count: 3,
            option_count: 11,
            sign_rows_per_modulus: 9,
        };
        let sign_words = shape.sign_words().unwrap();
        let sign_rows = shape.sign_rows().unwrap();
        let signs: Vec<u32> = (0..sign_rows * sign_words)
            .map(|i| {
                (i as u32)
                    .wrapping_mul(0x9e37_79b9)
                    .rotate_left((i % 31) as u32)
            })
            .collect();
        let messages: Vec<u64> = (0..shape.message_count().unwrap())
            .map(|i| {
                (i as u64)
                    .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    .rotate_left((i % 63) as u32)
                    % 0x1_ffff_e0001
            })
            .collect();
        let cpu = cpu_dots(shape, &signs, &messages);
        match precompute_signed_dots_wgpu(shape, &signs, &messages) {
            Ok(gpu) => assert_eq!(gpu, cpu),
            Err(error) if error.contains("no wgpu adapter") => {
                eprintln!("no wgpu adapter — exact signed-dot parity SKIPPED")
            }
            Err(error) => panic!("wgpu signed-dot precompute failed: {error}"),
        }
    }
}

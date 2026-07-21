//! Portable WebGPU arithmetic frontier for the TFHE programmable-bootstrap path.
//!
//! This module deliberately implements one primitive, not a programmable bootstrap:
//!
//! ```text
//! out = accumulator + sum_t lhs_t * rhs_t
//!       in (Z / 2^64 Z)[X] / (X^N + 1).
//! ```
//!
//! That batched negacyclic polynomial multiply-accumulate is the coefficient-domain
//! arithmetic reference beneath a GGSW x GLWE external product.  A complete TFHE
//! external product additionally needs signed gadget decomposition and a fast
//! Fourier/NTT representation; blind rotation additionally needs CMUX scheduling and
//! monomial rotations.  None of those are claimed here.  In particular, this module
//! is not yet connected to [`crate::fhe_clear`] and does not accelerate `FheUint32`
//! comparison by itself.
//!
//! The shader represents every torus coefficient as `(lo, hi)` `u32` limbs.  Its
//! 16-bit-split multiply retains exactly the low 64 bits, so the result is bit-for-bit
//! equal to Rust's wrapping `u64` arithmetic and tfhe-rs's
//! `polynomial_wrapping_add_mul_assign`.  The implementation is a deliberately simple
//! O(N^2) parity rung.  Replacing it with a subquadratic transform while preserving
//! this gate is the next performance step.

use std::fmt;
use std::sync::{mpsc, OnceLock};

const WORKGROUP_SIZE: u32 = 64;

/// Why the portable entry point used the bit-exact CPU implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TorusCpuFallbackReason {
    /// The process could not discover any adapter through wgpu.
    NoAdapter,
    /// An adapter existed but no device could be requested.
    DeviceRequestFailed(String),
    /// The adapter could not validate the fixed shader/pipeline.
    PipelineUnavailable(String),
    /// This valid input does not fit the selected adapter's storage/dispatch limits.
    ShapeExceedsAdapterLimits,
}

/// Which implementation produced a portable multiply-accumulate result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TorusMacBackend {
    Wgpu {
        adapter_name: String,
        backend: String,
    },
    /// The caller explicitly selected the deterministic CPU implementation.
    CpuOnly,
    CpuFallback(TorusCpuFallbackReason),
}

/// Backend-selection policy for deterministic tests and fail-closed GPU jobs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TorusMacPolicy {
    /// Prefer wgpu and visibly fall back only when the capability is unavailable.
    #[default]
    Auto,
    /// Do not initialize wgpu; execute the same bit-exact CPU reference directly.
    CpuOnly,
    /// Require real wgpu execution. Adapter/device/pipeline/limit absence is an error.
    RequireWgpu,
}

/// A bit-exact result plus an honest report of the backend that produced it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TorusMacResult {
    pub coefficients: Vec<u64>,
    pub backend: TorusMacBackend,
}

/// Refusals at the portable primitive boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TorusMacError {
    ZeroDegree,
    DegreeNotPowerOfTwo {
        degree: usize,
    },
    EmptyProductBatch,
    AccumulatorLength {
        expected: usize,
        actual: usize,
    },
    OperandLengthMismatch {
        lhs: usize,
        rhs: usize,
    },
    OperandLengthNotMultiple {
        len: usize,
        degree: usize,
    },
    AddressSpaceOverflow,
    WgpuRequired(TorusCpuFallbackReason),
    /// GPU execution failed after a device and supported shape were selected.
    /// This is not silently retried on CPU: doing so could conceal a broken shader
    /// or device-loss bug behind a green fallback.
    GpuExecution(String),
}

impl fmt::Display for TorusMacError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroDegree => write!(f, "torus polynomial degree must be nonzero"),
            Self::DegreeNotPowerOfTwo { degree } => write!(
                f,
                "torus polynomial degree {degree} is not a power of two (TFHE polynomial shape refused)"
            ),
            Self::EmptyProductBatch => {
                write!(f, "torus polynomial product batch must contain at least one pair")
            }
            Self::AccumulatorLength { expected, actual } => write!(
                f,
                "torus accumulator has {actual} coefficients; expected exactly {expected}"
            ),
            Self::OperandLengthMismatch { lhs, rhs } => write!(
                f,
                "torus product operands disagree in flattened length: lhs={lhs}, rhs={rhs}"
            ),
            Self::OperandLengthNotMultiple { len, degree } => write!(
                f,
                "flattened torus operand length {len} is not a multiple of degree {degree}"
            ),
            Self::AddressSpaceOverflow => write!(
                f,
                "torus polynomial shape exceeds the host/WebGPU addressable metadata range"
            ),
            Self::WgpuRequired(reason) => {
                write!(f, "torus wgpu execution was required but unavailable: {reason:?}")
            }
            Self::GpuExecution(error) => write!(f, "torus wgpu execution failed: {error}"),
        }
    }
}

impl std::error::Error for TorusMacError {}

#[derive(Clone, Copy)]
struct Shape {
    degree: usize,
    products: usize,
}

fn validate(
    accumulator: &[u64],
    lhs: &[u64],
    rhs: &[u64],
    degree: usize,
) -> Result<Shape, TorusMacError> {
    if degree == 0 {
        return Err(TorusMacError::ZeroDegree);
    }
    if !degree.is_power_of_two() {
        return Err(TorusMacError::DegreeNotPowerOfTwo { degree });
    }
    if accumulator.len() != degree {
        return Err(TorusMacError::AccumulatorLength {
            expected: degree,
            actual: accumulator.len(),
        });
    }
    if lhs.len() != rhs.len() {
        return Err(TorusMacError::OperandLengthMismatch {
            lhs: lhs.len(),
            rhs: rhs.len(),
        });
    }
    if lhs.is_empty() {
        return Err(TorusMacError::EmptyProductBatch);
    }
    if lhs.len() % degree != 0 {
        return Err(TorusMacError::OperandLengthNotMultiple {
            len: lhs.len(),
            degree,
        });
    }
    let products = lhs.len() / degree;
    let flattened = products
        .checked_mul(degree)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if flattened != lhs.len()
        || degree > u32::MAX as usize
        || products > u32::MAX as usize
        || flattened > u32::MAX as usize
    {
        return Err(TorusMacError::AddressSpaceOverflow);
    }
    Ok(Shape { degree, products })
}

/// Bit-exact CPU reference for the batched torus negacyclic MAC.
///
/// `lhs` and `rhs` each contain `products * degree` coefficients, with one
/// polynomial after another.  Products and accumulation wrap modulo 2^64;
/// polynomial reduction uses `X^degree = -1`.
pub fn torus_negacyclic_mac_cpu(
    accumulator: &[u64],
    lhs: &[u64],
    rhs: &[u64],
    degree: usize,
) -> Result<Vec<u64>, TorusMacError> {
    let shape = validate(accumulator, lhs, rhs, degree)?;
    Ok(cpu_validated(accumulator, lhs, rhs, shape))
}

fn cpu_validated(accumulator: &[u64], lhs: &[u64], rhs: &[u64], shape: Shape) -> Vec<u64> {
    let mut output = accumulator.to_vec();
    for product in 0..shape.products {
        let start = product * shape.degree;
        let lhs_poly = &lhs[start..start + shape.degree];
        let rhs_poly = &rhs[start..start + shape.degree];
        for (out_index, out) in output.iter_mut().enumerate() {
            let mut value = *out;
            for lhs_index in 0..shape.degree {
                let rhs_index = if lhs_index <= out_index {
                    out_index - lhs_index
                } else {
                    shape.degree + out_index - lhs_index
                };
                let term = lhs_poly[lhs_index].wrapping_mul(rhs_poly[rhs_index]);
                value = if lhs_index <= out_index {
                    value.wrapping_add(term)
                } else {
                    value.wrapping_sub(term)
                };
            }
            *out = value;
        }
    }
    output
}

/// Use the portable wgpu shader when an adapter and its limits permit it; use the
/// bit-exact CPU reference only for capability unavailability.
///
/// Once GPU execution begins, execution/validation failure is returned rather than
/// hidden by a CPU retry.  The returned backend makes every fallback visible.
pub fn torus_negacyclic_mac_portable(
    accumulator: &[u64],
    lhs: &[u64],
    rhs: &[u64],
    degree: usize,
) -> Result<TorusMacResult, TorusMacError> {
    torus_negacyclic_mac_with_policy(accumulator, lhs, rhs, degree, TorusMacPolicy::Auto)
}

/// Execute under an explicit backend policy.
///
/// This is the env-independent selection seam used by correctness matrices:
/// `CpuOnly` deterministically exercises the reference, while `RequireWgpu`
/// refuses to relabel a CPU result as GPU evidence.
pub fn torus_negacyclic_mac_with_policy(
    accumulator: &[u64],
    lhs: &[u64],
    rhs: &[u64],
    degree: usize,
    policy: TorusMacPolicy,
) -> Result<TorusMacResult, TorusMacError> {
    let shape = validate(accumulator, lhs, rhs, degree)?;
    if policy == TorusMacPolicy::CpuOnly {
        return Ok(TorusMacResult {
            coefficients: cpu_validated(accumulator, lhs, rhs, shape),
            backend: TorusMacBackend::CpuOnly,
        });
    }
    match gpu_context() {
        Ok(gpu) if gpu.supports(shape) => Ok(TorusMacResult {
            coefficients: gpu.run(accumulator, lhs, rhs, shape)?,
            backend: TorusMacBackend::Wgpu {
                adapter_name: gpu.adapter_name.clone(),
                backend: gpu.backend.clone(),
            },
        }),
        Ok(_) if policy == TorusMacPolicy::RequireWgpu => Err(TorusMacError::WgpuRequired(
            TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
        )),
        Ok(_) => Ok(TorusMacResult {
            coefficients: cpu_validated(accumulator, lhs, rhs, shape),
            backend: TorusMacBackend::CpuFallback(
                TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
            ),
        }),
        Err(reason) if policy == TorusMacPolicy::RequireWgpu => {
            Err(TorusMacError::WgpuRequired(reason))
        }
        Err(reason) => Ok(TorusMacResult {
            coefficients: cpu_validated(accumulator, lhs, rhs, shape),
            backend: TorusMacBackend::CpuFallback(reason),
        }),
    }
}

struct GpuContext {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    bind_group_layout: wgpu::BindGroupLayout,
    limits: wgpu::Limits,
    adapter_name: String,
    backend: String,
}

enum GpuAvailability {
    Ready(GpuContext),
    Unavailable(TorusCpuFallbackReason),
}

fn gpu_context() -> Result<&'static GpuContext, TorusCpuFallbackReason> {
    static GPU: OnceLock<GpuAvailability> = OnceLock::new();
    match GPU.get_or_init(init_gpu) {
        GpuAvailability::Ready(gpu) => Ok(gpu),
        GpuAvailability::Unavailable(reason) => Err(reason.clone()),
    }
}

fn init_gpu() -> GpuAvailability {
    let instance = wgpu::Instance::default();
    let Some(adapter) =
        pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: None,
            force_fallback_adapter: false,
        }))
    else {
        return GpuAvailability::Unavailable(TorusCpuFallbackReason::NoAdapter);
    };
    let limits = adapter.limits();
    let info = adapter.get_info();
    let device_request = pollster::block_on(adapter.request_device(
        &wgpu::DeviceDescriptor {
            label: Some("fhEgg torus negacyclic MAC"),
            required_features: wgpu::Features::empty(),
            required_limits: limits.clone(),
            memory_hints: Default::default(),
        },
        None,
    ));
    let (device, queue) = match device_request {
        Ok(pair) => pair,
        Err(error) => {
            return GpuAvailability::Unavailable(TorusCpuFallbackReason::DeviceRequestFailed(
                error.to_string(),
            ))
        }
    };

    device.push_error_scope(wgpu::ErrorFilter::Validation);
    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("torus_negacyclic_mac.wgsl"),
        source: wgpu::ShaderSource::Wgsl(include_str!("shaders/torus_negacyclic_mac.wgsl").into()),
    });
    let bind_group_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("torus negacyclic MAC bind-group layout"),
        entries: &[
            buffer_entry(0, wgpu::BufferBindingType::Uniform),
            buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: false }),
        ],
    });
    let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
        label: Some("torus negacyclic MAC pipeline layout"),
        bind_group_layouts: &[&bind_group_layout],
        push_constant_ranges: &[],
    });
    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: Some("torus negacyclic MAC pipeline"),
        layout: Some(&pipeline_layout),
        module: &shader,
        entry_point: Some("main"),
        compilation_options: Default::default(),
        cache: None,
    });
    if let Some(error) = pollster::block_on(device.pop_error_scope()) {
        return GpuAvailability::Unavailable(TorusCpuFallbackReason::PipelineUnavailable(
            error.to_string(),
        ));
    }

    GpuAvailability::Ready(GpuContext {
        device,
        queue,
        pipeline,
        bind_group_layout,
        limits,
        adapter_name: info.name,
        backend: format!("{:?}", info.backend),
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

impl GpuContext {
    fn supports(&self, shape: Shape) -> bool {
        let Some(flat_bytes) = shape
            .products
            .checked_mul(shape.degree)
            .and_then(|n| n.checked_mul(8))
            .and_then(|n| u64::try_from(n).ok())
        else {
            return false;
        };
        let Some(poly_bytes) = shape
            .degree
            .checked_mul(8)
            .and_then(|n| u64::try_from(n).ok())
        else {
            return false;
        };
        let binding_limit = u64::from(self.limits.max_storage_buffer_binding_size);
        let buffer_limit = self.limits.max_buffer_size;
        let workgroups = shape.degree.div_ceil(WORKGROUP_SIZE as usize);
        flat_bytes <= binding_limit
            && flat_bytes <= buffer_limit
            && poly_bytes <= binding_limit
            && poly_bytes <= buffer_limit
            && workgroups <= self.limits.max_compute_workgroups_per_dimension as usize
    }

    fn run(
        &self,
        accumulator: &[u64],
        lhs: &[u64],
        rhs: &[u64],
        shape: Shape,
    ) -> Result<Vec<u64>, TorusMacError> {
        use wgpu::util::DeviceExt;

        let lhs_limbs = to_limbs(lhs);
        let rhs_limbs = to_limbs(rhs);
        let accumulator_limbs = to_limbs(accumulator);
        let metadata = [shape.degree as u32, shape.products as u32, 0, 0];
        let metadata_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("torus MAC metadata"),
                contents: bytemuck::cast_slice(&metadata),
                usage: wgpu::BufferUsages::UNIFORM,
            });
        let lhs_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("torus MAC lhs"),
                contents: bytemuck::cast_slice(&lhs_limbs),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let rhs_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("torus MAC rhs"),
                contents: bytemuck::cast_slice(&rhs_limbs),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let accumulator_buffer =
            self.device
                .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                    label: Some("torus MAC accumulator"),
                    contents: bytemuck::cast_slice(&accumulator_limbs),
                    usage: wgpu::BufferUsages::STORAGE,
                });
        let output_bytes = (shape.degree * 8) as u64;
        let output_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("torus MAC output"),
            size: output_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let readback_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("torus MAC readback"),
            size: output_bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("torus MAC bind group"),
            layout: &self.bind_group_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: metadata_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: lhs_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: rhs_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: accumulator_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 4,
                    resource: output_buffer.as_entire_binding(),
                },
            ],
        });

        self.device.push_error_scope(wgpu::ErrorFilter::Validation);
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("torus MAC encoder"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("torus MAC pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups((shape.degree as u32).div_ceil(WORKGROUP_SIZE), 1, 1);
        }
        encoder.copy_buffer_to_buffer(&output_buffer, 0, &readback_buffer, 0, output_bytes);
        self.queue.submit(Some(encoder.finish()));

        let slice = readback_buffer.slice(..);
        let (sender, receiver) = mpsc::sync_channel(1);
        slice.map_async(wgpu::MapMode::Read, move |result| {
            let _ = sender.send(result);
        });
        self.device.poll(wgpu::Maintain::Wait);
        let map_result = receiver.recv().map_err(|error| {
            TorusMacError::GpuExecution(format!("readback callback disappeared: {error}"))
        })?;
        map_result.map_err(|error| TorusMacError::GpuExecution(error.to_string()))?;
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(TorusMacError::GpuExecution(error.to_string()));
        }

        let coefficients = {
            let mapped = slice.get_mapped_range();
            let limbs: &[u32] = bytemuck::cast_slice(&mapped);
            if limbs.len() != shape.degree * 2 {
                return Err(TorusMacError::GpuExecution(format!(
                    "readback returned {} limbs; expected {}",
                    limbs.len(),
                    shape.degree * 2
                )));
            }
            limbs
                .chunks_exact(2)
                .map(|pair| u64::from(pair[0]) | (u64::from(pair[1]) << 32))
                .collect()
        };
        readback_buffer.unmap();
        Ok(coefficients)
    }
}

fn to_limbs(values: &[u64]) -> Vec<u32> {
    let mut limbs = Vec::with_capacity(values.len() * 2);
    for &value in values {
        limbs.push(value as u32);
        limbs.push((value >> 32) as u32);
    }
    limbs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_every_malformed_shape_before_gpu_selection() {
        assert_eq!(
            torus_negacyclic_mac_cpu(&[], &[], &[], 0),
            Err(TorusMacError::ZeroDegree)
        );
        assert_eq!(
            torus_negacyclic_mac_cpu(&[0; 3], &[0; 3], &[0; 3], 3),
            Err(TorusMacError::DegreeNotPowerOfTwo { degree: 3 })
        );
        assert_eq!(
            torus_negacyclic_mac_cpu(&[0; 4], &[], &[], 4),
            Err(TorusMacError::EmptyProductBatch)
        );
        assert_eq!(
            torus_negacyclic_mac_cpu(&[0; 3], &[0; 4], &[0; 4], 4),
            Err(TorusMacError::AccumulatorLength {
                expected: 4,
                actual: 3
            })
        );
        assert_eq!(
            torus_negacyclic_mac_cpu(&[0; 4], &[0; 4], &[0; 8], 4),
            Err(TorusMacError::OperandLengthMismatch { lhs: 4, rhs: 8 })
        );
        assert_eq!(
            torus_negacyclic_mac_cpu(&[0; 4], &[0; 6], &[0; 6], 4),
            Err(TorusMacError::OperandLengthNotMultiple { len: 6, degree: 4 })
        );
    }

    #[test]
    fn negacyclic_sign_and_u64_wrap_are_exact() {
        let accumulator = [u64::MAX, 5, 7, 11];
        let lhs = [0, u64::MAX, 0, 0];
        let rhs = [0, 0, 0, 3];
        // (-1 * X) * (3 * X^3) = -3 X^4 = +3 modulo X^4 + 1.
        let output = torus_negacyclic_mac_cpu(&accumulator, &lhs, &rhs, 4).unwrap();
        assert_eq!(output, vec![2, 5, 7, 11]);
    }
}

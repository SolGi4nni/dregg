//! Portable WebGPU arithmetic frontier for the TFHE programmable-bootstrap path.
//!
//! This module implements two exact coefficient-domain rungs, not a programmable bootstrap:
//!
//! ```text
//! out = accumulator + sum_t lhs_t * rhs_t
//!       in (Z / 2^64 Z)[X] / (X^N + 1).
//! ```
//!
//! The second rung performs tfhe-rs-compatible signed gadget decomposition and the
//! complete standard-GGSW x GLWE external product, and exposes the corresponding
//! `ct0 + GGSW * (ct1 - ct0)` CMUX.  Both decomposition and convolution execute in
//! one GPU command submission.  It is a real private conditional primitive at the
//! deployed `N=2048, glwe_size=2, base_log=23, levels=1` shape.
//!
//! It is still deliberately coefficient-domain and O(N^2).  A production PBS needs
//! a transform-domain external product, blind-rotation scheduling, monomial rotation,
//! sample extraction, and keyswitching.  None of those are claimed here.  In
//! particular, this module is not yet connected to [`crate::fhe_clear`] and does not
//! accelerate `FheUint32` comparison by itself.
//!
//! The shader represents every torus coefficient as `(lo, hi)` `u32` limbs.  Its
//! 16-bit-split multiply retains exactly the low 64 bits, so the result is bit-for-bit
//! equal to Rust's wrapping `u64` arithmetic and tfhe-rs's
//! `polynomial_wrapping_add_mul_assign`.  The implementation is a deliberately simple
//! O(N^2) parity rung.  Replacing it with a subquadratic transform while preserving
//! this gate is the next performance step.

use std::fmt;
use std::sync::{mpsc, OnceLock};
use tfhe::core_crypto::algorithms::polynomial_algorithms::polynomial_wrapping_add_mul_assign;
use tfhe::core_crypto::entities::Polynomial;
use tfhe::core_crypto::prelude::{DecompositionBaseLog, DecompositionLevelCount, SignedDecomposer};

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

/// Native-torus shape for a standard-domain GGSW x GLWE external product.
///
/// `glwe_size` includes the body polynomial.  fhEgg's deployed tfhe-rs default
/// is `{ degree: 2048, glwe_size: 2, base_log: 23, level_count: 1 }`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TorusExternalProductParams {
    pub degree: usize,
    pub glwe_size: usize,
    pub decomposition_base_log: usize,
    pub decomposition_level_count: usize,
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
    ZeroGlweSize,
    ZeroDecompositionBaseLog,
    ZeroDecompositionLevelCount,
    /// The portable shader intentionally keeps each digit in one `u32` limb.
    /// Deployed TFHE uses 23; wider bases must use a separately validated shader.
    DecompositionBaseLogTooWide {
        base_log: usize,
    },
    DecompositionExhaustsTorus {
        base_log: usize,
        level_count: usize,
    },
    GlweLength {
        expected: usize,
        actual: usize,
    },
    GgswLength {
        expected: usize,
        actual: usize,
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
                write!(
                    f,
                    "torus polynomial product batch must contain at least one pair"
                )
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
            Self::ZeroGlweSize => write!(f, "TFHE GLWE size must be nonzero"),
            Self::ZeroDecompositionBaseLog => {
                write!(f, "TFHE gadget decomposition base log must be nonzero")
            }
            Self::ZeroDecompositionLevelCount => {
                write!(f, "TFHE gadget decomposition level count must be nonzero")
            }
            Self::DecompositionBaseLogTooWide { base_log } => write!(
                f,
                "TFHE gadget base log {base_log} exceeds the portable shader's 31-bit digit boundary"
            ),
            Self::DecompositionExhaustsTorus {
                base_log,
                level_count,
            } => write!(
                f,
                "TFHE gadget decomposition base_log={base_log}, levels={level_count} consumes all 64 torus bits"
            ),
            Self::GlweLength { expected, actual } => write!(
                f,
                "flattened GLWE ciphertext has {actual} coefficients; expected exactly {expected}"
            ),
            Self::GgswLength { expected, actual } => write!(
                f,
                "flattened standard GGSW ciphertext has {actual} coefficients; expected exactly {expected}"
            ),
            Self::AddressSpaceOverflow => write!(
                f,
                "torus polynomial shape exceeds the host/WebGPU addressable metadata range"
            ),
            Self::WgpuRequired(reason) => {
                write!(
                    f,
                    "torus wgpu execution was required but unavailable: {reason:?}"
                )
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
            ));
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

#[derive(Clone, Copy)]
struct ExternalShape {
    params: TorusExternalProductParams,
    glwe_coefficients: usize,
    ggsw_coefficients: usize,
    decomposed_coefficients: usize,
}

fn validate_external_product(
    accumulator: &[u64],
    glwe: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
) -> Result<ExternalShape, TorusMacError> {
    if params.degree == 0 {
        return Err(TorusMacError::ZeroDegree);
    }
    if !params.degree.is_power_of_two() {
        return Err(TorusMacError::DegreeNotPowerOfTwo {
            degree: params.degree,
        });
    }
    if params.glwe_size == 0 {
        return Err(TorusMacError::ZeroGlweSize);
    }
    if params.decomposition_base_log == 0 {
        return Err(TorusMacError::ZeroDecompositionBaseLog);
    }
    if params.decomposition_base_log > 31 {
        return Err(TorusMacError::DecompositionBaseLogTooWide {
            base_log: params.decomposition_base_log,
        });
    }
    if params.decomposition_level_count == 0 {
        return Err(TorusMacError::ZeroDecompositionLevelCount);
    }
    let represented_bits = params
        .decomposition_base_log
        .checked_mul(params.decomposition_level_count)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    // SignedDecomposer's native rounding needs at least one discarded bit.
    if represented_bits >= u64::BITS as usize {
        return Err(TorusMacError::DecompositionExhaustsTorus {
            base_log: params.decomposition_base_log,
            level_count: params.decomposition_level_count,
        });
    }

    let glwe_coefficients = params
        .glwe_size
        .checked_mul(params.degree)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    let ggsw_coefficients = params
        .decomposition_level_count
        .checked_mul(params.glwe_size)
        .and_then(|n| n.checked_mul(params.glwe_size))
        .and_then(|n| n.checked_mul(params.degree))
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    let decomposed_coefficients = params
        .decomposition_level_count
        .checked_mul(glwe_coefficients)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if accumulator.len() != glwe_coefficients {
        return Err(TorusMacError::AccumulatorLength {
            expected: glwe_coefficients,
            actual: accumulator.len(),
        });
    }
    if glwe.len() != glwe_coefficients {
        return Err(TorusMacError::GlweLength {
            expected: glwe_coefficients,
            actual: glwe.len(),
        });
    }
    if standard_ggsw.len() != ggsw_coefficients {
        return Err(TorusMacError::GgswLength {
            expected: ggsw_coefficients,
            actual: standard_ggsw.len(),
        });
    }
    if params.degree > u32::MAX as usize
        || params.glwe_size > u32::MAX as usize
        || params.decomposition_base_log > u32::MAX as usize
        || params.decomposition_level_count > u32::MAX as usize
        || glwe_coefficients > u32::MAX as usize
        || ggsw_coefficients > u32::MAX as usize
        || decomposed_coefficients > u32::MAX as usize
    {
        return Err(TorusMacError::AddressSpaceOverflow);
    }
    Ok(ExternalShape {
        params,
        glwe_coefficients,
        ggsw_coefficients,
        decomposed_coefficients,
    })
}

fn decompose_glwe_tfhe_oracle(glwe: &[u64], shape: ExternalShape) -> Vec<u64> {
    let decomposer = SignedDecomposer::<u64>::new(
        DecompositionBaseLog(shape.params.decomposition_base_log),
        DecompositionLevelCount(shape.params.decomposition_level_count),
    );
    let mut decomposed = vec![0u64; shape.decomposed_coefficients];
    for (coefficient, &value) in glwe.iter().enumerate() {
        for (level, term) in decomposer.decompose(value).enumerate() {
            decomposed[level * shape.glwe_coefficients + coefficient] = term.value();
        }
    }
    decomposed
}

fn external_product_cpu_validated(
    accumulator: &[u64],
    glwe: &[u64],
    standard_ggsw: &[u64],
    shape: ExternalShape,
) -> Vec<u64> {
    let decomposed = decompose_glwe_tfhe_oracle(glwe, shape);
    let p = shape.params;
    let mut output = accumulator.to_vec();
    for level in 0..p.decomposition_level_count {
        for row in 0..p.glwe_size {
            let digit_start = level * shape.glwe_coefficients + row * p.degree;
            let digit =
                Polynomial::from_container(&decomposed[digit_start..digit_start + p.degree]);
            for output_polynomial in 0..p.glwe_size {
                let ggsw_start =
                    ((level * p.glwe_size + row) * p.glwe_size + output_polynomial) * p.degree;
                let ggsw_polynomial =
                    Polynomial::from_container(&standard_ggsw[ggsw_start..ggsw_start + p.degree]);
                let output_start = output_polynomial * p.degree;
                let mut output_polynomial =
                    Polynomial::from_container(&mut output[output_start..output_start + p.degree]);
                polynomial_wrapping_add_mul_assign(
                    &mut output_polynomial,
                    &digit,
                    &ggsw_polynomial,
                );
            }
        }
    }
    output
}

/// Exact tfhe-rs CPU oracle for a native-torus standard-GGSW x GLWE external
/// product.  Storage is level-major, then GGSW row, then output polynomial.
pub fn torus_external_product_cpu(
    accumulator: &[u64],
    glwe: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
) -> Result<Vec<u64>, TorusMacError> {
    let shape = validate_external_product(accumulator, glwe, standard_ggsw, params)?;
    Ok(external_product_cpu_validated(
        accumulator,
        glwe,
        standard_ggsw,
        shape,
    ))
}

/// Execute a complete native-torus external product under an explicit backend
/// policy.  The wgpu path performs gadget decomposition and all GLWE output rows
/// in a single command submission.
pub fn torus_external_product_with_policy(
    accumulator: &[u64],
    glwe: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
    policy: TorusMacPolicy,
) -> Result<TorusMacResult, TorusMacError> {
    let shape = validate_external_product(accumulator, glwe, standard_ggsw, params)?;
    if policy == TorusMacPolicy::CpuOnly {
        return Ok(TorusMacResult {
            coefficients: external_product_cpu_validated(accumulator, glwe, standard_ggsw, shape),
            backend: TorusMacBackend::CpuOnly,
        });
    }
    match external_gpu_context() {
        Ok(gpu) if gpu.supports(shape) => Ok(TorusMacResult {
            coefficients: gpu.run(accumulator, glwe, standard_ggsw, shape)?,
            backend: TorusMacBackend::Wgpu {
                adapter_name: gpu.adapter_name.clone(),
                backend: gpu.backend.clone(),
            },
        }),
        Ok(_) if policy == TorusMacPolicy::RequireWgpu => Err(TorusMacError::WgpuRequired(
            TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
        )),
        Ok(_) => Ok(TorusMacResult {
            coefficients: external_product_cpu_validated(accumulator, glwe, standard_ggsw, shape),
            backend: TorusMacBackend::CpuFallback(
                TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
            ),
        }),
        Err(reason) if policy == TorusMacPolicy::RequireWgpu => {
            Err(TorusMacError::WgpuRequired(reason))
        }
        Err(reason) => Ok(TorusMacResult {
            coefficients: external_product_cpu_validated(accumulator, glwe, standard_ggsw, shape),
            backend: TorusMacBackend::CpuFallback(reason),
        }),
    }
}

/// Exact coefficient-domain CMUX oracle:
/// `ct0 + standard_ggsw * (ct1 - ct0)`.
pub fn torus_cmux_cpu(
    ct0: &[u64],
    ct1: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
) -> Result<Vec<u64>, TorusMacError> {
    let shape = validate_external_product(ct0, ct1, standard_ggsw, params)?;
    let difference: Vec<u64> = ct1
        .iter()
        .zip(ct0)
        .map(|(&then_coefficient, &else_coefficient)| {
            then_coefficient.wrapping_sub(else_coefficient)
        })
        .collect();
    Ok(external_product_cpu_validated(
        ct0,
        &difference,
        standard_ggsw,
        shape,
    ))
}

/// Portable coefficient-domain CMUX.  The subtraction is exact host torus
/// arithmetic; signed gadget decomposition and the external product execute on
/// the selected backend.
pub fn torus_cmux_with_policy(
    ct0: &[u64],
    ct1: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
    policy: TorusMacPolicy,
) -> Result<TorusMacResult, TorusMacError> {
    validate_external_product(ct0, ct1, standard_ggsw, params)?;
    let difference: Vec<u64> = ct1
        .iter()
        .zip(ct0)
        .map(|(&then_coefficient, &else_coefficient)| {
            then_coefficient.wrapping_sub(else_coefficient)
        })
        .collect();
    torus_external_product_with_policy(ct0, &difference, standard_ggsw, params, policy)
}

struct ExternalGpuContext {
    device: wgpu::Device,
    queue: wgpu::Queue,
    decomposition_pipeline: wgpu::ComputePipeline,
    external_product_pipeline: wgpu::ComputePipeline,
    bind_group_layout: wgpu::BindGroupLayout,
    limits: wgpu::Limits,
    adapter_name: String,
    backend: String,
}

enum ExternalGpuAvailability {
    Ready(ExternalGpuContext),
    Unavailable(TorusCpuFallbackReason),
}

fn external_gpu_context() -> Result<&'static ExternalGpuContext, TorusCpuFallbackReason> {
    static GPU: OnceLock<ExternalGpuAvailability> = OnceLock::new();
    match GPU.get_or_init(init_external_gpu) {
        ExternalGpuAvailability::Ready(gpu) => Ok(gpu),
        ExternalGpuAvailability::Unavailable(reason) => Err(reason.clone()),
    }
}

fn init_external_gpu() -> ExternalGpuAvailability {
    let instance = wgpu::Instance::default();
    let Some(adapter) =
        pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: None,
            force_fallback_adapter: false,
        }))
    else {
        return ExternalGpuAvailability::Unavailable(TorusCpuFallbackReason::NoAdapter);
    };
    let limits = adapter.limits();
    let info = adapter.get_info();
    let device_request = pollster::block_on(adapter.request_device(
        &wgpu::DeviceDescriptor {
            label: Some("fhEgg TFHE external product"),
            required_features: wgpu::Features::empty(),
            required_limits: limits.clone(),
            memory_hints: Default::default(),
        },
        None,
    ));
    let (device, queue) = match device_request {
        Ok(pair) => pair,
        Err(error) => {
            return ExternalGpuAvailability::Unavailable(
                TorusCpuFallbackReason::DeviceRequestFailed(error.to_string()),
            );
        }
    };

    device.push_error_scope(wgpu::ErrorFilter::Validation);
    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("torus_external_product.wgsl"),
        source: wgpu::ShaderSource::Wgsl(
            include_str!("shaders/torus_external_product.wgsl").into(),
        ),
    });
    let bind_group_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("TFHE external-product bind-group layout"),
        entries: &[
            buffer_entry(0, wgpu::BufferBindingType::Uniform),
            buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: false }),
            buffer_entry(5, wgpu::BufferBindingType::Storage { read_only: false }),
        ],
    });
    let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
        label: Some("TFHE external-product pipeline layout"),
        bind_group_layouts: &[&bind_group_layout],
        push_constant_ranges: &[],
    });
    let decomposition_pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: Some("TFHE signed gadget decomposition"),
        layout: Some(&pipeline_layout),
        module: &shader,
        entry_point: Some("decompose"),
        compilation_options: Default::default(),
        cache: None,
    });
    let external_product_pipeline =
        device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("TFHE standard GGSW external product"),
            layout: Some(&pipeline_layout),
            module: &shader,
            entry_point: Some("external_product"),
            compilation_options: Default::default(),
            cache: None,
        });
    if let Some(error) = pollster::block_on(device.pop_error_scope()) {
        return ExternalGpuAvailability::Unavailable(TorusCpuFallbackReason::PipelineUnavailable(
            error.to_string(),
        ));
    }

    ExternalGpuAvailability::Ready(ExternalGpuContext {
        device,
        queue,
        decomposition_pipeline,
        external_product_pipeline,
        bind_group_layout,
        limits,
        adapter_name: info.name,
        backend: format!("{:?}", info.backend),
    })
}

impl ExternalGpuContext {
    fn supports(&self, shape: ExternalShape) -> bool {
        let bytes = |coefficients: usize| {
            coefficients
                .checked_mul(8)
                .and_then(|n| u64::try_from(n).ok())
        };
        let Some(glwe_bytes) = bytes(shape.glwe_coefficients) else {
            return false;
        };
        let Some(ggsw_bytes) = bytes(shape.ggsw_coefficients) else {
            return false;
        };
        let Some(decomposed_bytes) = bytes(shape.decomposed_coefficients) else {
            return false;
        };
        let binding_limit = u64::from(self.limits.max_storage_buffer_binding_size);
        let buffer_limit = self.limits.max_buffer_size;
        let workgroups = shape.glwe_coefficients.div_ceil(WORKGROUP_SIZE as usize);
        [glwe_bytes, ggsw_bytes, decomposed_bytes]
            .into_iter()
            .all(|size| size <= binding_limit && size <= buffer_limit)
            && workgroups <= self.limits.max_compute_workgroups_per_dimension as usize
            && self.limits.max_storage_buffers_per_shader_stage >= 5
    }

    fn run(
        &self,
        accumulator: &[u64],
        glwe: &[u64],
        standard_ggsw: &[u64],
        shape: ExternalShape,
    ) -> Result<Vec<u64>, TorusMacError> {
        use wgpu::util::DeviceExt;

        let glwe_limbs = to_limbs(glwe);
        let ggsw_limbs = to_limbs(standard_ggsw);
        let accumulator_limbs = to_limbs(accumulator);
        let p = shape.params;
        let metadata = [
            p.degree as u32,
            p.glwe_size as u32,
            p.decomposition_base_log as u32,
            p.decomposition_level_count as u32,
        ];
        let metadata_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE external-product metadata"),
                contents: bytemuck::cast_slice(&metadata),
                usage: wgpu::BufferUsages::UNIFORM,
            });
        let glwe_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE external-product GLWE"),
                contents: bytemuck::cast_slice(&glwe_limbs),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let ggsw_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE external-product standard GGSW"),
                contents: bytemuck::cast_slice(&ggsw_limbs),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let accumulator_buffer =
            self.device
                .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                    label: Some("TFHE external-product accumulator"),
                    contents: bytemuck::cast_slice(&accumulator_limbs),
                    usage: wgpu::BufferUsages::STORAGE,
                });
        let decomposed_bytes = (shape.decomposed_coefficients * 8) as u64;
        let decomposed_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE signed gadget digits"),
            size: decomposed_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let output_bytes = (shape.glwe_coefficients * 8) as u64;
        let output_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE external-product output"),
            size: output_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let readback_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE external-product readback"),
            size: output_bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("TFHE external-product bind group"),
            layout: &self.bind_group_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: metadata_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: glwe_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: ggsw_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: accumulator_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 4,
                    resource: decomposed_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 5,
                    resource: output_buffer.as_entire_binding(),
                },
            ],
        });

        self.device.push_error_scope(wgpu::ErrorFilter::Validation);
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("TFHE external-product encoder"),
            });
        let workgroups = (shape.glwe_coefficients as u32).div_ceil(WORKGROUP_SIZE);
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("TFHE signed gadget-decomposition pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.decomposition_pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups(workgroups, 1, 1);
        }
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("TFHE external-product pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.external_product_pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups(workgroups, 1, 1);
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
            TorusMacError::GpuExecution(format!(
                "external-product readback callback disappeared: {error}"
            ))
        })?;
        map_result.map_err(|error| TorusMacError::GpuExecution(error.to_string()))?;
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(TorusMacError::GpuExecution(error.to_string()));
        }

        let coefficients = {
            let mapped = slice.get_mapped_range();
            let limbs: &[u32] = bytemuck::cast_slice(&mapped);
            if limbs.len() != shape.glwe_coefficients * 2 {
                return Err(TorusMacError::GpuExecution(format!(
                    "external-product readback returned {} limbs; expected {}",
                    limbs.len(),
                    shape.glwe_coefficients * 2
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

    #[test]
    fn external_product_refuses_hostile_parameters_before_gpu_selection() {
        let valid = TorusExternalProductParams {
            degree: 4,
            glwe_size: 2,
            decomposition_base_log: 4,
            decomposition_level_count: 2,
        };
        let accumulator = [0u64; 8];
        let glwe = [0u64; 8];
        let ggsw = [0u64; 32];

        let mutate = |degree, glwe_size, decomposition_base_log, decomposition_level_count| {
            TorusExternalProductParams {
                degree,
                glwe_size,
                decomposition_base_log,
                decomposition_level_count,
            }
        };
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe, &ggsw, mutate(0, 2, 4, 2)),
            Err(TorusMacError::ZeroDegree)
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe, &ggsw, mutate(3, 2, 4, 2)),
            Err(TorusMacError::DegreeNotPowerOfTwo { degree: 3 })
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe, &ggsw, mutate(4, 0, 4, 2)),
            Err(TorusMacError::ZeroGlweSize)
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe, &ggsw, mutate(4, 2, 0, 2)),
            Err(TorusMacError::ZeroDecompositionBaseLog)
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe, &ggsw, mutate(4, 2, 32, 1)),
            Err(TorusMacError::DecompositionBaseLogTooWide { base_log: 32 })
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe, &ggsw, mutate(4, 2, 4, 0)),
            Err(TorusMacError::ZeroDecompositionLevelCount)
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe, &ggsw, mutate(4, 2, 16, 4)),
            Err(TorusMacError::DecompositionExhaustsTorus {
                base_log: 16,
                level_count: 4
            })
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator[..7], &glwe, &ggsw, valid),
            Err(TorusMacError::AccumulatorLength {
                expected: 8,
                actual: 7
            })
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe[..7], &ggsw, valid),
            Err(TorusMacError::GlweLength {
                expected: 8,
                actual: 7
            })
        );
        assert_eq!(
            torus_external_product_cpu(&accumulator, &glwe, &ggsw[..31], valid),
            Err(TorusMacError::GgswLength {
                expected: 32,
                actual: 31
            })
        );
    }

    #[test]
    fn coefficient_cmux_selects_representable_then_value() {
        let params = TorusExternalProductParams {
            degree: 4,
            glwe_size: 2,
            decomposition_base_log: 4,
            decomposition_level_count: 2,
        };
        // Every coefficient is exactly representable by the 8 gadget bits.
        let scale = 1u64 << 56;
        let ct0 = [
            scale,
            2 * scale,
            3 * scale,
            4 * scale,
            5 * scale,
            6 * scale,
            7 * scale,
            0,
        ];
        let ct1 = [
            7 * scale,
            0,
            scale,
            2 * scale,
            3 * scale,
            4 * scale,
            5 * scale,
            6 * scale,
        ];
        let mut selector_one = vec![0u64; 32];
        // Standard GGSW identity gadget: diagonal constant polynomials carry
        // q/B^level. Storage level 0 is decomposition level 2, then level 1.
        for storage_level in 0..2 {
            let decomposition_level = 2 - storage_level;
            let gadget = 1u64 << (64 - 4 * decomposition_level);
            for diagonal in 0..2 {
                let polynomial = ((storage_level * 2 + diagonal) * 2 + diagonal) * 4;
                selector_one[polynomial] = gadget;
            }
        }
        let selected = torus_cmux_cpu(&ct0, &ct1, &selector_one, params).unwrap();
        assert_eq!(selected, ct1);
        let selected = torus_cmux_cpu(&ct0, &ct1, &[0u64; 32], params).unwrap();
        assert_eq!(selected, ct0);
    }
}

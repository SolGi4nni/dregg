//! Portable WebGPU arithmetic frontier for the TFHE programmable-bootstrap path.
//!
//! This module implements exact portable rungs toward a programmable bootstrap:
//!
//! ```text
//! out = accumulator + sum_t lhs_t * rhs_t
//!       in (Z / 2^64 Z)[X] / (X^N + 1).
//! ```
//!
//! The external-product rung performs tfhe-rs-compatible signed gadget decomposition and the
//! complete standard-GGSW x GLWE external product, and exposes the corresponding
//! `ct0 + GGSW * (ct1 - ct0)` CMUX.  An exact four-prime RNS-NTT route supplies the
//! subquadratic single-CMUX path.
//!
//! The chained rung implements tfhe-rs's native modulus switch, initial `LUT / X^b`,
//! and every dependent `CMUX(BSK_i, acc, acc * X^a_i)` with two device-resident
//! accumulator buffers and one resident standard bootstrapping-key buffer.  The
//! complete chain uses one command submission and one final readback.  Its current
//! external-product stage is deliberately coefficient-domain; moving CRT and gadget
//! decomposition fully onto-device is required before the RNS-NTT carrier can remain
//! resident across the dependency chain.
//!
//! The PBS-shaped rung fuses degree-zero GLWE sample extraction and an exact standard
//! native-torus LWE key switch after device-resident blind rotation, so only the
//! post-key-switch LWE ciphertext is read back. A dense gate now executes all 918
//! deployed CMUX steps with genuine noisy GGSWs and a real encrypted LWE input.
//! Reusable plans retain the full BSK/KSK; bounded command chunks retain both keys
//! and accumulator on-device. The exact transform plan additionally retains all
//! four-prime BSK spectra and performs inverse/centered CRT on-device. Default
//! shortint key-order integration and the [`crate::fhe_clear`] / `FheUint32` seam
//! remain.
//!
//! The shader represents every torus coefficient as `(lo, hi)` `u32` limbs.  Its
//! 16-bit-split multiply retains exactly the low 64 bits, so the result is bit-for-bit
//! equal to Rust's wrapping `u64` arithmetic and tfhe-rs's
//! `polynomial_wrapping_add_mul_assign`.  The implementation is a deliberately simple
//! O(N^2) authority rung retained beside the exact transform and chained gates.

use ethnum::I256;
use std::fmt;
use std::sync::{mpsc, OnceLock};
use tfhe::core_crypto::algorithms::polynomial_algorithms::polynomial_wrapping_add_mul_assign;
use tfhe::core_crypto::entities::Polynomial;
use tfhe::core_crypto::prelude::{DecompositionBaseLog, DecompositionLevelCount, SignedDecomposer};

use crate::tfhe_blind_rotation_ntt_wgpu::{
    prepare as prepare_transform_pbs_gpu, run as transform_pbs_gpu,
    run_bootstrap_only as transform_bootstrap_gpu,
    run_scalar_gt_chain as transform_scalar_gt_chain_gpu, PreparedTransformPbsGpuKeys,
    TransformPbsGpuError,
};
use crate::tfhe_blind_rotation_wgpu::{
    prepare_extract_keyswitch as prepare_pbs_extract_keyswitch_gpu, run as blind_rotation_gpu,
    run_extract_keyswitch as pbs_extract_keyswitch_gpu,
    run_extract_keyswitch_prepared as pbs_extract_keyswitch_prepared_gpu, BlindRotationGpuError,
    PreparedPbsGpuKeys,
};
use crate::tfhe_ntt_wgpu::{multiply_signed_batch, NttBatchError, TORUS_NTT_MODULI};

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
        algorithm: TorusWgpuAlgorithm,
    },
    /// The caller explicitly selected the deterministic CPU implementation.
    CpuOnly,
    CpuFallback(TorusCpuFallbackReason),
}

/// The arithmetic route that actually ran on the portable GPU.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TorusWgpuAlgorithm {
    /// Direct, bit-exact coefficient convolution.  This is the small-shape
    /// oracle and remains useful below the transform crossover.
    CoefficientDomain,
    /// Exact negacyclic RNS NTT under four primes, followed by a bounded CRT
    /// reconstruction of the native 64-bit torus coefficient.
    ExactRnsNtt,
    /// A complete exact blind-rotation chain whose accumulator and standard
    /// bootstrapping key stay device-resident until one final readback.
    ExactDeviceResidentBlindRotation,
    /// Blind rotation, degree-zero sample extraction, and native-torus LWE key
    /// switch with device-resident intermediates and one final readback.
    ExactDeviceResidentPbsExtractKeyswitch,
    /// Dense blind rotation with a one-time four-prime BSK transform, resident
    /// digit/product spectra, exact GPU inverse/centered CRT, and one final
    /// post-key-switch readback.
    ExactTransformResidentPbs,
}

/// Algorithm selection for the complete standard-GGSW external product.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TorusExternalProductMode {
    /// Use the exact RNS-NTT route when its CRT range and adapter are sufficient;
    /// otherwise retain the coefficient-domain GPU path.
    #[default]
    Auto,
    /// Force the original quadratic GPU kernel (or the ordinary labelled CPU
    /// capability fallback selected by [`TorusMacPolicy`]).
    CoefficientDomain,
    /// Require the exact transform route.  It never silently relabels the
    /// coefficient kernel as an NTT result.
    ExactRnsNtt,
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

/// Native-torus standard LWE key-switch shape appended to blind rotation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TorusKeyswitchParams {
    pub output_lwe_dimension: usize,
    pub decomposition_base_log: usize,
    pub decomposition_level_count: usize,
}

/// Exact GPU-resident BSK/KSK plan for repeated PBS-shaped calls.
///
/// Construction validates both host keys, uploads each exactly once, and binds
/// the resulting buffers to their blind-mask, GLWE, and key-switch dimensions.
/// Execution still creates per-ciphertext accumulator/output buffers; the large
/// immutable evaluation keys and the shared device/pipelines are retained.
pub struct TorusPbsWgpuPlan {
    prepared: PreparedPbsGpuKeys,
    blind_mask_dimension: usize,
    external_params: TorusExternalProductParams,
    keyswitch_params: TorusKeyswitchParams,
}

/// Deployed exact PBS plan whose complete standard BSK is retained in
/// four-prime NTT form. The accumulator and transform scratch remain on-device
/// across every dependent CMUX; only the final post-key-switch LWE is read back.
pub struct TorusPbsTransformWgpuPlan {
    prepared: PreparedTransformPbsGpuKeys,
    external_params: TorusExternalProductParams,
    keyswitch_params: TorusKeyswitchParams,
}

impl fmt::Debug for TorusPbsTransformWgpuPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TorusPbsTransformWgpuPlan")
            .field("blind_mask_dimension", &self.prepared.blind_mask_dimension)
            .field("external_params", &self.external_params)
            .field("keyswitch_params", &self.keyswitch_params)
            .field("adapter", &self.prepared.adapter)
            .field("backend", &self.prepared.backend)
            .finish_non_exhaustive()
    }
}

impl fmt::Debug for TorusPbsWgpuPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TorusPbsWgpuPlan")
            .field("blind_mask_dimension", &self.blind_mask_dimension)
            .field("external_params", &self.external_params)
            .field("keyswitch_params", &self.keyswitch_params)
            .field("adapter", &self.prepared.adapter)
            .field("backend", &self.prepared.backend)
            .finish_non_exhaustive()
    }
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
    EmptyBlindRotationMask,
    BlindRotationKeyLength {
        expected: usize,
        actual: usize,
    },
    BlindRotationMaskLength {
        expected: usize,
        actual: usize,
    },
    ZeroKeyswitchInputDimension,
    ZeroKeyswitchOutputDimension,
    KeyswitchKeyLength {
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
            Self::EmptyBlindRotationMask => {
                write!(f, "TFHE blind rotation requires a nonempty LWE mask")
            }
            Self::BlindRotationKeyLength { expected, actual } => write!(
                f,
                "flattened standard bootstrapping key has {actual} coefficients; expected exactly {expected}"
            ),
            Self::BlindRotationMaskLength { expected, actual } => write!(
                f,
                "blind-rotation mask has {actual} coefficients; prepared plan expects exactly {expected}"
            ),
            Self::ZeroKeyswitchInputDimension => write!(
                f,
                "sample extraction produced a zero-dimensional LWE mask; GLWE size must include a mask polynomial"
            ),
            Self::ZeroKeyswitchOutputDimension => {
                write!(f, "TFHE key switch requires a nonzero output LWE dimension")
            }
            Self::KeyswitchKeyLength { expected, actual } => write!(
                f,
                "flattened standard LWE keyswitch key has {actual} coefficients; expected exactly {expected}"
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
                algorithm: TorusWgpuAlgorithm::CoefficientDomain,
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

fn validate_external_product_shape(
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

fn validate_external_product(
    accumulator: &[u64],
    glwe: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
) -> Result<ExternalShape, TorusMacError> {
    let shape = validate_external_product_shape(params)?;
    if accumulator.len() != shape.glwe_coefficients {
        return Err(TorusMacError::AccumulatorLength {
            expected: shape.glwe_coefficients,
            actual: accumulator.len(),
        });
    }
    if glwe.len() != shape.glwe_coefficients {
        return Err(TorusMacError::GlweLength {
            expected: shape.glwe_coefficients,
            actual: glwe.len(),
        });
    }
    if standard_ggsw.len() != shape.ggsw_coefficients {
        return Err(TorusMacError::GgswLength {
            expected: shape.ggsw_coefficients,
            actual: standard_ggsw.len(),
        });
    }
    Ok(shape)
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

fn mod_pow_u64(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut output = 1u64;
    while exponent != 0 {
        if exponent & 1 != 0 {
            output = ((u128::from(output) * u128::from(base)) % u128::from(modulus)) as u64;
        }
        exponent >>= 1;
        if exponent != 0 {
            base = ((u128::from(base) * u128::from(base)) % u128::from(modulus)) as u64;
        }
    }
    output
}

struct CrtPlan {
    modulus: I256,
    terms: [I256; TORUS_NTT_MODULI.len()],
}

impl CrtPlan {
    fn new() -> Self {
        let modulus = TORUS_NTT_MODULI
            .iter()
            .fold(I256::ONE, |product, &q| product * I256::from(q));
        let terms = std::array::from_fn(|row| {
            let q = TORUS_NTT_MODULI[row];
            let partial = modulus / I256::from(q);
            let partial_mod_q = (partial % I256::from(q)).as_u64();
            let inverse = mod_pow_u64(partial_mod_q, q - 2, q);
            partial * I256::from(inverse)
        });
        Self { modulus, terms }
    }

    fn reconstruct_signed(&self, residues: [u64; TORUS_NTT_MODULI.len()]) -> I256 {
        let mut value = I256::ZERO;
        for (residue, term) in residues.into_iter().zip(self.terms) {
            value += I256::from(residue) * term;
        }
        value %= self.modulus;
        if value > self.modulus / I256::from(2u8) {
            value -= self.modulus;
        }
        value
    }
}

/// The four fixed RNS primes carry about 120 bits.  The transform is exact
/// only when their centered product uniquely contains the worst-case signed
/// convolution before reduction modulo 2^64.  This guard is deliberately
/// conservative: standard-GGSW coefficients are centered in [-2^63, 2^63),
/// gadget digits in [-2^(b-1), 2^(b-1)), and one output sums N*k*L terms.
fn exact_ntt_range_supported(shape: ExternalShape) -> bool {
    let p = shape.params;
    if p.degree < 8 || p.degree > 4096 {
        return false;
    }
    let Some(root_order) = p.degree.checked_mul(2).and_then(|n| u64::try_from(n).ok()) else {
        return false;
    };
    if TORUS_NTT_MODULI.iter().any(|q| (q - 1) % root_order != 0) {
        return false;
    }
    let Some(term_count) = p
        .degree
        .checked_mul(p.glwe_size)
        .and_then(|n| n.checked_mul(p.decomposition_level_count))
    else {
        return false;
    };
    let Ok(term_count) = u64::try_from(term_count) else {
        return false;
    };
    let Some(max_digit) = I256::ONE.checked_shl((p.decomposition_base_log - 1) as u32) else {
        return false;
    };
    let max_centered_torus = I256::ONE << 63;
    let Some(bound) = I256::from(term_count)
        .checked_mul(max_digit)
        .and_then(|n| n.checked_mul(max_centered_torus))
    else {
        return false;
    };
    let crt_modulus = TORUS_NTT_MODULI
        .iter()
        .fold(I256::ONE, |product, &q| product * I256::from(q));
    bound < crt_modulus / I256::from(2u8)
}

enum NttExternalProduct {
    Executed {
        coefficients: Vec<u64>,
        adapter: String,
        backend: String,
    },
    Unavailable,
}

fn external_product_ntt_gpu(
    accumulator: &[u64],
    glwe: &[u64],
    standard_ggsw: &[u64],
    shape: ExternalShape,
) -> Result<NttExternalProduct, TorusMacError> {
    if !exact_ntt_range_supported(shape) {
        return Ok(NttExternalProduct::Unavailable);
    }
    let p = shape.params;
    let decomposed = decompose_glwe_tfhe_oracle(glwe, shape);
    let mut lhs = Vec::with_capacity(p.decomposition_level_count * p.glwe_size * p.glwe_size);
    let mut rhs = Vec::with_capacity(lhs.capacity());
    let mut output_polynomials = Vec::with_capacity(lhs.capacity());
    for level in 0..p.decomposition_level_count {
        for row in 0..p.glwe_size {
            let digit_start = level * shape.glwe_coefficients + row * p.degree;
            let digit = decomposed[digit_start..digit_start + p.degree]
                .iter()
                .map(|&value| value as i64)
                .collect::<Vec<_>>();
            for output_polynomial in 0..p.glwe_size {
                let ggsw_start =
                    ((level * p.glwe_size + row) * p.glwe_size + output_polynomial) * p.degree;
                lhs.push(digit.clone());
                rhs.push(
                    standard_ggsw[ggsw_start..ggsw_start + p.degree]
                        .iter()
                        .map(|&value| value as i64)
                        .collect(),
                );
                output_polynomials.push(output_polynomial);
            }
        }
    }

    let batch = match multiply_signed_batch(&lhs, &rhs, p.degree) {
        Ok(batch) => batch,
        Err(NttBatchError::Unavailable) => return Ok(NttExternalProduct::Unavailable),
        Err(NttBatchError::Execution(error)) => {
            return Err(TorusMacError::GpuExecution(error));
        }
    };

    let crt = CrtPlan::new();
    let mut coefficients = accumulator.to_vec();
    for output_polynomial in 0..p.glwe_size {
        for coefficient in 0..p.degree {
            let mut residues = [0u64; TORUS_NTT_MODULI.len()];
            for (product, &product_output) in batch.residues.iter().zip(&output_polynomials) {
                if product_output != output_polynomial {
                    continue;
                }
                for (row, &modulus) in TORUS_NTT_MODULI.iter().enumerate() {
                    let sum = residues[row] + product[row][coefficient];
                    residues[row] = if sum >= modulus { sum - modulus } else { sum };
                }
            }
            let reconstructed = crt.reconstruct_signed(residues);
            let index = output_polynomial * p.degree + coefficient;
            coefficients[index] = coefficients[index].wrapping_add(reconstructed.as_u64());
        }
    }
    Ok(NttExternalProduct::Executed {
        coefficients,
        adapter: batch.adapter,
        backend: batch.backend,
    })
}

/// Execute a complete native-torus external product under an explicit backend
/// policy.  The wgpu path performs gadget decomposition and all GLWE output rows
/// in a single command submission on the coefficient route.  The exact RNS-NTT
/// route uses one retained portable GPU context and bounded CRT reconstruction.
pub fn torus_external_product_with_policy(
    accumulator: &[u64],
    glwe: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
    policy: TorusMacPolicy,
) -> Result<TorusMacResult, TorusMacError> {
    torus_external_product_with_mode(
        accumulator,
        glwe,
        standard_ggsw,
        params,
        policy,
        TorusExternalProductMode::Auto,
    )
}

/// Execute a complete external product with an explicit arithmetic algorithm.
/// This is the qualification seam used to measure the transform crossover
/// against the frozen coefficient-domain oracle on the same adapter.
pub fn torus_external_product_with_mode(
    accumulator: &[u64],
    glwe: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
    policy: TorusMacPolicy,
    mode: TorusExternalProductMode,
) -> Result<TorusMacResult, TorusMacError> {
    let shape = validate_external_product(accumulator, glwe, standard_ggsw, params)?;
    if policy == TorusMacPolicy::CpuOnly {
        return Ok(TorusMacResult {
            coefficients: external_product_cpu_validated(accumulator, glwe, standard_ggsw, shape),
            backend: TorusMacBackend::CpuOnly,
        });
    }
    let try_ntt = mode == TorusExternalProductMode::ExactRnsNtt
        || (mode == TorusExternalProductMode::Auto && params.degree >= 2048);
    if try_ntt {
        match external_product_ntt_gpu(accumulator, glwe, standard_ggsw, shape)? {
            NttExternalProduct::Executed {
                coefficients,
                adapter,
                backend,
            } => {
                return Ok(TorusMacResult {
                    coefficients,
                    backend: TorusMacBackend::Wgpu {
                        adapter_name: adapter,
                        backend,
                        algorithm: TorusWgpuAlgorithm::ExactRnsNtt,
                    },
                });
            }
            NttExternalProduct::Unavailable if mode == TorusExternalProductMode::ExactRnsNtt => {
                if policy == TorusMacPolicy::RequireWgpu {
                    return Err(TorusMacError::WgpuRequired(
                        TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
                    ));
                }
                return Ok(TorusMacResult {
                    coefficients: external_product_cpu_validated(
                        accumulator,
                        glwe,
                        standard_ggsw,
                        shape,
                    ),
                    backend: TorusMacBackend::CpuFallback(
                        TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
                    ),
                });
            }
            NttExternalProduct::Unavailable => {}
        }
    }
    match external_gpu_context() {
        Ok(gpu) if gpu.supports(shape) => Ok(TorusMacResult {
            coefficients: gpu.run(accumulator, glwe, standard_ggsw, shape)?,
            backend: TorusMacBackend::Wgpu {
                adapter_name: gpu.adapter_name.clone(),
                backend: gpu.backend.clone(),
                algorithm: TorusWgpuAlgorithm::CoefficientDomain,
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
    torus_cmux_with_mode(
        ct0,
        ct1,
        standard_ggsw,
        params,
        policy,
        TorusExternalProductMode::Auto,
    )
}

/// CMUX with an explicit external-product algorithm, used by the same-device
/// crossover and hostile differential gates.
pub fn torus_cmux_with_mode(
    ct0: &[u64],
    ct1: &[u64],
    standard_ggsw: &[u64],
    params: TorusExternalProductParams,
    policy: TorusMacPolicy,
    mode: TorusExternalProductMode,
) -> Result<TorusMacResult, TorusMacError> {
    validate_external_product(ct0, ct1, standard_ggsw, params)?;
    let difference: Vec<u64> = ct1
        .iter()
        .zip(ct0)
        .map(|(&then_coefficient, &else_coefficient)| {
            then_coefficient.wrapping_sub(else_coefficient)
        })
        .collect();
    torus_external_product_with_mode(ct0, &difference, standard_ggsw, params, policy, mode)
}

/// Exact native-torus modulus switch used by tfhe-rs before blind rotation.
///
/// The returned monomial degree is in `[0, 2N)`.  The wrapping add is
/// load-bearing: values in the final half-bin round through zero exactly as in
/// tfhe-rs's `fft_impl::common::modulus_switch`.
pub fn torus_pbs_modulus_switch(
    input: u64,
    polynomial_degree: usize,
) -> Result<usize, TorusMacError> {
    if polynomial_degree == 0 {
        return Err(TorusMacError::ZeroDegree);
    }
    if !polynomial_degree.is_power_of_two() {
        return Err(TorusMacError::DegreeNotPowerOfTwo {
            degree: polynomial_degree,
        });
    }
    let modulus = polynomial_degree
        .checked_mul(2)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    let log_modulus = modulus.ilog2();
    if log_modulus >= u64::BITS {
        return Err(TorusMacError::AddressSpaceOverflow);
    }
    let shift = u64::BITS - log_modulus;
    let rounding = 1u64 << (shift - 1);
    usize::try_from(input.wrapping_add(rounding) >> shift)
        .map_err(|_| TorusMacError::AddressSpaceOverflow)
}

fn rotate_glwe_monomial(
    input: &[u64],
    rotation: usize,
    params: TorusExternalProductParams,
) -> Result<Vec<u64>, TorusMacError> {
    let modulus = params
        .degree
        .checked_mul(2)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if rotation >= modulus {
        return Err(TorusMacError::AddressSpaceOverflow);
    }
    let global_negative = rotation >= params.degree;
    let shift = rotation % params.degree;
    let mut output = vec![0u64; input.len()];
    for polynomial in 0..params.glwe_size {
        let base = polynomial * params.degree;
        for out_index in 0..params.degree {
            let (source_index, wrap_negative) = if out_index >= shift {
                (out_index - shift, false)
            } else {
                (params.degree + out_index - shift, true)
            };
            let value = input[base + source_index];
            output[base + out_index] = if global_negative != wrap_negative {
                value.wrapping_neg()
            } else {
                value
            };
        }
    }
    Ok(output)
}

fn validate_blind_rotation(
    accumulator: &[u64],
    lwe_mask: &[u64],
    standard_bsk: &[u64],
    params: TorusExternalProductParams,
) -> Result<(ExternalShape, usize), TorusMacError> {
    if lwe_mask.is_empty() {
        return Err(TorusMacError::EmptyBlindRotationMask);
    }
    let ggsw_coefficients = params
        .decomposition_level_count
        .checked_mul(params.glwe_size)
        .and_then(|count| count.checked_mul(params.glwe_size))
        .and_then(|count| count.checked_mul(params.degree))
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    let expected_bsk = lwe_mask
        .len()
        .checked_mul(ggsw_coefficients)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if standard_bsk.len() != expected_bsk {
        return Err(TorusMacError::BlindRotationKeyLength {
            expected: expected_bsk,
            actual: standard_bsk.len(),
        });
    }
    let shape = validate_external_product(
        accumulator,
        accumulator,
        &standard_bsk[..ggsw_coefficients],
        params,
    )?;
    let twice_degree = params
        .degree
        .checked_mul(2)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if twice_degree > u32::MAX as usize || expected_bsk > u32::MAX as usize {
        return Err(TorusMacError::AddressSpaceOverflow);
    }
    Ok((shape, ggsw_coefficients))
}

fn blind_rotation_schedule(
    lwe_mask: &[u64],
    lwe_body: u64,
    degree: usize,
) -> Result<(usize, Vec<usize>), TorusMacError> {
    let modulus = degree
        .checked_mul(2)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    let switched_body = torus_pbs_modulus_switch(lwe_body, degree)?;
    let body_rotation = (modulus - switched_body) % modulus;
    let mask_rotations = lwe_mask
        .iter()
        .map(|&coefficient| torus_pbs_modulus_switch(coefficient, degree))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((body_rotation, mask_rotations))
}

/// Exact coefficient-domain authority for tfhe-rs's classic blind rotation.
///
/// The input is a native-modulus LWE mask/body and a coefficient-domain
/// standard bootstrapping key, one GGSW ciphertext per mask coefficient.
pub fn torus_blind_rotate_cpu(
    accumulator: &[u64],
    lwe_mask: &[u64],
    lwe_body: u64,
    standard_bsk: &[u64],
    params: TorusExternalProductParams,
) -> Result<Vec<u64>, TorusMacError> {
    let (shape, ggsw_coefficients) =
        validate_blind_rotation(accumulator, lwe_mask, standard_bsk, params)?;
    let (body_rotation, mask_rotations) =
        blind_rotation_schedule(lwe_mask, lwe_body, params.degree)?;
    let mut current = rotate_glwe_monomial(accumulator, body_rotation, params)?;
    for (step, rotation) in mask_rotations.into_iter().enumerate() {
        if rotation == 0 {
            continue;
        }
        let rotated = rotate_glwe_monomial(&current, rotation, params)?;
        let difference = rotated
            .iter()
            .zip(&current)
            .map(|(&then_coefficient, &else_coefficient)| {
                then_coefficient.wrapping_sub(else_coefficient)
            })
            .collect::<Vec<_>>();
        let key_start = step * ggsw_coefficients;
        current = external_product_cpu_validated(
            &current,
            &difference,
            &standard_bsk[key_start..key_start + ggsw_coefficients],
            shape,
        );
    }
    Ok(current)
}

/// One-submit exact blind rotation.  Both accumulator buffers and the complete
/// standard bootstrapping key stay resident across the dependent CMUX chain;
/// only the final GLWE ciphertext is read back.
pub fn torus_blind_rotate_with_policy(
    accumulator: &[u64],
    lwe_mask: &[u64],
    lwe_body: u64,
    standard_bsk: &[u64],
    params: TorusExternalProductParams,
    policy: TorusMacPolicy,
) -> Result<TorusMacResult, TorusMacError> {
    let (_, ggsw_coefficients) =
        validate_blind_rotation(accumulator, lwe_mask, standard_bsk, params)?;
    if policy == TorusMacPolicy::CpuOnly {
        return Ok(TorusMacResult {
            coefficients: torus_blind_rotate_cpu(
                accumulator,
                lwe_mask,
                lwe_body,
                standard_bsk,
                params,
            )?,
            backend: TorusMacBackend::CpuOnly,
        });
    }
    let (body_rotation, mask_rotations) =
        blind_rotation_schedule(lwe_mask, lwe_body, params.degree)?;
    match blind_rotation_gpu(
        accumulator,
        body_rotation,
        &mask_rotations,
        standard_bsk,
        ggsw_coefficients,
        params,
    ) {
        Ok(result) => Ok(TorusMacResult {
            coefficients: result.coefficients,
            backend: TorusMacBackend::Wgpu {
                adapter_name: result.adapter,
                backend: result.backend,
                algorithm: TorusWgpuAlgorithm::ExactDeviceResidentBlindRotation,
            },
        }),
        Err(BlindRotationGpuError::Unavailable(reason))
            if policy == TorusMacPolicy::RequireWgpu =>
        {
            Err(TorusMacError::WgpuRequired(reason))
        }
        Err(BlindRotationGpuError::Unavailable(reason)) => Ok(TorusMacResult {
            coefficients: torus_blind_rotate_cpu(
                accumulator,
                lwe_mask,
                lwe_body,
                standard_bsk,
                params,
            )?,
            backend: TorusMacBackend::CpuFallback(reason),
        }),
        Err(BlindRotationGpuError::Execution(error)) => Err(TorusMacError::GpuExecution(error)),
    }
}

fn validate_keyswitch(
    standard_ksk: &[u64],
    external_params: TorusExternalProductParams,
    keyswitch_params: TorusKeyswitchParams,
) -> Result<(usize, usize), TorusMacError> {
    let input_lwe_dimension = external_params
        .glwe_size
        .checked_sub(1)
        .and_then(|dimension| dimension.checked_mul(external_params.degree))
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if input_lwe_dimension == 0 {
        return Err(TorusMacError::ZeroKeyswitchInputDimension);
    }
    if keyswitch_params.output_lwe_dimension == 0 {
        return Err(TorusMacError::ZeroKeyswitchOutputDimension);
    }
    if keyswitch_params.decomposition_base_log == 0 {
        return Err(TorusMacError::ZeroDecompositionBaseLog);
    }
    if keyswitch_params.decomposition_base_log > 31 {
        return Err(TorusMacError::DecompositionBaseLogTooWide {
            base_log: keyswitch_params.decomposition_base_log,
        });
    }
    if keyswitch_params.decomposition_level_count == 0 {
        return Err(TorusMacError::ZeroDecompositionLevelCount);
    }
    let represented_bits = keyswitch_params
        .decomposition_base_log
        .checked_mul(keyswitch_params.decomposition_level_count)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if represented_bits >= u64::BITS as usize {
        return Err(TorusMacError::DecompositionExhaustsTorus {
            base_log: keyswitch_params.decomposition_base_log,
            level_count: keyswitch_params.decomposition_level_count,
        });
    }
    let output_lwe_size = keyswitch_params
        .output_lwe_dimension
        .checked_add(1)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    let expected = input_lwe_dimension
        .checked_mul(keyswitch_params.decomposition_level_count)
        .and_then(|count| count.checked_mul(output_lwe_size))
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if standard_ksk.len() != expected {
        return Err(TorusMacError::KeyswitchKeyLength {
            expected,
            actual: standard_ksk.len(),
        });
    }
    if input_lwe_dimension > u32::MAX as usize
        || output_lwe_size > u32::MAX as usize
        || expected > u32::MAX as usize
    {
        return Err(TorusMacError::AddressSpaceOverflow);
    }
    Ok((input_lwe_dimension, output_lwe_size))
}

fn extract_degree_zero_lwe(glwe: &[u64], params: TorusExternalProductParams) -> Vec<u64> {
    let input_lwe_dimension = (params.glwe_size - 1) * params.degree;
    let mut lwe = Vec::with_capacity(input_lwe_dimension + 1);
    for polynomial in 0..params.glwe_size - 1 {
        let base = polynomial * params.degree;
        lwe.push(glwe[base]);
        for local in 1..params.degree {
            lwe.push(glwe[base + params.degree - local].wrapping_neg());
        }
    }
    lwe.push(glwe[(params.glwe_size - 1) * params.degree]);
    lwe
}

/// Exact CPU authority for blind rotation followed by degree-zero sample
/// extraction and a standard native-torus LWE key switch.
pub fn torus_pbs_extract_keyswitch_cpu(
    accumulator: &[u64],
    lwe_mask: &[u64],
    lwe_body: u64,
    standard_bsk: &[u64],
    external_params: TorusExternalProductParams,
    standard_ksk: &[u64],
    keyswitch_params: TorusKeyswitchParams,
) -> Result<Vec<u64>, TorusMacError> {
    validate_blind_rotation(accumulator, lwe_mask, standard_bsk, external_params)?;
    let (input_lwe_dimension, output_lwe_size) =
        validate_keyswitch(standard_ksk, external_params, keyswitch_params)?;
    let rotated = torus_blind_rotate_cpu(
        accumulator,
        lwe_mask,
        lwe_body,
        standard_bsk,
        external_params,
    )?;
    let extracted = extract_degree_zero_lwe(&rotated, external_params);
    let decomposer = SignedDecomposer::<u64>::new(
        DecompositionBaseLog(keyswitch_params.decomposition_base_log),
        DecompositionLevelCount(keyswitch_params.decomposition_level_count),
    );
    let mut output = vec![0u64; output_lwe_size];
    output[output_lwe_size - 1] = extracted[input_lwe_dimension];
    for (input_index, &mask_coefficient) in extracted[..input_lwe_dimension].iter().enumerate() {
        for (level, term) in decomposer.decompose(mask_coefficient).enumerate() {
            let key_start = (input_index * keyswitch_params.decomposition_level_count + level)
                * output_lwe_size;
            for (output_coefficient, &key_coefficient) in output
                .iter_mut()
                .zip(&standard_ksk[key_start..key_start + output_lwe_size])
            {
                *output_coefficient =
                    (*output_coefficient).wrapping_sub(term.value().wrapping_mul(key_coefficient));
            }
        }
    }
    Ok(output)
}

/// PBS-shaped exact portable artifact: blind rotation, degree-zero sample
/// extraction, and native-torus LWE key switch with one final post-key-switch
/// readback. Dense schedules use bounded ordered command submissions while the
/// accumulator and evaluation keys stay resident.
#[allow(clippy::too_many_arguments)]
pub fn torus_pbs_extract_keyswitch_with_policy(
    accumulator: &[u64],
    lwe_mask: &[u64],
    lwe_body: u64,
    standard_bsk: &[u64],
    external_params: TorusExternalProductParams,
    standard_ksk: &[u64],
    keyswitch_params: TorusKeyswitchParams,
    policy: TorusMacPolicy,
) -> Result<TorusMacResult, TorusMacError> {
    let (_, ggsw_coefficients) =
        validate_blind_rotation(accumulator, lwe_mask, standard_bsk, external_params)?;
    let (_, output_lwe_size) = validate_keyswitch(standard_ksk, external_params, keyswitch_params)?;
    if policy == TorusMacPolicy::CpuOnly {
        return Ok(TorusMacResult {
            coefficients: torus_pbs_extract_keyswitch_cpu(
                accumulator,
                lwe_mask,
                lwe_body,
                standard_bsk,
                external_params,
                standard_ksk,
                keyswitch_params,
            )?,
            backend: TorusMacBackend::CpuOnly,
        });
    }
    let (body_rotation, mask_rotations) =
        blind_rotation_schedule(lwe_mask, lwe_body, external_params.degree)?;
    match pbs_extract_keyswitch_gpu(
        accumulator,
        body_rotation,
        &mask_rotations,
        standard_bsk,
        ggsw_coefficients,
        external_params,
        standard_ksk,
        output_lwe_size,
        keyswitch_params.decomposition_base_log,
        keyswitch_params.decomposition_level_count,
    ) {
        Ok(result) => Ok(TorusMacResult {
            coefficients: result.coefficients,
            backend: TorusMacBackend::Wgpu {
                adapter_name: result.adapter,
                backend: result.backend,
                algorithm: TorusWgpuAlgorithm::ExactDeviceResidentPbsExtractKeyswitch,
            },
        }),
        Err(BlindRotationGpuError::Unavailable(reason))
            if policy == TorusMacPolicy::RequireWgpu =>
        {
            Err(TorusMacError::WgpuRequired(reason))
        }
        Err(BlindRotationGpuError::Unavailable(reason)) => Ok(TorusMacResult {
            coefficients: torus_pbs_extract_keyswitch_cpu(
                accumulator,
                lwe_mask,
                lwe_body,
                standard_bsk,
                external_params,
                standard_ksk,
                keyswitch_params,
            )?,
            backend: TorusMacBackend::CpuFallback(reason),
        }),
        Err(BlindRotationGpuError::Execution(error)) => Err(TorusMacError::GpuExecution(error)),
    }
}

/// Validate and upload immutable standard-domain PBS evaluation keys once.
///
/// Unlike [`torus_pbs_extract_keyswitch_with_policy`], this is intentionally a
/// fail-closed GPU constructor: a returned plan is evidence that the exact key
/// shape fits the selected adapter. The host key slices are not retained.
pub fn prepare_torus_pbs_wgpu_plan(
    blind_mask_dimension: usize,
    standard_bsk: &[u64],
    external_params: TorusExternalProductParams,
    standard_ksk: &[u64],
    keyswitch_params: TorusKeyswitchParams,
) -> Result<TorusPbsWgpuPlan, TorusMacError> {
    if blind_mask_dimension == 0 {
        return Err(TorusMacError::EmptyBlindRotationMask);
    }
    let external_shape = validate_external_product_shape(external_params)?;
    let expected_bsk = blind_mask_dimension
        .checked_mul(external_shape.ggsw_coefficients)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if standard_bsk.len() != expected_bsk {
        return Err(TorusMacError::BlindRotationKeyLength {
            expected: expected_bsk,
            actual: standard_bsk.len(),
        });
    }
    if expected_bsk > u32::MAX as usize {
        return Err(TorusMacError::AddressSpaceOverflow);
    }
    let (_, output_lwe_size) = validate_keyswitch(standard_ksk, external_params, keyswitch_params)?;
    match prepare_pbs_extract_keyswitch_gpu(
        standard_bsk,
        external_shape.ggsw_coefficients,
        external_params,
        standard_ksk,
        output_lwe_size,
        keyswitch_params.decomposition_base_log,
        keyswitch_params.decomposition_level_count,
    ) {
        Ok(prepared) => Ok(TorusPbsWgpuPlan {
            prepared,
            blind_mask_dimension,
            external_params,
            keyswitch_params,
        }),
        Err(BlindRotationGpuError::Unavailable(reason)) => Err(TorusMacError::WgpuRequired(reason)),
        Err(BlindRotationGpuError::Execution(error)) => Err(TorusMacError::GpuExecution(error)),
    }
}

/// Execute one exact PBS-shaped operation against pre-uploaded evaluation keys.
///
/// The accumulator follows the same resident blind-rotate/extract/key-switch
/// path as the ordinary API. Only per-ciphertext buffers and the final LWE
/// readback are transient; BSK/KSK uploads are outside this call. Dense schedules
/// are command-chunked without an intermediate host readback.
pub fn torus_pbs_extract_keyswitch_prepared(
    plan: &TorusPbsWgpuPlan,
    accumulator: &[u64],
    lwe_mask: &[u64],
    lwe_body: u64,
) -> Result<TorusMacResult, TorusMacError> {
    if lwe_mask.len() != plan.blind_mask_dimension {
        return Err(TorusMacError::BlindRotationMaskLength {
            expected: plan.blind_mask_dimension,
            actual: lwe_mask.len(),
        });
    }
    let expected_accumulator = plan
        .external_params
        .glwe_size
        .checked_mul(plan.external_params.degree)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if accumulator.len() != expected_accumulator {
        return Err(TorusMacError::GlweLength {
            expected: expected_accumulator,
            actual: accumulator.len(),
        });
    }
    let (body_rotation, mask_rotations) =
        blind_rotation_schedule(lwe_mask, lwe_body, plan.external_params.degree)?;
    match pbs_extract_keyswitch_prepared_gpu(
        accumulator,
        body_rotation,
        &mask_rotations,
        &plan.prepared,
    ) {
        Ok(result) => Ok(TorusMacResult {
            coefficients: result.coefficients,
            backend: TorusMacBackend::Wgpu {
                adapter_name: result.adapter,
                backend: result.backend,
                algorithm: TorusWgpuAlgorithm::ExactDeviceResidentPbsExtractKeyswitch,
            },
        }),
        Err(BlindRotationGpuError::Unavailable(reason)) => Err(TorusMacError::WgpuRequired(reason)),
        Err(BlindRotationGpuError::Execution(error)) => Err(TorusMacError::GpuExecution(error)),
    }
}

/// Validate, transform, and upload the complete deployed PBS evaluation keys.
///
/// This first transform-resident backend intentionally admits exactly the
/// tfhe-rs parameter envelope used by fhEgg today. Unsupported shapes fail
/// closed instead of being relabelled as transform execution.
pub fn prepare_torus_pbs_transform_wgpu_plan(
    blind_mask_dimension: usize,
    standard_bsk: &[u64],
    external_params: TorusExternalProductParams,
    standard_ksk: &[u64],
    keyswitch_params: TorusKeyswitchParams,
) -> Result<TorusPbsTransformWgpuPlan, TorusMacError> {
    let shape = validate_external_product_shape(external_params)?;
    let expected_bsk = blind_mask_dimension
        .checked_mul(shape.ggsw_coefficients)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if standard_bsk.len() != expected_bsk {
        return Err(TorusMacError::BlindRotationKeyLength {
            expected: expected_bsk,
            actual: standard_bsk.len(),
        });
    }
    let (_, output_lwe_size) = validate_keyswitch(standard_ksk, external_params, keyswitch_params)?;
    let deployed = external_params
        == (TorusExternalProductParams {
            degree: 2048,
            glwe_size: 2,
            decomposition_base_log: 23,
            decomposition_level_count: 1,
        })
        && blind_mask_dimension == 918
        && keyswitch_params
            == (TorusKeyswitchParams {
                output_lwe_dimension: 918,
                decomposition_base_log: 4,
                decomposition_level_count: 4,
            })
        && exact_ntt_range_supported(shape);
    if !deployed {
        return Err(TorusMacError::WgpuRequired(
            TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
        ));
    }
    match prepare_transform_pbs_gpu(
        blind_mask_dimension,
        standard_bsk,
        external_params,
        standard_ksk,
        output_lwe_size,
        keyswitch_params.decomposition_base_log,
        keyswitch_params.decomposition_level_count,
    ) {
        Ok(prepared) => Ok(TorusPbsTransformWgpuPlan {
            prepared,
            external_params,
            keyswitch_params,
        }),
        Err(TransformPbsGpuError::Unavailable(reason)) => Err(TorusMacError::WgpuRequired(reason)),
        Err(TransformPbsGpuError::Execution(error)) => Err(TorusMacError::GpuExecution(error)),
    }
}

/// Execute one exact dense PBS against a pretransformed deployed evaluation key.
pub fn torus_pbs_extract_keyswitch_transform_prepared(
    plan: &TorusPbsTransformWgpuPlan,
    accumulator: &[u64],
    lwe_mask: &[u64],
    lwe_body: u64,
) -> Result<TorusMacResult, TorusMacError> {
    if lwe_mask.len() != plan.prepared.blind_mask_dimension {
        return Err(TorusMacError::BlindRotationMaskLength {
            expected: plan.prepared.blind_mask_dimension,
            actual: lwe_mask.len(),
        });
    }
    let expected_accumulator = plan
        .external_params
        .glwe_size
        .checked_mul(plan.external_params.degree)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if accumulator.len() != expected_accumulator {
        return Err(TorusMacError::GlweLength {
            expected: expected_accumulator,
            actual: accumulator.len(),
        });
    }
    let (body_rotation, mask_rotations) =
        blind_rotation_schedule(lwe_mask, lwe_body, plan.external_params.degree)?;
    match transform_pbs_gpu(accumulator, body_rotation, &mask_rotations, &plan.prepared) {
        Ok(result) => Ok(TorusMacResult {
            coefficients: result.coefficients,
            backend: TorusMacBackend::Wgpu {
                adapter_name: result.adapter,
                backend: result.backend,
                algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
            },
        }),
        Err(TransformPbsGpuError::Unavailable(reason)) => Err(TorusMacError::WgpuRequired(reason)),
        Err(TransformPbsGpuError::Execution(error)) => Err(TorusMacError::GpuExecution(error)),
    }
}

/// Execute the transform-resident blind rotation and degree-zero sample
/// extraction without a trailing key switch.
///
/// This is the terminal half of tfhe-rs's deployed `KeyswitchBootstrap`
/// order. `mask_rotations` and `body_rotation` are already modulus-switched in
/// `[0, 2N)`, which lets a caller preserve tfhe-rs's selected centered-mean or
/// drift noise-reduction policy exactly instead of silently applying the
/// standard modulus switch a second time.
pub fn torus_pbs_bootstrap_transform_prepared(
    plan: &TorusPbsTransformWgpuPlan,
    accumulator: &[u64],
    mask_rotations: &[usize],
    body_rotation: usize,
) -> Result<TorusMacResult, TorusMacError> {
    if mask_rotations.len() != plan.prepared.blind_mask_dimension {
        return Err(TorusMacError::BlindRotationMaskLength {
            expected: plan.prepared.blind_mask_dimension,
            actual: mask_rotations.len(),
        });
    }
    let twice_degree = plan
        .external_params
        .degree
        .checked_mul(2)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if body_rotation >= twice_degree || mask_rotations.iter().any(|&r| r >= twice_degree) {
        return Err(TorusMacError::AddressSpaceOverflow);
    }
    let expected_accumulator = plan
        .external_params
        .glwe_size
        .checked_mul(plan.external_params.degree)
        .ok_or(TorusMacError::AddressSpaceOverflow)?;
    if accumulator.len() != expected_accumulator {
        return Err(TorusMacError::GlweLength {
            expected: expected_accumulator,
            actual: accumulator.len(),
        });
    }
    match transform_bootstrap_gpu(accumulator, body_rotation, mask_rotations, &plan.prepared) {
        Ok(result) => Ok(TorusMacResult {
            coefficients: result.coefficients,
            backend: TorusMacBackend::Wgpu {
                adapter_name: result.adapter,
                backend: result.backend,
                algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
            },
        }),
        Err(TransformPbsGpuError::Unavailable(reason)) => Err(TorusMacError::WgpuRequired(reason)),
        Err(TransformPbsGpuError::Execution(error)) => Err(TorusMacError::GpuExecution(error)),
    }
}

/// Execute a complete radix scalar-comparison PBS chain with the large-key
/// state, pre-PBS key switches, centered modulus-switch schedules, and LUT
/// accumulators resident on the selected wgpu device. Only the final large-key
/// predicate LWE is read back.
pub fn torus_pbs_scalar_gt_chain_transform_prepared(
    plan: &TorusPbsTransformWgpuPlan,
    digit_lwes: &[u64],
    accumulators: &[u64],
    blocks: usize,
) -> Result<TorusMacResult, TorusMacError> {
    match transform_scalar_gt_chain_gpu(digit_lwes, accumulators, blocks, &plan.prepared) {
        Ok(result) => Ok(TorusMacResult {
            coefficients: result.coefficients,
            backend: TorusMacBackend::Wgpu {
                adapter_name: result.adapter,
                backend: result.backend,
                algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
            },
        }),
        Err(TransformPbsGpuError::Unavailable(reason)) => Err(TorusMacError::WgpuRequired(reason)),
        Err(TransformPbsGpuError::Execution(error)) => Err(TorusMacError::GpuExecution(error)),
    }
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

    #[test]
    fn exact_ntt_crt_range_is_load_bearing() {
        let deployed = ExternalShape {
            params: TorusExternalProductParams {
                degree: 2048,
                glwe_size: 2,
                decomposition_base_log: 23,
                decomposition_level_count: 1,
            },
            glwe_coefficients: 4096,
            ggsw_coefficients: 8192,
            decomposed_coefficients: 4096,
        };
        assert!(exact_ntt_range_supported(deployed));

        // Keep every arithmetic parameter locally valid while making the
        // worst-case convolution wider than the 120-bit CRT carrier. This
        // must select the exact coefficient route rather than alias modulo M.
        let too_wide = ExternalShape {
            params: TorusExternalProductParams {
                degree: 4096,
                glwe_size: 1 << 14,
                decomposition_base_log: 31,
                decomposition_level_count: 2,
            },
            glwe_coefficients: 0,
            ggsw_coefficients: 0,
            decomposed_coefficients: 0,
        };
        assert!(!exact_ntt_range_supported(too_wide));
    }

    #[test]
    fn crt_reconstruction_preserves_signed_value_and_low_torus_bits() {
        let crt = CrtPlan::new();
        for value in [
            I256::ZERO,
            I256::ONE,
            I256::from(-1),
            I256::ONE << 96u32,
            -(I256::ONE << 96u32),
            (I256::ONE << 118u32) - I256::ONE,
            -((I256::ONE << 118u32) - I256::ONE),
        ] {
            let residues = std::array::from_fn(|row| {
                let q = I256::from(TORUS_NTT_MODULI[row]);
                let mut residue = value % q;
                if residue < I256::ZERO {
                    residue += q;
                }
                residue.as_u64()
            });
            let reconstructed = crt.reconstruct_signed(residues);
            assert_eq!(reconstructed, value);
            assert_eq!(reconstructed.as_u64(), value.as_u64());
        }
    }

    #[test]
    fn pbs_modulus_switch_wraps_the_final_rounding_bin_to_zero() {
        let degree = 2048usize;
        let shift = 52u32;
        let rounding = 1u64 << 51;
        assert_eq!(torus_pbs_modulus_switch(0, degree), Ok(0));
        assert_eq!(torus_pbs_modulus_switch(rounding - 1, degree), Ok(0));
        assert_eq!(torus_pbs_modulus_switch(rounding, degree), Ok(1));
        assert_eq!(
            torus_pbs_modulus_switch(u64::MAX - rounding, degree),
            Ok((u64::MAX - rounding).wrapping_add(rounding) as usize >> shift)
        );
        assert_eq!(torus_pbs_modulus_switch(u64::MAX, degree), Ok(0));
    }

    #[test]
    fn monomial_rotation_matches_tfhe_polynomial_definition_across_2n() {
        use tfhe::core_crypto::algorithms::polynomial_algorithms::polynomial_wrapping_monic_monomial_mul;
        use tfhe::core_crypto::prelude::MonomialDegree;

        let params = TorusExternalProductParams {
            degree: 8,
            glwe_size: 1,
            decomposition_base_log: 4,
            decomposition_level_count: 2,
        };
        let input = [1u64, 2, u64::MAX, 4, 1u64 << 63, 6, 7, 8];
        for rotation in 0..16 {
            let mut tfhe_output = vec![0u64; params.degree];
            let mut output_polynomial = Polynomial::from_container(tfhe_output.as_mut_slice());
            let input_polynomial = Polynomial::from_container(input.as_slice());
            polynomial_wrapping_monic_monomial_mul(
                &mut output_polynomial,
                &input_polynomial,
                MonomialDegree(rotation),
            );
            assert_eq!(
                rotate_glwe_monomial(&input, rotation, params).unwrap(),
                tfhe_output,
                "rotation X^{rotation} diverged"
            );
        }
    }

    #[test]
    fn blind_rotation_refuses_unpaired_mask_and_key_before_gpu_selection() {
        let params = TorusExternalProductParams {
            degree: 8,
            glwe_size: 2,
            decomposition_base_log: 4,
            decomposition_level_count: 2,
        };
        let accumulator = [0u64; 16];
        assert_eq!(
            torus_blind_rotate_cpu(&accumulator, &[], 0, &[], params),
            Err(TorusMacError::EmptyBlindRotationMask)
        );
        assert_eq!(
            torus_blind_rotate_cpu(&accumulator, &[0], 0, &[0; 63], params),
            Err(TorusMacError::BlindRotationKeyLength {
                expected: 64,
                actual: 63,
            })
        );
        let keyswitch_params = TorusKeyswitchParams {
            output_lwe_dimension: 3,
            decomposition_base_log: 4,
            decomposition_level_count: 2,
        };
        assert_eq!(
            torus_pbs_extract_keyswitch_cpu(
                &accumulator,
                &[0],
                0,
                &[0; 64],
                params,
                &[0; 63],
                keyswitch_params,
            ),
            Err(TorusMacError::KeyswitchKeyLength {
                expected: 64,
                actual: 63,
            })
        );
    }
}

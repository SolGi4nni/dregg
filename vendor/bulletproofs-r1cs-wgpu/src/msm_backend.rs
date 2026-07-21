//! Owned Ristretto MSM dispatch seam for the R1CS prover.
//!
//! Upstream Bulletproofs hard-codes six calls to dalek's constant-time MSM in
//! `r1cs::Prover::prove`: the `(A_I, A_O, S)` commitments in each of the two
//! proving phases.  This module is the single replacement point for those
//! calls.
//!
//! The prover seam sends every witness-derived scalar through exact portable
//! GPU window preparation, but deliberately keeps group MSM in dalek: the
//! branch-bearing public-scalar kernel is not an acceptable secret-scalar
//! replacement. The verifier seam owns a complete bounded GPU MSM: a
//! device-resident radix-16 Pippenger reduction with chunk-local buckets.
//! Dalek still computes the result independently and is the canonical
//! acceptance oracle.
//!
//! No GPU path is default authority. Disabled mode is pure dalek; auto mode has
//! explicit CPU fallback; required mode fails closed on feature, adapter,
//! dimension, canonical-input, identity-input, or parity failure.

use core::borrow::Borrow;
use std::convert::{TryFrom, TryInto};

use curve25519_dalek::ristretto::{CompressedRistretto, DreggExtendedCoordinates, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{Identity, MultiscalarMul, VartimeMultiscalarMul};

use crate::errors::R1CSError;

/// The number of aligned radix-256 windows in a canonical 32-byte scalar.
pub const RADIX_256_WINDOWS: usize = 32;

/// Hard allocation/dispatch ceiling for the qualification MSM.
///
/// This comfortably covers small and medium Bulletproof verifier checks while
/// making hostile serialized dimensions fail before allocating device buffers.
pub const MAX_WGPU_MSM_TERMS: usize = 4096;

/// Result of the exact GPU-preparation stage.
#[derive(Debug, Eq, PartialEq)]
pub struct WgpuPreparation {
    /// Adapter selected by wgpu.
    pub adapter_name: String,
    /// `false` denotes a software/CPU adapter such as lavapipe.
    pub is_hardware: bool,
    /// Number of canonical scalars processed.
    pub scalar_count: usize,
    /// Exact unsigned radix-256 digits, `[scalar][window]`, little-endian.
    pub windows: Vec<u8>,
}

impl Drop for WgpuPreparation {
    fn drop(&mut self) {
        self.windows.fill(0);
    }
}

/// Result of exact GPU extended-Edwards additions.
#[derive(Debug, Eq, PartialEq)]
pub struct WgpuPointAddition {
    /// Adapter selected by wgpu.
    pub adapter_name: String,
    /// `false` denotes a software/CPU adapter such as lavapipe.
    pub is_hardware: bool,
    /// Canonical compressed sums, each independently matched to dalek.
    pub compressed_sums: Vec<[u8; 32]>,
}

/// Exact result of the bounded public-scalar GPU MSM.
#[derive(Debug, Eq, PartialEq)]
pub struct WgpuMsmResult {
    /// Adapter selected by wgpu.
    pub adapter_name: String,
    /// `false` denotes a software/CPU adapter such as lavapipe.
    pub is_hardware: bool,
    /// Number of scalar/point terms reduced by the GPU.
    pub term_count: usize,
    /// Canonical Ristretto encoding, accepted only after exact dalek parity.
    pub compressed_result: [u8; 32],
    /// Submit-to-completion time for scaling, reduction, and final readback.
    pub gpu_elapsed_micros: u128,
    /// Bits consumed per device-resident Pippenger window.
    pub window_bits: u32,
    /// Number of radix windows spanning a canonical scalar.
    pub window_count: u32,
    /// Number of nonzero buckets per window.
    pub bucket_count: u32,
    /// Number of bounded term chunks independently accumulated per bucket.
    pub chunk_count: u32,
    /// Number of independently parallel chunk-local bucket accumulators.
    pub partial_bucket_count: u32,
    /// Scalar/bucket comparisons performed by the first GPU stage.
    pub bucket_term_tests: u64,
    /// Exact number of nonzero radix digits considered by stage one.
    pub nonzero_digits: u64,
    /// Conservative point-addition bound after stage one; identity fast paths
    /// make the executed count smaller, especially for sparse small MSMs.
    pub post_bucket_addition_upper_bound: u64,
    /// Number of ordered device dispatches in the MSM pipeline.
    pub dispatch_count: u32,
    /// Number of device-to-host result readbacks.
    pub readback_count: u32,
}

#[cfg(feature = "wgpu-msm")]
struct CompleteMsmContext {
    adapter_name: String,
    is_hardware: bool,
    limits: wgpu::Limits,
    device: wgpu::Device,
    queue: wgpu::Queue,
    layout: wgpu::BindGroupLayout,
    pipeline: wgpu::ComputePipeline,
}

#[cfg(feature = "wgpu-msm")]
fn complete_msm_context() -> Result<&'static CompleteMsmContext, MsmBackendError> {
    static CONTEXT: std::sync::OnceLock<Result<CompleteMsmContext, String>> =
        std::sync::OnceLock::new();
    CONTEXT
        .get_or_init(|| {
            let instance = wgpu::Instance::default();
            let adapter =
                pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
                    power_preference: wgpu::PowerPreference::HighPerformance,
                    ..Default::default()
                }))
                .ok_or_else(|| "no adapter".to_owned())?;
            let adapter_info = adapter.get_info();
            let adapter_name = adapter_info.name;
            let is_hardware = !matches!(adapter_info.device_type, wgpu::DeviceType::Cpu);
            let limits = adapter.limits();
            let (device, queue) = pollster::block_on(adapter.request_device(
                &wgpu::DeviceDescriptor {
                    label: Some("bulletproofs-ristretto-complete-msm-device"),
                    required_features: wgpu::Features::empty(),
                    required_limits: limits.clone(),
                    memory_hints: Default::default(),
                },
                None,
            ))
            .map_err(|error| error.to_string())?;
            let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("bulletproofs-ristretto-complete-msm-shader"),
                source: wgpu::ShaderSource::Wgsl(
                    include_str!("shaders/edwards_add_radix5.wgsl").into(),
                ),
            });
            let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("bulletproofs-ristretto-complete-msm-bind-layout"),
                entries: &[
                    buffer_entry(0, wgpu::BufferBindingType::Uniform),
                    buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
                    buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
                    buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: false }),
                    buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: true }),
                ],
            });
            let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("bulletproofs-ristretto-complete-msm-pipeline-layout"),
                bind_group_layouts: &[&layout],
                push_constant_ranges: &[],
            });
            let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("bulletproofs-ristretto-complete-msm-pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some("pippenger"),
                compilation_options: Default::default(),
                cache: None,
            });
            Ok(CompleteMsmContext {
                adapter_name,
                is_hardware,
                limits,
                device,
                queue,
                layout,
                pipeline,
            })
        })
        .as_ref()
        .map_err(|reason| MsmBackendError::WgpuUnavailable(reason.clone()))
}

/// Fail-closed input or GPU error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MsmBackendError {
    /// An empty serialized MSM is not a verifier statement and cannot create
    /// non-empty wgpu storage bindings portably.
    EmptyMsm,
    /// Scalar and point sequences had different lengths.
    LengthMismatch { scalars: usize, points: usize },
    /// The bounded backend refuses allocations above its documented ceiling.
    TooManyTerms { terms: usize, maximum: usize },
    /// A serialized scalar was not canonical modulo the Ristretto group order.
    NonCanonicalScalar { index: usize },
    /// A serialized Ristretto point did not canonically decompress.
    NonCanonicalPoint { index: usize },
    /// Verifier proof inputs must not smuggle the Ristretto identity as a
    /// syntactically valid substitute for a required commitment.
    IdentityPoint { index: usize },
    /// No usable hardware/software wgpu adapter was available.
    WgpuUnavailable(String),
    /// The shader output disagreed with exact CPU radix-256 decomposition.
    WgpuParityMismatch { scalar: usize, window: usize },
    /// A GPU extended-coordinate result was malformed, off-curve, or did not
    /// compress to the exact dalek sum.
    WgpuPointMismatch { index: usize },
    /// The complete GPU MSM disagreed with dalek's canonical group result.
    WgpuMsmMismatch,
    /// Input dimensions overflowed a checked host or device limit.
    DimensionOverflow,
}

impl core::fmt::Display for MsmBackendError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyMsm => write!(f, "empty MSM is outside the bounded wgpu contract"),
            Self::LengthMismatch { scalars, points } => {
                write!(f, "MSM length mismatch: {scalars} scalars, {points} points")
            }
            Self::TooManyTerms { terms, maximum } => {
                write!(
                    f,
                    "MSM has {terms} terms; bounded wgpu maximum is {maximum}"
                )
            }
            Self::NonCanonicalScalar { index } => {
                write!(f, "non-canonical Ristretto scalar at index {index}")
            }
            Self::NonCanonicalPoint { index } => {
                write!(f, "non-canonical Ristretto point at index {index}")
            }
            Self::IdentityPoint { index } => {
                write!(
                    f,
                    "Ristretto identity point refused at verifier index {index}"
                )
            }
            Self::WgpuUnavailable(reason) => write!(f, "wgpu MSM backend unavailable: {reason}"),
            Self::WgpuParityMismatch { scalar, window } => write!(
                f,
                "wgpu scalar-window mismatch at scalar {scalar}, window {window}"
            ),
            Self::WgpuPointMismatch { index } => {
                write!(f, "wgpu extended-Edwards sum mismatch at pair {index}")
            }
            Self::WgpuMsmMismatch => write!(f, "wgpu MSM result disagrees with dalek"),
            Self::DimensionOverflow => write!(f, "MSM dimensions exceed checked device limits"),
        }
    }
}

impl std::error::Error for MsmBackendError {}

fn r1cs_error(error: MsmBackendError) -> R1CSError {
    R1CSError::GadgetError {
        description: format!("Ristretto MSM backend: {error}"),
    }
}

fn env_true(name: &str) -> bool {
    std::env::var(name)
        .map(|value| {
            matches!(
                value.to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "required"
            )
        })
        .unwrap_or(false)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WgpuPolicy {
    Disabled,
    Auto,
    Required,
}

fn wgpu_policy() -> WgpuPolicy {
    if env_true("DREGG_REQUIRE_WGPU") {
        return WgpuPolicy::Required;
    }
    match std::env::var("DREGG_BULLETPROOFS_WGPU") {
        Ok(value) if value.eq_ignore_ascii_case("auto") => WgpuPolicy::Auto,
        Ok(value)
            if matches!(
                value.to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "required"
            ) =>
        {
            WgpuPolicy::Required
        }
        _ => WgpuPolicy::Disabled,
    }
}

/// Validate serialized inputs before a future external/GPU point backend sees
/// them.  Both encodings must round-trip byte-for-byte; non-canonical aliases
/// and invalid group encodings are refused.
pub fn validate_canonical_inputs(
    scalar_bytes: &[[u8; 32]],
    point_bytes: &[[u8; 32]],
) -> Result<(Vec<Scalar>, Vec<RistrettoPoint>), MsmBackendError> {
    if scalar_bytes.len() != point_bytes.len() {
        return Err(MsmBackendError::LengthMismatch {
            scalars: scalar_bytes.len(),
            points: point_bytes.len(),
        });
    }

    let mut scalars = Vec::with_capacity(scalar_bytes.len());
    for (index, bytes) in scalar_bytes.iter().enumerate() {
        let scalar = Option::<Scalar>::from(Scalar::from_canonical_bytes(*bytes))
            .ok_or(MsmBackendError::NonCanonicalScalar { index })?;
        if scalar.to_bytes() != *bytes {
            return Err(MsmBackendError::NonCanonicalScalar { index });
        }
        scalars.push(scalar);
    }

    let mut points = Vec::with_capacity(point_bytes.len());
    for (index, bytes) in point_bytes.iter().enumerate() {
        let point = CompressedRistretto(*bytes)
            .decompress()
            .ok_or(MsmBackendError::NonCanonicalPoint { index })?;
        if point.compress().to_bytes() != *bytes {
            return Err(MsmBackendError::NonCanonicalPoint { index });
        }
        points.push(point);
    }
    Ok((scalars, points))
}

/// Execute the exact scalar-window stage on wgpu and compare it byte-for-byte
/// to the CPU definition.
///
/// This public tooth takes serialized scalars so malformed/non-canonical input
/// can be tested.  Production's typed `Scalar` path calls the same private
/// kernel after serializing its already-canonical values.
#[cfg(feature = "wgpu-msm")]
pub fn prepare_scalar_windows_wgpu(
    scalar_bytes: &[[u8; 32]],
) -> Result<WgpuPreparation, MsmBackendError> {
    let mut words = Vec::with_capacity(
        scalar_bytes
            .len()
            .checked_mul(8)
            .ok_or(MsmBackendError::DimensionOverflow)?,
    );
    for (index, bytes) in scalar_bytes.iter().enumerate() {
        let scalar = Option::<Scalar>::from(Scalar::from_canonical_bytes(*bytes))
            .ok_or(MsmBackendError::NonCanonicalScalar { index })?;
        if scalar.to_bytes() != *bytes {
            return Err(MsmBackendError::NonCanonicalScalar { index });
        }
        for chunk in bytes.chunks_exact(4) {
            words.push(u32::from_le_bytes(
                chunk.try_into().expect("four-byte chunk"),
            ));
        }
    }

    let scalar_count =
        u32::try_from(scalar_bytes.len()).map_err(|_| MsmBackendError::DimensionOverflow)?;
    if scalar_count == 0 {
        return Ok(WgpuPreparation {
            adapter_name: "no-dispatch(empty)".to_owned(),
            is_hardware: false,
            scalar_count: 0,
            windows: Vec::new(),
        });
    }

    let instance = wgpu::Instance::default();
    let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
        power_preference: wgpu::PowerPreference::HighPerformance,
        ..Default::default()
    }))
    .ok_or_else(|| MsmBackendError::WgpuUnavailable("no adapter".to_owned()))?;
    let adapter_info = adapter.get_info();
    let adapter_name = adapter_info.name;
    let is_hardware = !matches!(adapter_info.device_type, wgpu::DeviceType::Cpu);
    let limits = adapter.limits();
    let workgroups = scalar_count.div_ceil(64);
    if workgroups > limits.max_compute_workgroups_per_dimension {
        return Err(MsmBackendError::DimensionOverflow);
    }
    let (device, queue) = pollster::block_on(adapter.request_device(
        &wgpu::DeviceDescriptor {
            label: Some("bulletproofs-ristretto-msm-window-device"),
            required_features: wgpu::Features::empty(),
            required_limits: limits.clone(),
            memory_hints: Default::default(),
        },
        None,
    ))
    .map_err(|error| MsmBackendError::WgpuUnavailable(error.to_string()))?;

    use wgpu::util::DeviceExt;
    let input = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-ristretto-msm-scalars"),
        contents: bytemuck::cast_slice(&words),
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
    });
    let output_len = scalar_bytes
        .len()
        .checked_mul(RADIX_256_WINDOWS)
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let output_bytes = u64::try_from(
        output_len
            .checked_mul(core::mem::size_of::<u32>())
            .ok_or(MsmBackendError::DimensionOverflow)?,
    )
    .map_err(|_| MsmBackendError::DimensionOverflow)?;
    let input_bytes = u64::try_from(
        words
            .len()
            .checked_mul(core::mem::size_of::<u32>())
            .ok_or(MsmBackendError::DimensionOverflow)?,
    )
    .map_err(|_| MsmBackendError::DimensionOverflow)?;
    let storage_limit =
        u64::from(limits.max_storage_buffer_binding_size).min(limits.max_buffer_size);
    if input_bytes > storage_limit || output_bytes > storage_limit {
        words.fill(0);
        return Err(MsmBackendError::DimensionOverflow);
    }
    let output = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-msm-windows"),
        size: output_bytes,
        usage: wgpu::BufferUsages::STORAGE
            | wgpu::BufferUsages::COPY_SRC
            | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let readback = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-readback"),
        size: output_bytes,
        usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
        mapped_at_creation: false,
    });
    let metadata = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-metadata"),
        contents: bytemuck::cast_slice(&[scalar_count, 0_u32, 0, 0]),
        usage: wgpu::BufferUsages::UNIFORM,
    });

    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-shader"),
        source: wgpu::ShaderSource::Wgsl(include_str!("shaders/msm_windows.wgsl").into()),
    });
    let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-bind-layout"),
        entries: &[
            buffer_entry(0, wgpu::BufferBindingType::Uniform),
            buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
        ],
    });
    let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-pipeline-layout"),
        bind_group_layouts: &[&layout],
        push_constant_ranges: &[],
    });
    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-pipeline"),
        layout: Some(&pipeline_layout),
        module: &shader,
        entry_point: Some("main"),
        compilation_options: Default::default(),
        cache: None,
    });
    let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-bind-group"),
        layout: &layout,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: metadata.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: input.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: output.as_entire_binding(),
            },
        ],
    });

    let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-encoder"),
    });
    {
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some("bulletproofs-ristretto-msm-window-pass"),
            timestamp_writes: None,
        });
        pass.set_pipeline(&pipeline);
        pass.set_bind_group(0, &bind_group, &[]);
        pass.dispatch_workgroups(workgroups, 1, 1);
    }
    encoder.copy_buffer_to_buffer(&output, 0, &readback, 0, output_bytes);
    queue.submit(Some(encoder.finish()));

    let slice = readback.slice(..);
    let (send, receive) = std::sync::mpsc::sync_channel(1);
    slice.map_async(wgpu::MapMode::Read, move |result| {
        let _ = send.send(result);
    });
    device.poll(wgpu::Maintain::Wait);
    let map_result = receive.recv();
    match map_result {
        Ok(Ok(())) => {}
        Ok(Err(error)) => {
            clear_secret_buffers(&device, &queue, &input, &output, &readback);
            words.fill(0);
            return Err(MsmBackendError::WgpuUnavailable(error.to_string()));
        }
        Err(_) => {
            clear_secret_buffers(&device, &queue, &input, &output, &readback);
            words.fill(0);
            return Err(MsmBackendError::WgpuUnavailable(
                "readback callback was dropped".to_owned(),
            ));
        }
    }
    let mapped = slice.get_mapped_range();
    let gpu_words: &[u32] = bytemuck::cast_slice(&mapped);
    if gpu_words.len() != output_len {
        drop(mapped);
        readback.unmap();
        clear_secret_buffers(&device, &queue, &input, &output, &readback);
        words.fill(0);
        return Err(MsmBackendError::DimensionOverflow);
    }
    let mut windows = Vec::with_capacity(output_len);
    let mut mismatch = None;
    for (flat_index, &digit) in gpu_words.iter().enumerate() {
        let scalar = flat_index / RADIX_256_WINDOWS;
        let window = flat_index % RADIX_256_WINDOWS;
        let expected = scalar_bytes[scalar][window];
        if digit != u32::from(expected) {
            mismatch = Some(MsmBackendError::WgpuParityMismatch { scalar, window });
            break;
        }
        windows.push(expected);
    }
    drop(mapped);
    readback.unmap();

    // The scalar bytes are witness-derived.  Clear both device buffers and
    // wait before releasing them; also scrub the host staging words.
    clear_secret_buffers(&device, &queue, &input, &output, &readback);
    words.fill(0);
    if let Some(error) = mismatch {
        windows.fill(0);
        return Err(error);
    }

    Ok(WgpuPreparation {
        adapter_name,
        is_hardware,
        scalar_count: scalar_bytes.len(),
        windows,
    })
}

/// Execute a complete, bounded MSM on wgpu for public verifier inputs.
///
/// The device builds radix-16 public-scalar buckets in bounded 64-term chunks,
/// reduces those chunks, collapses the weighted buckets per window, and then
/// performs a short high-to-low radix-16 combination. All four ordered stages
/// stay device-resident and only the final extended point is read back.
/// The returned encoding remains CPU-authoritative: dalek independently
/// computes the same MSM, then validates the GPU coordinates and requires the
/// canonical compressed bytes to agree exactly. This variable-time kernel is
/// for public verifier scalars, never witness-derived prover scalars.
#[cfg(feature = "wgpu-msm")]
pub fn vartime_multiscalar_mul_wgpu(
    scalar_bytes: &[[u8; 32]],
    point_bytes: &[[u8; 32]],
) -> Result<WgpuMsmResult, MsmBackendError> {
    if scalar_bytes.len() != point_bytes.len() {
        return Err(MsmBackendError::LengthMismatch {
            scalars: scalar_bytes.len(),
            points: point_bytes.len(),
        });
    }
    if scalar_bytes.is_empty() {
        return Err(MsmBackendError::EmptyMsm);
    }
    if scalar_bytes.len() > MAX_WGPU_MSM_TERMS {
        return Err(MsmBackendError::TooManyTerms {
            terms: scalar_bytes.len(),
            maximum: MAX_WGPU_MSM_TERMS,
        });
    }

    let (scalars, points) = validate_canonical_inputs(scalar_bytes, point_bytes)?;
    let identity = RistrettoPoint::identity();
    if let Some(index) = points.iter().position(|point| *point == identity) {
        return Err(MsmBackendError::IdentityPoint { index });
    }
    let expected = RistrettoPoint::vartime_multiscalar_mul(&scalars, &points);
    let expected_compressed = expected.compress();

    const WINDOW_BITS: u32 = 4;
    const WINDOW_COUNT: u32 = 256 / WINDOW_BITS;
    const BUCKET_COUNT: u32 = (1 << WINDOW_BITS) - 1;
    const CHUNK_TERMS: u32 = 64;
    const WORKGROUP_SIZE: u32 = 64;
    const ONE_POINT_BYTES: u64 = (4 * 32 * core::mem::size_of::<u32>()) as u64;

    let term_count =
        u32::try_from(scalar_bytes.len()).map_err(|_| MsmBackendError::DimensionOverflow)?;
    let chunk_count = term_count.div_ceil(CHUNK_TERMS);
    let partial_bucket_count = WINDOW_COUNT
        .checked_mul(chunk_count)
        .and_then(|count| count.checked_mul(BUCKET_COUNT))
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let reduced_bucket_count = WINDOW_COUNT
        .checked_mul(BUCKET_COUNT)
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let partial_bucket_bytes = u64::from(partial_bucket_count)
        .checked_mul(ONE_POINT_BYTES)
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let reduced_bucket_bytes = u64::from(reduced_bucket_count)
        .checked_mul(ONE_POINT_BYTES)
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let window_sum_bytes = u64::from(WINDOW_COUNT)
        .checked_mul(ONE_POINT_BYTES)
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let partial_workgroups = partial_bucket_count.div_ceil(WORKGROUP_SIZE);
    let reduced_workgroups = reduced_bucket_count.div_ceil(WORKGROUP_SIZE);
    let coordinate_word_count = scalar_bytes
        .len()
        .checked_mul(4 * 32)
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let coordinate_buffer_bytes = u64::try_from(
        coordinate_word_count
            .checked_mul(core::mem::size_of::<u32>())
            .ok_or(MsmBackendError::DimensionOverflow)?,
    )
    .map_err(|_| MsmBackendError::DimensionOverflow)?;
    let scalar_word_count = scalar_bytes
        .len()
        .checked_mul(32)
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let scalar_buffer_bytes = u64::try_from(
        scalar_word_count
            .checked_mul(core::mem::size_of::<u32>())
            .ok_or(MsmBackendError::DimensionOverflow)?,
    )
    .map_err(|_| MsmBackendError::DimensionOverflow)?;
    let mut coordinate_words = Vec::with_capacity(coordinate_word_count);
    for point in &points {
        for coordinate in point.dregg_extended_coordinates() {
            coordinate_words.extend(coordinate.iter().copied().map(u32::from));
        }
    }
    let mut scalar_words = Vec::with_capacity(scalar_word_count);
    for bytes in scalar_bytes {
        scalar_words.extend(bytes.iter().copied().map(u32::from));
    }
    let mut constant_words = Vec::with_capacity(32 + 4 * 32);
    constant_words.extend(
        RistrettoPoint::dregg_edwards_d2_bytes()
            .iter()
            .copied()
            .map(u32::from),
    );
    for coordinate in identity.dregg_extended_coordinates() {
        constant_words.extend(coordinate.iter().copied().map(u32::from));
    }

    let context = complete_msm_context()?;
    let device = &context.device;
    let queue = &context.queue;
    let limits = &context.limits;
    let storage_limit =
        u64::from(limits.max_storage_buffer_binding_size).min(limits.max_buffer_size);
    if partial_workgroups > limits.max_compute_workgroups_per_dimension
        || reduced_workgroups > limits.max_compute_workgroups_per_dimension
        || coordinate_buffer_bytes > storage_limit
        || scalar_buffer_bytes > storage_limit
        || partial_bucket_bytes > storage_limit
        || reduced_bucket_bytes > storage_limit
        || window_sum_bytes > storage_limit
        || ONE_POINT_BYTES > storage_limit
    {
        coordinate_words.fill(0);
        scalar_words.fill(0);
        return Err(MsmBackendError::DimensionOverflow);
    }

    use wgpu::util::DeviceExt;
    let input_coordinates = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-points"),
        contents: bytemuck::cast_slice(&coordinate_words),
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
    });
    let input_scalars = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-scalars"),
        contents: bytemuck::cast_slice(&scalar_words),
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
    });
    let constants = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-constants"),
        contents: bytemuck::cast_slice(&constant_words),
        usage: wgpu::BufferUsages::STORAGE,
    });
    let partial_buckets = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-partial-buckets"),
        size: partial_bucket_bytes,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let reduced_buckets = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-reduced-buckets"),
        size: reduced_bucket_bytes,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let window_sums = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-window-sums"),
        size: window_sum_bytes,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let result_coordinates = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-result"),
        size: ONE_POINT_BYTES,
        usage: wgpu::BufferUsages::STORAGE
            | wgpu::BufferUsages::COPY_SRC
            | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let readback = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-readback"),
        size: ONE_POINT_BYTES,
        usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
        mapped_at_creation: false,
    });
    let make_metadata = |stage, label| {
        device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some(label),
            contents: bytemuck::cast_slice(&[
                term_count,
                WINDOW_COUNT,
                BUCKET_COUNT,
                chunk_count,
                stage,
                32,
                0,
                0,
            ]),
            usage: wgpu::BufferUsages::UNIFORM,
        })
    };
    let partial_metadata = make_metadata(
        0_u32,
        "bulletproofs-ristretto-complete-msm-partial-metadata",
    );
    let reduce_metadata =
        make_metadata(1_u32, "bulletproofs-ristretto-complete-msm-reduce-metadata");
    let collapse_metadata = make_metadata(
        2_u32,
        "bulletproofs-ristretto-complete-msm-collapse-metadata",
    );
    let combine_metadata = make_metadata(
        3_u32,
        "bulletproofs-ristretto-complete-msm-combine-metadata",
    );

    let partial_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-partial-group"),
        layout: &context.layout,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: partial_metadata.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: input_coordinates.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: constants.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 3,
                resource: partial_buckets.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 4,
                resource: input_scalars.as_entire_binding(),
            },
        ],
    });
    let reduce_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-reduce-group"),
        layout: &context.layout,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: reduce_metadata.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: partial_buckets.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: constants.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 3,
                resource: reduced_buckets.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 4,
                resource: input_scalars.as_entire_binding(),
            },
        ],
    });
    let collapse_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-collapse-group"),
        layout: &context.layout,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: collapse_metadata.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: reduced_buckets.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: constants.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 3,
                resource: window_sums.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 4,
                resource: input_scalars.as_entire_binding(),
            },
        ],
    });
    let combine_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-combine-group"),
        layout: &context.layout,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: combine_metadata.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: window_sums.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: constants.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 3,
                resource: result_coordinates.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 4,
                resource: input_scalars.as_entire_binding(),
            },
        ],
    });

    let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-encoder"),
    });
    {
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some("bulletproofs-ristretto-complete-msm-pass"),
            timestamp_writes: None,
        });
        pass.set_pipeline(&context.pipeline);
        pass.set_bind_group(0, &partial_group, &[]);
        pass.dispatch_workgroups(partial_workgroups, 1, 1);
        pass.set_bind_group(0, &reduce_group, &[]);
        pass.dispatch_workgroups(reduced_workgroups, 1, 1);
        pass.set_bind_group(0, &collapse_group, &[]);
        pass.dispatch_workgroups(1, 1, 1);
        pass.set_bind_group(0, &combine_group, &[]);
        pass.dispatch_workgroups(1, 1, 1);
    }
    encoder.copy_buffer_to_buffer(&result_coordinates, 0, &readback, 0, ONE_POINT_BYTES);
    let started = std::time::Instant::now();
    queue.submit(Some(encoder.finish()));

    let slice = readback.slice(..);
    let (send, receive) = std::sync::mpsc::sync_channel(1);
    slice.map_async(wgpu::MapMode::Read, move |result| {
        let _ = send.send(result);
    });
    device.poll(wgpu::Maintain::Wait);
    let gpu_elapsed_micros = started.elapsed().as_micros();
    match receive.recv() {
        Ok(Ok(())) => {}
        Ok(Err(error)) => {
            clear_buffers(
                &device,
                &queue,
                &[
                    &input_coordinates,
                    &input_scalars,
                    &partial_buckets,
                    &reduced_buckets,
                    &window_sums,
                    &result_coordinates,
                    &readback,
                ],
            );
            coordinate_words.fill(0);
            scalar_words.fill(0);
            return Err(MsmBackendError::WgpuUnavailable(error.to_string()));
        }
        Err(_) => {
            clear_buffers(
                &device,
                &queue,
                &[
                    &input_coordinates,
                    &input_scalars,
                    &partial_buckets,
                    &reduced_buckets,
                    &window_sums,
                    &result_coordinates,
                    &readback,
                ],
            );
            coordinate_words.fill(0);
            scalar_words.fill(0);
            return Err(MsmBackendError::WgpuUnavailable(
                "readback callback was dropped".to_owned(),
            ));
        }
    }

    let mapped = slice.get_mapped_range();
    let gpu_words: &[u32] = bytemuck::cast_slice(&mapped);
    let gpu_coordinates = coordinates_from_words(gpu_words).ok_or(MsmBackendError::WgpuMsmMismatch);
    drop(mapped);
    readback.unmap();
    let parity = gpu_coordinates.and_then(|coordinates| {
        RistrettoPoint::dregg_from_extended_coordinates_checked(&coordinates, &expected_compressed)
            .ok_or(MsmBackendError::WgpuMsmMismatch)
    });
    clear_buffers(
        &device,
        &queue,
        &[
            &input_coordinates,
            &input_scalars,
            &partial_buckets,
            &reduced_buckets,
            &window_sums,
            &result_coordinates,
            &readback,
        ],
    );
    coordinate_words.fill(0);
    scalar_words.fill(0);
    parity?;

    let nonzero_digits = scalar_bytes
        .iter()
        .flat_map(|scalar| scalar.iter())
        .map(|byte| u64::from(byte & 15 != 0) + u64::from(byte >> 4 != 0))
        .sum();
    let bucket_term_tests = u64::from(term_count)
        .checked_mul(u64::from(WINDOW_COUNT))
        .and_then(|count| count.checked_mul(u64::from(BUCKET_COUNT)))
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let post_bucket_addition_upper_bound = u64::from(reduced_bucket_count)
        .checked_mul(u64::from(chunk_count))
        .and_then(|count| count.checked_add(u64::from(WINDOW_COUNT) * u64::from(BUCKET_COUNT) * 2))
        .and_then(|count| count.checked_add(u64::from(WINDOW_COUNT) * u64::from(WINDOW_BITS + 1)))
        .ok_or(MsmBackendError::DimensionOverflow)?;

    Ok(WgpuMsmResult {
        adapter_name: context.adapter_name.clone(),
        is_hardware: context.is_hardware,
        term_count: scalar_bytes.len(),
        compressed_result: expected_compressed.to_bytes(),
        gpu_elapsed_micros,
        window_bits: WINDOW_BITS,
        window_count: WINDOW_COUNT,
        bucket_count: BUCKET_COUNT,
        chunk_count,
        partial_bucket_count,
        bucket_term_tests,
        nonzero_digits,
        post_bucket_addition_upper_bound,
        dispatch_count: 4,
        readback_count: 1,
    })
}

/// Add canonical compressed Ristretto pairs with exact extended-Edwards field
/// arithmetic on wgpu, then accept each result only if dalek validates its
/// coordinates and its compressed bytes equal the CPU sum.
///
/// This is the first actual GPU **group** operation in the backend.  It is an
/// independently testable stone for bucket accumulation, not yet a complete
/// multiscalar multiplication.
#[cfg(feature = "wgpu-msm")]
pub fn add_compressed_point_pairs_wgpu(
    pairs: &[([u8; 32], [u8; 32])],
) -> Result<WgpuPointAddition, MsmBackendError> {
    if pairs.is_empty() {
        return Ok(WgpuPointAddition {
            adapter_name: "no-dispatch(empty)".to_owned(),
            is_hardware: false,
            compressed_sums: Vec::new(),
        });
    }

    let mut input_words = Vec::with_capacity(
        pairs
            .len()
            .checked_mul(2 * 4 * 32)
            .ok_or(MsmBackendError::DimensionOverflow)?,
    );
    let mut expected = Vec::with_capacity(pairs.len());
    for (index, (left_bytes, right_bytes)) in pairs.iter().enumerate() {
        let left = CompressedRistretto(*left_bytes)
            .decompress()
            .filter(|point| point.compress().to_bytes() == *left_bytes)
            .ok_or(MsmBackendError::NonCanonicalPoint { index: index * 2 })?;
        let right = CompressedRistretto(*right_bytes)
            .decompress()
            .filter(|point| point.compress().to_bytes() == *right_bytes)
            .ok_or(MsmBackendError::NonCanonicalPoint {
                index: index * 2 + 1,
            })?;
        for point in [&left, &right] {
            for coordinate in point.dregg_extended_coordinates() {
                input_words.extend(coordinate.iter().copied().map(u32::from));
            }
        }
        expected.push((left + right).compress());
    }

    let d2_words: Vec<u32> = RistrettoPoint::dregg_edwards_d2_bytes()
        .iter()
        .copied()
        .map(u32::from)
        .collect();
    let pair_count = u32::try_from(pairs.len()).map_err(|_| MsmBackendError::DimensionOverflow)?;
    let workgroups = pair_count.div_ceil(64);
    let output_word_count = pairs
        .len()
        .checked_mul(4 * 32)
        .ok_or(MsmBackendError::DimensionOverflow)?;
    let output_bytes = u64::try_from(
        output_word_count
            .checked_mul(core::mem::size_of::<u32>())
            .ok_or(MsmBackendError::DimensionOverflow)?,
    )
    .map_err(|_| MsmBackendError::DimensionOverflow)?;
    let input_bytes = u64::try_from(
        input_words
            .len()
            .checked_mul(core::mem::size_of::<u32>())
            .ok_or(MsmBackendError::DimensionOverflow)?,
    )
    .map_err(|_| MsmBackendError::DimensionOverflow)?;

    let instance = wgpu::Instance::default();
    let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
        power_preference: wgpu::PowerPreference::HighPerformance,
        ..Default::default()
    }))
    .ok_or_else(|| MsmBackendError::WgpuUnavailable("no adapter".to_owned()))?;
    let adapter_info = adapter.get_info();
    let adapter_name = adapter_info.name;
    let is_hardware = !matches!(adapter_info.device_type, wgpu::DeviceType::Cpu);
    let limits = adapter.limits();
    let storage_limit =
        u64::from(limits.max_storage_buffer_binding_size).min(limits.max_buffer_size);
    if workgroups > limits.max_compute_workgroups_per_dimension
        || input_bytes > storage_limit
        || output_bytes > storage_limit
    {
        input_words.fill(0);
        return Err(MsmBackendError::DimensionOverflow);
    }
    let (device, queue) = pollster::block_on(adapter.request_device(
        &wgpu::DeviceDescriptor {
            label: Some("bulletproofs-ristretto-edwards-add-device"),
            required_features: wgpu::Features::empty(),
            required_limits: limits.clone(),
            memory_hints: Default::default(),
        },
        None,
    ))
    .map_err(|error| MsmBackendError::WgpuUnavailable(error.to_string()))?;

    use wgpu::util::DeviceExt;
    let metadata = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-metadata"),
        contents: bytemuck::cast_slice(&[pair_count, 0_u32, 0, 0, 0, 32, 0, 0]),
        usage: wgpu::BufferUsages::UNIFORM,
    });
    let input = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-input"),
        contents: bytemuck::cast_slice(&input_words),
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
    });
    let constants = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-constants"),
        contents: bytemuck::cast_slice(&d2_words),
        usage: wgpu::BufferUsages::STORAGE,
    });
    let output = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-output"),
        size: output_bytes,
        usage: wgpu::BufferUsages::STORAGE
            | wgpu::BufferUsages::COPY_SRC
            | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let readback = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-readback"),
        size: output_bytes,
        usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
        mapped_at_creation: false,
    });

    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-shader"),
        source: wgpu::ShaderSource::Wgsl(include_str!("shaders/edwards_add_radix5.wgsl").into()),
    });
    let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-bind-layout"),
        entries: &[
            buffer_entry(0, wgpu::BufferBindingType::Uniform),
            buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: false }),
        ],
    });
    let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-pipeline-layout"),
        bind_group_layouts: &[&layout],
        push_constant_ranges: &[],
    });
    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-pipeline"),
        layout: Some(&pipeline_layout),
        module: &shader,
        entry_point: Some("main"),
        compilation_options: Default::default(),
        cache: None,
    });
    let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-bind-group"),
        layout: &layout,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: metadata.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: input.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: constants.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 3,
                resource: output.as_entire_binding(),
            },
        ],
    });

    let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("bulletproofs-ristretto-edwards-add-encoder"),
    });
    {
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some("bulletproofs-ristretto-edwards-add-pass"),
            timestamp_writes: None,
        });
        pass.set_pipeline(&pipeline);
        pass.set_bind_group(0, &bind_group, &[]);
        pass.dispatch_workgroups(workgroups, 1, 1);
    }
    encoder.copy_buffer_to_buffer(&output, 0, &readback, 0, output_bytes);
    queue.submit(Some(encoder.finish()));

    let slice = readback.slice(..);
    let (send, receive) = std::sync::mpsc::sync_channel(1);
    slice.map_async(wgpu::MapMode::Read, move |result| {
        let _ = send.send(result);
    });
    device.poll(wgpu::Maintain::Wait);
    match receive.recv() {
        Ok(Ok(())) => {}
        Ok(Err(error)) => {
            clear_secret_buffers(&device, &queue, &input, &output, &readback);
            input_words.fill(0);
            return Err(MsmBackendError::WgpuUnavailable(error.to_string()));
        }
        Err(_) => {
            clear_secret_buffers(&device, &queue, &input, &output, &readback);
            input_words.fill(0);
            return Err(MsmBackendError::WgpuUnavailable(
                "readback callback was dropped".to_owned(),
            ));
        }
    }

    let mapped = slice.get_mapped_range();
    let gpu_words: &[u32] = bytemuck::cast_slice(&mapped);
    if gpu_words.len() != output_word_count {
        drop(mapped);
        readback.unmap();
        clear_secret_buffers(&device, &queue, &input, &output, &readback);
        input_words.fill(0);
        return Err(MsmBackendError::DimensionOverflow);
    }

    let mut compressed_sums = Vec::with_capacity(pairs.len());
    let mut mismatch = None;
    for (index, words) in gpu_words.chunks_exact(4 * 32).enumerate() {
        let mut coordinates: DreggExtendedCoordinates = [[0_u8; 32]; 4];
        for (coordinate_index, coordinate_words) in words.chunks_exact(32).enumerate() {
            for (byte_index, &word) in coordinate_words.iter().enumerate() {
                let Ok(byte) = u8::try_from(word) else {
                    mismatch = Some(MsmBackendError::WgpuPointMismatch { index });
                    break;
                };
                coordinates[coordinate_index][byte_index] = byte;
            }
            if mismatch.is_some() {
                break;
            }
        }
        if mismatch.is_some()
            || RistrettoPoint::dregg_from_extended_coordinates_checked(
                &coordinates,
                &expected[index],
            )
            .is_none()
        {
            mismatch = Some(MsmBackendError::WgpuPointMismatch { index });
            break;
        }
        compressed_sums.push(expected[index].to_bytes());
    }
    drop(mapped);
    readback.unmap();
    clear_secret_buffers(&device, &queue, &input, &output, &readback);
    input_words.fill(0);
    if let Some(error) = mismatch {
        return Err(error);
    }

    Ok(WgpuPointAddition {
        adapter_name,
        is_hardware,
        compressed_sums,
    })
}

#[cfg(feature = "wgpu-msm")]
fn coordinates_from_words(words: &[u32]) -> Option<DreggExtendedCoordinates> {
    if words.len() != 4 * 32 {
        return None;
    }
    let mut coordinates = [[0_u8; 32]; 4];
    for (coordinate_index, coordinate_words) in words.chunks_exact(32).enumerate() {
        for (byte_index, &word) in coordinate_words.iter().enumerate() {
            coordinates[coordinate_index][byte_index] = u8::try_from(word).ok()?;
        }
    }
    Some(coordinates)
}

#[cfg(feature = "wgpu-msm")]
fn clear_buffers(device: &wgpu::Device, queue: &wgpu::Queue, buffers: &[&wgpu::Buffer]) {
    let mut clear = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("bulletproofs-ristretto-complete-msm-clear"),
    });
    for buffer in buffers {
        clear.clear_buffer(buffer, 0, None);
    }
    queue.submit(Some(clear.finish()));
    device.poll(wgpu::Maintain::Wait);
}

#[cfg(feature = "wgpu-msm")]
fn clear_secret_buffers(
    device: &wgpu::Device,
    queue: &wgpu::Queue,
    input: &wgpu::Buffer,
    output: &wgpu::Buffer,
    readback: &wgpu::Buffer,
) {
    let mut clear = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("bulletproofs-ristretto-msm-window-clear"),
    });
    clear.clear_buffer(input, 0, None);
    clear.clear_buffer(output, 0, None);
    clear.clear_buffer(readback, 0, None);
    queue.submit(Some(clear.finish()));
    device.poll(wgpu::Maintain::Wait);
}

#[cfg(feature = "wgpu-msm")]
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

/// Optional verifier MSM dispatch. Dalek always remains the acceptance oracle
/// and output producer; required mode makes any GPU refusal or parity failure
/// a verification error, while auto mode falls back explicitly to dalek.
pub(crate) fn optional_vartime_multiscalar_mul<I, J>(
    scalars: I,
    points: J,
) -> Result<Option<RistrettoPoint>, R1CSError>
where
    I: IntoIterator,
    I::Item: Borrow<Scalar>,
    J: IntoIterator<Item = Option<RistrettoPoint>>,
{
    let scalar_values: Vec<Scalar> = scalars.into_iter().map(|scalar| *scalar.borrow()).collect();
    let point_values: Vec<Option<RistrettoPoint>> = points.into_iter().collect();
    if scalar_values.len() != point_values.len() {
        return Err(r1cs_error(MsmBackendError::LengthMismatch {
            scalars: scalar_values.len(),
            points: point_values.len(),
        }));
    }

    let cpu_result =
        RistrettoPoint::optional_multiscalar_mul(&scalar_values, point_values.iter().copied());
    let policy = wgpu_policy();
    if policy == WgpuPolicy::Disabled || cpu_result.is_none() {
        return Ok(cpu_result);
    }

    #[cfg(feature = "wgpu-msm")]
    {
        // Identity is a valid typed group element and contributes zero to an
        // MSM. Small valid Bulletproofs can contain identity commitments for
        // an unused phase, so remove those terms before crossing the stricter
        // serialized verifier boundary rather than treating them as aliases.
        let non_identity_terms: Vec<(Scalar, RistrettoPoint)> = scalar_values
            .iter()
            .copied()
            .zip(point_values.iter().copied())
            .filter_map(|(scalar, point)| {
                let point = point.expect("CPU optional MSM established every point");
                (point != RistrettoPoint::identity()).then_some((scalar, point))
            })
            .collect();
        let scalar_bytes: Vec<[u8; 32]> = non_identity_terms
            .iter()
            .map(|(scalar, _)| scalar.to_bytes())
            .collect();
        let point_bytes: Vec<[u8; 32]> = non_identity_terms
            .iter()
            .map(|(_, point)| point.compress().to_bytes())
            .collect();
        match vartime_multiscalar_mul_wgpu(&scalar_bytes, &point_bytes) {
            Ok(result) if policy == WgpuPolicy::Required && !result.is_hardware => {
                return Err(r1cs_error(MsmBackendError::WgpuUnavailable(format!(
                    "hard verifier gate selected CPU adapter {}",
                    result.adapter_name
                ))));
            }
            Ok(result) => {
                if Some(result.compressed_result)
                    != cpu_result.as_ref().map(|point| point.compress().to_bytes())
                {
                    return Err(r1cs_error(MsmBackendError::WgpuMsmMismatch));
                }
            }
            Err(error) if policy == WgpuPolicy::Required => return Err(r1cs_error(error)),
            Err(_) => return Ok(cpu_result),
        }
    }
    #[cfg(not(feature = "wgpu-msm"))]
    {
        if policy == WgpuPolicy::Required {
            return Err(r1cs_error(MsmBackendError::WgpuUnavailable(
                "bulletproofs was built without feature `wgpu-msm`".to_owned(),
            )));
        }
    }

    Ok(cpu_result)
}

/// The fork-owned replacement for the six R1CS prover MSM calls.
///
/// `DREGG_BULLETPROOFS_WGPU=auto` requests the exact GPU preparation with an
/// explicit CPU fallback. `DREGG_BULLETPROOFS_WGPU=1|required` or
/// `DREGG_REQUIRE_WGPU=1` makes any missing feature, adapter, dispatch error,
/// or parity mismatch fail the proof. In every current mode dalek remains the
/// group-operation oracle and output producer.
pub(crate) fn multiscalar_mul<I, J>(scalars: I, points: J) -> Result<RistrettoPoint, R1CSError>
where
    I: IntoIterator,
    I::Item: Borrow<Scalar>,
    J: IntoIterator,
    J::Item: Borrow<RistrettoPoint>,
{
    let policy = wgpu_policy();
    if policy == WgpuPolicy::Disabled {
        return Ok(RistrettoPoint::multiscalar_mul(scalars, points));
    }

    let scalar_values: Vec<Scalar> = scalars.into_iter().map(|s| *s.borrow()).collect();
    let point_values: Vec<RistrettoPoint> = points.into_iter().map(|p| *p.borrow()).collect();
    if scalar_values.len() != point_values.len() {
        return Err(r1cs_error(MsmBackendError::LengthMismatch {
            scalars: scalar_values.len(),
            points: point_values.len(),
        }));
    }

    #[cfg(feature = "wgpu-msm")]
    {
        let mut scalar_bytes: Vec<[u8; 32]> = scalar_values.iter().map(Scalar::to_bytes).collect();
        let preparation = prepare_scalar_windows_wgpu(&scalar_bytes);
        scalar_bytes.iter_mut().for_each(|bytes| bytes.fill(0));
        match preparation {
            Ok(prepared) if policy == WgpuPolicy::Required && !prepared.is_hardware => {
                return Err(r1cs_error(MsmBackendError::WgpuUnavailable(format!(
                    "hard gate selected CPU adapter {}",
                    prepared.adapter_name
                ))));
            }
            Ok(_) => {}
            Err(error) if policy == WgpuPolicy::Required => return Err(r1cs_error(error)),
            Err(_) => {
                return Ok(RistrettoPoint::multiscalar_mul(
                    &scalar_values,
                    &point_values,
                ))
            }
        }
    }
    #[cfg(not(feature = "wgpu-msm"))]
    {
        if policy == WgpuPolicy::Required {
            return Err(r1cs_error(MsmBackendError::WgpuUnavailable(
                "bulletproofs was built without feature `wgpu-msm`".to_owned(),
            )));
        }
    }

    Ok(RistrettoPoint::multiscalar_mul(
        &scalar_values,
        &point_values,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;

    #[test]
    fn canonical_boundary_rejects_scalar_and_point_aliases() {
        let scalar = Scalar::from(7_u64);
        let point = (Scalar::from(9_u64) * RISTRETTO_BASEPOINT_POINT)
            .compress()
            .to_bytes();
        assert!(validate_canonical_inputs(&[scalar.to_bytes()], &[point]).is_ok());

        // The group order L itself is not a canonical scalar encoding.
        let l = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x10,
        ];
        assert_eq!(
            validate_canonical_inputs(&[l], &[point]),
            Err(MsmBackendError::NonCanonicalScalar { index: 0 })
        );

        let invalid_point = [0xff; 32];
        assert_eq!(
            validate_canonical_inputs(&[scalar.to_bytes()], &[invalid_point]),
            Err(MsmBackendError::NonCanonicalPoint { index: 0 })
        );
    }
}

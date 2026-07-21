//! Owned Ristretto MSM dispatch seam for the R1CS prover.
//!
//! Upstream Bulletproofs hard-codes six calls to dalek's constant-time MSM in
//! `r1cs::Prover::prove`: the `(A_I, A_O, S)` commitments in each of the two
//! proving phases.  This module is the single replacement point for those
//! calls.
//!
//! The first backend stage is intentionally modest and precisely named.  It
//! sends every secret scalar to a portable wgpu compute shader, derives the
//! unsigned radix-256 Pippenger windows there, reads them back, and compares
//! every byte with the CPU definition before dalek performs the group MSM.
//! It does **not** claim that the Edwards bucket accumulation is on the GPU
//! yet.  That next step can replace the last line of [`multiscalar_mul`]
//! without touching the transcript or the six proof call sites again.
//!
//! These prover scalars are witness-derived.  An eventual bucket kernel must
//! therefore use a constant-work/constant-address construction (or explicitly
//! place the GPU and its side channels inside the prover's trust boundary).
//! Ordinary public-scalar verifier MSMs may use variable-time Pippenger.

use core::borrow::Borrow;
use std::convert::{TryFrom, TryInto};

use curve25519_dalek::ristretto::{CompressedRistretto, DreggExtendedCoordinates, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use crate::errors::R1CSError;

/// The number of aligned radix-256 windows in a canonical 32-byte scalar.
pub const RADIX_256_WINDOWS: usize = 32;

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

/// Fail-closed input or GPU error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MsmBackendError {
    /// Scalar and point sequences had different lengths.
    LengthMismatch { scalars: usize, points: usize },
    /// A serialized scalar was not canonical modulo the Ristretto group order.
    NonCanonicalScalar { index: usize },
    /// A serialized Ristretto point did not canonically decompress.
    NonCanonicalPoint { index: usize },
    /// No usable hardware/software wgpu adapter was available.
    WgpuUnavailable(String),
    /// The shader output disagreed with exact CPU radix-256 decomposition.
    WgpuParityMismatch { scalar: usize, window: usize },
    /// A GPU extended-coordinate result was malformed, off-curve, or did not
    /// compress to the exact dalek sum.
    WgpuPointMismatch { index: usize },
    /// Input dimensions overflowed a checked host or device limit.
    DimensionOverflow,
}

impl core::fmt::Display for MsmBackendError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::LengthMismatch { scalars, points } => {
                write!(f, "MSM length mismatch: {scalars} scalars, {points} points")
            }
            Self::NonCanonicalScalar { index } => {
                write!(f, "non-canonical Ristretto scalar at index {index}")
            }
            Self::NonCanonicalPoint { index } => {
                write!(f, "non-canonical Ristretto point at index {index}")
            }
            Self::WgpuUnavailable(reason) => write!(f, "wgpu MSM backend unavailable: {reason}"),
            Self::WgpuParityMismatch { scalar, window } => write!(
                f,
                "wgpu scalar-window mismatch at scalar {scalar}, window {window}"
            ),
            Self::WgpuPointMismatch { index } => {
                write!(f, "wgpu extended-Edwards sum mismatch at pair {index}")
            }
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
        contents: bytemuck::cast_slice(&[pair_count, 0_u32, 0, 0]),
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

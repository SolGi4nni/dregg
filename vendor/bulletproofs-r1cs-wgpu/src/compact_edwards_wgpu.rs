//! Qualification-only compact-field Edwards arithmetic on WGPU.
//!
//! This module accepts only public canonical Ristretto points and returns a
//! result only after dalek independently checks the extended coordinates and
//! exact compressed sum. It is intentionally not wired into the inner-product
//! prover and exposes no scalar input.

use core::convert::TryFrom;

use curve25519_dalek::ristretto::{CompressedRistretto, DreggExtendedCoordinates, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;

/// Radix-`2^13` limbs in one canonical field element.
pub const COMPACT_FIELD_LIMBS: usize = 20;
/// Bytes occupied by one compact extended Edwards point on the device.
pub const COMPACT_POINT_BYTES: u64 = (4 * COMPACT_FIELD_LIMBS * 4) as u64;
/// Workgroup width of the qualification point-add kernel.
pub const COMPACT_ADD_WORKGROUP_SIZE: u32 = 64;
/// Default executable ceiling. Production-size checks use geometry only.
pub const MAX_COMPACT_EXECUTION_PAIRS: usize = 4096;
/// Default point ceiling for the resident qualification fold.
pub const MAX_COMPACT_RESIDENT_POINTS: usize = 4096;
/// Explicit opt-in required before the public tooth allocates above 4,096 pairs.
pub const GIANT_PUBLIC_BUFFER_ENV: &str = "DREGG_WGPU_ALLOW_GIANT_PUBLIC_POINT_BUFFERS";

/// Actual-adapter geometry for a compact pointwise addition/fold dispatch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompactEdwardsGeometry {
    /// Adapter selected by WGPU.
    pub adapter_name: String,
    /// `false` denotes a software/CPU adapter.
    pub is_hardware: bool,
    /// Number of input point pairs and output points.
    pub pair_count: usize,
    /// Two compact extended points per pair.
    pub input_bytes: u64,
    /// One compact extended output point per pair.
    pub output_bytes: u64,
    /// One-dimensional dispatch width.
    pub workgroups: u32,
    /// Effective per-binding byte ceiling.
    pub storage_binding_limit: u64,
    /// Adapter one-dimensional workgroup ceiling.
    pub workgroup_limit: u32,
    /// Whether all individual bindings and the dispatch fit this adapter.
    pub fits_adapter_limits: bool,
}

/// Exact compact-field GPU point-add result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompactWgpuPointAddition {
    /// Adapter selected by WGPU.
    pub adapter_name: String,
    /// `false` denotes a software/CPU adapter.
    pub is_hardware: bool,
    /// Canonical compressed sums, independently matched to dalek.
    pub compressed_sums: Vec<[u8; 32]>,
}

/// Exact final state of a predetermined-public, device-resident fold.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompactPublicFoldResult {
    /// Adapter selected by WGPU.
    pub adapter_name: String,
    /// `false` denotes a software/CPU adapter.
    pub is_hardware: bool,
    /// Canonical public points uploaded before the first round.
    pub initial_point_count: usize,
    /// Canonical public points left after all rounds.
    pub final_point_count: usize,
    /// Number of ordered dependent fold dispatches.
    pub round_count: usize,
    /// Initial point-vector uploads. Always one for a non-empty fold.
    pub point_upload_count: u32,
    /// Predetermined challenge-vector uploads. Always one.
    pub challenge_upload_count: u32,
    /// Padded per-round control-table uploads. Always one.
    pub control_upload_count: u32,
    /// Ordered device dispatches. Exactly `round_count`.
    pub dispatch_count: u32,
    /// Device-to-host result readbacks. Always one.
    pub readback_count: u32,
    /// Final canonical points, independently matched to the dalek fold.
    pub compressed_points: Vec<[u8; 32]>,
}

/// Fail-closed compact qualification error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompactEdwardsError {
    /// A resident fold needs at least one public point and one round.
    EmptyFold,
    /// Each round consumes equal left and right halves.
    InvalidFoldShape { points: usize, rounds: usize },
    /// The ordinary executable tooth refuses an unexpectedly large allocation.
    TooManyPairs { pairs: usize, maximum: usize },
    /// The ordinary resident tooth refuses an unexpectedly large allocation.
    TooManyPoints { points: usize, maximum: usize },
    /// A serialized Ristretto point did not canonically round-trip.
    NonCanonicalPoint { index: usize },
    /// The selected adapter or device could not be used.
    WgpuUnavailable(String),
    /// A checked host or adapter dimension was exceeded.
    DimensionOverflow,
    /// GPU coordinates were malformed or differed from dalek's exact sum.
    WgpuPointMismatch { index: usize },
}

impl core::fmt::Display for CompactEdwardsError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyFold => write!(
                f,
                "resident public fold needs points and at least one round"
            ),
            Self::InvalidFoldShape { points, rounds } => write!(
                f,
                "{points} public points cannot be halved exactly for {rounds} rounds"
            ),
            Self::TooManyPairs { pairs, maximum } => write!(
                f,
                "compact Edwards dispatch has {pairs} pairs; default maximum is {maximum}"
            ),
            Self::TooManyPoints { points, maximum } => write!(
                f,
                "compact resident fold has {points} points; default maximum is {maximum}"
            ),
            Self::NonCanonicalPoint { index } => {
                write!(f, "non-canonical Ristretto point at index {index}")
            }
            Self::WgpuUnavailable(reason) => {
                write!(f, "compact Edwards WGPU backend unavailable: {reason}")
            }
            Self::DimensionOverflow => {
                write!(
                    f,
                    "compact Edwards dimensions exceed checked adapter limits"
                )
            }
            Self::WgpuPointMismatch { index } => {
                write!(f, "compact Edwards GPU sum mismatch at pair {index}")
            }
        }
    }
}

impl std::error::Error for CompactEdwardsError {}

struct CompactEdwardsContext {
    adapter_name: String,
    is_hardware: bool,
    limits: wgpu::Limits,
    device: wgpu::Device,
    queue: wgpu::Queue,
    layout: wgpu::BindGroupLayout,
    pipeline: wgpu::ComputePipeline,
}

struct CompactPublicFoldContext {
    adapter_name: String,
    is_hardware: bool,
    limits: wgpu::Limits,
    device: wgpu::Device,
    queue: wgpu::Queue,
    layout: wgpu::BindGroupLayout,
    pipeline: wgpu::ComputePipeline,
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

fn compact_context() -> Result<&'static CompactEdwardsContext, CompactEdwardsError> {
    static CONTEXT: std::sync::OnceLock<Result<CompactEdwardsContext, String>> =
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
                    label: Some("bulletproofs-compact-edwards-device"),
                    required_features: wgpu::Features::empty(),
                    required_limits: limits.clone(),
                    memory_hints: Default::default(),
                },
                None,
            ))
            .map_err(|error| error.to_string())?;
            let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("bulletproofs-compact-edwards-radix13-shader"),
                source: wgpu::ShaderSource::Wgsl(
                    include_str!("shaders/edwards_add_radix13.wgsl").into(),
                ),
            });
            let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("bulletproofs-compact-edwards-bind-layout"),
                entries: &[
                    buffer_entry(0, wgpu::BufferBindingType::Uniform),
                    buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
                    buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
                    buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: false }),
                ],
            });
            let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("bulletproofs-compact-edwards-pipeline-layout"),
                bind_group_layouts: &[&layout],
                push_constant_ranges: &[],
            });
            let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("bulletproofs-compact-edwards-pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some("main"),
                compilation_options: Default::default(),
                cache: None,
            });
            Ok(CompactEdwardsContext {
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
        .map_err(|reason| CompactEdwardsError::WgpuUnavailable(reason.clone()))
}

fn public_fold_context() -> Result<&'static CompactPublicFoldContext, CompactEdwardsError> {
    static CONTEXT: std::sync::OnceLock<Result<CompactPublicFoldContext, String>> =
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
                    label: Some("bulletproofs-compact-public-fold-device"),
                    required_features: wgpu::Features::empty(),
                    required_limits: limits.clone(),
                    memory_hints: Default::default(),
                },
                None,
            ))
            .map_err(|error| error.to_string())?;
            let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("bulletproofs-compact-public-fold-radix13-shader"),
                source: wgpu::ShaderSource::Wgsl(
                    include_str!("shaders/edwards_public_fold_radix13.wgsl").into(),
                ),
            });
            let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("bulletproofs-compact-public-fold-bind-layout"),
                entries: &[
                    buffer_entry(0, wgpu::BufferBindingType::Uniform),
                    buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
                    buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
                    buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
                    buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: false }),
                ],
            });
            let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("bulletproofs-compact-public-fold-pipeline-layout"),
                bind_group_layouts: &[&layout],
                push_constant_ranges: &[],
            });
            let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("bulletproofs-compact-public-fold-pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some("main"),
                compilation_options: Default::default(),
                cache: None,
            });
            Ok(CompactPublicFoldContext {
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
        .map_err(|reason| CompactEdwardsError::WgpuUnavailable(reason.clone()))
}

fn checked_geometry(
    context: &CompactEdwardsContext,
    pair_count: usize,
) -> Result<CompactEdwardsGeometry, CompactEdwardsError> {
    let pair_count_u32 =
        u32::try_from(pair_count).map_err(|_| CompactEdwardsError::DimensionOverflow)?;
    let input_bytes = u64::try_from(pair_count)
        .ok()
        .and_then(|pairs| pairs.checked_mul(2 * COMPACT_POINT_BYTES))
        .ok_or(CompactEdwardsError::DimensionOverflow)?;
    let output_bytes = u64::try_from(pair_count)
        .ok()
        .and_then(|pairs| pairs.checked_mul(COMPACT_POINT_BYTES))
        .ok_or(CompactEdwardsError::DimensionOverflow)?;
    let workgroups = pair_count_u32.div_ceil(COMPACT_ADD_WORKGROUP_SIZE);
    let storage_binding_limit = u64::from(context.limits.max_storage_buffer_binding_size)
        .min(context.limits.max_buffer_size);
    let workgroup_limit = context.limits.max_compute_workgroups_per_dimension;
    Ok(CompactEdwardsGeometry {
        adapter_name: context.adapter_name.clone(),
        is_hardware: context.is_hardware,
        pair_count,
        input_bytes,
        output_bytes,
        workgroups,
        storage_binding_limit,
        workgroup_limit,
        fits_adapter_limits: input_bytes <= storage_binding_limit
            && output_bytes <= storage_binding_limit
            && workgroups <= workgroup_limit,
    })
}

/// Check compact pointwise geometry against the actual selected adapter.
///
/// This compiles the small pipeline but performs no point-buffer allocation,
/// so production `2^21` geometry can be gated without allocating gigabytes.
pub fn compact_edwards_geometry_wgpu(
    pair_count: usize,
) -> Result<CompactEdwardsGeometry, CompactEdwardsError> {
    checked_geometry(compact_context()?, pair_count)
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

fn compact_limbs(bytes: &[u8; 32]) -> [u32; COMPACT_FIELD_LIMBS] {
    let mut limbs = [0_u32; COMPACT_FIELD_LIMBS];
    for (limb_index, limb) in limbs.iter_mut().enumerate() {
        let bit_index = limb_index * 13;
        let byte_index = bit_index / 8;
        let shift = bit_index % 8;
        let mut word = 0_u32;
        for offset in 0..3 {
            if let Some(byte) = bytes.get(byte_index + offset) {
                word |= u32::from(*byte) << (offset * 8);
            }
        }
        *limb = (word >> shift) & 0x1fff;
    }
    limbs
}

fn canonical_field_bytes(bytes: &[u8; 32]) -> bool {
    const P: [u8; 32] = [
        0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ];
    for index in (0..32).rev() {
        if bytes[index] < P[index] {
            return true;
        }
        if bytes[index] > P[index] {
            return false;
        }
    }
    false
}

fn field_bytes_from_compact(words: &[u32]) -> Option<[u8; 32]> {
    if words.len() != COMPACT_FIELD_LIMBS
        || words[..COMPACT_FIELD_LIMBS - 1]
            .iter()
            .any(|&limb| limb > 0x1fff)
        || words[COMPACT_FIELD_LIMBS - 1] > 0xff
    {
        return None;
    }
    let mut bytes = [0_u8; 32];
    for (limb_index, &limb) in words.iter().enumerate() {
        let bit_index = limb_index * 13;
        let byte_index = bit_index / 8;
        let shift = bit_index % 8;
        let shifted = u64::from(limb) << shift;
        for offset in 0..3 {
            if let Some(byte) = bytes.get_mut(byte_index + offset) {
                *byte |= ((shifted >> (offset * 8)) & 0xff) as u8;
            }
        }
    }
    canonical_field_bytes(&bytes).then_some(bytes)
}

fn coordinates_from_compact(words: &[u32]) -> Option<DreggExtendedCoordinates> {
    if words.len() != 4 * COMPACT_FIELD_LIMBS {
        return None;
    }
    let mut coordinates = [[0_u8; 32]; 4];
    for (coordinate, limbs) in coordinates
        .iter_mut()
        .zip(words.chunks_exact(COMPACT_FIELD_LIMBS))
    {
        *coordinate = field_bytes_from_compact(limbs)?;
    }
    Some(coordinates)
}

fn clear_public_buffers(device: &wgpu::Device, queue: &wgpu::Queue, buffers: &[&wgpu::Buffer]) {
    let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("bulletproofs-compact-edwards-clear"),
    });
    for buffer in buffers {
        encoder.clear_buffer(buffer, 0, None);
    }
    queue.submit(Some(encoder.finish()));
    device.poll(wgpu::Maintain::Wait);
}

/// Add canonical public Ristretto point pairs with compact WGPU field
/// arithmetic, accepting each output only after exact dalek parity.
pub fn add_compressed_point_pairs_compact_wgpu(
    pairs: &[([u8; 32], [u8; 32])],
) -> Result<CompactWgpuPointAddition, CompactEdwardsError> {
    if pairs.is_empty() {
        return Ok(CompactWgpuPointAddition {
            adapter_name: "no-dispatch(empty)".to_owned(),
            is_hardware: false,
            compressed_sums: Vec::new(),
        });
    }
    if pairs.len() > MAX_COMPACT_EXECUTION_PAIRS && !env_true(GIANT_PUBLIC_BUFFER_ENV) {
        return Err(CompactEdwardsError::TooManyPairs {
            pairs: pairs.len(),
            maximum: MAX_COMPACT_EXECUTION_PAIRS,
        });
    }

    let mut input_words = Vec::with_capacity(
        pairs
            .len()
            .checked_mul(2 * 4 * COMPACT_FIELD_LIMBS)
            .ok_or(CompactEdwardsError::DimensionOverflow)?,
    );
    let mut expected = Vec::with_capacity(pairs.len());
    for (index, (left_bytes, right_bytes)) in pairs.iter().enumerate() {
        let left = CompressedRistretto(*left_bytes)
            .decompress()
            .filter(|point| point.compress().to_bytes() == *left_bytes)
            .ok_or(CompactEdwardsError::NonCanonicalPoint { index: index * 2 })?;
        let right = CompressedRistretto(*right_bytes)
            .decompress()
            .filter(|point| point.compress().to_bytes() == *right_bytes)
            .ok_or(CompactEdwardsError::NonCanonicalPoint {
                index: index * 2 + 1,
            })?;
        for point in [&left, &right] {
            for coordinate in point.dregg_extended_coordinates() {
                input_words.extend(compact_limbs(&coordinate));
            }
        }
        expected.push((left + right).compress());
    }

    let context = compact_context()?;
    let geometry = checked_geometry(context, pairs.len())?;
    if !geometry.fits_adapter_limits {
        input_words.fill(0);
        return Err(CompactEdwardsError::DimensionOverflow);
    }

    let mut d2_words = Vec::with_capacity(COMPACT_FIELD_LIMBS);
    d2_words.extend(compact_limbs(&RistrettoPoint::dregg_edwards_d2_bytes()));
    let pair_count =
        u32::try_from(pairs.len()).map_err(|_| CompactEdwardsError::DimensionOverflow)?;
    let output_word_count = pairs
        .len()
        .checked_mul(4 * COMPACT_FIELD_LIMBS)
        .ok_or(CompactEdwardsError::DimensionOverflow)?;

    use wgpu::util::DeviceExt;
    let device = &context.device;
    let queue = &context.queue;
    let metadata = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-compact-edwards-metadata"),
        contents: bytemuck::cast_slice(&[pair_count, 0_u32, 0, 0]),
        usage: wgpu::BufferUsages::UNIFORM,
    });
    let input = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-compact-edwards-input"),
        contents: bytemuck::cast_slice(&input_words),
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
    });
    let constants = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-compact-edwards-constants"),
        contents: bytemuck::cast_slice(&d2_words),
        usage: wgpu::BufferUsages::STORAGE,
    });
    let output = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-compact-edwards-output"),
        size: geometry.output_bytes,
        usage: wgpu::BufferUsages::STORAGE
            | wgpu::BufferUsages::COPY_SRC
            | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let readback = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-compact-edwards-readback"),
        size: geometry.output_bytes,
        usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
        mapped_at_creation: false,
    });
    let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("bulletproofs-compact-edwards-bind-group"),
        layout: &context.layout,
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
        label: Some("bulletproofs-compact-edwards-encoder"),
    });
    {
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some("bulletproofs-compact-edwards-pass"),
            timestamp_writes: None,
        });
        pass.set_pipeline(&context.pipeline);
        pass.set_bind_group(0, &bind_group, &[]);
        pass.dispatch_workgroups(geometry.workgroups, 1, 1);
    }
    encoder.copy_buffer_to_buffer(&output, 0, &readback, 0, geometry.output_bytes);
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
            clear_public_buffers(device, queue, &[&input, &output, &readback]);
            input_words.fill(0);
            return Err(CompactEdwardsError::WgpuUnavailable(error.to_string()));
        }
        Err(_) => {
            clear_public_buffers(device, queue, &[&input, &output, &readback]);
            input_words.fill(0);
            return Err(CompactEdwardsError::WgpuUnavailable(
                "readback callback was dropped".to_owned(),
            ));
        }
    }

    let mapped = slice.get_mapped_range();
    let gpu_words: &[u32] = bytemuck::cast_slice(&mapped);
    if gpu_words.len() != output_word_count {
        drop(mapped);
        readback.unmap();
        clear_public_buffers(device, queue, &[&input, &output, &readback]);
        input_words.fill(0);
        return Err(CompactEdwardsError::DimensionOverflow);
    }

    let mut compressed_sums = Vec::with_capacity(pairs.len());
    let mut mismatch = None;
    for (index, words) in gpu_words.chunks_exact(4 * COMPACT_FIELD_LIMBS).enumerate() {
        let Some(coordinates) = coordinates_from_compact(words) else {
            mismatch = Some(CompactEdwardsError::WgpuPointMismatch { index });
            break;
        };
        if RistrettoPoint::dregg_from_extended_coordinates_checked(&coordinates, &expected[index])
            .is_none()
        {
            mismatch = Some(CompactEdwardsError::WgpuPointMismatch { index });
            break;
        }
        compressed_sums.push(expected[index].to_bytes());
    }
    drop(mapped);
    readback.unmap();
    clear_public_buffers(device, queue, &[&input, &output, &readback]);
    input_words.fill(0);
    if let Some(error) = mismatch {
        return Err(error);
    }

    Ok(CompactWgpuPointAddition {
        adapter_name: context.adapter_name.clone(),
        is_hardware: context.is_hardware,
        compressed_sums,
    })
}

/// Return the fixed public scalar pair used by each qualification fold round.
///
/// Round `r` uses `(u_r^-1, u_r)`. The `u_r` values are nonzero scalars derived
/// from this source-level public domain, not prover witnesses or transcript
/// state. The resident API accepts no caller-supplied scalar material.
pub fn predetermined_public_fold_challenges(round_count: usize) -> Vec<([u8; 32], [u8; 32])> {
    const DOMAIN: u64 = 0x4452_4547_4750_5542;
    const STEP: u64 = 0x9e37_79b9_7f4a_7c15;
    (0..round_count)
        .map(|round| {
            let public_word =
                DOMAIN.wrapping_add((round as u64).wrapping_add(1).wrapping_mul(STEP)) | 1;
            let challenge = Scalar::from(public_word);
            (challenge.invert().to_bytes(), challenge.to_bytes())
        })
        .collect()
}

/// Fold canonical public points through fixed public challenges while keeping
/// all intermediate vectors device-resident.
///
/// The initial compact point vector, complete public challenge table, and
/// padded public control table are each uploaded once. Exactly `round_count`
/// dependent dispatches alternate two resident point buffers; only the final
/// compact vector is read back. Dalek independently performs the same complete
/// fold and remains the acceptance oracle for every returned point.
///
/// This qualification API deliberately accepts no scalar argument and is not
/// wired into the Bulletproof inner-product prover.
pub fn fold_points_with_predetermined_public_challenges_compact_wgpu(
    point_bytes: &[[u8; 32]],
    round_count: usize,
) -> Result<CompactPublicFoldResult, CompactEdwardsError> {
    if point_bytes.is_empty() || round_count == 0 {
        return Err(CompactEdwardsError::EmptyFold);
    }
    let divisor = 1_usize
        .checked_shl(u32::try_from(round_count).map_err(|_| {
            CompactEdwardsError::InvalidFoldShape {
                points: point_bytes.len(),
                rounds: round_count,
            }
        })?)
        .ok_or(CompactEdwardsError::InvalidFoldShape {
            points: point_bytes.len(),
            rounds: round_count,
        })?;
    if point_bytes.len() % divisor != 0 {
        return Err(CompactEdwardsError::InvalidFoldShape {
            points: point_bytes.len(),
            rounds: round_count,
        });
    }
    if point_bytes.len() > MAX_COMPACT_RESIDENT_POINTS && !env_true(GIANT_PUBLIC_BUFFER_ENV) {
        return Err(CompactEdwardsError::TooManyPoints {
            points: point_bytes.len(),
            maximum: MAX_COMPACT_RESIDENT_POINTS,
        });
    }

    let challenges = predetermined_public_fold_challenges(round_count);
    let typed_challenges: Vec<(Scalar, Scalar)> = challenges
        .iter()
        .map(|(left, right)| {
            (
                Option::<Scalar>::from(Scalar::from_canonical_bytes(*left))
                    .expect("fixed inverse challenge is canonical"),
                Option::<Scalar>::from(Scalar::from_canonical_bytes(*right))
                    .expect("fixed challenge is canonical"),
            )
        })
        .collect();
    let mut expected = Vec::with_capacity(point_bytes.len());
    let mut input_words = Vec::with_capacity(
        point_bytes
            .len()
            .checked_mul(4 * COMPACT_FIELD_LIMBS)
            .ok_or(CompactEdwardsError::DimensionOverflow)?,
    );
    for (index, bytes) in point_bytes.iter().enumerate() {
        let point = CompressedRistretto(*bytes)
            .decompress()
            .filter(|point| point.compress().to_bytes() == *bytes)
            .ok_or(CompactEdwardsError::NonCanonicalPoint { index })?;
        for coordinate in point.dregg_extended_coordinates() {
            input_words.extend(compact_limbs(&coordinate));
        }
        expected.push(point);
    }
    for (left_scalar, right_scalar) in &typed_challenges {
        let half = expected.len() / 2;
        expected = (0..half)
            .map(|index| *left_scalar * expected[index] + *right_scalar * expected[index + half])
            .collect();
    }

    let context = public_fold_context()?;
    let device = &context.device;
    let queue = &context.queue;
    let storage_limit = u64::from(context.limits.max_storage_buffer_binding_size)
        .min(context.limits.max_buffer_size);
    let point_buffer_bytes = u64::try_from(point_bytes.len())
        .ok()
        .and_then(|count| count.checked_mul(COMPACT_POINT_BYTES))
        .ok_or(CompactEdwardsError::DimensionOverflow)?;
    let final_point_count = point_bytes.len() / divisor;
    let final_bytes = u64::try_from(final_point_count)
        .ok()
        .and_then(|count| count.checked_mul(COMPACT_POINT_BYTES))
        .ok_or(CompactEdwardsError::DimensionOverflow)?;
    let challenge_word_count = round_count
        .checked_mul(2 * 32)
        .ok_or(CompactEdwardsError::DimensionOverflow)?;
    let challenge_bytes = u64::try_from(challenge_word_count)
        .ok()
        .and_then(|count| count.checked_mul(4))
        .ok_or(CompactEdwardsError::DimensionOverflow)?;
    let first_output_count = point_bytes.len() / 2;
    let first_workgroups = u32::try_from(first_output_count)
        .map_err(|_| CompactEdwardsError::DimensionOverflow)?
        .div_ceil(COMPACT_ADD_WORKGROUP_SIZE);
    if point_buffer_bytes > storage_limit
        || challenge_bytes > storage_limit
        || first_workgroups > context.limits.max_compute_workgroups_per_dimension
    {
        input_words.fill(0);
        return Err(CompactEdwardsError::DimensionOverflow);
    }

    let mut challenge_words = Vec::with_capacity(challenge_word_count);
    for (left, right) in &challenges {
        challenge_words.extend(left.iter().copied().map(u32::from));
        challenge_words.extend(right.iter().copied().map(u32::from));
    }
    let alignment = usize::try_from(context.limits.min_uniform_buffer_offset_alignment)
        .map_err(|_| CompactEdwardsError::DimensionOverflow)?
        .max(16);
    let metadata_stride = alignment.div_ceil(4) * 4;
    let metadata_words_per_round = metadata_stride / 4;
    let mut metadata_words = vec![0_u32; round_count * metadata_words_per_round];
    for round in 0..round_count {
        let output_count = point_bytes.len() >> (round + 1);
        let base = round * metadata_words_per_round;
        metadata_words[base] =
            u32::try_from(output_count).map_err(|_| CompactEdwardsError::DimensionOverflow)?;
        metadata_words[base + 1] =
            u32::try_from(round).map_err(|_| CompactEdwardsError::DimensionOverflow)?;
    }

    use wgpu::util::DeviceExt;
    let metadata = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-compact-public-fold-control"),
        contents: bytemuck::cast_slice(&metadata_words),
        usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
    });
    let point_a = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-compact-public-fold-points-a"),
        contents: bytemuck::cast_slice(&input_words),
        usage: wgpu::BufferUsages::STORAGE
            | wgpu::BufferUsages::COPY_DST
            | wgpu::BufferUsages::COPY_SRC,
    });
    let point_b = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-compact-public-fold-points-b"),
        size: point_buffer_bytes,
        usage: wgpu::BufferUsages::STORAGE
            | wgpu::BufferUsages::COPY_DST
            | wgpu::BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let constants_words = compact_limbs(&RistrettoPoint::dregg_edwards_d2_bytes());
    let constants = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-compact-public-fold-constants"),
        contents: bytemuck::cast_slice(&constants_words),
        usage: wgpu::BufferUsages::STORAGE,
    });
    let public_challenges = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("bulletproofs-compact-public-fold-challenges"),
        contents: bytemuck::cast_slice(&challenge_words),
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
    });
    let readback = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("bulletproofs-compact-public-fold-readback"),
        size: final_bytes,
        usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
        mapped_at_creation: false,
    });

    let metadata_binding_size =
        wgpu::BufferSize::new(16).expect("nonzero fixed-size public fold metadata binding");
    let mut bind_groups = Vec::with_capacity(round_count);
    for round in 0..round_count {
        let (input, output) = if round % 2 == 0 {
            (&point_a, &point_b)
        } else {
            (&point_b, &point_a)
        };
        bind_groups.push(device.create_bind_group(
            &wgpu::BindGroupDescriptor {
                label: Some("bulletproofs-compact-public-fold-bind-group"),
                layout: &context.layout,
                entries:
                    &[
                        wgpu::BindGroupEntry {
                            binding: 0,
                            resource:
                                wgpu::BindingResource::Buffer(
                                    wgpu::BufferBinding {
                                        buffer: &metadata,
                                        offset:
                                            u64::try_from(round * metadata_stride).map_err(
                                                |_| CompactEdwardsError::DimensionOverflow,
                                            )?,
                                        size: Some(metadata_binding_size),
                                    },
                                ),
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
                            resource: public_challenges.as_entire_binding(),
                        },
                        wgpu::BindGroupEntry {
                            binding: 4,
                            resource: output.as_entire_binding(),
                        },
                    ],
            },
        ));
    }

    let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("bulletproofs-compact-public-fold-encoder"),
    });
    for (round, bind_group) in bind_groups.iter().enumerate() {
        let output_count = point_bytes.len() >> (round + 1);
        let workgroups = u32::try_from(output_count)
            .map_err(|_| CompactEdwardsError::DimensionOverflow)?
            .div_ceil(COMPACT_ADD_WORKGROUP_SIZE);
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some("bulletproofs-compact-public-fold-pass"),
            timestamp_writes: None,
        });
        pass.set_pipeline(&context.pipeline);
        pass.set_bind_group(0, bind_group, &[]);
        pass.dispatch_workgroups(workgroups, 1, 1);
    }
    let final_buffer = if round_count % 2 == 0 {
        &point_a
    } else {
        &point_b
    };
    encoder.copy_buffer_to_buffer(final_buffer, 0, &readback, 0, final_bytes);
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
            clear_public_buffers(
                device,
                queue,
                &[&point_a, &point_b, &public_challenges, &metadata, &readback],
            );
            input_words.fill(0);
            challenge_words.fill(0);
            return Err(CompactEdwardsError::WgpuUnavailable(error.to_string()));
        }
        Err(_) => {
            clear_public_buffers(
                device,
                queue,
                &[&point_a, &point_b, &public_challenges, &metadata, &readback],
            );
            input_words.fill(0);
            challenge_words.fill(0);
            return Err(CompactEdwardsError::WgpuUnavailable(
                "resident fold readback callback was dropped".to_owned(),
            ));
        }
    }

    let mapped = slice.get_mapped_range();
    let gpu_words: &[u32] = bytemuck::cast_slice(&mapped);
    let expected_word_count = final_point_count
        .checked_mul(4 * COMPACT_FIELD_LIMBS)
        .ok_or(CompactEdwardsError::DimensionOverflow)?;
    if gpu_words.len() != expected_word_count {
        drop(mapped);
        readback.unmap();
        clear_public_buffers(
            device,
            queue,
            &[&point_a, &point_b, &public_challenges, &metadata, &readback],
        );
        input_words.fill(0);
        challenge_words.fill(0);
        return Err(CompactEdwardsError::DimensionOverflow);
    }

    let mut compressed_points = Vec::with_capacity(final_point_count);
    let mut mismatch = None;
    for (index, words) in gpu_words.chunks_exact(4 * COMPACT_FIELD_LIMBS).enumerate() {
        let Some(coordinates) = coordinates_from_compact(words) else {
            mismatch = Some(CompactEdwardsError::WgpuPointMismatch { index });
            break;
        };
        let expected_compressed = expected[index].compress();
        if RistrettoPoint::dregg_from_extended_coordinates_checked(
            &coordinates,
            &expected_compressed,
        )
        .is_none()
        {
            mismatch = Some(CompactEdwardsError::WgpuPointMismatch { index });
            break;
        }
        compressed_points.push(expected_compressed.to_bytes());
    }
    drop(mapped);
    readback.unmap();
    clear_public_buffers(
        device,
        queue,
        &[&point_a, &point_b, &public_challenges, &metadata, &readback],
    );
    input_words.fill(0);
    challenge_words.fill(0);
    if let Some(error) = mismatch {
        return Err(error);
    }

    Ok(CompactPublicFoldResult {
        adapter_name: context.adapter_name.clone(),
        is_hardware: context.is_hardware,
        initial_point_count: point_bytes.len(),
        final_point_count,
        round_count,
        point_upload_count: 1,
        challenge_upload_count: 1,
        control_upload_count: 1,
        dispatch_count: u32::try_from(round_count)
            .map_err(|_| CompactEdwardsError::DimensionOverflow)?,
        readback_count: 1,
        compressed_points,
    })
}

#[cfg(test)]
mod tests {
    use super::{compact_limbs, field_bytes_from_compact};

    #[test]
    fn compact_field_host_encoding_round_trips_boundary_values() {
        let values = [
            [0_u8; 32],
            {
                let mut one = [0_u8; 32];
                one[0] = 1;
                one
            },
            {
                let mut p_minus_one = [0xff_u8; 32];
                p_minus_one[0] = 0xec;
                p_minus_one[31] = 0x7f;
                p_minus_one
            },
        ];
        for value in values {
            assert_eq!(
                field_bytes_from_compact(&compact_limbs(&value)),
                Some(value)
            );
        }
        let p = {
            let mut value = [0xff_u8; 32];
            value[0] = 0xed;
            value[31] = 0x7f;
            value
        };
        assert_eq!(field_bytes_from_compact(&compact_limbs(&p)), None);
    }
}

//! Exact four-prime transform-resident PBS backend for the deployed TFHE shape.

use std::sync::{mpsc, OnceLock};

use wgpu::util::DeviceExt;

use crate::tfhe_ntt_wgpu::{host_plan, signed_residue, NttBatchError, TORUS_NTT_MODULI};
use crate::tfhe_wgpu::{TorusCpuFallbackReason, TorusExternalProductParams};

const WORKGROUP_SIZE: u32 = 64;
const CMUX_STEPS_PER_SUBMISSION: usize = 256;

pub(crate) struct TransformPbsGpuResult {
    pub coefficients: Vec<u64>,
    pub adapter: String,
    pub backend: String,
}

pub(crate) enum TransformPbsGpuError {
    Unavailable(TorusCpuFallbackReason),
    Execution(String),
}

pub(crate) struct PreparedTransformPbsGpuKeys {
    bsk_spectra: wgpu::Buffer,
    ksk: wgpu::Buffer,
    qdata: wgpu::Buffer,
    roots: wgpu::Buffer,
    twists: wgpu::Buffer,
    crt_data: wgpu::Buffer,
    pub(crate) blind_mask_dimension: usize,
    pub(crate) params: TorusExternalProductParams,
    pub(crate) output_lwe_size: usize,
    pub(crate) ks_base_log: usize,
    pub(crate) ks_level_count: usize,
    pub(crate) adapter: String,
    pub(crate) backend: String,
}

enum GpuState {
    Ready(GpuContext),
    Unavailable(TorusCpuFallbackReason),
}

fn gpu_state() -> &'static GpuState {
    static GPU: OnceLock<GpuState> = OnceLock::new();
    GPU.get_or_init(GpuContext::initialize)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prepare(
    blind_mask_dimension: usize,
    standard_bsk: &[u64],
    params: TorusExternalProductParams,
    standard_ksk: &[u64],
    output_lwe_size: usize,
    ks_base_log: usize,
    ks_level_count: usize,
) -> Result<PreparedTransformPbsGpuKeys, TransformPbsGpuError> {
    match gpu_state() {
        GpuState::Ready(gpu) => gpu.prepare(
            blind_mask_dimension,
            standard_bsk,
            params,
            standard_ksk,
            output_lwe_size,
            ks_base_log,
            ks_level_count,
        ),
        GpuState::Unavailable(reason) => Err(TransformPbsGpuError::Unavailable(reason.clone())),
    }
}

pub(crate) fn run(
    accumulator: &[u64],
    body_rotation: usize,
    mask_rotations: &[usize],
    prepared: &PreparedTransformPbsGpuKeys,
) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
    match gpu_state() {
        GpuState::Ready(gpu) => gpu.run(accumulator, body_rotation, mask_rotations, prepared),
        GpuState::Unavailable(reason) => Err(TransformPbsGpuError::Unavailable(reason.clone())),
    }
}

pub(crate) fn run_bootstrap_only(
    accumulator: &[u64],
    body_rotation: usize,
    mask_rotations: &[usize],
    prepared: &PreparedTransformPbsGpuKeys,
) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
    match gpu_state() {
        GpuState::Ready(gpu) => gpu.run_with_finalization(
            accumulator,
            body_rotation,
            mask_rotations,
            prepared,
            Finalization::ExtractOnly,
        ),
        GpuState::Unavailable(reason) => Err(TransformPbsGpuError::Unavailable(reason.clone())),
    }
}

pub(crate) fn run_scalar_gt_chain(
    digit_lwes: &[u64],
    accumulators: &[u64],
    blocks: usize,
    prepared: &PreparedTransformPbsGpuKeys,
) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
    match gpu_state() {
        GpuState::Ready(gpu) => gpu.run_scalar_gt_chain(digit_lwes, accumulators, blocks, prepared),
        GpuState::Unavailable(reason) => Err(TransformPbsGpuError::Unavailable(reason.clone())),
    }
}

pub(crate) fn run_ciphertext_gt_chain(
    packed_digit_lwes: &[u64],
    accumulators: &[u64],
    blocks: usize,
    prepared: &PreparedTransformPbsGpuKeys,
) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
    match gpu_state() {
        GpuState::Ready(gpu) => {
            gpu.run_ciphertext_gt_chain(packed_digit_lwes, accumulators, blocks, prepared)
        }
        GpuState::Unavailable(reason) => Err(TransformPbsGpuError::Unavailable(reason.clone())),
    }
}

#[derive(Clone, Copy)]
enum Finalization {
    ExtractKeyswitch,
    ExtractOnly,
}

#[derive(Clone, Copy)]
enum ResidentDigitSource {
    Uploaded(usize),
    Local,
}

#[derive(Clone, Copy)]
enum ResidentStageOutput {
    State,
    Local,
}

#[derive(Clone, Copy)]
struct ResidentPbsStage {
    digit_source: ResidentDigitSource,
    include_state: bool,
    output: ResidentStageOutput,
}

struct GpuContext {
    _instance: wgpu::Instance,
    device: wgpu::Device,
    queue: wgpu::Queue,
    adapter: String,
    backend: String,
    limits: wgpu::Limits,
    bgl: wgpu::BindGroupLayout,
    forward_bsk: wgpu::ComputePipeline,
    rotate: wgpu::ComputePipeline,
    decompose: wgpu::ComputePipeline,
    forward_digits: wgpu::ComputePipeline,
    pointwise: wgpu::ComputePipeline,
    inverse_products: wgpu::ComputePipeline,
    crt_add: wgpu::ComputePipeline,
    rotate_scheduled: wgpu::ComputePipeline,
    decompose_scheduled: wgpu::ComputePipeline,
    keyswitch_bgl: wgpu::BindGroupLayout,
    extract_keyswitch: wgpu::ComputePipeline,
    extract_only: wgpu::ComputePipeline,
    scalar_chain_bgl: wgpu::BindGroupLayout,
    keyswitch_packed_input: wgpu::ComputePipeline,
    centered_modulus_switch: wgpu::ComputePipeline,
}

impl GpuContext {
    fn initialize() -> GpuState {
        let instance = wgpu::Instance::default();
        let Some(adapter) =
            pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                ..Default::default()
            }))
        else {
            return GpuState::Unavailable(TorusCpuFallbackReason::NoAdapter);
        };
        let info = adapter.get_info();
        let limits = adapter.limits();
        if limits.max_storage_buffers_per_shader_stage < 9
            || limits.max_compute_invocations_per_workgroup < 256
            || limits.max_compute_workgroup_size_x < 256
            || limits.max_compute_workgroup_storage_size < 4096 * 4
        {
            return GpuState::Unavailable(TorusCpuFallbackReason::ShapeExceedsAdapterLimits);
        }
        let (device, queue) = match pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("TFHE transform-resident PBS"),
                required_features: wgpu::Features::empty(),
                required_limits: limits.clone(),
                memory_hints: Default::default(),
            },
            None,
        )) {
            Ok(pair) => pair,
            Err(error) => {
                return GpuState::Unavailable(TorusCpuFallbackReason::DeviceRequestFailed(
                    error.to_string(),
                ));
            }
        };

        device.push_error_scope(wgpu::ErrorFilter::Validation);
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("torus_pbs_transform_resident.wgsl"),
            source: wgpu::ShaderSource::Wgsl(
                include_str!("shaders/torus_pbs_transform_resident.wgsl").into(),
            ),
        });
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("TFHE transform-resident PBS bindings"),
            entries: &[
                buffer_entry(0, wgpu::BufferBindingType::Uniform),
                buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(5, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(6, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(7, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(8, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(9, wgpu::BufferBindingType::Storage { read_only: true }),
            ],
        });
        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("TFHE transform-resident PBS layout"),
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let make = |entry: &'static str| {
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry),
                layout: Some(&layout),
                module: &shader,
                entry_point: Some(entry),
                compilation_options: Default::default(),
                cache: None,
            })
        };
        let forward_bsk = make("forward_bsk");
        let rotate = make("monomial_rotate");
        let decompose = make("decompose_difference_to_rns");
        let forward_digits = make("forward_digits");
        let pointwise = make("pointwise_products");
        let inverse_products = make("inverse_products");
        let crt_add = make("crt_add_accumulator");
        let rotate_scheduled = make("monomial_rotate_scheduled");
        let decompose_scheduled = make("decompose_difference_scheduled");

        let keyswitch_shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("torus_pbs_extract_keyswitch.wgsl"),
            source: wgpu::ShaderSource::Wgsl(
                include_str!("shaders/torus_pbs_extract_keyswitch.wgsl").into(),
            ),
        });
        let keyswitch_bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("TFHE transform PBS keyswitch bindings"),
            entries: &[
                buffer_entry(0, wgpu::BufferBindingType::Uniform),
                buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: false }),
            ],
        });
        let keyswitch_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("TFHE transform PBS keyswitch layout"),
            bind_group_layouts: &[&keyswitch_bgl],
            push_constant_ranges: &[],
        });
        let extract_keyswitch = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("extract_and_keyswitch"),
            layout: Some(&keyswitch_layout),
            module: &keyswitch_shader,
            entry_point: Some("extract_and_keyswitch"),
            compilation_options: Default::default(),
            cache: None,
        });
        let extract_only = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("extract_only"),
            layout: Some(&keyswitch_layout),
            module: &keyswitch_shader,
            entry_point: Some("extract_only"),
            compilation_options: Default::default(),
            cache: None,
        });
        let scalar_chain_shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("torus_scalar_gt_chain.wgsl"),
            source: wgpu::ShaderSource::Wgsl(
                include_str!("shaders/torus_scalar_gt_chain.wgsl").into(),
            ),
        });
        let scalar_chain_bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("TFHE resident scalar comparison KS/MS bindings"),
            entries: &[
                buffer_entry(0, wgpu::BufferBindingType::Uniform),
                buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(5, wgpu::BufferBindingType::Storage { read_only: false }),
            ],
        });
        let scalar_chain_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("TFHE resident scalar comparison KS/MS layout"),
            bind_group_layouts: &[&scalar_chain_bgl],
            push_constant_ranges: &[],
        });
        let make_scalar_chain = |entry: &'static str| {
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry),
                layout: Some(&scalar_chain_layout),
                module: &scalar_chain_shader,
                entry_point: Some(entry),
                compilation_options: Default::default(),
                cache: None,
            })
        };
        let keyswitch_packed_input = make_scalar_chain("keyswitch_packed_input");
        let centered_modulus_switch = make_scalar_chain("centered_modulus_switch");
        let context = Self {
            _instance: instance,
            device,
            queue,
            adapter: info.name,
            backend: format!("{:?}", info.backend),
            limits,
            bgl,
            forward_bsk,
            rotate,
            decompose,
            forward_digits,
            pointwise,
            inverse_products,
            crt_add,
            rotate_scheduled,
            decompose_scheduled,
            keyswitch_bgl,
            extract_keyswitch,
            extract_only,
            scalar_chain_bgl,
            keyswitch_packed_input,
            centered_modulus_switch,
        };
        if let Some(error) = pollster::block_on(context.device.pop_error_scope()) {
            return GpuState::Unavailable(TorusCpuFallbackReason::PipelineUnavailable(format!(
                "transform-resident PBS shader validation failed: {error}"
            )));
        }
        GpuState::Ready(context)
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare(
        &self,
        blind_mask_dimension: usize,
        standard_bsk: &[u64],
        params: TorusExternalProductParams,
        standard_ksk: &[u64],
        output_lwe_size: usize,
        ks_base_log: usize,
        ks_level_count: usize,
    ) -> Result<PreparedTransformPbsGpuKeys, TransformPbsGpuError> {
        let plan = host_plan(params.degree).map_err(map_ntt_error)?;
        let rows = TORUS_NTT_MODULI.len();
        let bsk_polynomials = standard_bsk.len() / params.degree;
        let bsk_series = bsk_polynomials
            .checked_mul(rows)
            .ok_or_else(|| TransformPbsGpuError::Execution("BSK series overflow".into()))?;
        let words = bsk_series
            .checked_mul(params.degree)
            .ok_or_else(|| TransformPbsGpuError::Execution("BSK spectrum overflow".into()))?;
        let mut packed_bsk = Vec::with_capacity(words);
        for polynomial in standard_bsk.chunks_exact(params.degree) {
            for (&q, row) in TORUS_NTT_MODULI.iter().zip(&plan.rows) {
                packed_bsk.extend(polynomial.iter().map(|&value| {
                    let residue = signed_residue(value as i64, q);
                    ((u128::from(residue) * u128::from(row.montgomery_r)) % u128::from(q)) as u32
                }));
            }
        }
        if packed_bsk.len() != words {
            return Err(TransformPbsGpuError::Execution(
                "BSK transform packing length mismatch".into(),
            ));
        }
        let bsk_bytes = word_bytes(packed_bsk.len())?;
        let ksk_limbs = to_limbs(standard_ksk);
        let ksk_bytes = word_bytes(ksk_limbs.len())?;
        let table_bytes = word_bytes(plan.roots.len().max(plan.twists.len()))?;
        let binding_limit = self
            .limits
            .max_buffer_size
            .min(u64::from(self.limits.max_storage_buffer_binding_size));
        let bsk_series_u32 = u32::try_from(bsk_series).map_err(|_| {
            TransformPbsGpuError::Unavailable(TorusCpuFallbackReason::ShapeExceedsAdapterLimits)
        })?;
        if bsk_bytes > binding_limit
            || ksk_bytes > binding_limit
            || table_bytes > binding_limit
            || bsk_series_u32 > self.limits.max_compute_workgroups_per_dimension
        {
            return Err(TransformPbsGpuError::Unavailable(
                TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
            ));
        }

        let crt_words = build_crt_data(&plan.rows);
        self.device.push_error_scope(wgpu::ErrorFilter::Validation);
        let bsk_spectra = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE pretransformed standard BSK"),
                contents: bytemuck::cast_slice(&packed_bsk),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let ksk = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE transform PBS resident KSK"),
                contents: bytemuck::cast_slice(&ksk_limbs),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let qdata = upload_storage(&self.device, "TFHE transform qdata", &plan.qdata);
        let roots = upload_storage(&self.device, "TFHE transform roots", &plan.roots);
        let twists = upload_storage(&self.device, "TFHE transform twists", &plan.twists);
        let crt_data = upload_storage(&self.device, "TFHE transform CRT plan", &crt_words);
        let dummy = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE transform preparation dummy"),
            size: 16,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        // Binding 9 is declared read-only while the accumulator/scratch dummy
        // bindings are read-write.  wgpu treats read-write storage as an
        // exclusive usage within a compute pass, even when the active entry
        // point never reads the extra binding, so it must not alias `dummy`.
        let schedule_dummy = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE transform preparation schedule dummy"),
            size: 16,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let metadata = [
            params.degree as u32,
            params.degree.trailing_zeros(),
            params.glwe_size as u32,
            params.decomposition_base_log as u32,
            params.decomposition_level_count as u32,
            0,
            0,
            0,
            rows as u32,
            bsk_series_u32,
            0,
            0,
        ];
        let metadata_buffer = uniform(&self.device, "TFHE BSK transform metadata", &metadata);
        let bind_group = self.bind_group(
            &metadata_buffer,
            &dummy,
            &dummy,
            &bsk_spectra,
            &dummy,
            &qdata,
            &roots,
            &twists,
            &crt_data,
            &schedule_dummy,
        );
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("TFHE one-time BSK forward transform"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("TFHE forward-transform complete BSK"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.forward_bsk);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups(1, bsk_series_u32, 1);
        }
        self.queue.submit([encoder.finish()]);
        self.device.poll(wgpu::Maintain::Wait);
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(TransformPbsGpuError::Execution(format!(
                "TFHE BSK transform/upload failed: {error}"
            )));
        }
        Ok(PreparedTransformPbsGpuKeys {
            bsk_spectra,
            ksk,
            qdata,
            roots,
            twists,
            crt_data,
            blind_mask_dimension,
            params,
            output_lwe_size,
            ks_base_log,
            ks_level_count,
            adapter: self.adapter.clone(),
            backend: self.backend.clone(),
        })
    }

    fn run(
        &self,
        accumulator: &[u64],
        body_rotation: usize,
        mask_rotations: &[usize],
        prepared: &PreparedTransformPbsGpuKeys,
    ) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
        self.run_with_finalization(
            accumulator,
            body_rotation,
            mask_rotations,
            prepared,
            Finalization::ExtractKeyswitch,
        )
    }

    fn run_with_finalization(
        &self,
        accumulator: &[u64],
        body_rotation: usize,
        mask_rotations: &[usize],
        prepared: &PreparedTransformPbsGpuKeys,
        finalization: Finalization,
    ) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
        let p = prepared.params;
        let rows = TORUS_NTT_MODULI.len();
        let accumulator_limbs = to_limbs(accumulator);
        let accumulator_bytes = word_bytes(accumulator_limbs.len())?;
        let scratch_words = p
            .glwe_size
            .checked_mul(rows)
            .and_then(|n| n.checked_mul(p.degree))
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(|| TransformPbsGpuError::Execution("transform scratch overflow".into()))?;
        let scratch_bytes = word_bytes(scratch_words)?;
        let output_lwe_size = match finalization {
            Finalization::ExtractKeyswitch => prepared.output_lwe_size,
            Finalization::ExtractOnly => (p.glwe_size - 1)
                .checked_mul(p.degree)
                .and_then(|dimension| dimension.checked_add(1))
                .ok_or_else(|| {
                    TransformPbsGpuError::Execution("extracted LWE size overflow".into())
                })?,
        };
        let output_bytes = output_lwe_size
            .checked_mul(8)
            .and_then(|n| u64::try_from(n).ok())
            .ok_or_else(|| TransformPbsGpuError::Execution("output size overflow".into()))?;
        let mut schedule_words = mask_rotations
            .iter()
            .map(|&rotation| u32::try_from(rotation))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| TransformPbsGpuError::Execution("rotation overflow".into()))?;
        schedule_words.push(
            u32::try_from(body_rotation)
                .map_err(|_| TransformPbsGpuError::Execution("rotation overflow".into()))?,
        );
        let schedule = upload_storage(
            &self.device,
            "TFHE transform host rotation schedule",
            &schedule_words,
        );
        let binding_limit = self
            .limits
            .max_buffer_size
            .min(u64::from(self.limits.max_storage_buffer_binding_size));
        if accumulator_bytes > binding_limit || scratch_bytes > binding_limit {
            return Err(TransformPbsGpuError::Unavailable(
                TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
            ));
        }

        self.device.push_error_scope(wgpu::ErrorFilter::Validation);
        let accumulator_a = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE transform accumulator A"),
                contents: bytemuck::cast_slice(&accumulator_limbs),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let accumulator_b = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE transform accumulator B"),
            size: accumulator_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let scratch = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE transform-resident digit/product scratch"),
            size: scratch_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let output = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE transform post-keyswitch LWE"),
            size: output_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let readback = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE transform final readback"),
            size: output_bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let mut encoder = self.encoder("TFHE transform PBS initial command chunk");
        let mut current = 0u32;
        if body_rotation != 0 {
            self.encode_transform_step(
                &mut encoder,
                &self.rotate,
                body_rotation,
                0,
                current,
                prepared,
                &accumulator_a,
                &accumulator_b,
                &scratch,
                &schedule,
            )?;
            current = 1;
        }
        let mut in_chunk = 0usize;
        for (step, &rotation) in mask_rotations.iter().enumerate() {
            if rotation == 0 {
                continue;
            }
            if in_chunk == CMUX_STEPS_PER_SUBMISSION {
                self.queue.submit([encoder.finish()]);
                self.device.poll(wgpu::Maintain::Wait);
                encoder = self.encoder("TFHE transform PBS continued command chunk");
                in_chunk = 0;
            }
            let metadata_buffer = self.step_metadata(rotation, step, current, prepared)?;
            let bind_group = self.bind_group(
                &metadata_buffer,
                &accumulator_a,
                &accumulator_b,
                &prepared.bsk_spectra,
                &scratch,
                &prepared.qdata,
                &prepared.roots,
                &prepared.twists,
                &prepared.crt_data,
                &schedule,
            );
            self.dispatch_1d(
                &mut encoder,
                &self.decompose,
                &bind_group,
                (p.glwe_size * p.degree).div_ceil(WORKGROUP_SIZE as usize) as u32,
                1,
                "TFHE transform decompose",
            );
            self.dispatch_1d(
                &mut encoder,
                &self.forward_digits,
                &bind_group,
                1,
                (p.glwe_size * rows) as u32,
                "TFHE transform forward digits",
            );
            self.dispatch_1d(
                &mut encoder,
                &self.pointwise,
                &bind_group,
                p.degree.div_ceil(WORKGROUP_SIZE as usize) as u32,
                (p.glwe_size * rows) as u32,
                "TFHE transform pointwise products",
            );
            self.dispatch_1d(
                &mut encoder,
                &self.inverse_products,
                &bind_group,
                1,
                (p.glwe_size * rows) as u32,
                "TFHE transform inverse products",
            );
            self.dispatch_1d(
                &mut encoder,
                &self.crt_add,
                &bind_group,
                (p.glwe_size * p.degree).div_ceil(WORKGROUP_SIZE as usize) as u32,
                1,
                "TFHE transform CRT add",
            );
            current = 1 - current;
            in_chunk += 1;
        }

        let keyswitch_metadata = [
            p.degree as u32,
            p.glwe_size as u32,
            output_lwe_size as u32,
            prepared.ks_base_log as u32,
            prepared.ks_level_count as u32,
            current,
            0,
            0,
        ];
        let keyswitch_metadata_buffer = uniform(
            &self.device,
            "TFHE transform keyswitch metadata",
            &keyswitch_metadata,
        );
        let keyswitch_bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("TFHE transform fused keyswitch bind group"),
            layout: &self.keyswitch_bgl,
            entries: &[
                entry(0, &keyswitch_metadata_buffer),
                entry(1, &accumulator_a),
                entry(2, &accumulator_b),
                entry(3, &prepared.ksk),
                entry(4, &output),
            ],
        });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("TFHE transform sample extract/key switch"),
                timestamp_writes: None,
            });
            pass.set_pipeline(match finalization {
                Finalization::ExtractKeyswitch => &self.extract_keyswitch,
                Finalization::ExtractOnly => &self.extract_only,
            });
            pass.set_bind_group(0, &keyswitch_bind_group, &[]);
            pass.dispatch_workgroups(
                output_lwe_size.div_ceil(WORKGROUP_SIZE as usize) as u32,
                1,
                1,
            );
        }
        encoder.copy_buffer_to_buffer(&output, 0, &readback, 0, output_bytes);
        self.queue.submit([encoder.finish()]);
        self.device.poll(wgpu::Maintain::Wait);
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(TransformPbsGpuError::Execution(format!(
                "TFHE transform-resident PBS dispatch failed: {error}"
            )));
        }
        let coefficients = read_u64(&self.device, &readback, output_lwe_size)?;
        Ok(TransformPbsGpuResult {
            coefficients,
            adapter: self.adapter.clone(),
            backend: self.backend.clone(),
        })
    }

    fn run_scalar_gt_chain(
        &self,
        digit_lwes: &[u64],
        accumulators: &[u64],
        blocks: usize,
        prepared: &PreparedTransformPbsGpuKeys,
    ) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
        let stages = (0..blocks)
            .map(|block| ResidentPbsStage {
                digit_source: ResidentDigitSource::Uploaded(block),
                include_state: block != 0,
                output: ResidentStageOutput::State,
            })
            .collect::<Vec<_>>();
        self.run_resident_gt_stages(digit_lwes, accumulators, blocks, &stages, prepared)
    }

    fn run_ciphertext_gt_chain(
        &self,
        packed_digit_lwes: &[u64],
        accumulators: &[u64],
        blocks: usize,
        prepared: &PreparedTransformPbsGpuKeys,
    ) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
        let stage_count = blocks
            .checked_mul(2)
            .and_then(|count| count.checked_sub(1))
            .ok_or_else(|| {
                TransformPbsGpuError::Execution(
                    "resident ciphertext comparison stage count overflow".into(),
                )
            })?;
        let mut stages = Vec::with_capacity(stage_count);
        if blocks != 0 {
            stages.push(ResidentPbsStage {
                digit_source: ResidentDigitSource::Uploaded(0),
                include_state: false,
                output: ResidentStageOutput::State,
            });
            for block in 1..blocks {
                // The radix-4 lhs/rhs digit pair consumes all sixteen plaintext
                // slots. First PBS it to a local 0/1/2 comparison, then fold
                // that result into the predecessor state with a second PBS.
                stages.push(ResidentPbsStage {
                    digit_source: ResidentDigitSource::Uploaded(block),
                    include_state: false,
                    output: ResidentStageOutput::Local,
                });
                stages.push(ResidentPbsStage {
                    digit_source: ResidentDigitSource::Local,
                    include_state: true,
                    output: ResidentStageOutput::State,
                });
            }
        }
        self.run_resident_gt_stages(packed_digit_lwes, accumulators, blocks, &stages, prepared)
    }

    fn run_resident_gt_stages(
        &self,
        digit_lwes: &[u64],
        accumulators: &[u64],
        uploaded_blocks: usize,
        stages: &[ResidentPbsStage],
        prepared: &PreparedTransformPbsGpuKeys,
    ) -> Result<TransformPbsGpuResult, TransformPbsGpuError> {
        if uploaded_blocks == 0 || stages.is_empty() {
            return Err(TransformPbsGpuError::Execution(
                "resident comparison has no radix blocks or PBS stages".into(),
            ));
        }
        if stages.iter().any(|stage| {
            matches!(
                stage.digit_source,
                ResidentDigitSource::Uploaded(block) if block >= uploaded_blocks
            )
        }) {
            return Err(TransformPbsGpuError::Execution(
                "resident comparison stage references a missing radix block".into(),
            ));
        }
        let p = prepared.params;
        let rows = TORUS_NTT_MODULI.len();
        let large_lwe_size = (p.glwe_size - 1)
            .checked_mul(p.degree)
            .and_then(|dimension| dimension.checked_add(1))
            .ok_or_else(|| TransformPbsGpuError::Execution("large LWE size overflow".into()))?;
        let accumulator_coefficients = p
            .glwe_size
            .checked_mul(p.degree)
            .ok_or_else(|| TransformPbsGpuError::Execution("accumulator size overflow".into()))?;
        let expected_digits = uploaded_blocks
            .checked_mul(large_lwe_size)
            .ok_or_else(|| TransformPbsGpuError::Execution("digit LWE size overflow".into()))?;
        if digit_lwes.len() != expected_digits {
            return Err(TransformPbsGpuError::Execution(format!(
                "resident comparison has {} digit coefficients; expected {expected_digits}",
                digit_lwes.len()
            )));
        }
        let expected_accumulators = stages
            .len()
            .checked_mul(accumulator_coefficients)
            .ok_or_else(|| TransformPbsGpuError::Execution("LUT family size overflow".into()))?;
        if accumulators.len() != expected_accumulators {
            return Err(TransformPbsGpuError::Execution(format!(
                "resident comparison has {} LUT coefficients; expected {expected_accumulators}",
                accumulators.len()
            )));
        }
        if prepared.output_lwe_size != prepared.blind_mask_dimension + 1 {
            return Err(TransformPbsGpuError::Execution(
                "resident comparison KSK output does not match BSK input".into(),
            ));
        }

        let digit_limbs = to_limbs(digit_lwes);
        let accumulator_limbs = to_limbs(accumulators);
        let digit_bytes = word_bytes(digit_limbs.len())?;
        let lut_bytes = word_bytes(accumulator_limbs.len())?;
        let one_accumulator_bytes = accumulator_coefficients
            .checked_mul(8)
            .and_then(|bytes| u64::try_from(bytes).ok())
            .ok_or_else(|| TransformPbsGpuError::Execution("accumulator bytes overflow".into()))?;
        let large_lwe_bytes = large_lwe_size
            .checked_mul(8)
            .and_then(|bytes| u64::try_from(bytes).ok())
            .ok_or_else(|| TransformPbsGpuError::Execution("large LWE bytes overflow".into()))?;
        let small_lwe_bytes = prepared
            .output_lwe_size
            .checked_mul(8)
            .and_then(|bytes| u64::try_from(bytes).ok())
            .ok_or_else(|| TransformPbsGpuError::Execution("small LWE bytes overflow".into()))?;
        let rotation_bytes = prepared
            .output_lwe_size
            .checked_mul(4)
            .and_then(|bytes| u64::try_from(bytes).ok())
            .ok_or_else(|| TransformPbsGpuError::Execution("rotation bytes overflow".into()))?;
        let scratch_words = p
            .glwe_size
            .checked_mul(rows)
            .and_then(|n| n.checked_mul(p.degree))
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(|| TransformPbsGpuError::Execution("transform scratch overflow".into()))?;
        let scratch_bytes = word_bytes(scratch_words)?;
        let binding_limit = self
            .limits
            .max_buffer_size
            .min(u64::from(self.limits.max_storage_buffer_binding_size));
        if [
            digit_bytes,
            lut_bytes,
            one_accumulator_bytes,
            large_lwe_bytes,
            small_lwe_bytes,
            rotation_bytes,
            scratch_bytes,
        ]
        .into_iter()
        .any(|bytes| bytes > binding_limit)
        {
            return Err(TransformPbsGpuError::Unavailable(
                TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
            ));
        }

        self.device.push_error_scope(wgpu::ErrorFilter::Validation);
        let digits = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE resident comparison radix LWEs"),
                contents: bytemuck::cast_slice(&digit_limbs),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let luts = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE resident comparison LUT family"),
                contents: bytemuck::cast_slice(&accumulator_limbs),
                usage: wgpu::BufferUsages::COPY_SRC,
            });
        let state = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE resident comparison large-key state"),
            size: large_lwe_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let local = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE resident comparison large-key local digit result"),
            size: large_lwe_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let small = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE resident comparison small-key LWE"),
            size: small_lwe_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let rotations = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE resident comparison centered rotations"),
            size: rotation_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let accumulator_a = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE resident comparison accumulator A"),
            size: one_accumulator_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let accumulator_b = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE resident comparison accumulator B"),
            size: one_accumulator_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let scratch = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE resident comparison transform scratch"),
            size: scratch_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let readback = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE resident comparison final readback"),
            size: large_lwe_bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });

        let input_lwe_size_u32 = u32::try_from(large_lwe_size)
            .map_err(|_| TransformPbsGpuError::Execution("input LWE size overflow".into()))?;
        let output_lwe_size_u32 = u32::try_from(prepared.output_lwe_size)
            .map_err(|_| TransformPbsGpuError::Execution("output LWE size overflow".into()))?;
        let log_modulus = (p.degree * 2).ilog2();
        for (stage_index, stage) in stages.iter().copied().enumerate() {
            let (digit_source, digit_block) = match stage.digit_source {
                ResidentDigitSource::Uploaded(block) => (&digits, block),
                ResidentDigitSource::Local => (&local, 0),
            };
            let block_u32 = u32::try_from(digit_block)
                .map_err(|_| TransformPbsGpuError::Execution("block index overflow".into()))?;
            let chain_metadata = [
                input_lwe_size_u32,
                output_lwe_size_u32,
                prepared.ks_base_log as u32,
                prepared.ks_level_count as u32,
                log_modulus,
                block_u32,
                u32::from(stage.include_state),
                u32::from(stage.include_state) * 2,
            ];
            let chain_metadata_buffer = uniform(
                &self.device,
                "TFHE resident comparison KS/MS metadata",
                &chain_metadata,
            );
            let chain_bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("TFHE resident comparison KS/MS bind group"),
                layout: &self.scalar_chain_bgl,
                entries: &[
                    entry(0, &chain_metadata_buffer),
                    entry(1, &state),
                    entry(2, digit_source),
                    entry(3, &prepared.ksk),
                    entry(4, &small),
                    entry(5, &rotations),
                ],
            });
            let mut encoder = self.encoder("TFHE resident comparison PBS stage");
            encoder.copy_buffer_to_buffer(
                &luts,
                stage_index as u64 * one_accumulator_bytes,
                &accumulator_a,
                0,
                one_accumulator_bytes,
            );
            self.dispatch_1d(
                &mut encoder,
                &self.keyswitch_packed_input,
                &chain_bind_group,
                prepared.output_lwe_size.div_ceil(WORKGROUP_SIZE as usize) as u32,
                1,
                "TFHE resident comparison large-to-small key switch",
            );
            self.dispatch_1d(
                &mut encoder,
                &self.centered_modulus_switch,
                &chain_bind_group,
                prepared.output_lwe_size.div_ceil(WORKGROUP_SIZE as usize) as u32,
                1,
                "TFHE resident comparison centered modulus switch",
            );

            // The body rotation is always dispatched. Rotation zero is an
            // exact copy, avoiding host knowledge of the GPU-produced schedule.
            let body_metadata =
                self.step_metadata(0, prepared.blind_mask_dimension, 0, prepared)?;
            let body_bind_group = self.bind_group(
                &body_metadata,
                &accumulator_a,
                &accumulator_b,
                &prepared.bsk_spectra,
                &scratch,
                &prepared.qdata,
                &prepared.roots,
                &prepared.twists,
                &prepared.crt_data,
                &rotations,
            );
            self.dispatch_1d(
                &mut encoder,
                &self.rotate_scheduled,
                &body_bind_group,
                accumulator_coefficients.div_ceil(WORKGROUP_SIZE as usize) as u32,
                1,
                "TFHE resident comparison scheduled body rotation",
            );
            let mut current = 1u32;
            let mut in_chunk = 0usize;
            for step in 0..prepared.blind_mask_dimension {
                if in_chunk == CMUX_STEPS_PER_SUBMISSION {
                    // Keep command recording below the driver's command-memory
                    // ceiling. Queue ordering preserves all accumulator and
                    // schedule dependencies; deliberately do not poll here.
                    self.queue.submit([encoder.finish()]);
                    encoder = self.encoder("TFHE resident comparison continued command chunk");
                    in_chunk = 0;
                }
                let metadata = self.step_metadata(0, step, current, prepared)?;
                let bind_group = self.bind_group(
                    &metadata,
                    &accumulator_a,
                    &accumulator_b,
                    &prepared.bsk_spectra,
                    &scratch,
                    &prepared.qdata,
                    &prepared.roots,
                    &prepared.twists,
                    &prepared.crt_data,
                    &rotations,
                );
                self.dispatch_1d(
                    &mut encoder,
                    &self.decompose_scheduled,
                    &bind_group,
                    accumulator_coefficients.div_ceil(WORKGROUP_SIZE as usize) as u32,
                    1,
                    "TFHE resident comparison scheduled decompose",
                );
                self.dispatch_1d(
                    &mut encoder,
                    &self.forward_digits,
                    &bind_group,
                    1,
                    (p.glwe_size * rows) as u32,
                    "TFHE resident comparison forward digits",
                );
                self.dispatch_1d(
                    &mut encoder,
                    &self.pointwise,
                    &bind_group,
                    p.degree.div_ceil(WORKGROUP_SIZE as usize) as u32,
                    (p.glwe_size * rows) as u32,
                    "TFHE resident comparison pointwise products",
                );
                self.dispatch_1d(
                    &mut encoder,
                    &self.inverse_products,
                    &bind_group,
                    1,
                    (p.glwe_size * rows) as u32,
                    "TFHE resident comparison inverse products",
                );
                self.dispatch_1d(
                    &mut encoder,
                    &self.crt_add,
                    &bind_group,
                    accumulator_coefficients.div_ceil(WORKGROUP_SIZE as usize) as u32,
                    1,
                    "TFHE resident comparison CRT add",
                );
                current = 1 - current;
                in_chunk += 1;
            }

            let extract_metadata = [
                p.degree as u32,
                p.glwe_size as u32,
                large_lwe_size as u32,
                prepared.ks_base_log as u32,
                prepared.ks_level_count as u32,
                current,
                0,
                0,
            ];
            let extract_metadata_buffer = uniform(
                &self.device,
                "TFHE resident comparison extract metadata",
                &extract_metadata,
            );
            let stage_output = match stage.output {
                ResidentStageOutput::State => &state,
                ResidentStageOutput::Local => &local,
            };
            let extract_bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("TFHE resident comparison extract bind group"),
                layout: &self.keyswitch_bgl,
                entries: &[
                    entry(0, &extract_metadata_buffer),
                    entry(1, &accumulator_a),
                    entry(2, &accumulator_b),
                    entry(3, &prepared.ksk),
                    entry(4, stage_output),
                ],
            });
            self.dispatch_1d(
                &mut encoder,
                &self.extract_only,
                &extract_bind_group,
                large_lwe_size.div_ceil(WORKGROUP_SIZE as usize) as u32,
                1,
                "TFHE resident comparison extract large-key state",
            );
            if stage_index + 1 == stages.len() {
                if !matches!(stage.output, ResidentStageOutput::State) {
                    return Err(TransformPbsGpuError::Execution(
                        "resident comparison final PBS stage does not produce state".into(),
                    ));
                }
                encoder.copy_buffer_to_buffer(&state, 0, &readback, 0, large_lwe_bytes);
            }
            // A bounded number of submissions per radix block, but no host
            // wait or readback. Queue ordering carries the encrypted state
            // directly into the next block; only the final state is mapped.
            self.queue.submit([encoder.finish()]);
        }
        self.device.poll(wgpu::Maintain::Wait);
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(TransformPbsGpuError::Execution(format!(
                "TFHE resident comparison dispatch failed: {error}"
            )));
        }
        let coefficients = read_u64(&self.device, &readback, large_lwe_size)?;
        Ok(TransformPbsGpuResult {
            coefficients,
            adapter: self.adapter.clone(),
            backend: self.backend.clone(),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_transform_step(
        &self,
        encoder: &mut wgpu::CommandEncoder,
        pipeline: &wgpu::ComputePipeline,
        rotation: usize,
        step: usize,
        current: u32,
        prepared: &PreparedTransformPbsGpuKeys,
        accumulator_a: &wgpu::Buffer,
        accumulator_b: &wgpu::Buffer,
        scratch: &wgpu::Buffer,
        schedule: &wgpu::Buffer,
    ) -> Result<(), TransformPbsGpuError> {
        let metadata = self.step_metadata(rotation, step, current, prepared)?;
        let bind_group = self.bind_group(
            &metadata,
            accumulator_a,
            accumulator_b,
            &prepared.bsk_spectra,
            scratch,
            &prepared.qdata,
            &prepared.roots,
            &prepared.twists,
            &prepared.crt_data,
            schedule,
        );
        self.dispatch_1d(
            encoder,
            pipeline,
            &bind_group,
            (prepared.params.glwe_size * prepared.params.degree).div_ceil(WORKGROUP_SIZE as usize)
                as u32,
            1,
            "TFHE transform monomial body rotation",
        );
        Ok(())
    }

    fn step_metadata(
        &self,
        rotation: usize,
        step: usize,
        current: u32,
        prepared: &PreparedTransformPbsGpuKeys,
    ) -> Result<wgpu::Buffer, TransformPbsGpuError> {
        let p = prepared.params;
        let metadata = [
            p.degree as u32,
            p.degree.trailing_zeros(),
            p.glwe_size as u32,
            p.decomposition_base_log as u32,
            p.decomposition_level_count as u32,
            u32::try_from(rotation)
                .map_err(|_| TransformPbsGpuError::Execution("rotation overflow".into()))?,
            u32::try_from(step)
                .map_err(|_| TransformPbsGpuError::Execution("BSK step overflow".into()))?,
            current,
            TORUS_NTT_MODULI.len() as u32,
            0,
            0,
            0,
        ];
        Ok(uniform(
            &self.device,
            "TFHE transform step metadata",
            &metadata,
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_group(
        &self,
        metadata: &wgpu::Buffer,
        accumulator_a: &wgpu::Buffer,
        accumulator_b: &wgpu::Buffer,
        bsk_spectra: &wgpu::Buffer,
        scratch: &wgpu::Buffer,
        qdata: &wgpu::Buffer,
        roots: &wgpu::Buffer,
        twists: &wgpu::Buffer,
        crt_data: &wgpu::Buffer,
        schedule: &wgpu::Buffer,
    ) -> wgpu::BindGroup {
        self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("TFHE transform-resident PBS bind group"),
            layout: &self.bgl,
            entries: &[
                entry(0, metadata),
                entry(1, accumulator_a),
                entry(2, accumulator_b),
                entry(3, bsk_spectra),
                entry(4, scratch),
                entry(5, qdata),
                entry(6, roots),
                entry(7, twists),
                entry(8, crt_data),
                entry(9, schedule),
            ],
        })
    }

    fn dispatch_1d(
        &self,
        encoder: &mut wgpu::CommandEncoder,
        pipeline: &wgpu::ComputePipeline,
        bind_group: &wgpu::BindGroup,
        x: u32,
        y: u32,
        label: &'static str,
    ) {
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some(label),
            timestamp_writes: None,
        });
        pass.set_pipeline(pipeline);
        pass.set_bind_group(0, bind_group, &[]);
        pass.dispatch_workgroups(x, y, 1);
    }

    fn encoder(&self, label: &'static str) -> wgpu::CommandEncoder {
        self.device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor { label: Some(label) })
    }
}

fn build_crt_data(rows: &[crate::tfhe_ntt_wgpu::RowPlan]) -> Vec<u32> {
    let q = TORUS_NTT_MODULI;
    let q01 = u128::from(q[0]) * u128::from(q[1]);
    let q012 = q01 * u128::from(q[2]);
    let modulus = q012 * u128::from(q[3]);
    let mont = |value: u64, row: usize| {
        ((u128::from(value % q[row]) * u128::from(rows[row].montgomery_r)) % u128::from(q[row]))
            as u32
    };
    let inv = |value: u64, row: usize| mont(mod_pow(value % q[row], q[row] - 2, q[row]), row);
    let mut words = vec![
        inv(q[0], 1),
        inv((q01 % u128::from(q[2])) as u64, 2),
        inv((q012 % u128::from(q[3])) as u64, 3),
        mont(q[0], 2),
        mont(q[0], 3),
        mont((q01 % u128::from(q[3])) as u64, 3),
        0,
        0,
    ];
    words.extend(u128_limbs(u128::from(q[0])));
    words.extend(u128_limbs(q01));
    words.extend(u128_limbs(q012));
    words.extend(u128_limbs(modulus));
    words.extend(u128_limbs(modulus / 2));
    words
}

fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
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

fn u128_limbs(value: u128) -> [u32; 4] {
    [
        value as u32,
        (value >> 32) as u32,
        (value >> 64) as u32,
        (value >> 96) as u32,
    ]
}

fn upload_storage(device: &wgpu::Device, label: &'static str, words: &[u32]) -> wgpu::Buffer {
    device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some(label),
        contents: bytemuck::cast_slice(words),
        usage: wgpu::BufferUsages::STORAGE,
    })
}

fn uniform(device: &wgpu::Device, label: &'static str, words: &[u32]) -> wgpu::Buffer {
    device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some(label),
        contents: bytemuck::cast_slice(words),
        usage: wgpu::BufferUsages::UNIFORM,
    })
}

fn entry<'a>(binding: u32, buffer: &'a wgpu::Buffer) -> wgpu::BindGroupEntry<'a> {
    wgpu::BindGroupEntry {
        binding,
        resource: buffer.as_entire_binding(),
    }
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

fn word_bytes(words: usize) -> Result<u64, TransformPbsGpuError> {
    words
        .checked_mul(4)
        .and_then(|bytes| u64::try_from(bytes).ok())
        .ok_or_else(|| TransformPbsGpuError::Execution("GPU buffer size overflow".into()))
}

fn to_limbs(values: &[u64]) -> Vec<u32> {
    values
        .iter()
        .flat_map(|&value| [value as u32, (value >> 32) as u32])
        .collect()
}

fn read_u64(
    device: &wgpu::Device,
    buffer: &wgpu::Buffer,
    coefficients: usize,
) -> Result<Vec<u64>, TransformPbsGpuError> {
    let slice = buffer.slice(..);
    let (sender, receiver) = mpsc::sync_channel(1);
    slice.map_async(wgpu::MapMode::Read, move |status| {
        let _ = sender.send(status);
    });
    device.poll(wgpu::Maintain::Wait);
    receiver
        .recv()
        .map_err(|error| TransformPbsGpuError::Execution(error.to_string()))?
        .map_err(|error| TransformPbsGpuError::Execution(error.to_string()))?;
    let mapped = slice.get_mapped_range();
    let limbs: &[u32] = bytemuck::cast_slice(&mapped);
    if limbs.len() != coefficients * 2 {
        return Err(TransformPbsGpuError::Execution(format!(
            "transform PBS readback has {} limbs; expected {}",
            limbs.len(),
            coefficients * 2
        )));
    }
    let output = limbs
        .chunks_exact(2)
        .map(|pair| u64::from(pair[0]) | (u64::from(pair[1]) << 32))
        .collect();
    drop(mapped);
    buffer.unmap();
    Ok(output)
}

fn map_ntt_error(error: NttBatchError) -> TransformPbsGpuError {
    match error {
        NttBatchError::Unavailable => {
            TransformPbsGpuError::Unavailable(TorusCpuFallbackReason::ShapeExceedsAdapterLimits)
        }
        NttBatchError::Execution(error) => TransformPbsGpuError::Execution(error),
    }
}

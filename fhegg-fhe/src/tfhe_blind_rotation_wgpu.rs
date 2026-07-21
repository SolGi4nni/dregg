//! One-submit, one-readback exact blind-rotation chain.

use std::sync::{mpsc, OnceLock};

use wgpu::util::DeviceExt;

use crate::tfhe_wgpu::{TorusCpuFallbackReason, TorusExternalProductParams};

const WORKGROUP_SIZE: u32 = 64;

pub(crate) struct BlindRotationGpuResult {
    pub coefficients: Vec<u64>,
    pub adapter: String,
    pub backend: String,
}

pub(crate) enum BlindRotationGpuError {
    Unavailable(TorusCpuFallbackReason),
    Execution(String),
}

enum GpuState {
    Ready(GpuContext),
    Unavailable(TorusCpuFallbackReason),
}

fn gpu_state() -> &'static GpuState {
    static GPU: OnceLock<GpuState> = OnceLock::new();
    GPU.get_or_init(GpuContext::initialize)
}

pub(crate) fn run(
    accumulator: &[u64],
    body_rotation: usize,
    mask_rotations: &[usize],
    standard_bsk: &[u64],
    ggsw_coefficients: usize,
    params: TorusExternalProductParams,
) -> Result<BlindRotationGpuResult, BlindRotationGpuError> {
    match gpu_state() {
        GpuState::Ready(gpu) => gpu.run(
            accumulator,
            body_rotation,
            mask_rotations,
            standard_bsk,
            ggsw_coefficients,
            params,
        ),
        GpuState::Unavailable(reason) => Err(BlindRotationGpuError::Unavailable(reason.clone())),
    }
}

struct GpuContext {
    _instance: wgpu::Instance,
    device: wgpu::Device,
    queue: wgpu::Queue,
    adapter: String,
    backend: String,
    limits: wgpu::Limits,
    bgl: wgpu::BindGroupLayout,
    rotate: wgpu::ComputePipeline,
    decompose: wgpu::ComputePipeline,
    external_product: wgpu::ComputePipeline,
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
        let (device, queue) = match pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("TFHE device-resident blind rotation"),
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
            label: Some("torus_blind_rotation.wgsl"),
            source: wgpu::ShaderSource::Wgsl(
                include_str!("shaders/torus_blind_rotation.wgsl").into(),
            ),
        });
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("TFHE blind-rotation bindings"),
            entries: &[
                buffer_entry(0, wgpu::BufferBindingType::Uniform),
                buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: false }),
            ],
        });
        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("TFHE blind-rotation pipeline layout"),
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
        let rotate = make("monomial_rotate");
        let decompose = make("decompose_rotated_difference");
        let external_product = make("external_product_step");
        let context = Self {
            _instance: instance,
            device,
            queue,
            adapter: info.name,
            backend: format!("{:?}", info.backend),
            limits,
            bgl,
            rotate,
            decompose,
            external_product,
        };
        if let Some(error) = pollster::block_on(context.device.pop_error_scope()) {
            return GpuState::Unavailable(TorusCpuFallbackReason::PipelineUnavailable(format!(
                "TFHE blind-rotation shader validation failed: {error}"
            )));
        }
        GpuState::Ready(context)
    }

    fn run(
        &self,
        accumulator: &[u64],
        body_rotation: usize,
        mask_rotations: &[usize],
        standard_bsk: &[u64],
        ggsw_coefficients: usize,
        params: TorusExternalProductParams,
    ) -> Result<BlindRotationGpuResult, BlindRotationGpuError> {
        let glwe_coefficients = accumulator.len();
        let accumulator_bytes = byte_len(glwe_coefficients)?;
        let bsk_bytes = byte_len(standard_bsk.len())?;
        let decomposed_coefficients = params
            .decomposition_level_count
            .checked_mul(glwe_coefficients)
            .ok_or_else(|| {
                BlindRotationGpuError::Execution("decomposition size overflow".into())
            })?;
        let decomposed_bytes = byte_len(decomposed_coefficients)?;
        let binding_limit = self
            .limits
            .max_buffer_size
            .min(u64::from(self.limits.max_storage_buffer_binding_size));
        let workgroups = u32::try_from(glwe_coefficients.div_ceil(WORKGROUP_SIZE as usize))
            .map_err(|_| {
                BlindRotationGpuError::Unavailable(
                    TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
                )
            })?;
        if [accumulator_bytes, bsk_bytes, decomposed_bytes]
            .into_iter()
            .any(|size| size > binding_limit)
            || self.limits.max_storage_buffers_per_shader_stage < 4
            || workgroups > self.limits.max_compute_workgroups_per_dimension
        {
            return Err(BlindRotationGpuError::Unavailable(
                TorusCpuFallbackReason::ShapeExceedsAdapterLimits,
            ));
        }

        let accumulator_limbs = to_limbs(accumulator);
        let bsk_limbs = to_limbs(standard_bsk);
        self.device.push_error_scope(wgpu::ErrorFilter::Validation);
        let accumulator_a = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE blind-rotation accumulator A"),
                contents: bytemuck::cast_slice(&accumulator_limbs),
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            });
        let accumulator_b = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE blind-rotation accumulator B"),
            size: accumulator_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let bsk = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE resident standard bootstrapping key"),
                contents: bytemuck::cast_slice(&bsk_limbs),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let decomposed = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE blind-rotation gadget digits"),
            size: decomposed_bytes,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: false,
        });
        let readback = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE blind-rotation final readback"),
            size: accumulator_bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("TFHE one-submit blind-rotation chain"),
            });
        let degree = u32::try_from(params.degree)
            .map_err(|_| BlindRotationGpuError::Execution("degree metadata overflow".into()))?;
        let glwe_size = u32::try_from(params.glwe_size)
            .map_err(|_| BlindRotationGpuError::Execution("GLWE metadata overflow".into()))?;
        let base_log = u32::try_from(params.decomposition_base_log)
            .map_err(|_| BlindRotationGpuError::Execution("base-log metadata overflow".into()))?;
        let level_count = u32::try_from(params.decomposition_level_count)
            .map_err(|_| BlindRotationGpuError::Execution("level metadata overflow".into()))?;
        let mut dispatch = |pipeline: &wgpu::ComputePipeline,
                            rotation: usize,
                            key_offset: usize,
                            input_buffer: u32|
         -> Result<(), BlindRotationGpuError> {
            let metadata = [
                degree,
                glwe_size,
                base_log,
                level_count,
                u32::try_from(rotation).map_err(|_| {
                    BlindRotationGpuError::Execution("rotation metadata overflow".into())
                })?,
                u32::try_from(key_offset).map_err(|_| {
                    BlindRotationGpuError::Execution("key-offset metadata overflow".into())
                })?,
                input_buffer,
                0,
            ];
            let metadata_buffer =
                self.device
                    .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                        label: Some("TFHE blind-rotation step metadata"),
                        contents: bytemuck::cast_slice(&metadata),
                        usage: wgpu::BufferUsages::UNIFORM,
                    });
            let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("TFHE blind-rotation step bind group"),
                layout: &self.bgl,
                entries: &[
                    wgpu::BindGroupEntry {
                        binding: 0,
                        resource: metadata_buffer.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 1,
                        resource: accumulator_a.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 2,
                        resource: accumulator_b.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 3,
                        resource: bsk.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 4,
                        resource: decomposed.as_entire_binding(),
                    },
                ],
            });
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("TFHE blind-rotation step"),
                timestamp_writes: None,
            });
            pass.set_pipeline(pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups(workgroups, 1, 1);
            Ok(())
        };

        let mut current = 0u32;
        if body_rotation != 0 {
            dispatch(&self.rotate, body_rotation, 0, current)?;
            current = 1;
        }
        for (step, &rotation) in mask_rotations.iter().enumerate() {
            if rotation == 0 {
                continue;
            }
            let key_offset = step.checked_mul(ggsw_coefficients).ok_or_else(|| {
                BlindRotationGpuError::Execution("bootstrapping-key offset overflow".into())
            })?;
            dispatch(&self.decompose, rotation, key_offset, current)?;
            dispatch(&self.external_product, rotation, key_offset, current)?;
            current = 1 - current;
        }
        drop(dispatch);
        let final_accumulator = if current == 0 {
            &accumulator_a
        } else {
            &accumulator_b
        };
        encoder.copy_buffer_to_buffer(final_accumulator, 0, &readback, 0, accumulator_bytes);
        self.queue.submit([encoder.finish()]);
        self.device.poll(wgpu::Maintain::Wait);
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(BlindRotationGpuError::Execution(format!(
                "TFHE blind-rotation dispatch failed: {error}"
            )));
        }

        let slice = readback.slice(..);
        let (sender, receiver) = mpsc::sync_channel(1);
        slice.map_async(wgpu::MapMode::Read, move |status| {
            let _ = sender.send(status);
        });
        self.device.poll(wgpu::Maintain::Wait);
        receiver
            .recv()
            .map_err(|error| BlindRotationGpuError::Execution(error.to_string()))?
            .map_err(|error| BlindRotationGpuError::Execution(error.to_string()))?;
        let mapped = slice.get_mapped_range();
        let limbs: &[u32] = bytemuck::cast_slice(&mapped);
        if limbs.len() != glwe_coefficients * 2 {
            return Err(BlindRotationGpuError::Execution(format!(
                "TFHE blind-rotation readback has {} limbs; expected {}",
                limbs.len(),
                glwe_coefficients * 2
            )));
        }
        let coefficients = limbs
            .chunks_exact(2)
            .map(|pair| u64::from(pair[0]) | (u64::from(pair[1]) << 32))
            .collect();
        drop(mapped);
        readback.unmap();
        Ok(BlindRotationGpuResult {
            coefficients,
            adapter: self.adapter.clone(),
            backend: self.backend.clone(),
        })
    }
}

fn byte_len(coefficients: usize) -> Result<u64, BlindRotationGpuError> {
    coefficients
        .checked_mul(8)
        .and_then(|bytes| u64::try_from(bytes).ok())
        .ok_or_else(|| BlindRotationGpuError::Execution("GPU buffer size overflow".into()))
}

fn to_limbs(values: &[u64]) -> Vec<u32> {
    values
        .iter()
        .flat_map(|&value| [value as u32, (value >> 32) as u32])
        .collect()
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

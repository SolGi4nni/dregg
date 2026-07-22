//! Protocol-identical WGPU implementation of Plonky3's BabyBear^4 FRI fold.
//!
//! Dregg's repo-vendored `p3-fri` exposes a narrow `TwoAdicFriFoldBackend`
//! seam at the prover matrix fold.  Query-row folding and verification remain
//! upstream CPU code, while this backend computes the protocol-identical matrix
//! fold on WGPU with an exact CPU fallback.  The strict hbox gate requires a
//! real dispatch and compares complete seeded HidingFRI proof bytes.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock, mpsc};
use std::time::{Duration, Instant};

use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_fri::{CpuTwoAdicFriFold, TwoAdicFriFoldBackend};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use wgpu::util::DeviceExt;

/// The exact challenge field used by dregg's HidingFRI configuration.
pub type HidingFriChallenge = BinomialExtensionField<BabyBear, 4>;

#[inline]
fn challenge_coefficients(value: &HidingFriChallenge) -> &[BabyBear] {
    <HidingFriChallenge as BasedVectorSpace<BabyBear>>::as_basis_coefficients_slice(value)
}

/// Auditable aggregate work performed by this fold backend.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct HidingFriFoldCounters {
    pub gpu_folds: u64,
    pub gpu_input_elements: u64,
    pub gpu_output_elements: u64,
}

static GPU_FOLDS: AtomicU64 = AtomicU64::new(0);
static GPU_INPUT_ELEMENTS: AtomicU64 = AtomicU64::new(0);
static GPU_OUTPUT_ELEMENTS: AtomicU64 = AtomicU64::new(0);

pub fn hidingfri_fold_counters() -> HidingFriFoldCounters {
    HidingFriFoldCounters {
        gpu_folds: GPU_FOLDS.load(Ordering::Relaxed),
        gpu_input_elements: GPU_INPUT_ELEMENTS.load(Ordering::Relaxed),
        gpu_output_elements: GPU_OUTPUT_ELEMENTS.load(Ordering::Relaxed),
    }
}

/// Timing and hardware identity for one exact matrix fold.
#[derive(Clone, Debug)]
pub struct HidingFriFoldRun {
    pub output: Vec<HidingFriChallenge>,
    pub adapter_name: String,
    /// Includes upload, dispatch, synchronization, and readback, but excludes
    /// process-cold adapter/device/pipeline construction.
    pub elapsed: Duration,
}

struct FoldGpu {
    // Kept alive until after every resource created from it.
    _instance: wgpu::Instance,
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    bind_group_layout: wgpu::BindGroupLayout,
    adapter_name: String,
    max_storage_binding_size: u64,
}

static FOLD_GPU: OnceLock<Option<Mutex<FoldGpu>>> = OnceLock::new();

fn fold_gpu() -> Option<&'static Mutex<FoldGpu>> {
    FOLD_GPU
        .get_or_init(|| FoldGpu::new().map(Mutex::new))
        .as_ref()
}

impl FoldGpu {
    fn new() -> Option<Self> {
        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))?;
        let adapter_name = adapter.get_info().name;
        let limits = adapter.limits();
        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("hidingfri-fold-device"),
                required_features: wgpu::Features::empty(),
                required_limits: limits.clone(),
                memory_hints: Default::default(),
            },
            None,
        ))
        .ok()?;

        let storage = |binding| wgpu::BindGroupLayoutEntry {
            binding,
            visibility: wgpu::ShaderStages::COMPUTE,
            ty: wgpu::BindingType::Buffer {
                ty: wgpu::BufferBindingType::Storage {
                    read_only: binding != 2,
                },
                has_dynamic_offset: false,
                min_binding_size: None,
            },
            count: None,
        };
        let bind_group_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("hidingfri-fold-bgl"),
            entries: &[storage(0), storage(1), storage(2), storage(3)],
        });
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("hidingfri-fold-layout"),
            bind_group_layouts: &[&bind_group_layout],
            push_constant_ranges: &[],
        });
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("hidingfri-fold-ext4"),
            source: wgpu::ShaderSource::Wgsl(
                include_str!("shaders/hidingfri_fold_ext4.wgsl").into(),
            ),
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("hidingfri-fold-ext4"),
            layout: Some(&pipeline_layout),
            module: &shader,
            entry_point: Some("main"),
            compilation_options: Default::default(),
            cache: None,
        });

        Some(Self {
            _instance: instance,
            device,
            queue,
            pipeline,
            bind_group_layout,
            adapter_name,
            max_storage_binding_size: limits.max_storage_buffer_binding_size as u64,
        })
    }

    fn run(
        &self,
        beta: HidingFriChallenge,
        log_arity: usize,
        values: &[HidingFriChallenge],
    ) -> Result<HidingFriFoldRun, String> {
        if !(1..=3).contains(&log_arity) {
            return Err(format!(
                "HidingFRI WGPU fold supports deployed log arities 1..=3, got {log_arity}"
            ));
        }
        let arity = 1usize << log_arity;
        if values.is_empty() || !values.len().is_multiple_of(arity) {
            return Err(format!(
                "HidingFRI WGPU fold input length {} is not a positive multiple of arity {arity}",
                values.len()
            ));
        }
        let output_len = values.len() / arity;
        if output_len > u32::MAX as usize {
            return Err("HidingFRI WGPU fold output exceeds u32 dispatch geometry".to_string());
        }

        let input_words = values
            .iter()
            .flat_map(|value| {
                challenge_coefficients(value)
                    .iter()
                    .map(|coefficient| coefficient.as_canonical_u32())
            })
            .collect::<Vec<_>>();

        // This is exactly the base-field sequence constructed by the pinned
        // `TwoAdicFriFolding::fold_matrix` before its arity decomposition.
        let initial_height = values.len() / 2;
        let g_inv = BabyBear::two_adic_generator(values.len().trailing_zeros() as usize).inverse();
        let mut power = BabyBear::ONE.halve();
        let mut halve_inv_powers = Vec::with_capacity(initial_height);
        for _ in 0..initial_height {
            halve_inv_powers.push(power.as_canonical_u32());
            power *= g_inv;
        }
        bit_reverse(&mut halve_inv_powers);

        let beta_coefficients = challenge_coefficients(&beta);
        let params = [
            values.len() as u32,
            log_arity as u32,
            beta_coefficients[0].as_canonical_u32(),
            beta_coefficients[1].as_canonical_u32(),
            beta_coefficients[2].as_canonical_u32(),
            beta_coefficients[3].as_canonical_u32(),
        ];

        let input_size = (input_words.len() * 4) as u64;
        let powers_size = (halve_inv_powers.len() * 4) as u64;
        let output_size = (output_len * 4 * 4) as u64;
        for (label, size) in [
            ("input", input_size),
            ("powers", powers_size),
            ("output", output_size),
        ] {
            if size > self.max_storage_binding_size {
                return Err(format!(
                    "HidingFRI WGPU fold {label} buffer {size} exceeds adapter storage binding limit {}",
                    self.max_storage_binding_size
                ));
            }
        }

        let started = Instant::now();
        let input_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("hidingfri-fold-input"),
                contents: bytemuck::cast_slice(&input_words),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let powers_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("hidingfri-fold-powers"),
                contents: bytemuck::cast_slice(&halve_inv_powers),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let output_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("hidingfri-fold-output"),
            size: output_size,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let params_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("hidingfri-fold-params"),
                contents: bytemuck::cast_slice(&params),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let readback = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("hidingfri-fold-readback"),
            size: output_size,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("hidingfri-fold-bind-group"),
            layout: &self.bind_group_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: input_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: powers_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: output_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: params_buffer.as_entire_binding(),
                },
            ],
        });
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("hidingfri-fold-encoder"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("hidingfri-fold-pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups((output_len as u32).div_ceil(256), 1, 1);
        }
        encoder.copy_buffer_to_buffer(&output_buffer, 0, &readback, 0, output_size);
        self.queue.submit([encoder.finish()]);

        let slice = readback.slice(..);
        let (sender, receiver) = mpsc::sync_channel(1);
        slice.map_async(wgpu::MapMode::Read, move |result| {
            let _ = sender.send(result);
        });
        self.device.poll(wgpu::Maintain::Wait);
        receiver
            .recv()
            .map_err(|_| "HidingFRI WGPU fold map callback disappeared".to_string())?
            .map_err(|error| format!("HidingFRI WGPU fold readback failed: {error}"))?;
        let mapped = slice.get_mapped_range();
        let canonical_words = bytemuck::cast_slice::<u8, u32>(&mapped).to_vec();
        drop(mapped);
        readback.unmap();

        let output = canonical_words
            .chunks_exact(4)
            .map(|coefficients| {
                <HidingFriChallenge as BasedVectorSpace<BabyBear>>::from_basis_coefficients_fn(
                    |i| BabyBear::new(coefficients[i]),
                )
            })
            .collect::<Vec<_>>();
        GPU_FOLDS.fetch_add(1, Ordering::Relaxed);
        GPU_INPUT_ELEMENTS.fetch_add(values.len() as u64, Ordering::Relaxed);
        GPU_OUTPUT_ELEMENTS.fetch_add(output.len() as u64, Ordering::Relaxed);

        Ok(HidingFriFoldRun {
            output,
            adapter_name: self.adapter_name.clone(),
            elapsed: started.elapsed(),
        })
    }
}

fn bit_reverse<T>(values: &mut [T]) {
    assert!(values.len().is_power_of_two());
    let shift = usize::BITS - values.len().trailing_zeros();
    for index in 0..values.len() {
        let reversed = index.reverse_bits() >> shift;
        if index < reversed {
            values.swap(index, reversed);
        }
    }
}

/// Execute one exact deployed BabyBear^4 fold and fail if no GPU is present.
pub fn fold_hidingfri_matrix_wgpu_required(
    beta: HidingFriChallenge,
    log_arity: usize,
    values: &[HidingFriChallenge],
) -> Result<HidingFriFoldRun, String> {
    let gpu =
        fold_gpu().ok_or_else(|| "no high-performance WGPU adapter is available".to_string())?;
    gpu.lock()
        .map_err(|_| "HidingFRI WGPU fold mutex is poisoned".to_string())?
        .run(beta, log_arity, values)
}

/// Exact matrix-fold backend injected into the production HidingFRI PCS.
///
/// `require_gpu=true` is appropriate for the hbox qualification gate.  The
/// production portable setting uses an exact CPU fallback if adapter selection
/// or shader execution is unavailable.
#[derive(Clone, Copy, Debug)]
pub struct GpuHidingFriFold {
    require_gpu: bool,
}

impl GpuHidingFriFold {
    pub const fn new(require_gpu: bool) -> Self {
        Self { require_gpu }
    }
}

impl TwoAdicFriFoldBackend<BabyBear, HidingFriChallenge> for GpuHidingFriFold {
    fn fold_matrix<M: Matrix<HidingFriChallenge>>(
        &self,
        beta: HidingFriChallenge,
        log_arity: usize,
        matrix: M,
    ) -> Vec<HidingFriChallenge> {
        let width = matrix.width();
        let values = matrix.to_row_major_matrix().values;
        match fold_hidingfri_matrix_wgpu_required(beta, log_arity, &values) {
            Ok(run) => run.output,
            Err(error) if self.require_gpu => {
                panic!("required HidingFRI WGPU fold failed: {error}")
            }
            Err(_) => <CpuTwoAdicFriFold as TwoAdicFriFoldBackend<
                BabyBear,
                HidingFriChallenge,
            >>::fold_matrix(
                &CpuTwoAdicFriFold,
                beta,
                log_arity,
                RowMajorMatrix::new(values, width),
            ),
        }
    }
}

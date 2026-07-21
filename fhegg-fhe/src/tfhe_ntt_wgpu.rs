//! One-submit exact RNS-NTT batch for TFHE native-torus external products.
//!
//! This module is intentionally private to `tfhe_wgpu`: public callers see the
//! coefficient-domain oracle and an honestly labelled algorithm choice there.

use std::collections::HashMap;
use std::sync::{mpsc, Arc, Mutex, OnceLock};

use wgpu::util::DeviceExt;

pub(crate) const TORUS_NTT_MODULI: [u64; 4] =
    [1_073_750_017, 1_073_815_553, 1_073_872_897, 1_073_971_201];

pub(crate) struct NttBatchResult {
    /// Product-major, then modulus-row, then coefficient.
    pub residues: Vec<Vec<Vec<u64>>>,
    pub adapter: String,
    pub backend: String,
}

pub(crate) enum NttBatchError {
    Unavailable,
    Execution(String),
}

enum GpuState {
    Ready(GpuContext),
    Unavailable,
    Broken(String),
}

fn gpu_state() -> &'static GpuState {
    static GPU: OnceLock<GpuState> = OnceLock::new();
    GPU.get_or_init(GpuContext::initialize)
}

pub(crate) fn multiply_signed_batch(
    lhs: &[Vec<i64>],
    rhs: &[Vec<i64>],
    degree: usize,
) -> Result<NttBatchResult, NttBatchError> {
    if lhs.is_empty()
        || lhs.len() != rhs.len()
        || degree < 8
        || degree > 4096
        || !degree.is_power_of_two()
        || lhs.iter().chain(rhs).any(|poly| poly.len() != degree)
    {
        return Err(NttBatchError::Execution(
            "invalid preflighted torus NTT batch shape".to_owned(),
        ));
    }
    let order = u64::try_from(degree)
        .ok()
        .and_then(|n| n.checked_mul(2))
        .ok_or_else(|| NttBatchError::Execution("torus NTT order overflow".to_owned()))?;
    if TORUS_NTT_MODULI.iter().any(|q| (q - 1) % order != 0) {
        return Err(NttBatchError::Execution(
            "torus NTT modulus lacks the requested root order".to_owned(),
        ));
    }
    match gpu_state() {
        GpuState::Ready(gpu) => gpu.run(lhs, rhs, degree),
        GpuState::Unavailable => Err(NttBatchError::Unavailable),
        GpuState::Broken(error) => Err(NttBatchError::Execution(error.clone())),
    }
}

pub(crate) struct RowPlan {
    pub(crate) roots: Vec<u32>,
    pub(crate) inverse_roots: Vec<u32>,
    pub(crate) twists: Vec<u32>,
    pub(crate) inverse_twists_times_n_inv: Vec<u32>,
    pub(crate) q_inv: u32,
    pub(crate) montgomery_r: u64,
}

pub(crate) struct HostPlan {
    pub(crate) rows: Vec<RowPlan>,
    pub(crate) qdata: Vec<u32>,
    pub(crate) roots: Vec<u32>,
    pub(crate) twists: Vec<u32>,
}

fn mod_mul(a: u64, b: u64, modulus: u64) -> u64 {
    ((u128::from(a) * u128::from(b)) % u128::from(modulus)) as u64
}

fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut output = 1u64;
    while exponent != 0 {
        if exponent & 1 != 0 {
            output = mod_mul(output, base, modulus);
        }
        exponent >>= 1;
        if exponent != 0 {
            base = mod_mul(base, base, modulus);
        }
    }
    output
}

fn powers_montgomery(base: u64, count: usize, modulus: u64, r: u64) -> Vec<u32> {
    let mut output = Vec::with_capacity(count);
    let mut value = 1u64;
    for _ in 0..count {
        output.push(mod_mul(value, r, modulus) as u32);
        value = mod_mul(value, base, modulus);
    }
    output
}

fn inverse_mod_2_32(odd: u32) -> u32 {
    // Newton iteration doubles the number of correct low bits each round.
    let mut inverse = odd;
    for _ in 0..5 {
        inverse = inverse.wrapping_mul(2u32.wrapping_sub(odd.wrapping_mul(inverse)));
    }
    inverse
}

fn is_prime_u32(value: u32) -> bool {
    if value < 2 || value % 2 == 0 {
        return value == 2;
    }
    let mut divisor = 3u32;
    while u64::from(divisor) * u64::from(divisor) <= u64::from(value) {
        if value % divisor == 0 {
            return false;
        }
        divisor += 2;
    }
    true
}

fn build_row_plan(q: u64, degree: usize) -> Result<RowPlan, NttBatchError> {
    if !is_prime_u32(q as u32) {
        return Err(NttBatchError::Execution(format!(
            "TFHE NTT modulus {q} is not prime"
        )));
    }
    let order = (degree as u64) * 2;
    let exponent = (q - 1) / order;
    let psi = (2u64..=1_000_000)
        .map(|candidate| mod_pow(candidate, exponent, q))
        .find(|&root| mod_pow(root, degree as u64, q) == q - 1)
        .ok_or_else(|| {
            NttBatchError::Execution(format!("no primitive {order}-th root modulo {q}"))
        })?;
    let psi_inv = mod_pow(psi, q - 2, q);
    let omega = mod_mul(psi, psi, q);
    let omega_inv = mod_pow(omega, q - 2, q);
    let n_inv = mod_pow((degree as u64) % q, q - 2, q);
    let montgomery_r = ((1u128 << 32) % u128::from(q)) as u64;
    let roots = powers_montgomery(omega, degree, q, montgomery_r);
    let inverse_roots = powers_montgomery(omega_inv, degree, q, montgomery_r);
    let twists = powers_montgomery(psi, degree, q, montgomery_r);
    let inverse_twists_times_n_inv = powers_montgomery(psi_inv, degree, q, montgomery_r)
        .into_iter()
        .map(|value_mont| {
            // value_mont = value*R. Multiplying the canonical n^-1 before
            // upload preserves exactly one Montgomery factor.
            mod_mul(u64::from(value_mont), n_inv, q) as u32
        })
        .collect();
    Ok(RowPlan {
        roots,
        inverse_roots,
        twists,
        inverse_twists_times_n_inv,
        q_inv: inverse_mod_2_32(q as u32).wrapping_neg(),
        montgomery_r,
    })
}

pub(crate) fn host_plan(degree: usize) -> Result<Arc<HostPlan>, NttBatchError> {
    static PLANS: OnceLock<Mutex<HashMap<usize, Arc<HostPlan>>>> = OnceLock::new();
    let plans = PLANS.get_or_init(|| Mutex::new(HashMap::new()));
    let mut plans = plans
        .lock()
        .map_err(|_| NttBatchError::Execution("TFHE NTT host-plan cache poisoned".to_owned()))?;
    if let Some(plan) = plans.get(&degree) {
        return Ok(Arc::clone(plan));
    }
    let rows = TORUS_NTT_MODULI
        .iter()
        .map(|&q| build_row_plan(q, degree))
        .collect::<Result<Vec<_>, _>>()?;
    let mut qdata = Vec::with_capacity(rows.len() * 4);
    let mut roots = Vec::with_capacity(rows.len() * degree * 2);
    let mut twists = Vec::with_capacity(rows.len() * degree * 2);
    for (&q, row) in TORUS_NTT_MODULI.iter().zip(&rows) {
        let r_squared = mod_mul(row.montgomery_r, row.montgomery_r, q) as u32;
        qdata.extend_from_slice(&[q as u32, row.q_inv, r_squared, 0]);
        roots.extend(row.roots.iter().chain(&row.inverse_roots));
        twists.extend(row.twists.iter().chain(&row.inverse_twists_times_n_inv));
    }
    let plan = Arc::new(HostPlan {
        rows,
        qdata,
        roots,
        twists,
    });
    plans.insert(degree, Arc::clone(&plan));
    Ok(plan)
}

pub(crate) fn signed_residue(value: i64, modulus: u64) -> u64 {
    i128::from(value).rem_euclid(i128::from(modulus)) as u64
}

struct GpuContext {
    _instance: wgpu::Instance,
    device: wgpu::Device,
    queue: wgpu::Queue,
    adapter: String,
    backend: String,
    limits: wgpu::Limits,
    bgl: wgpu::BindGroupLayout,
    fused_product: wgpu::ComputePipeline,
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
            return GpuState::Unavailable;
        };
        let info = adapter.get_info();
        let limits = adapter.limits();
        let (device, queue) = match pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("TFHE exact RNS-NTT batch"),
                required_features: wgpu::Features::empty(),
                required_limits: limits.clone(),
                memory_hints: Default::default(),
            },
            None,
        )) {
            Ok(pair) => pair,
            Err(_) => return GpuState::Unavailable,
        };
        device.push_error_scope(wgpu::ErrorFilter::Validation);
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("torus_ntt_montgomery.wgsl"),
            source: wgpu::ShaderSource::Wgsl(
                include_str!("shaders/torus_ntt_montgomery.wgsl").into(),
            ),
        });
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("TFHE exact RNS-NTT bindings"),
            entries: &[
                buffer_entry(0, wgpu::BufferBindingType::Uniform),
                buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(5, wgpu::BufferBindingType::Storage { read_only: true }),
            ],
        });
        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("TFHE exact RNS-NTT layout"),
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
        let fused_product = make("fused_product");
        let context = Self {
            _instance: instance,
            device,
            queue,
            adapter: info.name,
            backend: format!("{:?}", info.backend),
            limits,
            bgl,
            fused_product,
        };
        if let Some(error) = pollster::block_on(context.device.pop_error_scope()) {
            return GpuState::Broken(format!(
                "TFHE exact RNS-NTT shader validation failed: {error}"
            ));
        }
        GpuState::Ready(context)
    }

    fn run(
        &self,
        lhs: &[Vec<i64>],
        rhs: &[Vec<i64>],
        degree: usize,
    ) -> Result<NttBatchResult, NttBatchError> {
        let products = lhs.len();
        let rows = TORUS_NTT_MODULI.len();
        let series = products
            .checked_mul(rows)
            .ok_or_else(|| NttBatchError::Execution("NTT series count overflow".to_owned()))?;
        let coefficients = series
            .checked_mul(degree)
            .ok_or_else(|| NttBatchError::Execution("NTT coefficient count overflow".to_owned()))?;
        let bytes = coefficients
            .checked_mul(std::mem::size_of::<u32>())
            .and_then(|n| u64::try_from(n).ok())
            .ok_or_else(|| NttBatchError::Execution("NTT buffer size overflow".to_owned()))?;
        let table_bytes = rows
            .checked_mul(degree)
            .and_then(|n| n.checked_mul(2))
            .and_then(|n| n.checked_mul(std::mem::size_of::<u32>()))
            .and_then(|n| u64::try_from(n).ok())
            .ok_or_else(|| NttBatchError::Execution("NTT table size overflow".to_owned()))?;
        let binding_limit = self
            .limits
            .max_buffer_size
            .min(u64::from(self.limits.max_storage_buffer_binding_size));
        let series_u32 = u32::try_from(series).map_err(|_| NttBatchError::Unavailable)?;
        if bytes > binding_limit
            || table_bytes > binding_limit
            || self.limits.max_storage_buffers_per_shader_stage < 5
            || self.limits.max_compute_invocations_per_workgroup < 256
            || self.limits.max_compute_workgroup_size_x < 256
            || self.limits.max_compute_workgroup_storage_size < 4096 * 4
            || series_u32 > self.limits.max_compute_workgroups_per_dimension
        {
            return Err(NttBatchError::Unavailable);
        }

        let plan = host_plan(degree)?;
        let pack = |polynomials: &[Vec<i64>]| {
            let mut output = Vec::with_capacity(coefficients);
            for polynomial in polynomials {
                for (&q, row) in TORUS_NTT_MODULI.iter().zip(&plan.rows) {
                    output.extend(polynomial.iter().map(|&value| {
                        mod_mul(signed_residue(value, q), row.montgomery_r, q) as u32
                    }));
                }
            }
            output
        };
        let lhs_words = pack(lhs);
        let rhs_words = pack(rhs);

        self.device.push_error_scope(wgpu::ErrorFilter::Validation);
        let lhs_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE NTT lhs batch"),
                contents: bytemuck::cast_slice(&lhs_words),
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            });
        let rhs_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE NTT rhs batch"),
                contents: bytemuck::cast_slice(&rhs_words),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let q_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE NTT moduli"),
                contents: bytemuck::cast_slice(&plan.qdata),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let root_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE NTT roots"),
                contents: bytemuck::cast_slice(&plan.roots),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let twist_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE NTT twists"),
                contents: bytemuck::cast_slice(&plan.twists),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let read_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("TFHE NTT one-shot readback"),
            size: bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("TFHE NTT one-submit external product"),
            });
        let degree_u32 = degree as u32;
        let rows_u32 = rows as u32;
        let products_u32 = products as u32;
        let metadata = [
            degree_u32,
            degree.trailing_zeros(),
            0,
            0,
            0,
            rows_u32,
            products_u32,
            0,
        ];
        let metadata_buffer = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("TFHE fused NTT metadata"),
                contents: bytemuck::cast_slice(&metadata),
                usage: wgpu::BufferUsages::UNIFORM,
            });
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("TFHE fused NTT bind group"),
            layout: &self.bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: metadata_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: lhs_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: rhs_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: q_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 4,
                    resource: root_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 5,
                    resource: twist_buf.as_entire_binding(),
                },
            ],
        });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("TFHE fused exact NTT product"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.fused_product);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups(1, series_u32, 1);
        }
        encoder.copy_buffer_to_buffer(&lhs_buf, 0, &read_buf, 0, bytes);
        self.queue.submit([encoder.finish()]);
        self.device.poll(wgpu::Maintain::Wait);
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(NttBatchError::Execution(format!(
                "TFHE NTT buffer/bind/dispatch validation failed: {error}"
            )));
        }
        let slice = read_buf.slice(..);
        let (sender, receiver) = mpsc::sync_channel(1);
        slice.map_async(wgpu::MapMode::Read, move |status| {
            let _ = sender.send(status);
        });
        self.device.poll(wgpu::Maintain::Wait);
        receiver
            .recv()
            .map_err(|error| NttBatchError::Execution(error.to_string()))?
            .map_err(|error| NttBatchError::Execution(error.to_string()))?;
        let mapped = slice.get_mapped_range();
        let words: &[u32] = bytemuck::cast_slice(&mapped);
        if words.len() != coefficients {
            return Err(NttBatchError::Execution(format!(
                "TFHE NTT readback has {} residues; expected {coefficients}",
                words.len()
            )));
        }
        let mut output = Vec::with_capacity(products);
        let mut cursor = 0usize;
        for _ in 0..products {
            let mut product = Vec::with_capacity(rows);
            for &q in &TORUS_NTT_MODULI {
                let row = words[cursor..cursor + degree]
                    .iter()
                    .map(|&value| u64::from(value))
                    .collect::<Vec<_>>();
                if let Some((coefficient, &value)) =
                    row.iter().enumerate().find(|(_, value)| **value >= q)
                {
                    return Err(NttBatchError::Execution(format!(
                        "TFHE NTT emitted non-canonical residue at coefficient {coefficient}: {value} >= {q}"
                    )));
                }
                cursor += degree;
                product.push(row);
            }
            output.push(product);
        }
        drop(mapped);
        read_buf.unmap();
        Ok(NttBatchResult {
            residues: output,
            adapter: self.adapter.clone(),
            backend: self.backend.clone(),
        })
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

//! Portable, bit-exact GPU negacyclic polynomial multiplication for the BFV
//! RNS representation already used by [`crate::bfv_lean`] and the private-book
//! proof.
//!
//! `LeanCiphertext` serialization exposes power-basis residue rows.  This
//! module multiplies two such [`RnsPoly`] values in
//! `Z_q[X]/(X^n + 1)`: twist by a primitive `2n`-th root, cyclic radix-2 NTT,
//! pointwise multiply, inverse NTT, and untwist.  The WGSL shader uses split
//! `u32` limbs and exact double-and-add modular multiplication, so it requires
//! no CUDA, HIP, native `u64`, or vendor extension.
//!
//! The scope is deliberately below full BFV ciphertext multiplication.  It
//! does not perform BFV's extended-basis scaling, tensor assembly, or
//! relinearization; [`crate::bfv_mul`] remains the semantic ct×ct oracle.  This
//! is the first portable arithmetic organ needed underneath that operation.
//!
//! [`RnsNttEngine`] reports whether the result came from wgpu or an explicit
//! CPU capability fallback.  Invalid shapes, composite/non-NTT moduli,
//! non-canonical residues, and GPU execution failures never fall back and are
//! never relabeled as a successful GPU computation.

use std::fmt;
use std::sync::{mpsc, OnceLock};

use fhe_math::rq::Context;

use crate::bfv_lean::RnsPoly;

const WORKGROUP_SIZE: u32 = 64;
const MAX_DEGREE: usize = 1 << 16;
const MAX_RNS_ROWS: usize = 16;

type Result<T> = std::result::Result<T, BfvNttError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BfvNttError {
    InvalidShape(&'static str),
    UnsupportedParameters(String),
    NonCanonical {
        operand: &'static str,
        row: usize,
        coefficient: usize,
        value: u64,
        modulus: u64,
    },
    GpuExecution(String),
}

impl fmt::Display for BfvNttError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidShape(what) => write!(f, "invalid RNS polynomial shape: {what}"),
            Self::UnsupportedParameters(what) => {
                write!(f, "unsupported RNS NTT parameters: {what}")
            }
            Self::NonCanonical {
                operand,
                row,
                coefficient,
                value,
                modulus,
            } => write!(
                f,
                "non-canonical {operand} residue at row {row}, coefficient {coefficient}: \
                 {value} >= q = {modulus}"
            ),
            Self::GpuExecution(what) => write!(f, "wgpu RNS NTT failed: {what}"),
        }
    }
}

impl std::error::Error for BfvNttError {}

/// The arithmetic backend that actually produced a polynomial product.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RnsNttBackend {
    Wgpu {
        adapter: String,
    },
    /// Deterministic caller policy (from [`RnsNttEngine::cpu_only`]).
    CpuPolicy,
    /// No adapter/device could be acquired. The reason is retained rather
    /// than turning a CPU result into an apparent GPU green.
    CpuUnavailable {
        reason: String,
    },
    /// An adapter exists but its advertised buffer/dispatch limits cannot run
    /// this preflighted shape.
    CpuAdapterLimits {
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsNttExecution {
    pub polynomial: RnsPoly,
    pub backend: RnsNttBackend,
}

/// Reusable dispatch policy. GPU initialization is process-wide and lazy.
pub struct RnsNttEngine {
    cpu_only: bool,
}

impl RnsNttEngine {
    pub fn new() -> Self {
        Self { cpu_only: false }
    }

    /// Force the exact CPU reference and label it as policy-selected. This is
    /// useful both for deployments that forbid accelerators and for a
    /// deterministic fallback/parity gate.
    pub fn cpu_only() -> Self {
        Self { cpu_only: true }
    }

    pub fn has_gpu(&self) -> bool {
        !self.cpu_only && matches!(gpu_state(), GpuState::Ready(_))
    }

    pub fn multiply(
        &self,
        lhs: &RnsPoly,
        rhs: &RnsPoly,
        moduli: &[u64],
    ) -> Result<RnsNttExecution> {
        let plan = NttPlan::new(lhs, rhs, moduli)?;
        if self.cpu_only {
            return Ok(RnsNttExecution {
                polynomial: multiply_cpu_with_plan(lhs, rhs, &plan),
                backend: RnsNttBackend::CpuPolicy,
            });
        }
        match gpu_state() {
            GpuState::Unavailable(reason) => Ok(RnsNttExecution {
                polynomial: multiply_cpu_with_plan(lhs, rhs, &plan),
                backend: RnsNttBackend::CpuUnavailable {
                    reason: reason.clone(),
                },
            }),
            GpuState::Broken(reason) => Err(BfvNttError::GpuExecution(reason.clone())),
            GpuState::Ready(gpu) => {
                if let Err(reason) = gpu.supports(&plan) {
                    return Ok(RnsNttExecution {
                        polynomial: multiply_cpu_with_plan(lhs, rhs, &plan),
                        backend: RnsNttBackend::CpuAdapterLimits { reason },
                    });
                }
                Ok(RnsNttExecution {
                    polynomial: gpu.multiply(lhs, rhs, &plan)?,
                    backend: RnsNttBackend::Wgpu {
                        adapter: gpu.adapter.clone(),
                    },
                })
            }
        }
    }
}

impl Default for RnsNttEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// One-call convenience. Retain an [`RnsNttEngine`] when backend observation
/// or repeated calls matter.
pub fn multiply_rns_gpu_or_cpu(
    lhs: &RnsPoly,
    rhs: &RnsPoly,
    moduli: &[u64],
) -> Result<RnsNttExecution> {
    RnsNttEngine::new().multiply(lhs, rhs, moduli)
}

/// Exact CPU reference/fallback for negacyclic RNS multiplication.
pub fn multiply_rns_cpu(lhs: &RnsPoly, rhs: &RnsPoly, moduli: &[u64]) -> Result<RnsPoly> {
    let plan = NttPlan::new(lhs, rhs, moduli)?;
    Ok(multiply_cpu_with_plan(lhs, rhs, &plan))
}

#[derive(Clone)]
struct RowPlan {
    roots: Vec<u64>,
    inverse_roots: Vec<u64>,
    twists: Vec<u64>,
    inverse_twists_times_n_inv: Vec<u64>,
}

struct NttPlan {
    degree: usize,
    log_degree: u32,
    moduli: Vec<u64>,
    rows: Vec<RowPlan>,
}

impl NttPlan {
    fn new(lhs: &RnsPoly, rhs: &RnsPoly, moduli: &[u64]) -> Result<Self> {
        if moduli.is_empty() {
            return Err(BfvNttError::InvalidShape("modulus set is empty"));
        }
        if moduli.len() > MAX_RNS_ROWS {
            return Err(BfvNttError::InvalidShape(
                "RNS row count exceeds the bounded GPU/CPU plan",
            ));
        }
        if lhs.rows.len() != moduli.len() || rhs.rows.len() != moduli.len() {
            return Err(BfvNttError::InvalidShape(
                "operand row count differs from modulus count",
            ));
        }
        let degree = lhs.rows[0].len();
        if degree < 8 || !degree.is_power_of_two() {
            return Err(BfvNttError::InvalidShape(
                "degree must be a power of two at least 8",
            ));
        }
        if degree > MAX_DEGREE {
            return Err(BfvNttError::InvalidShape(
                "degree exceeds the bounded NTT implementation",
            ));
        }
        if lhs.rows.iter().any(|row| row.len() != degree)
            || rhs.rows.iter().any(|row| row.len() != degree)
        {
            return Err(BfvNttError::InvalidShape(
                "all operand rows must have the same degree",
            ));
        }
        for (operand, poly) in [("lhs", lhs), ("rhs", rhs)] {
            for (row, (&q, coefficients)) in moduli.iter().zip(&poly.rows).enumerate() {
                for (coefficient, &value) in coefficients.iter().enumerate() {
                    if value >= q {
                        return Err(BfvNttError::NonCanonical {
                            operand,
                            row,
                            coefficient,
                            value,
                            modulus: q,
                        });
                    }
                }
            }
        }
        if moduli.iter().any(|&q| q >= (1u64 << 62)) {
            return Err(BfvNttError::UnsupportedParameters(
                "moduli must be below 2^62 so every split-u32 add stays below 2^63".to_owned(),
            ));
        }
        // This is the same prime/2n-root/coprimality constructor fhe.rs uses.
        // It is a fail-closed parameter guard, not merely a root-search guess.
        Context::new(moduli, degree).map_err(|error| {
            BfvNttError::UnsupportedParameters(format!(
                "fhe-math rejected the modulus set/degree: {error}"
            ))
        })?;

        let mut rows = Vec::with_capacity(moduli.len());
        for &q in moduli {
            rows.push(build_row_plan(q, degree)?);
        }
        Ok(Self {
            degree,
            log_degree: degree.trailing_zeros(),
            moduli: moduli.to_vec(),
            rows,
        })
    }
}

fn build_row_plan(q: u64, degree: usize) -> Result<RowPlan> {
    let order = (degree as u64)
        .checked_mul(2)
        .ok_or(BfvNttError::InvalidShape("2*degree overflows u64"))?;
    let exponent = (q - 1) / order;
    let mut psi = None;
    for candidate in 2u64..=1_000_000 {
        let root = mod_pow(candidate, exponent, q);
        if mod_pow(root, degree as u64, q) == q - 1 {
            psi = Some(root);
            break;
        }
    }
    let psi = psi.ok_or_else(|| {
        BfvNttError::UnsupportedParameters(format!("no primitive {order}-th root found modulo {q}"))
    })?;
    let psi_inv = mod_pow(psi, q - 2, q);
    let omega = mod_mul(psi, psi, q);
    let omega_inv = mod_pow(omega, q - 2, q);
    let n_inv = mod_pow((degree as u64) % q, q - 2, q);

    let roots = powers(omega, degree, q);
    let inverse_roots = powers(omega_inv, degree, q);
    let twists = powers(psi, degree, q);
    let inverse_twists_times_n_inv = powers(psi_inv, degree, q)
        .into_iter()
        .map(|value| mod_mul(value, n_inv, q))
        .collect();
    Ok(RowPlan {
        roots,
        inverse_roots,
        twists,
        inverse_twists_times_n_inv,
    })
}

fn powers(base: u64, count: usize, modulus: u64) -> Vec<u64> {
    let mut out = Vec::with_capacity(count);
    let mut value = 1u64;
    for _ in 0..count {
        out.push(value);
        value = mod_mul(value, base, modulus);
    }
    out
}

fn mod_mul(a: u64, b: u64, modulus: u64) -> u64 {
    ((u128::from(a) * u128::from(b)) % u128::from(modulus)) as u64
}

fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut out = 1u64;
    while exponent != 0 {
        if exponent & 1 != 0 {
            out = mod_mul(out, base, modulus);
        }
        exponent >>= 1;
        if exponent != 0 {
            base = mod_mul(base, base, modulus);
        }
    }
    out
}

fn add_mod(a: u64, b: u64, modulus: u64) -> u64 {
    let sum = a + b;
    if sum >= modulus {
        sum - modulus
    } else {
        sum
    }
}

fn sub_mod(a: u64, b: u64, modulus: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        modulus - (b - a)
    }
}

fn bit_reverse_permute(values: &mut [u64]) {
    let bits = values.len().trailing_zeros();
    for i in 0..values.len() {
        let j = i.reverse_bits() >> (usize::BITS - bits);
        if i < j {
            values.swap(i, j);
        }
    }
}

fn cyclic_ntt(values: &mut [u64], roots: &[u64], modulus: u64) {
    bit_reverse_permute(values);
    let degree = values.len();
    let mut len = 2usize;
    while len <= degree {
        let half = len / 2;
        let step = degree / len;
        for block in (0..degree).step_by(len) {
            for j in 0..half {
                let u = values[block + j];
                let v = mod_mul(values[block + j + half], roots[j * step], modulus);
                values[block + j] = add_mod(u, v, modulus);
                values[block + j + half] = sub_mod(u, v, modulus);
            }
        }
        len *= 2;
    }
}

fn multiply_cpu_with_plan(lhs: &RnsPoly, rhs: &RnsPoly, plan: &NttPlan) -> RnsPoly {
    let mut rows = Vec::with_capacity(plan.moduli.len());
    for (row, ((left, right), &q)) in lhs.rows.iter().zip(&rhs.rows).zip(&plan.moduli).enumerate() {
        let row_plan = &plan.rows[row];
        let mut a: Vec<u64> = left
            .iter()
            .zip(&row_plan.twists)
            .map(|(&value, &twist)| mod_mul(value, twist, q))
            .collect();
        let mut b: Vec<u64> = right
            .iter()
            .zip(&row_plan.twists)
            .map(|(&value, &twist)| mod_mul(value, twist, q))
            .collect();
        cyclic_ntt(&mut a, &row_plan.roots, q);
        cyclic_ntt(&mut b, &row_plan.roots, q);
        for (value, &other) in a.iter_mut().zip(&b) {
            *value = mod_mul(*value, other, q);
        }
        cyclic_ntt(&mut a, &row_plan.inverse_roots, q);
        for (value, &scale) in a.iter_mut().zip(&row_plan.inverse_twists_times_n_inv) {
            *value = mod_mul(*value, scale, q);
        }
        rows.push(a);
    }
    RnsPoly { rows }
}

enum GpuState {
    Ready(GpuCtx),
    Unavailable(String),
    /// Adapter initialization reached our shader, so a validation failure is
    /// an implementation bug rather than a capability fallback.
    Broken(String),
}

fn gpu_state() -> &'static GpuState {
    static GPU: OnceLock<GpuState> = OnceLock::new();
    GPU.get_or_init(GpuCtx::initialize)
}

struct GpuCtx {
    _instance: wgpu::Instance,
    device: wgpu::Device,
    queue: wgpu::Queue,
    adapter: String,
    limits: wgpu::Limits,
    bgl: wgpu::BindGroupLayout,
    twist_both: wgpu::ComputePipeline,
    bit_reverse_both: wgpu::ComputePipeline,
    stage_both: wgpu::ComputePipeline,
    pointwise: wgpu::ComputePipeline,
    bit_reverse_lhs: wgpu::ComputePipeline,
    stage_lhs: wgpu::ComputePipeline,
    finalize_lhs: wgpu::ComputePipeline,
}

impl GpuCtx {
    fn initialize() -> GpuState {
        let instance = wgpu::Instance::default();
        let Some(adapter) =
            pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                ..Default::default()
            }))
        else {
            return GpuState::Unavailable("no wgpu adapter".to_owned());
        };
        let info = adapter.get_info();
        let limits = adapter.limits();
        let (device, queue) = match pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("bfv-rns-ntt"),
                required_features: wgpu::Features::empty(),
                required_limits: limits.clone(),
                memory_hints: Default::default(),
            },
            None,
        )) {
            Ok(pair) => pair,
            Err(error) => {
                return GpuState::Unavailable(format!("wgpu device request failed: {error}"));
            }
        };

        device.push_error_scope(wgpu::ErrorFilter::Validation);
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("bfv_ntt.wgsl"),
            source: wgpu::ShaderSource::Wgsl(include_str!("shaders/bfv_ntt.wgsl").into()),
        });
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("bfv-rns-ntt-bindings"),
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
            label: Some("bfv-rns-ntt-layout"),
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let make_pipeline = |entry: &'static str| {
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry),
                layout: Some(&layout),
                module: &shader,
                entry_point: Some(entry),
                compilation_options: Default::default(),
                cache: None,
            })
        };
        let twist_both = make_pipeline("twist_both");
        let bit_reverse_both = make_pipeline("bit_reverse_both");
        let stage_both = make_pipeline("stage_both");
        let pointwise = make_pipeline("pointwise");
        let bit_reverse_lhs = make_pipeline("bit_reverse_lhs");
        let stage_lhs = make_pipeline("stage_lhs");
        let finalize_lhs = make_pipeline("finalize_lhs");
        if let Some(error) = pollster::block_on(device.pop_error_scope()) {
            return GpuState::Broken(format!("BFV NTT shader validation failed: {error}"));
        }
        GpuState::Ready(Self {
            _instance: instance,
            device,
            queue,
            adapter: format!("{} ({:?})", info.name, info.backend),
            limits,
            bgl,
            twist_both,
            bit_reverse_both,
            stage_both,
            pointwise,
            bit_reverse_lhs,
            stage_lhs,
            finalize_lhs,
        })
    }

    fn supports(&self, plan: &NttPlan) -> std::result::Result<(), String> {
        if self.limits.max_storage_buffers_per_shader_stage < 5 {
            return Err(format!(
                "adapter exposes {} storage buffers per compute stage; 5 required",
                self.limits.max_storage_buffers_per_shader_stage
            ));
        }
        let rows = plan.moduli.len() as u64;
        let degree = plan.degree as u64;
        let coefficient_bytes = rows
            .checked_mul(degree)
            .and_then(|count| count.checked_mul(8))
            .ok_or_else(|| "coefficient buffer size overflow".to_owned())?;
        let table_bytes = coefficient_bytes
            .checked_mul(2)
            .ok_or_else(|| "root/twist table size overflow".to_owned())?;
        let max_storage = self
            .limits
            .max_buffer_size
            .min(u64::from(self.limits.max_storage_buffer_binding_size));
        if coefficient_bytes > max_storage || table_bytes > max_storage {
            return Err(format!(
                "shape needs {coefficient_bytes}-byte coefficient and {table_bytes}-byte table \
                 bindings, adapter limit is {max_storage}"
            ));
        }
        let workgroups_x = (plan.degree as u32).div_ceil(WORKGROUP_SIZE);
        if workgroups_x > self.limits.max_compute_workgroups_per_dimension
            || plan.moduli.len() as u32 > self.limits.max_compute_workgroups_per_dimension
        {
            return Err("dispatch dimensions exceed adapter limits".to_owned());
        }
        Ok(())
    }

    fn multiply(&self, lhs: &RnsPoly, rhs: &RnsPoly, plan: &NttPlan) -> Result<RnsPoly> {
        use wgpu::util::DeviceExt;

        // Any buffer/bind/dispatch validation failure is a kernel error. It
        // must not escape as an uncaptured panic or be converted into a CPU
        // capability fallback.
        self.device.push_error_scope(wgpu::ErrorFilter::Validation);

        let pack = |poly: &RnsPoly| -> Vec<u32> {
            let mut words = Vec::with_capacity(plan.moduli.len() * plan.degree * 2);
            for row in &poly.rows {
                for &value in row {
                    words.push(value as u32);
                    words.push((value >> 32) as u32);
                }
            }
            words
        };
        let mut qdata = Vec::with_capacity(plan.moduli.len() * 4);
        let mut roots = Vec::with_capacity(plan.moduli.len() * plan.degree * 4);
        let mut twists = Vec::with_capacity(plan.moduli.len() * plan.degree * 4);
        for (&q, row) in plan.moduli.iter().zip(&plan.rows) {
            qdata.extend_from_slice(&[q as u32, (q >> 32) as u32, 64 - q.leading_zeros(), 0]);
            for &value in row.roots.iter().chain(&row.inverse_roots) {
                roots.extend_from_slice(&[value as u32, (value >> 32) as u32]);
            }
            for &value in row.twists.iter().chain(&row.inverse_twists_times_n_inv) {
                twists.extend_from_slice(&[value as u32, (value >> 32) as u32]);
            }
        }

        let lhs_words = pack(lhs);
        let rhs_words = pack(rhs);
        let lhs_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("bfv-ntt-lhs"),
                contents: bytemuck::cast_slice(&lhs_words),
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            });
        let rhs_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("bfv-ntt-rhs"),
                contents: bytemuck::cast_slice(&rhs_words),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let q_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("bfv-ntt-moduli"),
                contents: bytemuck::cast_slice(&qdata),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let root_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("bfv-ntt-roots"),
                contents: bytemuck::cast_slice(&roots),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let twist_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("bfv-ntt-twists"),
                contents: bytemuck::cast_slice(&twists),
                usage: wgpu::BufferUsages::STORAGE,
            });

        let output_bytes = (lhs_words.len() * std::mem::size_of::<u32>()) as u64;
        let read_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("bfv-ntt-readback"),
            size: output_bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });

        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("bfv-rns-ntt"),
            });
        let mut metadata_buffers = Vec::new();
        let mut bind_groups = Vec::new();
        let rows = plan.moduli.len() as u32;
        let degree = plan.degree as u32;
        let log_degree = plan.log_degree;
        let mut dispatch =
            |pipeline: &wgpu::ComputePipeline, meta: [u32; 8], invocations_x: u32| {
                let meta_buf = self
                    .device
                    .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                        label: Some("bfv-ntt-meta"),
                        contents: bytemuck::cast_slice(&meta),
                        usage: wgpu::BufferUsages::UNIFORM,
                    });
                let bind = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                    label: Some("bfv-ntt-bind"),
                    layout: &self.bgl,
                    entries: &[
                        wgpu::BindGroupEntry {
                            binding: 0,
                            resource: meta_buf.as_entire_binding(),
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
                        label: Some("bfv-ntt-dispatch"),
                        timestamp_writes: None,
                    });
                    pass.set_pipeline(pipeline);
                    pass.set_bind_group(0, &bind, &[]);
                    pass.dispatch_workgroups(invocations_x.div_ceil(WORKGROUP_SIZE), rows, 1);
                }
                metadata_buffers.push(meta_buf);
                bind_groups.push(bind);
            };

        let base_meta = [degree, log_degree, 0, 0, 0, rows, 0, 0];
        dispatch(&self.twist_both, base_meta, degree);
        dispatch(&self.bit_reverse_both, base_meta, degree);
        let mut len = 2u32;
        while len <= degree {
            let half = len / 2;
            let step = degree / len;
            dispatch(
                &self.stage_both,
                [degree, log_degree, half, step, 0, rows, 0, 0],
                degree / 2,
            );
            len *= 2;
        }
        dispatch(&self.pointwise, base_meta, degree);
        dispatch(&self.bit_reverse_lhs, base_meta, degree);
        len = 2;
        while len <= degree {
            let half = len / 2;
            let step = degree / len;
            dispatch(
                &self.stage_lhs,
                [degree, log_degree, half, step, degree, rows, 0, 0],
                degree / 2,
            );
            len *= 2;
        }
        dispatch(&self.finalize_lhs, base_meta, degree);
        drop(dispatch);
        encoder.copy_buffer_to_buffer(&lhs_buf, 0, &read_buf, 0, output_bytes);

        self.queue.submit([encoder.finish()]);
        self.device.poll(wgpu::Maintain::Wait);
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(BfvNttError::GpuExecution(format!(
                "buffer/bind/dispatch validation failed: {error}"
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
            .map_err(|error| BfvNttError::GpuExecution(error.to_string()))?
            .map_err(|error| BfvNttError::GpuExecution(error.to_string()))?;
        let mapped = slice.get_mapped_range();
        let words: &[u32] = bytemuck::cast_slice(&mapped);
        let output = if words.len() == lhs_words.len() {
            let mut output_rows = Vec::with_capacity(plan.moduli.len());
            let mut cursor = 0usize;
            for _ in &plan.moduli {
                let mut row = Vec::with_capacity(plan.degree);
                for _ in 0..plan.degree {
                    row.push(u64::from(words[cursor]) | (u64::from(words[cursor + 1]) << 32));
                    cursor += 2;
                }
                output_rows.push(row);
            }
            Some(output_rows)
        } else {
            None
        };
        drop(mapped);
        read_buf.unmap();
        let output_rows = output.ok_or_else(|| {
            BfvNttError::GpuExecution(
                "readback word count differs from the preflighted shape".to_owned(),
            )
        })?;
        for (row, (&q, coefficients)) in plan.moduli.iter().zip(&output_rows).enumerate() {
            if let Some((coefficient, &value)) = coefficients
                .iter()
                .enumerate()
                .find(|(_, value)| **value >= q)
            {
                return Err(BfvNttError::GpuExecution(format!(
                    "shader emitted non-canonical residue at row {row}, coefficient {coefficient}: \
                     {value} >= {q}"
                )));
            }
        }
        Ok(RnsPoly { rows: output_rows })
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};
    use fhe_math::rq::{traits::TryConvertFrom, Poly, Representation};

    fn schoolbook(lhs: &[u64], rhs: &[u64], q: u64) -> Vec<u64> {
        let degree = lhs.len();
        let mut out = vec![0u64; degree];
        for (i, &a) in lhs.iter().enumerate() {
            for (j, &b) in rhs.iter().enumerate() {
                let product = mod_mul(a, b, q);
                let index = i + j;
                if index < degree {
                    out[index] = add_mod(out[index], product, q);
                } else {
                    out[index - degree] = sub_mod(out[index - degree], product, q);
                }
            }
        }
        out
    }

    fn deployed_poly(seed: u64) -> RnsPoly {
        let mut state = seed;
        RnsPoly {
            rows: FOLD_MODULI
                .iter()
                .enumerate()
                .map(|(row, &q)| {
                    (0..FOLD_DEGREE)
                        .map(|i| {
                            state = state
                                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                                .rotate_left(17)
                                .wrapping_add((row + i + 1) as u64);
                            match i {
                                0 => q - 1,
                                1 => 0,
                                _ => state % q,
                            }
                        })
                        .collect()
                })
                .collect(),
        }
    }

    #[test]
    fn cpu_reference_matches_independent_schoolbook_negacyclic_product() {
        let q = 97u64; // prime and 1 mod 2*8
        let lhs = RnsPoly {
            rows: vec![vec![96, 0, 1, 2, 33, 71, 95, 4]],
        };
        let rhs = RnsPoly {
            rows: vec![vec![5, 96, 0, 19, 88, 1, 2, 3]],
        };
        let got = multiply_rns_cpu(&lhs, &rhs, &[q]).expect("CPU NTT product");
        assert_eq!(got.rows[0], schoolbook(&lhs.rows[0], &rhs.rows[0], q));

        let identity = RnsPoly {
            rows: vec![vec![1, 0, 0, 0, 0, 0, 0, 0]],
        };
        assert_eq!(
            multiply_rns_cpu(&lhs, &identity, &[q]).expect("NTT round trip"),
            lhs,
            "forward + inverse negacyclic NTT must recover every exact coefficient"
        );
    }

    #[test]
    fn hostile_shape_modulus_and_residue_inputs_fail_before_dispatch() {
        let valid = RnsPoly {
            rows: vec![vec![0; 8]],
        };
        let short = RnsPoly {
            rows: vec![vec![0; 7]],
        };
        assert!(matches!(
            multiply_rns_cpu(&short, &short, &[97]),
            Err(BfvNttError::InvalidShape(_))
        ));
        assert!(matches!(
            multiply_rns_cpu(&valid, &RnsPoly { rows: vec![] }, &[97]),
            Err(BfvNttError::InvalidShape(_))
        ));
        assert!(matches!(
            multiply_rns_cpu(&valid, &valid, &[91]),
            Err(BfvNttError::UnsupportedParameters(_))
        )); // composite
        let noncanonical = RnsPoly {
            rows: vec![vec![97, 0, 0, 0, 0, 0, 0, 0]],
        };
        assert!(matches!(
            multiply_rns_cpu(&noncanonical, &valid, &[97]),
            Err(BfvNttError::NonCanonical {
                operand: "lhs",
                row: 0,
                coefficient: 0,
                value: 97,
                modulus: 97,
            })
        ));
    }

    #[test]
    fn explicit_cpu_fallback_is_labelled_and_bit_exact() {
        let q = 97u64;
        let lhs = RnsPoly {
            rows: vec![vec![96, 3, 1, 2, 33, 71, 95, 4]],
        };
        let rhs = RnsPoly {
            rows: vec![vec![5, 96, 7, 19, 88, 1, 2, 3]],
        };
        let expected = multiply_rns_cpu(&lhs, &rhs, &[q]).expect("CPU reference");
        let execution = RnsNttEngine::cpu_only()
            .multiply(&lhs, &rhs, &[q])
            .expect("explicit CPU policy");
        assert_eq!(execution.polynomial, expected);
        assert_eq!(execution.backend, RnsNttBackend::CpuPolicy);
    }

    #[test]
    fn deployed_rows_match_fhe_math_and_gpu_roundtrip_is_bit_exact() {
        let lhs = deployed_poly(0x6750_0001);
        let rhs = deployed_poly(0x6750_0002);
        let cpu = multiply_rns_cpu(&lhs, &rhs, &FOLD_MODULI).expect("CPU NTT reference");

        // Independent oracle: fhe-math is the arithmetic layer used by fhe.rs.
        let context = Context::new_arc(&FOLD_MODULI, FOLD_DEGREE).expect("fhe-math context");
        let flatten = |poly: &RnsPoly| poly.rows.iter().flatten().copied().collect::<Vec<_>>();
        let mut oracle_lhs =
            Poly::try_convert_from(flatten(&lhs), &context, false, Representation::PowerBasis)
                .expect("oracle lhs");
        let mut oracle_rhs =
            Poly::try_convert_from(flatten(&rhs), &context, false, Representation::PowerBasis)
                .expect("oracle rhs");
        oracle_lhs.change_representation(Representation::Ntt);
        oracle_rhs.change_representation(Representation::Ntt);
        let mut oracle = &oracle_lhs * &oracle_rhs;
        oracle.change_representation(Representation::PowerBasis);
        let oracle_rows: Vec<Vec<u64>> = oracle
            .coefficients()
            .outer_iter()
            .map(|row| row.to_vec())
            .collect();
        assert_eq!(
            cpu.rows, oracle_rows,
            "CPU reference diverged from fhe-math"
        );

        let engine = RnsNttEngine::new();
        let execution = engine
            .multiply(&lhs, &rhs, &FOLD_MODULI)
            .expect("GPU or explicit capability fallback");
        assert_eq!(
            execution.polynomial, cpu,
            "portable WGSL product diverged at an exact deployed coefficient"
        );

        // Multiplication by one forces the same twist -> forward NTT ->
        // inverse NTT -> untwist path and must recover every input coefficient.
        let identity = RnsPoly {
            rows: FOLD_MODULI
                .iter()
                .map(|_| {
                    let mut row = vec![0; FOLD_DEGREE];
                    row[0] = 1;
                    row
                })
                .collect(),
        };
        let roundtrip = engine
            .multiply(&lhs, &identity, &FOLD_MODULI)
            .expect("GPU NTT round trip");
        assert_eq!(
            roundtrip.polynomial, lhs,
            "NTT round trip changed coefficients"
        );
        match execution.backend {
            RnsNttBackend::Wgpu { adapter } => {
                eprintln!("portable BFV RNS NTT parity + roundtrip GREEN on {adapter}");
                assert!(matches!(roundtrip.backend, RnsNttBackend::Wgpu { .. }));
            }
            fallback => {
                assert!(
                    std::env::var_os("DREGG_REQUIRE_WGPU").is_none(),
                    "DREGG_REQUIRE_WGPU is set but BFV RNS NTT used {fallback:?}"
                );
                eprintln!(
                    "portable BFV RNS NTT GPU parity SKIPPED explicitly; exact CPU fallback used: {fallback:?}"
                );
            }
        }
    }
}

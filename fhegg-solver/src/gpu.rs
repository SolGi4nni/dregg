//! wgpu GPU paths for the two solver workloads.
//!
//! - `histogram`: the aggregation FOLD (FHEGG-KERNEL §2) — scatter order
//!   quantities into K price buckets with u32 atomics. The N-dependent, cheap
//!   half of the clearing.
//! - `solve_pdhg`: the PDHG matvec workhorse (PRIVATE-CONVEX-ENGINE §2.2). Keeps
//!   `f, f̄, y` RESIDENT on the GPU and encodes all `2·T` dispatches in one pass
//!   (WebGPU orders storage writes dispatch-to-dispatch), reading back only the
//!   endpoints — the fixed straight-line trace, entirely on device.
//!
//! Both matvecs are GATHER-based (no float atomics): `Aᵀy` per edge is
//! `y[head]−y[tail]`; `A f̄` per node sums its incident edges via a public CSR
//! (`node_off/node_edge/node_sign`) — the public topology, precomputed.
//!
//! HONEST: wgpu is used where it genuinely moves the matvec/fold; the benchmark
//! (`bin/bench.rs`) reports CPU-vs-GPU crossover — GPU wins only past the
//! dispatch-overhead break-even, which for these workloads is large.

use crate::pdhg::{finalize, preconditioner, FlowLp, PdhgResult};
use bytemuck::{Pod, Zeroable};
use wgpu::util::DeviceExt;

/// A wgpu device+queue, created once and reused across dispatches.
pub struct GpuContext {
    pub device: wgpu::Device,
    pub queue: wgpu::Queue,
    pub adapter_name: String,
    pub backend: String,
}

impl GpuContext {
    /// Acquire a high-performance adapter. Returns `None` if no GPU is available.
    pub fn new() -> Option<Self> {
        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))?;
        let info = adapter.get_info();
        let mut limits = adapter.limits();
        // Keep default limits; storage buffer binding size may need bumping for
        // large graphs but defaults cover the benchmarked sizes.
        limits.max_storage_buffers_per_shader_stage =
            limits.max_storage_buffers_per_shader_stage.max(12);
        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("fhegg"),
                required_features: wgpu::Features::empty(),
                required_limits: limits,
                memory_hints: Default::default(),
            },
            None,
        ))
        .ok()?;
        Some(GpuContext {
            device,
            queue,
            adapter_name: info.name,
            backend: format!("{:?}", info.backend),
        })
    }

    fn storage_ro<T: Pod>(&self, label: &str, data: &[T]) -> wgpu::Buffer {
        // arrayLength needs a non-empty buffer; pad empties to one element.
        let bytes: &[u8] = if data.is_empty() {
            &[0u8; 4]
        } else {
            bytemuck::cast_slice(data)
        };
        self.device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some(label),
                contents: bytes,
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            })
    }

    fn storage_rw<T: Pod>(&self, label: &str, data: &[T]) -> wgpu::Buffer {
        let bytes: &[u8] = if data.is_empty() {
            &[0u8; 4]
        } else {
            bytemuck::cast_slice(data)
        };
        self.device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some(label),
                contents: bytes,
                usage: wgpu::BufferUsages::STORAGE
                    | wgpu::BufferUsages::COPY_SRC
                    | wgpu::BufferUsages::COPY_DST,
            })
    }

    fn read_back(&self, buf: &wgpu::Buffer, n_bytes: u64) -> Vec<u8> {
        let read = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("read"),
            size: n_bytes,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(buf, 0, &read, 0, n_bytes);
        self.queue.submit([enc.finish()]);
        let slice = read.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let out = slice.get_mapped_range().to_vec();
        read.unmap();
        out
    }

    // ------------------------------------------------------------------
    // The aggregation fold: scatter qty into K buckets with u32 atomics.
    // ------------------------------------------------------------------

    /// Histogram `qtys` by `limits` into `k` buckets on the GPU.
    /// `limits[i]` must be in `[0, k)`. Returns the K-length bucket sums.
    pub fn histogram(&self, limits: &[u32], qtys: &[u32], k: usize) -> Vec<u32> {
        let n = limits.len();
        let hist_init = vec![0u32; k];
        let buf_hist = self.storage_rw("hist", &hist_init);
        let buf_lim = self.storage_ro("limits", limits);
        let buf_qty = self.storage_ro("qtys", qtys);

        let shader = r#"
@group(0) @binding(0) var<storage, read_write> hist: array<atomic<u32>>;
@group(0) @binding(1) var<storage, read> limits: array<u32>;
@group(0) @binding(2) var<storage, read> qtys: array<u32>;
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
  let i = gid.x;
  if (i >= arrayLength(&qtys)) { return; }
  atomicAdd(&hist[limits[i]], qtys[i]);
}
"#;
        let module = self
            .device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("hist"),
                source: wgpu::ShaderSource::Wgsl(shader.into()),
            });
        let pipeline = self
            .device
            .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("hist"),
                layout: None,
                module: &module,
                entry_point: Some("main"),
                compilation_options: Default::default(),
                cache: None,
            });
        let bgl = pipeline.get_bind_group_layout(0);
        let bind = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: buf_hist.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: buf_lim.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: buf_qty.as_entire_binding(),
                },
            ],
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut pass = enc.begin_compute_pass(&Default::default());
            pass.set_pipeline(&pipeline);
            pass.set_bind_group(0, &bind, &[]);
            let groups = ((n as u32) + 255) / 256;
            pass.dispatch_workgroups(groups.max(1), 1, 1);
        }
        self.queue.submit([enc.finish()]);
        self.device.poll(wgpu::Maintain::Wait);
        let raw = self.read_back(&buf_hist, (k * 4) as u64);
        bytemuck::cast_slice(&raw).to_vec()
    }

    // ------------------------------------------------------------------
    // The PDHG resident loop.
    // ------------------------------------------------------------------

    /// Run `iters` PDHG iterations fully on the GPU, reading back only `(f, y)`.
    pub fn solve_pdhg(&self, lp: &FlowLp, iters: usize) -> PdhgResult {
        let m = lp.m();
        let n = lp.n_nodes;
        let (tau, sigma) = preconditioner(lp, 1.0);

        // Public CSR: node -> (incident edges, signs).
        let (node_off, node_edge, node_sign) = build_csr(lp);

        let tail: Vec<u32> = lp.edges.iter().map(|&(t, _)| t).collect();
        let head: Vec<u32> = lp.edges.iter().map(|&(_, h)| h).collect();
        let w: Vec<f32> = lp.w.iter().map(|&x| x as f32).collect();
        let cap: Vec<f32> = lp.c.iter().map(|&x| x as f32).collect();
        let sigma_f: Vec<f32> = sigma.iter().map(|&x| x as f32).collect();
        let f0 = vec![0.0f32; m];
        let fbar0 = vec![0.0f32; m];
        let y0 = vec![0.0f32; n];

        #[repr(C)]
        #[derive(Clone, Copy, Pod, Zeroable)]
        struct Params {
            tau: f32,
            theta: f32,
            n: u32,
            m: u32,
        }
        let params = Params {
            tau: tau as f32,
            theta: 1.0,
            n: n as u32,
            m: m as u32,
        };
        let buf_params = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("params"),
                contents: bytemuck::bytes_of(&params),
                usage: wgpu::BufferUsages::UNIFORM,
            });

        let buf_tail = self.storage_ro("tail", &tail);
        let buf_head = self.storage_ro("head", &head);
        let buf_w = self.storage_ro("w", &w);
        let buf_cap = self.storage_ro("cap", &cap);
        let buf_f = self.storage_rw("f", &f0);
        let buf_fbar = self.storage_rw("fbar", &fbar0);
        let buf_y = self.storage_rw("y", &y0);
        let buf_noff = self.storage_ro("node_off", &node_off);
        let buf_nedge = self.storage_ro("node_edge", &node_edge);
        let buf_nsign = self.storage_ro("node_sign", &node_sign);
        let buf_sigma = self.storage_ro("sigma", &sigma_f);

        let shader = PDHG_WGSL;
        let module = self
            .device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("pdhg"),
                source: wgpu::ShaderSource::Wgsl(shader.into()),
            });

        let bgl = self
            .device
            .create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("pdhg-bgl"),
                entries: &pdhg_bgl_entries(),
            });
        let pipe_layout = self
            .device
            .create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: None,
                bind_group_layouts: &[&bgl],
                push_constant_ranges: &[],
            });
        let make = |entry: &str| {
            self.device
                .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                    label: Some(entry),
                    layout: Some(&pipe_layout),
                    module: &module,
                    entry_point: Some(entry),
                    compilation_options: Default::default(),
                    cache: None,
                })
        };
        let dual_pipe = make("dual_update");
        let primal_pipe = make("primal_update");

        let bind = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: buf_params.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: buf_tail.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: buf_head.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: buf_w.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 4,
                    resource: buf_cap.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 5,
                    resource: buf_f.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 6,
                    resource: buf_fbar.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 7,
                    resource: buf_y.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 8,
                    resource: buf_noff.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 9,
                    resource: buf_nedge.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 10,
                    resource: buf_nsign.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 11,
                    resource: buf_sigma.as_entire_binding(),
                },
            ],
        });

        let node_groups = (((n as u32) + 63) / 64).max(1);
        let edge_groups = (((m as u32) + 63) / 64).max(1);

        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut pass = enc.begin_compute_pass(&Default::default());
            pass.set_bind_group(0, &bind, &[]);
            for _ in 0..iters {
                pass.set_pipeline(&dual_pipe);
                pass.dispatch_workgroups(node_groups, 1, 1);
                pass.set_pipeline(&primal_pipe);
                pass.dispatch_workgroups(edge_groups, 1, 1);
            }
        }
        self.queue.submit([enc.finish()]);
        self.device.poll(wgpu::Maintain::Wait);

        let f_raw = self.read_back(&buf_f, (m * 4) as u64);
        let y_raw = self.read_back(&buf_y, (n * 4) as u64);
        let f: Vec<f64> = bytemuck::cast_slice::<u8, f32>(&f_raw)
            .iter()
            .map(|&x| x as f64)
            .collect();
        let y: Vec<f64> = bytemuck::cast_slice::<u8, f32>(&y_raw)
            .iter()
            .map(|&x| x as f64)
            .collect();
        // Recompute the certificate quantities in f64 from the GPU endpoints.
        finalize(lp, f, y, iters)
    }
}

/// Build the public CSR: for each node, its incident edges and signs
/// (`+1` if the node is the edge head, `−1` if the tail).
fn build_csr(lp: &FlowLp) -> (Vec<u32>, Vec<u32>, Vec<f32>) {
    let n = lp.n_nodes;
    let deg = lp.degrees();
    let mut node_off = vec![0u32; n + 1];
    for i in 0..n {
        node_off[i + 1] = node_off[i] + deg[i];
    }
    let nnz = node_off[n] as usize;
    let mut node_edge = vec![0u32; nnz];
    let mut node_sign = vec![0.0f32; nnz];
    let mut cursor: Vec<u32> = node_off[..n].to_vec();
    for (e, &(t, h)) in lp.edges.iter().enumerate() {
        let ti = cursor[t as usize] as usize;
        node_edge[ti] = e as u32;
        node_sign[ti] = -1.0;
        cursor[t as usize] += 1;
        let hi = cursor[h as usize] as usize;
        node_edge[hi] = e as u32;
        node_sign[hi] = 1.0;
        cursor[h as usize] += 1;
    }
    (node_off, node_edge, node_sign)
}

fn pdhg_bgl_entries() -> Vec<wgpu::BindGroupLayoutEntry> {
    let storage = |binding: u32, read_only: bool| wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty: wgpu::BufferBindingType::Storage { read_only },
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    };
    let mut v = vec![wgpu::BindGroupLayoutEntry {
        binding: 0,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty: wgpu::BufferBindingType::Uniform,
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }];
    v.push(storage(1, true)); // tail
    v.push(storage(2, true)); // head
    v.push(storage(3, true)); // w
    v.push(storage(4, true)); // cap
    v.push(storage(5, false)); // f
    v.push(storage(6, false)); // fbar
    v.push(storage(7, false)); // y
    v.push(storage(8, true)); // node_off
    v.push(storage(9, true)); // node_edge
    v.push(storage(10, true)); // node_sign
    v.push(storage(11, true)); // sigma
    v
}

const PDHG_WGSL: &str = r#"
struct Params { tau: f32, theta: f32, n: u32, m: u32 };
@group(0) @binding(0)  var<uniform> P: Params;
@group(0) @binding(1)  var<storage, read>       tail: array<u32>;
@group(0) @binding(2)  var<storage, read>       head: array<u32>;
@group(0) @binding(3)  var<storage, read>       w: array<f32>;
@group(0) @binding(4)  var<storage, read>       cap: array<f32>;
@group(0) @binding(5)  var<storage, read_write> f: array<f32>;
@group(0) @binding(6)  var<storage, read_write> fbar: array<f32>;
@group(0) @binding(7)  var<storage, read_write> y: array<f32>;
@group(0) @binding(8)  var<storage, read>       node_off: array<u32>;
@group(0) @binding(9)  var<storage, read>       node_edge: array<u32>;
@group(0) @binding(10) var<storage, read>       node_sign: array<f32>;
@group(0) @binding(11) var<storage, read>       sigma: array<f32>;

// Dual: y += sigma * (A fbar), per node via the public CSR.
@compute @workgroup_size(64)
fn dual_update(@builtin(global_invocation_id) gid: vec3<u32>) {
  let i = gid.x;
  if (i >= P.n) { return; }
  var acc = 0.0;
  let s = node_off[i];
  let e = node_off[i + 1u];
  for (var k = s; k < e; k = k + 1u) {
    acc = acc + node_sign[k] * fbar[node_edge[k]];
  }
  y[i] = y[i] + sigma[i] * acc;
}

// Primal: f = clip(f + tau*(w - A^T y)); fbar = f_new + theta*(f_new - f_old), per edge.
@compute @workgroup_size(64)
fn primal_update(@builtin(global_invocation_id) gid: vec3<u32>) {
  let e = gid.x;
  if (e >= P.m) { return; }
  let at = y[head[e]] - y[tail[e]];
  let fold = f[e];
  let fnew = clamp(fold + P.tau * (w[e] - at), 0.0, cap[e]);
  fbar[e] = fnew + P.theta * (fnew - fold);
  f[e] = fnew;
}
"#;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clearing::{crossing, scan_curves};
    use crate::pdhg::{cycle_lp, cycle_optimum, solve_cpu};

    #[test]
    fn gpu_histogram_matches_cpu() {
        let Some(gpu) = GpuContext::new() else {
            eprintln!("no GPU adapter — skipping gpu_histogram_matches_cpu");
            return;
        };
        let k = 64;
        let limits: Vec<u32> = (0..1000).map(|i| (i * 7 % k as u32)).collect();
        let qtys: Vec<u32> = (0..1000).map(|i| (i % 5) + 1).collect();
        let gpu_hist = gpu.histogram(&limits, &qtys, k);
        let mut cpu_hist = vec![0u32; k];
        for (l, q) in limits.iter().zip(&qtys) {
            cpu_hist[*l as usize] += *q;
        }
        assert_eq!(gpu_hist, cpu_hist, "GPU histogram must match CPU fold");
        // And it scans to a sensible crossing.
        let bh: Vec<u64> = gpu_hist.iter().map(|&x| x as u64).collect();
        let (d, s) = scan_curves(&bh, &bh);
        let (crossed, _, _) = crossing(&d, &s);
        assert!(crossed);
    }

    #[test]
    fn gpu_pdhg_matches_cpu_optimum() {
        let Some(gpu) = GpuContext::new() else {
            eprintln!("no GPU adapter — skipping gpu_pdhg_matches_cpu_optimum");
            return;
        };
        let caps = vec![5.0, 3.0, 7.0, 4.0];
        let w = vec![1.0; 4];
        let lp = cycle_lp(4, &caps, &w);
        let opt = cycle_optimum(&caps, &w); // 3 * 4 = 12
        let gpu_res = gpu.solve_pdhg(&lp, 8000);
        let cpu_res = solve_cpu(&lp, 8000);
        // GPU (f32) reaches the same optimum as CPU (f64) within f32 tolerance.
        assert!(
            (gpu_res.primal_obj - opt).abs() < 5e-2,
            "GPU primal {} vs optimum {}",
            gpu_res.primal_obj,
            opt
        );
        assert!(
            (gpu_res.primal_obj - cpu_res.primal_obj).abs() < 5e-2,
            "GPU {} vs CPU {}",
            gpu_res.primal_obj,
            cpu_res.primal_obj
        );
        assert!(
            gpu_res.duality_gap < 5e-2,
            "GPU gap {}",
            gpu_res.duality_gap
        );
    }
}

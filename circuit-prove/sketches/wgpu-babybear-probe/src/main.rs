//! wgpu/WGSL BabyBear Montgomery-multiply probe.
//!
//! Validates: (1) WGSL can express p3-compatible BabyBear Montgomery arithmetic
//! (no u64 in WGSL — 16-bit-split mul64); (2) bit-exact parity vs the pinned
//! Plonky3 rev 82cfad7 BabyBear; (3) measured field-mul throughput on the
//! default wgpu backend (Metal on macOS).

use p3_baby_bear::BabyBear;
use p3_field::integers::QuotientMap;
use p3_field::PrimeField32;
use rand::Rng;
use wgpu::util::DeviceExt;

const P: u32 = 0x7800_0001; // BabyBear prime (p3 baby_bear.rs:18)
const N: usize = 1 << 22; // 4M lanes
const K: u32 = 128; // chained muls per lane (compute-bound)

fn shader_source() -> String {
    // R2 = 2^64 mod P (Montgomery conversion constant), computed on host.
    let r2 = ((1u128 << 64) % P as u128) as u32;
    format!(
        r#"
const P: u32 = 0x78000001u;
const MU: u32 = 0x88000001u; // P^{{-1}} mod 2^32 (p3 MONTY_MU, baby_bear.rs:21)
const R2: u32 = {r2}u;       // 2^64 mod P
const K: u32 = {K}u;

// 32x32 -> 64 multiply via 16-bit split (WGSL has no u64).
fn mul64(a: u32, b: u32) -> vec2<u32> {{
    let a0 = a & 0xffffu; let a1 = a >> 16u;
    let b0 = b & 0xffffu; let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = p01 + p10;
    let carry_mid = select(0u, 0x10000u, mid < p01);
    let mid_lo = mid << 16u;
    let lo = p00 + mid_lo;
    let carry_lo = select(0u, 1u, lo < p00);
    let hi = p11 + (mid >> 16u) + carry_mid + carry_lo;
    return vec2<u32>(lo, hi);
}}

// Montgomery product, exactly the p3 monty-31 reduce (utils.rs:105):
// t = lo(x)*MU; u = t*P; result = hi(x) - hi(u)  (+P on borrow).
fn mmul(a: u32, b: u32) -> u32 {{
    let ab = mul64(a, b);
    let t = ab.x * MU;
    let tp = mul64(t, P);
    var r: u32 = ab.y - tp.y;
    if (ab.y < tp.y) {{ r += P; }}
    return r;
}}

@group(0) @binding(0) var<storage, read> ax: array<u32>;
@group(0) @binding(1) var<storage, read> bx: array<u32>;
@group(0) @binding(2) var<storage, read_write> outx: array<u32>;

@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {{
    let i = gid.x;
    if (i >= arrayLength(&ax)) {{ return; }}
    // canonical -> Montgomery form
    var x = mmul(ax[i], R2);
    let y = mmul(bx[i], R2);
    for (var j = 0u; j < K; j++) {{
        x = mmul(x, y);
    }}
    // Montgomery -> canonical
    outx[i] = mmul(x, 1u);
}}
"#
    )
}

fn main() {
    let mut rng = rand::thread_rng();
    let a: Vec<u32> = (0..N).map(|_| rng.gen_range(0..P)).collect();
    let b: Vec<u32> = (0..N).map(|_| rng.gen_range(0..P)).collect();

    // --- GPU ---
    let instance = wgpu::Instance::default();
    let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
        power_preference: wgpu::PowerPreference::HighPerformance,
        ..Default::default()
    }))
    .expect("no adapter");
    let info = adapter.get_info();
    println!("adapter: {} ({:?})", info.name, info.backend);
    let (device, queue) =
        pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor::default(), None))
            .expect("no device");

    let module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("babybear"),
        source: wgpu::ShaderSource::Wgsl(shader_source().into()),
    });
    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: None,
        layout: None,
        module: &module,
        entry_point: Some("main"),
        compilation_options: Default::default(),
        cache: None,
    });

    let buf_a = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: None,
        contents: bytemuck::cast_slice(&a),
        usage: wgpu::BufferUsages::STORAGE,
    });
    let buf_b = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: None,
        contents: bytemuck::cast_slice(&b),
        usage: wgpu::BufferUsages::STORAGE,
    });
    let buf_out = device.create_buffer(&wgpu::BufferDescriptor {
        label: None,
        size: (N * 4) as u64,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let buf_read = device.create_buffer(&wgpu::BufferDescriptor {
        label: None,
        size: (N * 4) as u64,
        usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });

    let bgl = pipeline.get_bind_group_layout(0);
    let bind = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: None,
        layout: &bgl,
        entries: &[
            wgpu::BindGroupEntry {
                binding: 0,
                resource: buf_a.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 1,
                resource: buf_b.as_entire_binding(),
            },
            wgpu::BindGroupEntry {
                binding: 2,
                resource: buf_out.as_entire_binding(),
            },
        ],
    });

    let dispatch = |label: &str| -> f64 {
        let t0 = std::time::Instant::now();
        let mut enc = device.create_command_encoder(&Default::default());
        {
            let mut pass = enc.begin_compute_pass(&Default::default());
            pass.set_pipeline(&pipeline);
            pass.set_bind_group(0, &bind, &[]);
            pass.dispatch_workgroups((N as u32).div_ceil(256), 1, 1);
        }
        queue.submit([enc.finish()]);
        device.poll(wgpu::Maintain::Wait);
        let dt = t0.elapsed().as_secs_f64();
        println!(
            "{label}: {:.1} ms  ({:.2} Gmul/s)",
            dt * 1e3,
            (N as f64 * K as f64) / dt / 1e9
        );
        dt
    };

    dispatch("gpu warmup");
    let mut best = f64::MAX;
    for i in 0..5 {
        best = best.min(dispatch(&format!("gpu run {i}")));
    }
    println!(
        "GPU best: {:.1} ms for {} lanes x {} chained muls = {:.2} Gmul/s",
        best * 1e3,
        N,
        K,
        (N as f64 * K as f64) / best / 1e9
    );

    // Read back
    let mut enc = device.create_command_encoder(&Default::default());
    enc.copy_buffer_to_buffer(&buf_out, 0, &buf_read, 0, (N * 4) as u64);
    queue.submit([enc.finish()]);
    let slice = buf_read.slice(..);
    slice.map_async(wgpu::MapMode::Read, |_| {});
    device.poll(wgpu::Maintain::Wait);
    let gpu_out: Vec<u32> = bytemuck::cast_slice(&slice.get_mapped_range()).to_vec();

    // --- CPU parity + single-thread baseline (pinned p3 BabyBear) ---
    let t0 = std::time::Instant::now();
    let mut mismatches = 0usize;
    for i in 0..N {
        let mut x = BabyBear::from_int(a[i]);
        let y = BabyBear::from_int(b[i]);
        for _ in 0..K {
            x *= y;
        }
        if x.as_canonical_u32() != gpu_out[i] {
            mismatches += 1;
            if mismatches < 4 {
                println!(
                    "MISMATCH lane {i}: cpu {} gpu {}",
                    x.as_canonical_u32(),
                    gpu_out[i]
                );
            }
        }
    }
    let cpu_dt = t0.elapsed().as_secs_f64();
    println!(
        "CPU (1 thread, pinned p3 rev 82cfad7): {:.1} ms = {:.2} Gmul/s",
        cpu_dt * 1e3,
        (N as f64 * K as f64) / cpu_dt / 1e9
    );
    if mismatches == 0 {
        println!("PARITY: all {N} lanes bit-exact vs Plonky3 BabyBear ✓");
    } else {
        println!("PARITY FAILED: {mismatches}/{N} mismatches");
        std::process::exit(1);
    }
}

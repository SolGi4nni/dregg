// Batched exact negacyclic NTT for native-torus external products.
//
// Four ~30-bit primes give a 120-bit CRT carrier. Every shader value is in
// Montgomery form; `mont_mul` uses an exact 16-bit-split 32x32->64 product and
// therefore needs no native u64, CUDA, HIP, or vendor extension. The product
// dimension is folded into gid.y so every GGSW row/output pair crosses the GPU
// boundary in one submission and one readback.

struct Meta {
    degree      : u32,
    log_degree  : u32,
    half        : u32,
    step        : u32,
    roots_offset: u32,
    n_rows      : u32,
    n_products  : u32,
    _pad        : u32,
};

@group(0) @binding(0) var<uniform>             params : Meta;
@group(0) @binding(1) var<storage, read_write> lhs    : array<u32>;
@group(0) @binding(2) var<storage, read_write> rhs    : array<u32>;
// Per modulus row: q, -q^-1 mod 2^32, padding, padding.
@group(0) @binding(3) var<storage, read>       qdata  : array<u32>;
// Per modulus row: degree forward powers followed by degree inverse powers.
@group(0) @binding(4) var<storage, read>       roots  : array<u32>;
// Per modulus row: psi^i followed by n^-1 * psi^-i, all Montgomery encoded.
@group(0) @binding(5) var<storage, read>       twists : array<u32>;

// The fused entry point owns one product/modulus series per workgroup.  The
// portable WebGPU minimum is 16 KiB of workgroup storage, exactly enough for
// the largest admitted N=4096 row.  Reusing one row avoids a global-memory
// round trip and a command dispatch at every forward/inverse butterfly stage.
var<workgroup> scratch : array<u32, 4096>;

fn addmod(a: u32, b: u32, q: u32) -> u32 {
    let sum = a + b;
    return select(sum, sum - q, sum >= q);
}

fn submod(a: u32, b: u32, q: u32) -> u32 {
    return select(q - (b - a), a - b, a >= b);
}

fn mul32_wide(a: u32, b: u32) -> vec2<u32> {
    let mask = 0xffffu;
    let a0 = a & mask;
    let a1 = a >> 16u;
    let b0 = b & mask;
    let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let middle = (p00 >> 16u) + (p01 & mask) + (p10 & mask);
    let lo = (p00 & mask) | (middle << 16u);
    let hi = p11 + (p01 >> 16u) + (p10 >> 16u) + (middle >> 16u);
    return vec2<u32>(lo, hi);
}

// REDC(a*b): inputs and output are canonical residues; callers maintain the
// Montgomery representation. q < 2^30 makes t + m*q < 2^63, so the high-word
// addition cannot overflow and one conditional subtraction is sufficient.
fn mont_mul(a: u32, b: u32, q: u32, qinv: u32) -> u32 {
    let product = mul32_wide(a, b);
    let m = product.x * qinv;
    let correction = mul32_wide(m, q);
    let low = product.x + correction.x;
    let carry = select(0u, 1u, low < product.x);
    let reduced = product.y + correction.y + carry;
    return select(reduced, reduced - q, reduced >= q);
}

fn series_row(series: u32) -> u32 { return series % params.n_rows; }

fn series_base(series: u32) -> u32 {
    return series * params.degree;
}

fn row_q(row: u32) -> u32 { return qdata[row * 4u]; }
fn row_qinv(row: u32) -> u32 { return qdata[row * 4u + 1u]; }

fn load_coeff(buf: u32, index: u32) -> u32 {
    return select(rhs[index], lhs[index], buf == 0u);
}

fn store_coeff(buf: u32, index: u32, value: u32) {
    if (buf == 0u) { lhs[index] = value; } else { rhs[index] = value; }
}

fn load_table(table: u32, row: u32, offset: u32) -> u32 {
    let index = row * (2u * params.degree) + offset;
    return select(twists[index], roots[index], table == 0u);
}

fn reverse_low_bits(value: u32, bits: u32) -> u32 {
    var x = value;
    var out = 0u;
    for (var bit = 0u; bit < bits; bit = bit + 1u) {
        out = (out << 1u) | (x & 1u);
        x = x >> 1u;
    }
    return out;
}

@compute @workgroup_size(64)
fn twist_both(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let series = gid.y;
    if (i >= params.degree || series >= params.n_rows * params.n_products) { return; }
    let row = series_row(series);
    let index = series_base(series) + i;
    let q = row_q(row);
    let qinv = row_qinv(row);
    let twist = load_table(1u, row, i);
    store_coeff(0u, index, mont_mul(load_coeff(0u, index), twist, q, qinv));
    store_coeff(1u, index, mont_mul(load_coeff(1u, index), twist, q, qinv));
}

@compute @workgroup_size(64)
fn bit_reverse_both(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let series = gid.y;
    if (i >= params.degree || series >= params.n_rows * params.n_products) { return; }
    let j = reverse_low_bits(i, params.log_degree);
    if (i >= j) { return; }
    let base = series_base(series);
    let a = base + i;
    let b = base + j;
    let la = lhs[a]; let lb = lhs[b]; let ra = rhs[a]; let rb = rhs[b];
    lhs[a] = lb; lhs[b] = la; rhs[a] = rb; rhs[b] = ra;
}

fn butterfly(buf: u32, butterfly_index: u32, series: u32) {
    let block = butterfly_index / params.half;
    let j = butterfly_index - block * params.half;
    let left = series_base(series) + block * (2u * params.half) + j;
    let right = left + params.half;
    let row = series_row(series);
    let q = row_q(row);
    let qinv = row_qinv(row);
    let w = load_table(0u, row, params.roots_offset + j * params.step);
    let u = load_coeff(buf, left);
    let v = mont_mul(load_coeff(buf, right), w, q, qinv);
    store_coeff(buf, left, addmod(u, v, q));
    store_coeff(buf, right, submod(u, v, q));
}

@compute @workgroup_size(64)
fn stage_both(@builtin(global_invocation_id) gid: vec3<u32>) {
    if (gid.x >= params.degree / 2u || gid.y >= params.n_rows * params.n_products) { return; }
    butterfly(0u, gid.x, gid.y);
    butterfly(1u, gid.x, gid.y);
}

@compute @workgroup_size(64)
fn pointwise(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let series = gid.y;
    if (i >= params.degree || series >= params.n_rows * params.n_products) { return; }
    let row = series_row(series);
    let index = series_base(series) + i;
    lhs[index] = mont_mul(lhs[index], rhs[index], row_q(row), row_qinv(row));
}

@compute @workgroup_size(64)
fn bit_reverse_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let series = gid.y;
    if (i >= params.degree || series >= params.n_rows * params.n_products) { return; }
    let j = reverse_low_bits(i, params.log_degree);
    if (i >= j) { return; }
    let base = series_base(series);
    let a = base + i; let b = base + j; let value = lhs[a];
    lhs[a] = lhs[b]; lhs[b] = value;
}

@compute @workgroup_size(64)
fn stage_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    if (gid.x >= params.degree / 2u || gid.y >= params.n_rows * params.n_products) { return; }
    butterfly(0u, gid.x, gid.y);
}

@compute @workgroup_size(64)
fn finalize_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let series = gid.y;
    if (i >= params.degree || series >= params.n_rows * params.n_products) { return; }
    let row = series_row(series);
    let index = series_base(series) + i;
    let q = row_q(row);
    let qinv = row_qinv(row);
    let scale = load_table(1u, row, params.degree + i);
    let scaled = mont_mul(lhs[index], scale, q, qinv);
    // One canonical operand removes the final Montgomery factor.
    lhs[index] = mont_mul(scaled, 1u, q, qinv);
}

// Complete negacyclic product in one workgroup and one dispatch per batch.
// `workgroup_id.y` selects the product/modulus series; every barrier is in
// uniform control flow even when degree < the 256-thread workgroup.
@compute @workgroup_size(256)
fn fused_product(
    @builtin(local_invocation_id) lid: vec3<u32>,
    @builtin(workgroup_id) wid: vec3<u32>,
) {
    let series = wid.y;
    if (series >= params.n_rows * params.n_products) { return; }
    let row = series_row(series);
    let base = series_base(series);
    let q = row_q(row);
    let qinv = row_qinv(row);

    // Forward lhs, loaded directly into bit-reversed order.
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        let reversed = reverse_low_bits(i, params.log_degree);
        let twist = load_table(1u, row, i);
        scratch[reversed] = mont_mul(lhs[base + i], twist, q, qinv);
    }
    workgroupBarrier();
    var len = 2u;
    while (len <= params.degree) {
        let half = len / 2u;
        let step = params.degree / len;
        for (var b = lid.x; b < params.degree / 2u; b = b + 256u) {
            let block = b / half;
            let j = b - block * half;
            let left = block * len + j;
            let right = left + half;
            let w = load_table(0u, row, j * step);
            let u = scratch[left];
            let v = mont_mul(scratch[right], w, q, qinv);
            scratch[left] = addmod(u, v, q);
            scratch[right] = submod(u, v, q);
        }
        workgroupBarrier();
        len = len * 2u;
    }
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        lhs[base + i] = scratch[i];
    }
    storageBarrier();
    workgroupBarrier();

    // Forward rhs in the same scratch row, then multiply by the retained lhs.
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        let reversed = reverse_low_bits(i, params.log_degree);
        let twist = load_table(1u, row, i);
        scratch[reversed] = mont_mul(rhs[base + i], twist, q, qinv);
    }
    workgroupBarrier();
    len = 2u;
    while (len <= params.degree) {
        let half = len / 2u;
        let step = params.degree / len;
        for (var b = lid.x; b < params.degree / 2u; b = b + 256u) {
            let block = b / half;
            let j = b - block * half;
            let left = block * len + j;
            let right = left + half;
            let w = load_table(0u, row, j * step);
            let u = scratch[left];
            let v = mont_mul(scratch[right], w, q, qinv);
            scratch[left] = addmod(u, v, q);
            scratch[right] = submod(u, v, q);
        }
        workgroupBarrier();
        len = len * 2u;
    }
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        scratch[i] = mont_mul(lhs[base + i], scratch[i], q, qinv);
    }
    workgroupBarrier();

    // Inverse transform: in-place bit reversal followed by inverse roots.
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        let reversed = reverse_low_bits(i, params.log_degree);
        if (i < reversed) {
            let value = scratch[i];
            scratch[i] = scratch[reversed];
            scratch[reversed] = value;
        }
    }
    workgroupBarrier();
    len = 2u;
    while (len <= params.degree) {
        let half = len / 2u;
        let step = params.degree / len;
        for (var b = lid.x; b < params.degree / 2u; b = b + 256u) {
            let block = b / half;
            let j = b - block * half;
            let left = block * len + j;
            let right = left + half;
            let w = load_table(0u, row, params.degree + j * step);
            let u = scratch[left];
            let v = mont_mul(scratch[right], w, q, qinv);
            scratch[left] = addmod(u, v, q);
            scratch[right] = submod(u, v, q);
        }
        workgroupBarrier();
        len = len * 2u;
    }
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        let scale = load_table(1u, row, params.degree + i);
        let scaled = mont_mul(scratch[i], scale, q, qinv);
        lhs[base + i] = mont_mul(scaled, 1u, q, qinv);
    }
}

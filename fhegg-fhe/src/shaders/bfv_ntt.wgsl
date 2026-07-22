// Exact negacyclic RNS NTT over fhe.rs's serialized power-basis rows.
//
// WGSL deliberately uses only core u32 operations.  Every residue/modulus is
// represented as (lo, hi), and modular multiplication is double-and-add.  It
// is not the final throughput kernel, but it is portable across Metal, Vulkan,
// DX12, and browser WebGPU and is bit-exact for the < 2^62 fhe-math moduli.

struct Meta {
    degree      : u32,
    log_degree  : u32,
    half        : u32,
    step        : u32,
    roots_offset: u32,
    n_rows      : u32,
    _pad0       : u32,
    _pad1       : u32,
};

@group(0) @binding(0) var<uniform>             params : Meta;
@group(0) @binding(1) var<storage, read_write> lhs    : array<u32>;
@group(0) @binding(2) var<storage, read_write> rhs    : array<u32>;
// Per row: q.lo, q.hi, significant_bits(q), padding.
@group(0) @binding(3) var<storage, read>       qdata  : array<u32>;
// Per row: degree forward powers followed by degree inverse powers.
@group(0) @binding(4) var<storage, read>       roots  : array<u32>;
// Per row: degree powers of psi followed by n^-1 * psi^-i.
@group(0) @binding(5) var<storage, read>       twists : array<u32>;

fn add64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let lo = a.x + b.x;
    let carry = select(0u, 1u, lo < a.x);
    return vec2<u32>(lo, a.y + b.y + carry);
}

fn sub64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let borrow = select(0u, 1u, a.x < b.x);
    return vec2<u32>(a.x - b.x, a.y - b.y - borrow);
}

fn ge64(a: vec2<u32>, b: vec2<u32>) -> bool {
    return a.y > b.y || (a.y == b.y && a.x >= b.x);
}

fn shr1(a: vec2<u32>) -> vec2<u32> {
    return vec2<u32>((a.x >> 1u) | (a.y << 31u), a.y >> 1u);
}

fn addmod(a: vec2<u32>, b: vec2<u32>, q: vec2<u32>) -> vec2<u32> {
    var s = add64(a, b);
    if (ge64(s, q)) { s = sub64(s, q); }
    return s;
}

fn submod(a: vec2<u32>, b: vec2<u32>, q: vec2<u32>) -> vec2<u32> {
    if (ge64(a, b)) { return sub64(a, b); }
    return sub64(q, sub64(b, a));
}

// Exact for canonical a,b < q and q < 2^62.  At every iteration acc,x < q,
// so addmod sees a sum < 2q < 2^63 and the split-u32 add never overflows u64.
fn mulmod(a: vec2<u32>, b: vec2<u32>, q: vec2<u32>, qbits: u32) -> vec2<u32> {
    var acc = vec2<u32>(0u, 0u);
    var x = a;
    var y = b;
    for (var bit = 0u; bit < qbits; bit = bit + 1u) {
        if ((y.x & 1u) != 0u) { acc = addmod(acc, x, q); }
        y = shr1(y);
        if (bit + 1u < qbits) { x = addmod(x, x, q); }
    }
    return acc;
}

fn row_q(row: u32) -> vec2<u32> {
    return vec2<u32>(qdata[row * 4u], qdata[row * 4u + 1u]);
}

fn row_qbits(row: u32) -> u32 { return qdata[row * 4u + 2u]; }

fn load_coeff(buf: u32, index: u32) -> vec2<u32> {
    if (buf == 0u) { return vec2<u32>(lhs[index * 2u], lhs[index * 2u + 1u]); }
    return vec2<u32>(rhs[index * 2u], rhs[index * 2u + 1u]);
}

fn store_coeff(buf: u32, index: u32, value: vec2<u32>) {
    if (buf == 0u) {
        lhs[index * 2u] = value.x;
        lhs[index * 2u + 1u] = value.y;
    } else {
        rhs[index * 2u] = value.x;
        rhs[index * 2u + 1u] = value.y;
    }
}

fn load_table(table: u32, row: u32, offset: u32) -> vec2<u32> {
    let index = (row * (2u * params.degree) + offset) * 2u;
    if (table == 0u) { return vec2<u32>(roots[index], roots[index + 1u]); }
    return vec2<u32>(twists[index], twists[index + 1u]);
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
    let row = gid.y;
    if (i >= params.degree || row >= params.n_rows) { return; }
    let q = row_q(row);
    let qbits = row_qbits(row);
    let index = row * params.degree + i;
    let twist = load_table(1u, row, i);
    store_coeff(0u, index, mulmod(load_coeff(0u, index), twist, q, qbits));
    store_coeff(1u, index, mulmod(load_coeff(1u, index), twist, q, qbits));
}

@compute @workgroup_size(64)
fn twist_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let row = gid.y;
    if (i >= params.degree || row >= params.n_rows) { return; }
    let q = row_q(row);
    let qbits = row_qbits(row);
    let index = row * params.degree + i;
    let twist = load_table(1u, row, i);
    store_coeff(0u, index, mulmod(load_coeff(0u, index), twist, q, qbits));
}

@compute @workgroup_size(64)
fn bit_reverse_both(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let row = gid.y;
    if (i >= params.degree || row >= params.n_rows) { return; }
    let j = reverse_low_bits(i, params.log_degree);
    if (i >= j) { return; }
    let a = row * params.degree + i;
    let b = row * params.degree + j;
    let lhs_a = load_coeff(0u, a);
    let lhs_b = load_coeff(0u, b);
    let rhs_a = load_coeff(1u, a);
    let rhs_b = load_coeff(1u, b);
    store_coeff(0u, a, lhs_b);
    store_coeff(0u, b, lhs_a);
    store_coeff(1u, a, rhs_b);
    store_coeff(1u, b, rhs_a);
}

fn butterfly(buf: u32, butterfly_index: u32, row: u32) {
    let block = butterfly_index / params.half;
    let j = butterfly_index - block * params.half;
    let left = block * (2u * params.half) + j;
    let right = left + params.half;
    let row_base = row * params.degree;
    let q = row_q(row);
    let qbits = row_qbits(row);
    let w = load_table(0u, row, params.roots_offset + j * params.step);
    let u = load_coeff(buf, row_base + left);
    let v = mulmod(load_coeff(buf, row_base + right), w, q, qbits);
    store_coeff(buf, row_base + left, addmod(u, v, q));
    store_coeff(buf, row_base + right, submod(u, v, q));
}

@compute @workgroup_size(64)
fn stage_both(@builtin(global_invocation_id) gid: vec3<u32>) {
    if (gid.x >= params.degree / 2u || gid.y >= params.n_rows) { return; }
    butterfly(0u, gid.x, gid.y);
    butterfly(1u, gid.x, gid.y);
}

@compute @workgroup_size(64)
fn pointwise(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let row = gid.y;
    if (i >= params.degree || row >= params.n_rows) { return; }
    let index = row * params.degree + i;
    store_coeff(
        0u,
        index,
        mulmod(load_coeff(0u, index), load_coeff(1u, index), row_q(row), row_qbits(row)),
    );
}

@compute @workgroup_size(64)
fn bit_reverse_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let row = gid.y;
    if (i >= params.degree || row >= params.n_rows) { return; }
    let j = reverse_low_bits(i, params.log_degree);
    if (i >= j) { return; }
    let a = row * params.degree + i;
    let b = row * params.degree + j;
    let va = load_coeff(0u, a);
    let vb = load_coeff(0u, b);
    store_coeff(0u, a, vb);
    store_coeff(0u, b, va);
}

@compute @workgroup_size(64)
fn stage_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    if (gid.x >= params.degree / 2u || gid.y >= params.n_rows) { return; }
    butterfly(0u, gid.x, gid.y);
}

@compute @workgroup_size(64)
fn finalize_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let row = gid.y;
    if (i >= params.degree || row >= params.n_rows) { return; }
    let index = row * params.degree + i;
    let inv_twist_times_n_inv = load_table(1u, row, params.degree + i);
    store_coeff(
        0u,
        index,
        mulmod(load_coeff(0u, index), inv_twist_times_n_inv, row_q(row), row_qbits(row)),
    );
}

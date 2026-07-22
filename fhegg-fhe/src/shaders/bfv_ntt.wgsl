// Exact negacyclic RNS NTT over fhe.rs's serialized power-basis rows.
//
// WGSL deliberately uses only core u32 operations. Every residue/modulus is
// represented as (lo, hi). The admitted GPU family is q < 2^48, so an exact
// three-limb radix-2^16 Montgomery product replaces the former per-bit
// double-and-add loop. Immutable tables upload in Montgomery form, while input
// conversion is fused into the first GPU pass; standalone forward and
// inverse/multiply terminal boundaries return canonical residues. This remains
// portable across Metal, Vulkan, DX12, and WebGPU.

struct Meta {
    degree      : u32,
    log_degree  : u32,
    half        : u32,
    step        : u32,
    roots_offset: u32,
    n_rows      : u32,
    modulus_rows: u32,
    _pad1       : u32,
};

@group(0) @binding(0) var<uniform>             params : Meta;
@group(0) @binding(1) var<storage, read_write> lhs    : array<u32>;
@group(0) @binding(2) var<storage, read_write> rhs    : array<u32>;
// Per row: q.lo, q.hi, -q[0]^-1 mod 2^16, padding,
//          R^2.lo, R^2.hi, padding, padding.
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

fn addmod(a: vec2<u32>, b: vec2<u32>, q: vec2<u32>) -> vec2<u32> {
    var s = add64(a, b);
    if (ge64(s, q)) { s = sub64(s, q); }
    return s;
}

fn submod(a: vec2<u32>, b: vec2<u32>, q: vec2<u32>) -> vec2<u32> {
    if (ge64(a, b)) { return sub64(a, b); }
    return sub64(q, sub64(b, a));
}

// REDC(a*b) in base 2^16 with R=2^48. `t` is a seven-limb carrier: six
// product limbs plus the bounded reduction carry. Every inner accumulator is
// at most 0xffff^2 + 2*0xffff = 0xffffffff, so no u32 product/add overflows.
// Inputs and output are canonical Montgomery residues; one final subtraction
// is sufficient because REDC(a*b) < 2q for a,b<q<R.
fn mont_mul(a: vec2<u32>, b: vec2<u32>, q: vec2<u32>, qinv16: u32) -> vec2<u32> {
    let mask = 0xffffu;
    let ad = array<u32, 3>(a.x & mask, a.x >> 16u, a.y & mask);
    let bd = array<u32, 3>(b.x & mask, b.x >> 16u, b.y & mask);
    let qd = array<u32, 3>(q.x & mask, q.x >> 16u, q.y & mask);
    var t = array<u32, 7>(0u, 0u, 0u, 0u, 0u, 0u, 0u);

    for (var i = 0u; i < 3u; i = i + 1u) {
        var carry = 0u;
        for (var j = 0u; j < 3u; j = j + 1u) {
            let index = i + j;
            let uv = t[index] + ad[j] * bd[i] + carry;
            t[index] = uv & mask;
            carry = uv >> 16u;
        }
        for (var k = i + 3u; k < 7u; k = k + 1u) {
            let uv = t[k] + carry;
            t[k] = uv & mask;
            carry = uv >> 16u;
        }

        let m = (t[i] * qinv16) & mask;
        carry = 0u;
        for (var j = 0u; j < 3u; j = j + 1u) {
            let index = i + j;
            let uv = t[index] + m * qd[j] + carry;
            t[index] = uv & mask;
            carry = uv >> 16u;
        }
        for (var k = i + 3u; k < 7u; k = k + 1u) {
            let uv = t[k] + carry;
            t[k] = uv & mask;
            carry = uv >> 16u;
        }
    }

    var reduced = vec2<u32>(t[3] | (t[4] << 16u), t[5] | (t[6] << 16u));
    if (ge64(reduced, q)) { reduced = sub64(reduced, q); }
    return reduced;
}

fn table_row(row: u32) -> u32 {
    return row % params.modulus_rows;
}

fn row_q(row: u32) -> vec2<u32> {
    let source = table_row(row);
    return vec2<u32>(qdata[source * 8u], qdata[source * 8u + 1u]);
}

fn row_qinv16(row: u32) -> u32 { return qdata[table_row(row) * 8u + 2u]; }

fn row_r_squared(row: u32) -> vec2<u32> {
    let source = table_row(row);
    return vec2<u32>(qdata[source * 8u + 4u], qdata[source * 8u + 5u]);
}

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
    let index = (table_row(row) * (2u * params.degree) + offset) * 2u;
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
    let qinv16 = row_qinv16(row);
    let index = row * params.degree + i;
    let twist = load_table(1u, row, i);
    store_coeff(0u, index, mont_mul(load_coeff(0u, index), twist, q, qinv16));
    store_coeff(1u, index, mont_mul(load_coeff(1u, index), twist, q, qinv16));
}

@compute @workgroup_size(64)
fn twist_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let row = gid.y;
    if (i >= params.degree || row >= params.n_rows) { return; }
    let q = row_q(row);
    let qinv16 = row_qinv16(row);
    let index = row * params.degree + i;
    let twist = load_table(1u, row, i);
    store_coeff(0u, index, mont_mul(load_coeff(0u, index), twist, q, qinv16));
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

fn butterfly(buf: u32, butterfly_index: u32, row: u32, normalize_output: bool) {
    let block = butterfly_index / params.half;
    let j = butterfly_index - block * params.half;
    let left = block * (2u * params.half) + j;
    let right = left + params.half;
    let row_base = row * params.degree;
    let q = row_q(row);
    let qinv16 = row_qinv16(row);
    let w = load_table(0u, row, params.roots_offset + j * params.step);
    let u = load_coeff(buf, row_base + left);
    let v = mont_mul(load_coeff(buf, row_base + right), w, q, qinv16);
    var left_output = addmod(u, v, q);
    var right_output = submod(u, v, q);
    if (normalize_output) {
        let one = vec2<u32>(1u, 0u);
        left_output = mont_mul(left_output, one, q, qinv16);
        right_output = mont_mul(right_output, one, q, qinv16);
    }
    store_coeff(buf, row_base + left, left_output);
    store_coeff(buf, row_base + right, right_output);
}

@compute @workgroup_size(64)
fn stage_both(@builtin(global_invocation_id) gid: vec3<u32>) {
    if (gid.x >= params.degree / 2u || gid.y >= params.n_rows) { return; }
    butterfly(0u, gid.x, gid.y, false);
    butterfly(1u, gid.x, gid.y, false);
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
        mont_mul(load_coeff(0u, index), load_coeff(1u, index), row_q(row), row_qinv16(row)),
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

// Standalone inverse transforms receive a canonical spectrum. Convert each
// coefficient with REDC(value * R^2) while performing the same in-place bit
// reversal. `i <= j` owns each pair exactly once; fixed points are converted
// rather than skipped.
@compute @workgroup_size(64)
fn bit_reverse_lhs_mont(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let row = gid.y;
    if (i >= params.degree || row >= params.n_rows) { return; }
    let j = reverse_low_bits(i, params.log_degree);
    if (i > j) { return; }
    let a = row * params.degree + i;
    let b = row * params.degree + j;
    let q = row_q(row);
    let qinv16 = row_qinv16(row);
    let r_squared = row_r_squared(row);
    if (i == j) {
        store_coeff(0u, a, mont_mul(load_coeff(0u, a), r_squared, q, qinv16));
        return;
    }
    let va = load_coeff(0u, a);
    let vb = load_coeff(0u, b);
    store_coeff(0u, a, mont_mul(vb, r_squared, q, qinv16));
    store_coeff(0u, b, mont_mul(va, r_squared, q, qinv16));
}

@compute @workgroup_size(64)
fn stage_lhs(@builtin(global_invocation_id) gid: vec3<u32>) {
    if (gid.x >= params.degree / 2u || gid.y >= params.n_rows) { return; }
    // A standalone forward transform returns canonical spectra. Multiply and
    // inverse stages use the inverse root-table half and stay Montgomery until
    // `finalize_lhs`.
    let normalize = params.roots_offset == 0u && params.half * 2u == params.degree;
    butterfly(0u, gid.x, gid.y, normalize);
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
        mont_mul(
            mont_mul(
                load_coeff(0u, index),
                inv_twist_times_n_inv,
                row_q(row),
                row_qinv16(row),
            ),
            vec2<u32>(1u, 0u),
            row_q(row),
            row_qinv16(row),
        ),
    );
}

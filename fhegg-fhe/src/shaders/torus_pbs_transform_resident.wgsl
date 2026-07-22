// Exact transform-resident dense TFHE blind rotation for the deployed native-
// torus shape. The standard BSK is forward-transformed once into four-prime RNS
// spectra. Each CMUX keeps accumulator, spectra, and scratch on-device:
//
//   rotate/difference/decompose -> forward digits -> spectral product/sum
//       -> inverse products -> exact centered CRT add
//
// WGSL has no portable u64. Torus coefficients use two u32 limbs; NTT residues
// use exact Montgomery u32 arithmetic; CRT reconstructs a centered ~120-bit
// integer with four u32 limbs and retains its exact low 64 bits.

struct Metadata {
    degree: u32,
    log_degree: u32,
    glwe_size: u32,
    base_log: u32,
    level_count: u32,
    rotation: u32,
    key_step: u32,
    input_buffer: u32,
    n_rows: u32,
    bsk_series: u32,
    _pad0: u32,
    _pad1: u32,
};

@group(0) @binding(0) var<uniform> params: Metadata;
@group(0) @binding(1) var<storage, read_write> accumulator_a: array<u32>;
@group(0) @binding(2) var<storage, read_write> accumulator_b: array<u32>;
@group(0) @binding(3) var<storage, read_write> bsk_spectra: array<u32>;
// First glwe_size*n_rows rows are digit spectra; the next equally-sized rows
// are product spectra, each row containing `degree` coefficients.
@group(0) @binding(4) var<storage, read_write> transform_scratch: array<u32>;
// Per row: q, -q^-1 mod 2^32, R^2 mod q, padding.
@group(0) @binding(5) var<storage, read> qdata: array<u32>;
// Per row: degree forward powers followed by degree inverse powers.
@group(0) @binding(6) var<storage, read> roots: array<u32>;
// Per row: psi^i followed by n^-1*psi^-i, all Montgomery encoded.
@group(0) @binding(7) var<storage, read> twists: array<u32>;
@group(0) @binding(8) var<storage, read> crt_data: array<u32>;
// GPU-produced centered-modulus-switch rotations. Existing single-PBS entry
// points continue to use params.rotation; only the resident-chain entry points
// consume this schedule.
@group(0) @binding(9) var<storage, read> scheduled_rotations: array<u32>;

var<workgroup> ntt_row: array<u32, 4096>;

fn add64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let lo = a.x + b.x;
    return vec2<u32>(lo, a.y + b.y + select(0u, 1u, lo < a.x));
}

fn sub64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let borrow = select(0u, 1u, a.x < b.x);
    return vec2<u32>(a.x - b.x, a.y - b.y - borrow);
}

fn neg64(a: vec2<u32>) -> vec2<u32> {
    return sub64(vec2<u32>(0u, 0u), a);
}

fn or64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    return vec2<u32>(a.x | b.x, a.y | b.y);
}

fn and64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    return vec2<u32>(a.x & b.x, a.y & b.y);
}

fn shr64(a: vec2<u32>, shift: u32) -> vec2<u32> {
    if (shift == 0u) { return a; }
    if (shift < 32u) {
        return vec2<u32>(a.x >> shift | a.y << (32u - shift), a.y >> shift);
    }
    if (shift == 32u) { return vec2<u32>(a.y, 0u); }
    return vec2<u32>(a.y >> (shift - 32u), 0u);
}

fn shl64(a: vec2<u32>, shift: u32) -> vec2<u32> {
    if (shift == 0u) { return a; }
    if (shift < 32u) {
        return vec2<u32>(a.x << shift, a.y << shift | a.x >> (32u - shift));
    }
    if (shift == 32u) { return vec2<u32>(0u, a.x); }
    return vec2<u32>(0u, a.x << (shift - 32u));
}

fn arithmetic_shr64(a: vec2<u32>, shift: u32) -> vec2<u32> {
    if (shift == 0u) { return a; }
    let fill = select(0u, 0xffffffffu, (a.y & 0x80000000u) != 0u);
    if (shift < 32u) {
        return vec2<u32>(
            a.x >> shift | a.y << (32u - shift),
            a.y >> shift | fill << (32u - shift),
        );
    }
    if (shift == 32u) { return vec2<u32>(a.y, fill); }
    return vec2<u32>(a.y >> (shift - 32u) | fill << (64u - shift), fill);
}

fn low_mask64(bits: u32) -> vec2<u32> {
    if (bits < 32u) { return vec2<u32>((1u << bits) - 1u, 0u); }
    if (bits == 32u) { return vec2<u32>(0xffffffffu, 0u); }
    return vec2<u32>(0xffffffffu, (1u << (bits - 32u)) - 1u);
}

fn load_acc64(coefficient: u32, which: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    if (which == 0u) {
        return vec2<u32>(accumulator_a[limb], accumulator_a[limb + 1u]);
    }
    return vec2<u32>(accumulator_b[limb], accumulator_b[limb + 1u]);
}

fn store_acc64(coefficient: u32, which: u32, value: vec2<u32>) {
    let limb = coefficient * 2u;
    if (which == 0u) {
        accumulator_a[limb] = value.x;
        accumulator_a[limb + 1u] = value.y;
    } else {
        accumulator_b[limb] = value.x;
        accumulator_b[limb + 1u] = value.y;
    }
}

fn batch_accumulator_coefficients() -> u32 {
    return params.glwe_size * params.degree;
}

fn load_batch_acc64(batch: u32, coefficient: u32, which: u32) -> vec2<u32> {
    let limb = (batch * batch_accumulator_coefficients() + coefficient) * 2u;
    if (which == 0u) {
        return vec2<u32>(accumulator_a[limb], accumulator_a[limb + 1u]);
    }
    return vec2<u32>(accumulator_b[limb], accumulator_b[limb + 1u]);
}

fn store_batch_acc64(batch: u32, coefficient: u32, which: u32, value: vec2<u32>) {
    let limb = (batch * batch_accumulator_coefficients() + coefficient) * 2u;
    if (which == 0u) {
        accumulator_a[limb] = value.x;
        accumulator_a[limb + 1u] = value.y;
    } else {
        accumulator_b[limb] = value.x;
        accumulator_b[limb + 1u] = value.y;
    }
}

fn init_decomposer_state(input: vec2<u32>) -> vec2<u32> {
    let represented_bits = params.base_log * params.level_count;
    let non_represented_bits = 64u - represented_bits;
    var state = shr64(input, non_represented_bits - 1u);
    let rounding_bit = state.x & 1u;
    state = shr64(add64(state, vec2<u32>(1u, 0u)), 1u);
    state = and64(state, low_mask64(represented_bits));
    let shifted_rounding = shl64(vec2<u32>(rounding_bit, 0u), represented_bits - 1u);
    let balance_source = and64(
        or64(sub64(state, vec2<u32>(1u, 0u)), shifted_rounding),
        state,
    );
    let need_balance = shr64(balance_source, represented_bits - 1u).x & 1u;
    return sub64(state, shl64(vec2<u32>(need_balance, 0u), represented_bits));
}

fn load_rotated64_at(output_coefficient: u32, rotation: u32) -> vec2<u32> {
    let polynomial = output_coefficient / params.degree;
    let out_index = output_coefficient % params.degree;
    let global_negative = rotation >= params.degree;
    let shift = select(rotation, rotation - params.degree, global_negative);
    var source_index: u32;
    var wrap_negative: bool;
    if (out_index >= shift) {
        source_index = out_index - shift;
        wrap_negative = false;
    } else {
        source_index = params.degree + out_index - shift;
        wrap_negative = true;
    }
    let value = load_acc64(polynomial * params.degree + source_index, params.input_buffer);
    return select(value, neg64(value), global_negative != wrap_negative);
}

fn load_batch_rotated64_at(batch: u32, output_coefficient: u32, rotation: u32) -> vec2<u32> {
    let polynomial = output_coefficient / params.degree;
    let out_index = output_coefficient % params.degree;
    let global_negative = rotation >= params.degree;
    let shift = select(rotation, rotation - params.degree, global_negative);
    var source_index: u32;
    var wrap_negative: bool;
    if (out_index >= shift) {
        source_index = out_index - shift;
        wrap_negative = false;
    } else {
        source_index = params.degree + out_index - shift;
        wrap_negative = true;
    }
    let value = load_batch_acc64(
        batch,
        polynomial * params.degree + source_index,
        params.input_buffer,
    );
    return select(value, neg64(value), global_negative != wrap_negative);
}

fn load_rotated64(output_coefficient: u32) -> vec2<u32> {
    return load_rotated64_at(output_coefficient, params.rotation);
}

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
    return vec2<u32>(
        (p00 & mask) | (middle << 16u),
        p11 + (p01 >> 16u) + (p10 >> 16u) + (middle >> 16u),
    );
}

fn mont_mul(a: u32, b: u32, q: u32, qinv: u32) -> u32 {
    let product = mul32_wide(a, b);
    let m = product.x * qinv;
    let correction = mul32_wide(m, q);
    let low = product.x + correction.x;
    let reduced = product.y + correction.y + select(0u, 1u, low < product.x);
    return select(reduced, reduced - q, reduced >= q);
}

fn row_q(row: u32) -> u32 { return qdata[row * 4u]; }
fn row_qinv(row: u32) -> u32 { return qdata[row * 4u + 1u]; }
fn row_r2(row: u32) -> u32 { return qdata[row * 4u + 2u]; }

fn root(row: u32, offset: u32) -> u32 {
    return roots[row * (2u * params.degree) + offset];
}

fn twist(row: u32, offset: u32) -> u32 {
    return twists[row * (2u * params.degree) + offset];
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

fn bsk_base(series: u32) -> u32 { return series * params.degree; }
fn digit_series_base(series: u32) -> u32 { return series * params.degree; }
fn product_offset() -> u32 { return params.glwe_size * params.n_rows * params.degree; }
fn product_series_base(series: u32) -> u32 {
    return product_offset() + series * params.degree;
}

fn batch_scratch_words() -> u32 {
    return 2u * params.glwe_size * params.n_rows * params.degree;
}

fn batch_digit_series_base(batch: u32, series: u32) -> u32 {
    return batch * batch_scratch_words() + digit_series_base(series);
}

fn batch_product_series_base(batch: u32, series: u32) -> u32 {
    return batch * batch_scratch_words() + product_series_base(series);
}

@compute @workgroup_size(64)
fn monomial_rotate(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    if (coefficient >= params.glwe_size * params.degree) { return; }
    store_acc64(coefficient, 1u - params.input_buffer, load_rotated64(coefficient));
}

@compute @workgroup_size(64)
fn monomial_rotate_scheduled(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    if (coefficient >= params.glwe_size * params.degree) { return; }
    let rotation = scheduled_rotations[params.key_step];
    store_acc64(
        coefficient,
        1u - params.input_buffer,
        load_rotated64_at(coefficient, rotation),
    );
}

@compute @workgroup_size(64)
fn monomial_rotate_scheduled_batch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let batch = gid.z;
    if (coefficient >= params.glwe_size * params.degree) { return; }
    let rotation = scheduled_rotations[batch * params._pad0 + params.key_step];
    store_batch_acc64(
        batch,
        coefficient,
        1u - params.input_buffer,
        load_batch_rotated64_at(batch, coefficient, rotation),
    );
}

fn decompose_at_rotation(coefficient: u32, rotation: u32) {
    let difference = sub64(
        load_rotated64_at(coefficient, rotation),
        load_acc64(coefficient, params.input_buffer),
    );
    var state = init_decomposer_state(difference);
    let digit_mask = (1u << params.base_log) - 1u;
    let raw_digit = state.x & digit_mask;
    state = arithmetic_shr64(state, params.base_log);
    let carry = (((raw_digit - 1u) | state.x) & raw_digit) >> (params.base_log - 1u);
    let digit = sub64(
        vec2<u32>(raw_digit, 0u),
        shl64(vec2<u32>(carry, 0u), params.base_log),
    );
    let negative = (digit.y & 0x80000000u) != 0u;
    let magnitude = select(digit, neg64(digit), negative).x;
    let polynomial = coefficient / params.degree;
    let local = coefficient % params.degree;
    for (var row = 0u; row < params.n_rows; row = row + 1u) {
        let q = row_q(row);
        let canonical = select(magnitude, select(0u, q - magnitude, magnitude != 0u), negative);
        let montgomery = mont_mul(canonical, row_r2(row), q, row_qinv(row));
        transform_scratch[digit_series_base(polynomial * params.n_rows + row) + local] = montgomery;
    }
}

@compute @workgroup_size(64)
fn decompose_difference_to_rns(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let glwe_coefficients = params.glwe_size * params.degree;
    if (coefficient >= glwe_coefficients) { return; }
    // The deployed shape has one level. Keep the exact tfhe-rs digit extraction
    // general enough to reject accidental metadata drift at the host boundary.
    decompose_at_rotation(coefficient, params.rotation);
}

@compute @workgroup_size(64)
fn decompose_difference_scheduled(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let glwe_coefficients = params.glwe_size * params.degree;
    if (coefficient >= glwe_coefficients) { return; }
    decompose_at_rotation(coefficient, scheduled_rotations[params.key_step]);
}

@compute @workgroup_size(64)
fn decompose_difference_scheduled_batch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let batch = gid.z;
    let glwe_coefficients = params.glwe_size * params.degree;
    if (coefficient >= glwe_coefficients) { return; }
    let rotation = scheduled_rotations[batch * params._pad0 + params.key_step];
    let difference = sub64(
        load_batch_rotated64_at(batch, coefficient, rotation),
        load_batch_acc64(batch, coefficient, params.input_buffer),
    );
    var state = init_decomposer_state(difference);
    let digit_mask = (1u << params.base_log) - 1u;
    let raw_digit = state.x & digit_mask;
    state = arithmetic_shr64(state, params.base_log);
    let carry = (((raw_digit - 1u) | state.x) & raw_digit) >> (params.base_log - 1u);
    let digit = sub64(
        vec2<u32>(raw_digit, 0u),
        shl64(vec2<u32>(carry, 0u), params.base_log),
    );
    let negative = (digit.y & 0x80000000u) != 0u;
    let magnitude = select(digit, neg64(digit), negative).x;
    let polynomial = coefficient / params.degree;
    let local = coefficient % params.degree;
    for (var row = 0u; row < params.n_rows; row = row + 1u) {
        let q = row_q(row);
        let canonical = select(magnitude, select(0u, q - magnitude, magnitude != 0u), negative);
        let montgomery = mont_mul(canonical, row_r2(row), q, row_qinv(row));
        transform_scratch[
            batch_digit_series_base(batch, polynomial * params.n_rows + row) + local
        ] = montgomery;
    }
}

// Forward-transform every BSK polynomial once at plan construction.
@compute @workgroup_size(256)
fn forward_bsk(
    @builtin(local_invocation_id) lid: vec3<u32>,
    @builtin(workgroup_id) wid: vec3<u32>,
) {
    let series = wid.y;
    if (series >= params.bsk_series) { return; }
    let row = series % params.n_rows;
    let base = bsk_base(series);
    let q = row_q(row);
    let qinv = row_qinv(row);
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        ntt_row[reverse_low_bits(i, params.log_degree)] =
            mont_mul(bsk_spectra[base + i], twist(row, i), q, qinv);
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
            let u = ntt_row[left];
            let v = mont_mul(ntt_row[right], root(row, j * step), q, qinv);
            ntt_row[left] = addmod(u, v, q);
            ntt_row[right] = submod(u, v, q);
        }
        workgroupBarrier();
        len = len * 2u;
    }
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        bsk_spectra[base + i] = ntt_row[i];
    }
}

@compute @workgroup_size(256)
fn forward_digits(
    @builtin(local_invocation_id) lid: vec3<u32>,
    @builtin(workgroup_id) wid: vec3<u32>,
) {
    let series = wid.y;
    if (series >= params.glwe_size * params.n_rows) { return; }
    let row = series % params.n_rows;
    let base = digit_series_base(series);
    let q = row_q(row);
    let qinv = row_qinv(row);
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        ntt_row[reverse_low_bits(i, params.log_degree)] =
            mont_mul(transform_scratch[base + i], twist(row, i), q, qinv);
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
            let u = ntt_row[left];
            let v = mont_mul(ntt_row[right], root(row, j * step), q, qinv);
            ntt_row[left] = addmod(u, v, q);
            ntt_row[right] = submod(u, v, q);
        }
        workgroupBarrier();
        len = len * 2u;
    }
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        transform_scratch[base + i] = ntt_row[i];
    }
}

@compute @workgroup_size(256)
fn forward_digits_batch(
    @builtin(local_invocation_id) lid: vec3<u32>,
    @builtin(workgroup_id) wid: vec3<u32>,
) {
    let series = wid.y;
    let batch = wid.z;
    if (series >= params.glwe_size * params.n_rows) { return; }
    let row = series % params.n_rows;
    let base = batch_digit_series_base(batch, series);
    let q = row_q(row);
    let qinv = row_qinv(row);
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        ntt_row[reverse_low_bits(i, params.log_degree)] =
            mont_mul(transform_scratch[base + i], twist(row, i), q, qinv);
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
            let u = ntt_row[left];
            let v = mont_mul(ntt_row[right], root(row, j * step), q, qinv);
            ntt_row[left] = addmod(u, v, q);
            ntt_row[right] = submod(u, v, q);
        }
        workgroupBarrier();
        len = len * 2u;
    }
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        transform_scratch[base + i] = ntt_row[i];
    }
}

@compute @workgroup_size(64)
fn pointwise_products(@builtin(global_invocation_id) gid: vec3<u32>) {
    let local = gid.x;
    let series = gid.y;
    if (local >= params.degree || series >= params.glwe_size * params.n_rows) { return; }
    let output_polynomial = series / params.n_rows;
    let row_prime = series % params.n_rows;
    let q = row_q(row_prime);
    let qinv = row_qinv(row_prime);
    var sum = 0u;
    for (var input_row = 0u; input_row < params.glwe_size; input_row = input_row + 1u) {
        let digit = transform_scratch[
            digit_series_base(input_row * params.n_rows + row_prime) + local
        ];
        let bsk_polynomial = params.key_step * params.glwe_size * params.glwe_size
            + input_row * params.glwe_size + output_polynomial;
        let bsk_series_index = bsk_polynomial * params.n_rows + row_prime;
        let key = bsk_spectra[bsk_base(bsk_series_index) + local];
        sum = addmod(sum, mont_mul(digit, key, q, qinv), q);
    }
    transform_scratch[product_series_base(series) + local] = sum;
}

@compute @workgroup_size(64)
fn pointwise_products_batch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let local = gid.x;
    let series = gid.y;
    let batch = gid.z;
    if (local >= params.degree || series >= params.glwe_size * params.n_rows) { return; }
    let output_polynomial = series / params.n_rows;
    let row_prime = series % params.n_rows;
    let q = row_q(row_prime);
    let qinv = row_qinv(row_prime);
    var sum = 0u;
    for (var input_row = 0u; input_row < params.glwe_size; input_row = input_row + 1u) {
        let digit = transform_scratch[
            batch_digit_series_base(batch, input_row * params.n_rows + row_prime) + local
        ];
        let bsk_polynomial = params.key_step * params.glwe_size * params.glwe_size
            + input_row * params.glwe_size + output_polynomial;
        let bsk_series_index = bsk_polynomial * params.n_rows + row_prime;
        let key = bsk_spectra[bsk_base(bsk_series_index) + local];
        sum = addmod(sum, mont_mul(digit, key, q, qinv), q);
    }
    transform_scratch[batch_product_series_base(batch, series) + local] = sum;
}

@compute @workgroup_size(256)
fn inverse_products(
    @builtin(local_invocation_id) lid: vec3<u32>,
    @builtin(workgroup_id) wid: vec3<u32>,
) {
    let series = wid.y;
    if (series >= params.glwe_size * params.n_rows) { return; }
    let row = series % params.n_rows;
    let base = product_series_base(series);
    let q = row_q(row);
    let qinv = row_qinv(row);
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        ntt_row[i] = transform_scratch[base + i];
    }
    workgroupBarrier();
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        let reversed = reverse_low_bits(i, params.log_degree);
        if (i < reversed) {
            let value = ntt_row[i];
            ntt_row[i] = ntt_row[reversed];
            ntt_row[reversed] = value;
        }
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
            let u = ntt_row[left];
            let v = mont_mul(ntt_row[right], root(row, params.degree + j * step), q, qinv);
            ntt_row[left] = addmod(u, v, q);
            ntt_row[right] = submod(u, v, q);
        }
        workgroupBarrier();
        len = len * 2u;
    }
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        let scaled = mont_mul(ntt_row[i], twist(row, params.degree + i), q, qinv);
        transform_scratch[base + i] = mont_mul(scaled, 1u, q, qinv);
    }
}

@compute @workgroup_size(256)
fn inverse_products_batch(
    @builtin(local_invocation_id) lid: vec3<u32>,
    @builtin(workgroup_id) wid: vec3<u32>,
) {
    let series = wid.y;
    let batch = wid.z;
    if (series >= params.glwe_size * params.n_rows) { return; }
    let row = series % params.n_rows;
    let base = batch_product_series_base(batch, series);
    let q = row_q(row);
    let qinv = row_qinv(row);
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        ntt_row[i] = transform_scratch[base + i];
    }
    workgroupBarrier();
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        let reversed = reverse_low_bits(i, params.log_degree);
        if (i < reversed) {
            let value = ntt_row[i];
            ntt_row[i] = ntt_row[reversed];
            ntt_row[reversed] = value;
        }
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
            let u = ntt_row[left];
            let v = mont_mul(ntt_row[right], root(row, params.degree + j * step), q, qinv);
            ntt_row[left] = addmod(u, v, q);
            ntt_row[right] = submod(u, v, q);
        }
        workgroupBarrier();
        len = len * 2u;
    }
    for (var i = lid.x; i < params.degree; i = i + 256u) {
        let scaled = mont_mul(ntt_row[i], twist(row, params.degree + i), q, qinv);
        transform_scratch[base + i] = mont_mul(scaled, 1u, q, qinv);
    }
}

fn mul_canonical_by_mont(a: u32, b_mont: u32, row: u32) -> u32 {
    return mont_mul(a, b_mont, row_q(row), row_qinv(row));
}

fn add128(a: vec4<u32>, b: vec4<u32>) -> vec4<u32> {
    let x0 = a.x + b.x;
    let c0 = select(0u, 1u, x0 < a.x);
    let y0 = a.y + b.y;
    let c1a = select(0u, 1u, y0 < a.y);
    let x1 = y0 + c0;
    let c1b = select(0u, 1u, x1 < y0);
    let z0 = a.z + b.z;
    let c2a = select(0u, 1u, z0 < a.z);
    let x2 = z0 + (c1a | c1b);
    let c2b = select(0u, 1u, x2 < z0);
    return vec4<u32>(x0, x1, x2, a.w + b.w + (c2a | c2b));
}

fn sub128(a: vec4<u32>, b: vec4<u32>) -> vec4<u32> {
    let x0 = a.x - b.x;
    let b0 = select(0u, 1u, a.x < b.x);
    let by = b.y + b0;
    let by_over = select(0u, 1u, by < b.y);
    let x1 = a.y - by;
    let b1 = by_over | select(0u, 1u, a.y < by);
    let bz = b.z + b1;
    let bz_over = select(0u, 1u, bz < b.z);
    let x2 = a.z - bz;
    let b2 = bz_over | select(0u, 1u, a.z < bz);
    return vec4<u32>(x0, x1, x2, a.w - b.w - b2);
}

fn mul128_word(base: vec4<u32>, word: u32) -> vec4<u32> {
    let p0 = mul32_wide(base.x, word);
    let p1 = mul32_wide(base.y, word);
    let x1 = p1.x + p0.y;
    let c1 = select(0u, 1u, x1 < p1.x);
    let p2 = mul32_wide(base.z, word);
    let carry2 = p1.y + c1;
    let x2 = p2.x + carry2;
    let c2 = select(0u, 1u, x2 < p2.x);
    let p3 = mul32_wide(base.w, word);
    return vec4<u32>(p0.x, x1, x2, p3.x + p2.y + c2);
}

fn greater128(a: vec4<u32>, b: vec4<u32>) -> bool {
    if (a.w != b.w) { return a.w > b.w; }
    if (a.z != b.z) { return a.z > b.z; }
    if (a.y != b.y) { return a.y > b.y; }
    return a.x > b.x;
}

fn crt_vec(offset: u32) -> vec4<u32> {
    return vec4<u32>(crt_data[offset], crt_data[offset + 1u], crt_data[offset + 2u], crt_data[offset + 3u]);
}

fn reconstruct_centered_low64(r: vec4<u32>) -> vec2<u32> {
    let c0 = r.x;
    let c1 = mul_canonical_by_mont(submod(r.y, c0, row_q(1u)), crt_data[0], 1u);
    let x_mod_q2 = addmod(c0, mul_canonical_by_mont(c1, crt_data[3], 2u), row_q(2u));
    let c2 = mul_canonical_by_mont(submod(r.z, x_mod_q2, row_q(2u)), crt_data[1], 2u);
    let x_mod_q3 = addmod(
        c0,
        addmod(
            mul_canonical_by_mont(c1, crt_data[4], 3u),
            mul_canonical_by_mont(c2, crt_data[5], 3u),
            row_q(3u),
        ),
        row_q(3u),
    );
    let c3 = mul_canonical_by_mont(submod(r.w, x_mod_q3, row_q(3u)), crt_data[2], 3u);
    var value = vec4<u32>(c0, 0u, 0u, 0u);
    value = add128(value, mul128_word(crt_vec(8u), c1));
    value = add128(value, mul128_word(crt_vec(12u), c2));
    value = add128(value, mul128_word(crt_vec(16u), c3));
    if (greater128(value, crt_vec(24u))) {
        value = sub128(value, crt_vec(20u));
    }
    return value.xy;
}

@compute @workgroup_size(64)
fn crt_add_accumulator(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    if (coefficient >= params.glwe_size * params.degree) { return; }
    let polynomial = coefficient / params.degree;
    let local = coefficient % params.degree;
    let base_series = polynomial * params.n_rows;
    let residues = vec4<u32>(
        transform_scratch[product_series_base(base_series) + local],
        transform_scratch[product_series_base(base_series + 1u) + local],
        transform_scratch[product_series_base(base_series + 2u) + local],
        transform_scratch[product_series_base(base_series + 3u) + local],
    );
    let product = reconstruct_centered_low64(residues);
    let next = add64(load_acc64(coefficient, params.input_buffer), product);
    store_acc64(coefficient, 1u - params.input_buffer, next);
}


@compute @workgroup_size(64)
fn crt_add_accumulator_batch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let batch = gid.z;
    if (coefficient >= params.glwe_size * params.degree) { return; }
    let polynomial = coefficient / params.degree;
    let local = coefficient % params.degree;
    let base_series = polynomial * params.n_rows;
    let residues = vec4<u32>(
        transform_scratch[batch_product_series_base(batch, base_series) + local],
        transform_scratch[batch_product_series_base(batch, base_series + 1u) + local],
        transform_scratch[batch_product_series_base(batch, base_series + 2u) + local],
        transform_scratch[batch_product_series_base(batch, base_series + 3u) + local],
    );
    let product = reconstruct_centered_low64(residues);
    let next = add64(load_batch_acc64(batch, coefficient, params.input_buffer), product);
    store_batch_acc64(batch, coefficient, 1u - params.input_buffer, next);
}

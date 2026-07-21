// Exact device-resident TFHE blind-rotation chain.
//
// The accumulator ping-pongs between two native-torus buffers.  One standard
// GGSW bootstrapping-key buffer remains resident for the complete chain.  Each
// nonzero mask rotation performs GPU-side
//
//   difference = accumulator * X^a - accumulator
//   next        = accumulator + GGSW_i * Decomp(difference)
//
// and only the final accumulator is copied back to the host.  Arithmetic is
// exact modulo 2^64 using two u32 limbs and 16-bit-split products.

struct Metadata {
    degree: u32,
    glwe_size: u32,
    base_log: u32,
    level_count: u32,
    rotation: u32,
    key_offset: u32,
    input_buffer: u32,
    _pad: u32,
};

@group(0) @binding(0) var<uniform> params: Metadata;
@group(0) @binding(1) var<storage, read_write> accumulator_a: array<u32>;
@group(0) @binding(2) var<storage, read_write> accumulator_b: array<u32>;
@group(0) @binding(3) var<storage, read> bootstrap_key: array<u32>;
@group(0) @binding(4) var<storage, read_write> decomposed: array<u32>;

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

fn load_key64(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(bootstrap_key[limb], bootstrap_key[limb + 1u]);
}

fn load_decomposed64(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(decomposed[limb], decomposed[limb + 1u]);
}

fn store_decomposed64(coefficient: u32, value: vec2<u32>) {
    let limb = coefficient * 2u;
    decomposed[limb] = value.x;
    decomposed[limb + 1u] = value.y;
}

fn add64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let lo = a.x + b.x;
    let carry = select(0u, 1u, lo < a.x);
    return vec2<u32>(lo, a.y + b.y + carry);
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
    let sign_fill = select(0u, 0xffffffffu, (a.y & 0x80000000u) != 0u);
    if (shift < 32u) {
        return vec2<u32>(
            a.x >> shift | a.y << (32u - shift),
            a.y >> shift | sign_fill << (32u - shift),
        );
    }
    if (shift == 32u) { return vec2<u32>(a.y, sign_fill); }
    return vec2<u32>(a.y >> (shift - 32u) | sign_fill << (64u - shift), sign_fill);
}

fn low_mask64(bits: u32) -> vec2<u32> {
    if (bits < 32u) { return vec2<u32>((1u << bits) - 1u, 0u); }
    if (bits == 32u) { return vec2<u32>(0xffffffffu, 0u); }
    return vec2<u32>(0xffffffffu, (1u << (bits - 32u)) - 1u);
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

fn mul64_low(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let low = mul32_wide(a.x, b.x);
    return vec2<u32>(low.x, low.y + a.x * b.y + a.y * b.x);
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

// Exact multiplication by X^rotation in Z[X]/(X^N+1), where rotation is in
// [0, 2N).  The second half of that range carries the global minus sign.
fn load_rotated64(output_coefficient: u32) -> vec2<u32> {
    let polynomial = output_coefficient / params.degree;
    let out_index = output_coefficient % params.degree;
    let global_negative = params.rotation >= params.degree;
    let shift = select(params.rotation, params.rotation - params.degree, global_negative);
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

@compute @workgroup_size(64)
fn monomial_rotate(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let count = params.glwe_size * params.degree;
    if (coefficient >= count) { return; }
    store_acc64(coefficient, 1u - params.input_buffer, load_rotated64(coefficient));
}

@compute @workgroup_size(64)
fn decompose_rotated_difference(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let glwe_coefficients = params.glwe_size * params.degree;
    if (coefficient >= glwe_coefficients) { return; }

    let difference = sub64(
        load_rotated64(coefficient),
        load_acc64(coefficient, params.input_buffer),
    );
    var state = init_decomposer_state(difference);
    for (var level = 0u; level < params.level_count; level = level + 1u) {
        let digit_mask = (1u << params.base_log) - 1u;
        let raw_digit = state.x & digit_mask;
        state = arithmetic_shr64(state, params.base_log);
        let carry = (((raw_digit - 1u) | state.x) & raw_digit) >> (params.base_log - 1u);
        state = add64(state, vec2<u32>(carry, 0u));
        let digit = sub64(
            vec2<u32>(raw_digit, 0u),
            shl64(vec2<u32>(carry, 0u), params.base_log),
        );
        store_decomposed64(level * glwe_coefficients + coefficient, digit);
    }
}

@compute @workgroup_size(64)
fn external_product_step(@builtin(global_invocation_id) gid: vec3<u32>) {
    let output_coefficient = gid.x;
    let output_coefficients = params.glwe_size * params.degree;
    if (output_coefficient >= output_coefficients) { return; }

    let output_polynomial = output_coefficient / params.degree;
    let out_index = output_coefficient % params.degree;
    let glwe_coefficients = params.glwe_size * params.degree;
    var value = load_acc64(output_coefficient, params.input_buffer);
    for (var level = 0u; level < params.level_count; level = level + 1u) {
        for (var row = 0u; row < params.glwe_size; row = row + 1u) {
            let digit_base = level * glwe_coefficients + row * params.degree;
            let key_poly = params.key_offset
                + ((level * params.glwe_size + row) * params.glwe_size + output_polynomial)
                * params.degree;
            for (var lhs_index = 0u; lhs_index < params.degree; lhs_index = lhs_index + 1u) {
                var rhs_index: u32;
                var positive: bool;
                if (lhs_index <= out_index) {
                    rhs_index = out_index - lhs_index;
                    positive = true;
                } else {
                    rhs_index = params.degree + out_index - lhs_index;
                    positive = false;
                }
                let term = mul64_low(
                    load_decomposed64(digit_base + lhs_index),
                    load_key64(key_poly + rhs_index),
                );
                value = select(sub64(value, term), add64(value, term), positive);
            }
        }
    }
    store_acc64(output_coefficient, 1u - params.input_buffer, value);
}

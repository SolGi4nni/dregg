// Exact coefficient-domain TFHE external product.
//
// Pass 1 (`decompose`) performs tfhe-rs's native-modulus balanced signed
// gadget decomposition on every coefficient of the input GLWE ciphertext.
// Pass 2 (`external_product`) evaluates the vector/matrix product between
// those digit polynomials and a standard-domain GGSW ciphertext:
//
//   out <- accumulator + Decomp(glwe) * ggsw
//
// in (Z / 2^64 Z)[X] / (X^N + 1).  This is deliberately the exact
// coefficient-domain rung; a transform-domain implementation can replace the
// O(N^2) convolution only after matching this shader bit for bit.

struct Metadata {
    degree: u32,
    glwe_size: u32,
    base_log: u32,
    level_count: u32,
};

@group(0) @binding(0) var<uniform> params: Metadata;
@group(0) @binding(1) var<storage, read> glwe: array<u32>;
@group(0) @binding(2) var<storage, read> ggsw: array<u32>;
@group(0) @binding(3) var<storage, read> accumulator: array<u32>;
@group(0) @binding(4) var<storage, read_write> decomposed: array<u32>;
@group(0) @binding(5) var<storage, read_write> output: array<u32>;

fn load64(buffer_index: u32, which: u32) -> vec2<u32> {
    let limb = buffer_index * 2u;
    if (which == 0u) {
        return vec2<u32>(glwe[limb], glwe[limb + 1u]);
    }
    if (which == 1u) {
        return vec2<u32>(ggsw[limb], ggsw[limb + 1u]);
    }
    if (which == 2u) {
        return vec2<u32>(accumulator[limb], accumulator[limb + 1u]);
    }
    return vec2<u32>(decomposed[limb], decomposed[limb + 1u]);
}

fn store_decomposed(coefficient: u32, value: vec2<u32>) {
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

fn or64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    return vec2<u32>(a.x | b.x, a.y | b.y);
}

fn and64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    return vec2<u32>(a.x & b.x, a.y & b.y);
}

// Logical shifts with explicit 32-bit branches avoid relying on WebGPU's
// modulo-shift behavior at the limb boundary.
fn shr64(a: vec2<u32>, shift: u32) -> vec2<u32> {
    if (shift == 0u) {
        return a;
    }
    if (shift < 32u) {
        return vec2<u32>(a.x >> shift | a.y << (32u - shift), a.y >> shift);
    }
    if (shift == 32u) {
        return vec2<u32>(a.y, 0u);
    }
    return vec2<u32>(a.y >> (shift - 32u), 0u);
}

fn shl64(a: vec2<u32>, shift: u32) -> vec2<u32> {
    if (shift == 0u) {
        return a;
    }
    if (shift < 32u) {
        return vec2<u32>(a.x << shift, a.y << shift | a.x >> (32u - shift));
    }
    if (shift == 32u) {
        return vec2<u32>(0u, a.x);
    }
    return vec2<u32>(0u, a.x << (shift - 32u));
}

fn arithmetic_shr64(a: vec2<u32>, shift: u32) -> vec2<u32> {
    if (shift == 0u) {
        return a;
    }
    let sign_fill = select(0u, 0xffffffffu, (a.y & 0x80000000u) != 0u);
    if (shift < 32u) {
        return vec2<u32>(
            a.x >> shift | a.y << (32u - shift),
            a.y >> shift | sign_fill << (32u - shift),
        );
    }
    if (shift == 32u) {
        return vec2<u32>(a.y, sign_fill);
    }
    return vec2<u32>(a.y >> (shift - 32u) | sign_fill << (64u - shift), sign_fill);
}

fn low_mask64(bits: u32) -> vec2<u32> {
    if (bits < 32u) {
        return vec2<u32>((1u << bits) - 1u, 0u);
    }
    if (bits == 32u) {
        return vec2<u32>(0xffffffffu, 0u);
    }
    return vec2<u32>(0xffffffffu, (1u << (bits - 32u)) - 1u);
}

// Exact 32x32 -> 64 multiply using 16-bit partial products.
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

fn mul64_low(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let low = mul32_wide(a.x, b.x);
    let hi = low.y + a.x * b.y + a.y * b.x;
    return vec2<u32>(low.x, hi);
}

// tfhe-rs SignedDecomposer::init_decomposer_state, specialized to native u64.
fn init_decomposer_state(input: vec2<u32>) -> vec2<u32> {
    let represented_bits = params.base_log * params.level_count;
    let non_represented_bits = 64u - represented_bits;
    var state = shr64(input, non_represented_bits - 1u);
    let rounding_bit = state.x & 1u;
    state = add64(state, vec2<u32>(1u, 0u));
    state = shr64(state, 1u);
    state = and64(state, low_mask64(represented_bits));

    // Same balanced-rounding bit trick as tfhe-rs:
    // ((state - 1 | rounding << (r-1)) & state) >> (r-1).
    let shifted_rounding = shl64(vec2<u32>(rounding_bit, 0u), represented_bits - 1u);
    let balance_source = and64(
        or64(sub64(state, vec2<u32>(1u, 0u)), shifted_rounding),
        state,
    );
    let need_balance = shr64(balance_source, represented_bits - 1u).x & 1u;
    return sub64(state, shl64(vec2<u32>(need_balance, 0u), represented_bits));
}

@compute @workgroup_size(64)
fn decompose(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let glwe_coefficients = params.glwe_size * params.degree;
    if (coefficient >= glwe_coefficients) {
        return;
    }

    var state = init_decomposer_state(load64(coefficient, 0u));
    for (var level = 0u; level < params.level_count; level = level + 1u) {
        // Inline the one-level routine here so both limbs of the next state stay
        // available (vec3 only carries the digit and next low limb).
        let digit_mask = (1u << params.base_log) - 1u;
        let raw_digit = state.x & digit_mask;
        state = arithmetic_shr64(state, params.base_log);
        let carry = (((raw_digit - 1u) | state.x) & raw_digit) >> (params.base_log - 1u);
        state = add64(state, vec2<u32>(carry, 0u));
        let digit = sub64(
            vec2<u32>(raw_digit, 0u),
            shl64(vec2<u32>(carry, 0u), params.base_log),
        );
        store_decomposed(level * glwe_coefficients + coefficient, digit);
    }
}

@compute @workgroup_size(64)
fn external_product(@builtin(global_invocation_id) gid: vec3<u32>) {
    let output_coefficient = gid.x;
    let output_coefficients = params.glwe_size * params.degree;
    if (output_coefficient >= output_coefficients) {
        return;
    }

    let output_polynomial = output_coefficient / params.degree;
    let out_index = output_coefficient % params.degree;
    let glwe_coefficients = params.glwe_size * params.degree;
    var value = load64(output_coefficient, 2u);

    for (var level = 0u; level < params.level_count; level = level + 1u) {
        for (var row = 0u; row < params.glwe_size; row = row + 1u) {
            let digit_base = level * glwe_coefficients + row * params.degree;
            let ggsw_poly =
                ((level * params.glwe_size + row) * params.glwe_size + output_polynomial)
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
                    load64(digit_base + lhs_index, 3u),
                    load64(ggsw_poly + rhs_index, 1u),
                );
                if (positive) {
                    value = add64(value, term);
                } else {
                    value = sub64(value, term);
                }
            }
        }
    }

    let limb = output_coefficient * 2u;
    output[limb] = value.x;
    output[limb + 1u] = value.y;
}

// Bit-exact batched torus polynomial multiply-accumulate.
//
// out = accumulator + sum_t lhs_t * rhs_t
// in (Z / 2^64 Z)[X] / (X^N + 1).
//
// WebGPU core does not require shader u64.  Each coefficient is stored as
// vec2<u32>(lo, hi).  mul64_low uses 16-bit partial products and retains exactly
// the low 64 bits.  All add/sub operations wrap naturally in u32 limbs.

struct Metadata {
    degree: u32,
    products: u32,
    _pad0: u32,
    _pad1: u32,
};

@group(0) @binding(0) var<uniform> params: Metadata;
@group(0) @binding(1) var<storage, read> lhs: array<u32>;
@group(0) @binding(2) var<storage, read> rhs: array<u32>;
@group(0) @binding(3) var<storage, read> accumulator: array<u32>;
@group(0) @binding(4) var<storage, read_write> output: array<u32>;

fn load_lhs(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(lhs[limb], lhs[limb + 1u]);
}

fn load_rhs(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(rhs[limb], rhs[limb + 1u]);
}

fn load_accumulator(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(accumulator[limb], accumulator[limb + 1u]);
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

// Low 64 bits of a 64x64 product.  The high halves of the cross-products land
// above bit 63 and are intentionally discarded modulo 2^64.
fn mul64_low(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let low = mul32_wide(a.x, b.x);
    let hi = low.y + a.x * b.y + a.y * b.x;
    return vec2<u32>(low.x, hi);
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let out_index = gid.x;
    if (out_index >= params.degree) {
        return;
    }

    var value = load_accumulator(out_index);
    for (var product = 0u; product < params.products; product = product + 1u) {
        let base = product * params.degree;
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
                load_lhs(base + lhs_index),
                load_rhs(base + rhs_index),
            );
            if (positive) {
                value = add64(value, term);
            } else {
                value = sub64(value, term);
            }
        }
    }

    let limb = out_index * 2u;
    output[limb] = value.x;
    output[limb + 1u] = value.y;
}

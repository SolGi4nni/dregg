// Exact degree-zero GLWE sample extraction fused with native-torus LWE key switch.
// The final blind-rotation accumulator remains on-device; only the post-key-switch
// LWE ciphertext is copied back.

struct Metadata {
    degree: u32,
    glwe_size: u32,
    output_lwe_size: u32,
    base_log: u32,
    level_count: u32,
    input_buffer: u32,
    _pad0: u32,
    _pad1: u32,
};

@group(0) @binding(0) var<uniform> params: Metadata;
@group(0) @binding(1) var<storage, read> accumulator_a: array<u32>;
@group(0) @binding(2) var<storage, read> accumulator_b: array<u32>;
@group(0) @binding(3) var<storage, read> keyswitch_key: array<u32>;
@group(0) @binding(4) var<storage, read_write> output_lwe: array<u32>;

fn load_acc64(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    if (params.input_buffer == 0u) {
        return vec2<u32>(accumulator_a[limb], accumulator_a[limb + 1u]);
    }
    return vec2<u32>(accumulator_b[limb], accumulator_b[limb + 1u]);
}

fn load_batch_acc64(batch: u32, coefficient: u32) -> vec2<u32> {
    let accumulator_coefficients = params.glwe_size * params.degree;
    let limb = (batch * accumulator_coefficients + coefficient) * 2u;
    if (params.input_buffer == 0u) {
        return vec2<u32>(accumulator_a[limb], accumulator_a[limb + 1u]);
    }
    return vec2<u32>(accumulator_b[limb], accumulator_b[limb + 1u]);
}

fn load_ksk64(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(keyswitch_key[limb], keyswitch_key[limb + 1u]);
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

fn extracted_mask_coefficient(index: u32) -> vec2<u32> {
    let local = index % params.degree;
    let polynomial = index / params.degree;
    if (local == 0u) {
        return load_acc64(polynomial * params.degree);
    }
    return neg64(load_acc64(polynomial * params.degree + params.degree - local));
}

fn extracted_batch_mask_coefficient(batch: u32, index: u32) -> vec2<u32> {
    let local = index % params.degree;
    let polynomial = index / params.degree;
    if (local == 0u) {
        return load_batch_acc64(batch, polynomial * params.degree);
    }
    return neg64(load_batch_acc64(
        batch,
        polynomial * params.degree + params.degree - local,
    ));
}

// Degree-zero GLWE sample extraction without the following key switch.  This
// is the terminal step for tfhe-rs's KS->PBS order: the caller has already
// switched the input from the large LWE key to the BSK input key, and the PBS
// output must remain under the large (GLWE-equivalent) key.
@compute @workgroup_size(64)
fn extract_only(@builtin(global_invocation_id) gid: vec3<u32>) {
    let output_index = gid.x;
    let input_dimension = (params.glwe_size - 1u) * params.degree;
    if (output_index > input_dimension) { return; }

    var value = vec2<u32>(0u, 0u);
    if (output_index == input_dimension) {
        value = load_acc64((params.glwe_size - 1u) * params.degree);
    } else {
        value = extracted_mask_coefficient(output_index);
    }

    let limb = output_index * 2u;
    output_lwe[limb] = value.x;
    output_lwe[limb + 1u] = value.y;
}


@compute @workgroup_size(64)
fn extract_only_batch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let output_index = gid.x;
    let batch = gid.y;
    let input_dimension = (params.glwe_size - 1u) * params.degree;
    if (output_index > input_dimension) { return; }

    var value = vec2<u32>(0u, 0u);
    if (output_index == input_dimension) {
        value = load_batch_acc64(batch, (params.glwe_size - 1u) * params.degree);
    } else {
        value = extracted_batch_mask_coefficient(batch, output_index);
    }

    let output_lwe_size = input_dimension + 1u;
    let limb = (batch * output_lwe_size + output_index) * 2u;
    output_lwe[limb] = value.x;
    output_lwe[limb + 1u] = value.y;
}

@compute @workgroup_size(64)
fn extract_and_keyswitch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let output_index = gid.x;
    if (output_index >= params.output_lwe_size) { return; }
    let input_dimension = (params.glwe_size - 1u) * params.degree;
    var value = vec2<u32>(0u, 0u);
    if (output_index + 1u == params.output_lwe_size) {
        value = load_acc64((params.glwe_size - 1u) * params.degree);
    }

    for (var input_index = 0u; input_index < input_dimension; input_index = input_index + 1u) {
        var state = init_decomposer_state(extracted_mask_coefficient(input_index));
        for (var level = 0u; level < params.level_count; level = level + 1u) {
            let digit_mask = (1u << params.base_log) - 1u;
            let raw_digit = state.x & digit_mask;
            state = arithmetic_shr64(state, params.base_log);
            let carry = (((raw_digit - 1u) | state.x) & raw_digit)
                >> (params.base_log - 1u);
            state = add64(state, vec2<u32>(carry, 0u));
            let digit = sub64(
                vec2<u32>(raw_digit, 0u),
                shl64(vec2<u32>(carry, 0u), params.base_log),
            );
            let key_index = ((input_index * params.level_count + level)
                * params.output_lwe_size) + output_index;
            value = sub64(value, mul64_low(digit, load_ksk64(key_index)));
        }
    }

    let limb = output_index * 2u;
    output_lwe[limb] = value.x;
    output_lwe[limb + 1u] = value.y;
}

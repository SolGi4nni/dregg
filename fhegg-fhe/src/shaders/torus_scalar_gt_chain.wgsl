// Large-key radix-block packing, exact native-torus key switch, and tfhe-rs
// centered-binary modulus switching for the resident scalar-comparison chain.
// All torus words are represented as little-endian pairs of u32 limbs.

struct Metadata {
    input_lwe_size: u32,
    output_lwe_size: u32,
    base_log: u32,
    level_count: u32,
    log_modulus: u32,
    digit_block: u32,
    include_state: u32,
    digit_scale_log: u32,
};

@group(0) @binding(0) var<uniform> params: Metadata;
@group(0) @binding(1) var<storage, read> state_lwe: array<u32>;
@group(0) @binding(2) var<storage, read> digit_lwes: array<u32>;
@group(0) @binding(3) var<storage, read> keyswitch_key: array<u32>;
@group(0) @binding(4) var<storage, read_write> small_lwe: array<u32>;
@group(0) @binding(5) var<storage, read_write> rotations: array<u32>;

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

fn signed_divide_by_two_toward_zero(a: vec2<u32>) -> vec2<u32> {
    if ((a.y & 0x80000000u) == 0u) {
        return shr64(a, 1u);
    }
    return neg64(shr64(neg64(a), 1u));
}

fn low_mask64(bits: u32) -> vec2<u32> {
    if (bits < 32u) { return vec2<u32>((1u << bits) - 1u, 0u); }
    if (bits == 32u) { return vec2<u32>(0xffffffffu, 0u); }
    return vec2<u32>(0xffffffffu, (1u << (bits - 32u)) - 1u);
}

fn pow2_64(bit: u32) -> vec2<u32> {
    if (bit < 32u) { return vec2<u32>(1u << bit, 0u); }
    return vec2<u32>(0u, 1u << (bit - 32u));
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

fn load_state(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(state_lwe[limb], state_lwe[limb + 1u]);
}

fn load_digit(coefficient: u32) -> vec2<u32> {
    let digit_coefficient = params.digit_block * params.input_lwe_size + coefficient;
    let limb = digit_coefficient * 2u;
    return vec2<u32>(digit_lwes[limb], digit_lwes[limb + 1u]);
}

fn load_state_at(block: u32, coefficient: u32) -> vec2<u32> {
    let limb = (block * params.input_lwe_size + coefficient) * 2u;
    return vec2<u32>(state_lwe[limb], state_lwe[limb + 1u]);
}

fn load_digit_at(block: u32, coefficient: u32) -> vec2<u32> {
    let limb = (block * params.input_lwe_size + coefficient) * 2u;
    return vec2<u32>(digit_lwes[limb], digit_lwes[limb + 1u]);
}

fn load_small_at(block: u32, coefficient: u32) -> vec2<u32> {
    let limb = (block * params.output_lwe_size + coefficient) * 2u;
    return vec2<u32>(small_lwe[limb], small_lwe[limb + 1u]);
}

fn store_small_at(block: u32, coefficient: u32, value: vec2<u32>) {
    let limb = (block * params.output_lwe_size + coefficient) * 2u;
    small_lwe[limb] = value.x;
    small_lwe[limb + 1u] = value.y;
}

fn load_packed_batch_input(batch: u32, coefficient: u32) -> vec2<u32> {
    let digit = shl64(
        load_digit_at(params.digit_block + batch, coefficient),
        params.digit_scale_log,
    );
    if (params.include_state == 0u) { return digit; }
    return add64(load_state_at(0u, coefficient), digit);
}

fn load_input(coefficient: u32) -> vec2<u32> {
    let digit = shl64(load_digit(coefficient), params.digit_scale_log);
    if (params.include_state == 0u) {
        // The first digit is compared directly, without a predecessor state.
        return load_digit(coefficient);
    }
    return add64(load_state(coefficient), digit);
}

fn load_ksk(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(keyswitch_key[limb], keyswitch_key[limb + 1u]);
}

fn load_small(coefficient: u32) -> vec2<u32> {
    let limb = coefficient * 2u;
    return vec2<u32>(small_lwe[limb], small_lwe[limb + 1u]);
}

// Add two large-key LWEs coefficient-wise.  The fused comparison/select path
// evaluates the two mutually-exclusive masks
//
//   predicate * when + (1 - predicate) * otherwise
//
// with one PBS per mask.  Keeping this final addition on device means the
// encrypted predicate never crosses the host boundary between comparison and
// selection.  Binding 4 is deliberately reused as the output: it is sized for
// a large LWE by that path, while the KS/MS entries only address its small-LWE
// prefix.
@compute @workgroup_size(64)
fn add_large_lwes(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    if (coefficient >= params.input_lwe_size) { return; }
    let value = add64(load_state(coefficient), load_digit(coefficient));
    let limb = coefficient * 2u;
    small_lwe[limb] = value.x;
    small_lwe[limb + 1u] = value.y;
}

// Batched form used after the resident comparison. Bindings 1 and 2 carry
// contiguous true-mask and false-mask LWEs respectively; binding 4 receives
// one contiguous selected radix ciphertext.
@compute @workgroup_size(64)
fn add_large_lwe_pairs(@builtin(global_invocation_id) gid: vec3<u32>) {
    let coefficient = gid.x;
    let block = gid.y;
    if (coefficient >= params.input_lwe_size) { return; }
    let value = add64(
        load_state_at(block, coefficient),
        load_digit_at(params.digit_block + block, coefficient),
    );
    let limb = (block * params.input_lwe_size + coefficient) * 2u;
    small_lwe[limb] = value.x;
    small_lwe[limb + 1u] = value.y;
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

fn modulus_switch(value: vec2<u32>) -> u32 {
    let shift = 64u - params.log_modulus;
    return shr64(add64(value, pow2_64(shift - 1u)), shift).x;
}

@compute @workgroup_size(64)
fn keyswitch_packed_input(@builtin(global_invocation_id) gid: vec3<u32>) {
    let output_index = gid.x;
    if (output_index >= params.output_lwe_size) { return; }
    let input_dimension = params.input_lwe_size - 1u;
    var value = vec2<u32>(0u, 0u);
    if (output_index + 1u == params.output_lwe_size) {
        value = load_input(input_dimension);
    }

    for (var input_index = 0u; input_index < input_dimension; input_index = input_index + 1u) {
        var state = init_decomposer_state(load_input(input_index));
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
            value = sub64(value, mul64_low(digit, load_ksk(key_index)));
        }
    }

    let limb = output_index * 2u;
    small_lwe[limb] = value.x;
    small_lwe[limb + 1u] = value.y;
}


// Key-switch every independent masked selection digit in parallel. `gid.y`
// is the mask lane; each lane packs the shared encrypted predicate with one
// uploaded branch digit and writes a disjoint small-key LWE.
@compute @workgroup_size(64)
fn keyswitch_packed_inputs_batch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let output_index = gid.x;
    let batch = gid.y;
    if (output_index >= params.output_lwe_size) { return; }
    let input_dimension = params.input_lwe_size - 1u;
    var value = vec2<u32>(0u, 0u);
    if (output_index + 1u == params.output_lwe_size) {
        value = load_packed_batch_input(batch, input_dimension);
    }

    for (var input_index = 0u; input_index < input_dimension; input_index = input_index + 1u) {
        var state = init_decomposer_state(load_packed_batch_input(batch, input_index));
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
            value = sub64(value, mul64_low(digit, load_ksk(key_index)));
        }
    }
    store_small_at(batch, output_index, value);
}

// Reproduce tfhe-rs's centered_binary_ms_body_correction_to_add exactly.
// Mask rotations are independent. The body invocation performs the bounded
// 918-element correction reduction and writes the corrected body rotation.
@compute @workgroup_size(64)
fn centered_modulus_switch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    let mask_dimension = params.output_lwe_size - 1u;
    if (index < mask_dimension) {
        rotations[index] = modulus_switch(load_small(index));
        return;
    }
    if (index != mask_dimension) { return; }

    let shift = 64u - params.log_modulus;
    var sum_half_round_errors = vec2<u32>(0u, 0u);
    var sum_halving_errors_doubled = vec2<u32>(0u, 0u);
    for (var mask_index = 0u; mask_index < mask_dimension; mask_index = mask_index + 1u) {
        let mask = load_small(mask_index);
        let rounded = shl64(vec2<u32>(modulus_switch(mask), 0u), shift);
        let error = sub64(rounded, mask);
        let half_error = signed_divide_by_two_toward_zero(error);
        let halving_error_doubled = sub64(shl64(half_error, 1u), error);
        sum_half_round_errors = add64(sum_half_round_errors, half_error);
        sum_halving_errors_doubled =
            add64(sum_halving_errors_doubled, halving_error_doubled);
    }
    let sum_halving_errors =
        signed_divide_by_two_toward_zero(sum_halving_errors_doubled);
    sum_half_round_errors = sub64(sum_half_round_errors, sum_halving_errors);
    let half_case = pow2_64(shift - 1u);
    let correction = sub64(sum_half_round_errors, half_case);
    // The blind-rotation convention is X^(-b) for the body and X^(a_i)
    // for each mask coefficient.  Keep the sign conversion on device too;
    // merely storing the modulus-switched body here would select the inverse
    // LUT bucket for every non-zero body rotation.
    let switched_body = modulus_switch(add64(load_small(mask_dimension), correction));
    let rotation_modulus = 1u << params.log_modulus;
    rotations[mask_dimension] = (rotation_modulus - switched_body) & (rotation_modulus - 1u);
}


@compute @workgroup_size(64)
fn centered_modulus_switch_batch(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    let batch = gid.y;
    let mask_dimension = params.output_lwe_size - 1u;
    let schedule_base = batch * params.output_lwe_size;
    if (index < mask_dimension) {
        rotations[schedule_base + index] = modulus_switch(load_small_at(batch, index));
        return;
    }
    if (index != mask_dimension) { return; }

    let shift = 64u - params.log_modulus;
    var sum_half_round_errors = vec2<u32>(0u, 0u);
    var sum_halving_errors_doubled = vec2<u32>(0u, 0u);
    for (var mask_index = 0u; mask_index < mask_dimension; mask_index = mask_index + 1u) {
        let mask = load_small_at(batch, mask_index);
        let rounded = shl64(vec2<u32>(modulus_switch(mask), 0u), shift);
        let error = sub64(rounded, mask);
        let half_error = signed_divide_by_two_toward_zero(error);
        let halving_error_doubled = sub64(shl64(half_error, 1u), error);
        sum_half_round_errors = add64(sum_half_round_errors, half_error);
        sum_halving_errors_doubled =
            add64(sum_halving_errors_doubled, halving_error_doubled);
    }
    let sum_halving_errors =
        signed_divide_by_two_toward_zero(sum_halving_errors_doubled);
    sum_half_round_errors = sub64(sum_half_round_errors, sum_halving_errors);
    let correction = sub64(sum_half_round_errors, pow2_64(shift - 1u));
    let switched_body = modulus_switch(add64(load_small_at(batch, mask_dimension), correction));
    let rotation_modulus = 1u << params.log_modulus;
    rotations[schedule_base + mask_dimension] =
        (rotation_modulus - switched_body) & (rotation_modulus - 1u);
}

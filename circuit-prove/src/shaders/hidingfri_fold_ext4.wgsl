// Exact Plonky3 TwoAdicFriFolding for BabyBear^4, max deployed arity 8.
// Inputs/outputs use canonical u32 coefficients. Arithmetic is performed in
// BabyBear Montgomery form with the same 16-bit-split reduction as p3-monty-31.

const P: u32 = 0x78000001u;
const MU: u32 = 0x88000001u;
const R2: u32 = 1172168163u;
const W_MONT: u32 = 939524073u; // montgomery(11), X^4 = 11

@group(0) @binding(0) var<storage, read> input_values: array<vec4<u32>>;
@group(0) @binding(1) var<storage, read> initial_halve_inv_powers: array<u32>;
@group(0) @binding(2) var<storage, read_write> output_values: array<vec4<u32>>;
// [input_len, log_arity, beta.c0, beta.c1, beta.c2, beta.c3]
@group(0) @binding(3) var<storage, read> params: array<u32>;

fn mul64(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xffffu;
    let a1 = a >> 16u;
    let b0 = b & 0xffffu;
    let b1 = b >> 16u;
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
}

fn mmul(a: u32, b: u32) -> u32 {
    let ab = mul64(a, b);
    let t = ab.x * MU;
    let tp = mul64(t, P);
    var r = ab.y - tp.y;
    if (ab.y < tp.y) {
        r += P;
    }
    return r;
}

fn addp(a: u32, b: u32) -> u32 {
    let sum = a + b;
    return select(sum, sum - P, sum >= P);
}

fn subp(a: u32, b: u32) -> u32 {
    var result = a - b;
    if (a < b) {
        result += P;
    }
    return result;
}

fn halve(a: u32) -> u32 {
    return select(a >> 1u, (a >> 1u) + 0x3c000001u, (a & 1u) != 0u);
}

fn to_mont(value: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(
        mmul(value.x, R2),
        mmul(value.y, R2),
        mmul(value.z, R2),
        mmul(value.w, R2),
    );
}

fn from_mont(value: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(
        mmul(value.x, 1u),
        mmul(value.y, 1u),
        mmul(value.z, 1u),
        mmul(value.w, 1u),
    );
}

fn ext_add(a: vec4<u32>, b: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(addp(a.x, b.x), addp(a.y, b.y), addp(a.z, b.z), addp(a.w, b.w));
}

fn ext_sub(a: vec4<u32>, b: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(subp(a.x, b.x), subp(a.y, b.y), subp(a.z, b.z), subp(a.w, b.w));
}

fn ext_halve(a: vec4<u32>) -> vec4<u32> {
    return vec4<u32>(halve(a.x), halve(a.y), halve(a.z), halve(a.w));
}

fn ext_base_mul(a: vec4<u32>, b: u32) -> vec4<u32> {
    return vec4<u32>(mmul(a.x, b), mmul(a.y, b), mmul(a.z, b), mmul(a.w, b));
}

fn ext_mul(a: vec4<u32>, b: vec4<u32>) -> vec4<u32> {
    let c0 = addp(
        mmul(a.x, b.x),
        mmul(W_MONT, addp(addp(mmul(a.y, b.w), mmul(a.z, b.z)), mmul(a.w, b.y))),
    );
    let c1 = addp(
        addp(mmul(a.x, b.y), mmul(a.y, b.x)),
        mmul(W_MONT, addp(mmul(a.z, b.w), mmul(a.w, b.z))),
    );
    let c2 = addp(
        addp(addp(mmul(a.x, b.z), mmul(a.y, b.y)), mmul(a.z, b.x)),
        mmul(W_MONT, mmul(a.w, b.w)),
    );
    let c3 = addp(
        addp(mmul(a.x, b.w), mmul(a.y, b.z)),
        addp(mmul(a.z, b.y), mmul(a.w, b.x)),
    );
    return vec4<u32>(c0, c1, c2, c3);
}

@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let input_len = params[0];
    let log_arity = params[1];
    let arity = 1u << log_arity;
    let output_len = input_len >> log_arity;
    if (gid.x >= output_len) {
        return;
    }

    var values: array<vec4<u32>, 8>;
    let input_base = gid.x * arity;
    for (var i = 0u; i < arity; i++) {
        values[i] = to_mont(input_values[input_base + i]);
    }
    var beta = to_mont(vec4<u32>(params[2], params[3], params[4], params[5]));

    for (var step = 0u; step < log_arity; step++) {
        let local_height = arity >> (step + 1u);
        for (var j = 0u; j < local_height; j++) {
            let global_j = gid.x * local_height + j;
            var halve_inv_power = mmul(
                initial_halve_inv_powers[global_j << step],
                R2,
            );
            for (var power_step = 0u; power_step < step; power_step++) {
                halve_inv_power = addp(
                    mmul(halve_inv_power, halve_inv_power),
                    mmul(halve_inv_power, halve_inv_power),
                );
            }
            let lo = values[j << 1u];
            let hi = values[(j << 1u) + 1u];
            values[j] = ext_add(
                ext_halve(ext_add(lo, hi)),
                ext_base_mul(ext_mul(ext_sub(lo, hi), beta), halve_inv_power),
            );
        }
        beta = ext_mul(beta, beta);
    }

    output_values[gid.x] = from_mont(values[0]);
}

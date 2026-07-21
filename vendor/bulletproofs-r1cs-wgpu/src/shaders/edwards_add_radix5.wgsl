// Exact extended-Edwards addition modulo p = 2^255 - 19.
// Historical filename retained so the already-qualified pair-add include path
// does not churn; the implementation below is now radix-2^8.
//
// Field elements use 32 little-endian radix-2^8 limbs. A convolution
// coefficient is bounded by 32 * 255^2 = 2,080,800, and the pseudo-Mersenne
// fold `2^256 = 38 (mod 2^255-19)` remains below 80 million. Every arithmetic
// operation is therefore exact in u32, while multiplication needs only 1,024
// limb products instead of the earlier radix-2^5 kernel's 2,601.

struct Params {
    pair_count: u32,
    _pad0: u32,
    _pad1: u32,
    _pad2: u32,
};

struct Fe {
    limb: array<u32, 32>,
};

struct ExtPoint {
    x: Fe,
    y: Fe,
    z: Fe,
    t: Fe,
};

@group(0) @binding(0) var<uniform> params: Params;
// `[pair][left/right][X/Y/Z/T][32 canonical bytes]`, one byte per u32.
@group(0) @binding(1) var<storage, read> coordinates: array<u32>;
// Canonical bytes of Edwards 2*d, one byte per u32.
@group(0) @binding(2) var<storage, read> constants: array<u32>;
// `[pair][X/Y/Z/T][32 canonical bytes]`, one byte per u32.
@group(0) @binding(3) var<storage, read_write> sums: array<u32>;
// Canonical scalar bytes, `[term][32 bytes]`, one byte per u32.  Only the
// verifier-useful `scale_terms` entry point reads this binding.
@group(0) @binding(4) var<storage, read> scalar_bytes: array<u32>;

fn p_digit(index: u32) -> u32 {
    // 2^255 - 19 in radix 2^8 is [237, 255, ..., 255, 127].
    if (index == 0u) {
        return 237u;
    }
    return select(255u, 127u, index == 31u);
}

fn fe_ge_p(a: Fe) -> bool {
    var cursor = 32u;
    var decided = false;
    var result = true;
    loop {
        if (cursor == 0u) {
            break;
        }
        cursor = cursor - 1u;
        if (!decided) {
            let p = p_digit(cursor);
            if (a.limb[cursor] > p) {
                result = true;
                decided = true;
            } else if (a.limb[cursor] < p) {
                result = false;
                decided = true;
            }
        }
    }
    return result;
}

fn fe_sub_p(a: Fe) -> Fe {
    var out: Fe;
    var borrow = 0u;
    for (var i = 0u; i < 32u; i = i + 1u) {
        let subtrahend = p_digit(i) + borrow;
        if (a.limb[i] < subtrahend) {
            out.limb[i] = a.limb[i] + 256u - subtrahend;
            borrow = 1u;
        } else {
            out.limb[i] = a.limb[i] - subtrahend;
            borrow = 0u;
        }
    }
    return out;
}

fn fe_canonical(input: Fe) -> Fe {
    var out = input;
    // Five fixed carry laps cover the convolution bound above. The top carry
    // folds by 2^256 = 38 modulo p.
    for (var round = 0u; round < 5u; round = round + 1u) {
        for (var i = 0u; i < 32u; i = i + 1u) {
            let carry = out.limb[i] >> 8u;
            out.limb[i] = out.limb[i] & 255u;
            if (i < 31u) {
                out.limb[i + 1u] = out.limb[i + 1u] + carry;
            } else {
                out.limb[0] = out.limb[0] + carry * 38u;
            }
        }
    }
    // The carry bound leaves less than 2p.  A second fixed subtraction is a
    // defensive canonicalization tooth and is a no-op for already-reduced data.
    if (fe_ge_p(out)) {
        out = fe_sub_p(out);
    }
    if (fe_ge_p(out)) {
        out = fe_sub_p(out);
    }
    return out;
}

fn fe_add(a: Fe, b: Fe) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 32u; i = i + 1u) {
        out.limb[i] = a.limb[i] + b.limb[i];
    }
    return fe_canonical(out);
}

fn fe_is_zero(a: Fe) -> bool {
    let reduced = fe_canonical(a);
    var any = 0u;
    for (var i = 0u; i < 32u; i = i + 1u) {
        any = any | reduced.limb[i];
    }
    return any == 0u;
}

fn fe_neg(a: Fe) -> Fe {
    let reduced = fe_canonical(a);
    if (fe_is_zero(reduced)) {
        var zero: Fe;
        return zero;
    }
    var out: Fe;
    var borrow = 0u;
    for (var i = 0u; i < 32u; i = i + 1u) {
        let subtrahend = reduced.limb[i] + borrow;
        let p = p_digit(i);
        if (p < subtrahend) {
            out.limb[i] = p + 256u - subtrahend;
            borrow = 1u;
        } else {
            out.limb[i] = p - subtrahend;
            borrow = 0u;
        }
    }
    return out;
}

fn fe_sub(a: Fe, b: Fe) -> Fe {
    return fe_add(a, fe_neg(b));
}

fn fe_mul(a: Fe, b: Fe) -> Fe {
    var wide: array<u32, 63>;
    for (var i = 0u; i < 32u; i = i + 1u) {
        for (var j = 0u; j < 32u; j = j + 1u) {
            wide[i + j] = wide[i + j] + a.limb[i] * b.limb[j];
        }
    }
    var cursor = 63u;
    loop {
        if (cursor == 32u) {
            break;
        }
        cursor = cursor - 1u;
        wide[cursor - 32u] = wide[cursor - 32u] + wide[cursor] * 38u;
    }
    var out: Fe;
    for (var i = 0u; i < 32u; i = i + 1u) {
        out.limb[i] = wide[i];
    }
    return fe_canonical(out);
}

fn fe_from_coordinates(base: u32) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 32u; i = i + 1u) {
        out.limb[i] = coordinates[base + i] & 255u;
    }
    return out;
}

fn fe_from_constants(base: u32) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 32u; i = i + 1u) {
        out.limb[i] = constants[base + i] & 255u;
    }
    return out;
}

fn point_from_constants(base: u32) -> ExtPoint {
    var point: ExtPoint;
    point.x = fe_from_constants(base);
    point.y = fe_from_constants(base + 32u);
    point.z = fe_from_constants(base + 64u);
    point.t = fe_from_constants(base + 96u);
    return point;
}

fn fe_to_sums(value: Fe, base: u32) {
    let reduced = fe_canonical(value);
    for (var i = 0u; i < 32u; i = i + 1u) {
        sums[base + i] = reduced.limb[i];
    }
}

fn load_point(base: u32) -> ExtPoint {
    var point: ExtPoint;
    point.x = fe_from_coordinates(base);
    point.y = fe_from_coordinates(base + 32u);
    point.z = fe_from_coordinates(base + 64u);
    point.t = fe_from_coordinates(base + 96u);
    return point;
}

fn store_point(point: ExtPoint, base: u32) {
    fe_to_sums(point.x, base);
    fe_to_sums(point.y, base + 32u);
    fe_to_sums(point.z, base + 64u);
    fe_to_sums(point.t, base + 96u);
}

fn add_points(left: ExtPoint, right: ExtPoint, d2: Fe) -> ExtPoint {
    // Complete extended-coordinate addition for a = -1.
    let a = fe_mul(fe_sub(left.y, left.x), fe_sub(right.y, right.x));
    let b = fe_mul(fe_add(left.y, left.x), fe_add(right.y, right.x));
    let c = fe_mul(fe_mul(left.t, right.t), d2);
    let d = fe_add(fe_mul(left.z, right.z), fe_mul(left.z, right.z));
    let e = fe_sub(b, a);
    let f = fe_sub(d, c);
    let g = fe_add(d, c);
    let h = fe_add(b, a);
    var sum: ExtPoint;
    sum.x = fe_mul(e, f);
    sum.y = fe_mul(g, h);
    sum.t = fe_mul(e, h);
    sum.z = fe_mul(f, g);
    return sum;
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let pair = gid.x;
    if (pair >= params.pair_count) {
        return;
    }
    let input_base = pair * 256u;
    let output_base = pair * 128u;
    let left = load_point(input_base);
    let right = load_point(input_base + 128u);
    let result = add_points(left, right, fe_from_constants(0u));
    store_point(result, output_base);
}

// Variable-time bit buckets for PUBLIC verifier scalars. Each of 256
// invocations accumulates all points whose scalar has its public bit set.
// This removes every per-term doubling from the device work. Witness-derived
// prover scalars must not use this branch-bearing entry point.
@compute @workgroup_size(64)
fn bucket_bits(@builtin(global_invocation_id) gid: vec3<u32>) {
    let bit = gid.x;
    if (bit >= 256u) {
        return;
    }

    let d2 = fe_from_constants(0u);
    var accumulator = point_from_constants(32u);
    for (var term = 0u; term < params.pair_count; term = term + 1u) {
        let byte = scalar_bytes[term * 32u + (bit >> 3u)];
        if (((byte >> (bit & 7u)) & 1u) == 1u) {
            accumulator = add_points(accumulator, load_point(term * 128u), d2);
        }
    }
    store_point(accumulator, bit * 128u);
}

// Exact high-to-low Horner reduction: accumulator = 2*accumulator + bucket.
// Only one invocation owns the dependent chain; the expensive term scan above
// remains parallel across all 256 public scalar bits.
@compute @workgroup_size(1)
fn combine_bits(@builtin(global_invocation_id) gid: vec3<u32>) {
    if (gid.x != 0u) {
        return;
    }
    let d2 = fe_from_constants(0u);
    var accumulator = point_from_constants(32u);
    var cursor = 256u;
    loop {
        if (cursor == 0u) {
            break;
        }
        cursor = cursor - 1u;
        accumulator = add_points(accumulator, accumulator, d2);
        accumulator = add_points(accumulator, load_point(cursor * 128u), d2);
    }
    store_point(accumulator, 0u);
}

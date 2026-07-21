// Exact extended-Edwards addition modulo p = 2^255 - 19.
//
// Field elements use 51 little-endian radix-2^5 limbs.  The radix divides 255
// exactly, making the pseudo-Mersenne fold `2^255 = 19` direct.  A convolution
// coefficient is bounded by 51 * 31^2 = 49,011; after the single high fold it
// remains below one million, so every arithmetic operation is exact in u32.

struct Params {
    pair_count: u32,
    _pad0: u32,
    _pad1: u32,
    _pad2: u32,
};

struct Fe {
    limb: array<u32, 51>,
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

fn p_digit(index: u32) -> u32 {
    // 2^255 - 19 in radix 2^5 is [13, 31, ..., 31].
    return select(31u, 13u, index == 0u);
}

fn fe_ge_p(a: Fe) -> bool {
    var cursor = 51u;
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
    for (var i = 0u; i < 51u; i = i + 1u) {
        let subtrahend = p_digit(i) + borrow;
        if (a.limb[i] < subtrahend) {
            out.limb[i] = a.limb[i] + 32u - subtrahend;
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
    // Four fixed carry laps are more than the two required by the convolution
    // bounds above.  The top carry folds by 2^255 = 19.
    for (var round = 0u; round < 4u; round = round + 1u) {
        for (var i = 0u; i < 51u; i = i + 1u) {
            let carry = out.limb[i] >> 5u;
            out.limb[i] = out.limb[i] & 31u;
            if (i < 50u) {
                out.limb[i + 1u] = out.limb[i + 1u] + carry;
            } else {
                out.limb[0] = out.limb[0] + carry * 19u;
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
    for (var i = 0u; i < 51u; i = i + 1u) {
        out.limb[i] = a.limb[i] + b.limb[i];
    }
    return fe_canonical(out);
}

fn fe_is_zero(a: Fe) -> bool {
    let reduced = fe_canonical(a);
    var any = 0u;
    for (var i = 0u; i < 51u; i = i + 1u) {
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
    for (var i = 0u; i < 51u; i = i + 1u) {
        let subtrahend = reduced.limb[i] + borrow;
        let p = p_digit(i);
        if (p < subtrahend) {
            out.limb[i] = p + 32u - subtrahend;
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
    var wide: array<u32, 101>;
    for (var i = 0u; i < 51u; i = i + 1u) {
        for (var j = 0u; j < 51u; j = j + 1u) {
            wide[i + j] = wide[i + j] + a.limb[i] * b.limb[j];
        }
    }
    var cursor = 101u;
    loop {
        if (cursor == 51u) {
            break;
        }
        cursor = cursor - 1u;
        wide[cursor - 51u] = wide[cursor - 51u] + wide[cursor] * 19u;
    }
    var out: Fe;
    for (var i = 0u; i < 51u; i = i + 1u) {
        out.limb[i] = wide[i];
    }
    return fe_canonical(out);
}

fn fe_from_coordinates(base: u32) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 51u; i = i + 1u) {
        let bit_index = i * 5u;
        let byte_index = bit_index >> 3u;
        let shift = bit_index & 7u;
        var value = coordinates[base + byte_index] >> shift;
        if (shift > 3u) {
            value = value | (coordinates[base + byte_index + 1u] << (8u - shift));
        }
        out.limb[i] = value & 31u;
    }
    return out;
}

fn fe_from_constants(base: u32) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 51u; i = i + 1u) {
        let bit_index = i * 5u;
        let byte_index = bit_index >> 3u;
        let shift = bit_index & 7u;
        var value = constants[base + byte_index] >> shift;
        if (shift > 3u) {
            value = value | (constants[base + byte_index + 1u] << (8u - shift));
        }
        out.limb[i] = value & 31u;
    }
    return out;
}

fn fe_to_sums(value: Fe, base: u32) {
    let reduced = fe_canonical(value);
    for (var byte = 0u; byte < 32u; byte = byte + 1u) {
        sums[base + byte] = 0u;
    }
    for (var i = 0u; i < 51u; i = i + 1u) {
        let bit_index = i * 5u;
        let byte_index = bit_index >> 3u;
        let shift = bit_index & 7u;
        sums[base + byte_index] =
            sums[base + byte_index] | ((reduced.limb[i] << shift) & 255u);
        if (shift > 3u) {
            sums[base + byte_index + 1u] =
                sums[base + byte_index + 1u] | (reduced.limb[i] >> (8u - shift));
        }
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
    fe_to_sums(result.x, output_base);
    fe_to_sums(result.y, output_base + 32u);
    fe_to_sums(result.z, output_base + 64u);
    fe_to_sums(result.t, output_base + 96u);
}

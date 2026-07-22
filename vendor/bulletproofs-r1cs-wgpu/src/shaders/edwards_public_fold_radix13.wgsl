// Qualification-only fixed-public-scalar pointwise fold over extended Edwards
// points. Field elements use twenty radix-2^13 u32 limbs modulo 2^255-19.
// Every invocation reads the same predetermined public scalar pair for its
// round; no witness or caller-supplied scalar enters this shader.

struct Params {
    output_count: u32,
    round: u32,
    reserved_0: u32,
    reserved_1: u32,
};

struct Fe {
    limb: array<u32, 20>,
};

struct ExtPoint {
    x: Fe,
    y: Fe,
    z: Fe,
    t: Fe,
};

@group(0) @binding(0) var<uniform> params: Params;
// Current public point vector, `[point][X/Y/Z/T][20 radix-2^13 limbs]`.
@group(0) @binding(1) var<storage, read> coordinates: array<u32>;
// Twenty radix-2^13 limbs of Edwards 2*d.
@group(0) @binding(2) var<storage, read> constants: array<u32>;
// `[round][left/right][32 canonical bytes]`, one public byte per u32.
@group(0) @binding(3) var<storage, read> public_challenges: array<u32>;
// Next resident public point vector.
@group(0) @binding(4) var<storage, read_write> folded: array<u32>;

fn p_digit(index: u32) -> u32 {
    if (index == 0u) {
        return 8173u;
    }
    return select(8191u, 255u, index == 19u);
}

fn fe_ge_p(a: Fe) -> bool {
    var cursor = 20u;
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
    for (var i = 0u; i < 20u; i = i + 1u) {
        let subtrahend = p_digit(i) + borrow;
        if (a.limb[i] < subtrahend) {
            out.limb[i] = a.limb[i] + 8192u - subtrahend;
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
    for (var round = 0u; round < 6u; round = round + 1u) {
        for (var i = 0u; i < 20u; i = i + 1u) {
            let carry = out.limb[i] >> 13u;
            out.limb[i] = out.limb[i] & 8191u;
            if (i < 19u) {
                out.limb[i + 1u] = out.limb[i + 1u] + carry;
            } else {
                out.limb[0] = out.limb[0] + carry * 608u;
            }
        }
    }
    for (var round = 0u; round < 4u; round = round + 1u) {
        let high = out.limb[19] >> 8u;
        out.limb[19] = out.limb[19] & 255u;
        out.limb[0] = out.limb[0] + high * 19u;
        for (var i = 0u; i < 19u; i = i + 1u) {
            let carry = out.limb[i] >> 13u;
            out.limb[i] = out.limb[i] & 8191u;
            out.limb[i + 1u] = out.limb[i + 1u] + carry;
        }
    }
    if (fe_ge_p(out)) {
        out = fe_sub_p(out);
    }
    return out;
}

fn fe_add(a: Fe, b: Fe) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 20u; i = i + 1u) {
        out.limb[i] = a.limb[i] + b.limb[i];
    }
    return fe_canonical(out);
}

fn fe_sub(a: Fe, b: Fe) -> Fe {
    var augmented: Fe;
    var carry = 0u;
    for (var i = 0u; i < 20u; i = i + 1u) {
        let sum = a.limb[i] + p_digit(i) + carry;
        augmented.limb[i] = sum & 8191u;
        carry = sum >> 13u;
    }
    var out: Fe;
    var borrow = 0u;
    for (var i = 0u; i < 20u; i = i + 1u) {
        let subtrahend = b.limb[i] + borrow;
        if (augmented.limb[i] < subtrahend) {
            out.limb[i] = augmented.limb[i] + 8192u - subtrahend;
            borrow = 1u;
        } else {
            out.limb[i] = augmented.limb[i] - subtrahend;
            borrow = 0u;
        }
    }
    return fe_canonical(out);
}

fn fe_mul(a: Fe, b: Fe) -> Fe {
    var wide: array<u32, 40>;
    for (var i = 0u; i < 20u; i = i + 1u) {
        for (var j = 0u; j < 20u; j = j + 1u) {
            wide[i + j] = wide[i + j] + a.limb[i] * b.limb[j];
        }
    }
    for (var i = 0u; i < 39u; i = i + 1u) {
        let carry = wide[i] >> 13u;
        wide[i] = wide[i] & 8191u;
        wide[i + 1u] = wide[i + 1u] + carry;
    }
    wide[39] = wide[39] & 8191u;
    var cursor = 40u;
    loop {
        if (cursor == 20u) {
            break;
        }
        cursor = cursor - 1u;
        wide[cursor - 20u] = wide[cursor - 20u] + wide[cursor] * 608u;
    }
    var out: Fe;
    for (var i = 0u; i < 20u; i = i + 1u) {
        out.limb[i] = wide[i];
    }
    return fe_canonical(out);
}

fn fe_zero() -> Fe {
    var out: Fe;
    return out;
}

fn fe_one() -> Fe {
    var out = fe_zero();
    out.limb[0] = 1u;
    return out;
}

fn identity_point() -> ExtPoint {
    var point: ExtPoint;
    point.x = fe_zero();
    point.y = fe_one();
    point.z = fe_one();
    point.t = fe_zero();
    return point;
}

fn fe_from_coordinates(base: u32) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 20u; i = i + 1u) {
        out.limb[i] = coordinates[base + i];
    }
    return out;
}

fn fe_from_constants(base: u32) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 20u; i = i + 1u) {
        out.limb[i] = constants[base + i];
    }
    return out;
}

fn load_point(base: u32) -> ExtPoint {
    var point: ExtPoint;
    point.x = fe_from_coordinates(base);
    point.y = fe_from_coordinates(base + 20u);
    point.z = fe_from_coordinates(base + 40u);
    point.t = fe_from_coordinates(base + 60u);
    return point;
}

fn fe_to_folded(value: Fe, base: u32) {
    for (var i = 0u; i < 20u; i = i + 1u) {
        folded[base + i] = value.limb[i];
    }
}

fn store_point(point: ExtPoint, base: u32) {
    fe_to_folded(point.x, base);
    fe_to_folded(point.y, base + 20u);
    fe_to_folded(point.z, base + 40u);
    fe_to_folded(point.t, base + 60u);
}

fn add_points(left: ExtPoint, right: ExtPoint, d2: Fe) -> ExtPoint {
    let a = fe_mul(fe_sub(left.y, left.x), fe_sub(right.y, right.x));
    let b = fe_mul(fe_add(left.y, left.x), fe_add(right.y, right.x));
    let c = fe_mul(fe_mul(left.t, right.t), d2);
    let zz = fe_mul(left.z, right.z);
    let d = fe_add(zz, zz);
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

fn public_scalar_bit(side: u32, bit: u32) -> bool {
    let byte_index = bit >> 3u;
    let shift = bit & 7u;
    let scalar_base = params.round * 64u + side * 32u;
    return ((public_challenges[scalar_base + byte_index] >> shift) & 1u) == 1u;
}

fn fold_pair(left: ExtPoint, right: ExtPoint, d2: Fe) -> ExtPoint {
    // Simultaneous left-to-right double-and-add. Both scalar bitstreams are
    // predetermined and uniform across the dispatch. The point addresses and
    // 256-bit schedule are fixed; only public uniform branches remain.
    var accumulator = identity_point();
    var bit = 256u;
    loop {
        if (bit == 0u) {
            break;
        }
        bit = bit - 1u;
        accumulator = add_points(accumulator, accumulator, d2);
        if (public_scalar_bit(0u, bit)) {
            accumulator = add_points(accumulator, left, d2);
        }
        if (public_scalar_bit(1u, bit)) {
            accumulator = add_points(accumulator, right, d2);
        }
    }
    return accumulator;
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let pair = gid.x;
    if (pair >= params.output_count) {
        return;
    }
    let left = load_point(pair * 80u);
    let right = load_point((pair + params.output_count) * 80u);
    store_point(fold_pair(left, right, fe_from_constants(0u)), pair * 80u);
}

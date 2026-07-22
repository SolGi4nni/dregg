// Qualification-only constant-address MSM for secret scalars and public
// Ristretto points. Secret scalar bits affect only `select`; they never affect
// buffer addresses, loop bounds, dispatch geometry, branches, or early exits.
// The only `if` statements are explicitly marked public gid bounds.

struct Params {
    item_count: u32,
    reserved_0: u32,
    reserved_1: u32,
    reserved_2: u32,
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
// Current points, `[point][X/Y/Z/T][20 radix-2^13 limbs]`.
@group(0) @binding(1) var<storage, read> coordinates: array<u32>;
// Witness scalars, `[term][32 canonical bytes]`, one byte per u32.
@group(0) @binding(2) var<storage, read> secret_scalars: array<u32>;
// Twenty radix-2^13 limbs of Edwards 2*d.
@group(0) @binding(3) var<storage, read> constants: array<u32>;
// Scaled points or the next fixed reduction level.
@group(0) @binding(4) var<storage, read_write> output_points: array<u32>;

fn p_digit(index: u32) -> u32 {
    return select(select(8191u, 255u, index == 19u), 8173u, index == 0u);
}

fn fe_select(left: Fe, right: Fe, choose_right: bool) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 20u; i = i + 1u) {
        out.limb[i] = select(left.limb[i], right.limb[i], choose_right);
    }
    return out;
}

fn fe_ge_p(a: Fe) -> bool {
    var greater = false;
    var equal = true;
    for (var reverse = 0u; reverse < 20u; reverse = reverse + 1u) {
        let index = 19u - reverse;
        let greater_here = a.limb[index] > p_digit(index);
        let less_here = a.limb[index] < p_digit(index);
        greater = greater || (equal && greater_here);
        equal = equal && !(greater_here || less_here);
    }
    return greater || equal;
}

fn fe_sub_p(a: Fe) -> Fe {
    var out: Fe;
    var borrow = 0u;
    for (var i = 0u; i < 20u; i = i + 1u) {
        let subtrahend = p_digit(i) + borrow;
        let underflow = a.limb[i] < subtrahend;
        out.limb[i] =
            a.limb[i] + select(0u, 8192u, underflow) - subtrahend;
        borrow = select(0u, 1u, underflow);
    }
    return out;
}

fn fe_canonical(input: Fe) -> Fe {
    var out = input;
    // All loop bounds and limb addresses are public constants.
    for (var round = 0u; round < 6u; round = round + 1u) {
        for (var i = 0u; i < 19u; i = i + 1u) {
            let carry = out.limb[i] >> 13u;
            out.limb[i] = out.limb[i] & 8191u;
            out.limb[i + 1u] = out.limb[i + 1u] + carry;
        }
        let top_carry = out.limb[19] >> 13u;
        out.limb[19] = out.limb[19] & 8191u;
        out.limb[0] = out.limb[0] + top_carry * 608u;
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
    return fe_select(out, fe_sub_p(out), fe_ge_p(out));
}

fn fe_add(a: Fe, b: Fe) -> Fe {
    var out: Fe;
    for (var i = 0u; i < 20u; i = i + 1u) {
        out.limb[i] = a.limb[i] + b.limb[i];
    }
    return fe_canonical(out);
}

fn fe_sub(a: Fe, b: Fe) -> Fe {
    // Since a,b < p, a+p-b is nonnegative and below 2p.
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
        let underflow = augmented.limb[i] < subtrahend;
        out.limb[i] =
            augmented.limb[i] + select(0u, 8192u, underflow) - subtrahend;
        borrow = select(0u, 1u, underflow);
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
    for (var reverse = 0u; reverse < 20u; reverse = reverse + 1u) {
        let high = 39u - reverse;
        wide[high - 20u] = wide[high - 20u] + wide[high] * 608u;
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

fn point_select(left: ExtPoint, right: ExtPoint, choose_right: bool) -> ExtPoint {
    var out: ExtPoint;
    out.x = fe_select(left.x, right.x, choose_right);
    out.y = fe_select(left.y, right.y, choose_right);
    out.z = fe_select(left.z, right.z, choose_right);
    out.t = fe_select(left.t, right.t, choose_right);
    return out;
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

fn fe_to_output(value: Fe, base: u32) {
    for (var i = 0u; i < 20u; i = i + 1u) {
        output_points[base + i] = value.limb[i];
    }
}

fn store_point(point: ExtPoint, base: u32) {
    fe_to_output(point.x, base);
    fe_to_output(point.y, base + 20u);
    fe_to_output(point.z, base + 40u);
    fe_to_output(point.t, base + 60u);
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

fn secret_scalar_bit(term: u32, bit: u32) -> bool {
    // Address depends only on public term id and the fixed loop bit, never on
    // the loaded secret value.
    let byte_index = bit >> 3u;
    let shift = bit & 7u;
    return ((secret_scalars[term * 32u + byte_index] >> shift) & 1u) == 1u;
}

fn scale_secret(point: ExtPoint, term: u32, d2: Fe) -> ExtPoint {
    var accumulator = identity_point();
    let identity = identity_point();
    // Exactly 256 doublings and 256 additions for every scalar, including zero.
    for (var round = 0u; round < 256u; round = round + 1u) {
        let bit = 255u - round;
        accumulator = add_points(accumulator, accumulator, d2);
        let selected = point_select(identity, point, secret_scalar_bit(term, bit));
        accumulator = add_points(accumulator, selected, d2);
    }
    return accumulator;
}

@compute @workgroup_size(64)
fn scale_terms(@builtin(global_invocation_id) gid: vec3<u32>) {
    let term = gid.x;
    // PUBLIC_GID_BOUND: depends only on dispatch geometry and public term count.
    if (term >= params.item_count) {
        return;
    }
    store_point(
        scale_secret(load_point(term * 80u), term, fe_from_constants(0u)),
        term * 80u,
    );
}

@compute @workgroup_size(64)
fn reduce_points(@builtin(global_invocation_id) gid: vec3<u32>) {
    let pair = gid.x;
    // PUBLIC_GID_BOUND: depends only on dispatch geometry and public pair count.
    if (pair >= params.item_count) {
        return;
    }
    let left = load_point(pair * 160u);
    let right = load_point(pair * 160u + 80u);
    store_point(add_points(left, right, fe_from_constants(0u)), pair * 80u);
}

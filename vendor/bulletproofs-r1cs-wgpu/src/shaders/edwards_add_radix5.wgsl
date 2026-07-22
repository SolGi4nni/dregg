// Exact extended-Edwards addition modulo p = 2^255 - 19.
// Historical filename retained so the already-qualified pair-add include path
// does not churn; the implementation below is radix-2^8.
//
// Field elements use 32 little-endian radix-2^8 limbs. A convolution
// coefficient is bounded by 32 * 255^2 = 2,080,800, and the pseudo-Mersenne
// fold `2^256 = 38 (mod 2^255-19)` remains below 80 million. Every arithmetic
// operation is therefore exact in u32.

struct Params {
    item_count: u32,
    window_count: u32,
    bucket_count: u32,
    chunk_count: u32,
    stage: u32,
    limb_count: u32,
    window_bits: u32,
    chunk_terms: u32,
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
// Canonical scalar bytes, `[term][32 bytes]`, one byte per u32. Only the
// public-verifier Pippenger entry point reads this binding.
@group(0) @binding(4) var<storage, read> scalar_bytes: array<u32>;

fn p_digit(index: u32) -> u32 {
    // 2^255 - 19 in radix 2^8 is [237, 255, ..., 255, 127].
    if (index == 0u) {
        return 237u;
    }
    return select(255u, 127u, index + 1u == params.limb_count);
}

fn fe_ge_p(a: Fe) -> bool {
    var cursor = params.limb_count;
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
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
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
        for (var i = 0u; i < params.limb_count; i = i + 1u) {
            let carry = out.limb[i] >> 8u;
            out.limb[i] = out.limb[i] & 255u;
            if (i + 1u < params.limb_count) {
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
    var carry = 0u;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        let sum = a.limb[i] + b.limb[i] + carry;
        out.limb[i] = sum & 255u;
        carry = sum >> 8u;
    }
    // Canonical inputs are both below p, hence a+b < 2p < 2^256: the final
    // carry is zero and one conditional subtraction is sufficient.
    if (fe_ge_p(out)) {
        out = fe_sub_p(out);
    }
    return out;
}

fn fe_is_zero(a: Fe) -> bool {
    var any = 0u;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        any = any | a.limb[i];
    }
    return any == 0u;
}

fn fe_equal(a: Fe, b: Fe) -> bool {
    var different = 0u;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        different = different | (a.limb[i] ^ b.limb[i]);
    }
    return different == 0u;
}

fn fe_sub(a: Fe, b: Fe) -> Fe {
    // Form canonical base-256 digits of a+p first. Since a<p, a+p<2^256.
    // Subtracting b cannot underflow, and the result is below 2p, so one
    // conditional p subtraction gives the canonical field difference. This
    // avoids the old negate+add path's repeated five-lap canonicalizations.
    var augmented: Fe;
    var carry = 0u;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        let sum = a.limb[i] + p_digit(i) + carry;
        augmented.limb[i] = sum & 255u;
        carry = sum >> 8u;
    }

    var out: Fe;
    var borrow = 0u;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        let subtrahend = b.limb[i] + borrow;
        if (augmented.limb[i] < subtrahend) {
            out.limb[i] = augmented.limb[i] + 256u - subtrahend;
            borrow = 1u;
        } else {
            out.limb[i] = augmented.limb[i] - subtrahend;
            borrow = 0u;
        }
    }
    if (fe_ge_p(out)) {
        out = fe_sub_p(out);
    }
    return out;
}

fn fe_mul(a: Fe, b: Fe) -> Fe {
    var wide: array<u32, 63>;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        for (var j = 0u; j < params.limb_count; j = j + 1u) {
            wide[i + j] = wide[i + j] + a.limb[i] * b.limb[j];
        }
    }
    var cursor = params.limb_count * 2u - 1u;
    loop {
        if (cursor == params.limb_count) {
            break;
        }
        cursor = cursor - 1u;
        wide[cursor - params.limb_count] =
            wide[cursor - params.limb_count] + wide[cursor] * 38u;
    }
    var out: Fe;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        out.limb[i] = wide[i];
    }
    return fe_canonical(out);
}

fn fe_from_coordinates(base: u32) -> Fe {
    var out: Fe;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        out.limb[i] = coordinates[base + i] & 255u;
    }
    return out;
}

fn fe_from_constants(base: u32) -> Fe {
    var out: Fe;
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
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
    for (var i = 0u; i < params.limb_count; i = i + 1u) {
        sums[base + i] = value.limb[i];
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

fn point_is_identity(point: ExtPoint) -> bool {
    return fe_is_zero(point.x) && fe_is_zero(point.t) && fe_equal(point.y, point.z);
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let pair = gid.x;
    if (pair >= params.item_count) {
        return;
    }
    let input_base = pair * 256u;
    let output_base = pair * 128u;
    let left = load_point(input_base);
    let right = load_point(input_base + 128u);
    let result = add_points(left, right, fe_from_constants(0u));
    store_point(result, output_base);
}

fn scalar_window(term: u32, window: u32) -> u32 {
    let bit_index = window * params.window_bits;
    let byte_index = bit_index >> 3u;
    let shift = bit_index & 7u;
    var digit = scalar_bytes[term * 32u + byte_index] >> shift;
    if (shift + params.window_bits > 8u && byte_index + 1u < 32u) {
        digit = digit | (scalar_bytes[term * 32u + byte_index + 1u] << (8u - shift));
    }
    let mask = (1u << params.window_bits) - 1u;
    return digit & mask;
}

// Stage 1: one invocation per `[window][bounded-term chunk][nonzero bucket]`.
// Every invocation owns its accumulator, so no coordinate atomics or host
// synchronization are needed. Scalar-dependent control flow is permitted only
// because verifier scalars are public.
fn run_partial_buckets(flat: u32) {
    let partial_count = params.window_count * params.chunk_count * params.bucket_count;
    if (flat >= partial_count) {
        return;
    }
    let bucket = flat % params.bucket_count;
    let quotient = flat / params.bucket_count;
    let chunk = quotient % params.chunk_count;
    let window = quotient / params.chunk_count;
    let first_term = chunk * params.chunk_terms;
    let end_term = min(first_term + params.chunk_terms, params.item_count);
    let d2 = fe_from_constants(0u);
    var accumulator = point_from_constants(32u);
    var has_value = false;
    for (var term = first_term; term < end_term; term = term + 1u) {
        if (scalar_window(term, window) == bucket + 1u) {
            let point = load_point(term * 128u);
            if (has_value) {
                accumulator = add_points(accumulator, point, d2);
            } else {
                accumulator = point;
                has_value = true;
            }
        }
    }
    store_point(accumulator, flat * 128u);
}

// Stage 2: reduce the chunk-local partials into one point per window/bucket.
fn run_reduce_buckets(flat: u32) {
    let reduced_count = params.window_count * params.bucket_count;
    if (flat >= reduced_count) {
        return;
    }
    let bucket = flat % params.bucket_count;
    let window = flat / params.bucket_count;
    let d2 = fe_from_constants(0u);
    var accumulator = point_from_constants(32u);
    var has_value = false;
    for (var chunk = 0u; chunk < params.chunk_count; chunk = chunk + 1u) {
        let partial = (window * params.chunk_count + chunk) * params.bucket_count + bucket;
        let point = load_point(partial * 128u);
        if (!point_is_identity(point)) {
            if (has_value) {
                accumulator = add_points(accumulator, point, d2);
            } else {
                accumulator = point;
                has_value = true;
            }
        }
    }
    store_point(accumulator, flat * 128u);
}

// Stage 3: Pippenger's descending running-sum identity converts the nonzero
// buckets into one weighted point per window.
fn run_collapse_windows(window: u32) {
    if (window >= params.window_count) {
        return;
    }
    let d2 = fe_from_constants(0u);
    var running = point_from_constants(32u);
    var weighted = point_from_constants(32u);
    var running_has_value = false;
    var weighted_has_value = false;
    var cursor = params.bucket_count;
    loop {
        if (cursor == 0u) {
            break;
        }
        cursor = cursor - 1u;
        let bucket = load_point((window * params.bucket_count + cursor) * 128u);
        if (!point_is_identity(bucket)) {
            if (running_has_value) {
                running = add_points(running, bucket, d2);
            } else {
                running = bucket;
                running_has_value = true;
            }
        }
        if (running_has_value) {
            if (weighted_has_value) {
                weighted = add_points(weighted, running, d2);
            } else {
                weighted = running;
                weighted_has_value = true;
            }
        }
    }
    store_point(weighted, window * 128u);
}

// Stage 4: only the bounded window sums remain. This dependent chain is at
// most 256 doublings plus one addition per window and stays device-resident.
fn run_combine_windows(invocation: u32) {
    if (invocation != 0u) {
        return;
    }
    let d2 = fe_from_constants(0u);
    var accumulator = point_from_constants(32u);
    var has_value = false;
    var cursor = params.window_count;
    loop {
        if (cursor == 0u) {
            break;
        }
        cursor = cursor - 1u;
        let window_sum = load_point(cursor * 128u);
        if (has_value) {
            for (var bit = 0u; bit < params.window_bits; bit = bit + 1u) {
                accumulator = add_points(accumulator, accumulator, d2);
            }
            if (!point_is_identity(window_sum)) {
                accumulator = add_points(accumulator, window_sum, d2);
            }
        } else if (!point_is_identity(window_sum)) {
            accumulator = window_sum;
            has_value = true;
        }
    }
    store_point(accumulator, 0u);
}

// One pipeline serves all four ordered stages. Separate metadata bindings
// select the stage for each dispatch, avoiding four expensive driver
// compilations of the same exact field/group arithmetic.
@compute @workgroup_size(64)
fn pippenger(@builtin(global_invocation_id) gid: vec3<u32>) {
    if (params.stage == 0u) {
        run_partial_buckets(gid.x);
    } else if (params.stage == 1u) {
        run_reduce_buckets(gid.x);
    } else if (params.stage == 2u) {
        run_collapse_windows(gid.x);
    } else if (params.stage == 3u) {
        run_combine_windows(gid.x);
    }
}

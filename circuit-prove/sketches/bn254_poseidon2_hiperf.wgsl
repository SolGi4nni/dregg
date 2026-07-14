// Compact Poseidon2-BN254 t=3 Merkle engine.
//
// The host dispatches leaf_main once per equal-height matrix group, then
// compress_main once per binary-tree level, with combine_main at matrix
// injection heights. All digest I/O is canonical little-endian u32x8; the
// permutation and its externally supplied round constants are Montgomery.

alias Fp = array<u32, 8>;

// Named lanes keep the 24-limb permutation state statically addressable even
// though the arithmetic inside each Fp is looped.
struct PoseidonState {
    x: Fp,
    y: Fp,
    z: Fp,
}

const LIMBS: u32 = 8u;
const BB_P: u32 = 0x78000001u;
const BB_MU: u32 = 0x88000001u;

// BN254 base-field modulus, little-endian 32-bit limbs:
// 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001.
fn fp_p() -> Fp {
    return Fp(
        0xf0000001u, 0x43e1f593u, 0x79b97091u, 0x2833e848u,
        0x8181585du, 0xb85045b6u, 0xe131a029u, 0x30644e72u,
    );
}

// R^2 mod P for R=2^256. Multiplying a canonical value by this with
// mont_mul converts it to Montgomery representation.
fn fp_r2() -> Fp {
    return Fp(
        0xae216da7u, 0x1bb8e645u, 0xe35c59e3u, 0x53fe3ab1u,
        0x53bb8085u, 0x8c49833du, 0x7f4e44a5u, 0x0216d0b1u,
    );
}

// -P[0]^-1 mod 2^32.
const N0_INV: u32 = 0xefffffffu;

// Every constant occupies exactly 32 bytes. This makes the uniform array
// naturally 16-byte aligned without the surprising stride of array<u32> in
// the uniform address space.
struct MontFp {
    lo: vec4<u32>,
    hi: vec4<u32>,
}

struct PoseidonParams {
    // 0..11: initial external RCs, round-major/lane-major.
    // 12..67: internal RCs (lane 0 only).
    // 68..79: terminal external RCs, round-major/lane-major.
    round_constants: array<MontFp, 80>,

    // The matrices are J + diag(d). Padding lanes must be zero.
    external_diag: vec4<u32>, // (1, 1, 1, 0)
    internal_diag: vec4<u32>, // (1, 1, 2, 0)
}

// b0: matrix arena, previous digest layer, or injected digest layer.
// b1: dispatch descriptor (entry-point-specific layout documented below).
// b2: canonical output digests; combine_main also reads its old contents.
// b3: the immutable 2,592-byte PoseidonParams uniform block.
@group(0) @binding(0) var<storage, read> src: array<u32>;
@group(0) @binding(1) var<storage, read> desc: array<u32>;
@group(0) @binding(2) var<storage, read_write> outd: array<u32>;
@group(0) @binding(3) var<uniform> poseidon_params: PoseidonParams;

// Portable 32x32 -> 64 multiplication. WGSL intentionally has no u64; the
// split form maps to ordinary integer ALU on Vulkan, Metal, and browser GPUs.
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
    let mid_carry = select(0u, 0x10000u, mid < p01);
    let lo = p00 + (mid << 16u);
    let lo_carry = select(0u, 1u, lo < p00);
    return vec2<u32>(lo, p11 + (mid >> 16u) + mid_carry + lo_carry);
}

// Subtract P once and select the original value if it was already canonical.
// high_nonzero supplies the ninth limb used by Montgomery reduction. This is
// branch-free because field reductions would otherwise diverge almost every
// wave on pseudorandom Poseidon states.
fn fp_reduce_once(a: Fp, high_nonzero: bool) -> Fp {
    let p = fp_p();
    var d: Fp;
    var borrow = 0u;
    for (var i = 0u; i < LIMBS; i = i + 1u) {
        let d0 = a[i] - p[i];
        let b0 = select(0u, 1u, a[i] < p[i]);
        let d1 = d0 - borrow;
        let b1 = select(0u, 1u, d0 < borrow);
        d[i] = d1;
        borrow = b0 | b1;
    }

    let keep_a = (borrow != 0u) && !high_nonzero;
    for (var i = 0u; i < LIMBS; i = i + 1u) {
        d[i] = select(d[i], a[i], keep_a);
    }
    return d;
}

fn fp_add(a: Fp, b: Fp) -> Fp {
    var s: Fp;
    var carry = 0u;
    for (var i = 0u; i < LIMBS; i = i + 1u) {
        let s0 = a[i] + b[i];
        let c0 = select(0u, 1u, s0 < a[i]);
        let s1 = s0 + carry;
        let c1 = select(0u, 1u, s1 < carry);
        s[i] = s1;
        carry = c0 | c1;
    }
    return fp_reduce_once(s, carry != 0u);
}

// Coarsely Integrated Operand Scanning (CIOS) Montgomery multiplication.
//
// This is deliberately looped: one 10-word accumulator replaces the 17-word
// fully materialized product, and there is only one copy of the 8x8 limb loop
// in shader IR. t[9] catches the carry above the ordinary ninth accumulator
// limb before the radix-word shift; the final CIOS bound is < 2P.
fn mont_mul(a: Fp, b: Fp) -> Fp {
    let p = fp_p();
    var t: array<u32, 10>;

    for (var i = 0u; i < LIMBS; i = i + 1u) {
        let bi = b[i];
        var carry = 0u;

        // t += a * b[i].
        for (var j = 0u; j < LIMBS; j = j + 1u) {
            let product = mul64(a[j], bi);
            let s0 = t[j] + product.x;
            let c0 = select(0u, 1u, s0 < t[j]);
            let s1 = s0 + carry;
            let c1 = select(0u, 1u, s1 < carry);
            t[j] = s1;
            carry = product.y + c0 + c1;
        }
        var top = t[8] + carry;
        t[9] = t[9] + select(0u, 1u, top < t[8]);
        t[8] = top;

        // m chooses the low word so t + mP is divisible by 2^32.
        let m = t[0] * N0_INV;
        carry = 0u;
        for (var j = 0u; j < LIMBS; j = j + 1u) {
            let product = mul64(m, p[j]);
            let s0 = t[j] + product.x;
            let c0 = select(0u, 1u, s0 < t[j]);
            let s1 = s0 + carry;
            let c1 = select(0u, 1u, s1 < carry);
            t[j] = s1;
            carry = product.y + c0 + c1;
        }
        top = t[8] + carry;
        t[9] = t[9] + select(0u, 1u, top < t[8]);
        t[8] = top;

        // Exact division by the radix word.
        for (var j = 0u; j < 9u; j = j + 1u) {
            t[j] = t[j + 1u];
        }
        t[9] = 0u;
    }

    var r: Fp;
    for (var i = 0u; i < LIMBS; i = i + 1u) {
        r[i] = t[i];
    }
    return fp_reduce_once(r, t[8] != 0u);
}

fn sbox(x: Fp) -> Fp {
    let x2 = mont_mul(x, x);
    let x4 = mont_mul(x2, x2);
    return mont_mul(x4, x);
}

fn load_round_constant(index: u32) -> Fp {
    let c = poseidon_params.round_constants[index];
    return Fp(c.lo.x, c.lo.y, c.lo.z, c.lo.w, c.hi.x, c.hi.y, c.hi.z, c.hi.w);
}

// The only diagonal coefficients in the pinned matrices are 1 and 2. Keeping
// the matrices in the uniform ABI while specializing tiny coefficients avoids
// nine Montgomery multiplications per linear layer. k is uniform across every
// invocation at a given call site, so this branch does not split a wave.
fn fp_mul_diag(x: Fp, k: u32) -> Fp {
    var result = x;
    if (k == 2u) {
        result = fp_add(x, x);
    }
    return result;
}

// External matrix J + diag(1,1,1).
fn ext_linear(s: ptr<function, PoseidonState>) {
    let sum = fp_add(fp_add((*s).x, (*s).y), (*s).z);
    (*s).x = fp_add(sum, fp_mul_diag((*s).x, poseidon_params.external_diag.x));
    (*s).y = fp_add(sum, fp_mul_diag((*s).y, poseidon_params.external_diag.y));
    (*s).z = fp_add(sum, fp_mul_diag((*s).z, poseidon_params.external_diag.z));
}

// Internal matrix J + diag(1,1,2).
fn int_linear(s: ptr<function, PoseidonState>) {
    let sum = fp_add(fp_add((*s).x, (*s).y), (*s).z);
    (*s).x = fp_add(sum, fp_mul_diag((*s).x, poseidon_params.internal_diag.x));
    (*s).y = fp_add(sum, fp_mul_diag((*s).y, poseidon_params.internal_diag.y));
    (*s).z = fp_add(sum, fp_mul_diag((*s).z, poseidon_params.internal_diag.z));
}

fn full_round(s: ptr<function, PoseidonState>, rc_base: u32) {
    (*s).x = fp_add((*s).x, load_round_constant(rc_base));
    (*s).y = fp_add((*s).y, load_round_constant(rc_base + 1u));
    (*s).z = fp_add((*s).z, load_round_constant(rc_base + 2u));
    (*s).x = sbox((*s).x);
    (*s).y = sbox((*s).y);
    (*s).z = sbox((*s).z);
    ext_linear(s);
}

// Poseidon2Bn254<3>: 4 initial external rounds, 56 internal rounds, and 4
// terminal external rounds. The loops are essential: Mesa/RADV must never see
// 64 separately expanded copies of the round or Montgomery-multiply bodies.
fn permute(s: ptr<function, PoseidonState>) {
    ext_linear(s);

    for (var round = 0u; round < 4u; round = round + 1u) {
        full_round(s, round * 3u);
    }

    for (var round = 0u; round < 56u; round = round + 1u) {
        (*s).x = fp_add((*s).x, load_round_constant(12u + round));
        (*s).x = sbox((*s).x);
        int_linear(s);
    }

    for (var round = 0u; round < 4u; round = round + 1u) {
        full_round(s, 68u + round * 3u);
    }
}

fn canonical_to_montgomery(x: Fp) -> Fp {
    return mont_mul(x, fp_r2());
}

fn montgomery_to_canonical(x: Fp) -> Fp {
    var one: Fp;
    one[0] = 1u;
    return mont_mul(x, one);
}

fn load_digest(buffer_index: u32, from_output: bool) -> Fp {
    var x: Fp;
    let base = buffer_index * LIMBS;
    if (from_output) {
        for (var word = 0u; word < LIMBS; word = word + 1u) {
            x[word] = outd[base + word];
        }
    } else {
        for (var word = 0u; word < LIMBS; word = word + 1u) {
            x[word] = src[base + word];
        }
    }
    return canonical_to_montgomery(x);
}

fn store_digest(buffer_index: u32, x: Fp) {
    let canonical = montgomery_to_canonical(x);
    let base = buffer_index * LIMBS;
    for (var word = 0u; word < LIMBS; word = word + 1u) {
        outd[base + word] = canonical[word];
    }
}

// BabyBear Montgomery -> canonical, exactly matching the backend's existing
// radix-2^31 leaf packing path.
fn bb_canonical(x: u32) -> u32 {
    let m = x * BB_MU;
    let mp = mul64(m, BB_P);
    return (0u - mp.y) + select(0u, BB_P, mp.y != 0u);
}

// desc = [matrix_count, base_row, row_count, 0, (src_offset, width) ...]
//
// One invocation hashes one logical row across all same-height matrices.
// Matrix data is row-major BabyBear Montgomery u32. Digits are canonical+1,
// shifted radix-2^31 packed eight per BN254 rate element. The sponge has
// width 3/rate 2, overwrite absorption, and digest state[0].
@compute @workgroup_size(64)
fn leaf_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let local_row = gid.x;
    let row_count = desc[2];
    if (local_row >= row_count) {
        return;
    }

    let row = desc[1] + local_row;
    let matrix_count = desc[0];
    var state: PoseidonState;
    var packed: Fp;
    var digit_count = 0u;
    var rate_lane = 0u;

    for (var matrix = 0u; matrix < matrix_count; matrix = matrix + 1u) {
        let matrix_offset = desc[4u + 2u * matrix];
        let width = desc[5u + 2u * matrix];
        let row_base = matrix_offset + row * width;

        for (var column = 0u; column < width; column = column + 1u) {
            let digit = bb_canonical(src[row_base + column]) + 1u;
            let bit_position = 31u * digit_count;
            let limb = bit_position >> 5u;
            let shift = bit_position & 31u;
            packed[limb] = packed[limb] | (digit << shift);
            if (shift > 1u) {
                packed[limb + 1u] = packed[limb + 1u] | (digit >> (32u - shift));
            }

            digit_count = digit_count + 1u;
            if (digit_count == 8u) {
                let montgomery_packed = canonical_to_montgomery(packed);
                if (rate_lane == 0u) {
                    state.x = montgomery_packed;
                } else {
                    state.y = montgomery_packed;
                }
                packed = Fp();
                digit_count = 0u;
                rate_lane = rate_lane + 1u;
                if (rate_lane == 2u) {
                    permute(&state);
                    rate_lane = 0u;
                }
            }
        }
    }

    if (digit_count != 0u) {
        if (rate_lane == 0u) {
            state.x = canonical_to_montgomery(packed);
        } else {
            state.y = canonical_to_montgomery(packed);
        }
        rate_lane = rate_lane + 1u;
    }
    if (rate_lane != 0u) {
        permute(&state);
    }
    store_digest(row, state.x);
}

// desc = [output_count, base_output, 0, 0]
// src contains the previous canonical digest layer. Each output is
// permute([src[2*i], src[2*i+1], 0])[0]. src and outd must not overlap.
@compute @workgroup_size(64)
fn compress_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let local_output = gid.x;
    if (local_output >= desc[0]) {
        return;
    }

    let output_index = desc[1] + local_output;
    var state: PoseidonState;
    state.x = load_digest(2u * output_index, false);
    state.y = load_digest(2u * output_index + 1u, false);
    permute(&state);
    store_digest(output_index, state.x);
}

// desc = [output_count, base_output, 0, 0]
// outd contains the current canonical digest layer and src the same-height
// injected layer. Each output becomes permute([outd[i], src[i], 0])[0].
@compute @workgroup_size(64)
fn combine_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let local_output = gid.x;
    if (local_output >= desc[0]) {
        return;
    }

    let output_index = desc[1] + local_output;
    var state: PoseidonState;
    state.x = load_digest(output_index, true);
    state.y = load_digest(output_index, false);
    permute(&state);
    store_digest(output_index, state.x);
}

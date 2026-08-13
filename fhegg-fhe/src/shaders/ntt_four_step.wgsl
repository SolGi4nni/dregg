// Four-step (Bailey) negacyclic RNS NTT, in two arithmetic dialects.
//
// The transform of length N = R*C is decomposed into
//   step 1: C-point transforms along rows   -> one (R x C) @ (C x C) GEMM
//   step 2: a pointwise twiddle by w_N^{r c'}
//   step 3: R-point transforms along columns -> one (R x R) @ (R x C) GEMM
// which is O(N*sqrt(N)) modular multiplies against radix-2's O(N log N), bought
// back (on the right silicon) at the matrix-engine rate. This is the CROSS /
// MORPH shape; see notes/ntt-as-gemm.md for the derivation and the read.
//
// Two dialects share every table and every boundary:
//   * `mont` — the existing three-limb radix-2^16 Montgomery kernel from
//     bfv_ntt.wgsl, one modmul per MAC. This is the honest baseline for a GPU
//     with no matrix engine.
//   * `bat`  — CROSS's Basis Aligned Transformation. The PREKNOWN operand (the
//     twiddle matrix) is expanded offline into a K x K byte matrix per entry;
//     the runtime operand is byte-decomposed for free (a (lo,hi) residue IS its
//     own byte packing); the contraction is exact 8-bit MACs into a u32 that
//     provably cannot overflow; one REDC per output element closes it.
//
// Data convention: residues are PLAIN (not Montgomery); every twiddle table is
// uploaded in Montgomery form, so `mont_mul(plain, mont) = plain*w` exactly.
// WGSL core only: no u64, no vendor extension, no 64-bit atomics.

const MAXK: u32 = 8u;

struct Meta {
    n            : u32,  // N = R*C
    r_dim        : u32,
    c_dim        : u32,
    items        : u32,  // number of independent (poly, modulus) transforms
    modulus_rows : u32,  // stride for per-modulus tables
    k_limbs      : u32,  // K = ceil(log2(q)/8)
    k_words      : u32,  // ceil(K/4)
    off_tw_c     : u32,  // u32 offsets into `tables`, per-row base added by shader
    off_tw_r     : u32,
    off_tw_mid   : u32,
    off_twist    : u32,
    tbl_stride   : u32,  // per-modulus-row stride into `tables`
    bat_stride   : u32,  // per-modulus-row stride into `bat`
    off_bat_c    : u32,
    off_bat_r    : u32,
    grid_w       : u32,  // threads per dispatch row (grid.x * 64), for 2D grids
};

@group(0) @binding(0) var<uniform>             params  : Meta;
@group(0) @binding(1) var<storage, read_write> data    : array<u32>;
@group(0) @binding(2) var<storage, read_write> scratch : array<u32>;
// Per modulus row: q.lo, q.hi, -q^-1 mod 2^16, pad, R^2.lo, R^2.hi, pad, pad.
@group(0) @binding(3) var<storage, read>       qdata   : array<u32>;
@group(0) @binding(4) var<storage, read>       tables  : array<u32>;
@group(0) @binding(5) var<storage, read>       bat     : array<u32>;

// ---------------------------------------------------------------- 64-bit core

fn add64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let lo = a.x + b.x;
    let carry = select(0u, 1u, lo < a.x);
    return vec2<u32>(lo, a.y + b.y + carry);
}

fn sub64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let borrow = select(0u, 1u, a.x < b.x);
    return vec2<u32>(a.x - b.x, a.y - b.y - borrow);
}

fn ge64(a: vec2<u32>, b: vec2<u32>) -> bool {
    return a.y > b.y || (a.y == b.y && a.x >= b.x);
}

fn addmod(a: vec2<u32>, b: vec2<u32>, q: vec2<u32>) -> vec2<u32> {
    var s = add64(a, b);
    if (ge64(s, q)) { s = sub64(s, q); }
    return s;
}

// REDC(a*b) in base 2^16 with R = 2^48; identical to bfv_ntt.wgsl's kernel.
// Inputs < q < 2^48; output < q.
fn mont_mul(a: vec2<u32>, b: vec2<u32>, q: vec2<u32>, qinv16: u32) -> vec2<u32> {
    let mask = 0xffffu;
    let ad = array<u32, 3>(a.x & mask, a.x >> 16u, a.y & mask);
    let bd = array<u32, 3>(b.x & mask, b.x >> 16u, b.y & mask);
    let qd = array<u32, 3>(q.x & mask, q.x >> 16u, q.y & mask);
    var t = array<u32, 7>(0u, 0u, 0u, 0u, 0u, 0u, 0u);

    for (var i = 0u; i < 3u; i = i + 1u) {
        var carry = 0u;
        for (var j = 0u; j < 3u; j = j + 1u) {
            let index = i + j;
            let uv = t[index] + ad[j] * bd[i] + carry;
            t[index] = uv & mask;
            carry = uv >> 16u;
        }
        for (var k = i + 3u; k < 7u; k = k + 1u) {
            let uv = t[k] + carry;
            t[k] = uv & mask;
            carry = uv >> 16u;
        }

        let m = (t[i] * qinv16) & mask;
        carry = 0u;
        for (var j = 0u; j < 3u; j = j + 1u) {
            let index = i + j;
            let uv = t[index] + m * qd[j] + carry;
            t[index] = uv & mask;
            carry = uv >> 16u;
        }
        for (var k = i + 3u; k < 7u; k = k + 1u) {
            let uv = t[k] + carry;
            t[k] = uv & mask;
            carry = uv >> 16u;
        }
    }

    var reduced = vec2<u32>(t[3] | (t[4] << 16u), t[5] | (t[6] << 16u));
    if (ge64(reduced, q)) { reduced = sub64(reduced, q); }
    return reduced;
}

// Bare Montgomery reduction: t < R*q  =>  t * R^-1 mod q. BAT's exit boundary.
fn redc(t: vec2<u32>, q: vec2<u32>, qinv16: u32) -> vec2<u32> {
    let mask = 0xffffu;
    let qd = array<u32, 3>(q.x & mask, q.x >> 16u, q.y & mask);
    var w = array<u32, 7>(
        t.x & mask, (t.x >> 16u) & mask, t.y & mask, (t.y >> 16u) & mask, 0u, 0u, 0u);

    for (var i = 0u; i < 3u; i = i + 1u) {
        let m = (w[i] * qinv16) & mask;
        var carry = 0u;
        for (var j = 0u; j < 3u; j = j + 1u) {
            let index = i + j;
            let uv = w[index] + m * qd[j] + carry;
            w[index] = uv & mask;
            carry = uv >> 16u;
        }
        for (var k = i + 3u; k < 7u; k = k + 1u) {
            let uv = w[k] + carry;
            w[k] = uv & mask;
            carry = uv >> 16u;
        }
    }

    var out = vec2<u32>(w[3] | (w[4] << 16u), w[5] | (w[6] << 16u));
    if (ge64(out, q)) { out = sub64(out, q); }
    return out;
}

// Unsigned 4-lane 8-bit dot product. On a DP4a / V_DOT4_U32_U8 / MXU target
// this is ONE instruction; naga 24 has no `dot4U8Packed`, and Apple GPUs have
// no DP4a either, so the hand-rolled form is what this hardware would run
// regardless. Max value 4*255^2 = 260100.
fn dot4u8(a: u32, b: u32) -> u32 {
    return (a & 0xffu) * (b & 0xffu)
         + ((a >> 8u) & 0xffu) * ((b >> 8u) & 0xffu)
         + ((a >> 16u) & 0xffu) * ((b >> 16u) & 0xffu)
         + ((a >> 24u) & 0xffu) * ((b >> 24u) & 0xffu);
}

// ------------------------------------------------------------------ accessors

fn row_of(item: u32) -> u32 { return item % params.modulus_rows; }

fn row_q(item: u32) -> vec2<u32> {
    let s = row_of(item) * 8u;
    return vec2<u32>(qdata[s], qdata[s + 1u]);
}
fn row_qinv(item: u32) -> u32 { return qdata[row_of(item) * 8u + 2u]; }
fn row_r2(item: u32) -> vec2<u32> {
    let s = row_of(item) * 8u;
    return vec2<u32>(qdata[s + 4u], qdata[s + 5u]);
}

fn load(buf_base: u32, index: u32) -> vec2<u32> {
    let o = (buf_base + index) * 2u;
    return vec2<u32>(data[o], data[o + 1u]);
}
fn store(buf_base: u32, index: u32, v: vec2<u32>) {
    let o = (buf_base + index) * 2u;
    data[o] = v.x;
    data[o + 1u] = v.y;
}
fn load_s(buf_base: u32, index: u32) -> vec2<u32> {
    let o = (buf_base + index) * 2u;
    return vec2<u32>(scratch[o], scratch[o + 1u]);
}
fn store_s(buf_base: u32, index: u32, v: vec2<u32>) {
    let o = (buf_base + index) * 2u;
    scratch[o] = v.x;
    scratch[o + 1u] = v.y;
}
fn tbl(base: u32, index: u32) -> vec2<u32> {
    let o = (base + index) * 2u;
    return vec2<u32>(tables[o], tables[o + 1u]);
}

// ------------------------------------------------------------------- passes

// Twist / untwist: data[i] *= table[i]. Also serves the inverse's n^-1 psi^-i.
@compute @workgroup_size(64)
fn pass_twist(@builtin(global_invocation_id) gid: vec3<u32>) {
    let tid = gid.y * params.grid_w + gid.x;
    if (tid >= params.items * params.n) { return; }
    let item = tid / params.n;
    let idx = tid % params.n;
    let q = row_q(item);
    let qi = row_qinv(item);
    let tb = row_of(item) * params.tbl_stride + params.off_twist;
    store(item * params.n, idx, mont_mul(load(item * params.n, idx), tbl(tb, idx), q, qi));
}

// scratch[r][c'] = sum_c data[c*R + r] * tw_c[c][c']   (Montgomery dialect)
@compute @workgroup_size(64)
fn pass_step1_mont(@builtin(global_invocation_id) gid: vec3<u32>) {
    let tid = gid.y * params.grid_w + gid.x;
    if (tid >= params.items * params.n) { return; }
    let item = tid / params.n;
    let local = tid % params.n;
    let r = local / params.c_dim;
    let cp = local % params.c_dim;

    let q = row_q(item);
    let qi = row_qinv(item);
    let base = item * params.n;
    let tb = row_of(item) * params.tbl_stride + params.off_tw_c;

    var acc = vec2<u32>(0u, 0u);
    for (var c = 0u; c < params.c_dim; c = c + 1u) {
        let v = load(base, c * params.r_dim + r);
        let w = tbl(tb, c * params.c_dim + cp);
        acc = addmod(acc, mont_mul(v, w, q, qi), q);
    }
    store_s(base, r * params.c_dim + cp, acc);
}

// scratch[r][c'] *= w_N^{r c'}
@compute @workgroup_size(64)
fn pass_step2(@builtin(global_invocation_id) gid: vec3<u32>) {
    let tid = gid.y * params.grid_w + gid.x;
    if (tid >= params.items * params.n) { return; }
    let item = tid / params.n;
    let local = tid % params.n;
    let q = row_q(item);
    let qi = row_qinv(item);
    let base = item * params.n;
    let tb = row_of(item) * params.tbl_stride + params.off_tw_mid;
    store_s(base, local, mont_mul(load_s(base, local), tbl(tb, local), q, qi));
}

// data[r'][c'] = sum_r scratch[r][c'] * tw_r[r'][r]   (Montgomery dialect)
@compute @workgroup_size(64)
fn pass_step3_mont(@builtin(global_invocation_id) gid: vec3<u32>) {
    let tid = gid.y * params.grid_w + gid.x;
    if (tid >= params.items * params.n) { return; }
    let item = tid / params.n;
    let local = tid % params.n;
    let rp = local / params.c_dim;
    let cp = local % params.c_dim;

    let q = row_q(item);
    let qi = row_qinv(item);
    let base = item * params.n;
    let tb = row_of(item) * params.tbl_stride + params.off_tw_r;

    var acc = vec2<u32>(0u, 0u);
    for (var r = 0u; r < params.r_dim; r = r + 1u) {
        let v = load_s(base, r * params.c_dim + cp);
        let w = tbl(tb, rp * params.r_dim + r);
        acc = addmod(acc, mont_mul(v, w, q, qi), q);
    }
    store(base, rp * params.c_dim + cp, acc);
}

// --- BAT dialect -------------------------------------------------------------
//
// psum[j] = sum over the contracted index and over byte-lane i of
//           batbyte[j][i] * runtimebyte[i].
// Bound: psum[j] <= dim * K * 255^2. At dim=64, K=5 that is 20,808,000 < 2^25,
// so the u32 accumulator has 7 bits of headroom and an INT32 MXU accumulator
// would have 6. Overflow needs dim*K > 2^15.
//
// The runtime operand needs NO preprocessing: bytes 0..3 of a residue are
// exactly its low u32 and byte 4 is the low byte of its high u32.

fn bat_merge(psum: ptr<function, array<u32, 8>>, q: vec2<u32>, qinv16: u32) -> vec2<u32> {
    var acc = vec2<u32>(0u, 0u);
    for (var jj = 0u; jj < params.k_limbs; jj = jj + 1u) {
        let j = params.k_limbs - 1u - jj;
        for (var b = 0u; b < 8u; b = b + 1u) {
            acc = add64(acc, acc);
            if (ge64(acc, q)) { acc = sub64(acc, q); }
        }
        acc = add64(acc, vec2<u32>((*psum)[j], 0u));
        if (ge64(acc, q)) { acc = sub64(acc, q); }
    }
    // acc == a_plain * w_mont mod q; one REDC yields a_plain * w.
    return redc(acc, q, qinv16);
}

@compute @workgroup_size(64)
fn pass_step1_bat(@builtin(global_invocation_id) gid: vec3<u32>) {
    let tid = gid.y * params.grid_w + gid.x;
    if (tid >= params.items * params.n) { return; }
    let item = tid / params.n;
    let local = tid % params.n;
    let r = local / params.c_dim;
    let cp = local % params.c_dim;

    let q = row_q(item);
    let qi = row_qinv(item);
    let base = item * params.n;
    let bb = row_of(item) * params.bat_stride + params.off_bat_c;
    let kw = params.k_words;
    let kl = params.k_limbs;

    // Plane-major table: bat[((j*KW + w)*C + c)*C + c'], so lanes that differ
    // only in c' read adjacent words. Entry-major (the obvious layout) strides
    // by K*KW and costs ~2x on this GPU.
    let plane = params.c_dim * params.c_dim;
    var psum = array<u32, 8>(0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u);
    for (var c = 0u; c < params.c_dim; c = c + 1u) {
        let v = load(base, c * params.r_dim + r);
        let cell = c * params.c_dim + cp;
        for (var j = 0u; j < kl; j = j + 1u) {
            var s = psum[j];
            s = s + dot4u8(bat[bb + (j * kw) * plane + cell], v.x);
            if (kw > 1u) { s = s + dot4u8(bat[bb + (j * kw + 1u) * plane + cell], v.y); }
            psum[j] = s;
        }
    }
    store_s(base, r * params.c_dim + cp, bat_merge(&psum, q, qi));
}

@compute @workgroup_size(64)
fn pass_step3_bat(@builtin(global_invocation_id) gid: vec3<u32>) {
    let tid = gid.y * params.grid_w + gid.x;
    if (tid >= params.items * params.n) { return; }
    let item = tid / params.n;
    let local = tid % params.n;
    let rp = local / params.c_dim;
    let cp = local % params.c_dim;

    let q = row_q(item);
    let qi = row_qinv(item);
    let base = item * params.n;
    let bb = row_of(item) * params.bat_stride + params.off_bat_r;
    let kw = params.k_words;
    let kl = params.k_limbs;

    // Plane-major: bat[((j*KW + w)*R + r')*R + r]. Lanes here differ only in c',
    // so every table read is a broadcast; the layout matters for step 1.
    let plane = params.r_dim * params.r_dim;
    var psum = array<u32, 8>(0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u);
    for (var r = 0u; r < params.r_dim; r = r + 1u) {
        let v = load_s(base, r * params.c_dim + cp);
        let cell = rp * params.r_dim + r;
        for (var j = 0u; j < kl; j = j + 1u) {
            var s = psum[j];
            s = s + dot4u8(bat[bb + (j * kw) * plane + cell], v.x);
            if (kw > 1u) { s = s + dot4u8(bat[bb + (j * kw + 1u) * plane + cell], v.y); }
            psum[j] = s;
        }
    }
    store(base, rp * params.c_dim + cp, bat_merge(&psum, q, qi));
}

// data[lo] = data[lo] * data[hi]  (plain x plain, so two REDCs via R^2)
@compute @workgroup_size(64)
fn pass_pointwise(@builtin(global_invocation_id) gid: vec3<u32>) {
    let tid = gid.y * params.grid_w + gid.x;
    if (tid >= params.items * params.n) { return; }
    let item = tid / params.n;
    let idx = tid % params.n;
    let q = row_q(item);
    let qi = row_qinv(item);
    let lo = item * params.n;
    let hi = (item + params.items) * params.n;
    let a = load(lo, idx);
    let b = load(hi, idx);
    store(lo, idx, mont_mul(mont_mul(a, b, q, qi), row_r2(item), q, qi));
}

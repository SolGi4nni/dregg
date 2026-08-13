// Multilinear-extension fold over BabyBear (p = 2013265921 = 15*2^27 + 1) — the sumcheck prover's
// inner loop, on the GPU, IN PLACE.
//
// One sumcheck round takes an evaluation table of the multilinear `f` over {0,1}^k and folds the
// last bound variable away with the verifier's challenge `r`:
//
//     f'(x) = f(x, 0) + r * (f(x, 1) - f(x, 0))        for x in {0,1}^(k-1)
//
// The table is indexed so that the folded variable is the HIGH bit: `f(x,0) = table[i]` and
// `f(x,1) = table[i + half]` with `half = 2^(k-1)`. So a round is a strided halving reduction.
//
// ⚑ THE FOLD IS RACE-FREE IN PLACE. Invocation `i` reads exactly indices `i` and `i + half`, and
// writes exactly index `i`. Index `i` (in [0,half)) is read by NO other invocation — invocation
// `i - half` does not exist — and index `i + half` is written by no invocation at all. So the
// output aliases the input with no cross-invocation hazard, and the table shrinks in place with
// ZERO extra allocation and zero ping-pong copies. This is what lets an n-round sumcheck run as n
// bare dispatches against one resident buffer.
//
// WGSL core has no u64 and no 32x32->64 widening multiply, so the BabyBear product goes through an
// explicit `mul_hi` (16-bit limbs, every intermediate provably < 2^32) feeding a Montgomery REDC
// with R = 2^32. The TABLE stays in CANONICAL form; only the challenge is uploaded in Montgomery
// form (`r_mont = r * 2^32 mod p`), so `mont_mul(r_mont, d) = r_mont * d * R^-1 = r * d` exactly and
// no conversion pass over the table is ever needed.

const P  : u32 = 2013265921u;  // BabyBear
const MU : u32 = 2013265919u;  // -P^{-1} mod 2^32

struct MleMeta {
    // Output length of this round = half the current table length.
    half   : u32,
    // The round challenge in Montgomery form: r * 2^32 mod P.
    r_mont : u32,
    _pad0  : u32,
    _pad1  : u32,
};

@group(0) @binding(0) var<uniform>              params : MleMeta;
@group(0) @binding(1) var<storage, read_write>  table  : array<u32>;

// High 32 bits of a*b. 16-bit limbs; `cross` is at most 2^16 + 2*(2^16-1) < 2^18 so it cannot
// overflow, and the final sum EQUALS the true high word (< 2^32) so it cannot overflow either.
fn mul_hi(a: u32, b: u32) -> u32 {
    let a0 = a & 0xffffu;
    let a1 = a >> 16u;
    let b0 = b & 0xffffu;
    let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let cross = (p00 >> 16u) + (p01 & 0xffffu) + (p10 & 0xffffu);
    return p11 + (p01 >> 16u) + (p10 >> 16u) + (cross >> 16u);
}

// REDC with R = 2^32: given x = (hi:lo) < P * 2^32, return x * R^-1 mod P.
//
// m = lo * MU mod 2^32 makes (x + m*P) divisible by 2^32. The low word of m*P is (2^32 - lo) mod
// 2^32, so the low words cancel and the carry out of them is exactly 1 when lo != 0. The result
// (x + m*P)/2^32 < (P^2 + 2^32*P)/2^32 < 2P < 2^32, so it fits a u32 and ONE conditional subtract
// canonicalizes it.
fn monty_reduce(lo: u32, hi: u32) -> u32 {
    let m = lo * MU;
    let mp_hi = mul_hi(m, P);
    let carry = select(0u, 1u, lo != 0u);
    var r = hi + mp_hi + carry;
    if (r >= P) { r = r - P; }
    return r;
}

// a * b * R^-1 mod P. With `a` in Montgomery form and `b` canonical this is the canonical product.
fn mont_mul(a: u32, b: u32) -> u32 {
    return monty_reduce(a * b, mul_hi(a, b));
}

fn addmod(a: u32, b: u32) -> u32 {
    let s = a + b;                       // a,b < P < 2^31 so the sum cannot wrap
    return select(s, s - P, s >= P);
}

fn submod(a: u32, b: u32) -> u32 {
    return select(a - b + P, a - b, a >= b);
}

@compute @workgroup_size(256)
fn fold_round(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    if (i >= params.half) { return; }
    let f0 = table[i];
    let f1 = table[i + params.half];
    let d = submod(f1, f0);
    table[i] = addmod(f0, mont_mul(params.r_mont, d));
}

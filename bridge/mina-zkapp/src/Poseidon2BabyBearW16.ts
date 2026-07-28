import { Field, Provable, Gadgets } from 'o1js';

// ---------------------------------------------------------------------------
// Poseidon2-w16 over BabyBear, AS AN o1js/KIMCHI CIRCUIT.
//
// WHY: `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` prices a Mina-side verifier of
// dregg's FRI-STARK at ~2.2e7 Kimchi rows, and the whole product rests on ONE
// number it flags as a DESIGN CLAIM rather than a measurement: ~2,000 Kimchi
// rows per Poseidon2-w16-BabyBear permutation. Its band runs to ~8,400 (§3.7,
// from the one measured comparable: 16,837 R1CS/perm for the same permutation
// emulated in gnark over BN254), i.e. a 4x uncertainty on the headline. Its own
// top recommendation is "write a single o1js `P2.perm` gadget and read
// `getRows()` off it". This is that gadget.
//
// ⚑ THIS IS NOT AN AIR, AND IT IS NOT A dregg CONSTRAINT SYSTEM. It emits no
// dregg circuit and nothing in dregg calls it. It is a COST PROBE for a
// hypothetical Mina-side verifier: an o1js circuit whose only purpose is to be
// counted. dregg's own AIR is authored in Lean and stays there.
//
// THE REFERENT. The permutation is pinned to
// `metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean`, which is itself
// KAT-validated bit-exact against the deployed Rust
// `default_babybear_poseidon2_16().permute(.)`:
//   WIDTH 16, S-box x^7, 4 external-initial + 13 internal + 4 external-final
//   rounds, `MDSMat4` circulant external layer (ADD-ONLY), internal layer
//   `(1 + Diag(V))` with V = [-2,1,2,1/2,3,4,-1/2,-3,-4,2^-8,1/4,1/8,2^-27,
//   -2^-8,-1/16,-2^-27].
// `permBigInt` below reproduces the Lean's two `#guard` vectors, and
// `provablePerm` is checked against `permBigInt` inside `Provable.runAndCheck`,
// so a divergence is a failure, not a footnote.
//
// ---------------------------------------------------------------------------
// THE COST MODEL, WHICH IS THE WHOLE POINT
//
// BabyBear p = 2^31 - 2^27 + 1 is 31 bits; Pasta Fp is ~254 bits. So a BabyBear
// element is ONE native Pasta element with ~223 bits of headroom, and `p` is a
// COMPILE-TIME CONSTANT, so `q*p` is a coefficient rather than a multiplication.
// That is what makes this route expressible where a pairing is not.
//
// It is still a foreign modulus. Two facts drive every number below:
//
//  (1) INTERMEDIATES NEED NOT BE CANONICAL. Both linear layers and x -> x^7 are
//      functions of the residue class, so any representative is sound. We track
//      an INTEGER upper bound per lane instead of reducing, and reduce only when
//      the bound would overflow. `assertSafe` throws if any tracked bound could
//      reach the Pasta modulus — a bound violation is an UNSOUND circuit (field
//      arithmetic would stop agreeing with integer arithmetic), not a slow one.
//
//  (2) THE S-BOX DEFEATS LAZY REDUCTION. The usual "amortise reductions over the
//      headroom" advice holds for Horner chains, where accumulation is LINEAR.
//      `x^7` is a multiplication chain: each step DOUBLES the bit width, so at
//      most four multiplications ride before the native modulus is hit and there
//      is no amortisation across S-boxes. One reduction per S-box is the floor.
//
// The bound chain, which is why the lane target is 2^31 and not 2^32:
//   * after a reduction a lane is < 2^31;
//   * the external layer's coefficients sum to at most 35 per output, so the
//     layer's output is < 35*2^31 ~ 2^36.13;
//   * the S-box input is that plus a round constant, < 2^36.17, and its 7th
//     power is < 2^253.2 — under the Pasta modulus with ~0.8 bits to spare.
//   A 2^32 lane target would put x^7 at ~2^260 and wrap. This is measured, not
//   assumed: `assertSafe` is what would catch it.
// ---------------------------------------------------------------------------

/** BabyBear prime. */
export const P = 2013265921n;
/** Pasta Fp modulus — the ceiling every tracked bound must stay under. */
export const N = Field.ORDER;
/** `2^-1 mod p`. */
const INV2 = 1006632961n;

const inv2exp = (k: number): bigint => {
  let x = 1n;
  for (let i = 0; i < k; i++) x = (x * INV2) % P;
  return x;
};

// The internal layer's diagonal, as (positive multiplier, subtract?) pairs.
// Lane 0 is special (V0 = -2 is folded into `partSum - s0`).
const INTERNAL_DIAG: { c: bigint; sub: boolean }[] = [
  { c: 0n, sub: false }, //  0: handled separately
  { c: 1n, sub: false }, //  1: +1
  { c: 2n, sub: false }, //  2: +2
  { c: INV2, sub: false }, //  3: +1/2
  { c: 3n, sub: false }, //  4: +3
  { c: 4n, sub: false }, //  5: +4
  { c: INV2, sub: true }, //  6: -1/2
  { c: 3n, sub: true }, //  7: -3
  { c: 4n, sub: true }, //  8: -4
  { c: inv2exp(8), sub: false }, //  9: +2^-8
  { c: inv2exp(2), sub: false }, // 10: +1/4
  { c: inv2exp(3), sub: false }, // 11: +1/8
  { c: inv2exp(27), sub: false }, // 12: +2^-27
  { c: inv2exp(8), sub: true }, // 13: -2^-8
  { c: inv2exp(4), sub: true }, // 14: -1/16
  { c: inv2exp(27), sub: true }, // 15: -2^-27
];

/** `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL` (4 rounds x 16). */
export const RC_EXT_INITIAL: bigint[][] = [
  [0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
   0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
   0x221e2e36, 0x1ab7202e],
  [0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
   0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
   0x52eb6ba2, 0x50642905],
  [0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
   0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
   0x29fbda49, 0x018afffd],
  [0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
   0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
   0x2cc78315, 0x1e36ea47],
].map((r) => r.map(BigInt));

/** `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL` (4 rounds x 16). */
export const RC_EXT_FINAL: bigint[][] = [
  [0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
   0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
   0x6a2d3d10, 0x20523767],
  [0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
   0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
   0x49a12590, 0x35ec52a1],
  [0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
   0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
   0x45e1547b, 0x4a8db2ab],
  [0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
   0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
   0x3c8bcd87, 0x608758b8],
].map((r) => r.map(BigInt));

/** `BABYBEAR_POSEIDON2_RC_16_INTERNAL` (13 scalars). */
export const RC_INTERNAL: bigint[] = [
  0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb, 0x61210ce0,
  0x3c318939, 0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606, 0x241af16d,
].map(BigInt);

// ===========================================================================
// 1. The plain-bigint reference — a direct transcription of the Lean module.
// ===========================================================================

const fadd = (a: bigint, b: bigint) => (a + b) % P;
const fsub = (a: bigint, b: bigint) => (a + P - (b % P)) % P;
const fmul = (a: bigint, b: bigint) => (a * b) % P;
const sboxBigInt = (a: bigint) => {
  const x2 = fmul(a, a);
  const x4 = fmul(x2, x2);
  return fmul(fmul(x4, x2), a);
};

/** `apply_mat4` on a block of 4, operation-for-operation as p3's `external.rs`. */
function mat4(x0: bigint, x1: bigint, x2: bigint, x3: bigint): bigint[] {
  const t01 = fadd(x0, x1);
  const t23 = fadd(x2, x3);
  const t0123 = fadd(t01, t23);
  const t01123 = fadd(t0123, x1);
  const t01233 = fadd(t0123, x3);
  const y3 = fadd(t01233, fadd(x0, x0));
  const y1 = fadd(t01123, fadd(x2, x2));
  const y0 = fadd(t01123, t01);
  const y2 = fadd(t01233, t23);
  return [y0, y1, y2, y3];
}

/** The width-16 external linear layer. */
export function mdsLightBigInt(s: bigint[]): bigint[] {
  const m: bigint[] = [];
  for (let k = 0; k < 4; k++) m.push(...mat4(s[4 * k], s[4 * k + 1], s[4 * k + 2], s[4 * k + 3]));
  const sums: bigint[] = [];
  for (let k = 0; k < 4; k++)
    sums.push(fadd(fadd(m[k], m[4 + k]), fadd(m[8 + k], m[12 + k])));
  return m.map((v, i) => fadd(v, sums[i % 4]));
}

export function internalRoundBigInt(rc: bigint, s: bigint[]): bigint[] {
  const s0 = sboxBigInt(fadd(s[0], rc));
  let partSum = 0n;
  for (let j = 1; j < 16; j++) partSum = fadd(partSum, s[j]);
  const fullSum = fadd(partSum, s0);
  const out = [fsub(partSum, s0)];
  for (let j = 1; j < 16; j++) {
    const { c, sub } = INTERNAL_DIAG[j];
    const t = fmul(s[j], c);
    out.push(sub ? fsub(fullSum, t) : fadd(fullSum, t));
  }
  return out;
}

export function externalRoundBigInt(rc: bigint[], s: bigint[]): bigint[] {
  return mdsLightBigInt(s.map((v, i) => sboxBigInt(fadd(v, rc[i]))));
}

/** The deployed BabyBear Poseidon2-w16 permutation, in plain bigints. */
export function permBigInt(input: bigint[]): bigint[] {
  let s = mdsLightBigInt(input.map((x) => x % P));
  for (const rc of RC_EXT_INITIAL) s = externalRoundBigInt(rc, s);
  for (const rc of RC_INTERNAL) s = internalRoundBigInt(rc, s);
  for (const rc of RC_EXT_FINAL) s = externalRoundBigInt(rc, s);
  return s;
}

/** `permute([0..15])`, from the deployed Rust permutation (Lean `#guard`, :192-195). */
export const KAT_RANGE16 = [
  1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788, 1726691001,
  1761127344, 1552405120, 417318995, 36799261, 1215172152, 614923223, 1300746575,
  957311597, 304856115,
].map(BigInt);

/** `permute([0,...,0])`, from the deployed Rust permutation (Lean `#guard`, :198-201). */
export const KAT_ZERO16 = [
  1168947398, 128782440, 747404447, 883925857, 360581875, 1704698758, 1878363991,
  1054281681, 682225194, 705839125, 1218819873, 41544645, 1095344608, 174996601,
  1678438226, 11259290,
].map(BigInt);

// ===========================================================================
// 2. The in-circuit permutation, with explicit integer-bound tracking.
// ===========================================================================

/** A BabyBear element as a native Pasta `Field`, with an inclusive integer
 *  upper bound on the representative it holds. Not necessarily canonical. */
export type BB = { v: Field; max: bigint };

/** Rows are only meaningful if the circuit is SOUND: field arithmetic has to
 *  agree with integer arithmetic, which needs every value strictly under the
 *  Pasta modulus. This is what makes the measurement of a real object. */
function assertSafe(max: bigint, what: string) {
  if (max >= N)
    throw new Error(
      `Poseidon2BabyBearW16: ${what} can reach ${max} >= Pasta modulus ${N}; ` +
        'the circuit would be UNSOUND (field arithmetic stops matching integer arithmetic)',
    );
}

const constBB = (c: bigint): BB => ({ v: Field(c), max: c });
const bits = (x: bigint) => (x <= 0n ? 0 : x.toString(2).length);

function add(a: BB, b: BB): BB {
  const max = a.max + b.max;
  assertSafe(max, 'add');
  return { v: a.v.add(b.v), max };
}
/** Multiply by a positive constant < p. Free of gates (a coefficient), not of bound. */
function scale(a: BB, c: bigint): BB {
  const max = a.max * c;
  assertSafe(max, 'scale');
  return { v: a.v.mul(c), max };
}
/** `a - b`, kept non-negative by adding the smallest multiple of `p` that
 *  dominates `b`'s bound. The multiple is a constant, so this is still linear. */
function sub(a: BB, b: BB): BB {
  const k = ((b.max + P - 1n) / P) * P; // smallest multiple of p >= b.max
  const max = a.max + k;
  assertSafe(max, 'sub');
  return { v: a.v.add(Field(k)).sub(b.v), max };
}
function mul(a: BB, b: BB): BB {
  const max = a.max * b.max;
  assertSafe(max, 'mul');
  return { v: a.v.seal().mul(b.v.seal()), max };
}

/** `r < 2^31`, via three 12-bit lookups (o1js's cheapest sub-32-bit check) and a
 *  recomposition over the integers. `rangeCheck32` would give `r < 2^32`, which
 *  the external layer's 35x growth cannot absorb (see the header). */
function assertLt2p31(r: Field) {
  const [a, b, c] = Provable.witness(Provable.Array(Field, 3), () => {
    const v = r.toBigInt();
    return [Field(v & 0xfffn), Field((v >> 12n) & 0xfffn), Field((v >> 24n) & 0x7fn)];
  });
  // a, b < 2^12 and 16*c < 2^12  =>  c < 2^7
  Gadgets.rangeCheck3x12(a, b, c.mul(16n));
  // a + 2^12 b + 2^24 c <= (2^12-1) + (2^12-1)2^12 + (2^7-1)2^24 = 2^31 - 1
  a.add(b.mul(1n << 12n)).add(c.mul(1n << 24n)).assertEquals(r);
}

/**
 * Range-check a witnessed quotient `q` whose honest value is at most `qmax`,
 * returning a LINEAR EXPRESSION for `q*p` built from the checked limbs.
 *
 * The limbs are 64-bit (`rangeCheck64` is o1js's cheapest bulk check: one
 * `RangeCheck0` row) laid at a 53-bit stride, so the SOUNDNESS bound —
 * `(2^64-1) * sum_i 2^(53 i)` — stays under `N/p` while the HONEST value is
 * still representable. Both facts are asserted here rather than argued.
 */
function quotientTimesP(qmax: bigint, value: () => bigint): { qp: Field; q: Field } {
  const STRIDE = 53n;
  const LIMB = 64n;
  let nLimbs = 1;
  while ((1n << (LIMB + STRIDE * BigInt(nLimbs - 1))) - 1n < qmax) nLimbs++;

  // soundness: the largest q the checks admit, and its q*p + 2^31 must be < N.
  let soundMax = 0n;
  for (let i = 0; i < nLimbs; i++) soundMax += ((1n << LIMB) - 1n) << (STRIDE * BigInt(i));
  if (soundMax * P + (1n << 31n) >= N)
    throw new Error(
      `quotient range check admits q up to 2^${bits(soundMax)}; q*p would reach ` +
        `2^${bits(soundMax * P)} >= Pasta modulus — UNSOUND`,
    );

  const limbs = Provable.witness(Provable.Array(Field, nLimbs), () => {
    let q = value();
    const out: Field[] = [];
    for (let i = 0; i < nLimbs - 1; i++) {
      out.push(Field(q & ((1n << STRIDE) - 1n)));
      q >>= STRIDE;
    }
    out.push(Field(q));
    return out;
  });
  for (const l of limbs) Gadgets.rangeCheck64(l);

  // q*p as one linear combination: sum_i limb_i * (p << 53i).
  let qp = limbs[0].mul(P);
  let q = limbs[0];
  for (let i = 1; i < nLimbs; i++) {
    qp = qp.add(limbs[i].mul(P << (STRIDE * BigInt(i))));
    q = q.add(limbs[i].mul(1n << (STRIDE * BigInt(i))));
  }
  return { qp, q };
}

/**
 * Reduce `v` to a representative `< 2^31` of the same residue class mod p.
 * Witnesses `q, r` with `v = q*p + r` over the INTEGERS (both sides < N, so the
 * field equation implies it), range-checks both, and returns `r`.
 */
function reduce(v: BB): BB {
  const qmax = v.max / P;
  const { qp } = quotientTimesP(qmax, () => v.v.toBigInt() / P);
  const r = Provable.witness(Field, () => Field(v.v.toBigInt() % P));
  assertLt2p31(r);
  qp.add(r).assertEquals(v.v);
  return { v: r, max: (1n << 31n) - 1n };
}

/** `x -> x^7` with exactly one reduction: four multiplications ride unreduced
 *  (the input bound is chosen so `x^7 < N`), then one `mod p`. */
function sbox(xIn: BB): BB {
  const x: BB = { v: xIn.v.seal(), max: xIn.max }; // materialise once, used twice
  const x2 = mul(x, x);
  const x4 = mul(x2, x2);
  const x6 = mul(x4, x2);
  const x7 = mul(x6, x);
  return reduce(x7);
}

/** Materialise a value into one variable. Free when it is already a variable;
 *  otherwise it costs the generic gates for the linear combination, ONCE. Every
 *  value used more than once is sealed, or o1js re-emits its gates per use — an
 *  unsealed shared sub-expression is a measurement artefact, not a real cost. */
const seal = (a: BB): BB => ({ v: a.v.seal(), max: a.max });

function mat4BB(x: BB[]): BB[] {
  const t01 = seal(add(x[0], x[1])); //   used twice
  const t23 = seal(add(x[2], x[3])); //   used twice
  const t0123 = add(t01, t23);
  const t01123 = seal(add(t0123, x[1])); // used twice
  const t01233 = seal(add(t0123, x[3])); // used twice
  return [
    add(t01123, t01), //                 2 x0 + 3 x1 + x2 + x3
    add(t01123, scale(x[2], 2n)), //     x0 + 2 x1 + 3 x2 + x3
    add(t01233, t23), //                 x0 + x1 + 2 x2 + 3 x3
    add(t01233, scale(x[0], 2n)), //     3 x0 + x1 + x2 + 2 x3
  ];
}

/** The external linear layer — ADD-ONLY, no multiplications. */
export function mdsLightBB(s: BB[]): BB[] {
  const m: BB[] = [];
  for (let k = 0; k < 4; k++) m.push(...mat4BB(s.slice(4 * k, 4 * k + 4)).map(seal));
  const sums: BB[] = [];
  for (let k = 0; k < 4; k++)
    sums.push(seal(add(add(m[k], m[4 + k]), add(m[8 + k], m[12 + k]))));
  return m.map((v, i) => seal(add(v, sums[i % 4])));
}

function externalRoundBB(rc: bigint[], s: BB[]): BB[] {
  return mdsLightBB(s.map((v, i) => sbox(add(v, constBB(rc[i])))));
}

/** A lane whose diagonal coefficient is a full-width inverse (1/2, 1/4, 1/8,
 *  1/16, 2^-8, 2^-27) gains ~31 bits every internal round, so it MUST be reduced
 *  every round or the width compounds 13 times over. The six lanes with small
 *  coefficients (+-1, +-2, +-3, +-4) gain ~2 bits a round and are left alone. */
const FULL_WIDTH_LANE = INTERNAL_DIAG.map(({ c }, j) => j > 0 && c > 4n);

function internalRoundBB(rc: bigint, s: BB[]): BB[] {
  const s0 = sbox(add(s[0], constBB(rc)));
  let partSum = s[1];
  for (let j = 2; j < 16; j++) partSum = add(partSum, s[j]);
  // ONE reduction here does the work of fifteen: `partSum` is what the next
  // round's S-box eats (lane 0 = partSum - s0), so bounding it bounds the only
  // value that has to stay under ~2^36 for x^7 to fit the Pasta modulus.
  const ps = reduce(partSum);
  const fullSum = seal(add(ps, s0));

  const out: BB[] = [sub(ps, s0)]; // V0 = -2
  for (let j = 1; j < 16; j++) {
    const { c, sub: isSub } = INTERNAL_DIAG[j];
    const t = scale(s[j], c);
    const lane = isSub ? sub(fullSum, t) : add(fullSum, t);
    out.push(FULL_WIDTH_LANE[j] ? reduce(lane) : seal(lane));
  }
  return out;
}

/** **The deployed BabyBear Poseidon2-w16 permutation, as an o1js circuit.**
 *  Input lanes must be canonical (`< p`). */
export function provablePerm(input: Field[]): Field[] {
  let s: BB[] = input.map((v) => ({ v, max: P - 1n }));
  s = mdsLightBB(s);
  for (const rc of RC_EXT_INITIAL) s = externalRoundBB(rc, s);
  for (const rc of RC_INTERNAL) s = internalRoundBB(rc, s);
  // The internal rounds leave six small-coefficient lanes unreduced (they grow
  // ~2 bits a round, not ~31). The external layer's 35x fan-in cannot absorb
  // that, so bring every lane back under 2^31 exactly once, here.
  s = s.map((x) => (x.max < 1n << 31n ? x : reduce(x)));
  for (const rc of RC_EXT_FINAL) s = externalRoundBB(rc, s);
  // The digest a hash consumer sees must be canonical; the internal rounds'
  // last `reduce` already lands every lane < 2^31, and a lane in [p, 2^31) is
  // one conditional subtraction away. Returned as-is: the sponge/compression
  // above this would canonicalise once, not 16 times per permutation.
  return s.map((x) => x.v);
}

/** `compress` — the deployed `TruncatedPermutation<., 2, 8, 16>`. */
export function provableCompress(a: Field[], b: Field[]): Field[] {
  return provablePerm([...a, ...b]).slice(0, 8);
}

// ---------------------------------------------------------------------------
// Component probes — so the measured total can be attributed to the same lines
// the design estimate used (`MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.3-3.4), rather
// than landing as one opaque number.
// ---------------------------------------------------------------------------

/** One S-box on a lane-sized input (the external-round shape). */
export function probeSbox(x: Field): Field {
  // 35*(2^31 - 1) + (p - 1) is the real external-round S-box input bound.
  return sbox({ v: x, max: 35n * ((1n << 31n) - 1n) + P - 1n }).v;
}
/** One external linear layer on reduced lanes (add-only). */
export function probeMdsLight(s: Field[]): Field[] {
  return mdsLightBB(s.map((v) => ({ v, max: (1n << 31n) - 1n }))).map((x) => x.v);
}
/** One external round: 16 S-boxes + the linear layer. */
export function probeExternalRound(s: Field[]): Field[] {
  return externalRoundBB(RC_EXT_INITIAL[0], s.map((v) => ({ v, max: (1n << 31n) - 1n }))).map(
    (x) => x.v,
  );
}
/** One internal round: 1 S-box + the broadcast/diagonal layer + re-bounding. */
export function probeInternalRound(s: Field[]): Field[] {
  return internalRoundBB(RC_INTERNAL[0], s.map((v) => ({ v, max: (1n << 31n) - 1n }))).map(
    (x) => x.v,
  );
}
/** One `mod p` reduction of a value the size an S-box produces. */
export function probeReduceSboxOutput(x: Field): Field {
  const yMax = 35n * ((1n << 31n) - 1n) + P - 1n;
  return reduce({ v: x, max: yMax ** 7n }).v;
}

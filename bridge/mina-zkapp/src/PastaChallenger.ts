import { Bool, Field, Poseidon, Provable } from 'o1js';
import { assertLowBitsSplit, assertLowBitsZero } from './FriChallenger.js';
import { BbExt, EXT_D } from './FriQueryStep.js';
import {
  LANES_PER_PERM,
  LIMBS_PER_SLOT,
  PASTA_RATE,
  P_BB,
  P_PASTA,
  PastaDigest,
  RADIX,
  assertCanonicalBb,
  assertLt2p31,
  assertLtPow2Pasta,
} from './PastaMmcs.js';

// ---------------------------------------------------------------------------
// THE PASTA-NATIVE CHALLENGER — `MultiField32Challenger<BabyBear, PastaFp,
// MinaPoseidonPerm, 3, 2>`, the Fiat-Shamir transcript of a `DreggMinaConfig`
// proof, as an o1js/Kimchi circuit.
//
// ⚑ WHY THIS IS THE HARD HALF OF THE HASH SWAP, AND THE MERKLE PATH IS THE EASY
// ONE. Swapping the Merkle hash replaces one 2,600-row emulated permutation with
// one 13-row native gate chain and changes nothing else. The transcript is a
// different STATE MACHINE, not the same machine with a different hash: the
// deployed `DuplexChallenger<BabyBear, _, 16, 8>` absorbs and squeezes in the
// SAME field, while this one PACKS BabyBear into Pasta to absorb and SPLITS
// Pasta back into BabyBear to squeeze. Both directions are places a
// transcription silently produces a different protocol.
//
// ⚑ THE SQUEEZE IS WHERE A PROVER WOULD ATTACK, AND IT IS THE ONE PLACE A
// WITNESS CAN LIE AND THE SPONGE STILL LOOK RIGHT. `split_pf_to_field_order_
// limbs(v, 7)` (`field/src/helpers.rs:338`) decomposes a Pasta cell as
// `v = c0 + c1*p + ... + c6*p^6 + r*p^7` over the INTEGERS. In circuit the limbs
// arrive as a hint, and the linear relation `v == sum ci p^i + r p^7` holds over
// Pasta for a whole ORBIT of decompositions — shift by `p_Pasta` and it still
// satisfies. Each of those is a different challenge set. So the decomposition
// must be pinned to the unique one whose INTEGER value is below `p_Pasta`:
//
//   (a) every limb `c_i` canonical, `< p_BabyBear` (not merely `< 2^31`);
//   (b) `r < 2^38`;
//   (c) the linear recomposition;
//   (d) `(r, c6, ..., c0) <=` the base-`p` digits of `p_Pasta - 1`, lexicographic.
//
// (d) is what forbids the wrap, and without it (a)-(c) are satisfiable by a
// prover choosing its own query indices out of a perfectly honest sponge. This
// is the same four-part argument `chain/gnark/multifield_challenger.go` makes
// for the ETH wrap's BN254 twin, at the same three derived constants (absorb
// radix 31, 8 limbs per rate slot, 7 squeezed limbs) — which is a RESULT, not a
// coincidence of design: Pasta and BN254 land on the same three, pinned on the
// Rust side by `dregg_mina_challenger_pack_split_matches_the_eth_wrap`.
//
// ⚑ WHAT `MultiField32Challenger` DOES THAT A READER WOULD GET WRONG:
//
//   1. `observe(F)` buffers BabyBear and auto-flushes at `8 * RATE = 16` — the
//      flush is a PACKED absorb with a LENGTH TAG added into the capacity lane,
//      so absorbing 5 values is not absorbing 5 values then 11 zeros
//      (`multi_field_challenger.rs:150-157`, `duplex_challenger.rs:117-131`).
//   2. `observe(Hash)` FLUSHES pending BabyBear first, then absorbs the digest's
//      Pasta words NATIVELY, in RATE-chunks, with the CHUNK LENGTH as tag —
//      there is no PF -> F -> repack detour (`:181-193`). A verifier that
//      unpacked the root into BabyBear limbs and observed those would get a
//      different transcript, and p3 has a test for exactly that confusion.
//   3. `sample` pops the squeezed limb queue from the BACK, and the queue is
//      filled cell by cell IN ORDER — so the first challenge after a permutation
//      is the SEVENTH limb of the SECOND rate cell, not the first of the first.
//   4. `refill` DRAINS the inner output buffer, so the next empty queue triggers
//      a fresh permutation rather than re-reading the same rate row (`:120-131`).
//   5. `observe` clears BOTH the inner output buffer and the squeeze queue, so a
//      sample after an observe never reads a stale limb.
//   6. `check_witness(0, w)` returns BEFORE observing. The commit-phase PoW is 0
//      bits and is called once per fold layer; a circuit that "checked" them by
//      absorbing the witness would get every beta wrong.
//
// The inner `input_buffer` is never written by this wrapper — every absorb goes
// through `absorb_rate_padded_with_tag`, which clears it — so the `!input_buffer.
// is_empty()` half of `sample`'s duplex condition is dead here and is not
// modelled. That is stated rather than silently dropped.
// ---------------------------------------------------------------------------

/** `squeeze_field_order_num_limbs::<PastaFp, BabyBear>()` — the largest `k` with
 *  `p_BB^(k+1) < p_Pasta`, minus one. Seven: `p^8 ~ 2^247.9 < p_Pasta ~ 2^254.0`
 *  and `p^9` does not fit, so `count = 8` and the last limb (which would carry
 *  bias `>= 1/p`) is DROPPED. */
export const SQUEEZE_NUM_F_ELMS = 7;

/** `r = v div p^7` bound. `p^7 ~ 2^216.94`, `p_Pasta ~ 2^254.00`, so
 *  `floor((p_Pasta - 1) / p^7)` is a 38-bit number. */
export const SPLIT_REM_BITS = 38;

/** `p_BB^0 .. p_BB^7`. */
export const P_POW: bigint[] = (() => {
  const out: bigint[] = [1n];
  for (let i = 0; i < SQUEEZE_NUM_F_ELMS; i++) out.push(out[i] * P_BB);
  return out;
})();

/** The base-`p_BB` digits of `p_Pasta - 1`, low first, with the eighth entry the
 *  remainder `floor((p_Pasta - 1) / p^7)`. The lexicographic bound (d) compares
 *  against these MOST-SIGNIFICANT FIRST. */
export const PASTA_MINUS_ONE_DIGITS: bigint[] = (() => {
  let v = P_PASTA - 1n;
  const out: bigint[] = [];
  for (let i = 0; i < SQUEEZE_NUM_F_ELMS; i++) {
    out.push(v % P_BB);
    v /= P_BB;
  }
  out.push(v);
  return out;
})();

// ===========================================================================
// 1. The out-of-circuit twin. Calls o1js's own `Poseidon` — the same
//    permutation the circuit emits — so a divergence between it and the circuit
//    is a real disagreement. Both are checked against p3's own challenger via
//    the Rust emitter's transcript log.
// ===========================================================================

/** `reduce_packed(vals, 31)` — Horner in base `2^31`, NOT shifted. ⚑ The
 *  challenger's absorb is the UNSHIFTED pack; the MMCS leaf sponge's is the
 *  SHIFTED one (`lane + 1`). Two functions that differ by a constant and are
 *  used ten lines apart is exactly the kind of thing that agrees on the fixture
 *  and diverges on the root, so they are named differently and each says which
 *  p3 function it is. */
export function reducePackedBigInt(vals: bigint[]): bigint {
  let acc = 0n;
  for (let i = vals.length - 1; i >= 0; i--) acc = (acc * RADIX + (vals[i] % P_BB)) % P_PASTA;
  return acc;
}

/** `split_pf_to_field_order_limbs(v, 7)` plus the remainder the circuit pins. */
export function splitPastaBigInt(v: bigint): { limbs: bigint[]; rem: bigint } {
  let rem = v % P_PASTA;
  const limbs: bigint[] = [];
  for (let i = 0; i < SQUEEZE_NUM_F_ELMS; i++) {
    limbs.push(rem % P_BB);
    rem /= P_BB;
  }
  return { limbs, rem };
}

export class PastaChallengerBigInt {
  /** The inner `DuplexChallenger<PastaFp, _, 3, 2>` sponge state. */
  state: bigint[] = [0n, 0n, 0n];
  /** `inner.output_buffer` — up to `RATE` Pasta rate cells. */
  innerOutput: bigint[] = [];
  /** `f_buffer` — pending BabyBear observes, flushed at 16. */
  fBuffer: bigint[] = [];
  /** `f_squeeze_buffer` — BabyBear limbs, POPPED FROM THE END. */
  fSqueeze: bigint[] = [];
  /** Instrumentation: permutations performed. The transcript's whole cost. */
  perms = 0;

  private permute(rate0: bigint, rate1: bigint, capAdd: bigint) {
    const st = Poseidon.update(
      [Field(this.state[0]), Field(this.state[1]), Field(this.state[2] + capAdd)],
      [Field(rate0).sub(Field(this.state[0])), Field(rate1).sub(Field(this.state[1]))],
    );
    this.state = st.map((x) => x.toBigInt());
    this.perms++;
  }

  /** `absorb_rate_padded_with_tag` — overwrite the rate with `values`, ZERO the
   *  unused rate slots, add the length tag into the capacity lane, permute. */
  absorbRatePaddedWithTag(values: bigint[], tag: number) {
    if (values.length > PASTA_RATE) throw new Error('absorb: more values than RATE');
    this.innerOutput = [];
    this.permute(values[0] ?? 0n, values[1] ?? 0n, BigInt(tag));
    this.innerOutput = this.state.slice(0, PASTA_RATE);
  }

  /** `duplexing()` with an empty input buffer: permute, keep the rate. */
  duplexing() {
    this.permute(this.state[0], this.state[1], 0n);
    this.innerOutput = this.state.slice(0, PASTA_RATE);
  }

  flushFIfNonEmpty() {
    if (this.fBuffer.length === 0) return;
    const nIn = this.fBuffer.length;
    const packed: bigint[] = [];
    for (let i = 0; i < nIn; i += LIMBS_PER_SLOT)
      packed.push(reducePackedBigInt(this.fBuffer.slice(i, i + LIMBS_PER_SLOT)));
    this.absorbRatePaddedWithTag(packed, nIn);
    this.fBuffer = [];
    this.fSqueeze = [];
  }

  refillFSqueezeFromInner() {
    this.fSqueeze = [];
    for (const pf of this.innerOutput) this.fSqueeze.push(...splitPastaBigInt(pf).limbs);
    this.innerOutput = [];
  }

  observe(v: bigint) {
    this.innerOutput = [];
    this.fSqueeze = [];
    this.fBuffer.push(((v % P_BB) + P_BB) % P_BB);
    if (this.fBuffer.length === LANES_PER_PERM) this.flushFIfNonEmpty();
  }
  observeSlice(vs: bigint[]) {
    for (const v of vs) this.observe(v);
  }
  /** `observe(Hash<F, PF, 1>)` — the digest's Pasta words absorbed NATIVELY. */
  observeDigest(words: bigint[]) {
    this.innerOutput = [];
    this.fSqueeze = [];
    this.flushFIfNonEmpty();
    for (let i = 0; i < words.length; i += PASTA_RATE) {
      const chunk = words.slice(i, i + PASTA_RATE);
      this.absorbRatePaddedWithTag(chunk, chunk.length);
      this.fSqueeze = [];
    }
  }
  sample(): bigint {
    this.flushFIfNonEmpty();
    if (this.fSqueeze.length === 0) {
      if (this.innerOutput.length === 0) this.duplexing();
      this.refillFSqueezeFromInner();
    }
    return this.fSqueeze.pop()!;
  }
  sampleExt(): bigint[] {
    return Array.from({ length: EXT_D }, () => this.sample());
  }
  sampleBits(bits: number): number {
    return Number(this.sample() & ((1n << BigInt(bits)) - 1n));
  }
  clone(): PastaChallengerBigInt {
    const c = new PastaChallengerBigInt();
    c.state = this.state.slice();
    c.innerOutput = this.innerOutput.slice();
    c.fBuffer = this.fBuffer.slice();
    c.fSqueeze = this.fSqueeze.slice();
    c.perms = this.perms;
    return c;
  }
  checkWitness(bits: number, witness: bigint): boolean {
    if (bits === 0) return true;
    this.observe(witness);
    return this.sampleBits(bits) === 0;
  }
  grind(bits: number): bigint {
    if (bits === 0) return 0n;
    for (let w = 0n; w < P_BB; w++) if (this.clone().checkWitness(bits, w)) return w;
    throw new Error('no PoW witness exists — impossible for bits < log2(p)');
  }
}

// ===========================================================================
// 2. The base-|F| split, in circuit — the soundness core of this module.
// ===========================================================================

/**
 * `split_pf_to_field_order_limbs(v, 7)` in circuit, pinned to the UNIQUE
 * decomposition whose integer value is below `p_Pasta`.
 *
 * The (d) step, spelled out because it is the part that looks optional: walking
 * the digits most-significant first, `eq` is 1 while every digit so far has
 * EQUALLED the modulus digit. While tied, `eq * (D_i - l_i)` must range-check —
 * so `l_i > D_i` wraps modulo Pasta into a ~254-bit number and the check blows.
 * Once strictly below, `eq` is 0 and every later `sel` is 0, so the remaining
 * digits are free. This is exact: the canonical decomposition of ANY `v` always
 * satisfies the bound, so there is no completeness gap.
 */
export function splitToFieldOrderLimbs(v: Field): Field[] {
  const hint = Provable.witness(Provable.Array(Field, SQUEEZE_NUM_F_ELMS + 1), () => {
    const { limbs, rem } = splitPastaBigInt(v.toBigInt());
    return [...limbs, rem].map((x) => Field(x));
  });
  const limbs = hint.slice(0, SQUEEZE_NUM_F_ELMS);
  const rem = hint[SQUEEZE_NUM_F_ELMS];

  // (a) every limb is a CANONICAL BabyBear element; (b) `r < 2^38`.
  for (const l of limbs) assertCanonicalBb(l);
  assertLtPow2Pasta(rem, SPLIT_REM_BITS);

  // (c) the recomposition. Cannot wrap, because (d) bounds the integer value.
  let acc = Field(0);
  for (let i = 0; i < SQUEEZE_NUM_F_ELMS; i++) acc = acc.add(limbs[i].mul(Field(P_POW[i])));
  acc = acc.add(rem.mul(Field(P_POW[SQUEEZE_NUM_F_ELMS])));
  acc.assertEquals(v);

  // (d) lexicographic canonicity against the digits of `p_Pasta - 1`.
  let eq = Field(1);
  const lexStep = (l: Field, digit: bigint, bits: number) => {
    const sel = eq.mul(Field(digit).sub(l));
    assertLtPow2Pasta(sel, bits);
    eq = eq.mul(l.equals(Field(digit)).toField());
  };
  lexStep(rem, PASTA_MINUS_ONE_DIGITS[SQUEEZE_NUM_F_ELMS], SPLIT_REM_BITS);
  for (let i = SQUEEZE_NUM_F_ELMS - 1; i >= 0; i--) lexStep(limbs[i], PASTA_MINUS_ONE_DIGITS[i], 31);

  return limbs;
}

/** `reduce_packed(lanes, 31)` in circuit — UNSHIFTED, the challenger's pack.
 *  Every lane is range-checked to `< 2^31` here, which is what makes the pack
 *  injective into Pasta. */
export function packSlotUnshifted(lanes: Field[]): Field {
  let acc = Field(0);
  for (let i = lanes.length - 1; i >= 0; i--) {
    assertLt2p31(lanes[i]);
    acc = acc.mul(Field(RADIX)).add(lanes[i]);
  }
  return acc;
}

// ===========================================================================
// 3. The in-circuit challenger.
// ===========================================================================

/**
 * ⚑ THE SCHEDULE IS COMPILE-TIME, THE VALUES ARE NOT — the same property that
 * makes the BabyBear challenger affordable. A verifier's observe/sample
 * sequence is fixed by the protocol parameters, so `fBuffer`, `innerOutput` and
 * `fSqueeze` are plain JS arrays whose LENGTHS are known while the circuit is
 * built, and the whole state machine unrolls into straight-line constraints with
 * no `Provable.if` on a buffer position anywhere.
 */
export class PastaChallenger {
  state: [Field, Field, Field] = [Field(0), Field(0), Field(0)];
  innerOutput: Field[] = [];
  fBuffer: Field[] = [];
  fSqueeze: Field[] = [];
  /** Instrumentation, out of circuit: permutations emitted so far. */
  perms = 0;

  private permuteInto(rate0: Field, rate1: Field, capAdd: bigint) {
    const cap = capAdd === 0n ? this.state[2] : this.state[2].add(Field(capAdd));
    this.state = Poseidon.update(
      [this.state[0], this.state[1], cap],
      [rate0.sub(this.state[0]), rate1.sub(this.state[1])],
    ) as [Field, Field, Field];
    this.perms++;
  }

  absorbRatePaddedWithTag(values: Field[], tag: number) {
    if (values.length > PASTA_RATE) throw new Error('absorb: more values than RATE');
    this.innerOutput = [];
    this.permuteInto(values[0] ?? Field(0), values[1] ?? Field(0), BigInt(tag));
    this.innerOutput = this.state.slice(0, PASTA_RATE);
  }

  duplexing() {
    this.permuteInto(this.state[0], this.state[1], 0n);
    this.innerOutput = this.state.slice(0, PASTA_RATE);
  }

  flushFIfNonEmpty() {
    if (this.fBuffer.length === 0) return;
    const nIn = this.fBuffer.length;
    const packed: Field[] = [];
    for (let i = 0; i < nIn; i += LIMBS_PER_SLOT)
      packed.push(packSlotUnshifted(this.fBuffer.slice(i, i + LIMBS_PER_SLOT)));
    this.absorbRatePaddedWithTag(packed, nIn);
    this.fBuffer = [];
    this.fSqueeze = [];
  }

  refillFSqueezeFromInner() {
    this.fSqueeze = [];
    for (const pf of this.innerOutput) this.fSqueeze.push(...splitToFieldOrderLimbs(pf));
    this.innerOutput = [];
  }

  /** Absorb one BabyBear value. It is a WITNESS, so the pack's injectivity
   *  bound is enforced at the pack — see `packSlotUnshifted`. */
  observe(v: Field) {
    this.innerOutput = [];
    this.fSqueeze = [];
    this.fBuffer.push(v);
    if (this.fBuffer.length === LANES_PER_PERM) this.flushFIfNonEmpty();
  }
  observeSlice(vs: Field[]) {
    for (const v of vs) this.observe(v);
  }
  /** `observe(Hash<BabyBear, PastaFp, 1>)` — NATIVE Pasta words, no repack. */
  observeDigest(d: PastaDigest) {
    this.innerOutput = [];
    this.fSqueeze = [];
    this.flushFIfNonEmpty();
    const words = d.limbs;
    for (let i = 0; i < words.length; i += PASTA_RATE) {
      const chunk = words.slice(i, i + PASTA_RATE);
      this.absorbRatePaddedWithTag(chunk, chunk.length);
      this.fSqueeze = [];
    }
  }
  /** `observe_algebra_element` — the limbs, in basis order. */
  observeExt(e: BbExt) {
    this.observeSlice(e.limbs);
  }
  /** A COMPILE-TIME constant: protocol data, not proof data. */
  observeConstant(c: bigint) {
    this.observe(Field(c));
  }

  /** One base-field challenge. It is a limb of the split, hence already
   *  CANONICAL — `assertCanonicalBb` inside the split is what makes that true
   *  rather than hoped. */
  sample(): Field {
    this.flushFIfNonEmpty();
    if (this.fSqueeze.length === 0) {
      if (this.innerOutput.length === 0) this.duplexing();
      this.refillFSqueezeFromInner();
    }
    return this.fSqueeze.pop()!;
  }
  sampleExt(): BbExt {
    return new BbExt({ limbs: Array.from({ length: EXT_D }, () => this.sample()) });
  }

  /** `sample_bits(k)` returning the BITS — the shape a FRI query index needs.
   *  A canonical sample `c < p < 2^31` splits as `c = hi*2^k + sum b_i 2^i` with
   *  every `b_i` boolean and `hi < 2^(31-k)`; both bounds are load-bearing. */
  sampleBitsAsBits(k: number): Bool[] {
    if (k < 1 || k > 30) throw new Error(`sampleBitsAsBits: k=${k} out of range`);
    const c = this.sample();
    const bits = Provable.witness(Provable.Array(Bool, k), () => {
      const v = c.toBigInt();
      return Array.from({ length: k }, (_, i) => Bool(((v >> BigInt(i)) & 1n) === 1n));
    });
    const hi = Provable.witness(Field, () => Field(c.toBigInt() >> BigInt(k)));
    assertLowBitsSplit(c, bits, hi, k);
    return bits;
  }

  /** `check_witness(bits, w)`, ASSERTED. ⚑ At `bits == 0` this observes NOTHING
   *  — `grinding_challenger.rs:41-43` — and the commit-phase PoW is 0 bits, once
   *  per fold layer. */
  assertCheckWitness(bits: number, witness: Field) {
    if (bits === 0) return;
    this.observe(witness);
    const c = this.sample();
    const hi = Provable.witness(Field, () => Field(c.toBigInt() >> BigInt(bits)));
    assertLowBitsZero(c, hi, bits);
  }
}

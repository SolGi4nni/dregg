import { Bool, Field, Provable, Struct, ZkProgram } from 'o1js';
import { P, canonicalLane, reduceLane } from './Poseidon2BabyBearW16.js';
import {
  BbDigest,
  DEPLOYED_COMMIT_LAYERS,
  DEPLOYED_INPUT_PHASE_DEPTH,
  assertDigestInRange,
  babyBearMerkleSuite,
  compressBB,
  condSwap,
  spongeBB,
} from './Poseidon2Merkle.js';
import type { Digestish, MerkleSuite } from './HashSuiteType.js';
import { assertLaneLt2p31 } from './Poseidon2BabyBearW16.js';

// ---------------------------------------------------------------------------
// RUNG 2 — ONE FRI QUERY at the DEPLOYED root's geometry, as an o1js circuit.
//
// `verify_query` (vendor/plonky3-fri-82cfad73/src/verifier.rs:363-500) is, per
// query: an input-phase MMCS opening, then for each commit-phase round —
// reconstruct the arity-2 evaluation row from the running folded value and the
// sibling, verify that row's opening against the round's commitment, and fold
// the two evaluations at `beta`. The deployed root's knobs
// (MINA-VERIFIES-DREGG-FRI-SIZE §1.2, all re-derived from source there):
//
//     |D^0| = 2^22   log_blowup = 6   num_queries = 19
//     max_log_arity = 1  (IT FOLDS BY 2 — the "arity 3" in
//                         `ir2_leaf_wrap_config`'s doc-comment describes the
//                         INNER batch, a documented name collision)
//     log_final_height = 6, so (22 - 6)/1 = 16 commit-phase layers
//     cap_height = 0, so no path is ever truncated
//
// ⚑ THE INDEX IS ONE OBJECT, AND IT DOES THREE JOBS AT THREE OFFSETS. The 22
// query-index bits are supplied ONCE and reused: bit `r` selects which slot
// round `r`'s folded value occupies; bits `r+1..22` are the Merkle path
// directions for round `r`'s depth-`21-r` opening; and bit `r+1` — NOT bit `r`
// — carries the sign of round `r`'s coset descent. The third of those was
// WRONG here until the 16-layer chain was checked against p3's own chain; see
// `commitPhaseRound`. A circuit that witnessed a fresh index per round would
// measure the same and verify something strictly weaker.
//
// ⚑ WHAT THIS RUNG IS NOT. It is the FRI FOLD CHAIN. It is not the DEEP
// quotient (the `(f(zeta) - f(x))/(zeta - x)` reduced openings and their alpha
// powers), and not the AIR constraint evaluation. Those are separate cost
// centres and neither is priced here.
//
// ⚑ AND ONE THING IT WAS NOT, WHICH IT NOW IS. This header used to say `beta`
// and the query index were witnessed "precisely because binding them to a
// transcript is the part that is missing". `FriChallenger.ts` is that binding —
// it derives `alpha`, every `beta`, the 16-bit query PoW and every query index
// from a `DuplexChallenger` transcript KAT'd against the deployed one, and
// `makeDerivedQueryProgram` joins the derivation to the walk in one statement.
// The witnessed forms below survive because they are what `getRows()` prices;
// the DERIVED form is what a verifier would run.
// ---------------------------------------------------------------------------

/** `BinomialExtensionField<BabyBear, 4>`; `X^4 = W`. `EXT_W` is checked against
 *  p3's own extension multiplication by the Rust probe's
 *  `ext_w_is_the_deployed_constant`, not asserted here. */
export const EXT_D = 4;
export const EXT_W = 11n;

/** An extension element, coefficient basis. Lanes are kept `< 2^31`. */
export class BbExt extends Struct({ limbs: Provable.Array(Field, EXT_D) }) {
  static from(v: bigint[] | Field[]): BbExt {
    return new BbExt({ limbs: v.map((x) => (typeof x === 'bigint' ? Field(x) : x)) });
  }
  static zero(): BbExt {
    return BbExt.from([0n, 0n, 0n, 0n]);
  }
  toBigInts(): bigint[] {
    return this.limbs.map((x) => x.toBigInt() % P);
  }
}

// ===========================================================================
// 1. Out-of-circuit twins (the `p2fold` referent's shape).
// ===========================================================================

const md = (x: bigint) => ((x % P) + P) % P;
export const extAddBigInt = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x + b[i]));
export const extSubBigInt = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x - b[i]));
export function extMulBigInt(a: bigint[], b: bigint[]): bigint[] {
  const acc = Array(2 * EXT_D - 1).fill(0n) as bigint[];
  for (let i = 0; i < EXT_D; i++)
    for (let j = 0; j < EXT_D; j++) acc[i + j] = md(acc[i + j] + a[i] * b[j]);
  return Array.from({ length: EXT_D }, (_, i) =>
    i + EXT_D < 2 * EXT_D - 1 ? md(acc[i] + EXT_W * acc[i + EXT_D]) : acc[i],
  );
}
export const extScaleBigInt = (a: bigint[], s: bigint) => a.map((x) => md(x * s));
export const extOfBaseBigInt = (s: bigint) => [md(s), 0n, 0n, 0n];

function invBigInt(a: bigint): bigint {
  // p is prime; a^(p-2).
  let r = 1n;
  let b = md(a);
  let e = P - 2n;
  while (e > 0n) {
    if (e & 1n) r = md(r * b);
    b = md(b * b);
    e >>= 1n;
  }
  return r;
}

/** `fold_row` at `log_arity = 1`: two-point Lagrange through `(x, eEven)` and
 *  `(-x, eOdd)`, evaluated at `beta`. */
export function foldRowArity2BigInt(
  x: bigint,
  beta: bigint[],
  eEven: bigint[],
  eOdd: bigint[],
): bigint[] {
  const num = extSubBigInt(
    extMulBigInt(eEven, extAddBigInt(beta, extOfBaseBigInt(x))),
    extMulBigInt(eOdd, extSubBigInt(beta, extOfBaseBigInt(x))),
  );
  return extScaleBigInt(num, invBigInt(md(2n * x)));
}

// ===========================================================================
// 2. The in-circuit extension arithmetic.
// ===========================================================================

const LANE_MAX = (1n << 31n) - 1n;

/** Range-check every lane of a witnessed extension element. */
export function assertExtInRange(e: BbExt) {
  for (const l of e.limbs) assertLaneLt2p31(l);
}

export function extAdd(a: BbExt, b: BbExt): BbExt {
  // a + b <= 2*(2^31-1); one reduce brings it back into the lane budget.
  return new BbExt({ limbs: a.limbs.map((x, i) => reduceLane(x.add(b.limbs[i]), 2n * LANE_MAX)) });
}
export function extSub(a: BbExt, b: BbExt): BbExt {
  // Add p to keep the representative non-negative before reducing.
  return new BbExt({
    limbs: a.limbs.map((x, i) => reduceLane(x.add(Field(P)).sub(b.limbs[i]), LANE_MAX + P)),
  });
}
/** Schoolbook multiply, reduce by `X^4 - W`, then one `mod p` per output lane.
 *  The unreduced accumulator peaks at `37 * (2^31)^2 ~ 2^67.3`, far under the
 *  Pasta modulus, so the whole product rides on native arithmetic. */
export function extMul(a: BbExt, b: BbExt): BbExt {
  const acc: Field[] = Array.from({ length: 2 * EXT_D - 1 }, () => Field(0));
  for (let i = 0; i < EXT_D; i++)
    for (let j = 0; j < EXT_D; j++) acc[i + j] = acc[i + j].add(a.limbs[i].mul(b.limbs[j]));
  const out: Field[] = [];
  for (let i = 0; i < EXT_D; i++) {
    const v = i + EXT_D < 2 * EXT_D - 1 ? acc[i].add(acc[i + EXT_D].mul(EXT_W)) : acc[i];
    // acc[k] holds at most 4 products of two <2^31 values; the W-fold adds 11x
    // of another such accumulator.
    out.push(reduceLane(v, 4n * LANE_MAX * LANE_MAX * (1n + EXT_W)));
  }
  return new BbExt({ limbs: out });
}
/** Scale by a base-field element (`< 2^31`). */
export function extScale(a: BbExt, s: Field): BbExt {
  return new BbExt({ limbs: a.limbs.map((x) => reduceLane(x.mul(s), LANE_MAX * LANE_MAX)) });
}
export function extOfBase(s: Field): BbExt {
  return new BbExt({ limbs: [s, Field(0), Field(0), Field(0)] });
}

/** `1/a` for a base-field element: witness the inverse, check `a * inv = 1`
 *  mod p. The check is over the INTEGERS with a witnessed quotient, so it is a
 *  `reduce` of the product against the constant 1. */
export function baseInverse(a: Field): Field {
  const inv = Provable.witness(Field, () => Field(invBigInt(a.toBigInt())));
  assertLaneLt2p31(inv);
  const prod = reduceLane(a.mul(inv), LANE_MAX * LANE_MAX);
  canonicalLane(prod, LANE_MAX).assertEquals(Field(1));
  return inv;
}

/** `fold_row` at arity 2, in circuit. */
export function foldRowArity2(x: Field, beta: BbExt, eEven: BbExt, eOdd: BbExt): BbExt {
  const xe = extOfBase(x);
  const num = extSub(extMul(eEven, extAdd(beta, xe)), extMul(eOdd, extSub(beta, xe)));
  const twoX = reduceLane(x.add(x), 2n * LANE_MAX);
  return extScale(num, baseInverse(twoX));
}

/** `x_{r+1} = (-1)^{b} * x_r^2` — the coset point descent
 *  (`p2bb.rs::next_coset_point`, pinned by
 *  `coset_points_descend_by_squaring_and_a_sign`). One squaring and a
 *  conditional negation, on a bit the circuit has already witnessed. */
export function nextCosetPoint(x: Field, bit: Bool): Field {
  const sq = canonicalLane(x.mul(x), LANE_MAX * LANE_MAX);
  const neg = Field(P).sub(sq);
  return Provable.if(bit, neg, sq);
}

// ===========================================================================
// 3. One commit-phase round.
// ===========================================================================

export type CommitRound = {
  /** The sibling evaluation: the OTHER slot of this round's arity-2 row. */
  sibling: BbExt;
  /** The Merkle path for this round's opening (depth = folded log height).
   *  ⚑ `Digestish` rather than `BbDigest`: this chain is hash-agnostic and is
   *  the SAME code for a `DreggMinaConfig` proof's Pasta digests. See
   *  `HashSuiteType.ts` for why there is not a second copy of it. */
  path: Digestish[];
  /** `beta` for this round. */
  beta: BbExt;
  /** The MMCS root this round's row must open under. */
  commit: Digestish;
};

/**
 * One round of `verify_query`:
 *   1. reconstruct the arity-2 row `[even, odd]` from the running folded value
 *      and the sibling, ordered by the index bit (`index_in_group`);
 *   2. hash that row with the deployed leaf sponge and verify its opening
 *      against `commit` along `path`;
 *   3. fold to the parent evaluation at `beta`;
 *   4. descend the coset point for the NEXT round.
 *
 * `slotBit` is the index bit consumed at this round; `pathBits` are the
 * remaining, higher bits — the SAME bits, which is what makes the openings a
 * consistent walk rather than 17 unrelated ones.
 *
 * ⚑ `descentBit` IS NOT `slotBit`, AND THIS WAS WRONG HERE FOR A DAY.
 * `verify_query` shifts the index BEFORE it folds, so round `r` folds at
 * `i_r = index >> (r+1)` and height `L_r`. The descent
 * `x_{r+1} = (-1)^b * x_r^2` is driven by the low bit of `i_r`
 * (`coset_points_descend_by_squaring_and_a_sign`, p2bb.rs) — which is
 * `indexBits[r+1]`, one PAST the bit that chose the slot. Passing `slotBit`
 * agrees whenever two consecutive index bits happen to be equal, i.e. on about
 * half of every chain's rounds and on 100% of a chain whose index is all-zero —
 * which is what `getRows()` witnesses. It was caught only by chaining sixteen
 * rounds against p3's own chain (`p2chain`); no single-round check can see it,
 * because a single round never consumes two bits.
 */
export function commitPhaseRound(
  folded: BbExt,
  x: Field,
  slotBit: Bool,
  descentBit: Bool,
  pathBits: Bool[],
  round: CommitRound,
  /** The MMCS hash. Defaults to the deployed BabyBear one so every existing
   *  caller and every measured row count in this arc is unchanged; a
   *  `DreggMinaConfig` proof passes `pastaMerkleSuite` and runs THIS function,
   *  not a second copy of it. */
  suite: MerkleSuite = babyBearMerkleSuite,
): { folded: BbExt; x: Field } {
  assertExtInRange(round.sibling);
  assertExtInRange(round.beta);

  // The row, in domain order: slot 0 is the even point, slot 1 the odd one.
  const even: Field[] = [];
  const odd: Field[] = [];
  for (let i = 0; i < EXT_D; i++) {
    even.push(Provable.if(slotBit, round.sibling.limbs[i], folded.limbs[i]));
    odd.push(Provable.if(slotBit, folded.limbs[i], round.sibling.limbs[i]));
  }
  const eEven = new BbExt({ limbs: even });
  const eOdd = new BbExt({ limbs: odd });

  // The MMCS leaf for this row: an 8-element BabyBear row. Under the deployed
  // `PaddingFreeSponge<.,16,8,8>` that is exactly ONE permutation (one full
  // block, no pad); under the Pasta `MultiField32PaddingFreeSponge<.,3,2,1>` it
  // is also one, because sixteen lanes ride a permutation and eight is a
  // partial block. The lanes came out of `assertExtInRange` above, so the sponge
  // is told not to bound them again.
  let cur = suite.sponge([...even, ...odd], true);
  for (let h = 0; h < round.path.length; h++) {
    suite.assertInRange(round.path[h]);
    const [l, r] = suite.condSwap(cur, round.path[h], pathBits[h]);
    cur = suite.compress(l, r);
  }
  suite.assertEq(cur, round.commit);

  return {
    folded: foldRowArity2(x, round.beta, eEven, eOdd),
    x: nextCosetPoint(x, descentBit),
  };
}

/**
 * The BabyBear 2-adic generator of order `2^k`, as a compile-time constant.
 * BabyBear `p - 1 = 2^27 * 15`, and `31` is a generator of the multiplicative
 * group, so `g_k = 31^((p-1)/2^k)`.
 */
export function twoAdicGenerator(k: number): bigint {
  if (k > 27) throw new Error(`BabyBear has no 2^${k} root of unity (2-adicity is 27)`);
  let e = (P - 1n) / (1n << BigInt(k));
  let b = 31n;
  let r = 1n;
  while (e > 0n) {
    if (e & 1n) r = md(r * b);
    b = md(b * b);
    e >>= 1n;
  }
  return r;
}

/**
 * `g_{logOrder} ^ reverse_bits_len(index, revLen)`, with `index`'s bits given
 * low-first, as a product of COMPILE-TIME constants selected by the bits.
 *
 * `reverse_bits_len(i, R) = sum_j bit_j * 2^(R-1-j)`, so the exponent
 * decomposes and each bit contributes a fixed `g^(2^(R-1-j))`. That is `n`
 * conditional multiplications instead of an exponentiation, and — the point —
 * it BINDS the domain point to the index instead of trusting a witness for it.
 *
 * `bits` may be SHORTER than `revLen`: the missing high bits are zero, which is
 * exactly the situation at the end of the fold chain, where the index has been
 * shifted down but the reversal length is still the original one.
 */
export function powTwoAdicRevBits(bits: Bool[], logOrder: number, revLen: number): Field {
  if (bits.length > revLen) throw new Error('powTwoAdicRevBits: more bits than revLen');
  const g = twoAdicGenerator(logOrder);
  let acc = Field(1);
  for (let i = 0; i < bits.length; i++) {
    let c = g;
    for (let k = 0; k < revLen - 1 - i; k++) c = md(c * c);
    const scaled = reduceLane(acc.mul(Field(c)), LANE_MAX * LANE_MAX);
    acc = Provable.if(bits[i], scaled, acc);
  }
  return acc;
}

/**
 * The first coset point, DERIVED from the witnessed index bits rather than
 * witnessed alongside them.
 *
 * `fold_row` uses `g_{L+1} ^ reverse_bits_len(index, L)`, with `index` the
 * already-shifted index at folded height `L`.
 */
export function cosetPointFromBits(bits: Bool[], logHeight: number): Field {
  if (bits.length !== logHeight) throw new Error('cosetPointFromBits: bit count != logHeight');
  return powTwoAdicRevBits(bits, logHeight + 1, logHeight);
}

/**
 * The point at which the FINAL polynomial is evaluated:
 * `g_{log_global_max_height} ^ reverse_bits_len(domain_index, log_global_max_height)`
 * (`fri/src/verifier.rs:296-297`), where `domain_index` is what is LEFT of the
 * query index after every fold has shifted it down.
 *
 * ⚑ At the deployed knobs this value is dead weight: `log_final_poly_len = 0`
 * means the final polynomial is a single coefficient and Horner returns it
 * regardless of the point. It is computed anyway because the parameter is a
 * knob, and a verifier that skipped it would be wrong the moment the knob moved
 * — but the row cost is charged to a term the deployed shape does not need, and
 * §3.12 says so.
 */
export function finalEvalPointFromBits(
  remainingBits: Bool[],
  logGlobalMaxHeight: number,
): Field {
  return powTwoAdicRevBits(remainingBits, logGlobalMaxHeight, logGlobalMaxHeight);
}

/** `a^(2^k)` — the roll-in factor `beta^arity` at `arity = 2^k`. */
export function extPowPow2(a: BbExt, k: number): BbExt {
  let r = a;
  for (let i = 0; i < k; i++) r = extMul(r, r);
  return r;
}

/** Horner over the extension: `sum_i c_i x^i` at a base-field point `x`.
 *  p3 starts the accumulator at ZERO and folds `final_poly` in reverse
 *  (`verifier.rs:302-305`); starting at the top coefficient is the same value
 *  without the degenerate first multiply. */
export function evalFinalPoly(coeffs: BbExt[], x: Field): BbExt {
  if (coeffs.length === 0) throw new Error('evalFinalPoly: no coefficients');
  let acc = coeffs[coeffs.length - 1];
  for (let i = coeffs.length - 2; i >= 0; i--) acc = extAdd(extScale(acc, x), coeffs[i]);
  return acc;
}

/** The bigint twin of `evalFinalPoly`. */
export function evalFinalPolyBigInt(coeffs: bigint[][], x: bigint): bigint[] {
  let acc = coeffs[coeffs.length - 1];
  for (let i = coeffs.length - 2; i >= 0; i--)
    acc = extAddBigInt(extScaleBigInt(acc, x), coeffs[i]);
  return acc;
}

// ===========================================================================
// 4. The whole query.
// ===========================================================================

export type QueryWitness = {
  /** The query index, low bit first; `logD0` of them. */
  indexBits: Bool[];
  /** The opened input-phase row and its path (depth `logD0`). */
  inputRow: Field[];
  inputPath: Digestish[];
  inputCommit: Digestish;
  /** The MMCS hash. Defaults to the deployed BabyBear suite. */
  suite?: MerkleSuite;
  /** The reduced opening rolled in at the top height — a witnessed extension
   *  value. ⚑ Binding it to `inputRow` is the DEEP quotient, NOT this rung. */
  reducedOpening: BbExt;
  rounds: CommitRound[];
};

// ===========================================================================
// 4b. The COMMIT PHASE — all layers as ONE object.
// ===========================================================================

/**
 * A reduced opening rolled in partway down the chain.
 *
 * `verify_query` adds `beta_r^arity * ro` to the folded evaluation AFTER round
 * `r`'s fold, whenever an input matrix's height equals that round's folded
 * height (`fri/src/verifier.rs:470-474`). At the deployed shape the number of
 * such roll-ins is the number of DISTINCT input-matrix heights below the top,
 * which is a function of the root's `degree_bits` — and §1.3 records that no
 * committed measurement of the root's own `degree_bits` exists. So the schedule
 * is a PARAMETER here and the marginal cost per roll-in is reported separately,
 * rather than a count being invented.
 */
export type RollIn = {
  /** The round AFTER whose fold this opening is added (0-based). */
  afterRound: number;
  value: BbExt;
};

export type CommitPhaseWitness = {
  /** The query index, low bit first; `logD0` of them. Bit `r` is round `r`'s
   *  slot selector AND bits `r+1..` are round `r`'s path directions — one
   *  object, which is what makes the openings a consistent walk. */
  indexBits: Bool[];
  /** The evaluation the chain starts from: the reduced opening at the top
   *  height. ⚑ Binding it to the input-phase row is the DEEP quotient. */
  initial: BbExt;
  rounds: CommitRound[];
  /** Compile-time schedule; may be empty. */
  rollIns: RollIn[];
  /** `proof.final_poly`, `2^log_final_poly_len` coefficients. When present the
   *  chain's landing value is ASSERTED equal to its evaluation — the check that
   *  makes the walk closed rather than open-ended. */
  finalPoly?: BbExt[];
  /** `log_global_max_height`, for the final evaluation point. Defaults to
   *  `logD0`. */
  logGlobalMaxHeight?: number;
  /** The MMCS hash. Defaults to the deployed BabyBear suite. */
  suite?: MerkleSuite;
};

/**
 * **The Rung-4 statement.** The whole commit phase: `rounds.length` rounds of
 * reconstruct-open-fold sharing ONE index, the roll-ins at their scheduled
 * heights, and — when a final polynomial is supplied — the closing check that
 * the chain lands on its evaluation.
 *
 * Rung 2 proved one round. A chain of rounds is not `n` copies of one round:
 * the index is shared, the coset point descends by `(-1)^b x^2` sixteen times
 * with the sign taken from the same bit that selected the slot, and the landing
 * value has to MEAN something. All three are properties of the chain and none
 * is visible in a single round.
 */
export function verifyCommitPhase(w: CommitPhaseWitness): { folded: BbExt; x: Field } {
  const logD0 = w.indexBits.length;
  const layers = w.rounds.length;
  if (w.rollIns.some((r) => r.afterRound < 0 || r.afterRound >= layers))
    throw new Error('a roll-in is scheduled outside the fold chain');

  assertExtInRange(w.initial);
  let folded = w.initial;
  let x = cosetPointFromBits(w.indexBits.slice(1), logD0 - 1);

  for (let r = 0; r < layers; r++) {
    const out = commitPhaseRound(
      folded,
      x,
      w.indexBits[r],
      // The descent bit is the NEXT one — see `commitPhaseRound`. At the last
      // possible round there is none, and the returned `x` is unused.
      r + 1 < logD0 ? w.indexBits[r + 1] : Bool(false),
      w.indexBits.slice(r + 1, logD0),
      w.rounds[r],
      w.suite ?? babyBearMerkleSuite,
    );
    folded = out.folded;
    x = out.x;
    // The roll-in uses `beta^arity`, arity = 2 at the deployed max_log_arity.
    for (const ri of w.rollIns) {
      if (ri.afterRound !== r) continue;
      assertExtInRange(ri.value);
      folded = extAdd(folded, extMul(extPowPow2(w.rounds[r].beta, 1), ri.value));
    }
  }

  if (w.finalPoly !== undefined) {
    for (const c of w.finalPoly) assertExtInRange(c);
    const lgmh = w.logGlobalMaxHeight ?? logD0;
    const xFinal = finalEvalPointFromBits(w.indexBits.slice(layers), lgmh);
    const want = evalFinalPoly(w.finalPoly, xFinal);
    for (let j = 0; j < EXT_D; j++)
      canonicalLane(folded.limbs[j], LANE_MAX).assertEquals(
        canonicalLane(want.limbs[j], LANE_MAX),
      );
  }
  return { folded, x };
}

/**
 * **The Rung-2 statement.** One FRI query, end to end: the input-phase opening,
 * then `rounds.length` commit-phase rounds of open-and-fold, returning the
 * evaluation the chain lands on. The caller compares it to the claimed final
 * polynomial's evaluation.
 */
export function verifyQuery(w: QueryWitness): BbExt {
  const logD0 = w.indexBits.length;
  if (w.inputPath.length !== logD0)
    throw new Error(`inputPath depth ${w.inputPath.length} != logD0 ${logD0}`);
  if (w.rounds.some((r, i) => r.path.length !== logD0 - 1 - i))
    throw new Error('a commit-phase path is not at its round height');

  // -- input phase: hash the opened row, walk it to the input commitment.
  const suite = w.suite ?? babyBearMerkleSuite;
  let cur = suite.sponge(w.inputRow);
  for (let h = 0; h < logD0; h++) {
    suite.assertInRange(w.inputPath[h]);
    const [l, r] = suite.condSwap(cur, w.inputPath[h], w.indexBits[h]);
    cur = suite.compress(l, r);
  }
  suite.assertEq(cur, w.inputCommit);

  // -- commit phase.
  return verifyCommitPhase({
    indexBits: w.indexBits,
    initial: w.reducedOpening,
    rounds: w.rounds,
    rollIns: [],
    suite,
  }).folded;
}

/** The deployed root's query shape, for measurement: `|D^0| = 2^22`, 16 arity-2
 *  commit-phase layers at depths 21..6, `cap_height = 0`. */
export function deployedQueryShape(inputRowWidth: number) {
  return {
    logD0: DEPLOYED_INPUT_PHASE_DEPTH,
    layers: DEPLOYED_COMMIT_LAYERS,
    inputRowWidth,
    commitDepths: Array.from(
      { length: DEPLOYED_COMMIT_LAYERS },
      (_, i) => DEPLOYED_INPUT_PHASE_DEPTH - 1 - i,
    ),
  };
}

/** Witness a whole query of the given shape, all-zero — for `getRows()`. The
 *  values are irrelevant to the row count; the SHAPE is not. */
export function witnessQueryShape(logD0: number, layers: number, inputRowWidth: number): QueryWitness {
  const wit = <T>(f: () => T, t: any) => Provable.witness(t, f);
  return {
    indexBits: Array.from({ length: logD0 }, () => wit(() => Bool(false), Bool)),
    inputRow: Array.from({ length: inputRowWidth }, () => wit(() => Field(1), Field)),
    inputPath: Array.from({ length: logD0 }, () => wit(() => BbDigest.zero(), BbDigest)),
    inputCommit: wit(() => BbDigest.zero(), BbDigest),
    reducedOpening: wit(() => BbExt.zero(), BbExt),
    rounds: Array.from({ length: layers }, (_, i) => ({
      sibling: wit(() => BbExt.zero(), BbExt),
      path: Array.from({ length: logD0 - 1 - i }, () => wit(() => BbDigest.zero(), BbDigest)),
      beta: wit(() => BbExt.zero(), BbExt),
      commit: wit(() => BbDigest.zero(), BbDigest),
    })),
  };
}

/** Witness a commit-phase chain of the given shape — for `getRows()`. */
export function witnessCommitPhaseShape(
  logD0: number,
  layers: number,
  pathDepths: number[],
  rollInRounds: number[],
  finalPolyLen: number,
): CommitPhaseWitness {
  const wit = <T>(f: () => T, t: any) => Provable.witness(t, f);
  return {
    indexBits: Array.from({ length: logD0 }, () => wit(() => Bool(false), Bool)),
    initial: wit(() => BbExt.zero(), BbExt),
    rounds: Array.from({ length: layers }, (_, i) => ({
      sibling: wit(() => BbExt.zero(), BbExt),
      path: Array.from({ length: pathDepths[i] }, () => wit(() => BbDigest.zero(), BbDigest)),
      beta: wit(() => BbExt.zero(), BbExt),
      commit: wit(() => BbDigest.zero(), BbDigest),
    })),
    rollIns: rollInRounds.map((r) => ({ afterRound: r, value: wit(() => BbExt.zero(), BbExt) })),
    finalPoly:
      finalPolyLen > 0
        ? Array.from({ length: finalPolyLen }, () => wit(() => BbExt.zero(), BbExt))
        : undefined,
    logGlobalMaxHeight: logD0,
  };
}

/** The bigint twin of the commit phase, for the KAT. Returns the landing value
 *  and the coset point at every layer, so a divergence localises to a round
 *  rather than to "the chain". */
export function verifyCommitPhaseBigInt(w: {
  indexBits: boolean[];
  initial: bigint[];
  betas: bigint[][];
  siblings: bigint[][];
  rollIns: { afterRound: number; value: bigint[] }[];
}): { folded: bigint[]; xs: bigint[] } {
  const logD0 = w.indexBits.length;
  const layers = w.betas.length;
  let folded = w.initial;
  // `g_{L+1} ^ reverse_bits_len(index >> 1, L)` at L = logD0 - 1.
  let idx = 0n;
  for (let i = 1; i < logD0; i++) if (w.indexBits[i]) idx |= 1n << BigInt(i - 1);
  const L = logD0 - 1;
  let rev = 0n;
  for (let i = 0; i < L; i++) if ((idx >> BigInt(i)) & 1n) rev |= 1n << BigInt(L - 1 - i);
  let x = 1n;
  {
    let b = twoAdicGenerator(L + 1);
    let e = rev;
    while (e > 0n) {
      if (e & 1n) x = md(x * b);
      b = md(b * b);
      e >>= 1n;
    }
  }
  const xs = [x];
  for (let r = 0; r < layers; r++) {
    const even = w.indexBits[r] ? w.siblings[r] : folded;
    const odd = w.indexBits[r] ? folded : w.siblings[r];
    folded = foldRowArity2BigInt(x, w.betas[r], even, odd);
    const sq = md(x * x);
    // ⚑ The descent sign is bit r+1, NOT the slot bit r — `verify_query` shifts
    // the index before it folds. See `commitPhaseRound`.
    x = r + 1 < logD0 && w.indexBits[r + 1] ? md(P - sq) : sq;
    xs.push(x);
    for (const ri of w.rollIns) {
      if (ri.afterRound !== r) continue;
      folded = extAddBigInt(folded, extMulBigInt(extMulBigInt(w.betas[r], w.betas[r]), ri.value));
    }
  }
  return { folded, xs };
}

/**
 * **The Rung-4 program.** All `layers` commit-phase rounds as ONE `ZkProgram`.
 *
 * ⚑ THE PATH DEPTHS ARE A PARAMETER, AND THE PROVABLE INSTANCE RUNS THEM AT
 * ZERO. The deployed chain's Merkle paths (depths 21..6, 216 levels) are two
 * orders of magnitude past one Kimchi domain — that is §3.10's measurement, not
 * a defect of this program. At depth 0 the round's leaf digest IS its
 * commitment, which is the `cap_height = log_folded_height` corner of the same
 * `MerkleTreeMmcs` and therefore a real configuration rather than a fiction.
 * What survives at depth 0 is exactly what a single round could not show: the
 * shared index, the sixteen-fold coset descent, the chained evaluation, the
 * roll-ins, and the closing comparison against the final polynomial.
 *
 * The commitments and the final polynomial are the PUBLIC INPUT. Without that
 * the statement would be "there EXIST sixteen commitments under which some
 * index closes", which a prover satisfies by choosing them.
 */
export function makeCommitPhaseProgram(opts: {
  logD0: number;
  layers: number;
  pathDepths: number[];
  rollInRounds: number[];
  finalPolyLen: number;
}) {
  const { logD0, layers, pathDepths, rollInRounds, finalPolyLen } = opts;
  if (pathDepths.length !== layers) throw new Error('pathDepths.length != layers');

  class CommitPhaseClaim extends Struct({
    commits: Provable.Array(BbDigest, layers),
    finalPoly: Provable.Array(BbExt, finalPolyLen),
  }) {}

  const prog = ZkProgram({
    name: `dregg-fri-commit-phase-l${layers}-d${logD0}-p${pathDepths.join('_')}-r${rollInRounds.length}`,
    publicInput: CommitPhaseClaim,
    publicOutput: Field, // the query index this chain walked, recomposed
    methods: {
      proveChain: {
        privateInputs: [
          Provable.Array(Bool, logD0), //                    index bits
          BbExt, //                                          the initial reduced opening
          Provable.Array(BbExt, layers), //                  siblings
          Provable.Array(BbExt, layers), //                  betas
          Provable.Array(BbExt, Math.max(rollInRounds.length, 1)), // roll-ins (>=1 for the type)
          Provable.Array(Provable.Array(BbDigest, Math.max(...pathDepths, 1)), layers),
        ],
        async method(
          claim: CommitPhaseClaim,
          indexBits: Bool[],
          initial: BbExt,
          siblings: BbExt[],
          betas: BbExt[],
          rollInValues: BbExt[],
          paths: BbDigest[][],
        ) {
          verifyCommitPhase({
            indexBits,
            initial,
            rounds: Array.from({ length: layers }, (_, r) => ({
              sibling: siblings[r],
              path: paths[r].slice(0, pathDepths[r]),
              beta: betas[r],
              commit: claim.commits[r],
            })),
            rollIns: rollInRounds.map((r, i) => ({ afterRound: r, value: rollInValues[i] })),
            finalPoly: claim.finalPoly,
            logGlobalMaxHeight: logD0,
          });
          let acc = Field(0);
          for (let i = 0; i < logD0; i++) acc = acc.add(indexBits[i].toField().mul(1n << BigInt(i)));
          return { publicOutput: acc };
        },
      },
    },
  });
  return { prog, CommitPhaseClaim };
}

/**
 * A single commit-phase round as a `ZkProgram`, at a small path depth so it
 * COMPILES and PROVES. The full query does not fit a Pickles step by an order
 * of magnitude — that is the measurement, not a defect — so this is what makes
 * "the round is a real provable object" a fact rather than a row count.
 */
export function makeCommitRoundProgram(pathDepth: number) {
  return ZkProgram({
    name: `dregg-fri-commit-round-d${pathDepth}`,
    publicInput: BbDigest, //   the round's MMCS commitment
    publicOutput: BbExt, //     the folded evaluation
    methods: {
      proveRound: {
        privateInputs: [
          BbExt, //                              folded-in value
          Field, //                              coset point x
          Bool, //                               slot bit
          Provable.Array(Bool, pathDepth), //    path directions
          BbExt, //                              sibling evaluation
          Provable.Array(BbDigest, pathDepth), //path
          BbExt, //                              beta
        ],
        async method(
          commit: BbDigest,
          folded: BbExt,
          x: Field,
          slotBit: Bool,
          pathBits: Bool[],
          sibling: BbExt,
          path: BbDigest[],
          beta: BbExt,
        ) {
          assertExtInRange(folded);
          assertLaneLt2p31(x);
          // In a chain, the descent bit is the next index bit — which is also
          // this round's FIRST path direction, because the path walks the
          // already-shifted index. A one-round program has no later bit, so
          // that identity is what it can pass.
          const descentBit = pathDepth > 0 ? pathBits[0] : slotBit;
          const out = commitPhaseRound(folded, x, slotBit, descentBit, pathBits, {
            sibling,
            path,
            beta,
            commit,
          });
          return { publicOutput: out.folded };
        },
      },
    },
  });
}

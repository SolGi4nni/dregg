import { Bool, Field, Provable, Struct, ZkProgram } from 'o1js';
import { P, canonicalLane, reduceLane } from './Poseidon2BabyBearW16.js';
import {
  BbDigest,
  DEPLOYED_COMMIT_LAYERS,
  DEPLOYED_INPUT_PHASE_DEPTH,
  assertDigestInRange,
  compressBB,
  condSwap,
  spongeBB,
} from './Poseidon2Merkle.js';
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
// ⚑ THE INDEX IS ONE OBJECT. The 22 query-index bits are witnessed ONCE and
// reused: bit `r` selects which slot round `r`'s folded value occupies, and
// bits `r+1..22` are the Merkle path directions for round `r`'s depth-`21-r`
// opening. A circuit that witnessed a fresh index per round would measure the
// same and verify something strictly weaker, so the sharing is written out
// rather than left to a comment.
//
// ⚑ WHAT THIS RUNG IS NOT. It is the FRI FOLD CHAIN. It is not the DEEP
// quotient (the `(f(zeta) - f(x))/(zeta - x)` reduced openings and their alpha
// powers), not the AIR constraint evaluation, not the challenger/Fiat-Shamir
// that produces `beta`, and not the proof-of-work grind. Those are separate
// cost centres and none of them is priced here. `beta`, the commitments and the
// claimed final evaluation are PUBLIC INPUTS of this statement precisely
// because binding them to a transcript is the part that is missing.
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
  /** The Merkle path for this round's opening (depth = folded log height). */
  path: BbDigest[];
  /** `beta` for this round. */
  beta: BbExt;
  /** The MMCS root this round's row must open under. */
  commit: BbDigest;
};

/**
 * One round of `verify_query`:
 *   1. reconstruct the arity-2 row `[even, odd]` from the running folded value
 *      and the sibling, ordered by the index bit (`index_in_group`);
 *   2. hash that row with the deployed leaf sponge and verify its opening
 *      against `commit` along `path`;
 *   3. fold to the parent evaluation at `beta`.
 *
 * `slotBit` is the index bit consumed at this round; `pathBits` are the
 * remaining, higher bits — the SAME bits, which is what makes the openings a
 * consistent walk rather than 17 unrelated ones.
 */
export function commitPhaseRound(
  folded: BbExt,
  x: Field,
  slotBit: Bool,
  pathBits: Bool[],
  round: CommitRound,
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

  // The MMCS leaf for this row: an 8-element BabyBear row => exactly ONE
  // permutation (`PaddingFreeSponge<.,16,8,8>`, one full block, no pad).
  let cur = spongeBB([...even, ...odd]);
  for (let h = 0; h < round.path.length; h++) {
    assertDigestInRange(round.path[h]);
    const [l, r] = condSwap(cur, round.path[h], pathBits[h]);
    cur = compressBB(l, r);
  }
  for (let j = 0; j < 8; j++) cur.limbs[j].assertEquals(round.commit.limbs[j]);

  return {
    folded: foldRowArity2(x, round.beta, eEven, eOdd),
    x: nextCosetPoint(x, slotBit),
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
 * The first coset point, DERIVED from the witnessed index bits rather than
 * witnessed alongside them.
 *
 * `fold_row` uses `g_{L+1} ^ reverse_bits_len(index, L)`. With `index` the
 * already-shifted index at folded height `L`, the bit-reversal turns the
 * exponent into a product of constants selected by the bits, so this is `L`
 * conditional multiplications by compile-time constants — and it BINDS the
 * domain point to the index instead of trusting a witness for it.
 */
export function cosetPointFromBits(bits: Bool[], logHeight: number): Field {
  if (bits.length !== logHeight) throw new Error('cosetPointFromBits: bit count != logHeight');
  const g = twoAdicGenerator(logHeight + 1);
  let acc = Field(1);
  // reverse_bits_len(index, L) = sum_i bit_i * 2^(L-1-i), and bits[i] here is
  // bit `i` of the shifted index (bottom-up, matching the path directions).
  for (let i = 0; i < logHeight; i++) {
    let c = g;
    for (let k = 0; k < logHeight - 1 - i; k++) c = md(c * c);
    const scaled = reduceLane(acc.mul(Field(c)), LANE_MAX * LANE_MAX);
    acc = Provable.if(bits[i], scaled, acc);
  }
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
  inputPath: BbDigest[];
  inputCommit: BbDigest;
  /** The reduced opening rolled in at the top height — a witnessed extension
   *  value. ⚑ Binding it to `inputRow` is the DEEP quotient, NOT this rung. */
  reducedOpening: BbExt;
  rounds: CommitRound[];
};

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
  for (const v of w.inputRow) assertLaneLt2p31(v);
  let cur = spongeBB(w.inputRow);
  for (let h = 0; h < logD0; h++) {
    assertDigestInRange(w.inputPath[h]);
    const [l, r] = condSwap(cur, w.inputPath[h], w.indexBits[h]);
    cur = compressBB(l, r);
  }
  for (let j = 0; j < 8; j++) cur.limbs[j].assertEquals(w.inputCommit.limbs[j]);

  // -- commit phase.
  assertExtInRange(w.reducedOpening);
  let folded = w.reducedOpening;
  let x = cosetPointFromBits(w.indexBits.slice(1), logD0 - 1);
  for (let r = 0; r < w.rounds.length; r++) {
    const out = commitPhaseRound(
      folded,
      x,
      w.indexBits[r],
      w.indexBits.slice(r + 1, logD0),
      w.rounds[r],
    );
    folded = out.folded;
    x = out.x;
  }
  return folded;
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
          const out = commitPhaseRound(folded, x, slotBit, pathBits, {
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

import { Bool, Field, Provable, Struct, ZkProgram } from 'o1js';
import {
  P,
  assertLaneLt2p31,
  canonicalLane,
  reduceLane,
} from './Poseidon2BabyBearW16.js';
import { BbDigest, compressBB, condSwap, spongeBB, assertDigestInRange } from './Poseidon2Merkle.js';
import {
  BbExt,
  EXT_D,
  assertExtInRange,
  extAdd,
  extMul,
  extMulBigInt,
  extAddBigInt,
  extSubBigInt,
  extOfBase,
  extSub,
  powTwoAdicRevBits,
  verifyCommitPhase,
} from './FriQueryStep.js';
import {
  DEPLOYED_KNOBS,
  FriKnobs,
  deriveFriChallenges,
} from './FriChallenger.js';

// ---------------------------------------------------------------------------
// RUNG 6 — THE DEEP QUOTIENT. `p3_fri::verifier::open_input`
// (`vendor/plonky3-fri-82cfad73/src/verifier.rs:524-660`) as an o1js circuit.
//
// ⚑ WHY THIS IS THE SOUNDNESS RUNG, AND WHAT IT REPLACES.
//
// Every rung before this one starts the fold chain from `initial` — the reduced
// opening at the global max height — and `initial` is a WITNESS. Rung 3 made the
// query index unchooseable; rung 5 made the walk *the prover's* walk. Neither
// touched the number the walk is about. A FRI verifier whose starting value is
// witnessed proves "there is a low-degree function taking this value here". It
// does not say the value has anything to do with the committed trace, and a
// prover that can pick it can pick a chain that closes.
//
// `open_input` is the object that ties them together:
//
//     ro[L]  =  sum over (matrix at height 2^L, point z, column f)
//                   alpha^k * (f(z) - f(x)) / (z - x)
//
//   * `f(x)` is an entry of the MMCS-OPENED input row — bound by the input-phase
//     Merkle path to the batch commitment;
//   * `f(z)` is the claimed out-of-domain evaluation — bound by being ABSORBED
//     into the challenger before `alpha` is sampled (`two_adic_pcs.rs:780-788`),
//     so a prover that moves one moves every challenge and every query index;
//   * `x` is derived from the SAME index bits the transcript produced;
//   * `alpha` is the transcript's.
//
// and `(f(z) - f(x))/(z - x)` is `q(x)` for `q(X) = (f(X) - f(z))/(X - z)`, which
// is low-degree exactly when `f(z)` is the true evaluation. That is what makes
// the FRI walk a statement ABOUT SOMETHING. It is pinned on the Rust side by
// `p2deep::deep_quotient_is_the_quotient_polynomial`, which builds `q` by
// synthetic division rather than by rearranging the same formula.
//
// ⚑ FOUR CONVENTIONS THAT ARE EACH INVISIBLE ON A DEGENERATE FIXTURE. The
// lesson the coset-descent bug taught — a both-polarity check on one round could
// not see a sign error because one round never consumes two bits — applies here
// four times over, so every fixture in `fri-deep-rows.ts` carries TWO heights,
// TWO matrices sharing a height across DIFFERENT batches, and MULTIPLE points:
//
//   1. `x` carries the multiplicative-group GENERATOR (31). The fold chain's
//      `cosetPointFromBits` does not. Invisible at index 0 only if you also drop
//      the generator, so: not invisible — but see (2).
//   2. `x` uses `g_L`. The fold chain uses `g_{L+1}`. Both give 1 at reversed
//      index 0, i.e. on the all-zero index every `getRows()` supplies.
//   3. the index is SHIFTED DOWN by `LGMH - L` before bit-reversal. Invisible
//      unless a matrix sits BELOW the global max height.
//   4. `alpha_pow` is keyed by HEIGHT, in ENCOUNTER order across batches.
//      Invisible unless two matrices share a height AND a second height exists.
//
// Each has a live wrong twin in `fri-deep-rows.ts` that must diverge.
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;

/** BabyBear's multiplicative-group `GENERATOR`, the coset shift `open_input`
 *  applies to every query point. Checked against the emitter's own
 *  `BabyBear::GENERATOR` rather than trusted. */
export const BB_GENERATOR = 31n;

// ===========================================================================
// 1. Out-of-circuit twins.
// ===========================================================================

const md = (x: bigint) => ((x % P) + P) % P;

export function extPowBigInt(a: bigint[], e: bigint): bigint[] {
  let r = [1n, 0n, 0n, 0n];
  let b = a.slice();
  let k = e;
  while (k > 0n) {
    if (k & 1n) r = extMulBigInt(r, b);
    b = extMulBigInt(b, b);
    k >>= 1n;
  }
  return r;
}

/** `a^{-1}` in `BinomialExtensionField<BabyBear,4>`, by Fermat over the
 *  extension: the multiplicative group has order `p^4 - 1`. */
export function extInvBigInt(a: bigint[]): bigint[] {
  if (a.every((x) => md(x) === 0n)) throw new Error('extInvBigInt: zero has no inverse');
  return extPowBigInt(a, P ** 4n - 2n);
}

export function twoAdicGeneratorBigInt(k: number): bigint {
  if (k > 27) throw new Error(`BabyBear has no 2^${k} root of unity`);
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

/** `open_input`'s query point, out of circuit. */
export function deepQueryPointBigInt(
  index: bigint,
  logHeight: number,
  logGlobalMaxHeight: number,
): bigint {
  const bitsReduced = logGlobalMaxHeight - logHeight;
  if (bitsReduced < 0) throw new Error('a matrix cannot be taller than the global max height');
  const shifted = index >> BigInt(bitsReduced);
  let rev = 0n;
  for (let i = 0; i < logHeight; i++)
    if ((shifted >> BigInt(i)) & 1n) rev |= 1n << BigInt(logHeight - 1 - i);
  const g = twoAdicGeneratorBigInt(logHeight);
  // g^rev
  let acc = 1n;
  let b = g;
  let e = rev;
  while (e > 0n) {
    if (e & 1n) acc = md(acc * b);
    b = md(b * b);
    e >>= 1n;
  }
  return md(BB_GENERATOR * acc);
}

export type DeepMatBigInt = {
  logHeight: number;
  /** `mat_opening` — the MMCS-opened row, one base element per column. */
  openedRow: bigint[];
  /** Per opening point: `z` and the claimed evaluations. */
  points: { z: bigint[]; psAtZ: bigint[][] }[];
};

/**
 * `open_input`, out of circuit. `batches` is the batch structure of
 * `input_proof`; the alpha power is keyed by log HEIGHT and advances in
 * ENCOUNTER order across batches, which is exactly the thing a per-matrix or a
 * global counter gets wrong.
 *
 * Returns the reduced openings DESCENDING by log height — `verify_query`'s
 * consumption order, and the order in which `initial` must be the first entry
 * and must sit at `logGlobalMaxHeight`.
 */
export function reducedOpeningsBigInt(opts: {
  index: bigint;
  logGlobalMaxHeight: number;
  alpha: bigint[];
  batches: DeepMatBigInt[][];
}): { logHeight: number; ro: bigint[] }[] {
  const slots: { logHeight: number; alphaPow: bigint[]; acc: bigint[] }[] = [];
  for (const batch of opts.batches) {
    for (const m of batch) {
      const x = deepQueryPointBigInt(opts.index, m.logHeight, opts.logGlobalMaxHeight);
      let slot = slots.find((s) => s.logHeight === m.logHeight);
      if (!slot) {
        slot = { logHeight: m.logHeight, alphaPow: [1n, 0n, 0n, 0n], acc: [0n, 0n, 0n, 0n] };
        slots.push(slot);
      }
      for (const pt of m.points) {
        const q = extInvBigInt(extSubBigInt(pt.z, [x, 0n, 0n, 0n]));
        for (let c = 0; c < pt.psAtZ.length; c++) {
          const dCol = extSubBigInt(pt.psAtZ[c], [m.openedRow[c], 0n, 0n, 0n]);
          slot.acc = extAddBigInt(slot.acc, extMulBigInt(extMulBigInt(slot.alphaPow, dCol), q));
          slot.alphaPow = extMulBigInt(slot.alphaPow, opts.alpha);
        }
      }
    }
  }
  slots.sort((a, b) => b.logHeight - a.logHeight);
  return slots.map((s) => ({ logHeight: s.logHeight, ro: s.acc }));
}

// ===========================================================================
// 2. In-circuit primitives the DEEP quotient needs and the fold chain did not.
// ===========================================================================

/** `e - b` for a BASE-field `b`. Only lane 0 moves, so this is one reduction
 *  rather than four — and `(f(z) - f(x))` is the single most repeated operation
 *  in the whole verifier (once per opened column per query). */
export function extSubBase(e: BbExt, b: Field): BbExt {
  return new BbExt({
    limbs: [
      reduceLane(e.limbs[0].add(Field(P)).sub(b), LANE_MAX + P),
      e.limbs[1],
      e.limbs[2],
      e.limbs[3],
    ],
  });
}

/** The extension ONE, as constants. */
export function extOne(): BbExt {
  return BbExt.from([1n, 0n, 0n, 0n]);
}

/**
 * `1/a` over `BinomialExtensionField<BabyBear,4>`: witness the inverse and check
 * `a * inv == 1` on all four lanes, canonically.
 *
 * ⚑ THE CANONICAL COMPARISON IS THE WHOLE CHECK. `extMul` returns lanes reduced
 * to `< 2^31` but NOT canonical, and `2^31 - 1 > p`, so two representatives of
 * the same residue can differ as Pasta field elements. Comparing the raw lanes
 * would let a witness pass `1 + p` for the constant `1`. Every lane goes through
 * `canonicalLane` first, exactly as `baseInverse` does.
 *
 * ⚑ AND A ZERO DENOMINATOR IS UNSATISFIABLE, WHICH IS CORRECT. `z == x` makes
 * `(z-x)*inv == 1` impossible over the field, so the circuit REFUSES rather than
 * producing a wrong answer — the constraint-system analogue of the `.inverse()`
 * panic p3 would take. `fri-deep-rows.ts` supplies `z = x` and requires refusal.
 */
export function extInverse(a: BbExt): BbExt {
  const inv = Provable.witness(BbExt, () =>
    BbExt.from(extInvBigInt(a.toBigInts())),
  );
  assertExtInverse(a, inv);
  return inv;
}

/**
 * The CONSTRAINT half of `extInverse`, separated so it can be shown REFUSING.
 *
 * ⚑ SAME REASON `assertLowBitsSplit` is separate from `sampleBitsAsBits`: a
 * function that witnesses its own inputs cannot be handed a dishonest one, so a
 * gate can never watch it say no. The pieces are arguments, and
 * `fri-deep-rows.ts` supplies a lying inverse and requires a refusal.
 */
export function assertExtInverse(a: BbExt, inv: BbExt) {
  assertExtInRange(inv);
  const prod = extMul(a, inv);
  canonicalLane(prod.limbs[0], LANE_MAX).assertEquals(Field(1));
  for (let i = 1; i < EXT_D; i++)
    canonicalLane(prod.limbs[i], LANE_MAX).assertEquals(Field(0));
}

/**
 * `open_input`'s query point, IN CIRCUIT, derived from the transcript's index
 * bits rather than witnessed:
 *
 *     x = GENERATOR * g_L ^ reverse_bits_len(index >> (LGMH - L), L)
 *
 * ⚑ `g_L`, NOT `g_{L+1}`, and the GENERATOR factor is not optional. See the
 * header: both are silently right at reversed-index 0.
 */
export function deepQueryPoint(
  indexBits: Bool[],
  logHeight: number,
  logGlobalMaxHeight: number,
): Field {
  if (indexBits.length !== logGlobalMaxHeight)
    throw new Error(`deepQueryPoint: ${indexBits.length} bits for LGMH ${logGlobalMaxHeight}`);
  const bitsReduced = logGlobalMaxHeight - logHeight;
  if (bitsReduced < 0) throw new Error('a matrix cannot be taller than the global max height');
  const bits = indexBits.slice(bitsReduced, bitsReduced + logHeight);
  const g = powTwoAdicRevBits(bits, logHeight, logHeight);
  return reduceLane(g.mul(Field(BB_GENERATOR)), LANE_MAX * BB_GENERATOR);
}

// ===========================================================================
// 3. The reduced openings.
// ===========================================================================

export type DeepPoint = { z: BbExt; psAtZ: BbExt[] };
export type DeepMatrix = { logHeight: number; openedRow: Field[]; points: DeepPoint[] };

/** A memo for `alpha^n` at the COMPILE-TIME column counts. Every distinct `n`
 *  costs ~`2*log2(n)` extension multiplies once, amortised over `n` columns. */
function alphaPowN(alpha: BbExt, n: number, memo: Map<number, BbExt>): BbExt {
  if (n === 0) return extOne();
  const hit = memo.get(n);
  if (hit) return hit;
  let r: BbExt | null = null;
  let b = alpha;
  let k = n;
  while (k > 0) {
    if (k & 1) r = r === null ? b : extMul(r, b);
    k >>= 1;
    if (k > 0) b = extMul(b, b);
  }
  memo.set(n, r!);
  return r!;
}

/**
 * **The Rung-6 statement.** The reduced openings, COMPUTED from the opened rows,
 * the claimed out-of-domain evaluations, `alpha` and the query index — not
 * witnessed.
 *
 * `perColumn` selects between two forms that are the same value:
 *
 *   * `true`  — p3's literal loop: `ro += alpha_pow * (f(z) - f(x)) * q` and
 *               `alpha_pow *= alpha` once per column. Three extension multiplies
 *               per column.
 *   * `false` — one Horner over the columns of each (matrix, point), then ONE
 *               scale by `alpha_pow * q`. Algebraically identical (pinned by
 *               `p2deep::the_factored_horner_form_agrees_with_p3s_per_column_loop`
 *               AND by this module's own KAT against p3), one extension multiply
 *               per column.
 *
 * The factored form is what a verifier would build; the literal form is measured
 * beside it so the saving is a number rather than a claim.
 */
export function reducedOpenings(opts: {
  indexBits: Bool[];
  logGlobalMaxHeight: number;
  alpha: BbExt;
  batches: DeepMatrix[][];
  perColumn?: boolean;
}): { logHeight: number; ro: BbExt }[] {
  const { indexBits, logGlobalMaxHeight, alpha, batches } = opts;
  const perColumn = opts.perColumn ?? false;
  assertExtInRange(alpha);

  // One query point per HEIGHT — the same for every matrix at that height, and
  // computing it twice would be pure cost.
  const xs = new Map<number, Field>();
  const slots: { logHeight: number; alphaPow: BbExt; acc: BbExt }[] = [];
  const powMemo = new Map<number, BbExt>();

  for (const batch of batches) {
    for (const m of batch) {
      let x = xs.get(m.logHeight);
      if (x === undefined) {
        x = deepQueryPoint(indexBits, m.logHeight, logGlobalMaxHeight);
        xs.set(m.logHeight, x);
      }
      let slot = slots.find((s) => s.logHeight === m.logHeight);
      if (!slot) {
        slot = { logHeight: m.logHeight, alphaPow: extOne(), acc: BbExt.zero() };
        slots.push(slot);
      }
      for (const v of m.openedRow) assertLaneLt2p31(v);
      for (const pt of m.points) {
        assertExtInRange(pt.z);
        for (const v of pt.psAtZ) assertExtInRange(v);
        if (pt.psAtZ.length !== m.openedRow.length)
          throw new Error('the claimed evaluations and the opened row have different widths');
        const q = extInverse(extSub(pt.z, extOfBase(x)));
        const n = pt.psAtZ.length;
        if (perColumn) {
          for (let c = 0; c < n; c++) {
            const dCol = extSubBase(pt.psAtZ[c], m.openedRow[c]);
            slot.acc = extAdd(slot.acc, extMul(extMul(slot.alphaPow, dCol), q));
            slot.alphaPow = extMul(slot.alphaPow, alpha);
          }
        } else {
          // Horner from the TOP column down: `sum_c d_c alpha^c`. Starting at
          // `d_{n-1}` rather than zero skips a degenerate first multiply.
          let h = extSubBase(pt.psAtZ[n - 1], m.openedRow[n - 1]);
          for (let c = n - 2; c >= 0; c--)
            h = extAdd(extMul(h, alpha), extSubBase(pt.psAtZ[c], m.openedRow[c]));
          slot.acc = extAdd(slot.acc, extMul(extMul(slot.alphaPow, q), h));
          slot.alphaPow = extMul(slot.alphaPow, alphaPowN(alpha, n, powMemo));
        }
      }
    }
  }
  slots.sort((a, b) => b.logHeight - a.logHeight);
  return slots.map((s) => ({ logHeight: s.logHeight, ro: s.acc }));
}

/**
 * The roll-in schedule, DERIVED from the opened matrices' heights rather than
 * supplied as a parameter.
 *
 * `verify_query` rolls the opening at height `L` in after the round whose FOLDED
 * height is `L` (`fri/src/verifier.rs:472-477`); with `max_log_arity = 1` the
 * folded height after round `r` is `LGMH - 1 - r`, so `r = LGMH - 1 - L`. The
 * opening at `LGMH` is not rolled in at all: it is the chain's `initial`, and
 * `verify_query` REFUSES a proof whose first reduced opening is at any other
 * height (`:388-393`).
 *
 * ⚑ §3.14 listed "the roll-in schedule" as an uncounted quantity. It is not a
 * free parameter — it is a function of the input matrix heights, and this is the
 * function.
 */
export function rollInSchedule(
  openings: { logHeight: number; ro: unknown }[],
  logGlobalMaxHeight: number,
  layers: number,
): { initialIndex: number; rounds: number[] } {
  if (openings.length === 0) throw new Error('no reduced openings: nothing to fold');
  if (openings[0].logHeight !== logGlobalMaxHeight)
    throw new Error(
      `the first reduced opening is at height ${openings[0].logHeight}, not the global max ` +
        `${logGlobalMaxHeight} — verify_query refuses this proof`,
    );
  const rounds = openings.slice(1).map((o) => {
    const r = logGlobalMaxHeight - 1 - o.logHeight;
    if (r < 0 || r >= layers)
      throw new Error(`a reduced opening at height ${o.logHeight} rolls in outside the fold chain`);
    return r;
  });
  return { initialIndex: 0, rounds };
}

// ===========================================================================
// 4. THE DEEP-BOUND QUERY — the seam that removes the last witnessed input.
// ===========================================================================

/** A batch's shape: one MMCS commitment over matrices, each with its height,
 *  its width, and how many out-of-domain points it opens at. */
export type DeepBatchSpec = { logHeight: number; numPoints: number; numCols: number }[];

/**
 * The transcript state the FRI challenges are drawn from.
 *
 * `prefix` stands for the batch-STARK's own observes (degree bits, the trace and
 * quotient commitments, the public values); the opening points and every claimed
 * evaluation follow it. The EVALUATIONS are observed by `two_adic_pcs::verify`
 * itself (`:780-788`) before `verify_fri` is entered, so that half is exact. The
 * `z`s are observed here as a stand-in for having been SAMPLED upstream — a
 * weaker binding than sampling, and named as such.
 */
export function deepPreamble(prefix: Field[], zs: BbExt[], evals: BbExt[]): Field[] {
  const out: Field[] = [...prefix];
  for (const z of zs) out.push(...z.limbs);
  for (const e of evals) out.push(...e.limbs);
  return out;
}

/** The bigint twin of `deepPreamble`. */
export function deepPreambleBigInt(
  prefix: bigint[],
  zs: bigint[][],
  evals: bigint[][],
): bigint[] {
  return [...prefix, ...zs.flat(), ...evals.flat()];
}

/**
 * **The Rung-6 program.** One FRI query in which NOTHING the chain consumes is
 * witnessed:
 *
 *   * the opened input rows are bound to the batch commitments by MMCS paths;
 *   * the claimed evaluations `f(z)` are ABSORBED into the transcript, so alpha,
 *     every beta and the query index all move if any of them moves;
 *   * `alpha` and the index come out of that transcript;
 *   * the reduced openings are COMPUTED from those, not supplied;
 *   * the chain starts at the opening at the global max height and rolls the
 *     rest in at the rounds their heights name;
 *   * the chain lands on the absorbed final polynomial.
 *
 * ⚑ WHAT IS STILL A STAND-IN. `prefix` stands for the batch-STARK's own observes
 * that precede the opened values (degree bits, trace/quotient commitments, the
 * public values, and `zeta` itself). The `z`s are carried in it so they are
 * bound, but binding them to a STARK transcript that SAMPLED zeta is a further
 * rung. And each batch here holds ONE matrix: `MerkleTreeMmcs::verify_batch`
 * over several matrices of MIXED heights under one root is not built, and the
 * input-phase opening is priced for it rather than implemented.
 */
export function makeDeepBoundQueryProgram(opts: {
  knobs: FriKnobs;
  prefixLen: number;
  batches: DeepBatchSpec[];
  /** Merkle depth used for each batch's input opening. */
  inputPathDepths: number[];
  /** Merkle depth used for each commit-phase round. */
  pathDepths: number[];
}) {
  const { knobs, prefixLen, batches, inputPathDepths, pathDepths } = opts;
  const { layers, finalPolyLen, indexBits: nIndexBits, logGlobalMaxHeight } = knobs;
  if (pathDepths.length !== layers) throw new Error('pathDepths.length != layers');
  if (inputPathDepths.length !== batches.length)
    throw new Error('inputPathDepths.length != batches.length');
  if (batches.some((b) => b.length !== 1))
    throw new Error('this program carries ONE matrix per batch — see the header');

  const maxDepth = Math.max(...pathDepths, 1);
  const maxInputDepth = Math.max(...inputPathDepths, 1);
  const nBatches = batches.length;
  const widths = batches.map((b) => b[0].numCols);
  const nPoints = batches.map((b) => b[0].numPoints);
  const totalEvals = batches.reduce((a, b) => a + b[0].numPoints * b[0].numCols, 0);
  const totalZs = nPoints.reduce((a, b) => a + b, 0);
  const totalRow = widths.reduce((a, b) => a + b, 0);

  // The roll-in schedule is a COMPILE-TIME consequence of the matrix heights —
  // §3.14 listed it as an uncounted quantity and it is not one. `rollInSchedule`
  // recomputes it inside the circuit from the same heights and would throw if
  // the two disagreed.
  const heights = [...new Set(batches.map((b) => b[0].logHeight))].sort((a, b) => b - a);
  const rollInRounds = heights.slice(1).map((h) => logGlobalMaxHeight - 1 - h);
  const nRollIns = rollInRounds.length;

  class DeepQueryClaim extends Struct({
    /** One MMCS root per input batch. */
    inputCommits: Provable.Array(BbDigest, nBatches),
    /** `proof.commit_phase_commits`. */
    commits: Provable.Array(BbDigest, layers),
    finalPoly: Provable.Array(BbExt, finalPolyLen),
  }) {}

  const prog = ZkProgram({
    name: `dregg-fri-deep-query-l${layers}-b${nBatches}-c${totalRow}`,
    publicInput: DeepQueryClaim,
    publicOutput: Field, //  the DERIVED query index this whole statement walked
    methods: {
      proveDeepQuery: {
        privateInputs: [
          Provable.Array(Field, prefixLen), //                the STARK-preamble stand-in
          Provable.Array(BbExt, totalZs), //                  the opening points
          Provable.Array(BbExt, totalEvals), //               f(z), flattened
          Provable.Array(Field, totalRow), //                 f(x), flattened
          Provable.Array(Provable.Array(BbDigest, maxInputDepth), nBatches),
          Field, //                                           query PoW witness
          Provable.Array(BbExt, layers), //                   siblings
          Provable.Array(Provable.Array(BbDigest, maxDepth), layers),
        ],
        async method(
          claim: DeepQueryClaim,
          prefix: Field[],
          zs: BbExt[],
          evals: BbExt[],
          rows: Field[],
          inputPaths: BbDigest[][],
          queryPowWitness: Field,
          siblings: BbExt[],
          paths: BbDigest[][],
        ) {
          // -- 1. the preamble. `two_adic_pcs::verify` observes every opened
          //       evaluation BEFORE `verify_fri` samples alpha (`:780-788`), so
          //       f(z) is inside the Fiat-Shamir state, not beside it.
          const preamble = deepPreamble(prefix, zs, evals);
          const chal = deriveFriChallenges(
            { preamble, commits: claim.commits, finalPoly: claim.finalPoly, queryPowWitness },
            knobs,
          );
          const bits = chal.queryIndexBits[0];

          // -- 2. the input-phase openings: each batch's row must open under its
          //       own commitment at the index SHIFTED to that batch's height.
          let rowOff = 0;
          let evalOff = 0;
          let zOff = 0;
          const mats: DeepMatrix[][] = [];
          for (let b = 0; b < nBatches; b++) {
            const w = widths[b];
            const row = rows.slice(rowOff, rowOff + w);
            rowOff += w;
            for (const v of row) assertLaneLt2p31(v);
            let cur = spongeBB(row);
            const bitsReduced = logGlobalMaxHeight - batches[b][0].logHeight;
            for (let h = 0; h < inputPathDepths[b]; h++) {
              assertDigestInRange(inputPaths[b][h]);
              const [l, r] = condSwap(cur, inputPaths[b][h], bits[bitsReduced + h]);
              cur = compressBB(l, r);
            }
            for (let j = 0; j < 8; j++) cur.limbs[j].assertEquals(claim.inputCommits[b].limbs[j]);

            const points: DeepPoint[] = [];
            for (let p = 0; p < nPoints[b]; p++) {
              points.push({ z: zs[zOff + p], psAtZ: evals.slice(evalOff, evalOff + w) });
              evalOff += w;
            }
            zOff += nPoints[b];
            mats.push([{ logHeight: batches[b][0].logHeight, openedRow: row, points }]);
          }

          // -- 3. THE DEEP QUOTIENT. `initial` stops being a witness here.
          const ro = reducedOpenings({
            indexBits: bits,
            logGlobalMaxHeight,
            alpha: chal.alpha,
            batches: mats,
          });
          const sched = rollInSchedule(ro, logGlobalMaxHeight, layers);

          // -- 4. the fold chain, at the derived index, under the derived betas.
          verifyCommitPhase({
            indexBits: bits,
            initial: ro[0].ro,
            rounds: Array.from({ length: layers }, (_, r) => ({
              sibling: siblings[r],
              path: paths[r].slice(0, pathDepths[r]),
              beta: chal.betas[r],
              commit: claim.commits[r],
            })),
            rollIns: sched.rounds.map((r, i) => ({ afterRound: r, value: ro[i + 1].ro })),
            finalPoly: claim.finalPoly,
            logGlobalMaxHeight,
          });

          let acc = Field(0);
          for (let i = 0; i < nIndexBits; i++)
            acc = acc.add(bits[i].toField().mul(1n << BigInt(i)));
          return { publicOutput: acc };
        },
      },

      /**
       * ⚑ THE PRE-RUNG-6 STATEMENT, KEPT LIVE AS A COUNTER-EXAMPLE.
       *
       * Identical to `proveDeepQuery` except that the chain starts from a
       * WITNESSED `initial` and the reduced openings are never computed. That is
       * exactly what every rung up to 5 proved, and it is here so the gate can
       * EXHIBIT the gap rather than assert it: `fri-deep-rows.ts` builds a
       * witness whose `initial` is not the DEEP value, proves it under THIS
       * method, and requires `proveDeepQuery` to refuse the same public claim.
       *
       * A rung whose predecessor cannot be shown accepting what it now refuses
       * is a rung nobody has measured. Compiling both in one program costs one
       * compile and makes the comparison a fact.
       */
      proveWitnessedInitial: {
        privateInputs: [
          Provable.Array(Field, prefixLen),
          Provable.Array(BbExt, totalZs),
          Provable.Array(BbExt, totalEvals),
          Provable.Array(Field, totalRow),
          Provable.Array(Provable.Array(BbDigest, maxInputDepth), nBatches),
          Field,
          BbExt, //                                           the WITNESSED initial
          Provable.Array(BbExt, Math.max(nRollIns, 1)), //     the WITNESSED roll-ins
          Provable.Array(BbExt, layers),
          Provable.Array(Provable.Array(BbDigest, maxDepth), layers),
        ],
        async method(
          claim: DeepQueryClaim,
          prefix: Field[],
          zs: BbExt[],
          evals: BbExt[],
          rows: Field[],
          inputPaths: BbDigest[][],
          queryPowWitness: Field,
          initial: BbExt,
          rollInValues: BbExt[],
          siblings: BbExt[],
          paths: BbDigest[][],
        ) {
          const preamble = deepPreamble(prefix, zs, evals);
          const chal = deriveFriChallenges(
            { preamble, commits: claim.commits, finalPoly: claim.finalPoly, queryPowWitness },
            knobs,
          );
          const bits = chal.queryIndexBits[0];

          let rowOff = 0;
          for (let b = 0; b < nBatches; b++) {
            const w = widths[b];
            const row = rows.slice(rowOff, rowOff + w);
            rowOff += w;
            for (const v of row) assertLaneLt2p31(v);
            let cur = spongeBB(row);
            const bitsReduced = logGlobalMaxHeight - batches[b][0].logHeight;
            for (let h = 0; h < inputPathDepths[b]; h++) {
              assertDigestInRange(inputPaths[b][h]);
              const [l, r] = condSwap(cur, inputPaths[b][h], bits[bitsReduced + h]);
              cur = compressBB(l, r);
            }
            for (let j = 0; j < 8; j++) cur.limbs[j].assertEquals(claim.inputCommits[b].limbs[j]);
          }

          verifyCommitPhase({
            indexBits: bits,
            initial,
            rounds: Array.from({ length: layers }, (_, r) => ({
              sibling: siblings[r],
              path: paths[r].slice(0, pathDepths[r]),
              beta: chal.betas[r],
              commit: claim.commits[r],
            })),
            rollIns: rollInRounds.map((r, i) => ({ afterRound: r, value: rollInValues[i] })),
            finalPoly: claim.finalPoly,
            logGlobalMaxHeight,
          });

          let acc = Field(0);
          for (let i = 0; i < nIndexBits; i++)
            acc = acc.add(bits[i].toField().mul(1n << BigInt(i)));
          return { publicOutput: acc };
        },
      },
    },
  });
  return { prog, DeepQueryClaim };
}

// ===========================================================================
// 5. The DEPLOYED shape, for measurement.
// ===========================================================================

/**
 * The root's opened-column census, from §1.3's 7-table set.
 *
 * ⚑ THE 5-TABLE `[9,9,15,14,15]` FIGURE IS THE BN254 SHRINK PROOF, NOT THE ROOT.
 * That mis-attribution has already been made once in this tree and is called out
 * at §1.2. The root is verified by `verify_all_tables` over 3 primitives plus one
 * AIR per non-primitive op-type present, which at `K >= 2` is 7 tables and 940
 * main / 175 preprocessed columns.
 *
 * Each main and preprocessed column is opened at TWO points (`zeta`, `g*zeta`);
 * each quotient chunk contributes `D = 4` base columns at ONE point, and there
 * are `n_chunks = 2` chunks per instance.
 */
export const ROOT_TABLES = [
  { name: 'Const', main: 4, prep: 2 },
  { name: 'Public', main: 4, prep: 2 },
  { name: 'Alu', main: 76, prep: 59 },
  { name: 'poseidon2-W16', main: 300, prep: 24 },
  { name: 'poseidon2-W24', main: 452, prep: 36 },
  { name: 'recompose', main: 4, prep: 2 },
  { name: 'expose_claim', main: 100, prep: 50 },
] as const;

export const ROOT_QUOTIENT_CHUNKS = 2;
export const ROOT_EXT_DEGREE = 4;

/** `(matrix, point, column)` triples in ONE query's `open_input` — the count the
 *  DEEP quotient's row budget is linear in. */
export function rootDeepTermCount(): {
  main: number;
  prep: number;
  quotient: number;
  total: number;
} {
  const main = ROOT_TABLES.reduce((a, t) => a + t.main, 0) * 2;
  const prep = ROOT_TABLES.reduce((a, t) => a + t.prep, 0) * 2;
  const quotient = ROOT_TABLES.length * ROOT_QUOTIENT_CHUNKS * ROOT_EXT_DEGREE;
  return { main, prep, quotient, total: main + prep + quotient };
}

/** Witness a DEEP shape of the given widths — for `getRows()`. The values are
 *  irrelevant to the row count; the SHAPE is not. */
export function witnessDeepShape(
  logGlobalMaxHeight: number,
  batches: DeepBatchSpec[],
): { indexBits: Bool[]; alpha: BbExt; batches: DeepMatrix[][] } {
  const wit = <T>(f: () => T, t: any) => Provable.witness(t, f);
  return {
    indexBits: Array.from({ length: logGlobalMaxHeight }, () => wit(() => Bool(false), Bool)),
    alpha: wit(() => BbExt.zero(), BbExt),
    batches: batches.map((b) =>
      b.map((s) => ({
        logHeight: s.logHeight,
        openedRow: Array.from({ length: s.numCols }, () => wit(() => Field(1), Field)),
        points: Array.from({ length: s.numPoints }, () => ({
          z: wit(() => BbExt.from([2n, 0n, 0n, 0n]), BbExt),
          psAtZ: Array.from({ length: s.numCols }, () => wit(() => BbExt.zero(), BbExt)),
        })),
      })),
    ),
  };
}

/** The deployed root's DEEP shape at §1.3's table set: one batch per commitment
 *  round, each matrix at the top height unless told otherwise. */
export function deployedDeepShape(logGlobalMaxHeight = DEPLOYED_KNOBS.logGlobalMaxHeight) {
  const main: DeepBatchSpec = ROOT_TABLES.map((t) => ({
    logHeight: logGlobalMaxHeight,
    numPoints: 2,
    numCols: t.main,
  }));
  const prep: DeepBatchSpec = ROOT_TABLES.map((t) => ({
    logHeight: logGlobalMaxHeight,
    numPoints: 2,
    numCols: t.prep,
  }));
  const quot: DeepBatchSpec = ROOT_TABLES.flatMap(() =>
    Array.from({ length: ROOT_QUOTIENT_CHUNKS }, () => ({
      logHeight: logGlobalMaxHeight,
      numPoints: 1,
      numCols: ROOT_EXT_DEGREE,
    })),
  );
  return [main, prep, quot];
}

import { Bool, Field, Provable, Struct, ZkProgram } from 'o1js';
import { assertLaneLt2p31, canonicalLane } from './Poseidon2BabyBearW16.js';
import {
  BbExt,
  EXT_D,
  assertExtInRange,
  extMul,
  extOfBase,
  extSub,
  twoAdicGenerator,
  verifyCommitPhase,
} from './FriQueryStep.js';
import { FriKnobs } from './FriChallenger.js';
import type { ChallengerLike, Digestish, HashSuite } from './HashSuiteType.js';
import { babyBearSuite, suiteByName } from './HashSuites.js';
import { DeepMatrix, reducedOpenings, rollInSchedule } from './DeepQuotient.js';
import {
  extScaleConst,
  foldConstraints,
  recomposeQuotient,
  selectorsAtPoint,
} from './AirEval.js';

// ---------------------------------------------------------------------------
// THE ASSEMBLY — `DreggProofVerify`.
//
// ⚑ WHAT IS NEW HERE, AND IT IS NOT A ROW COUNT.
//
// Rungs 1-7 are seven objects, each of which verifies a PIECE of a FRI-STARK
// proof, each measured, each KAT'd. None of them consumes a proof. The inputs
// are synthesised by the measurement: an opened row that no prover produced, a
// fold chain over a value nobody committed to, a transcript whose preamble is a
// stand-in. That is a set of components, and "Mina verifies dregg" is not a
// statement one can make about a set of components.
//
// This module is the one program that takes a proof `p3_uni_stark::prove`
// produced under `DreggStarkConfig` and DECIDES. It is the whole of
// `p3_uni_stark::verify`, with nothing witnessed that the verifier derives:
//
//   1. the STARK preamble — degree bits, the trace commitment, the public
//      values — absorbed, then `alpha` SAMPLED, the quotient commitment
//      absorbed, then `zeta` SAMPLED (`uni-stark/src/verifier.rs:361-390`);
//   2. every claimed out-of-domain evaluation absorbed, in round order, before
//      FRI's own alpha (`two_adic_pcs.rs:780-788`);
//   3. the FRI transcript — alpha, every beta, the arity schedule, the query
//      grind, and every query index DERIVED (`fri/src/verifier.rs:139-270`);
//   4. **the AIR closing equality** at `zeta`:
//      `sum_i alpha^i C_i * Z_H(zeta)^{-1} == quotient(zeta)`, with
//      `quotient(zeta)` recomposed from the opened chunks by Lagrange over the
//      chunk domains, and the three Lagrange selectors computed, not supplied;
//   5. per query — the input-phase MMCS openings under the SAME commitments the
//      transcript absorbed, the DEEP quotient (so the fold chain starts from a
//      value bound to the opened trace rather than one the prover chose), and
//      the fold chain to the final polynomial.
//
// ⚑ THE AIR IS A PARAMETER, AND THAT IS THE HONEST SHAPE. `C_i` for dregg's
// seven ROOT tables is not built and its count `N` is not taken (§3.14) — rung 7
// prices the arithmetic AROUND `C_i` for exactly that reason. So the constraint
// evaluator is an argument here. `minaFixtureConstraints` below is the evaluator
// for the 3-column degree-3 AIR the Rust emitter proves, and at that AIR this
// program is CLOSED: it evaluates the constraints itself and there is no
// residual. Handed dregg's root tables it would be closed too — at a row count
// this file measures and does not pretend to fit.
//
// ⚑ WHAT A ROW COUNT CANNOT SEE, AND WHY THE LEG DOES WHAT IT DOES. §3.15e:
// `Provable.runAndCheck` does not evaluate lookup constraints, and a derived
// variable is indistinguishable from a witness carrying its value to
// `runAndCheck`, to `prove` AND to `getRows()`. So the accompanying leg proves
// with the real Pickles prover, and every "this is derived" claim is backed by a
// ROW-COUNT DELTA against a twin that witnesses it instead.
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;

// ===========================================================================
// 1. The shape — everything the circuit needs at COMPILE time.
// ===========================================================================

/** One matrix inside an input-phase batch: its LDE log height, its column count
 *  and how many out-of-domain points it opens at.
 *
 * ⚑ `pointScales` IS THE FOUR-ROUND WIRING, AND IT REPLACED A `b === 0` SWITCH.
 * Every out-of-domain point in a `uni-stark`/batch-STARK opening is `ζ · c` for a
 * CONSTANT `c`: `c = 1` at ζ itself, and `c = g_k` — the two-adic generator of
 * the instance's own trace domain — at the next-row point. The assembly used to
 * infer that from the batch index ("batch 0 is the trace, everything else is a
 * quotient chunk"), which is exactly the mis-wiring `verifyPlan` refused a third
 * round to avoid. Declaring the scales per matrix makes the wiring a property of
 * the SHAPE, so a preprocessed or permutation round is ordinary.
 *
 * ⚠ AND `c = 1` TWICE IS A REAL SHAPE, NOT A BUG TO DEDUPE. dregg's root has an
 * instance at `degree_bits = 0` (`expose_claim`), whose next-row point is `ζ·g_0
 * = ζ`. Its permutation matrix opens at ζ TWICE and the DEEP quotient charges
 * both — 200 of the permutation round's 512 terms. A wiring that collapsed equal
 * points would drop 100 of them and still produce a plausible number. */
export type MatrixShape = {
  logHeight: number;
  numCols: number;
  numPoints: number;
  /** The constant multiples of ζ this matrix opens at, in `points` order.
   *  Defaults to `[1n]` / `[1n, g_{traceLogSize}]` — the legacy trace wiring —
   *  when absent, so the two-round fixture shape is unchanged. */
  pointScales?: bigint[];
};

/** One MMCS commitment and the matrices committed under it.
 *
 * ⚑ MIXED HEIGHTS ARE THE ROOT'S REAL SHAPE AND THEY ARE NOT A LEAF
 * CONCATENATION. `MerkleTreeMmcs::verify_batch` sponges the rows of the matrices
 * at the TALLEST padded height into the leaf, then walks the path — and at each
 * level whose padded height a shorter matrix names, compresses THAT height's own
 * row digest into the running root (`merkle-tree/src/mmcs.rs:1065-1105`, the
 * `peeking_take_while` loop). Equal heights keep committed order, because the
 * sort is stable. A batch whose matrices are all one height degenerates to the
 * single sponge + flat path this file did before, which is why the fixture's
 * gate order does not move. */
export type BatchShape = { matrices: MatrixShape[]; pathDepth: number };

export type DreggProofShape = {
  knobs: FriKnobs;
  /** LDE log height of the tallest input matrix — `verify_fri`'s
   *  `log_global_max_height`. */
  logGlobalMaxHeight: number;
  /** Merkle depth of each commit-phase round's opening. */
  commitPathDepths: number[];
  /** The input-phase batches, in the order `coms_to_verify` builds them:
   *  trace, then quotient chunks, then preprocessed. */
  batches: BatchShape[];
  /** The whole per-instance STARK shape. */
  air: {
    /** `proof.degree_bits` — observed as the FIRST transcript element. */
    degreeBits: number;
    baseDegreeBits: number;
    preprocessedWidth: number;
    width: number;
    numPublicValues: number;
    numQuotientChunks: number;
    hasTraceNext: boolean;
    /** `log2` of the trace domain — the vanishing polynomial's squaring count. */
    traceLogSize: number;
    /** `g_{traceLogSize}^{-1}`, from p3's own domain algebra. */
    subgroupGenInv: bigint;
    /** `log2` of ONE quotient chunk's domain. */
    chunkLogSize: number;
    /** Each chunk domain's `shift^{-1}`. */
    chunkShiftInvs: bigint[];
    /** `Z_{D_j}(first_point(D_i))^{-1}`, indexed `[i][j]`; the diagonal is unused. */
    lagrangeConstInvs: bigint[][];
  };
  /** The constraint evaluator. Absent, the AIR closing equality is NOT checked
   *  and the program is a PCS verifier — which is a strictly weaker statement
   *  and is named as one wherever it is used. */
  constraints?: ConstraintEvaluator;
  /** ⚑ THE §3.15e TWIN. When false the challenges are WITNESSED instead of
   *  derived, and the program is otherwise identical. It exists so the cost of
   *  deriving them is a measured DELTA rather than a claim; a program built this
   *  way must never be proved as if it verified anything. */
  deriveChallenges?: boolean;
  /**
   * ⚑ THE HASH, AS A PARAMETER — the whole reason there is one verifier and not
   * two. Defaults to `babyBearSuite`, the `DreggStarkConfig` proof every rung
   * before this one measured. A proof minted under `DreggMinaConfig`
   * (`circuit-prove/src/dregg_mina_config.rs`) sets `pastaSuite` and runs
   * EXACTLY the code below: the transcript order, the DEEP quotient, the
   * roll-in schedule, the AIR closing equality and the fold chain are shared,
   * and what differs is a hundred lines of hashing in `PastaMmcs` /
   * `PastaChallenger`. `shapeOf` reads it off the fixture's own `hash` field, so
   * feeding a Pasta proof to the BabyBear walk is refused by NAME rather than
   * discovered as a digest mismatch forty thousand rows in.
   */
  suite?: HashSuite<any>;
};

/** What a constraint evaluator is handed. Everything is already derived. */
export type ConstraintContext = {
  traceLocal: BbExt[];
  traceNext: BbExt[];
  publicValues: Field[];
  isFirstRow: BbExt;
  isLastRow: BbExt;
  isTransition: BbExt;
  zeta: BbExt;
};
/** `C_0 .. C_{N-1}`, in the AIR's own `assert_zero` EMISSION order — which is
 *  the FOLDING order, because `VerifierConstraintFolder::assert_zero` does
 *  `acc = acc * alpha + C` (`uni-stark/src/folder.rs:181-184`). A permuted list
 *  is a different accumulator and refuses an honest proof. */
export type ConstraintEvaluator = (ctx: ConstraintContext) => BbExt[];

// ===========================================================================
// 2. The AIR the Rust emitter proves.
// ===========================================================================

/**
 * `MinaFixtureAir` — `circuit/src/bin/mina_stark_fixture.rs`, evaluated at
 * `zeta`. Columns `[a, b, c]`:
 *
 *   C0                 `b - a^3`                    (degree 3 — forces 2 chunks)
 *   C1  is_first_row * `c - pis[0]`
 *   C2  is_transition * `c' - c - b`                (the only next-row term)
 *   C3  is_last_row   * `c - pis[1]`
 *
 * The order is `eval`'s order and must stay that way.
 */
export const minaFixtureConstraints: ConstraintEvaluator = (ctx) => {
  const [a, b, c] = ctx.traceLocal;
  const cNext = ctx.traceNext[2];
  const a3 = extMul(extMul(a, a), a);
  return [
    extSub(b, a3),
    extMul(ctx.isFirstRow, extSub(c, extOfBase(ctx.publicValues[0]))),
    extMul(ctx.isTransition, extSub(extSub(cNext, c), b)),
    extMul(ctx.isLastRow, extSub(c, extOfBase(ctx.publicValues[1]))),
  ];
};

/**
 * The SAME AIR with `a^3` replaced by `a^2` — a live counter-example, kept so
 * the leg can show the closing equality REFUSING rather than assert that it
 * bites. A rung whose check cannot be watched saying no is a rung nobody has
 * measured; this is the cheapest object that lets it be watched, because the
 * proof, the transcript, the openings and the fold chain are all identical and
 * only `C_0` moves.
 */
export const minaFixtureConstraintsBentDegree: ConstraintEvaluator = (ctx) => {
  const [a, b, c] = ctx.traceLocal;
  const cNext = ctx.traceNext[2];
  return [
    extSub(b, extMul(a, a)),
    extMul(ctx.isFirstRow, extSub(c, extOfBase(ctx.publicValues[0]))),
    extMul(ctx.isTransition, extSub(extSub(cNext, c), b)),
    extMul(ctx.isLastRow, extSub(c, extOfBase(ctx.publicValues[1]))),
  ];
};

/** The same AIR with `C_1` and `C_3` SWAPPED. Every constraint is still present
 *  and still correct; only the fold order moves — which is a different
 *  accumulator, and the whole point of saying the emission order is the folding
 *  order. It must refuse. */
export const minaFixtureConstraintsPermuted: ConstraintEvaluator = (ctx) => {
  const cs = minaFixtureConstraints(ctx);
  return [cs[0], cs[3], cs[2], cs[1]];
};

/** The same AIR with `is_transition` dropped from `C_2` — the selector-blind
 *  reading. Silently right on a trace whose last row happens to satisfy the
 *  transition, so it is checked against a real fixture rather than reasoned
 *  about. */
export const minaFixtureConstraintsNoSelector: ConstraintEvaluator = (ctx) => {
  const cs = minaFixtureConstraints(ctx);
  const [, b, c] = ctx.traceLocal;
  const cNext = ctx.traceNext[2];
  return [cs[0], cs[1], extSub(extSub(cNext, c), b), cs[3]];
};

// ===========================================================================
// 3. The verifier, in PIECES — because a step boundary has to be able to fall
//    between them.
//
// ⚑ WHY THIS IS A SET OF FUNCTIONS AND NOT ONE METHOD BODY. The monolith below
// is 86.9% of a Pickles step at the smallest geometry that proves, and the
// deployed one is ~500 steps — so the verifier has to SPLIT, and a split can
// only fall where the code has a seam. These four functions are that seam, and
// `DreggProofPartition.ts` cuts between (2) and (3). The monolith calls exactly
// the same functions in exactly the same order, so the partitioned steps and the
// one-step program are not two implementations that agree today.
// ===========================================================================

/** Total base-field lanes in a batch's MMCS leaf. */
const batchRowWidth = (b: BatchShape) => b.matrices.reduce((a, m) => a + m.numCols, 0);

/** Where ONE `(batch, matrix, point)`'s claimed evaluations live in the flat
 *  opened-value list, and which constant multiple of ζ they are claimed at.
 *
 *  `offset` indexes the CONCATENATION `[...openedTrace, ...openedQuotient]` —
 *  which is p3's own observe order, round-major then matrix-major then
 *  point-major (`two_adic_pcs.rs:780-788`). `openedTrace` is round 0's flat run
 *  and `openedQuotient` is every later round's, so the two-round fixture's
 *  meaning of those two names is exactly what it was. */
export type PointWire = { scaleIndex: number; offset: number; len: number };

/** Everything the compile-time shape implies. Computed ONCE so a shape check
 *  lives in one place and the monolith and the steps cannot disagree about it. */
export type VerifyPlan = {
  sh: DreggProofShape;
  suite: HashSuite<any>;
  derive: boolean;
  nBatches: number;
  maxCommitDepth: number;
  maxInputDepth: number;
  rowWidths: number[];
  totalRow: number;
  nTraceCols: number;
  nQuotientVals: number;
  nOpenedTrace: number;
  nRollIns: number;
  /** The DISTINCT constant multiples of ζ any matrix opens at, first-encounter
   *  order, `1n` first. `zetaPointsOf` turns these into extension values ONCE
   *  per proof, outside the query loop — which is where the fixture's single
   *  `ζ·g` already lived. */
  pointScales: bigint[];
  /** `[batch][matrix][point]`. */
  wiring: PointWire[][][];
  /** `nOpenedTrace + nQuotientVals` — the whole opened-value census. */
  nOpenedValues: number;
  /** Distinct log heights in each batch, DESCENDING. The mixed-height MMCS
   *  injection schedule is a function of exactly this. */
  batchHeights: number[][];
};

export function verifyPlan(sh: DreggProofShape): VerifyPlan {
  const { knobs, batches, air, logGlobalMaxHeight } = sh;
  const { layers, indexBits: nIndexBits } = knobs;
  const derive = sh.deriveChallenges ?? true;
  if (sh.commitPathDepths.length !== layers)
    throw new Error(`commitPathDepths has ${sh.commitPathDepths.length} entries for ${layers} layers`);
  if (nIndexBits !== logGlobalMaxHeight)
    throw new Error('this assembly does not use extra query index bits');

  const nBatches = batches.length;
  const rowWidths = batches.map(batchRowWidth);

  // ⚑ THIS USED TO THROW ON `nBatches !== 2`, AND THE THROW WAS RIGHT FOR THE
  // CODE IT GUARDED. The opened-value wiring was inferred from the batch index —
  // batch 0's points were (ζ, trace_local) and (ζ·g, trace_next), every other
  // batch's matrix `m` took quotient chunk `m` at ζ — so a third round would
  // have MIS-WIRED silently. `coms_to_verify` grows a preprocessed round
  // whenever the AIR has preprocessed columns (`uni-stark/src/verifier.rs:
  // 465-476`) and a batch-STARK grows a permutation round on top, and neither
  // is either shape. dregg's root has all FOUR.
  //
  // The fix is not a wider switch, it is deleting the inference: `pointScales`
  // says which multiple of ζ each point is at and the offsets below say where
  // its values live. `defaultScales` reproduces the old inference EXACTLY for a
  // shape that does not declare them, so the fixture's wiring — and its emitted
  // gate order — is unchanged to the row.
  const defaultScales = (b: number, m: MatrixShape): bigint[] => {
    if (m.pointScales) {
      if (m.pointScales.length !== m.numPoints)
        throw new Error(
          `a matrix in batch ${b} declares ${m.numPoints} points and ${m.pointScales.length} ` +
            'point scales',
        );
      return m.pointScales;
    }
    if (b === 0)
      return m.numPoints === 2 ? [1n, twoAdicGenerator(air.traceLogSize)] : [1n];
    if (m.numPoints !== 1)
      throw new Error(
        `batch ${b} matrix opens at ${m.numPoints} points and declares no \`pointScales\`. ` +
          'Only the trace round has an inferable next-row point; every other round must say ' +
          'which multiples of ζ it opens at.',
      );
    return [1n];
  };

  const pointScales: bigint[] = [1n];
  const wiring: PointWire[][][] = [];
  let off = 0;
  let nOpenedTrace = 0;
  for (let b = 0; b < nBatches; b++) {
    const perMat: PointWire[][] = [];
    for (const m of batches[b].matrices) {
      const scales = defaultScales(b, m);
      const wires: PointWire[] = [];
      for (const c of scales) {
        let si = pointScales.indexOf(c);
        if (si < 0) si = pointScales.push(c) - 1;
        wires.push({ scaleIndex: si, offset: off, len: m.numCols });
        off += m.numCols;
      }
      perMat.push(wires);
    }
    wiring.push(perMat);
    if (b === 0) nOpenedTrace = off;
  }
  const nOpenedValues = off;

  // ⚑ THE MIXED-HEIGHT SCHEDULE, AS A COMPILE-TIME FACT. A batch whose matrices
  // are all one height is the flat opening this file did before; a batch at
  // several heights pays one path with the shorter matrices' row digests
  // injected at the level their height names.
  const batchHeights = batches.map((b) =>
    [...new Set(b.matrices.map((m) => m.logHeight))].sort((x, y) => y - x),
  );
  for (let b = 0; b < nBatches; b++) {
    const top = batchHeights[b][0];
    if (batchHeights[b].length > 1 && batches[b].pathDepth !== top)
      throw new Error(
        `batch ${b} sits at heights [${batchHeights[b]}] and opens with a depth-` +
          `${batches[b].pathDepth} path. A mixed-height \`verify_batch\` walks the tallest ` +
          `matrix's own ${top} levels, injecting at the level each shorter height names; a ` +
          'shorter path would inject at the wrong levels and still produce a digest.',
      );
  }

  // ⚑ THE ROLL-IN SCHEDULE IS A COMPILE-TIME CONSEQUENCE OF THE HEIGHTS, and
  // `rollInSchedule` recomputes it inside the circuit from the same heights, so
  // a disagreement throws at build time rather than folding silently.
  const heights = [...new Set(batches.flatMap((b) => b.matrices.map((m) => m.logHeight)))].sort(
    (x, y) => y - x,
  );
  if (heights[0] !== logGlobalMaxHeight)
    throw new Error(
      `the tallest input matrix is at ${heights[0]}, not log_global_max_height ${logGlobalMaxHeight}`,
    );

  // ⚑ THE TWO NAMES ARE NOW DERIVED FROM THE WIRING RATHER THAN FROM THE AIR,
  // and the assertion is what keeps that from being a redefinition: at the
  // fixture's shape `nOpenedTrace` is still `hasTraceNext ? 2w : w` and
  // `nQuotientVals` is still `chunks · D`. At four rounds the AIR-derived form
  // has no meaning at all — `openedQuotient` carries the quotient, preprocessed
  // AND permutation rounds — and the wiring-derived one is exact.
  const airOpenedTrace = air.hasTraceNext ? 2 * air.width : air.width;
  if (nBatches === 2 && nOpenedTrace !== airOpenedTrace)
    throw new Error(
      `round 0 opens ${nOpenedTrace} values and the AIR shape implies ${airOpenedTrace}`,
    );
  return {
    sh,
    suite: sh.suite ?? babyBearSuite,
    derive,
    nBatches,
    maxCommitDepth: Math.max(...sh.commitPathDepths, 1),
    maxInputDepth: Math.max(...batches.map((b) => b.pathDepth), 1),
    rowWidths,
    totalRow: rowWidths.reduce((a, b) => a + b, 0),
    nTraceCols: air.width,
    nQuotientVals: nOpenedValues - nOpenedTrace,
    nOpenedTrace,
    nRollIns: heights.length - 1,
    pointScales,
    wiring,
    nOpenedValues,
    batchHeights,
  };
}

/** The public claim's shape. A factory because every array length is a shape
 *  parameter; the SAME class is used by the monolith and by every partitioned
 *  step, so a step cannot re-witness a differently shaped claim. */
export function makeDreggProofClaim(sh: DreggProofShape) {
  const { knobs, air } = sh;
  const Digest = (sh.suite ?? babyBearSuite).Digest;
  return class DreggProofClaim extends Struct({
    /** `commitments.trace`, `commitments.quotient_chunks`, ... — one per batch,
     *  in the order `coms_to_verify` builds them. `cap_height = 0`, so each is
     *  ONE digest. */
    inputCommits: Provable.Array(Digest, sh.batches.length),
    /** `opening_proof.commit_phase_commits`. */
    commitPhaseCommits: Provable.Array(Digest, knobs.layers),
    /** `opening_proof.final_poly`. */
    finalPoly: Provable.Array(BbExt, knobs.finalPolyLen),
    /** The STARK's public values — in the transcript AND, for this AIR, in two
     *  of the constraints. */
    publicValues: Provable.Array(Field, Math.max(air.numPublicValues, 1)),
  }) {};
}

/** A claim's VALUES, structurally — so the pieces below take the claim without
 *  each needing the shape's own class. */
export type ClaimValue = {
  inputCommits: Digestish[];
  commitPhaseCommits: Digestish[];
  finalPoly: BbExt[];
  publicValues: Field[];
};

/** What §1 derives and §3–§4 consume. **This is the set a step boundary has to
 *  carry**, and it is the reason `DreggProofPartition` exists. */
export type StarkChallenges = {
  alphaStark: BbExt;
  zeta: BbExt;
  friAlpha: BbExt;
  betas: BbExt[];
  queryBits: Bool[][];
};

/** (0) Range-check the witnessed proof data. Every step that re-witnesses the
 *  proof pays this again — an unchecked lane makes the whole bound chain in
 *  `Poseidon2BabyBearW16` a claim about numbers nothing forces to be small. */
export function assertProofDataInRange(
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
) {
  for (const e of openedTrace) assertExtInRange(e);
  for (const e of openedQuotient) assertExtInRange(e);
  for (const v of claim.publicValues) assertLaneLt2p31(v);
}

/** (1) The transcript — `uni-stark`'s preamble, then FRI's own schedule. */
export function deriveStarkChallenges(
  plan: VerifyPlan,
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
  queryPowWitness: Field,
  /** Read ONLY when the shape says the challenges are carried rather than
   *  derived — a partitioned walk step, or the §3.15e twin that measures what
   *  deriving costs. Absent it, a non-deriving shape is a build error rather
   *  than a circuit that quietly witnesses zero. */
  wit?: {
    alphaStark: BbExt;
    zeta: BbExt;
    friAlpha: BbExt;
    betas: BbExt[];
    queryBits: Bool[][];
  },
): StarkChallenges {
  const { sh, derive } = plan;
  const { knobs, air } = sh;
  const { layers, numQueries, indexBits: nIndexBits } = knobs;
  if (derive) {
    const c: ChallengerLike<any> = plan.suite.newChallenger();
    // `challenger.observe(Val::from_usize(..))` x3 — SHAPE data, fixed by
    // the circuit, so constants: a prover that changed `degree_bits`
    // would be proving against a different compiled program.
    c.observeConstant(BigInt(air.degreeBits));
    c.observeConstant(BigInt(air.baseDegreeBits));
    c.observeConstant(BigInt(air.preprocessedWidth));
    c.observeDigest(claim.inputCommits[0]); //  commitments.trace
    if (air.numPublicValues > 0) c.observeSlice(claim.publicValues.slice(0, air.numPublicValues));
    const alphaStark = c.sampleExt();
    c.observeDigest(claim.inputCommits[1]); //  commitments.quotient_chunks
    const zeta = c.sampleExt();

    // `two_adic_pcs::verify` observes every opened evaluation, in round
    // order, BEFORE `verify_fri` samples its alpha. Moving one moves
    // every challenge below.
    for (const e of openedTrace) c.observeExt(e);
    for (const e of openedQuotient) c.observeExt(e);

    const friAlpha = c.sampleExt();
    const betas: BbExt[] = [];
    for (let r = 0; r < layers; r++) {
      c.observeDigest(claim.commitPhaseCommits[r]);
      // commit_pow_bits = 0: observes NOTHING, constrains nothing.
      c.assertCheckWitness(knobs.commitPowBits, Field(0));
      betas.push(c.sampleExt());
    }
    for (const coeff of claim.finalPoly) c.observeExt(coeff);
    for (let r = 0; r < layers; r++) c.observeConstant(BigInt(knobs.maxLogArity));
    c.assertCheckWitness(knobs.queryPowBits, queryPowWitness);
    const queryBits = Array.from({ length: numQueries }, () => c.sampleBitsAsBits(nIndexBits));
    return { alphaStark, zeta, friAlpha, betas, queryBits };
  }
  if (!wit)
    throw new Error(
      'deriveStarkChallenges: the shape says the challenges are CARRIED, and none were supplied',
    );
  queryPowWitness.seal();
  return carriedChallenges(wit);
}

/** A CARRIED challenge set, range-checked. A re-witnessed lane is unconstrained
 *  until it is checked, and every step past the transcript re-witnesses the whole
 *  set in order to re-derive `challengeDigest` — so this is the one place that
 *  makes the carried transcript mean anything, and it has exactly one
 *  implementation. */
export function carriedChallenges(wit: StarkChallenges): StarkChallenges {
  assertExtInRange(wit.alphaStark);
  assertExtInRange(wit.zeta);
  assertExtInRange(wit.friAlpha);
  for (const b of wit.betas) assertExtInRange(b);
  return {
    alphaStark: wit.alphaStark,
    zeta: wit.zeta,
    friAlpha: wit.friAlpha,
    betas: wit.betas,
    queryBits: wit.queryBits,
  };
}

/** (2) The AIR closing equality at `zeta`. */
export function assertAirClosing(
  plan: VerifyPlan,
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
  ch: StarkChallenges,
) {
  const { sh, nTraceCols } = plan;
  const { air } = sh;
  if (!sh.constraints) return;
  // ⚑ THE TWO-ROUND REFUSAL THAT SURVIVED THE FOUR-ROUND MERGE, AND MUST.
  // `verifyPlan` no longer refuses a third PCS round because the OPENING wiring
  // stopped being inferred from the batch index. This function's wiring still
  // is: `openedQuotient` is read as `numQuotientChunks` consecutive chunks, and
  // at four rounds it carries the preprocessed and permutation rounds too. The
  // root supplies no `constraints` — its AIR closing equality is `RootAirChain`'s
  // seven slices over 1,093 constraints — so this is unreachable today, and it
  // refuses rather than folding a permutation column as a quotient chunk if a
  // caller ever does supply one.
  if (plan.nBatches !== 2)
    throw new Error(
      `the AIR closing equality is wired for the two-round uni-stark shape and this proof has ` +
        `${plan.nBatches} PCS rounds. \`openedQuotient\` would be read as ${air.numQuotientChunks} ` +
        'quotient chunks while it actually carries the later rounds as well. A batch-STARK closes ' +
        'its AIR per instance — see `RootAirChain` — and that is not this function.',
    );
  const sels = selectorsAtPoint(ch.zeta, air.traceLogSize, 1n, air.subgroupGenInv);
  const traceLocal = openedTrace.slice(0, nTraceCols);
  const traceNext = air.hasTraceNext
    ? openedTrace.slice(nTraceCols, 2 * nTraceCols)
    : Array.from({ length: nTraceCols }, () => BbExt.zero());
  const cs = sh.constraints({
    traceLocal,
    traceNext,
    publicValues: claim.publicValues,
    isFirstRow: sels.isFirstRow,
    isLastRow: sels.isLastRow,
    isTransition: sels.isTransition,
    zeta: ch.zeta,
  });
  const acc = foldConstraints(ch.alphaStark, cs);
  const quotient = recomposeQuotient({
    zeta: ch.zeta,
    chunks: Array.from({ length: air.numQuotientChunks }, (_, i) =>
      openedQuotient.slice(i * EXT_D, (i + 1) * EXT_D),
    ),
    logChunkSize: air.chunkLogSize,
    chunkShiftInvs: air.chunkShiftInvs,
    lagrangeConsts: air.lagrangeConstInvs,
  });
  const lhs = extMul(acc, sels.invVanishing);
  for (let j = 0; j < EXT_D; j++)
    canonicalLane(lhs.limbs[j], LANE_MAX).assertEquals(canonicalLane(quotient.limbs[j], LANE_MAX));
}

/** What ONE query's input phase hands to its fold chain: the reduced openings at
 *  each opened height and the roll-in schedule they imply.
 *
 * ⚑ THIS IS THE INTRA-QUERY STEP BOUNDARY, and it is the cheap one. Everything a
 * fold chain needs from the first half of its own query is `ro` — one extension
 * element per opened height — plus the index bits. The whole opened-value set,
 * every input Merkle path and the leaf rows are read by the first half and never
 * again, which is why a cut HERE carries a fold value and a cut at a query ENTRY
 * carries the entire claim (§3.20). `DreggProofSchedule` is what exploits it. */
export type QueryDeepResult = {
  ro: { logHeight: number; ro: BbExt }[];
  rollInRounds: number[];
  indexAcc: Field;
};

/**
 * (3a) ONE query's input-phase MMCS openings — every round, at whatever mix of
 * heights it commits. Returns each batch's rows SPLIT BY MATRIX, which is what
 * the DEEP quotient consumes next.
 *
 * ⚑ A SEAM, NOT A HELPER. This is the half of a query the four-round merge
 * changed, and it is separated so a measurement can price it ALONE — at
 * BabyBear against Pasta, on dregg's real four-round geometry — rather than
 * inferring its share of a combined figure. `runQueryInputAndDeep` calls it, so
 * the priced object and the verified object are the same code.
 */
export function verifyInputBatches(
  plan: VerifyPlan,
  claim: ClaimValue,
  rowsQ: Field[],
  inputPathsQ: Digestish[][],
  bits: Bool[],
  /** ⚑ MEASUREMENT ONLY, and it changes NOTHING about what is verified: which
   *  batches emit their opening. Absent, all of them — which is the only form
   *  any verifier calls. A row measurement uses it to price one PCS round at a
   *  time, because the rounds sit at different widths and a single combined
   *  figure hides which one the hash swap actually moves. The row split is
   *  tracked for every batch either way, so a selected batch's gates are
   *  identical to the ones it emits in a full call. */
  only?: number[],
): Field[][][] {
  const { sh, suite, nBatches, rowWidths, batchHeights } = plan;
  const { batches, logGlobalMaxHeight } = sh;
  // ⚑ THE SUITE'S RANGE CHECKS HAVE TO EXIST BEFORE THEY ARE USED. Absent for
  // BabyBear — which is why no measured BabyBear row count moves — and one
  // `RangeCheck0` for Pasta, without which a body made only of Pasta MMCS work
  // compiles, analyses, passes `runAndCheck` and dies in `prove()`. See
  // `PastaMmcs.assertPastaLookupTable` for the measurement that found it.
  suite.anchorLookupTable?.();
  const out: Field[][][] = [];
  let rowOff = 0;
  for (let b = 0; b < nBatches; b++) {
    const bs = batches[b];
    if (only && !only.includes(b)) {
      const leafSkip = rowsQ.slice(rowOff, rowOff + rowWidths[b]);
      rowOff += rowWidths[b];
      const perSkip: Field[][] = [];
      let off = 0;
      for (const m of bs.matrices) {
        perSkip.push(leafSkip.slice(off, off + m.numCols));
        off += m.numCols;
      }
      out.push(perSkip);
      continue;
    }
    const leaf = rowsQ.slice(rowOff, rowOff + rowWidths[b]);
    rowOff += rowWidths[b];

    //  Split the leaf into its matrices' rows FIRST: a mixed-height batch
    //  sponges them in height groups rather than as one run.
    const perMat: Field[][] = [];
    let colOff = 0;
    for (const m of bs.matrices) {
      perMat.push(leaf.slice(colOff, colOff + m.numCols));
      colOff += m.numCols;
    }
    const hs = batchHeights[b];
    const rowsAt = (h: number) =>
      bs.matrices.flatMap((m, i) => (m.logHeight === h ? perMat[i] : []));

    // The MMCS leaf is ONE sponge over the rows of the matrices at the TALLEST
    // padded height, concatenated in committed order — not one hash per matrix,
    // and not one hash over the whole batch when the batch is mixed. The row is
    // a fresh witness, so the suite bounds every lane here: BabyBear packs 8
    // lanes per permutation and Pasta 16, but BOTH need `< 2^31` per lane — for
    // BabyBear to keep `provablePermBounded`'s bound chain meaningful, for Pasta
    // to make the shifted radix-2^31 pack injective.
    const top = hs[0];
    let cur = suite.sponge(rowsAt(top));
    // `open_input` shifts the index by the BATCH's max height, not the
    // matrix's (`fri/src/verifier.rs:576-580`).
    const bitsReduced = logGlobalMaxHeight - top;
    for (let h = 0; h < bs.pathDepth; h++) {
      suite.assertInRange(inputPathsQ[b][h]);
      const [l, r] = suite.condSwap(cur, inputPathsQ[b][h], bits[bitsReduced + h]);
      cur = suite.compress(l, r);
      // ⚑ THE MIXED-HEIGHT INJECTION. After the compress, `curr_height_padded`
      // is `2^(top-1-h)`; a matrix whose padded height is exactly that has its
      // own row digest compressed into the running root. Four of them per round
      // at dregg's root, none at the fixture. A flat path that skipped these is
      // a different tree and produces a digest, not an error.
      const nextH = top - 1 - h;
      if (hs.includes(nextH)) cur = suite.compress(cur, suite.sponge(rowsAt(nextH)));
    }
    suite.assertEq(cur, claim.inputCommits[b]);
    out.push(perMat);
  }
  return out;
}

/**
 * (3b) Attach each matrix's claimed evaluations, from the wiring — the whole of
 * what the four-round merge replaced a `b === 0` switch with.
 *
 * Emits NO gates: it is array slicing over values the caller already holds. It
 * is separate so a measurement can build the DEEP quotient's input without
 * re-deriving the wiring, which would be a second reading of the thing most
 * likely to be got wrong.
 */
export function deepMatricesOf(
  plan: VerifyPlan,
  opened: BbExt[],
  zPoints: BbExt[],
  perBatch: Field[][][],
): DeepMatrix[][] {
  const { sh, nBatches, wiring } = plan;
  const mats: DeepMatrix[][] = [];
  for (let b = 0; b < nBatches; b++) {
    const batchMats: DeepMatrix[] = [];
    for (let i = 0; i < sh.batches[b].matrices.length; i++) {
      const m = sh.batches[b].matrices[i];
      const points = wiring[b][i].map((w) => ({
        z: zPoints[w.scaleIndex],
        psAtZ: opened.slice(w.offset, w.offset + w.len),
      }));
      if (points.length !== m.numPoints)
        throw new Error(
          `batch ${b} matrix declares ${m.numPoints} points, the wiring gives ${points.length}`,
        );
      batchMats.push({ logHeight: m.logHeight, openedRow: perBatch[b][i], points });
    }
    mats.push(batchMats);
  }
  return mats;
}

/** (3) ONE query's input phase and DEEP quotient — the half that reads the
 *  opened values. `q` indexes this call's witness arrays; `g` is the GLOBAL
 *  query index, which is what `ch.queryBits` is indexed by. */
export function runQueryInputAndDeep(
  plan: VerifyPlan,
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
  ch: StarkChallenges,
  /** The extension values of every distinct `ζ · c` in `plan.pointScales`, in
   *  that order — `zetaPointsOf`'s output, computed ONCE per proof outside the
   *  query loop. */
  zPoints: BbExt[],
  rowsQ: Field[],
  inputPathsQ: Digestish[][],
  g: number,
): QueryDeepResult {
  const { sh, nBatches, nRollIns, wiring } = plan;
  const { knobs, batches, logGlobalMaxHeight } = sh;
  const { layers, indexBits: nIndexBits } = knobs;
  const bits = ch.queryBits[g];
  if (zPoints.length !== plan.pointScales.length)
    throw new Error(
      `${zPoints.length} opening points for ${plan.pointScales.length} distinct scales`,
    );
  //  The whole opened-value list, in p3's observe order. The two arguments keep
  //  their names because at the fixture's shape they ARE the trace round and the
  //  quotient round; at four rounds the second is every non-main round, and the
  //  wiring — not the argument boundary — says which values belong to which
  //  matrix.
  const opened = [...openedTrace, ...openedQuotient];

  const perBatch = verifyInputBatches(plan, claim, rowsQ, inputPathsQ, bits);
  const mats = deepMatricesOf(plan, opened, zPoints, perBatch);

  // -- the DEEP quotient: `initial` stops being a witness.
  const ro = reducedOpenings({
    indexBits: bits,
    logGlobalMaxHeight,
    alpha: ch.friAlpha,
    batches: mats,
  });
  const sched = rollInSchedule(ro, logGlobalMaxHeight, layers);
  if (sched.rounds.length !== nRollIns)
    throw new Error('the in-circuit roll-in schedule disagrees with the compiled shape');

  let acc = Field(0);
  for (let i = 0; i < nIndexBits; i++) acc = acc.add(bits[i].toField().mul(1n << BigInt(i)));
  return { ro, rollInRounds: sched.rounds, indexAcc: acc };
}

/** (4) ONE query's fold chain — the half that reads NONE of the opened values.
 *  It needs the commit-phase commitments, the betas, the final polynomial, the
 *  index bits and `deep.ro`, and nothing else. */
export function runQueryCommitPhase(
  plan: VerifyPlan,
  claim: ClaimValue,
  ch: StarkChallenges,
  deep: QueryDeepResult,
  siblingsQ: BbExt[],
  commitPathsQ: Digestish[][],
  g: number,
): void {
  const { sh } = plan;
  const { knobs, logGlobalMaxHeight } = sh;
  const { layers } = knobs;
  verifyCommitPhase({
    indexBits: ch.queryBits[g],
    initial: deep.ro[0].ro,
    rounds: Array.from({ length: layers }, (_, r) => ({
      sibling: siblingsQ[r],
      path: commitPathsQ[r].slice(0, sh.commitPathDepths[r]),
      beta: ch.betas[r],
      commit: claim.commitPhaseCommits[r],
    })),
    rollIns: deep.rollInRounds.map((r, i) => ({ afterRound: r, value: deep.ro[i + 1].ro })),
    finalPoly: claim.finalPoly,
    logGlobalMaxHeight,
    suite: plan.suite,
  });
}

/**
 * Every distinct opening point, DERIVED from ζ.
 *
 * `zeta_next = zeta * g` on the NATURAL trace domain (`domain.rs:169-171`), and
 * a batch-STARK has one such `g` per instance because each instance has its own
 * trace size. `g` is protocol data, so each scale is a constant multiply —
 * `extScaleConst` returns ζ itself at scale 1 without emitting a gate, so the
 * count of real multiplies is the number of DISTINCT next-row domains and not
 * the number of matrices. dregg's root has seven instances at five distinct
 * `degree_bits`, one of which is 0, so it costs four.
 *
 * ⚑ COMPUTED ONCE PER PROOF, OUTSIDE THE QUERY LOOP — which is where the
 * fixture's single `ζ·g` already was. Moving it inside would be nineteen copies
 * and would move every recorded row count in this arc.
 */
export function zetaPointsOf(plan: VerifyPlan, zeta: BbExt): BbExt[] {
  return plan.pointScales.map((c) => extScaleConst(zeta, c));
}

/** The legacy single next-row point — the fixture's `ζ·g`. Kept because the
 *  scheduled and partitioned chains name it, and defined in terms of the table
 *  above so the two cannot drift. */
export function zetaNextOf(plan: VerifyPlan, zeta: BbExt): BbExt {
  return extScaleConst(zeta, twoAdicGenerator(plan.sh.air.traceLogSize));
}

/** (3+4) The opening points and every query walk. Returns the DERIVED query
 *  indices — the walk's own account of where it went. */
export function runQueryWalk(
  plan: VerifyPlan,
  claim: ClaimValue,
  openedTrace: BbExt[],
  openedQuotient: BbExt[],
  ch: StarkChallenges,
  rows: Field[][],
  inputPaths: Digestish[][][],
  siblings: BbExt[][],
  commitPaths: Digestish[][][],
  /** ⚑ THE PARTITION'S ONLY REACH INTO THIS FUNCTION. Which GLOBAL query indices
   *  this call walks; `rows`/`inputPaths`/`siblings`/`commitPaths` are indexed by
   *  position in this list, while `ch.queryBits` is indexed GLOBALLY — because
   *  the carried Fiat-Shamir state is the whole index set and a step walks a
   *  slice of it. Absent, every query, which is the one-step program. */
  queries?: number[],
): Field[] {
  const { numQueries } = plan.sh.knobs;
  const qs = queries ?? Array.from({ length: numQueries }, (_, i) => i);
  for (const g of qs)
    if (g < 0 || g >= numQueries)
      throw new Error(`query ${g} is outside the shape's 0..${numQueries - 1}`);

  const zPoints = zetaPointsOf(plan, ch.zeta);

  // ⚑ THE TWO HALVES ARE CALLED, NOT RE-IMPLEMENTED. `DreggProofSchedule` puts a
  // step boundary between them; if this function inlined the same work a second
  // time, the monolith and the scheduled chain would be two verifiers that agree
  // today. The gate order is identical to the inlined version, which is why the
  // §3.20 row ratchet still holds to the row.
  const outIndices: Field[] = [];
  for (let q = 0; q < qs.length; q++) {
    const deep = runQueryInputAndDeep(
      plan,
      claim,
      openedTrace,
      openedQuotient,
      ch,
      zPoints,
      rows[q],
      inputPaths[q],
      qs[q],
    );
    runQueryCommitPhase(plan, claim, ch, deep, siblings[q], commitPaths[q], qs[q]);
    outIndices.push(deep.indexAcc);
  }
  return outIndices;
}

// ===========================================================================
// 3b. The one-step program — the four pieces above, in order.
// ===========================================================================

export function makeDreggProofVerifyProgram(sh: DreggProofShape) {
  const plan = verifyPlan(sh);
  const { knobs, air, logGlobalMaxHeight } = sh;
  const { layers, numQueries, indexBits: nIndexBits } = knobs;
  const derive = plan.derive;
  const {
    nBatches,
    maxCommitDepth,
    maxInputDepth,
    rowWidths,
    totalRow,
    nQuotientVals,
    nOpenedTrace,
  } = plan;

  const DreggProofClaim = makeDreggProofClaim(sh);

  const privateInputs = [
    Provable.Array(BbExt, nOpenedTrace), //                 trace_local (+ trace_next)
    Provable.Array(BbExt, nQuotientVals), //                quotient_chunks, flattened
    Field, //                                               query_pow_witness
    Provable.Array(Provable.Array(Field, totalRow), numQueries), //          opened rows
    Provable.Array(
      Provable.Array(Provable.Array(plan.suite.Digest, maxInputDepth), nBatches),
      numQueries,
    ), //                                                   input-phase paths
    Provable.Array(Provable.Array(BbExt, layers), numQueries), //            fold siblings
    Provable.Array(
      Provable.Array(Provable.Array(plan.suite.Digest, maxCommitDepth), layers),
      numQueries,
    ), //                                                   commit-phase paths
    // ⚑ ONLY read when `deriveChallenges` is false — the twin that measures what
    // deriving costs. They are declared unconditionally so both programs take
    // the same arguments and the delta is the derivation and nothing else.
    BbExt, //                                               witnessed alpha_stark
    BbExt, //                                               witnessed zeta
    BbExt, //                                               witnessed fri alpha
    Provable.Array(BbExt, layers), //                       witnessed betas
    Provable.Array(Provable.Array(Bool, nIndexBits), numQueries), // witnessed indices
  ];

  const prog = ZkProgram({
    name: `dregg-proof-verify-w${air.width}-q${numQueries}-l${layers}-h${logGlobalMaxHeight}${
      derive ? '' : '-witnessed'
    }${sh.constraints ? '' : '-noair'}`,
    publicInput: DreggProofClaim,
    /** The DERIVED query indices — the walk's own account of where it went. */
    publicOutput: Provable.Array(Field, numQueries),
    methods: {
      // The private-input list is built from the SHAPE, so its length is not a
      // literal tuple TypeScript can track; the `as any` is that and nothing
      // else. What checks the wiring is the `analyzeMethods`/`compile`
      // round-trip the leg runs, which fails loudly on an arity mismatch.
      verifyDreggProof: {
        privateInputs: privateInputs as any,
        async method(
          claim: InstanceType<typeof DreggProofClaim>,
          openedTrace: BbExt[],
          openedQuotient: BbExt[],
          queryPowWitness: Field,
          rows: Field[][],
          inputPaths: Digestish[][][],
          siblings: BbExt[][],
          commitPaths: Digestish[][][],
          witAlphaStark: BbExt,
          witZeta: BbExt,
          witFriAlpha: BbExt,
          witBetas: BbExt[],
          witIndexBits: Bool[][],
        ) {
          assertProofDataInRange(claim, openedTrace, openedQuotient);
          const ch = deriveStarkChallenges(plan, claim, openedTrace, openedQuotient, queryPowWitness, {
            alphaStark: witAlphaStark,
            zeta: witZeta,
            friAlpha: witFriAlpha,
            betas: witBetas,
            queryBits: witIndexBits,
          });
          assertAirClosing(plan, claim, openedTrace, openedQuotient, ch);
          const outIndices = runQueryWalk(
            plan,
            claim,
            openedTrace,
            openedQuotient,
            ch,
            rows,
            inputPaths,
            siblings,
            commitPaths,
          );

          return { publicOutput: outIndices };
        },
      },
    },
  });

  return { prog, DreggProofClaim, nOpenedTrace, nQuotientVals, totalRow, rowWidths, maxInputDepth, maxCommitDepth };
}

// ===========================================================================
// 4. Reading the Rust emitter's fixture into the shape and the witness.
// ===========================================================================

const B = (v: number | string) => BigInt(v);

/** The JSON the dregg-side emitters print — `mina_stark_fixture` (BabyBear) and
 *  `mina_pasta_stark_fixture` (Pasta). ONE schema, one `hash` field. */
export type Fixture = any;

/**
 * ⚑ THE HASH IS READ OFF THE FIXTURE, NOT PASSED IN. A fixture carries the name
 * of the config it was minted under, so a Pasta proof handed to this verifier
 * gets the Pasta suite because it SAYS so — not because a caller remembered. A
 * fixture with no `hash` field predates the Pasta emitter and is BabyBear;
 * anything else is refused by name in `suiteByName`.
 */
export function suiteOf(fx: Fixture): HashSuite<any> {
  return suiteByName(fx.hash ?? 'poseidon2-babybear-w16');
}

/** Derive the compile-time shape from an emitted fixture. */
export function shapeOf(fx: Fixture, opts?: { constraints?: ConstraintEvaluator; deriveChallenges?: boolean }): DreggProofShape {
  const k = fx.knobs;
  const s = fx.shape;
  const suite = suiteOf(fx);
  if (fx.digestElems !== undefined && fx.digestElems !== suite.digestElems)
    throw new Error(
      `fixture '${fx.hash}' declares ${fx.digestElems} digest elements, the '${suite.name}' ` +
        `suite has ${suite.digestElems}`,
    );
  const knobs: FriKnobs = {
    logBlowup: k.logBlowup,
    logFinalPolyLen: k.logFinalPolyLen,
    commitPowBits: k.commitPowBits,
    queryPowBits: k.queryPowBits,
    maxLogArity: k.maxLogArity,
    numQueries: k.numQueries,
    logGlobalMaxHeight: s.logGlobalMaxHeight,
    extraQueryIndexBits: 0,
    layers: s.layers,
    indexBits: s.logGlobalMaxHeight,
    finalPolyLen: 1 << k.logFinalPolyLen,
  };
  const qp0 = fx.fri.queryProofs[0];
  return {
    knobs,
    logGlobalMaxHeight: s.logGlobalMaxHeight,
    commitPathDepths: qp0.commitPhaseOpenings.map((o: any) => o.openingProof.length),
    batches: [
      {
        matrices: [
          {
            logHeight: s.traceLdeLogHeight,
            numCols: s.airWidth,
            numPoints: s.hasTraceNext ? 2 : 1,
          },
        ],
        pathDepth: qp0.inputProof[0].openingProof.length,
      },
      {
        matrices: Array.from({ length: s.numQuotientChunks }, () => ({
          logHeight: s.quotientLdeLogHeight,
          numCols: k.extDegree,
          numPoints: 1,
        })),
        pathDepth: qp0.inputProof[1].openingProof.length,
      },
    ],
    air: {
      degreeBits: s.degreeBits,
      baseDegreeBits: s.baseDegreeBits,
      preprocessedWidth: s.preprocessedWidth,
      width: s.airWidth,
      numPublicValues: s.numPublicValues,
      numQuotientChunks: s.numQuotientChunks,
      hasTraceNext: s.hasTraceNext,
      traceLogSize: fx.domain.traceLogSize,
      subgroupGenInv: B(fx.domain.subgroupGenInv),
      chunkLogSize: fx.domain.chunkLogSize,
      chunkShiftInvs: fx.domain.chunkShiftInvs.map(B),
      lagrangeConstInvs: fx.domain.lagrangeConstInvs.map((r: any[]) => r.map(B)),
    },
    constraints: opts?.constraints,
    deriveChallenges: opts?.deriveChallenges,
    suite,
  };
}

const ext = (v: (number | string)[]) => BbExt.from(v.map(B));

/** One emitted digest -> this suite's digest. ⚑ A Pasta element is emitted as a
 *  canonical DECIMAL STRING because it does not fit a JSON number; `BigInt`
 *  takes either, so the ONE decoder serves both schemas and there is no place
 *  for a "which encoding is this" branch to be got wrong. */
const digOf = (suite: HashSuite<any>) => (v: (number | string)[]) => {
  if (v.length !== suite.digestElems)
    throw new Error(`emitted digest has ${v.length} elements, '${suite.name}' has ${suite.digestElems}`);
  return suite.from(v.map(B));
};

/** The public claim, from an emitted fixture. */
export function claimOf(fx: Fixture, Claim: any) {
  const dig = digOf(suiteOf(fx));
  const npv = Math.max(fx.shape.numPublicValues, 1);
  const pvs = Array.from({ length: npv }, (_, i) =>
    Field(B(fx.publicValues[i] ?? 0)),
  );
  return new Claim({
    inputCommits: [dig(fx.commitments.trace[0]), dig(fx.commitments.quotient[0])],
    commitPhaseCommits: fx.fri.commitPhaseCommits.map((c: any) => dig(c[0])),
    finalPoly: fx.fri.finalPoly.map(ext),
    publicValues: pvs,
  });
}

/** The private witness, from an emitted fixture. In the same order the method
 *  declares. */
export function witnessOf(fx: Fixture, sh: DreggProofShape): any[] {
  const s = fx.shape;
  const suite = sh.suite ?? babyBearSuite;
  const dig = digOf(suite);
  const openedTrace = [
    ...fx.openedValues.traceLocal.map(ext),
    ...(s.hasTraceNext ? fx.openedValues.traceNext.map(ext) : []),
  ];
  const openedQuotient = fx.openedValues.quotientChunks.flatMap((c: any) => c.map(ext));
  const pad = (arr: Digestish[], n: number) =>
    arr.length >= n ? arr.slice(0, n) : [...arr, ...Array.from({ length: n - arr.length }, () => suite.zero())];

  const maxInputDepth = Math.max(...sh.batches.map((b) => b.pathDepth), 1);
  const maxCommitDepth = Math.max(...sh.commitPathDepths, 1);

  const rows: Field[][] = [];
  const inputPaths: Digestish[][][] = [];
  const siblings: BbExt[][] = [];
  const commitPaths: Digestish[][][] = [];
  for (const qp of fx.fri.queryProofs) {
    rows.push(qp.inputProof.flatMap((b: any) => b.openedValues.flat().map((v: any) => Field(B(v)))));
    inputPaths.push(qp.inputProof.map((b: any) => pad(b.openingProof.map(dig), maxInputDepth)));
    siblings.push(qp.commitPhaseOpenings.map((o: any) => ext(o.siblingValues[0])));
    commitPaths.push(qp.commitPhaseOpenings.map((o: any) => pad(o.openingProof.map(dig), maxCommitDepth)));
  }

  const ch = fx.challenges;
  const idxBits = ch.queryIndices.map((idx: number) =>
    Array.from({ length: sh.knobs.indexBits }, (_, i) => Bool(((BigInt(idx) >> BigInt(i)) & 1n) === 1n)),
  );

  return [
    openedTrace,
    openedQuotient,
    Field(B(fx.fri.queryPowWitness)),
    rows,
    inputPaths,
    siblings,
    commitPaths,
    ext(ch.alphaStark),
    ext(ch.zeta),
    ext(ch.friAlpha),
    ch.betas.map(ext),
    idxBits,
  ];
}

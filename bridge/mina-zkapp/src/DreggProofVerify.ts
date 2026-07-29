import { Bool, Field, Provable, Struct, ZkProgram } from 'o1js';
import { assertLaneLt2p31, canonicalLane } from './Poseidon2BabyBearW16.js';
import { BbDigest, compressBB, condSwap, assertDigestInRange, spongeBB } from './Poseidon2Merkle.js';
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
import { Challenger, FriKnobs } from './FriChallenger.js';
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
 *  and how many out-of-domain points it opens at. */
export type MatrixShape = { logHeight: number; numCols: number; numPoints: number };

/** One MMCS commitment and the matrices committed under it. All matrices in a
 *  batch share ONE leaf, hashed over their rows concatenated in order —
 *  `MerkleTreeMmcs::verify_batch` hashes `heights_tallest_first` with a STABLE
 *  sort, so equal heights keep the committed order (`merkle-tree/src/mmcs.rs:
 *  1065-1105`). */
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
// 3. The program.
// ===========================================================================

/** Total base-field lanes in a batch's MMCS leaf. */
const batchRowWidth = (b: BatchShape) => b.matrices.reduce((a, m) => a + m.numCols, 0);

export function makeDreggProofVerifyProgram(sh: DreggProofShape) {
  const { knobs, batches, air, logGlobalMaxHeight } = sh;
  const { layers, finalPolyLen, numQueries, indexBits: nIndexBits } = knobs;
  const derive = sh.deriveChallenges ?? true;
  if (sh.commitPathDepths.length !== layers)
    throw new Error(`commitPathDepths has ${sh.commitPathDepths.length} entries for ${layers} layers`);
  if (nIndexBits !== logGlobalMaxHeight)
    throw new Error('this assembly does not use extra query index bits');

  const nBatches = batches.length;
  // ⚑ THE OPENED-VALUE WIRING BELOW IS TWO-BATCH SPECIFIC and would MIS-WIRE
  // silently if a third round appeared: batch 0's points are (zeta, trace_local)
  // and (zeta*g, trace_next); every other batch's matrix `m` takes quotient
  // chunk `m` at zeta. `coms_to_verify` grows a PREPROCESSED round whenever the
  // AIR has preprocessed columns (`uni-stark/src/verifier.rs:465-476`), and that
  // round's points are neither shape. Refuse rather than wire it wrong.
  if (nBatches !== 2)
    throw new Error(
      `${nBatches} input-phase batches: this assembly wires the trace round and the quotient ` +
        'round only. A preprocessed round needs its own point wiring — see the note here.',
    );
  const maxCommitDepth = Math.max(...sh.commitPathDepths, 1);
  const maxInputDepth = Math.max(...batches.map((b) => b.pathDepth), 1);
  const rowWidths = batches.map(batchRowWidth);
  const totalRow = rowWidths.reduce((a, b) => a + b, 0);
  const nTraceCols = air.width;
  const nQuotientVals = air.numQuotientChunks * EXT_D;
  const nOpenedTrace = air.hasTraceNext ? 2 * nTraceCols : nTraceCols;

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
  const nRollIns = heights.length - 1;

  class DreggProofClaim extends Struct({
    /** `commitments.trace`, `commitments.quotient_chunks`, ... — one per batch,
     *  in the order `coms_to_verify` builds them. `cap_height = 0`, so each is
     *  ONE digest. */
    inputCommits: Provable.Array(BbDigest, nBatches),
    /** `opening_proof.commit_phase_commits`. */
    commitPhaseCommits: Provable.Array(BbDigest, layers),
    /** `opening_proof.final_poly`. */
    finalPoly: Provable.Array(BbExt, finalPolyLen),
    /** The STARK's public values — in the transcript AND, for this AIR, in two
     *  of the constraints. */
    publicValues: Provable.Array(Field, Math.max(air.numPublicValues, 1)),
  }) {}

  const privateInputs = [
    Provable.Array(BbExt, nOpenedTrace), //                 trace_local (+ trace_next)
    Provable.Array(BbExt, nQuotientVals), //                quotient_chunks, flattened
    Field, //                                               query_pow_witness
    Provable.Array(Provable.Array(Field, totalRow), numQueries), //          opened rows
    Provable.Array(
      Provable.Array(Provable.Array(BbDigest, maxInputDepth), nBatches),
      numQueries,
    ), //                                                   input-phase paths
    Provable.Array(Provable.Array(BbExt, layers), numQueries), //            fold siblings
    Provable.Array(
      Provable.Array(Provable.Array(BbDigest, maxCommitDepth), layers),
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
          inputPaths: BbDigest[][][],
          siblings: BbExt[][],
          commitPaths: BbDigest[][][],
          witAlphaStark: BbExt,
          witZeta: BbExt,
          witFriAlpha: BbExt,
          witBetas: BbExt[],
          witIndexBits: Bool[][],
        ) {
          for (const e of openedTrace) assertExtInRange(e);
          for (const e of openedQuotient) assertExtInRange(e);
          for (const v of claim.publicValues) assertLaneLt2p31(v);

          // -- 1. the transcript ------------------------------------------------
          let alphaStark: BbExt;
          let zeta: BbExt;
          let friAlpha: BbExt;
          let betas: BbExt[];
          let queryBits: Bool[][];

          if (derive) {
            const c = new Challenger();
            // `challenger.observe(Val::from_usize(..))` x3 — SHAPE data, fixed by
            // the circuit, so constants: a prover that changed `degree_bits`
            // would be proving against a different compiled program.
            c.observeConstant(BigInt(air.degreeBits));
            c.observeConstant(BigInt(air.baseDegreeBits));
            c.observeConstant(BigInt(air.preprocessedWidth));
            c.observeDigest(claim.inputCommits[0]); //  commitments.trace
            if (air.numPublicValues > 0) c.observeSlice(claim.publicValues.slice(0, air.numPublicValues));
            alphaStark = c.sampleExt();
            c.observeDigest(claim.inputCommits[1]); //  commitments.quotient_chunks
            zeta = c.sampleExt();

            // `two_adic_pcs::verify` observes every opened evaluation, in round
            // order, BEFORE `verify_fri` samples its alpha. Moving one moves
            // every challenge below.
            for (const e of openedTrace) c.observeExt(e);
            for (const e of openedQuotient) c.observeExt(e);

            friAlpha = c.sampleExt();
            betas = [];
            for (let r = 0; r < layers; r++) {
              c.observeDigest(claim.commitPhaseCommits[r]);
              // commit_pow_bits = 0: observes NOTHING, constrains nothing.
              c.assertCheckWitness(knobs.commitPowBits, Field(0));
              betas.push(c.sampleExt());
            }
            for (const coeff of claim.finalPoly) c.observeExt(coeff);
            for (let r = 0; r < layers; r++) c.observeConstant(BigInt(knobs.maxLogArity));
            c.assertCheckWitness(knobs.queryPowBits, queryPowWitness);
            queryBits = Array.from({ length: numQueries }, () => c.sampleBitsAsBits(nIndexBits));
          } else {
            alphaStark = witAlphaStark;
            zeta = witZeta;
            friAlpha = witFriAlpha;
            betas = witBetas;
            queryBits = witIndexBits;
            assertExtInRange(alphaStark);
            assertExtInRange(zeta);
            assertExtInRange(friAlpha);
            for (const b of betas) assertExtInRange(b);
            queryPowWitness.seal();
          }

          // -- 2. the AIR closing equality --------------------------------------
          if (sh.constraints) {
            const sels = selectorsAtPoint(zeta, air.traceLogSize, 1n, air.subgroupGenInv);
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
              zeta,
            });
            const acc = foldConstraints(alphaStark, cs);
            const quotient = recomposeQuotient({
              zeta,
              chunks: Array.from({ length: air.numQuotientChunks }, (_, i) =>
                openedQuotient.slice(i * EXT_D, (i + 1) * EXT_D),
              ),
              logChunkSize: air.chunkLogSize,
              chunkShiftInvs: air.chunkShiftInvs,
              lagrangeConsts: air.lagrangeConstInvs,
            });
            const lhs = extMul(acc, sels.invVanishing);
            for (let j = 0; j < EXT_D; j++)
              canonicalLane(lhs.limbs[j], LANE_MAX).assertEquals(
                canonicalLane(quotient.limbs[j], LANE_MAX),
              );
          }

          // -- 3. the opening points --------------------------------------------
          // `zeta_next = zeta * g` on the NATURAL trace domain
          // (`domain.rs:169-171`); `g` is protocol data, so the scale is free.
          const gTrace = twoAdicGenerator(air.traceLogSize);
          const zetaNext = extScaleConst(zeta, gTrace);

          // -- 4. every query ----------------------------------------------------
          const outIndices: Field[] = [];
          for (let q = 0; q < numQueries; q++) {
            const bits = queryBits[q];
            let rowOff = 0;
            const mats: DeepMatrix[][] = [];
            for (let b = 0; b < nBatches; b++) {
              const bs = batches[b];
              const leaf = rows[q].slice(rowOff, rowOff + rowWidths[b]);
              rowOff += rowWidths[b];
              for (const v of leaf) assertLaneLt2p31(v);

              // The MMCS leaf is ONE sponge over every matrix's row in this
              // batch, concatenated — not one hash per matrix.
              let cur = spongeBB(leaf);
              // `open_input` shifts the index by the BATCH's max height, not the
              // matrix's (`fri/src/verifier.rs:576-580`).
              const batchMax = Math.max(...bs.matrices.map((m) => m.logHeight));
              const bitsReduced = logGlobalMaxHeight - batchMax;
              for (let h = 0; h < bs.pathDepth; h++) {
                assertDigestInRange(inputPaths[q][b][h]);
                const [l, r] = condSwap(cur, inputPaths[q][b][h], bits[bitsReduced + h]);
                cur = compressBB(l, r);
              }
              for (let j = 0; j < 8; j++)
                cur.limbs[j].assertEquals(claim.inputCommits[b].limbs[j]);

              // Split the leaf back into its matrices for the DEEP quotient, and
              // attach the claimed evaluations each one opens at.
              let colOff = 0;
              const batchMats: DeepMatrix[] = [];
              for (const m of bs.matrices) {
                const openedRow = leaf.slice(colOff, colOff + m.numCols);
                colOff += m.numCols;
                const points =
                  b === 0
                    ? // the trace: (zeta, trace_local) and (zeta*g, trace_next)
                      (air.hasTraceNext
                        ? [
                            { z: zeta, psAtZ: openedTrace.slice(0, nTraceCols) },
                            { z: zetaNext, psAtZ: openedTrace.slice(nTraceCols, 2 * nTraceCols) },
                          ]
                        : [{ z: zeta, psAtZ: openedTrace.slice(0, nTraceCols) }])
                    : // a quotient chunk: (zeta, that chunk's D values)
                      [
                        {
                          z: zeta,
                          psAtZ: openedQuotient.slice(
                            batchMats.length * EXT_D,
                            (batchMats.length + 1) * EXT_D,
                          ),
                        },
                      ];
                if (points.length !== m.numPoints)
                  throw new Error(
                    `batch ${b} matrix declares ${m.numPoints} points, the wiring gives ${points.length}`,
                  );
                batchMats.push({ logHeight: m.logHeight, openedRow, points });
              }
              mats.push(batchMats);
            }

            // -- the DEEP quotient: `initial` stops being a witness.
            const ro = reducedOpenings({
              indexBits: bits,
              logGlobalMaxHeight,
              alpha: friAlpha,
              batches: mats,
            });
            const sched = rollInSchedule(ro, logGlobalMaxHeight, layers);
            if (sched.rounds.length !== nRollIns)
              throw new Error('the in-circuit roll-in schedule disagrees with the compiled shape');

            verifyCommitPhase({
              indexBits: bits,
              initial: ro[0].ro,
              rounds: Array.from({ length: layers }, (_, r) => ({
                sibling: siblings[q][r],
                path: commitPaths[q][r].slice(0, sh.commitPathDepths[r]),
                beta: betas[r],
                commit: claim.commitPhaseCommits[r],
              })),
              rollIns: sched.rounds.map((r, i) => ({ afterRound: r, value: ro[i + 1].ro })),
              finalPoly: claim.finalPoly,
              logGlobalMaxHeight,
            });

            let acc = Field(0);
            for (let i = 0; i < nIndexBits; i++)
              acc = acc.add(bits[i].toField().mul(1n << BigInt(i)));
            outIndices.push(acc);
          }

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

/** The JSON `circuit/src/bin/mina_stark_fixture.rs` prints. */
export type Fixture = any;

/** Derive the compile-time shape from an emitted fixture. */
export function shapeOf(fx: Fixture, opts?: { constraints?: ConstraintEvaluator; deriveChallenges?: boolean }): DreggProofShape {
  const k = fx.knobs;
  const s = fx.shape;
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
  };
}

const ext = (v: (number | string)[]) => BbExt.from(v.map(B));
const dig = (v: (number | string)[]) => BbDigest.from(v.map(B));

/** The public claim, from an emitted fixture. */
export function claimOf(fx: Fixture, Claim: any) {
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
  const openedTrace = [
    ...fx.openedValues.traceLocal.map(ext),
    ...(s.hasTraceNext ? fx.openedValues.traceNext.map(ext) : []),
  ];
  const openedQuotient = fx.openedValues.quotientChunks.flatMap((c: any) => c.map(ext));
  const pad = (arr: BbDigest[], n: number) =>
    arr.length >= n ? arr.slice(0, n) : [...arr, ...Array.from({ length: n - arr.length }, () => BbDigest.zero())];

  const maxInputDepth = Math.max(...sh.batches.map((b) => b.pathDepth), 1);
  const maxCommitDepth = Math.max(...sh.commitPathDepths, 1);

  const rows: Field[][] = [];
  const inputPaths: BbDigest[][][] = [];
  const siblings: BbExt[][] = [];
  const commitPaths: BbDigest[][][] = [];
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

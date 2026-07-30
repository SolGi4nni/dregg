import { Bool, Field } from 'o1js';
import { P } from './Poseidon2BabyBearW16.js';
import { BbExt, EXT_D, extMulBigInt, twoAdicGenerator } from './FriQueryStep.js';
import { FriKnobs } from './FriChallenger.js';
import type { Digestish, HashSuite, MerkleSuite } from './HashSuiteType.js';
import { babyBearSuite, pastaSuite } from './HashSuites.js';
import {
  extInvBigInt,
  reducedOpeningsBigInt,
  type DeepMatBigInt,
} from './DeepQuotient.js';
import type { ClaimValue, DreggProofShape, MatrixShape } from './DreggProofVerify.js';
import type { RealRootFri } from './RootFriWalk.js';

// ---------------------------------------------------------------------------
// dregg's COMMITTED ROOT PROOF, AS SOMETHING THE ASSEMBLY CAN CONSUME.
//
// ⚑ THE GAP THIS FILE CLOSES, NAMED BY THE LANE THAT FOUND IT. There were two
// halves of "Mina verifies dregg" and each was missing exactly what the other
// had. `DreggProofVerify` consumes a REAL proof end to end and is hash-agnostic
// — but `verifyPlan` threw on `nBatches !== 2` and dregg's root has FOUR PCS
// rounds. `RootFriSlice`/`RootFriUniform` run at the root's real four-round
// geometry — but hard-code `compressBB`/`condSwap`, and `RootFriWalk` prices at
// `BABYBEAR_HASH`. So the 54-slice (now 80-slice) projection prices a
// Pasta-hashed root while the proof actually consumed was a two-round fixture,
// and the real-geometry chain ran at BabyBear prices. Neither half was both.
//
// This module is the bridge: it reads `root_fri_instance.rs`'s emitted object —
// dregg's committed whole-history root proof, four rounds, five matrix heights,
// a 2,630-term DEEP census — into a `DreggProofShape` the generalised assembly
// takes, at EITHER hash.
//
// ⚑ WHAT IS REAL AND WHAT IS RE-HASHED, SAID BEFORE ANY NUMBER IS QUOTED,
// because the honest answer is three-valued and the dishonest one is a headline.
//
//   REAL, at both hashes: the four PCS rounds and their 35 matrices; the five
//   log heights [22, 21, 16, 9, 6] and therefore the mixed-height injection
//   schedule; every opened row (1,427 base lanes a query); every opened
//   evaluation (2,630 extension values); every opening point; the 19 query
//   indices; ζ, α, the FRI α, the 16 βs and the final polynomial; the roll-in
//   schedule. All of it is read off `.fullchain/real-root-fri.json` and none of
//   it is synthesised.
//
//   RE-HASHED, at Pasta ONLY: the MMCS digests — the four round commitments,
//   the 16 commit-phase commitments, and every path sibling. dregg's root
//   commits with Poseidon2-over-BabyBear. A Pasta-hashed root is a RE-MINT
//   (`DreggMinaConfig`), not a re-read, and minting one is a Rust prove run over
//   a 2^22 batch. So `rehash` recomputes the commitments THIS proof's own
//   openings imply under the Pasta suite, deriving each sibling from the
//   BabyBear sibling it stands in for. Nothing is invented — every Pasta digest
//   is a function of the committed proof's own bytes — but it is a re-hash and
//   is labelled one everywhere it is reported.
//
//   ⚠ AND THE COST DOES NOT CARE, WHICH IS THE POINT. Rows are a function of the
//   GEOMETRY — how many lanes are sponged, how many levels are walked, how many
//   DEEP terms are folded — and every one of those is real here. What a re-mint
//   would move is which 19 indices are drawn, and 19 different indices cost the
//   same. What it would ALSO move is the FRI knobs, if the re-mint kept
//   `DreggMinaConfig`'s (`log_blowup = 3`, 38 queries) rather than the root's —
//   that is a different geometry and a different number, and this file does not
//   quote it.
// ---------------------------------------------------------------------------

const md = (x: bigint) => ((x % P) + P) % P;
const B = (v: number | string | bigint) => BigInt(v);

// ===========================================================================
// 1. The shape — four rounds, five heights, declared point scales.
// ===========================================================================

/**
 * The constant `c` with `point = ζ · c`, as a BASE-field element.
 *
 * ⚑ THIS IS A CHECK, NOT A LOOKUP, and it is the cheapest available evidence
 * that the second opening point is DERIVED rather than witnessed. `verify`
 * opens the next-row point at `ζ · g_k` where `g_k` generates the instance's own
 * trace domain, so `point/ζ` must come out a base element AND must be the
 * two-adic generator the instance's `degree_bits` names. If it were witnessed
 * the quotient would be an arbitrary extension element and this would throw.
 */
export function pointScaleOf(zeta: bigint[], point: bigint[]): bigint {
  const c = extMulBigInt(point, extInvBigInt(zeta));
  if (c[1] !== 0n || c[2] !== 0n || c[3] !== 0n)
    throw new Error(
      `an opening point is ζ times ${c.join(',')}, which is not a base element — it is not ` +
        'ζ·g for any trace domain, so it cannot be derived from ζ and a protocol constant',
    );
  return c[0];
}

/** The four-round shape, read off the committed proof. */
export function rootShapeOf(
  real: RealRootFri,
  suite: HashSuite<any> = babyBearSuite,
): DreggProofShape {
  const k = real.knobs as any;
  const lgmh = k.logGlobalMaxHeight;
  const zeta = real.zeta.map(B);
  const q0 = (real as any).queries[0];

  const batches = real.inputRounds.map((r, ri) => ({
    matrices: r.matrices.map((m): MatrixShape => {
      const scales = m.points.map((p) => pointScaleOf(zeta, p.map(B)));
      if (scales[0] !== 1n)
        throw new Error(`round ${ri} matrix ${m.matrix} opens its FIRST point at ζ·${scales[0]}`);
      //  ⚑ THE `degree_bits` CROSS-CHECK. The next-row scale must be the
      //  generator of the instance's OWN trace domain — not the matrix's LDE
      //  height, and not the batch's tallest. Instance 6 sits at `degree_bits =
      //  0`, so its scale is `g_0 = 1` and it opens at ζ TWICE.
      for (let p = 1; p < scales.length; p++) {
        const want = twoAdicGenerator(real.degreeBits[m.instance]);
        if (scales[p] !== want)
          throw new Error(
            `round ${ri} matrix ${m.matrix} (instance ${m.instance}, degree_bits ` +
              `${real.degreeBits[m.instance]}) opens point ${p} at ζ·${scales[p]}, and its own ` +
              `trace domain's generator is ${want}`,
          );
      }
      return {
        logHeight: m.logHeight,
        numCols: m.width,
        numPoints: m.points.length,
        pointScales: scales,
      };
    }),
    pathDepth: q0.inputBatches[ri].path.length,
  }));

  const knobs: FriKnobs = {
    logBlowup: k.logBlowup,
    logFinalPolyLen: k.logFinalPolyLen,
    commitPowBits: k.commitPowBits,
    queryPowBits: k.queryPowBits,
    maxLogArity: k.maxLogArity,
    numQueries: k.numQueries,
    logGlobalMaxHeight: lgmh,
    extraQueryIndexBits: 0,
    layers: k.layers,
    indexBits: lgmh,
    finalPolyLen: k.finalPolyLen ?? 1 << k.logFinalPolyLen,
  };

  return {
    knobs,
    logGlobalMaxHeight: lgmh,
    commitPathDepths: q0.commitPhase.map((c: any) => c.path.length),
    batches,
    // ⚑ THE ROOT IS A BATCH STARK AND HAS NO SINGLE AIR. Every field below that
    // could be read is unread: `constraints` is absent, so `assertAirClosing`
    // returns immediately and the AIR closing equality is the OTHER chain's
    // (`RootAirChain` / `RootAirProcessChain`, seven slices over 1,093
    // constraints). Saying that here rather than filling in a plausible width is
    // the difference between a shape and a fiction.
    air: {
      degreeBits: 0,
      baseDegreeBits: 0,
      preprocessedWidth: 0,
      width: 0,
      numPublicValues: 0,
      numQuotientChunks: 0,
      hasTraceNext: false,
      traceLogSize: 0,
      subgroupGenInv: 1n,
      chunkLogSize: 0,
      chunkShiftInvs: [],
      lagrangeConstInvs: [],
    },
    //  Carried, not derived — see `ROOT_CHALLENGE_STATUS` below.
    deriveChallenges: false,
    suite,
  };
}

/**
 * ⚑ THE ROOT PATH'S CHALLENGE STATUS, AS A STRING THE LEGS PRINT rather than a
 * footnote a reader has to find.
 *
 * The fixture path DERIVES every challenge from the transcript and the
 * `pasta-verify` / `dregg-verify` legs measure the row-count delta against a
 * twin that witnesses them instead. The ROOT path cannot yet: its transcript is
 * a batch-STARK preamble over seven instances entered at an emitted
 * `challengerStateBeforeFriAlpha`, which `root-fri-preamble` models and this
 * assembly does not implement. So the root's α, ζ, FRI α, βs and query indices
 * are CARRIED — which is `MINA-VERIFIES-DREGG-FRI-SIZE` §3.14's residual 1, the
 * one the braid and the uniform chain already carry, and NOT a new hole opened
 * by this merge.
 */
export const ROOT_CHALLENGE_STATUS =
  'CARRIED (§3.14 residual 1 — the batch-STARK preamble is not in this assembly; the ' +
  'input-phase openings, the DEEP quotient, the roll-in schedule and the fold chain are all DERIVED)';

// ===========================================================================
// 2. The proof's values, as bigints — one reader for both hashes.
// ===========================================================================

export type RootValues = {
  /** `[round][matrix][col]` — the opened rows, base lanes. */
  rows: bigint[][][][];
  /** `[round][matrix][point][col]` — the claimed evaluations, extension. */
  opened: bigint[][][][];
  /** `[query][round][level]` — the input-phase path siblings, as this suite's
   *  digest (8 BabyBear lanes, or 1 Pasta element). */
  inputPaths: bigint[][][][];
  /** `[round]` — the input-phase commitments. */
  inputCommits: bigint[][];
  /** `[query][layer]` and `[query][layer][level]`. */
  siblings: bigint[][][];
  /** `[query][layer]` — the fold value ENTERING each commit-phase round, which
   *  together with the sibling is that round's MMCS leaf. Round 0 enters at the
   *  reduced opening at the global max height; round `r > 0` enters at what
   *  round `r-1` emitted, roll-ins included. */
  foldEntering: bigint[][][];
  commitPaths: bigint[][][][];
  commitPhaseCommits: bigint[][];
  finalPoly: bigint[][];
  queryIndices: number[];
  zeta: bigint[];
  airAlpha: bigint[];
  friAlpha: bigint[];
  betas: bigint[][];
  queryPowWitness: bigint;
  /** Which hash these digests are under, and whether they were re-hashed. */
  hash: { name: string; rehashed: boolean };
};

/** The committed proof's own values, at its own hash. Nothing is recomputed. */
export function rootValues(real: RealRootFri): RootValues {
  const qs = (real as any).queries as any[];
  const evalAt = new Map<string, bigint[][]>();
  for (const e of (real as any).openedEvals)
    evalAt.set(`${e.round}/${e.matrix}/${e.pointIndex}`, e.values.map((v: any[]) => v.map(B)));

  return {
    rows: qs.map((q) => q.inputBatches.map((b: any) => b.rows.map((r: any[]) => r.map(B)))),
    opened: [
      real.inputRounds.map((r, ri) =>
        r.matrices.map((m) =>
          m.points.map((_, p) => {
            const v = evalAt.get(`${ri}/${m.matrix}/${p}`);
            if (!v) throw new Error(`no opened evaluation for round ${ri} matrix ${m.matrix} point ${p}`);
            if (v.length !== m.width)
              throw new Error(
                `round ${ri} matrix ${m.matrix} point ${p} opens ${v.length} values for ${m.width} columns`,
              );
            return v.flat();
          }),
        ),
      ),
    ][0] as any,
    inputPaths: qs.map((q) => q.inputBatches.map((b: any) => b.path.map((d: any[]) => d.map(B)))),
    inputCommits: real.inputRounds.map((r) => r.commit.map(B)),
    siblings: qs.map((q) => q.commitPhase.map((c: any) => c.sibling.map(B))),
    foldEntering: qs.map((q) => [
      q.reducedOpenings[0].ro.map(B),
      ...q.foldedAfterRound.slice(0, -1).map((f: any[]) => f.map(B)),
    ]),
    commitPaths: qs.map((q) => q.commitPhase.map((c: any) => c.path.map((d: any[]) => d.map(B)))),
    commitPhaseCommits: real.commits.map((c) => c.map(B)),
    finalPoly: real.finalPoly.map((c) => c.map(B)),
    queryIndices: qs.map((q) => q.index),
    zeta: real.zeta.map(B),
    airAlpha: real.airAlpha.map(B),
    friAlpha: real.friAlpha.map(B),
    betas: real.betas.map((b) => b.map(B)),
    queryPowWitness: B(real.queryPowWitness),
    hash: { name: 'poseidon2-babybear-w16', rehashed: false },
  };
}

// ===========================================================================
// 3. `MerkleTreeMmcs::verify_batch` OVER MIXED HEIGHTS, OUT OF CIRCUIT.
//
// ⚑ THIS IS THE FALSIFIER'S HOME AND IT RUNS IN MILLISECONDS. Every real defect
// in this arc came from an out-of-circuit differential — four silent wrongs
// across 11,303 segments, all 19 block-joins broken across 820 boundaries. A
// four-round mixed-height opening has four NEW ways to be silently wrong (the
// injection level, the injection ORDER, which matrices seed the leaf, and which
// index bits the level consumes) and every one of them compiles, proves, and
// gives a beautiful row count. So the twin below is checked LEVEL BY LEVEL
// against the committed proof's own round commitments before anything is built.
// ===========================================================================

export type MixedBatchSpec = {
  /** Committed order. */
  matrices: { logHeight: number; numCols: number }[];
  pathDepth: number;
};

/** One level of the walk, kept so a differential can say WHERE it diverged. */
export type MmcsTrace = {
  level: number;
  /** The padded height this level's compress lands at. */
  height: number;
  injected: number | null;
  digest: bigint[];
};

/**
 * The out-of-circuit twin of `runQueryInputAndDeep`'s input phase, at any suite.
 *
 * ⚑ IT IS A TWIN, NOT A SECOND VERIFIER — the level loop, the `top - 1 - level`
 * injection schedule, the `logGlobalMaxHeight - top` bit shift and the
 * committed-order grouping are the SAME four decisions the circuit makes, which
 * is the only reason a disagreement here is evidence about the circuit.
 */
export function verifyMixedBatchBigInt(
  suite: MerkleSuite<any>,
  spec: MixedBatchSpec,
  rowsByMatrix: bigint[][],
  path: bigint[][],
  index: bigint,
  logGlobalMaxHeight: number,
): { root: bigint[]; trace: MmcsTrace[] } {
  const hs = [...new Set(spec.matrices.map((m) => m.logHeight))].sort((a, b) => b - a);
  const top = hs[0];
  const bitsReduced = logGlobalMaxHeight - top;
  const rowsAt = (h: number) =>
    spec.matrices.flatMap((m, i) => (m.logHeight === h ? rowsByMatrix[i] : []));

  let cur = suite.spongeBigInt(rowsAt(top));
  const trace: MmcsTrace[] = [];
  for (let lv = 0; lv < spec.pathDepth; lv++) {
    const isRight = ((index >> BigInt(bitsReduced + lv)) & 1n) === 1n;
    cur = isRight ? suite.compressBigInt(path[lv], cur) : suite.compressBigInt(cur, path[lv]);
    const nextH = top - 1 - lv;
    const injected = hs.includes(nextH) ? nextH : null;
    //  ⚑ ORDER IS LOAD-BEARING: `compress([root, digest_of_this_height])`, root
    //  FIRST. The swapped form is a perfectly good Merkle tree and a different
    //  one; `root-consume-differential` puts both to the committed proof.
    if (injected !== null) cur = suite.compressBigInt(cur, suite.spongeBigInt(rowsAt(injected)));
    trace.push({ level: lv, height: nextH, injected, digest: cur });
  }
  return { root: cur, trace };
}

/** The DEEP-quotient input for one query, from the shape and this proof's own
 *  values — the same `(matrix, point, column)` traversal the circuit makes. */
export function deepInputBigInt(
  sh: DreggProofShape,
  v: RootValues,
  q: number,
): DeepMatBigInt[][] {
  const zeta = v.zeta;
  return sh.batches.map((bs, ri) =>
    bs.matrices.map((m, mi) => ({
      logHeight: m.logHeight,
      openedRow: v.rows[q][ri][mi],
      points: (m.pointScales ?? [1n]).map((c, p) => ({
        z: zeta.map((x) => md(x * c)),
        psAtZ: Array.from({ length: m.numCols }, (_, col) =>
          v.opened[ri][mi][p].slice(col * EXT_D, (col + 1) * EXT_D),
        ),
      })),
    })),
  );
}

/** Reduced openings for one query, out of circuit. */
export function reducedOpeningsOf(sh: DreggProofShape, v: RootValues, q: number) {
  return reducedOpeningsBigInt({
    index: BigInt(v.queryIndices[q]),
    logGlobalMaxHeight: sh.logGlobalMaxHeight,
    alpha: v.friAlpha,
    batches: deepInputBigInt(sh, v, q),
  });
}

// ===========================================================================
// 4. THE RE-HASH — the same object, at the other hash.
// ===========================================================================

/**
 * Re-commit this proof's openings under `suite`, and return a `RootValues` whose
 * every digest is that suite's.
 *
 * ⚑ WHAT IS DERIVED FROM WHAT, so nobody has to guess. Each Pasta path sibling
 * is `suite.spongeBigInt(<the BabyBear sibling's 8 lanes>)` — a function of the
 * committed proof's own bytes, chosen so no value is invented and so two
 * distinct BabyBear siblings stay distinct. Each round commitment and each
 * commit-phase commitment is then the root the re-hashed opening COMPUTES,
 * which is what makes the re-hashed object self-consistent: the assembly's
 * `assertEq(cur, commit)` has something true to check.
 *
 * ⚠ WHAT THIS IS NOT. It is not a proof minted under `DreggMinaConfig`. A real
 * Pasta-hashed root would draw different query indices (and, if it kept that
 * config's own FRI knobs, a different geometry entirely). What it shares with
 * this object is every quantity a row count is a function of.
 *
 * ⚠ AND IT IS NOT A SOUNDNESS CLAIM. Re-deriving a commitment from an opening
 * cannot fail, so the re-hashed object's input-phase equalities are true by
 * construction and prove nothing about the prover. What they measure is COST,
 * and what checks the CODE is the BabyBear column, where the commitments were
 * emitted by p3 and the equality can go red.
 */
/**
 * ⚑ A SPARSE TREE, NOT NINETEEN INDEPENDENT PATHS — and the difference is the
 * whole soundness-shaped content of the re-hash.
 *
 * The naive re-hash gives each query its own recomputed root, which is 19
 * commitments wearing one name. What a real MMCS has is ONE root that 19 paths
 * agree on, and two query paths that share a prefix share every node above the
 * point they meet. This builds exactly that: the 19 known leaves are folded
 * level by level, siblings that another query supplies are the COMPUTED node,
 * and the rest — the subtrees this proof never opens — are fixed to a value
 * derived from the BabyBear sibling standing in the same slot, MEMOISED by
 * (level, index) so two queries needing the same unknown sibling get the same
 * one.
 *
 * The result is a single root per round that all 19 openings verify against,
 * with the sharing structure a real tree has. `assertMerged` then checks the
 * thing that would silently not hold otherwise: every pair of queries that meets
 * at a level agrees on the node they meet at.
 */
function sparseRoot(
  suite: MerkleSuite<any>,
  opts: {
    depth: number;
    /** Per query: the index at the leaf level. */
    indices: bigint[];
    /** Per query: the leaf digest. */
    leaves: bigint[][];
    /** Per query, per level: the stand-in for a sibling nothing else supplies. */
    fallback: (q: number, level: number) => bigint[];
    /** Per level: the digest compressed in after the level's compress, per
     *  query, or `null` when this level injects nothing. */
    inject?: (level: number, q: number) => bigint[] | null;
  },
): { root: bigint[]; paths: bigint[][][]; merges: number } {
  const { depth, indices, leaves } = opts;
  const nQ = indices.length;
  let cur = indices.map((i) => i);
  let node = leaves.map((d) => d);
  const paths: bigint[][][] = Array.from({ length: nQ }, () => []);
  let merges = 0;

  for (let lv = 0; lv < depth; lv++) {
    const have = new Map<string, bigint[]>();
    for (let q = 0; q < nQ; q++) have.set(String(cur[q]), node[q]);
    const unknown = new Map<string, bigint[]>();
    const nextNode: bigint[][] = [];
    const nextIdx: bigint[] = [];
    for (let q = 0; q < nQ; q++) {
      const sibIdx = cur[q] ^ 1n;
      let sib = have.get(String(sibIdx));
      if (sib === undefined) {
        const key = String(sibIdx);
        sib = unknown.get(key);
        if (sib === undefined) {
          sib = opts.fallback(q, lv);
          unknown.set(key, sib);
        }
      } else merges++;
      paths[q].push(sib);
      const isRight = (cur[q] & 1n) === 1n;
      let up = isRight ? suite.compressBigInt(sib, node[q]) : suite.compressBigInt(node[q], sib);
      const inj = opts.inject ? opts.inject(lv, q) : null;
      if (inj !== null) up = suite.compressBigInt(up, inj);
      nextNode.push(up);
      nextIdx.push(cur[q] >> 1n);
    }
    //  Two queries that have met must stay met.
    const seen = new Map<string, bigint[]>();
    for (let q = 0; q < nQ; q++) {
      const key = String(nextIdx[q]);
      const prev = seen.get(key);
      if (prev && prev.some((x, i) => x !== nextNode[q][i]))
        throw new Error(
          `the sparse re-hash split at level ${lv}: two queries reach node ${key} with different ` +
            'digests, so the object is not one tree',
        );
      seen.set(key, nextNode[q]);
    }
    cur = nextIdx;
    node = nextNode;
  }
  for (let q = 1; q < nQ; q++)
    if (node[q].some((x, i) => x !== node[0][i]))
      throw new Error('the sparse re-hash produced more than one root');
  return { root: node[0], paths, merges };
}

export function rehash(
  sh: DreggProofShape,
  v: RootValues,
  suite: MerkleSuite<any>,
): RootValues & { merges: number } {
  const lgmh = sh.logGlobalMaxHeight;
  const D = suite.digestElems;
  const reDigest = (d: bigint[]): bigint[] => (d.length === D ? d : suite.spongeBigInt(d));
  const nQ = v.queryIndices.length;
  let merges = 0;

  //  -- the four input rounds ------------------------------------------------
  const inputPaths: bigint[][][][] = Array.from({ length: nQ }, () => []);
  const inputCommits: bigint[][] = [];
  for (let ri = 0; ri < sh.batches.length; ri++) {
    const bs = sh.batches[ri];
    const hs = [...new Set(bs.matrices.map((m) => m.logHeight))].sort((a, b) => b - a);
    const top = hs[0];
    const rowsAt = (q: number, h: number) =>
      bs.matrices.flatMap((m, i) => (m.logHeight === h ? v.rows[q][ri][i] : []));
    const r = sparseRoot(suite, {
      depth: bs.pathDepth,
      indices: v.queryIndices.map((i) => BigInt(i) >> BigInt(lgmh - top)),
      leaves: Array.from({ length: nQ }, (_, q) => suite.spongeBigInt(rowsAt(q, top))),
      fallback: (q, lv) => reDigest(v.inputPaths[q][ri][lv]),
      inject: (lv, q) => {
        const nextH = top - 1 - lv;
        return hs.includes(nextH) ? suite.spongeBigInt(rowsAt(q, nextH)) : null;
      },
    });
    merges += r.merges;
    inputCommits.push(r.root);
    for (let q = 0; q < nQ; q++) inputPaths[q].push(r.paths[q]);
  }

  //  -- the sixteen commit-phase layers -------------------------------------
  //  The leaf is `sponge([even, odd])` over the (folded, sibling) pair the fold
  //  chain builds, which is why this re-hash needs the emitted fold values and
  //  not just the paths.
  const commitPaths: bigint[][][][] = Array.from({ length: nQ }, () => []);
  const commitPhaseCommits: bigint[][] = [];
  for (let r = 0; r < sh.knobs.layers; r++) {
    const res = sparseRoot(suite, {
      depth: sh.commitPathDepths[r],
      indices: v.queryIndices.map((i) => BigInt(i) >> BigInt(r + 1)),
      leaves: Array.from({ length: nQ }, (_, q) => {
        const [even, odd] = commitLeafPair(v, q, r);
        return suite.spongeBigInt([...even, ...odd]);
      }),
      fallback: (q, lv) => reDigest(v.commitPaths[q][r][lv]),
    });
    merges += res.merges;
    commitPhaseCommits.push(res.root);
    for (let q = 0; q < nQ; q++) commitPaths[q].push(res.paths[q]);
  }

  return {
    ...v,
    inputPaths,
    inputCommits,
    commitPaths,
    commitPhaseCommits,
    hash: { name: suite.name, rehashed: true },
    merges,
  };
}

/** `(even, odd)` for a commit-phase round's MMCS leaf: the value entering the
 *  fold and the witnessed sibling, in DOMAIN order — slot 0 is the even point.
 *  The entering value is the reduced opening at the global max height for round
 *  0 and the previous round's output after it. */
export function commitLeafPair(v: RootValues, q: number, r: number): [bigint[], bigint[]] {
  const entering = r === 0 ? v.foldEntering[q][0] : v.foldEntering[q][r];
  const sib = v.siblings[q][r];
  const isRight = ((BigInt(v.queryIndices[q]) >> BigInt(r)) & 1n) === 1n;
  return isRight ? [sib, entering] : [entering, sib];
}

// ===========================================================================
// 5. The claim and the witness the generalised assembly takes.
// ===========================================================================

const ext = (v: bigint[]) => BbExt.from(v);

export function rootClaim(sh: DreggProofShape, v: RootValues, Claim: any) {
  const suite = sh.suite!;
  return new Claim({
    inputCommits: v.inputCommits.map((d) => suite.from(d)),
    commitPhaseCommits: v.commitPhaseCommits.map((d) => suite.from(d)),
    finalPoly: v.finalPoly.map(ext),
    publicValues: [Field(0)],
  });
}

export function rootClaimValue(sh: DreggProofShape, v: RootValues): ClaimValue {
  const suite = sh.suite!;
  return {
    inputCommits: v.inputCommits.map((d) => suite.from(d)) as Digestish[],
    commitPhaseCommits: v.commitPhaseCommits.map((d) => suite.from(d)) as Digestish[],
    finalPoly: v.finalPoly.map(ext),
    publicValues: [Field(0)],
  };
}

/** The private witness, in the order the generalised method declares. */
export function rootWitness(sh: DreggProofShape, v: RootValues, queries?: number[]): any[] {
  const suite = sh.suite!;
  const qs = queries ?? v.queryIndices.map((_, i) => i);
  const maxInputDepth = Math.max(...sh.batches.map((b) => b.pathDepth), 1);
  const maxCommitDepth = Math.max(...sh.commitPathDepths, 1);
  const pad = (arr: bigint[][], n: number) =>
    [...arr, ...Array.from({ length: Math.max(0, n - arr.length) }, () => null)].slice(0, n).map(
      (d) => (d === null ? suite.zero() : suite.from(d)),
    );

  //  ⚑ ROUND-MAJOR, MATRIX-MAJOR, POINT-MAJOR, COLUMN-MAJOR — p3's own observe
  //  order (`two_adic_pcs.rs:780-788`) and therefore the order `verifyPlan`'s
  //  wiring offsets assume. `openedTrace` is round 0's run and `openedQuotient`
  //  is every later round's; at two rounds those names mean what they always
  //  meant, at four the second carries the quotient, preprocessed AND
  //  permutation rounds.
  const flat: BbExt[] = [];
  for (let ri = 0; ri < sh.batches.length; ri++)
    for (let mi = 0; mi < sh.batches[ri].matrices.length; mi++) {
      const m = sh.batches[ri].matrices[mi];
      for (let p = 0; p < m.numPoints; p++)
        for (let c = 0; c < m.numCols; c++)
          flat.push(ext(v.opened[ri][mi][p].slice(c * EXT_D, (c + 1) * EXT_D)));
    }
  const nRound0 = sh.batches[0].matrices.reduce((a, m) => a + m.numCols * m.numPoints, 0);

  return [
    flat.slice(0, nRound0),
    flat.slice(nRound0),
    Field(v.queryPowWitness),
    qs.map((q) => v.rows[q].flat().flat().map((x) => Field(x))),
    qs.map((q) => v.inputPaths[q].map((perR) => pad(perR, maxInputDepth))),
    qs.map((q) => v.siblings[q].map(ext)),
    qs.map((q) => v.commitPaths[q].map((perR) => pad(perR, maxCommitDepth))),
    ext(v.airAlpha),
    ext(v.zeta),
    ext(v.friAlpha),
    v.betas.map(ext),
    qs.map((q) =>
      Array.from({ length: sh.knobs.indexBits }, (_, i) =>
        Bool(((BigInt(v.queryIndices[q]) >> BigInt(i)) & 1n) === 1n),
      ),
    ),
  ];
}

/** Both suites, by the name the reports use. */
export const SUITES: { label: string; suite: HashSuite<any> }[] = [
  { label: 'BabyBear (deployed, emulated)', suite: babyBearSuite },
  { label: 'Pasta (Mina-native)', suite: pastaSuite },
];

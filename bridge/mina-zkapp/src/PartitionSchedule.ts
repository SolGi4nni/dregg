import { DreggProofShape, verifyPlan } from './DreggProofVerify.js';
import { carriedLaneCount } from './DreggProofPartition.js';

// ---------------------------------------------------------------------------
// THE SCHEDULER — where to cut, and what the cut costs.
//
// ⚑ WHAT THIS EXISTS TO KILL. §3.20 ran the partition and priced a boundary,
// and the price turned out to depend entirely on WHERE the boundary is: 34,566
// rows at a query ENTRY (69.8% of a `max_proofs_verified = 2` step), 762 rows
// INSIDE a query. So the deployed step count was left as a BAND, 564-1,838, with
// the note that "which end you land on is the scheduler `KimchiPartition` names
// as its remainder". A 3.3x spread is the difference between a feasible project
// and an infeasible one, and it is entirely a placement problem. This module is
// the placement.
//
// ⚑ THE OBJECTIVE IS REAL, NOT A HEURISTIC. The carry was measured to be LINEAR
// in the carried lane count at 3.757 rows/lane over a 100x range (§3.20, two
// independent slopes agreeing within 5%), and the pack-and-hash half of it
// separately at 1.258. So "minimise total steps subject to no step exceeding the
// domain" is an optimisation over a measured cost function, and it is solved
// here by a dynamic program rather than approached by a rule of thumb.
//
// ⚑ AND THE MECHANISM THAT MAKES A GOOD SCHEDULE POSSIBLE IS NOT ARITHMETIC.
// A boundary costs 34,566 rows at a query entry because `rootCommitDigest` is a
// digest of ONE flat lane list, so any step that has to re-derive it must
// re-witness ALL 9,103 lanes — including 8,920 lanes of claimed opened
// evaluations that a fold chain never looks at. Chunk the lane list and commit
// to the VECTOR OF CHUNK DIGESTS instead, and a step re-witnesses only the
// chunks it READS plus `m` field elements:
//
//     rootCommitDigest = Poseidon(d_0, ..., d_{m-1}),  d_i = digest of chunk i
//
// The digest is the same kind of object, the boundary is still ONE field, and
// `KimchiPartition.StepPublicInput`'s three slots are unchanged. What changes is
// that a step's carry becomes a function of what it READS instead of what the
// proof CONTAINS. `DreggProofSchedule.ts` builds it and the leg PROVES a chain
// under it; this module schedules against it.
//
// ⚑ THE COST MODEL USES BOTH MEASURED SLOPES, AND THE DISTINCTION MATTERS.
// A lane a step's own work already witnesses and range-checks costs only the
// pack-and-hash rate to fold into a chunk digest (1.258 rows/lane, §3.20's
// `probeNoRc`); a lane a step witnesses ONLY in order to re-derive a digest pays
// the full 3.757, because a re-witnessed lane is unconstrained until it is
// range-checked. Charging 3.757 for both would inflate the deployed count by
// ~6%, and charging 1.258 for both would understate the carry that is the whole
// subject of §3.20.
// ---------------------------------------------------------------------------

/** §3.20, measured: the carry circuit is linear in the carried lane count at
 *  this rate across 203..9,198 lanes. Re-witness + range-check + pack + hash. */
export const REBIND_ROWS_PER_LANE = 34_566 / 9_198;
/** §3.20, measured: the same circuit with the range checks removed — what a lane
 *  the step ALREADY holds costs to fold into a digest. */
export const HASH_ROWS_PER_LANE = 11_571 / 9_198;

/** §3.19/`KimchiPartition.EMITTED_ROWS_PER_PERM`: what one Poseidon2-w16
 *  permutation costs in emitted Kimchi rows. The finest granularity a Merkle
 *  path or a sponge absorb can be cut at. */
export const PERM_ROWS = 2_668;

/** The Kimchi step domain (`kimchi_pasta_basic.ml:16-17`, `Step = Nat.N16`). */
export const KIMCHI_ROWS = 65_536;
/** `zk_rows` (§4.1). */
export const ZK_ROWS = 3;
/** `StepPublicInput` is ONE field element, at one full row (§3.2). */
export const N_PUB = 1;

/** §4.1's recursive-verifier overhead, by `max_proofs_verified`. The pessimistic
 *  end of each cited range is taken, so a step count is never optimistic by
 *  construction. */
export const PICKLES_OVERHEAD = { straightChain: 8_000, aggregationTree: 16_000 } as const;

export const usableRows = (overhead: number) => KIMCHI_ROWS - ZK_ROWS - N_PUB - overhead;

// ===========================================================================
// 1. The program, as ATOMS.
// ===========================================================================

export type AtomKind =
  | 'absorb-col' //     the transcript absorbing one opened column's evaluations
  | 'transcript-tail' //  sampling, the arity schedule and the query grind
  | 'input-path' //     one level of one input-phase Merkle path
  | 'deep-col' //       one column's MMCS leaf lane and its DEEP quotient term
  | 'fold-arith' //     one commit-phase round's fold arithmetic and roll-in
  | 'fold-path' //      one level of one commit-phase Merkle path
  | 'final-poly' //     the closing evaluation of `final_poly`
  | 'air-node' //       one node of the ROOT's constraint DAG (leg 13)
  | 'air-fold'; //      one `acc = acc*alpha + C_i` step, all 1,093 of them

/** An indivisible unit of verifier work. A cut may be placed between any two
 *  atoms and nowhere else — which is what makes a schedule a placement over a
 *  real structure rather than a division of a total. */
export type Atom = {
  id: string;
  kind: AtomKind;
  /** Which query this belongs to; `null` for the transcript block. */
  query: number | null;
  rows: number;
  /** The committed lane chunk this atom READS — the step containing it must hold
   *  those lanes and fold them into the chunk's digest. */
  reads: string;
  /** How many of that chunk's lanes this atom's OWN measured cost already
   *  witnesses and range-checks. Those lanes cost only the pack-and-hash rate to
   *  fold into the digest; the rest of the chunk costs the full rebind rate. */
  ownLanes: number;
  /** Lanes of step-local state that must cross a cut placed AFTER this atom: the
   *  transcript sponge, the DEEP accumulator, or the running fold value. */
  liveAfter: number;
};

/** A committed lane chunk. `rootCommitDigest` is the Poseidon hash of the
 *  chunks' digests, in this order. */
export type Chunk = { id: string; lanes: number };

export type Program = {
  atoms: Atom[];
  chunks: Chunk[];
  /** Lanes hashed into `challengeDigest` — carried by every step past sampling. */
  challengeLanes: number;
  totalRows: number;
};

/** The deployed FRI geometry (§1.2) at the deployed opened-column census (§1.3:
 *  940 main + 175 preprocessed, each opened at two points), as a shape the same
 *  `verifyPlan`/`carriedLaneCount` the circuit uses can be asked about.
 *
 * ⚑ SHARED WITH §3.20's ROW PHASE ON PURPOSE. The lane counts this schedule is
 * priced against and the lane counts §3.20's boundary probe was MEASURED at have
 * to be the same object, or the price is for a different boundary. */
export function deployedShapeOf(base: DreggProofShape, width: number): DreggProofShape {
  return {
    ...base,
    constraints: undefined,
    deriveChallenges: false,
    knobs: {
      ...base.knobs,
      layers: 16,
      logGlobalMaxHeight: 22,
      indexBits: 22,
      logBlowup: 6,
      numQueries: 19,
    },
    logGlobalMaxHeight: 22,
    commitPathDepths: Array.from({ length: 16 }, (_, i) => 21 - i),
    batches: base.batches.map((b, i) => ({
      matrices: b.matrices.map((m) => ({ ...m, logHeight: 22, numCols: i === 0 ? width : m.numCols })),
      pathDepth: 22,
    })),
    air: { ...base.air, width },
  };
}

/** The deployed root's opened-column census (§1.3). */
export const DEPLOYED_COLS = 940 + 175;

/**
 * §3.19's MEASURED marginals, which are the only thing this model is allowed to
 * be built out of. Every row figure below is one of these or a sum of them.
 */
export const MEASURED = {
  /** One query at the deployed FRI geometry, challenges witnessed, no AIR check
   *  — i.e. the query WALK alone, carrying the fixture's 3 columns. */
  deployedQueryWalk: 748_438,
  /** Transcript + AIR arithmetic at deployed geometry, at 3 columns. */
  deployedTranscriptAir: 79_449,
  /** Per additional opened trace column, absorbed ONCE by the transcript. */
  absorbPerColumn: 2_705,
  /** Per additional opened trace column, PER QUERY: its DEEP term and its MMCS
   *  leaf lane. */
  deepPerColumnPerQuery: 481,
  /** The whole deployed root, as §3.19 projects it — what the model must
   *  reproduce, or the model is about a different circuit. */
  deployedTotal: 2.75e7,
} as const;

/**
 * The deployed verifier as an ordered atom list.
 *
 * ⚑ EVERY ROW FIGURE HERE IS A MEASURED MARGINAL OR A SUM OF THEM, and the
 * decomposition of the two measured AGGREGATES is structural: a query walk at
 * `|D⁰| = 2²²` with 16 arity-2 layers contains `2 x 22` input-path levels and
 * `sum_r (21-r) = 216` commit-path levels, each one Poseidon2 compression at
 * `PERM_ROWS`; what those 260 permutations do not account for is the fold
 * arithmetic and the closing evaluation, and that residual is spread over the
 * 17 arithmetic atoms rather than invented per-atom. The model is checked
 * against `MEASURED.deployedTotal` by the leg, not asserted here.
 */
export function deployedProgram(
  base: DreggProofShape,
  opts: { openChunkLanes: number; cols?: number },
): Program {
  const cols = opts.cols ?? DEPLOYED_COLS;
  const sh = deployedShapeOf(base, cols);
  const plan = verifyPlan(sh);
  const lanes = carriedLaneCount(sh);
  const { layers, numQueries } = sh.knobs;
  const inputDepth = plan.maxInputDepth;
  const atoms: Atom[] = [];

  // ── the committed lane chunks ────────────────────────────────────────────
  // `misc` and `fold` are named groups because a step reads them as a unit; the
  // opened evaluations — 8,920 of the 9,103 root lanes — are the only group big
  // enough for the chunk size to matter, and it is the one the fold chain never
  // reads.
  const openLanes = plan.nOpenedTrace * 4 + plan.nQuotientVals * 4;
  const foldLanes = layers * 8 + sh.knobs.finalPolyLen * 4;
  const miscLanes = plan.nBatches * 8 + Math.max(sh.air.numPublicValues, 1) + 1;
  if (openLanes + foldLanes + miscLanes !== lanes.root)
    throw new Error(
      `the chunking covers ${openLanes + foldLanes + miscLanes} root lanes, not the ` +
        `${lanes.root} that cross a boundary — a lane in no chunk is a lane nothing binds`,
    );
  const nOpenChunks = Math.ceil(openLanes / opts.openChunkLanes);
  const chunks: Chunk[] = [
    { id: 'misc', lanes: miscLanes },
    { id: 'fold', lanes: foldLanes },
    ...Array.from({ length: nOpenChunks }, (_, i) => ({
      id: `open${i}`,
      lanes: Math.min(opts.openChunkLanes, openLanes - i * opts.openChunkLanes),
    })),
  ];
  /** Which chunk holds column `c`'s opened evaluations. A column contributes
   *  `numPoints * EXT_D` lanes, contiguously. */
  const lanesPerCol = (plan.nOpenedTrace * 4) / cols;
  const openChunkOf = (c: number) => `open${Math.floor((c * lanesPerCol) / opts.openChunkLanes)}`;

  // ── the transcript block ─────────────────────────────────────────────────
  // Sponge state (`WIDTH = 16`) is what crosses a cut inside an absorb run.
  const SPONGE_LANES = 16;
  for (let c = 0; c < cols; c++)
    atoms.push({
      id: `absorb:${c}`,
      kind: 'absorb-col',
      query: null,
      rows: MEASURED.absorbPerColumn,
      reads: openChunkOf(c),
      ownLanes: lanesPerCol,
      liveAfter: SPONGE_LANES,
    });
  // §3.19's 79,449 covers the fixture's 3 columns too; those are already atoms.
  const tailRows = MEASURED.deployedTranscriptAir - 3 * MEASURED.absorbPerColumn;
  const nTail = Math.ceil(tailRows / PERM_ROWS);
  for (let i = 0; i < nTail; i++)
    atoms.push({
      id: `transcript-tail:${i}`,
      kind: 'transcript-tail',
      query: null,
      rows: Math.round(tailRows / nTail),
      reads: 'misc',
      ownLanes: 0,
      liveAfter: SPONGE_LANES,
    });

  // ── the query walks ──────────────────────────────────────────────────────
  // What §3.19's 748,438 does NOT spend on Merkle compressions is the fold
  // arithmetic and the closing evaluation.
  const pathLevels = plan.nBatches * inputDepth + sh.commitPathDepths.reduce((a, b) => a + b, 0);
  const arithRows = MEASURED.deployedQueryWalk - pathLevels * PERM_ROWS;
  const nArith = layers + 1;
  if (arithRows <= 0)
    throw new Error(
      `${pathLevels} Merkle levels at ${PERM_ROWS} rows already exceed the measured ` +
        `${MEASURED.deployedQueryWalk}-row query walk — the decomposition is wrong, not tight`,
    );
  const perArith = Math.round(arithRows / nArith);
  /** After the DEEP quotient, only the reduced openings and the index cross. */
  const DEEP_OUT_LANES = 4 * (plan.nRollIns + 1) + 1;
  /** Mid-fold: the folded value, the coset point, the index and the round. */
  const FOLD_LANES = 4 + 1 + 1 + 1;
  /** Mid-DEEP: one accumulator and one alpha power per opened height, plus the
   *  query point. */
  const DEEP_LANES = 8 * (plan.nRollIns + 1) + 1;

  for (let q = 0; q < numQueries; q++) {
    for (let b = 0; b < plan.nBatches; b++)
      for (let h = 0; h < inputDepth; h++)
        atoms.push({
          id: `q${q}:input:${b}:${h}`,
          kind: 'input-path',
          query: q,
          rows: PERM_ROWS,
          reads: 'misc',
          ownLanes: 0,
          liveAfter: DEEP_LANES,
        });
    for (let c = 0; c < cols; c++)
      atoms.push({
        id: `q${q}:deep:${c}`,
        kind: 'deep-col',
        query: q,
        rows: MEASURED.deepPerColumnPerQuery,
        reads: openChunkOf(c),
        ownLanes: lanesPerCol,
        liveAfter: c === cols - 1 ? DEEP_OUT_LANES : DEEP_LANES,
      });
    for (let r = 0; r < layers; r++) {
      atoms.push({
        id: `q${q}:fold:${r}`,
        kind: 'fold-arith',
        query: q,
        rows: perArith,
        reads: 'fold',
        ownLanes: 0,
        liveAfter: FOLD_LANES,
      });
      for (let h = 0; h < sh.commitPathDepths[r]; h++)
        atoms.push({
          id: `q${q}:foldpath:${r}:${h}`,
          kind: 'fold-path',
          query: q,
          rows: PERM_ROWS,
          reads: 'fold',
          ownLanes: 0,
          liveAfter: FOLD_LANES,
        });
    }
    atoms.push({
      id: `q${q}:final`,
      kind: 'final-poly',
      query: q,
      rows: perArith,
      reads: 'fold',
      ownLanes: 0,
      // A query ends holding nothing: the next query starts from the index bits
      // in the carried challenge set.
      liveAfter: 0,
    });
  }

  return {
    atoms,
    chunks,
    challengeLanes: lanes.challenge,
    totalRows: atoms.reduce((a, x) => a + x.rows, 0),
  };
}

// ===========================================================================
// 2. What a step costs.
// ===========================================================================

export type CarryModel = {
  /** Lanes the step witnesses ONLY to re-derive a digest. */
  rebindPerLane: number;
  /** Lanes the step's own work already holds, folded into a digest. */
  hashPerLane: number;
};

export const MEASURED_CARRY: CarryModel = {
  rebindPerLane: REBIND_ROWS_PER_LANE,
  hashPerLane: HASH_ROWS_PER_LANE,
};

/**
 * The carry a step over `atoms[i..j)` pays, and every term is a lane count times
 * a measured slope.
 *
 *   * the chunks its atoms read, at the HASH rate for the lanes those atoms
 *     witness anyway and at the REBIND rate for the rest of each chunk it must
 *     complete in order to re-derive the digest;
 *   * `m` chunk digests, so it can rebuild `rootCommitDigest` from the chunks it
 *     did not read;
 *   * the challenge lanes and the live state entering it, at the REBIND rate;
 *   * the challenge lanes and the live state leaving it, at the HASH rate — it
 *     already holds them, and it hands them on as `challengeDigest`.
 */
export function stepCarry(
  prog: Program,
  i: number,
  j: number,
  model: CarryModel = MEASURED_CARRY,
): number {
  const acc = new CarryAcc(prog, i, model);
  for (let k = i; k < j; k++) acc.push(k);
  return acc.total(j);
}

/**
 * A step's carry, built up one atom at a time — because the scheduler asks for
 * it once per candidate step and recomputing it from scratch would make the DP
 * quadratic in the window as well as in the atom count.
 *
 * `own` is the running per-chunk tally of lanes the step's own atoms already
 * witness and range-check; everything else in a touched chunk still has to be
 * witnessed to complete its digest, and a chunk is never charged for more lanes
 * than it has.
 */
class CarryAcc {
  private readonly laneOf: Map<string, number>;
  private readonly own = new Map<string, number>();
  private rows = 0;
  constructor(
    private readonly prog: Program,
    i: number,
    private readonly model: CarryModel,
  ) {
    this.laneOf = laneIndex(prog);
    // Every step re-derives `rootCommitDigest` from the chunk digests, so it
    // witnesses all `m` of them; the ones it read it recomputes instead.
    this.rows += prog.chunks.length * model.rebindPerLane;
    const liveIn = i === 0 ? 0 : prog.atoms[i - 1].liveAfter;
    this.rows += (prog.challengeLanes + liveIn) * model.rebindPerLane;
  }
  push(k: number) {
    const a = this.prog.atoms[k];
    const lanes = this.laneOf.get(a.reads);
    if (lanes === undefined) throw new Error(`atom ${a.id} reads unknown chunk ${a.reads}`);
    const prev = this.own.get(a.reads);
    if (prev === undefined) {
      // First atom in this step to touch the chunk: the whole chunk must be
      // present, at the rebind rate, before any of it is discounted.
      this.rows += lanes * this.model.rebindPerLane;
      this.own.set(a.reads, 0);
    }
    const had = this.own.get(a.reads)!;
    const add = Math.min(a.ownLanes, lanes - had);
    if (add > 0) {
      this.own.set(a.reads, had + add);
      this.rows -= add * (this.model.rebindPerLane - this.model.hashPerLane);
    }
  }
  total(j: number): number {
    const liveOut = j >= this.prog.atoms.length ? 0 : this.prog.atoms[j - 1].liveAfter;
    return this.rows + (this.prog.challengeLanes + liveOut) * this.model.hashPerLane;
  }
}

const laneIndexCache = new WeakMap<Program, Map<string, number>>();
function laneIndex(prog: Program): Map<string, number> {
  let m = laneIndexCache.get(prog);
  if (!m) {
    m = new Map(prog.chunks.map((c) => [c.id, c.lanes]));
    laneIndexCache.set(prog, m);
  }
  return m;
}

// ===========================================================================
// 3. The schedule.
// ===========================================================================

export type Schedule = {
  /** `cuts[s]` is the index of the first atom of step `s`; the last entry is
   *  `atoms.length`, so step `s` covers `[cuts[s], cuts[s+1])`. */
  cuts: number[];
  steps: number;
  /** Rows spent on carry, over the whole chain. */
  carryRows: number;
  /** Rows of verifier work — `Program.totalRows`, unchanged by any schedule. */
  workRows: number;
  /** Rows a step wastes because the next atom did not fit. */
  slackRows: number;
  /** How many boundaries land at each of the two classes §3.20 measured. */
  census: { atQueryEntry: number; insideQuery: number; inTranscript: number };
  maxStepRows: number;
};

/**
 * **The scheduler.** Minimise the number of steps subject to no step exceeding
 * the usable domain, over the atom sequence and the measured carry.
 *
 * A dynamic program, not a greedy fill. `f[j]` = the fewest steps that cover
 * `atoms[0..j)`, with ties broken by the least carry — and the tie-break is not
 * decoration: at the deployed geometry many packings reach the same step count
 * and they differ by hundreds of thousands of carried rows, which is what turns
 * into the NEXT step when the geometry moves. The window is bounded because a
 * step cannot hold more rows than the domain, so this is O(n·w), not O(n²).
 */
export function schedule(
  prog: Program,
  usable: number,
  model: CarryModel = MEASURED_CARRY,
): Schedule {
  const n = prog.atoms.length;
  const INF = Number.POSITIVE_INFINITY;
  const steps = new Float64Array(n + 1).fill(INF);
  const carry = new Float64Array(n + 1).fill(INF);
  const from = new Int32Array(n + 1).fill(-1);
  steps[0] = 0;
  carry[0] = 0;

  // Prefix sums so a step's work rows are O(1).
  const pre = new Float64Array(n + 1);
  for (let k = 0; k < n; k++) pre[k + 1] = pre[k] + prog.atoms[k].rows;

  for (let i = 0; i < n; i++) {
    if (steps[i] === INF) continue;
    const acc = new CarryAcc(prog, i, model);
    for (let j = i + 1; j <= n; j++) {
      acc.push(j - 1);
      const work = pre[j] - pre[i];
      if (work >= usable) break; //          no carry is negative; nothing longer fits
      const c = acc.total(j);
      if (work + c > usable) break;
      const s = steps[i] + 1;
      const cc = carry[i] + c;
      if (s < steps[j] || (s === steps[j] && cc < carry[j])) {
        steps[j] = s;
        carry[j] = cc;
        from[j] = i;
      }
    }
  }
  if (steps[n] === INF)
    throw new Error(
      `no schedule exists at ${usable} usable rows — some single atom plus its carry is bigger ` +
        'than a step, and the atom decomposition is what has to get finer',
    );

  const cuts: number[] = [n];
  for (let j = n; j > 0; j = from[j]) cuts.push(from[j]);
  cuts.reverse();

  let slack = 0;
  let maxStep = 0;
  const census = { atQueryEntry: 0, insideQuery: 0, inTranscript: 0 };
  for (let s = 0; s + 1 < cuts.length; s++) {
    const i = cuts[s];
    const j = cuts[s + 1];
    const spent = pre[j] - pre[i] + stepCarry(prog, i, j, model);
    slack += usable - spent;
    maxStep = Math.max(maxStep, spent);
    if (j < prog.atoms.length) {
      const before = prog.atoms[j - 1];
      const after = prog.atoms[j];
      if (after.query !== null && before.query !== after.query) census.atQueryEntry++;
      else if (after.query === null) census.inTranscript++;
      else census.insideQuery++;
    }
  }
  return {
    cuts,
    steps: cuts.length - 1,
    carryRows: carry[n],
    workRows: prog.totalRows,
    slackRows: slack,
    census,
    maxStepRows: maxStep,
  };
}

/**
 * **The schedule §3.20's band assumes at its expensive end**: cut wherever the
 * ceiling falls, and pay the full flat-`rootCommitDigest` carry — every root
 * lane plus every challenge lane re-witnessed — at every boundary. This is not a
 * straw man: it is what a partitioner that does not look at WHERE it is cutting
 * costs, and it is the 1,838 the document quotes.
 */
export function scheduleFlatCarry(prog: Program, usable: number, rootLanes: number): Schedule {
  const perBoundary = (rootLanes + prog.challengeLanes) * REBIND_ROWS_PER_LANE;
  const n = prog.atoms.length;
  const cuts = [0];
  let acc = 0;
  let slack = 0;
  let maxStep = 0;
  let carryRows = 0;
  for (let k = 0; k < n; k++) {
    const c = cuts.length === 1 ? 0 : perBoundary;
    if (acc + c + prog.atoms[k].rows > usable) {
      slack += usable - (acc + c);
      maxStep = Math.max(maxStep, acc + c);
      carryRows += c;
      cuts.push(k);
      acc = prog.atoms[k].rows;
    } else acc += prog.atoms[k].rows;
  }
  cuts.push(n);
  carryRows += cuts.length > 2 ? perBoundary : 0;
  return {
    cuts,
    steps: cuts.length - 1,
    carryRows,
    workRows: prog.totalRows,
    slackRows: slack,
    census: { atQueryEntry: 0, insideQuery: 0, inTranscript: 0 },
    maxStepRows: maxStep,
  };
}

/** Sweep the one free parameter the chunking has — how many lanes go in a chunk
 *  — and return the best schedule. Small chunks mean a long digest vector every
 *  step must carry; large chunks mean a step completes lanes it never reads.
 *  The optimum is near `sqrt` of the chunked lane count and the sweep finds it
 *  rather than the comment asserting it. */
export function bestSchedule(
  base: DreggProofShape,
  usable: number,
  chunkSizes: number[],
  model: CarryModel = MEASURED_CARRY,
): { chunkLanes: number; prog: Program; sched: Schedule } {
  let best: { chunkLanes: number; prog: Program; sched: Schedule } | null = null;
  for (const chunkLanes of chunkSizes) {
    const prog = deployedProgram(base, { openChunkLanes: chunkLanes });
    const sched = schedule(prog, usable, model);
    if (
      !best ||
      sched.steps < best.sched.steps ||
      (sched.steps === best.sched.steps && sched.carryRows < best.sched.carryRows)
    )
      best = { chunkLanes, prog, sched };
  }
  return best!;
}

// ===========================================================================
// 5. THE EMITTED PROGRAM — the same atoms, priced by EMISSION rather than by
//    dividing an aggregate, and with the ROOT's own AIR in it.
// ===========================================================================
//
// ⚑ WHAT §3.21 LEFT OPEN, IN ITS OWN WORDS:
//
//   "The atom model's row figures are §3.19's measured marginals and its
//    aggregate matches §3.19's projection to 0.01%, but a 2.75 x 10^7-row
//    circuit has never been emitted. 591 is a schedule over a measured MODEL,
//    not over an emitted row list."
//   "2.75 x 10^7 is itself a FLOOR (the AIR term in it is the fixture's four
//    constraints, not the root's 1,093). A floor scheduled is still a floor."
//
// Both are closed here, and neither by argument:
//
//  * `deployedProgram` divides TWO aggregates across atoms — `perArith =
//    (deployedQueryWalk - pathLevels * PERM_ROWS) / (layers + 1)` and `tailRows
//    / nTail`. `scripts/emitted-atoms.ts` measures each atom kind as an
//    IN-CONTEXT MARGINAL on the deployed program itself (rows at 16 layers
//    against 15 against 14; at input depth 22 against 21), so every figure below
//    is a difference of two emitted circuits.
//  * the AIR term is leg 13's emission of the root's own 1,093 constraints over
//    10,417 DAG nodes, not the fixture's four.
//
// ⚑ THE LARGEST ATOM MOVED AND THAT IS THE INTERESTING PART. The model's
// `perArith` is 3,221 rows — its "largest indivisible atom, 6.5% of a step",
// the figure that licensed "this is a placement and not a rounding". EMITTED it
// is 2,809, 12.8% lower, because the division charged the fold rounds for a
// residual that is not theirs.

/** The atom prices `scripts/emitted-atoms.ts` measures. Every one is a
 *  difference of two `analyzeMethods` readings on the deployed program. */
export type EmittedAtoms = {
  kind: string;
  geometry: { logD0: number; layers: number; logBlowup: number; inputDepth: number; nBatches: number; queries: number };
  measured: {
    deployedWalkOneQuery: number;
    walk15Layers: number;
    walk14Layers: number;
    walkInputDepth21: number;
    wideOneQuery: number;
    wideCols: number;
    baseCols: number;
  };
  atoms: {
    foldPath: number;
    foldArith: number;
    inputPath: number;
    perColumnOneQuery: number;
    residualPerQuery: number;
  };
  air: {
    nodes: number;
    kinds: Record<string, number>;
    n: number;
    rowsMul: number;
    rowsLin: number;
    rowsCopy: number;
    rowsFold: number;
    rowsWitnessPerCol: number;
    totalRows: number;
  };
};

/**
 * The deployed verifier as an atom list whose every row figure is EMITTED, with
 * the root's own AIR included.
 *
 * ⚑ WHERE THE AIR BLOCK GOES, AND WHY THERE. `verify_constraints_with_lookups`
 * runs ONCE per instance per proof, after the transcript has sampled `alpha` and
 * `zeta` and before any query is walked — which is exactly where
 * `DreggProofSchedule`'s `transcript` method calls `assertAirClosing`. So the
 * AIR atoms sit at the end of the transcript block, not inside a query, and
 * they are paid ONCE rather than 19 times.
 *
 * ⚑ WHAT THE AIR ATOMS READ, stated rather than assumed. The DAG's 1,282 base
 * column variables ARE the root's opened evaluations under the extractor's own
 * numbering (main and preprocessed at two row offsets, plus the three selectors
 * and the public values), so they are charged against the SAME `open*` chunks
 * the absorb atoms read, mapped proportionally — not given a second commitment,
 * which would double-count the lanes. The 320 EXTENSION column variables are
 * the LogUp permutation columns and challenges; the deployed lane census
 * (`carriedLaneCount`) does not carry a permutation commitment at all, so they
 * are charged to `misc` and that is an UNDERCOUNT this comment exists to name.
 */
export function emittedProgram(
  base: DreggProofShape,
  em: EmittedAtoms,
  opts: { openChunkLanes: number; cols?: number; withAir?: boolean },
): Program {
  const cols = opts.cols ?? DEPLOYED_COLS;
  const sh = deployedShapeOf(base, cols);
  const plan = verifyPlan(sh);
  const lanes = carriedLaneCount(sh);
  const { layers, numQueries } = sh.knobs;
  const inputDepth = plan.maxInputDepth;
  const atoms: Atom[] = [];

  const openLanes = plan.nOpenedTrace * 4 + plan.nQuotientVals * 4;
  const foldLanes = layers * 8 + sh.knobs.finalPolyLen * 4;
  const miscLanes = plan.nBatches * 8 + Math.max(sh.air.numPublicValues, 1) + 1;
  if (openLanes + foldLanes + miscLanes !== lanes.root)
    throw new Error(
      `the chunking covers ${openLanes + foldLanes + miscLanes} root lanes, not the ` +
        `${lanes.root} that cross a boundary — a lane in no chunk is a lane nothing binds`,
    );
  const nOpenChunks = Math.ceil(openLanes / opts.openChunkLanes);
  const chunks: Chunk[] = [
    { id: 'misc', lanes: miscLanes },
    { id: 'fold', lanes: foldLanes },
    ...Array.from({ length: nOpenChunks }, (_, i) => ({
      id: `open${i}`,
      lanes: Math.min(opts.openChunkLanes, openLanes - i * opts.openChunkLanes),
    })),
  ];
  const lanesPerCol = (plan.nOpenedTrace * 4) / cols;
  const openChunkOf = (c: number) => `open${Math.floor((c * lanesPerCol) / opts.openChunkLanes)}`;

  const SPONGE_LANES = 16;
  // ── the transcript block ────────────────────────────────────────────────
  for (let c = 0; c < cols; c++)
    atoms.push({
      id: `absorb:${c}`,
      kind: 'absorb-col',
      query: null,
      // The per-column marginal is measured at ONE query and therefore contains
      // the absorb AND that query's DEEP term; the per-query half is subtracted
      // so the absorb is charged once and the DEEP term per query.
      rows: Math.round(em.atoms.perColumnOneQuery - MEASURED.deepPerColumnPerQuery),
      reads: openChunkOf(c),
      ownLanes: lanesPerCol,
      liveAfter: SPONGE_LANES,
    });
  const nTail = Math.ceil(em.atoms.residualPerQuery / PERM_ROWS);
  for (let i = 0; i < nTail; i++)
    atoms.push({
      id: `transcript-tail:${i}`,
      kind: 'transcript-tail',
      query: null,
      rows: Math.round(em.atoms.residualPerQuery / nTail),
      reads: 'misc',
      ownLanes: 0,
      liveAfter: SPONGE_LANES,
    });

  // ── THE ROOT'S OWN AIR ──────────────────────────────────────────────────
  if (opts.withAir !== false) {
    const k = em.air.kinds;
    const nMul = k.mul ?? 0;
    const nLin = (k.add ?? 0) + (k.sub ?? 0) + (k.neg ?? 0);
    const nFree = (k.var ?? 0) + (k.cst ?? 0) + (k.evar ?? 0) + (k.ecst ?? 0);
    // One atom per node, in the emitted node order, at its own EMITTED price.
    // Free nodes are atoms too: a cut may fall between any two, and an atom of
    // zero rows still moves the live set.
    const nDagBaseCols = 1282;
    const airCols = nDagBaseCols + 320;
    let placed = 0;
    const emit = (n: number, rows: number, kind: 'mul' | 'lin' | 'free') => {
      for (let i = 0; i < n; i++) {
        const c = Math.floor((placed / em.air.nodes) * cols);
        atoms.push({
          id: `air:${kind}:${i}`,
          kind: 'air-node',
          query: null,
          rows,
          reads: kind === 'free' ? openChunkOf(Math.min(c, cols - 1)) : 'misc',
          ownLanes: kind === 'free' ? lanesPerCol : 0,
          // ⚑ The live set is a MEASURED property of the DAG, not a guess:
          // `RootAirDag.liveness` bounds the cut width at 102 across all 10,417
          // nodes. 102 extension values is 408 lanes; the mean is 65.1.
          liveAfter: 4 * 102,
        });
        placed++;
      }
    };
    emit(nMul, em.air.rowsMul, 'mul');
    emit(nLin, em.air.rowsLin, 'lin');
    emit(nFree, em.air.rowsCopy, 'free');
    // The witnessing of the AIR's own columns, spread over the free nodes'
    // chunks — it is what `air.rowsWitnessPerCol` prices.
    for (let i = 0; i < em.air.n; i++)
      atoms.push({
        id: `air:fold:${i}`,
        kind: 'air-fold',
        query: null,
        rows: em.air.rowsFold,
        reads: 'misc',
        ownLanes: 0,
        liveAfter: 4 * 102,
      });
    void airCols;
    void nFree;
  }

  // ── the query walks, every figure EMITTED ───────────────────────────────
  const DEEP_OUT_LANES = 4 * (plan.nRollIns + 1) + 1;
  const FOLD_LANES = 4 + 1 + 1 + 1;
  const DEEP_LANES = 8 * (plan.nRollIns + 1) + 1;

  for (let q = 0; q < numQueries; q++) {
    for (let b = 0; b < plan.nBatches; b++)
      for (let h = 0; h < inputDepth; h++)
        atoms.push({
          id: `q${q}:input:${b}:${h}`,
          kind: 'input-path',
          query: q,
          rows: Math.round(em.atoms.inputPath),
          reads: 'misc',
          ownLanes: 0,
          liveAfter: DEEP_LANES,
        });
    for (let c = 0; c < cols; c++)
      atoms.push({
        id: `q${q}:deep:${c}`,
        kind: 'deep-col',
        query: q,
        rows: MEASURED.deepPerColumnPerQuery,
        reads: openChunkOf(c),
        ownLanes: lanesPerCol,
        liveAfter: c === cols - 1 ? DEEP_OUT_LANES : DEEP_LANES,
      });
    for (let r = 0; r < layers; r++) {
      atoms.push({
        id: `q${q}:fold:${r}`,
        kind: 'fold-arith',
        query: q,
        rows: Math.round(em.atoms.foldArith),
        reads: 'fold',
        ownLanes: 0,
        liveAfter: FOLD_LANES,
      });
      for (let h = 0; h < sh.commitPathDepths[r]; h++)
        atoms.push({
          id: `q${q}:foldpath:${r}:${h}`,
          kind: 'fold-path',
          query: q,
          rows: Math.round(em.atoms.foldPath),
          reads: 'fold',
          ownLanes: 0,
          liveAfter: FOLD_LANES,
        });
    }
    atoms.push({
      id: `q${q}:final`,
      kind: 'final-poly',
      query: q,
      rows: Math.round(em.atoms.foldArith),
      reads: 'fold',
      ownLanes: 0,
      liveAfter: 0,
    });
  }

  return {
    atoms,
    chunks,
    challengeLanes: lanes.challenge,
    totalRows: atoms.reduce((a, x) => a + x.rows, 0),
  };
}

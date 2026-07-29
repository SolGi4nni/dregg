import { Field, Poseidon, Provable, SelfProof, ZkProgram } from 'o1js';
import { canonicalLane } from './Poseidon2BabyBearW16.js';
import { BbExt, extAdd, extMul, extSub } from './FriQueryStep.js';
import {
  FOLD_ROWS,
  KIND,
  NODE_ROWS,
  UnifiedDag,
  WITNESS_ROWS_PER_VALUE,
  liveSet,
  liveness,
} from './RootAirDag.js';

// ---------------------------------------------------------------------------
// THE ROOT AIR AS A CHAIN — 275,143 emitted rows do not fit in a 65,536-row
// Pickles step, so the root's own constraint system is decided by chained steps
// or not at all.
//
// ⚑ THIS IS THE SAME SHAPE OF OBJECT AS §3.20/§3.21 AND ONE THING ABOUT IT IS
// DIFFERENT, WHICH IS THE POINT.
//
// §3.20's chain is ONE walk circuit invoked N times, because all 19 query walks
// are the same shape and 573 compiles is not a thing anyone can do — and it
// MEASURED why: a node process that has compiled FOUR step circuits hangs at the
// first `prove`. The AIR is not like that. Its slices are structurally DIFFERENT
// programs (different nodes, different operands), so a uniform circuit is not
// available without an in-circuit multiplexer over the live set, which is priced
// below and is not close.
//
// What makes that acceptable here and not there: **the AIR is a FIXED program.**
// Its slices are the same slices for every dregg proof that will ever be
// verified, so their verification keys are PROTOCOL CONSTANTS, emitted once —
// not a per-proof cost. A per-query-step VK would have been a per-proof cost,
// which is why §3.20 refused one.
//
// ⚑ AND THE PROCESS WALL IS STILL REAL AND IS NAMED WITH ITS NUMBER. Three
// compiled circuits per process is the ceiling (§3.20's measurement), so a
// single-process chain covers 3 x usable rows and no more. The rest is a
// process-per-slice architecture, priced in the leg and not built here.
//
// ⚑ THE LIVE SET IS WHAT MAKES THIS AFFORDABLE, and it is a property of the DAG
// rather than a design choice: the extractor emits in DFS post-order, so the cut
// width — the number of already-computed values a later node still reads —
// never exceeds 102 across all 10,417 nodes, median 66. A boundary therefore
// carries ~100 extension values, not the 1,602 columns.
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;
/** Eight 31-bit lanes pack losslessly into one 254-bit Pasta field; §3.20
 *  measured this carrier at 2.96x cheaper than hashing raw lanes. */
export const LANES_PER_FIELD = 8;
export const LANE_BITS = 31n;
/** The chain opens at a digest a verifier can compute: there is no live set
 *  before the first node. */
export const GENESIS_LIVE_DIGEST = Field(0);

// ===========================================================================
// 1. The boundary — one field element.
// ===========================================================================

export function packLanes(lanes: Field[]): Field[] {
  const out: Field[] = [];
  for (let i = 0; i < lanes.length; i += LANES_PER_FIELD) {
    let acc = Field(0);
    for (let j = 0; j < LANES_PER_FIELD && i + j < lanes.length; j++)
      acc = acc.add(lanes[i + j].mul(Field(1n << (LANE_BITS * BigInt(j)))));
    out.push(acc);
  }
  return out;
}

export const digestOfLanes = (lanes: Field[]): Field =>
  lanes.length === 0 ? Field(0) : Poseidon.hash(packLanes(lanes));

/** `boundary_k = Poseidon(dagDigest, liveDigest, k)` — `KimchiPartition
 *  .StepPublicInput`'s three slots, unchanged. */
export const stepBoundary = (dag: Field, live: Field, k: Field | number): Field =>
  Poseidon.hash([dag, live, typeof k === 'number' ? Field(k) : k]);

/** The terminal seal carries the ACCUMULATOR's digest, not a live set — so the
 *  single external check is one field comparison a verifier computes from the
 *  expected accumulator and the artifact alone. */
export const terminalSeal = (dag: Field, accDigest: Field, nSteps: number): Field =>
  Poseidon.hash([dag, accDigest, Field(nSteps), Field(1)]);

export const extLanes = (e: BbExt): Field[] => e.limbs;

// ===========================================================================
// 2. The column commitment — chunked, as §3.21 established.
// ===========================================================================

export type ColChunk = { id: string; lanes: Field[] };

/**
 * The column assignment, chunked. A slice witnesses the LANES of the chunks its
 * nodes read and the DIGESTS of the ones they do not, re-deriving the same
 * `dagDigest` either way.
 *
 * ⚑ This is §3.21's mechanism, and it is what stops a slice's carry being a
 * function of how wide the root is: the whole assignment is 1,602 extension
 * values (6,408 lanes) and a slice reads a few dozen of them.
 */
export function colChunks(base: BbExt[], ext: BbExt[], chunkSize: number): ColChunk[] {
  const all = [...base, ...ext];
  // ⚑ PADDED to a whole number of chunks. A short final chunk would make a
  // slice's lane offsets depend on WHICH chunks it read, and the two sides of
  // that arithmetic living in different files is exactly how a digest ends up
  // covering a different thing than the circuit thinks it does.
  while (all.length % chunkSize !== 0) all.push(BbExt.zero());
  const out: ColChunk[] = [];
  for (let i = 0; i < all.length; i += chunkSize)
    out.push({
      id: `col${out.length}`,
      lanes: all.slice(i, i + chunkSize).flatMap(extLanes),
    });
  return out;
}

export const chunkCount = (nCols: number, chunkSize: number) => Math.ceil(nCols / chunkSize);
export const dagDigestOfChunkDigests = (ds: Field[]): Field => Poseidon.hash(ds);

// ===========================================================================
// 3. The plan — where the cuts go.
// ===========================================================================

export type Slice = {
  index: number;
  /** Nodes `[from, to)`. */
  from: number;
  to: number;
  /** Constraints `[foldFrom, foldTo)` folded in this slice. */
  foldFrom: number;
  foldTo: number;
  /** Node indices entering / leaving across this slice's boundaries. */
  liveIn: number[];
  liveOut: number[];
  /** Column chunk indices this slice's nodes read. */
  readsChunks: number[];
  /** Modelled rows: node work + fold work + the carry, at leg 13's EMITTED
   *  per-operation prices. The circuit's own `analyzeMethods` is what the leg
   *  quotes; this is what the planner optimises against. */
  workRows: number;
  carryRows: number;
};

export type ChainPlan = {
  slices: Slice[];
  nColChunks: number;
  chunkSize: number;
  nCols: number;
  totalWork: number;
  totalCarry: number;
};

/** What a slice's nodes read, as chunk indices. */
function chunksRead(u: UnifiedDag, from: number, to: number, chunkSize: number): number[] {
  const s = new Set<number>();
  for (let i = from; i < to; i++) {
    const n = u.nodes[i];
    if (n[0] === KIND.var) s.add(Math.floor(n[1] / chunkSize));
    else if (n[0] === KIND.evar) s.add(Math.floor((u.nBaseCols + n[1]) / chunkSize));
  }
  return [...s].sort((a, b) => a - b);
}

/**
 * **THE PLANNER.** Greedy-maximal slices under a row budget: extend the slice
 * while work + carry fits, then cut. The carry is recomputed at each candidate
 * end because it is a function of the cut, not of the slice's length —
 * `liveOut` is the whole point.
 *
 * ⚑ NOT A DP, and the reason is measured rather than assumed: the cut width is
 * bounded by 102 across the whole DAG, so the carry varies by at most ~10,600
 * rows between the best and worst cut in a window, against a ~57,000-row budget.
 * `PartitionSchedule`'s DP exists because a query-entry boundary costs 45x an
 * intra-query one; there is no such cliff here. The leg reports the achieved
 * slack so this claim is visible rather than asserted.
 */
export function planRootAirChain(
  u: UnifiedDag,
  opts: { usableRows: number; chunkSize: number; maxSlices?: number },
): ChainPlan {
  const { lastUse, foldAt } = liveness(u);
  const nCols = u.nBaseCols + u.nExtCols;
  const nColChunks = chunkCount(nCols, opts.chunkSize);
  const slices: Slice[] = [];
  let from = 0;
  let foldFrom = 0;
  let liveIn: number[] = [];
  while (from < u.nodes.length) {
    let work = 0;
    let to = from;
    let best = -1;
    let bestCarry = 0;
    let bestWork = 0;
    while (to < u.nodes.length) {
      work += NODE_ROWS[u.nodes[to]![0]] ?? 0;
      to++;
      // Constraints whose fold position has passed.
      let foldTo = foldFrom;
      while (foldTo < u.roots.length && foldAt[foldTo] < to) foldTo++;
      const w = work + (foldTo - foldFrom) * FOLD_ROWS;
      const lo = liveSet(u, lastUse, to);
      const reads = chunksRead(u, from, to, opts.chunkSize);
      const carry =
        (liveIn.length + lo.length + 1) * WITNESS_ROWS_PER_VALUE * 1 +
        reads.length * opts.chunkSize * WITNESS_ROWS_PER_VALUE +
        nColChunks * WITNESS_ROWS_PER_VALUE;
      if (w + carry > opts.usableRows) {
        to--;
        work -= NODE_ROWS[u.nodes[to]![0]] ?? 0;
        break;
      }
      best = to;
      bestCarry = carry;
      bestWork = w;
      if (opts.maxSlices && slices.length + 1 === opts.maxSlices && to === u.nodes.length) break;
    }
    if (best <= from)
      throw new Error(
        `no slice fits at node ${from}: one node plus its carry exceeds ${opts.usableRows} rows`,
      );
    let foldTo = foldFrom;
    while (foldTo < u.roots.length && foldAt[foldTo] < best) foldTo++;
    const liveOut = best >= u.nodes.length ? [] : liveSet(u, lastUse, best);
    slices.push({
      index: slices.length,
      from,
      to: best,
      foldFrom,
      foldTo,
      liveIn,
      liveOut,
      readsChunks: chunksRead(u, from, best, opts.chunkSize),
      workRows: bestWork,
      carryRows: bestCarry,
    });
    from = best;
    foldFrom = foldTo;
    liveIn = liveOut;
    if (opts.maxSlices && slices.length >= opts.maxSlices) break;
  }
  return {
    slices,
    nColChunks,
    chunkSize: opts.chunkSize,
    nCols,
    totalWork: slices.reduce((a, s) => a + s.workRows, 0),
    totalCarry: slices.reduce((a, s) => a + s.carryRows, 0),
  };
}

// ===========================================================================
// 4. The circuit.
// ===========================================================================

// ---------------------------------------------------------------------------
// ⚑ THE SLICE'S TWO HALVES, FACTORED OUT — because leg 17 compiles this same
// slice ONE PER PROCESS with a side-loaded predecessor, and a second copy of the
// node walk is a second definition of what dregg's AIR means. What is NOT
// factored out is the BOUNDARY: the single-process chain binds a `SelfProof`
// against a baked-in verification key, leg 17 binds a `DynamicProof` against a
// pinned VK hash, and those are different obligations that must read differently.
// ---------------------------------------------------------------------------

/**
 * The column commitment. Range-checks the lanes this slice loaded, digests them
 * chunk by chunk, splices the result into the digests it did NOT load, and
 * returns the one `dagDigest` every slice re-derives.
 */
export function sliceCommitment(
  plan: ChainPlan,
  s: Slice,
  readLanes: Field[],
  otherDigests: Field[],
): Field {
  for (const l of readLanes) canonicalLane(l, LANE_MAX);
  const computed: Field[] = [];
  for (let c = 0; c < s.readsChunks.length; c++)
    computed.push(digestOfLanes(readLanes.slice(c * plan.chunkSize * 4, (c + 1) * plan.chunkSize * 4)));
  // Splice the computed digests into the witnessed ones in chunk order, so
  // `dagDigest` is the SAME object whichever chunks this slice read.
  const digests: Field[] = [];
  let ci = 0;
  let oi = 0;
  for (let c = 0; c < plan.nColChunks; c++)
    digests.push(s.readsChunks.includes(c) ? computed[ci++] : otherDigests[oi++]);
  return dagDigestOfChunkDigests(digests);
}

/**
 * The slice's own work: the node walk over `[from, to)` and the α-fold over
 * `[foldFrom, foldTo)`, in p3's constraint order. Returns the outgoing
 * accumulator and the values this slice must hand on.
 */
export function sliceWork(
  u: UnifiedDag,
  plan: ChainPlan,
  s: Slice,
  alpha: BbExt,
  accIn: BbExt,
  liveInVals: BbExt[],
  readLanes: Field[],
): { acc: BbExt; liveOutVals: BbExt[] } {
  const val = new Map<number, BbExt>();
  s.liveIn.forEach((idx, i) => val.set(idx, liveInVals[i]));
  const colOf = (g: number): BbExt => {
    const chunk = Math.floor(g / plan.chunkSize);
    const at = s.readsChunks.indexOf(chunk);
    if (at < 0)
      throw new Error(`slice ${s.index} reads column ${g} in chunk ${chunk}, which it did not load`);
    const within = g - chunk * plan.chunkSize;
    const off = (at * plan.chunkSize + within) * 4;
    return new BbExt({ limbs: readLanes.slice(off, off + 4) });
  };
  for (let i = s.from; i < s.to; i++) {
    const n = u.nodes[i];
    let v: BbExt;
    switch (n[0]) {
      case KIND.var:
        v = colOf(n[1]);
        break;
      case KIND.evar:
        v = colOf(u.nBaseCols + n[1]);
        break;
      case KIND.cst:
        v = BbExt.from([BigInt(n[1]), 0n, 0n, 0n]);
        break;
      case KIND.ecst:
        v = BbExt.from([BigInt(n[1]), BigInt(n[2]), BigInt(n[3]), BigInt(n[4])]);
        break;
      case KIND.add:
        v = extAdd(val.get(n[1])!, val.get(n[2])!);
        break;
      case KIND.sub:
        v = extSub(val.get(n[1])!, val.get(n[2])!);
        break;
      case KIND.neg:
        v = extSub(BbExt.zero(), val.get(n[1])!);
        break;
      case KIND.mul:
        v = extMul(val.get(n[1])!, val.get(n[2])!);
        break;
      default:
        throw new Error(`unknown kind ${n[0]}`);
    }
    val.set(i, v);
  }
  let acc = accIn;
  for (let j = s.foldFrom; j < s.foldTo; j++) {
    const r = u.roots[j];
    const c = val.get(r);
    if (!c) throw new Error(`slice ${s.index} folds constraint ${j} whose root ${r} is not live`);
    acc = extAdd(extMul(acc, alpha), c);
  }
  const liveOutVals = s.liveOut.map((idx) => {
    const v = val.get(idx);
    if (!v) throw new Error(`slice ${s.index} must hand on node ${idx} and does not hold it`);
    return v;
  });
  return { acc, liveOutVals };
}

export type ChainOpts = {
  /** ⚑ FALSE builds the UNBOUND CONTROL — the same circuit with the boundary
   *  assertions removed. A refusal is attributable to the binding only if
   *  something shows the circuit would otherwise have ACCEPTED. */
  bindCarry?: boolean;
};

/**
 * One `ZkProgram` with one `@method` per slice. Slice 0 has no predecessor;
 * every later slice takes its predecessor as a `SelfProof`.
 *
 * ⚑ THE THREE-CIRCUIT WALL IS ENFORCED HERE, LOUDLY. §3.20 measured a process
 * that compiled four step circuits hanging at the first `prove` — the worker
 * dies and the promise never settles, which from the outside is indistinguish-
 * able from a slow compile. A plan that would silently hang is refused with the
 * number instead.
 */
export function makeRootAirChain(u: UnifiedDag, plan: ChainPlan, opts: ChainOpts = {}) {
  const bind = opts.bindCarry !== false;
  if (plan.slices.length > 3)
    throw new Error(
      `a ${plan.slices.length}-slice chain needs ${plan.slices.length} compiled circuits in one ` +
        'process; §3.20 measured FOUR hanging at the first prove (kimchi\'s wasm heap is 32-bit). ' +
        'Cap the plan at 3 slices or run a process per slice.',
    );
  const { lastUse } = liveness(u);
  void lastUse;

  const methods: Record<string, any> = {};
  const privateInputs: Record<string, any> = {};

  plan.slices.forEach((s, si) => {
    const nLiveIn = s.liveIn.length;
    const nLiveOut = s.liveOut.length;
    const nReadLanes = s.readsChunks.length * plan.chunkSize * 4;
    const nOtherDigests = plan.nColChunks - s.readsChunks.length;
    const key = `slice${si}`;

    /** The body — identical in shape for every slice; only the node range moves. */
    const body = (
      bIn: Field,
      prev: SelfProof<Field, Field> | undefined,
      alpha: BbExt,
      accIn: BbExt,
      liveInVals: BbExt[],
      readLanes: Field[],
      otherDigests: Field[],
    ) => {
      // ── the column commitment ────────────────────────────────────────────
      const dagDigest = sliceCommitment(plan, s, readLanes, otherDigests);

      // ── the boundary in ──────────────────────────────────────────────────
      for (const e of [...liveInVals, accIn, alpha])
        for (const x of e.limbs) canonicalLane(x, LANE_MAX);
      const liveInDigest =
        si === 0
          ? GENESIS_LIVE_DIGEST
          : digestOfLanes([...liveInVals.flatMap(extLanes), ...extLanes(accIn), ...extLanes(alpha)]);
      if (bind) {
        stepBoundary(dagDigest, liveInDigest, si).assertEquals(bIn);
        if (prev) prev.publicOutput.assertEquals(bIn);
      }

      // ── the slice's own work, then the fold in CONSTRAINT order ──────────
      const { acc, liveOutVals } = sliceWork(u, plan, s, alpha, accIn, liveInVals, readLanes);

      // ── the boundary out ─────────────────────────────────────────────────
      void nLiveOut;
      if (si + 1 === plan.slices.length) {
        // ⚑ THE TERMINAL SEAL CARRIES THE ACCUMULATOR, which is what a verifier
        // compares against `quotient(zeta) * Z_H(zeta)`. For a COMPLETE chain
        // the live set is empty, so the seal is `Poseidon(dagDigest,
        // digest(acc), nSteps)` and BOTH ENDS are verifier-computable from the
        // artifact and the expected accumulator alone. For a PARTIAL chain the
        // live set is not empty and it is in the preimage — which means a
        // partial chain's far end is NOT verifier-computable, and the leg says
        // so rather than quoting the complete chain's property for it.
        return terminalSeal(
          dagDigest,
          digestOfLanes([...extLanes(acc), ...liveOutVals.flatMap(extLanes)]),
          plan.slices.length,
        );
      }
      const liveOutDigest = digestOfLanes([
        ...liveOutVals.flatMap(extLanes),
        ...extLanes(acc),
        ...extLanes(alpha),
      ]);
      return stepBoundary(dagDigest, liveOutDigest, si + 1);
    };

    if (si === 0) {
      privateInputs[key] = [
        BbExt,
        BbExt,
        Provable.Array(BbExt, Math.max(nLiveIn, 1)),
        Provable.Array(Field, Math.max(nReadLanes, 1)),
        Provable.Array(Field, Math.max(nOtherDigests, 1)),
      ];
      methods[key] = {
        privateInputs: privateInputs[key],
        async method(
          bIn: Field,
          alpha: BbExt,
          accIn: BbExt,
          liveInVals: BbExt[],
          readLanes: Field[],
          otherDigests: Field[],
        ) {
          return {
            publicOutput: body(
              bIn,
              undefined,
              alpha,
              accIn,
              liveInVals.slice(0, nLiveIn),
              readLanes.slice(0, nReadLanes),
              otherDigests.slice(0, nOtherDigests),
            ),
          };
        },
      };
    } else {
      methods[key] = {
        privateInputs: [
          SelfProof,
          BbExt,
          BbExt,
          Provable.Array(BbExt, Math.max(nLiveIn, 1)),
          Provable.Array(Field, Math.max(nReadLanes, 1)),
          Provable.Array(Field, Math.max(nOtherDigests, 1)),
        ],
        async method(
          bIn: Field,
          prev: SelfProof<Field, Field>,
          alpha: BbExt,
          accIn: BbExt,
          liveInVals: BbExt[],
          readLanes: Field[],
          otherDigests: Field[],
        ) {
          prev.verify();
          return {
            publicOutput: body(
              bIn,
              prev,
              alpha,
              accIn,
              liveInVals.slice(0, nLiveIn),
              readLanes.slice(0, nReadLanes),
              otherDigests.slice(0, nOtherDigests),
            ),
          };
        },
      };
    }
  });

  const prog = ZkProgram({
    name: `dregg-root-air-chain-${plan.slices.length}${bind ? '' : '-UNBOUND'}`,
    publicInput: Field,
    publicOutput: Field,
    methods: methods as any,
  });

  return { prog, plan, bind, nSteps: plan.slices.length };
}

// ===========================================================================
// 5. The out-of-circuit twin — what the harness computes to check the circuit.
// ===========================================================================

export function chainSideOf(
  u: UnifiedDag,
  plan: ChainPlan,
  base: bigint[][],
  ext: bigint[][],
  alpha: bigint[],
) {
  const P = 2013265921n;
  const md = (x: bigint) => ((x % P) + P) % P;
  const eAdd = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x + b[i]));
  const eSub = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x - b[i]));
  const eMul = (a: bigint[], b: bigint[]) => {
    const acc = Array(7).fill(0n) as bigint[];
    for (let i = 0; i < 4; i++)
      for (let j = 0; j < 4; j++) acc[i + j] = md(acc[i + j] + a[i] * b[j]);
    return Array.from({ length: 4 }, (_, i) => (i + 4 < 7 ? md(acc[i] + 11n * acc[i + 4]) : acc[i]));
  };
  const all = [...base, ...ext];
  const nPadded = plan.nColChunks * plan.chunkSize;
  while (all.length < nPadded) all.push([0n, 0n, 0n, 0n]);
  const chunks: bigint[][] = [];
  for (let i = 0; i < nPadded; i += plan.chunkSize)
    chunks.push(all.slice(i, i + plan.chunkSize).flat());

  const v = new Map<number, bigint[]>();
  const evalTo = (to: number) => {
    for (let i = v.size ? Math.max(...v.keys()) + 1 : 0; i < to; i++) {
      const n = u.nodes[i];
      switch (n[0]) {
        case KIND.var:
          v.set(i, all[n[1]]);
          break;
        case KIND.evar:
          v.set(i, all[u.nBaseCols + n[1]]);
          break;
        case KIND.cst:
          v.set(i, [md(BigInt(n[1])), 0n, 0n, 0n]);
          break;
        case KIND.ecst:
          v.set(i, [md(BigInt(n[1])), md(BigInt(n[2])), md(BigInt(n[3])), md(BigInt(n[4]))]);
          break;
        case KIND.add:
          v.set(i, eAdd(v.get(n[1])!, v.get(n[2])!));
          break;
        case KIND.sub:
          v.set(i, eSub(v.get(n[1])!, v.get(n[2])!));
          break;
        case KIND.neg:
          v.set(i, eSub([0n, 0n, 0n, 0n], v.get(n[1])!));
          break;
        default:
          v.set(i, eMul(v.get(n[1])!, v.get(n[2])!));
      }
    }
  };

  const perSlice = plan.slices.map((s) => {
    evalTo(s.to);
    return {
      liveIn: s.liveIn.map((i) => v.get(i)!),
      liveOut: s.liveOut.map((i) => v.get(i)!),
      readLanes: s.readsChunks.flatMap((c) => chunks[c] ?? []),
      readsChunks: s.readsChunks,
    };
  });

  // The accumulator entering each slice.
  const accs: bigint[][] = [[0n, 0n, 0n, 0n]];
  plan.slices.forEach((s) => {
    let acc = accs[accs.length - 1];
    for (let j = s.foldFrom; j < s.foldTo; j++) acc = eAdd(eMul(acc, alpha), v.get(u.roots[j])!);
    accs.push(acc);
  });

  return { chunks, perSlice, accs, valueOf: (i: number) => v.get(i)! };
}

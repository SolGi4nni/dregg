import {
  Bool,
  DynamicProof,
  FeatureFlags,
  Field,
  Poseidon,
  Provable,
  VerificationKey,
  ZkProgram,
} from 'o1js';
import { canonicalLane } from './Poseidon2BabyBearW16.js';
import { BbExt } from './FriQueryStep.js';
import {
  CHAL_WIDTH,
  EXT_LANES,
  FriLaneTable,
  FriPlan,
  FriShape,
  FriSlice,
  LANES_PER_DIGEST,
  OpenedPlan,
  PRICE,
  RealRootFri,
  SegmentedWalk,
  airColumnIndex,
  segmentReads,
} from './RootFriWalk.js';
import {
  AIR_SLICES,
  SliceIo,
  WalkTwin,
  auxLanes,
  chunkedCommitment,
  runSegments,
} from './RootFriSlice.js';
import { dagDigestOfChunkDigests, digestOfLanes, stepBoundary, terminalSeal } from './RootAirChain.js';
import {
  ChainClaim,
  ClaimCarry,
  ClaimedBoundary,
  assertClaimCarried,
  assertClaimSeal,
  claimOfLanes,
  readClaimLanes,
} from './RootClaim.js';

// ---------------------------------------------------------------------------
// THE UNIFORM WALK — one circuit per POSITION IN A QUERY, not one per slice.
//
// ⚑ THE OBSERVATION THIS IS BUILT ON WAS ALREADY WRITTEN DOWN, AS A CONTRAST.
// `RootAirChain`'s header explains why the AIR needs a verification key per
// slice and says, in passing, that a FRI chain does not — "their chains are ONE
// circuit invoked N times, BECAUSE 19 QUERY WALKS ARE THE SAME SHAPE". Nothing
// drew the consequence, and the deployed walk compiles one `ZkProgram` per slice
// index anyway: `friSliceProgramName(si, …)` bakes `si` into the name,
// `friSliceShape(si)` makes the widths a function of `si`, and `AIR_SLICES + si`
// enters the boundary as a compile-time constant. 839 slices, 839 compiles,
// 839 verification keys.
//
// ⚑ THE HOMOGENEITY IS EXACT, AND IT IS CHECKED HERE RATHER THAN ASSUMED.
// `assertHomogeneous` compares the segment list of every query against query 0
// FIELD BY FIELD, and the lane reads after the per-query shift. Measured at the
// root's real geometry: 36 head segments (22 duplex + 14 permBind), then 19
// blocks of 593 segments that are structurally IDENTICAL and carry the same
// 1,593,956.5 modelled rows each. Zero mismatches. A geometry change that broke
// that would fail loudly here instead of quietly producing a wrong chain.
//
// ⚑ WHAT MAKES ONE CIRCUIT SERVABLE AT NINETEEN POSITIONS, AND WHAT PINS IT.
// Three things become witnesses, and each is forced:
//
//   * the STEP INDEX `k`. The head's slices carry it as a compile-time constant
//     (the induction base); a block slice takes it as a private input and
//     asserts `stepBoundary(friCommit, carry, k) == publicInput` AND
//     `predecessor.publicOutput == publicInput`, while the predecessor emitted
//     `..., k_prev + 1`. So `k = k_prev + 1` by collision resistance, inductively
//     from the constant. Exactly `DreggProofPartition.makeChainedProofVerify`.
//   * the QUERY INDEX `q`. It is NOT independently witnessed-and-hoped: the
//     circuit asserts `k == AIR_SLICES + headSlices + q·blockSlices + pos` with
//     `pos` a compile-time constant, so `q` is a function of `k`, and the
//     one-hot over the 19 queries range-checks it. Double-count and skip are
//     therefore impossible for the same reason they are impossible in the
//     deployed chain: `k` is pinned inductively and the terminal seal pins the
//     length.
//   * the TERMINAL BIT. It is not witnessed at all here — the last position of a
//     block emits a seal exactly when `q == numQueries - 1`, and `q` is pinned
//     by `k`. Strictly stronger than the witnessed `isLast` of §3.20.
//
// ⚑ AND THE PREDECESSOR KEY IS STILL PINNED — BY A DIFFERENT MECHANISM, BECAUSE
// A COMPILE-TIME PIN CANNOT CLOSE A RING. The deployed chain pins
// `vk.hash.assertEquals(Field(prevKeyHash))`, a compile-time constant. That
// works for a PATH: slice i is compiled after slice i-1. A uniform block is a
// RING — position 0's predecessor is the head's last slice for q = 0 and the
// block's LAST position for q > 0 — and a ring of compile-time constants has no
// fixed point: position 0 would need the last position's key, which needs
// position 0's. So the key list becomes a MERKLE ROOT carried in the chain, each
// slice proves its predecessor's `vk.hash` at a FIXED LEAF INDEX under that
// root, and the root is anchored where the verifier already looks: the TERMINAL
// SEAL carries it, and the verifier recomputes the seal from the protocol's own
// key list. A prover who substitutes a key list produces a seal that does not
// match. The hole side-loading opens ("a `DynamicProof` circuit makes no
// assertions about the verificationKey used on its own") stays closed, and the
// admissible key at each position is still exactly ONE.
//
// ⚑ ONE PIN STAYS A COMPILE-TIME CONSTANT AND MUST: head slice 0's predecessor
// is AIR slice 6. That is the braid, it is acyclic, and it is untouched.
// ---------------------------------------------------------------------------

const LANE_MAX = (1n << 31n) - 1n;

/** The verification-key list is padded to a fixed power of two so the Merkle
 *  depth — and therefore every slice's cost — does not move when the plan does. */
export const VK_TREE_DEPTH = 7;
export const VK_TREE_LEAVES = 1 << VK_TREE_DEPTH;

/** The modelled cost of what uniformity adds to a slice: the key path, the
 *  one-hot over the queries, the current-index multiplexer and the `k`/`q`
 *  affine tie. A MODEL figure; `root-fri-uniform.ts` measures the real one by
 *  building the same cut twice, once with the indices baked and once with them
 *  witnessed, and reports the difference. */
export const UNIFORM_OVERHEAD_ROWS = 250;

// ===========================================================================
// 1. The layout — where the head ends and what a query block is.
// ===========================================================================

export type UniformLayout = {
  /** Segments before the first query block: the FRI transcript and `permBind`. */
  headSegs: number;
  /** Segments in ONE query block. Every query has exactly this many. */
  blockSegs: number;
  numQueries: number;
  /** Opened row lanes per query, unpadded (`ft.perQueryRowLanes`). */
  qStride: number;
  /** Lanes before the first query's block in the DEPLOYED lane table. */
  globalLanes: number;
  chunkLanes: number;
  nGlobalChunks: number;
  chunksPerQuery: number;
  /** The lane a query block starts at once the global region is chunk-padded. */
  qBase: number;
  /** Total lanes of the uniform (padded) table. */
  nLanes: number;
  nFriChunks: number;
};

/** A segment's identity with the query label removed — two segments at the same
 *  position in two query blocks must agree on this exactly. */
const segSignature = (s: any): string =>
  JSON.stringify(Object.keys(s).filter((k) => k !== 'q').sort().map((k) => [k, s[k]]));

export function uniformLayout(
  w: SegmentedWalk,
  shape: FriShape,
  ft: FriLaneTable,
  chunkLanes: number,
): UniformLayout {
  const numQueries = shape.knobs.numQueries;
  let headSegs = 0;
  while (headSegs < w.segs.length && typeof (w.segs[headSegs] as any).q !== 'number') headSegs++;
  for (let k = headSegs; k < w.segs.length; k++)
    if (typeof (w.segs[k] as any).q !== 'number')
      throw new Error(
        `segment ${k} (${w.segs[k].t}) carries no query label and sits AFTER the head — the walk is ` +
          'not head-then-blocks and the uniform decomposition does not describe it',
      );
  const rest = w.segs.length - headSegs;
  if (rest % numQueries !== 0)
    throw new Error(
      `${rest} segments after the head do not divide into ${numQueries} query blocks — the walk is ` +
        'not homogeneous and one circuit per position would be a lie',
    );
  const blockSegs = rest / numQueries;
  const globalLanes = ft.nLanes - numQueries * ft.perQueryRowLanes;
  if (globalLanes <= 0)
    throw new Error(`the lane table has no global region: ${ft.nLanes} lanes, ${numQueries} queries`);
  const nGlobalChunks = Math.ceil(globalLanes / chunkLanes);
  const chunksPerQuery = Math.ceil(ft.perQueryRowLanes / chunkLanes);
  const qBase = nGlobalChunks * chunkLanes;
  return {
    headSegs,
    blockSegs,
    numQueries,
    qStride: ft.perQueryRowLanes,
    globalLanes,
    chunkLanes,
    nGlobalChunks,
    chunksPerQuery,
    qBase,
    nLanes: qBase + numQueries * chunksPerQuery * chunkLanes,
    nFriChunks: nGlobalChunks + numQueries * chunksPerQuery,
  };
}

/**
 * ⚑ THE CHECK THAT MAKES THE WHOLE CONSTRUCTION HONEST. Every query's segment
 * list is compared against query 0's field by field, its modelled rows compared
 * exactly, and its committed lane reads compared after subtracting the per-query
 * shift. Anything that differs is reported with the position it differs at.
 */
export function assertHomogeneous(
  w: SegmentedWalk,
  op: OpenedPlan,
  ft: FriLaneTable,
  L: UniformLayout,
): { rowsPerBlock: number; headRows: number } {
  //  Works over either lane table: the deployed one packs the query blocks back
  //  to back, the uniform one puts each on a chunk boundary.
  const uni = ft.nLanes === L.nLanes;
  const qBase = uni ? L.qBase : L.globalLanes;
  const qStride = uni ? L.chunksPerQuery * L.chunkLanes : L.qStride;
  const at = (q: number, j: number) => L.headSegs + q * L.blockSegs + j;
  for (let j = 0; j < L.blockSegs; j++) {
    const base = segSignature(w.segs[at(0, j)]);
    const r0 = segmentReads(w, op, ft, at(0, j));
    const key = (xs: number[]) => xs.slice().sort((a, b) => a - b).join(',');
    for (let q = 1; q < L.numQueries; q++) {
      const s = w.segs[at(q, j)];
      if (segSignature(s) !== base)
        throw new Error(
          `query ${q} position ${j} is a DIFFERENT segment from query 0's: ${segSignature(s)} vs ${base}`,
        );
      if ((s as any).q !== q)
        throw new Error(`segment ${at(q, j)} is labelled query ${(s as any).q}, not ${q}`);
      const rq = segmentReads(w, op, ft, at(q, j));
      const shift = q * qStride;
      const norm = rq.fri.map((l) => (l >= qBase ? l - shift : l));
      if (key(norm) !== key(r0.fri))
        throw new Error(
          `query ${q} position ${j} reads different FRI lanes from query 0's, even after the ` +
            `${qStride}-lane per-query shift`,
        );
      if (key(rq.air) !== key(r0.air))
        throw new Error(`query ${q} position ${j} reads different AIR lanes from query 0's`);
    }
  }
  const rowsIn = (a: number, b: number) => {
    let r = 0;
    for (let k = a; k < b; k++) r += w.segs[k].rows;
    return r;
  };
  const rowsPerBlock = rowsIn(at(0, 0), at(1, 0));
  for (let q = 1; q < L.numQueries; q++)
    if (rowsIn(at(q, 0), at(q, 0) + L.blockSegs) !== rowsPerBlock)
      throw new Error(`query ${q}'s block does not carry the same modelled rows as query 0's`);
  return { rowsPerBlock, headRows: rowsIn(0, L.headSegs) };
}

// ===========================================================================
// 2. The lane table, chunk-aligned per query.
// ===========================================================================

/**
 * The deployed table packs the 19 opened-row blocks back to back, so a query's
 * lanes straddle chunk boundaries differently for every query and the chunk a
 * slice reads is a function of `q`. Padding each query's block to a whole number
 * of chunks makes the chunk index `qChunkBase + q·chunksPerQuery + rel`, which
 * is a SHIFT — and a shift is what a witnessed `q` can carry.
 *
 * ⚑ THE PRICE IS NAMED: 33,062 lanes become 35,328 and 130 chunks become 138 at
 * the root's geometry. The padding lanes are zero and are covered by the same
 * digests, so they cost carry and nothing else.
 */
export function uniformLaneTable(shape: FriShape, ft: FriLaneTable, L: UniformLayout): FriLaneTable {
  const remap = (lane: number): number => {
    if (lane < L.globalLanes) return lane;
    const off = lane - L.globalLanes;
    const q = Math.floor(off / L.qStride);
    return L.qBase + q * L.chunksPerQuery * L.chunkLanes + (off - q * L.qStride);
  };
  const fx = ft.fx.map((byRound) => byRound.map((perMat) => perMat.map(remap)));
  const roundOrder = shape.rounds.map((round) => {
    const hs = [...new Set(round.matrices.map((m) => m.logHeight))].sort((a, b) => b - a);
    const order: number[] = [];
    for (const h of hs) round.matrices.forEach((m, mi) => m.logHeight === h && order.push(mi));
    return order;
  });
  const blockLanes = (q: number, ri: number, height: number, block: number): [number, number] => {
    const [a, b] = ft.blockLanes(q, ri, height, block);
    return [remap(a), remap(a) + (b - a)];
  };
  void roundOrder;
  return { ...ft, fx, blockLanes, nLanes: L.nLanes };
}

/** The uniform lane VALUES: the global region as it is, and query `q`'s opened
 *  rows moved to the position query 0's occupy — which is where the one circuit
 *  reads them. */
export function laneValuesForQuery(all: bigint[], L: UniformLayout, q: number): bigint[] {
  const out = all.slice(0, L.qBase);
  const from = L.qBase + q * L.chunksPerQuery * L.chunkLanes;
  for (let i = 0; i < L.chunksPerQuery * L.chunkLanes; i++) out.push(all[from + i] ?? 0n);
  return out;
}

// ===========================================================================
// 3. The planner — cut ONE query block, replay it nineteen times.
// ===========================================================================

export type UniformPlan = {
  /** Cuts over `[0, headSegs)`. One program each; their keys are chain-ordered. */
  head: FriSlice[];
  /** Cuts over query 0's block. One program each, invoked once per query. */
  block: FriSlice[];
  layout: UniformLayout;
  chunkSize: number;
  nAirChunks: number;
  /** `head.length + numQueries · block.length` — slice INSTANCES. */
  totalSlices: number;
  /** `head.length + block.length` — compiles, and verification keys. */
  distinctPrograms: number;
  totalWork: number;
  totalCarry: number;
};

const DIGEST_ROWS = PRICE.witnessLane * EXT_LANES;

function cutRange(
  w: SegmentedWalk,
  op: OpenedPlan,
  ftU: FriLaneTable,
  L: UniformLayout,
  nAirChunks: number,
  from0: number,
  to0: number,
  budget: number,
  flatDigests: boolean,
): FriSlice[] {
  const CL = L.chunkLanes;
  //  ⚑ The witnessed digests a uniform slice carries: every AIR chunk it did
  //  not read, every GLOBAL FRI chunk it did not read, every chunk of its OWN
  //  query it did not read, and the 19 per-query digests. That is 75 at the
  //  root's geometry against the deployed 156 — the two-level commitment is
  //  cheaper, not dearer. `flatDigests` prices the alignment ALONE, against the
  //  deployed one-level commitment, so the two effects are never quoted as one.
  const digestRows =
    (flatDigests
      ? nAirChunks + L.nFriChunks
      : nAirChunks + L.nGlobalChunks + L.chunksPerQuery + L.numQueries) * DIGEST_ROWS;
  const out: FriSlice[] = [];
  let from = from0;
  while (from < to0) {
    let work = 0;
    const airSet = new Set<number>();
    const friSet = new Set<number>();
    let best = -1;
    let bestCarry = 0;
    let bestWork = 0;
    let bestAir: number[] = [];
    let bestFri: number[] = [];
    let to = from;
    while (to < to0) {
      work += w.segs[to].rows;
      const rd = segmentReads(w, op, ftU, to);
      for (const l of rd.air) airSet.add(Math.floor(l / CL));
      for (const l of rd.fri) friSet.add(Math.floor(l / CL));
      to++;
      const carry =
        (w.liveIn[from].length + w.liveIn[to].length) * PRICE.witnessLane +
        (airSet.size + friSet.size) * CL * PRICE.witnessLane +
        digestRows +
        UNIFORM_OVERHEAD_ROWS;
      if (work + carry > budget) {
        to--;
        work -= w.segs[to].rows;
        break;
      }
      best = to;
      bestCarry = carry;
      bestWork = work;
      bestAir = [...airSet].sort((a, b) => a - b);
      bestFri = [...friSet].sort((a, b) => a - b);
    }
    if (best <= from)
      throw new Error(
        `no uniform slice fits at segment ${from} (${w.segs[from].t}, ${Math.round(
          w.segs[from].rows,
        )} rows) under ${budget} rows`,
      );
    out.push({
      index: out.length,
      from,
      to: best,
      liveIn: w.liveIn[from],
      liveOut: w.liveIn[best],
      readsAirChunks: bestAir,
      readsFriChunks: bestFri,
      workRows: bestWork,
      carryRows: bestCarry,
    });
    from = best;
  }
  return out;
}

export function planUniform(
  w: SegmentedWalk,
  op: OpenedPlan,
  ftU: FriLaneTable,
  L: UniformLayout,
  opts: { usableRows: number; flatDigests?: boolean },
): UniformPlan {
  const air = airColumnIndex();
  const flat = opts.flatDigests === true;
  const nAirChunks = Math.ceil(((air.nBase + air.nExt) * EXT_LANES) / L.chunkLanes);
  const head = cutRange(w, op, ftU, L, nAirChunks, 0, L.headSegs, opts.usableRows, flat);
  const block = cutRange(
    w,
    op,
    ftU,
    L,
    nAirChunks,
    L.headSegs,
    L.headSegs + L.blockSegs,
    opts.usableRows,
    flat,
  );
  //  ⚑ A BLOCK IS A RING AND ITS TWO ENDS MUST CARRY THE SAME SLOT LIST. The
  //  walk's own liveness disagrees: at the start of query q+1's block the
  //  transcript slots `qidx[0..q]` are dead, so `liveIn[headSegs + blockSegs]`
  //  is 19 slots SHORTER than `liveIn[headSegs]` and the last position would
  //  emit a carry the next position cannot read. The block therefore exits on
  //  the set it ENTERS on — an over-carry of the dead transcript indices, which
  //  is exactly where the current-query register lives.
  //
  //  This is a real join and no partial proof run reaches it; `[3b]` does.
  const entry = w.liveIn[L.headSegs];
  const last = block[block.length - 1];
  last.carryRows += (entry.length - last.liveOut.length) * PRICE.witnessLane;
  last.liveOut = entry;
  const sum = (xs: FriSlice[], f: (s: FriSlice) => number) => xs.reduce((a, s) => a + f(s), 0);
  return {
    head,
    block,
    layout: L,
    chunkSize: L.chunkLanes,
    nAirChunks,
    totalSlices: head.length + L.numQueries * block.length,
    distinctPrograms: head.length + block.length,
    totalWork: sum(head, (s) => s.workRows) + L.numQueries * sum(block, (s) => s.workRows),
    totalCarry: sum(head, (s) => s.carryRows) + L.numQueries * sum(block, (s) => s.carryRows),
  };
}

// ===========================================================================
// 4. Addressing — where a slice sits in the chain.
// ===========================================================================

export type UniformSpec =
  | { kind: 'head'; pos: number }
  | { kind: 'block'; pos: number };

export const specName = (sp: UniformSpec) => `${sp.kind}${sp.pos}`;

/** The chain step index of a slice instance. `AIR_SLICES` steps of the AIR chain
 *  come first, then the head, then `q` whole query blocks. */
export function stepIndexOf(p: UniformPlan, sp: UniformSpec, q: number): number {
  return sp.kind === 'head'
    ? AIR_SLICES + sp.pos
    : AIR_SLICES + p.head.length + q * p.block.length + sp.pos;
}

/** The step index the chain closes at — what the terminal seal carries. */
export const totalSteps = (p: UniformPlan) => AIR_SLICES + p.totalSlices;

/** The leaf of the key tree a slice's PREDECESSOR occupies. Head slice 0's
 *  predecessor is the AIR chain and is pinned by a constant instead. */
export function prevLeaf(p: UniformPlan, sp: UniformSpec, q: number): number {
  //  Head slice 0's predecessor is AIR slice 6, pinned by a compile-time
  //  constant and NOT by the tree; leaf 0 is returned so a path can still be
  //  built for it, and the circuit never looks at it.
  if (sp.kind === 'head') return Math.max(sp.pos - 1, 0);
  if (sp.pos > 0) return p.head.length + sp.pos - 1;
  return q === 0 ? p.head.length - 1 : p.head.length + p.block.length - 1;
}

export const leafOf = (p: UniformPlan, sp: UniformSpec) =>
  sp.kind === 'head' ? sp.pos : p.head.length + sp.pos;

/** The key list, padded, as a Merkle root over `Poseidon.hash([l, r])`. */
export function vkTreeRoot(hashes: Field[]): Field {
  if (hashes.length > VK_TREE_LEAVES)
    throw new Error(`${hashes.length} programs do not fit a depth-${VK_TREE_DEPTH} key tree`);
  let level = [...hashes];
  while (level.length < VK_TREE_LEAVES) level.push(Field(0));
  for (let d = 0; d < VK_TREE_DEPTH; d++) {
    const next: Field[] = [];
    for (let i = 0; i < level.length; i += 2) next.push(Poseidon.hash([level[i], level[i + 1]]));
    level = next;
  }
  return level[0];
}

export function vkTreePath(hashes: Field[], leaf: number): Field[] {
  let level = [...hashes];
  while (level.length < VK_TREE_LEAVES) level.push(Field(0));
  const path: Field[] = [];
  let i = leaf;
  for (let d = 0; d < VK_TREE_DEPTH; d++) {
    path.push(level[i ^ 1]);
    const next: Field[] = [];
    for (let j = 0; j < level.length; j += 2) next.push(Poseidon.hash([level[j], level[j + 1]]));
    level = next;
    i >>= 1;
  }
  return path;
}

// ===========================================================================
// 5. The two-level FRI commitment.
// ===========================================================================

/**
 * `friDigest = H(g_0 … g_{G-1}, qd_0 … qd_{Q-1})` with `qd_q = H(c_{q,0} …)`.
 *
 * ⚑ WHY IT IS TWO LEVELS. One circuit reads its own query's chunks at query 0's
 * POSITIONS, because that is what makes the circuit uniform. The digest it
 * computes therefore has to be placed at position `q` of the per-query list, and
 * `q` is a witness — so the placement is a one-hot select, the same shape
 * `selectQueryBits` uses in §3.20. Everything else is compile-time.
 */
export function uniformFriDigest(
  L: UniformLayout,
  readsGlobal: number[],
  readsQuery: number[],
  readLanes: Field[],
  otherGlobal: Field[],
  otherQuery: Field[],
  otherQd: Field[],
  isQ: Bool[],
): Field {
  const CL = L.chunkLanes;
  for (const l of readLanes) canonicalLane(l, LANE_MAX);
  const G = readsGlobal.length;
  const globals: Field[] = [];
  let gi = 0;
  let oi = 0;
  for (let c = 0; c < L.nGlobalChunks; c++)
    globals.push(
      readsGlobal.includes(c)
        ? digestOfLanes(readLanes.slice(gi * CL, (gi++ + 1) * CL))
        : otherGlobal[oi++],
    );
  const qChunks: Field[] = [];
  let qi = 0;
  let qo = 0;
  for (let c = 0; c < L.chunksPerQuery; c++)
    qChunks.push(
      readsQuery.includes(c)
        ? digestOfLanes(readLanes.slice((G + qi) * CL, (G + qi++ + 1) * CL))
        : otherQuery[qo++],
    );
  const qd = dagDigestOfChunkDigests(qChunks);
  const qdList: Field[] = [];
  for (let j = 0; j < L.numQueries; j++) qdList.push(Provable.if(isQ[j], qd, otherQd[j]));
  return dagDigestOfChunkDigests([...globals, ...qdList]);
}

/** The same function on constants, for the out-of-circuit twin. */
export function uniformFriDigestOf(L: UniformLayout, lanes: bigint[]): Field {
  const CL = L.chunkLanes;
  const d = (a: number, n: number) =>
    digestOfLanes(lanes.slice(a, a + n).map((x) => Field(x ?? 0n)));
  const globals: Field[] = [];
  for (let c = 0; c < L.nGlobalChunks; c++) globals.push(d(c * CL, CL));
  const qds: Field[] = [];
  for (let q = 0; q < L.numQueries; q++) {
    const base = L.qBase + q * L.chunksPerQuery * CL;
    const cs: Field[] = [];
    for (let c = 0; c < L.chunksPerQuery; c++) cs.push(d(base + c * CL, CL));
    qds.push(dagDigestOfChunkDigests(cs));
  }
  return dagDigestOfChunkDigests([...globals, ...qds]);
}

/** The per-query digests a slice witnesses for the OTHER eighteen queries. */
export function otherQdOf(L: UniformLayout, lanes: bigint[]): Field[] {
  const CL = L.chunkLanes;
  const out: Field[] = [];
  for (let q = 0; q < L.numQueries; q++) {
    const base = L.qBase + q * L.chunksPerQuery * CL;
    const cs: Field[] = [];
    for (let c = 0; c < L.chunksPerQuery; c++)
      cs.push(digestOfLanes(lanes.slice(base + c * CL, base + (c + 1) * CL).map((x) => Field(x ?? 0n))));
    out.push(dagDigestOfChunkDigests(cs));
  }
  return out;
}

// ===========================================================================
// 6. The slice program.
// ===========================================================================

export type UniformCtx = {
  w: SegmentedWalk;
  shape: FriShape;
  ft: FriLaneTable;
  op: OpenedPlan;
  plan: UniformPlan;
  real: RealRootFri;
};

export type UniformOpts = {
  /** ⚑ FALSE builds the UNBOUND control — the boundary assertions removed. */
  bindCarry?: boolean;
  /** ⚑ FALSE builds the UNPINNED control — the predecessor's key is verified
   *  against but never proved to be the one the chain names. */
  pinVk?: boolean;
  /** ⚑ FALSE bakes `k` and `q` back in as compile-time constants at a chosen
   *  query — the BASELINE the uniformity cost is measured against. */
  uniform?: boolean;
  /** The query the baked baseline is built at. Ignored when `uniform`. */
  bakedQuery?: number;
  /** Head slice 0 pins AIR slice 6's key as a constant; nothing else does. */
  airVkHash?: bigint;
  /** ⚑ THE THIRD VARIANT, and it exists to price the ring-breaking separately
   *  from the index-witnessing. When set, the predecessor's key is pinned by
   *  this compile-time constant instead of by the carried key tree — which is
   *  what the DEPLOYED chain does and what a ring cannot do. */
  constKeyPin?: bigint;
  /** ⚑ One `DynamicProof` class per PROCESS, not per program. Row measurement
   *  builds three variants in one process and must share it. */
  prevClass?: any;
  prevFlags: FeatureFlags;
  /** ⚑ THE CLAIM THE CHAIN CARRIES OUT (§3.30). ABSENT builds the chain exactly
   *  as §3.29 left it — `publicOutput: Field`, a boundary and nothing else, and
   *  a Mina-side verifier that learns "*some* batch with these column digests
   *  verifies". PRESENT makes the public output `ClaimedBoundary`, so the
   *  terminal proof STATES `(genesisRoot, finalRoot, numTurns, chainDigest)`.
   *
   *  ⚑ BREAKING WHEN PRESENT: the public output type changes, so every
   *  verification key in the chain changes and the whole key list re-emits. */
  claim?: ClaimCarry;
};

export function uniformProgramName(sp: UniformSpec, o: UniformOpts) {
  const bind = o.bindCarry !== false;
  const pin = o.pinVk !== false;
  const uni = o.uniform !== false;
  return (
    `dregg-root-fri-${sp.kind}${sp.pos}` +
    (uni ? '' : `-BAKED-q${o.bakedQuery ?? 0}`) +
    (o.constKeyPin === undefined ? '' : '-CONSTKEY') +
    (o.claim === undefined ? '' : o.claim.armed === false ? '-CLAIM-UNSEALED' : '-CLAIM') +
    (bind ? '' : '-UNBOUND') +
    (pin ? '' : '-UNPINNED')
  );
}

/** The slice of the plan a spec names, and its private-input widths. */
export function uniformSlice(p: UniformPlan, sp: UniformSpec): FriSlice {
  return sp.kind === 'head' ? p.head[sp.pos] : p.block[sp.pos];
}

export function uniformShape(ctx: UniformCtx, sp: UniformSpec) {
  const { w, plan } = ctx;
  const L = plan.layout;
  const sl = uniformSlice(plan, sp);
  const CL = L.chunkLanes;
  let aux = 0;
  for (let k = sl.from; k < sl.to; k++) aux += auxLanes(w.segs[k]);
  const readsGlobal = sl.readsFriChunks.filter((c) => c < L.nGlobalChunks);
  const readsQuery = sl.readsFriChunks
    .filter((c) => c >= L.nGlobalChunks)
    .map((c) => c - L.nGlobalChunks);
  for (const c of readsQuery)
    if (c >= L.chunksPerQuery)
      throw new Error(
        `${specName(sp)} reads FRI chunk ${c + L.nGlobalChunks}, which belongs to a query OTHER ` +
          'than the one its segments are labelled with — the uniform decomposition is wrong',
      );
  return {
    sl,
    readsGlobal,
    readsQuery,
    nLiveIn: sl.liveIn.length,
    nLiveOut: sl.liveOut.length,
    nAirRead: sl.readsAirChunks.length * CL,
    nAirOther: plan.nAirChunks - sl.readsAirChunks.length,
    nFriRead: sl.readsFriChunks.length * CL,
    nOtherGlobal: L.nGlobalChunks - readsGlobal.length,
    nOtherQuery: L.chunksPerQuery - readsQuery.length,
    nAux: aux,
    isBlockLast: sp.kind === 'block' && sp.pos + 1 === plan.block.length,
  };
}

let sideloadedClasses = 0;

/** ⚑ ONE side-loaded class per process — `DynamicProof.tag()` names itself off a
 *  process-global counter, so a second class in one process gets an identifier
 *  that depends on creation ORDER.
 *
 *  ⚑ `withClaim` PICKS THE PREDECESSOR'S PUBLIC OUTPUT TYPE, and it is not
 *  cosmetic: head slice 0's predecessor is the AIR chain, which emits a plain
 *  `Field` terminal seal, while every later predecessor is a claim-carrying
 *  slice emitting a `ClaimedBoundary`. */
export function makePrevProofClass(flags: FeatureFlags, withClaim = false) {
  if (sideloadedClasses > 0)
    throw new Error(
      'a SECOND side-loaded proof class in one process: build one slice program per process',
    );
  sideloadedClasses++;
  class PrevProof extends DynamicProof<Field, any> {
    static publicInputType = Field;
    static publicOutputType = (withClaim ? ClaimedBoundary : Field) as any;
    static maxProofsVerified = 1 as const;
    static featureFlags = flags;
  }
  return PrevProof;
}

/** The carried digest: the live set and the AIR accumulator as the deployed
 *  chain hashes them, plus the key-tree root the chain carries. */
const carriedDigest = (live: Field[], acc: Field[], vkRoot: Field): Field =>
  Poseidon.hash([digestOfLanes([...live, ...acc]), vkRoot]);

const terminalDigest = (acc: Field[], out: Field[], vkRoot: Field): Field =>
  Poseidon.hash([digestOfLanes([...acc, ...out]), vkRoot]);

export function makeUniformSliceProgram(ctx: UniformCtx, sp: UniformSpec, opts: UniformOpts) {
  const { w, shape, ft, op, plan } = ctx;
  const L = plan.layout;
  const bind = opts.bindCarry !== false;
  const pin = opts.pinVk !== false;
  const uni = opts.uniform !== false;
  const bakedQ = opts.bakedQuery ?? 0;
  const sh = uniformShape(ctx, sp);
  const CL = L.chunkLanes;
  const Q = L.numQueries;
  const isHead0 = sp.kind === 'head' && sp.pos === 0;
  if (isHead0 && opts.airVkHash === undefined && pin)
    throw new Error(
      'head slice 0 pins AIR slice 6\'s verification key and was given none — an unpinned ' +
        "side-loaded chain accepts any program's proof and is not a chain",
    );

  //  ⚑ HEAD SLICE 0's PREDECESSOR IS THE AIR CHAIN and emits a plain `Field`;
  //  every other predecessor is a claim-carrying slice.
  const Prev = opts.prevClass ?? makePrevProofClass(opts.prevFlags, !!opts.claim && !isHead0);
  const carry = opts.claim;
  const arr = (n: number) => Provable.Array(Field, Math.max(n, 1));
  //  The plan's slices index `runSegments`, which reads `plan.slices[si]`.
  const runPlan: FriPlan = {
    slices: [sh.sl],
    nAirChunks: plan.nAirChunks,
    nFriChunks: L.nFriChunks,
    chunkSize: CL,
    totalWork: 0,
    totalCarry: 0,
  };
  /** Leaf-index bits of the predecessor, per query case. Compile-time except at
   *  a block's position 0, where the two cases differ and are selected on `q`. */
  const bitsOf = (leaf: number) =>
    Array.from({ length: VK_TREE_DEPTH }, (_, i) => ((leaf >> i) & 1) === 1);
  const leafFirst = prevLeaf(plan, sp, 0);
  const leafLater = prevLeaf(plan, sp, Math.min(1, Q - 1));
  const leafSplit = sp.kind === 'block' && sp.pos === 0 && leafFirst !== leafLater;

  const prog = ZkProgram({
    name: uniformProgramName(sp, opts),
    publicInput: Field,
    //  ⚑ THE CHAIN'S PUBLIC OUTPUT. `Field` is §3.29's — a boundary, and a
    //  verifier that never learns which proof it verified. `ClaimedBoundary`
    //  carries the claim beside it.
    publicOutput: (carry ? ClaimedBoundary : Field) as any,
    methods: {
      slice: {
        privateInputs: [
          Prev,
          VerificationKey,
          Field, //                          k — the chain step index, witnessed
          Field, //                          q — the query, tied to k below
          Field, //                          vkRoot — the key list, carried
          Provable.Array(Field, VK_TREE_DEPTH),
          BbExt, //                          the AIR chain's terminal accumulator
          arr(sh.nLiveIn),
          arr(sh.nAirRead),
          arr(sh.nAirOther),
          arr(sh.nFriRead),
          arr(sh.nOtherGlobal),
          arr(sh.nOtherQuery),
          Provable.Array(Field, Q),
          arr(sh.nAux),
          //  ⚑ THE CLAIM IS A PRIVATE INPUT AND THAT IS NOT A HOLE. It is
          //  forced twice: the sealing slice asserts it IS the `expose_claim`
          //  lanes under `dagDigest`, and every slice asserts it equals its
          //  predecessor's. A slice that only propagates therefore has no
          //  freedom either — its claim is pinned inductively from the seal,
          //  exactly the way `k` is pinned from the base of the chain.
          ...(carry ? [ChainClaim] : []),
        ] as any,
        async method(
          bIn: Field,
          prev: InstanceType<typeof Prev>,
          vk: VerificationKey,
          kIn: Field,
          qIn: Field,
          vkRoot: Field,
          vkPath: Field[],
          acc: BbExt,
          liveIn: Field[],
          airLanes: Field[],
          airOther: Field[],
          friLanes: Field[],
          otherGlobal: Field[],
          otherQuery: Field[],
          otherQd: Field[],
          aux: Field[],
          claimIn?: ChainClaim,
        ) {
          // ---- the query, and what forces it -----------------------------
          //  ⚑ `q` is a private input and a private input is a value the prover
          //  chooses. It is forced by an EQUATION against `k`, which is itself
          //  forced inductively by the boundary chain: `k = AIR_SLICES +
          //  |head| + q·|block| + pos` with `pos` a compile-time constant. The
          //  one-hot below range-checks it into `[0, numQueries)`, so the
          //  equation has exactly one solution and a witnessed index that
          //  nothing constrains does not exist here.
          const q = uni ? qIn : Field(bakedQ);
          const isQ = Array.from({ length: Q }, (_, j) => q.equals(Field(j)));
          let hot = Field(0);
          for (const b of isQ) hot = hot.add(b.toField());
          hot.assertEquals(Field(1));

          const kConst =
            sp.kind === 'head'
              ? stepIndexOf(plan, sp, 0)
              : AIR_SLICES + plan.head.length + sp.pos;
          const k = uni && sp.kind === 'block' ? kIn : Field(stepIndexOf(plan, sp, bakedQ));
          if (uni && sp.kind === 'block')
            k.assertEquals(Field(kConst).add(q.mul(Field(plan.block.length))));

          // ---- the predecessor, and the key it was made under -------------
          if (pin) {
            if (isHead0) {
              //  ⚑ THE BRAID'S PIN, UNCHANGED. AIR slice 6's key is a
              //  compile-time constant here and the edge is acyclic.
              vk.hash.assertEquals(Field(opts.airVkHash!));
            } else if (opts.constKeyPin !== undefined) {
              //  The deployed shape, kept as a priceable variant: one constant.
              vk.hash.assertEquals(Field(opts.constKeyPin));
            } else {
              //  ⚑ A RING CANNOT BE PINNED BY A CONSTANT (see the header). The
              //  key list is a carried Merkle root; the LEAF INDEX is fixed, so
              //  exactly one key is admissible at this position.
              const bits = leafSplit
                ? bitsOf(leafFirst).map((b, i) =>
                    Provable.if(isQ[0], Bool(b), Bool(bitsOf(leafLater)[i])),
                  )
                : bitsOf(leafFirst).map((b) => Bool(b));
              let cur = vk.hash;
              for (let d = 0; d < VK_TREE_DEPTH; d++) {
                const l = Provable.if(bits[d], vkPath[d], cur);
                const r = Provable.if(bits[d], cur, vkPath[d]);
                cur = Poseidon.hash([l, r]);
              }
              cur.assertEquals(vkRoot);
            }
          }
          prev.verify(vk);

          // ---- the commitments -------------------------------------------
          const dagDigest = chunkedCommitment(
            plan.nAirChunks,
            CL,
            sh.sl.readsAirChunks,
            airLanes.slice(0, sh.nAirRead),
            airOther.slice(0, sh.nAirOther),
          );
          const friDigest = uniformFriDigest(
            L,
            sh.readsGlobal,
            sh.readsQuery,
            friLanes.slice(0, sh.nFriRead),
            otherGlobal.slice(0, sh.nOtherGlobal),
            otherQuery.slice(0, sh.nOtherQuery),
            otherQd,
            isQ,
          );
          const friCommit = Poseidon.hash([dagDigest, friDigest]);

          const live = liveIn.slice(0, sh.nLiveIn);
          for (const l of live) canonicalLane(l, LANE_MAX);
          for (const l of acc.limbs) canonicalLane(l, LANE_MAX);

          // ---- the boundary this slice enters ----------------------------
          if (bind) {
            const want = isHead0
              ? //  ⚑ THE BRAID. Head slice 0 enters AIR slice 6's terminal seal,
                //  recomputed from the AIR column chunks THIS circuit loads.
                terminalSeal(dagDigest, digestOfLanes([...acc.limbs]), AIR_SLICES)
              : stepBoundary(friCommit, carriedDigest(live, acc.limbs, vkRoot), k);
            want.assertEquals(bIn);
            //  ⚑ THE PREDECESSOR'S BOUNDARY, and — once the chain carries a
            //  claim — its CLAIM. Head slice 0's predecessor is the AIR chain
            //  and has no claim to carry; the seal below is what forces head
            //  slice 0's claim anyway, inductively, through this equality.
            if (carry && !isHead0) {
              const po = prev.publicOutput as ClaimedBoundary;
              po.boundary.assertEquals(bIn);
              assertClaimCarried(po.claim, claimIn!);
            } else {
              (prev.publicOutput as Field).assertEquals(bIn);
            }
          }

          // ---- the claim, sealed where the chunks already are -------------
          //  ⚑ NOT A FRESH WITNESS. `readClaimLanes` resolves the 25
          //  `expose_claim|public[i]` lanes out of the SAME loaded AIR chunks
          //  whose digests were just spliced into `dagDigest`, which the
          //  boundary above pins. Replacing one prover-chosen value with
          //  another is this campaign's failure mode, not its fix.
          if (carry?.seals)
            assertClaimSeal(
              claimIn!,
              claimOfLanes(
                readClaimLanes(carry.ix, sh.sl.readsAirChunks, CL, airLanes.slice(0, sh.nAirRead)),
              ),
              carry.armed !== false,
            );

          // ---- the walk ---------------------------------------------------
          const sto = new Map<number, Field>();
          w.liveIn[sh.sl.from].forEach((slot, i) => sto.set(slot, live[i]));
          if (sp.kind === 'block' && sp.pos === 0) {
            //  ⚑ THE CURRENT-QUERY REGISTER. Slot `qidx[0]` is the index the
            //  block's segments walk; the other eighteen carry the transcript's
            //  remaining indices. A block opens by selecting its own out of the
            //  carried set on the one-hot — so the index a block walks is the
            //  index the TRANSCRIPT derived for the query its position names,
            //  and not one the prover chose. Without this a uniform chain would
            //  walk the same query nineteen times.
            const slots = w.slots.qidx;
            let cur = Field(0);
            for (let j = 0; j < Q; j++)
              cur = cur.add(isQ[j].toField().mul(sto.get(slots[j])!));
            sto.set(slots[0], cur);
          }
          runSegments(w, shape, ft, op, runPlan, 0, sto, {
            airLanes: airLanes.slice(0, sh.nAirRead),
            airOther: airOther.slice(0, sh.nAirOther),
            friLanes: friLanes.slice(0, sh.nFriRead),
            friOther: [],
            aux: aux.slice(0, sh.nAux),
          } as SliceIo);
          const out = sh.sl.liveOut.map((slot) => {
            const v = sto.get(slot);
            if (v === undefined)
              throw new Error(
                `${specName(sp)} must hand on slot ${w.slots.names[slot]} and does not hold it`,
              );
            return v;
          });

          // ---- the boundary it emits --------------------------------------
          //  ⚑ THE TERMINAL BIT IS NOT A WITNESS. The block's last position
          //  seals exactly when `q` is the last query, and `q` is pinned by `k`.
          const kOut = k.add(1);
          const seal = terminalSeal(
            friCommit,
            terminalDigest(acc.limbs, out, vkRoot),
            Field(totalSteps(plan)),
          );
          const step = stepBoundary(friCommit, carriedDigest(out, acc.limbs, vkRoot), kOut);
          const boundary = sh.isBlockLast ? Provable.if(isQ[Q - 1], seal, step) : step;
          //  ⚑ THE TERMINAL PROOF NOW STATES WHAT IT PROVED. The boundary field
          //  is byte-for-byte §3.29's; the claim rides beside it, so a Mina-side
          //  verifier reads `(genesisRoot, finalRoot, numTurns, chainDigest)`
          //  instead of comparing a digest of prover-supplied lanes against
          //  nothing.
          return { publicOutput: carry ? new ClaimedBoundary({ boundary, claim: claimIn! }) : boundary };
        },
      },
    },
  });
  return { prog, Prev, sp, bind, pin, uniform: uni, shape: sh, leafFirst, leafLater, leafSplit };
}

// ===========================================================================
// 7. The out-of-circuit twin of the boundaries.
// ===========================================================================

/** The global segment index a slice instance covers. */
export function globalRange(p: UniformPlan, sp: UniformSpec, q: number): [number, number] {
  const sl = uniformSlice(p, sp);
  if (sp.kind === 'head') return [sl.from, sl.to];
  const shift = q * p.layout.blockSegs;
  return [sl.from + shift, sl.to + shift];
}

/** The carried values a slice instance enters with: the live set of query 0's
 *  block at this position, read out of query `q`'s state — and with slot
 *  `qidx[0]` holding the CURRENT query's index rather than query 0's. */
export function carriedLanes(
  ctx: UniformCtx,
  twin: WalkTwin,
  sp: UniformSpec,
  q: number,
  end: 'in' | 'out',
): bigint[] {
  const { w, plan } = ctx;
  const S = w.slots;
  const sl = uniformSlice(plan, sp);
  const [gFrom, gTo] = globalRange(plan, sp, q);
  //  The SLOT LIST is query 0's — that is what the one circuit reads. The
  //  VALUES are query `q`'s, read at the corresponding global position.
  const slots = end === 'in' ? sl.liveIn : sl.liveOut;
  const at = end === 'in' ? gFrom : gTo;
  const byId = new Map<number, bigint>();
  w.liveIn[at].forEach((slot, i) => byId.set(slot, twin.carry[at][i]));
  //  ⚑ Which transcript index the CURRENT-QUERY REGISTER (slot `qidx[0]`) holds
  //  at this end: the previous block's on the way IN to a block's position 0,
  //  this block's everywhere after.
  const register =
    sp.kind !== 'block'
      ? S.qidx[0]
      : end === 'in' && sp.pos === 0
        ? S.qidx[Math.max(q - 1, 0)]
        : S.qidx[q];
  return slots.map((slot) => {
    const src = slot === S.qidx[0] ? register : slot;
    const v = byId.get(src);
    if (v !== undefined) return v;
    return twinValue(w, twin, src);
  });
}

/**
 * Query 0's live set is a SUPERSET of a later query's — the transcript's own
 * `alpha`, `beta` and `qidx` slots die once the last query that needs them is
 * done, and the uniform circuit carries them at every position. Their values are
 * CONSTANT after the head, so the twin's final state is the right reader.
 *
 * ⚑ AND IT IS A CHECKED CLAIM, NOT A CONVENIENCE. Any other slot family
 * reaching here would mean query 0's live set contains a query-LOCAL slot a
 * later query does not, which would make the decomposition wrong; it throws.
 */
function twinValue(w: SegmentedWalk, twin: WalkTwin, slot: number): bigint {
  const name = w.slots.names[slot];
  if (!/^(alpha|beta\d+|qidx)\[/.test(name))
    throw new Error(
      `slot ${name} is live in query 0's block and dead in a later query's at the same position — ` +
        'the query blocks are not carrying the same state and one circuit does not serve both',
    );
  return twin.at.get(slot) ?? 0n;
}

export function uniformBoundaryIn(
  ctx: UniformCtx,
  twin: WalkTwin,
  sp: UniformSpec,
  q: number,
  dagDigest: Field,
  friCommit: Field,
  acc: bigint[],
  vkRoot: Field,
): Field {
  if (sp.kind === 'head' && sp.pos === 0)
    return terminalSeal(dagDigest, digestOfLanes(acc.map((x) => Field(x))), AIR_SLICES);
  const live = carriedLanes(ctx, twin, sp, q, 'in').map((x) => Field(x));
  return stepBoundary(
    friCommit,
    carriedDigest(live, acc.map((x) => Field(x)), vkRoot),
    Field(stepIndexOf(ctx.plan, sp, q)),
  );
}

export function uniformBoundaryOut(
  ctx: UniformCtx,
  twin: WalkTwin,
  sp: UniformSpec,
  q: number,
  friCommit: Field,
  acc: bigint[],
  vkRoot: Field,
): Field {
  const p = ctx.plan;
  const out = carriedLanes(ctx, twin, sp, q, 'out').map((x) => Field(x));
  const a = acc.map((x) => Field(x));
  const last = sp.kind === 'block' && sp.pos + 1 === p.block.length && q === p.layout.numQueries - 1;
  return last
    ? terminalSeal(friCommit, terminalDigest(a, out, vkRoot), Field(totalSteps(p)))
    : stepBoundary(friCommit, carriedDigest(out, a, vkRoot), Field(stepIndexOf(p, sp, q) + 1));
}

/** The aux lanes a slice instance consumes, in segment order. */
export function auxOf(ctx: UniformCtx, twin: WalkTwin, sp: UniformSpec, q: number): bigint[] {
  const [gFrom, gTo] = globalRange(ctx.plan, sp, q);
  const out: bigint[] = [];
  for (let k = gFrom; k < gTo; k++) out.push(...twin.aux[k]);
  return out;
}

export { CHAL_WIDTH, LANES_PER_DIGEST };

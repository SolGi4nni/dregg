import { BbExt } from './FriQueryStep.js';
import { DEPLOYED_KNOBS, FriKnobs } from './FriChallenger.js';
import { RealRootAir, rootAirDag } from './RootAirDag.js';

// ---------------------------------------------------------------------------
// THE ROOT'S FRI WALK AS A SEGMENT LIST — the object the AIR chain's terminal
// seal is braided INTO.
//
// ⚑ WHAT THIS IS FOR. The AIR half is closed at real geometry: seven slices,
// seven processes, all 10,417 DAG nodes and all 1,093 constraints over dregg's
// committed root proof, ending in `terminalSeal(dagDigest, digest(acc), 7)` —
// and `acc` is verifier-computable as `Σ_T acc_T · α^(1093 − b_T)`. That seal
// says the AIR's closing equalities hold **at the opened values the chain was
// handed**. It says nothing about whether those opened values are the ones
// dregg committed to. Authenticating them is the FRI walk, and the two halves
// have never been the same chain.
//
// ⚑ AND THE JOIN IS NOT A CONCATENATION. Two chains glued end to end, each
// reading its own copy of the opened values, prove strictly less than either
// looks like it proves: the AIR half folds one set of numbers, the FRI half
// authenticates another, and nothing says they are the same set. The braid is
// therefore built on ONE column commitment. `dagDigest` — the AIR chain's own
// chunked commitment over its 1,602 extension values — is carried across the
// seal into the FRI slices, and every DEEP-quotient term whose `f(z)` the AIR
// legend names is READ OUT OF THOSE CHUNKS rather than witnessed again. A FRI
// half that authenticated different numbers would re-derive a different
// `dagDigest` and the boundary would refuse.
//
// ⚑ WHAT THE AIR LEGEND DOES NOT COVER, MEASURED RATHER THAN ASSUMED. The AIR
// reads only the columns it constrains: 1,060 of the 1,880 opened main values,
// 176 of the 350 preprocessed, and all 128 permutation ones. The quotient-chunk
// openings it never touches at all. So the braid binds 1,364 of the walk's
// 2,798 DEEP terms to the AIR's own commitment and the remaining 1,434 to a
// second, FRI-side one (`friDigest`). Both are in the boundary; only the first
// is shared with the AIR half, and `deepTermSplit` reports the ratio so the
// claim is a number.
//
// ⚑ 2,798, NOT 2,286. §3.15 prices the DEEP quotient at 2,286 terms —
// `940·2 + 175·2 + 7·2·4`. That census omits the PERMUTATION round entirely:
// the root's seven instances carry 64 extension permutation columns, which is
// `64 · 4 · 2 = 512` further base terms. The real count is 2,798, 22% higher,
// and every per-query DEEP figure derived from 2,286 is low by that factor.
//
// ⚑ THE UNIT OF ACCOUNT IS A SEGMENT, AND A CUT MAY ONLY FALL BETWEEN TWO.
// A slice is a contiguous run of segments, exactly as an AIR slice is a
// contiguous run of DAG nodes. Segments are chosen so that every one of them
// fits inside a step domain with room to spare (the widest is one 452-column
// DEEP matrix at ~34,000 rows) and so that the state crossing a cut is small:
// a challenger sponge, a running Merkle digest, a running fold value, and the
// derived challenges. What does NOT cross is the per-query Merkle data — every
// row, path digest and sibling belongs to exactly one segment, and is
// self-authenticating, because the opening it feeds binds it to a commitment
// that IS in the boundary.
// ---------------------------------------------------------------------------

export const LANES_PER_DIGEST = 8;
export const EXT_LANES = 4;
export const CHAL_WIDTH = 16;
export const CHAL_RATE = 8;

// ===========================================================================
// 1. Measured unit prices. Every one of these is a `getRows()` figure from a
//    committed leg, not an estimate; the § is where it was taken.
// ===========================================================================

export const PRICE = {
  /** One Poseidon2-w16-BabyBear permutation (§3.8, measured 2,600.5). */
  perm: 2601,
  /** One Merkle level: `condSwap` + `compress` + the sibling's 8 range checks
   *  (§3.9, measured 2,677). */
  merkleLevel: 2677,
  /** A mixed-height INJECTION: `compress(root, digestOfRowsAtThisHeight)`. No
   *  `condSwap` and no witnessed sibling — both operands are computed. */
  merkleInject: 2601,
  /** One extension Horner step `acc ← acc·α + v` (§3.14, measured 49). */
  horner: 49,
  /** One arity-2 `fold_row` (§3.14, measured 150). */
  foldRow: 150,
  /** One reduced-opening roll-in: `folded += β² · ro` (§3.13, measured 88). */
  rollIn: 88,
  extMul: 31,
  extAdd: 19,
  /** `extInverse`: witness 4 lanes, one `extMul`, four canonical comparisons. */
  extInverse: 88,
  /** EMITTED rows to witness and range-check ONE carried lane. §3.20 measured
   *  the deployed carry linear at 3.75 rows/lane over a 100× range; the AIR
   *  chain's own model charges 26 rows per 4-lane extension value, i.e. 6.5.
   *  The higher of the two is used, because a cut that fits at 6.5 also fits at
   *  3.75 and the failure mode of the other direction is a circuit that does
   *  not compile. */
  witnessLane: 6.5,
  /** The coset descent `x ← ±x²`. */
  descent: 20,
} as const;

// ===========================================================================
// 2. The shape — the root's PCS rounds, read off the committed proof.
// ===========================================================================

export type MatrixSpec = {
  /** Batch-STARK instance index. */
  instance: number;
  name: string;
  /** `degree_bits + log_blowup`. */
  logHeight: number;
  /** BASE columns committed for this matrix (an extension column is 4). */
  width: number;
  /** Out-of-domain points this matrix is opened at (2 for ζ and g·ζ, 1 for a
   *  quotient chunk). */
  numPoints: number;
};

export type RoundSpec = {
  name: 'main' | 'preprocessed' | 'permutation' | 'quotient';
  matrices: MatrixSpec[];
};

export type FriShape = {
  knobs: FriKnobs;
  rounds: RoundSpec[];
  /** Distinct input-matrix log heights, DESCENDING. The DEEP quotient keys its
   *  accumulator by these and the roll-in schedule is a function of them. */
  heights: number[];
};

/**
 * The root's PCS round structure, derived from the committed proof's own
 * per-instance metadata rather than from a table in a document.
 *
 * ⚑ THE QUOTIENT CHUNKS SIT AT THE TRACE HEIGHT. `TwoAdicFriPcs` commits the
 * quotient over `create_disjoint_domain(1 << (db + log_quotient_degree))` split
 * into `n_chunks` pieces of `2^db` each, so a chunk's committed LDE height is
 * `db + log_blowup` — the same height as the instance's main matrix, which is
 * why no new height appears in the roll-in schedule.
 */
export function rootFriShape(real: RealRootAir, knobs: FriKnobs = DEPLOYED_KNOBS): FriShape {
  const lb = knobs.logBlowup;
  const main: MatrixSpec[] = [];
  const prep: MatrixSpec[] = [];
  const perm: MatrixSpec[] = [];
  const quot: MatrixSpec[] = [];
  for (const i of real.instances) {
    const logHeight = i.degreeBits + lb;
    main.push({ instance: i.index, name: i.table, logHeight, width: i.width, numPoints: 2 });
    if (i.prepWidth > 0)
      prep.push({ instance: i.index, name: i.table, logHeight, width: i.prepWidth, numPoints: 2 });
    if (i.permLocal.length > 0)
      perm.push({
        instance: i.index,
        name: i.table,
        logHeight,
        width: i.permLocal.length * EXT_LANES,
        numPoints: 2,
      });
    for (let c = 0; c < i.nChunks; c++)
      quot.push({
        instance: i.index,
        name: `${i.table}/chunk${c}`,
        logHeight,
        width: EXT_LANES,
        numPoints: 1,
      });
  }
  const rounds: RoundSpec[] = [
    { name: 'main', matrices: main },
    { name: 'preprocessed', matrices: prep },
    { name: 'permutation', matrices: perm },
    { name: 'quotient', matrices: quot },
  ];
  const heights = [...new Set(rounds.flatMap((r) => r.matrices.map((m) => m.logHeight)))].sort(
    (a, b) => b - a,
  );
  const lgmh = heights[0];
  if (lgmh !== knobs.logGlobalMaxHeight)
    throw new Error(
      `the tallest committed matrix is at 2^${lgmh} and the knobs say the global max height is ` +
        `2^${knobs.logGlobalMaxHeight} — one of them is describing a different proof`,
    );
  return { knobs, rounds, heights };
}

/** `(matrix, point, column)` triples in ONE query's `open_input`, by round. */
export function deepTermCensus(shape: FriShape): Record<string, number> & { total: number } {
  const out: any = { total: 0 };
  for (const r of shape.rounds) {
    const n = r.matrices.reduce((a, m) => a + m.width * m.numPoints, 0);
    out[r.name] = n;
    out.total += n;
  }
  return out;
}

// ===========================================================================
// 3. The two lane tables — what a slice may READ, and under which commitment.
// ===========================================================================

/**
 * The AIR chain's column assignment, as a lane index space. This is EXACTLY
 * `colChunks([...base, ...ext])`'s input order: every table's base columns in
 * legend order, then every table's extension columns, four lanes each.
 *
 * A `(round, matrix, point, column)` triple resolves to a lane here when the
 * AIR legend names it, and to the FRI-side table otherwise.
 */
export type AirColumnIndex = {
  /** `label -> global extension-value index` over the concatenated assignment. */
  byLabel: Map<string, number>;
  nBase: number;
  nExt: number;
  /** Per table, the base and ext offsets its legend indices are relative to. */
  tables: { name: string; baseOff: number; extOff: number }[];
};

export function airColumnIndex(): AirColumnIndex {
  const d = rootAirDag();
  const byLabel = new Map<string, number>();
  const tables: AirColumnIndex['tables'] = [];
  let baseOff = 0;
  for (const t of d.tables) {
    tables.push({ name: t.name, baseOff, extOff: 0 });
    t.cols.forEach((l, j) => byLabel.set(`${t.name}|${l}`, baseOff + j));
    baseOff += t.cols.length;
  }
  const nBase = baseOff;
  let extOff = 0;
  d.tables.forEach((t, ti) => {
    tables[ti].extOff = extOff;
    t.extCols.forEach((l, j) => byLabel.set(`${t.name}|${l}`, nBase + extOff + j));
    extOff += t.extCols.length;
  });
  return { byLabel, nBase, nExt: extOff, tables };
}

/** The AIR table names, keyed the way `root-air-dag.json` spells them, from the
 *  instance name the root proof carries. */
export const dagTableName = (instanceName: string): string =>
  instanceName.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_');

/**
 * Where one opened value lives.
 *
 *   * `air` — the AIR chain's assignment holds this exact number, at extension
 *     index `at`. The DEEP quotient reads it from there, and re-deriving
 *     `dagDigest` is what forces the two halves to agree.
 *   * `fri` — the AIR never reads it; it lives in the FRI-side lane table at
 *     extension index `at`, under `friDigest`.
 */
export type OpenedRef = { where: 'air' | 'fri'; at: number };

export type OpenedPlan = {
  /** `refs[round][matrix][point][column]`. */
  refs: OpenedRef[][][][];
  /** How many extension values the FRI-side table holds. */
  nFri: number;
  /** Census. */
  split: { air: number; fri: number; total: number };
};

/**
 * Resolve every opened value against the AIR legend.
 *
 * The legend labels are the contract: `main[0][i]` is main column `i` at ζ,
 * `main[1][i]` the same column at `g·ζ`, `prep[a][j]` likewise, and
 * `perm[a][k]` the `k`-th extension permutation column. An extension
 * permutation column occupies FOUR base lanes in the PCS commitment and ONE
 * extension value in the AIR assignment, so the four consecutive PCS columns
 * `4k .. 4k+3` resolve to the four lanes of AIR extension value `perm[a][k]`.
 */
export function planOpenedValues(shape: FriShape, air: AirColumnIndex): OpenedPlan {
  const refs: OpenedRef[][][][] = [];
  let nFri = 0;
  let nAir = 0;
  for (const r of shape.rounds) {
    const byMat: OpenedRef[][][] = [];
    for (const m of r.matrices) {
      const t = dagTableName(m.name.split('/chunk')[0]);
      const byPt: OpenedRef[][] = [];
      for (let p = 0; p < m.numPoints; p++) {
        const byCol: OpenedRef[] = [];
        for (let c = 0; c < m.width; c++) {
          let label: string | null = null;
          if (r.name === 'main') label = `main[${p}][${c}]`;
          else if (r.name === 'preprocessed') label = `prep[${p}][${c}]`;
          else if (r.name === 'permutation') label = `perm[${p}][${Math.floor(c / EXT_LANES)}]`;
          // The quotient chunks are never in the AIR's assignment.
          const key = label === null ? null : `${t}|${label}`;
          const hit = key === null ? undefined : air.byLabel.get(key);
          if (hit === undefined) {
            byCol.push({ where: 'fri', at: nFri++ });
          } else {
            byCol.push({ where: 'air', at: hit });
            nAir++;
          }
        }
        byPt.push(byCol);
      }
      byMat.push(byPt);
    }
    refs.push(byMat);
  }
  return { refs, nFri, split: { air: nAir, fri: nFri, total: nAir + nFri } };
}

// ===========================================================================
// 4. Slots — the state that crosses a cut.
// ===========================================================================

/**
 * Every value that can be live at a slice boundary, as a flat lane space.
 *
 * ⚑ ONE SLOT SET FOR ALL 19 QUERIES, and that is not an approximation. A
 * query's running Merkle digest, sponge state and fold value are dead the
 * moment its walk ends, so re-using the same slot ids is what LIVENESS is for:
 * the backward pass below kills a slot at the segment that overwrites it, and a
 * boundary inside query 7 carries query 7's fold value and nothing of query 6's.
 */
export type SlotLayout = {
  n: number;
  chal: number[];
  alpha: number[];
  beta: number[][];
  qidx: number[];
  cur: number[];
  sponge: number[];
  dacc: number[][];
  dpow: number[][];
  ro: number[][];
  /** The running Horner accumulator of ONE (matrix, point), which is live only
   *  when that matrix's columns are split across a cut. */
  dh: number[];
  folded: number[];
  x: number;
  names: string[];
};

export function slotLayout(shape: FriShape): SlotLayout {
  const names: string[] = [];
  const take = (label: string, n: number): number[] => {
    const out: number[] = [];
    for (let i = 0; i < n; i++) {
      out.push(names.length);
      names.push(`${label}[${i}]`);
    }
    return out;
  };
  const chal = take('chal', CHAL_WIDTH);
  const alpha = take('alpha', EXT_LANES);
  const beta = Array.from({ length: shape.knobs.layers }, (_, r) => take(`beta${r}`, EXT_LANES));
  const qidx = take('qidx', shape.knobs.numQueries);
  const cur = take('cur', LANES_PER_DIGEST);
  const sponge = take('sponge', CHAL_WIDTH);
  const dacc = shape.heights.map((h) => take(`dacc${h}`, EXT_LANES));
  const dpow = shape.heights.map((h) => take(`dpow${h}`, EXT_LANES));
  const ro = shape.heights.map((h) => take(`ro${h}`, EXT_LANES));
  const dh = take('dh', EXT_LANES);
  const folded = take('folded', EXT_LANES);
  const x = take('x', 1)[0];
  return {
    n: names.length,
    chal,
    alpha,
    beta,
    qidx,
    cur,
    sponge,
    dacc,
    dpow,
    ro,
    dh,
    folded,
    x,
    names,
  };
}

// ===========================================================================
// 5. The segments.
// ===========================================================================

/** A lane of the FRI transcript's absorb schedule. */
export type AbsorbRef =
  | { src: 'commit'; layer: number; lane: number }
  | { src: 'finalPoly'; i: number; lane: number }
  | { src: 'arity' } //  a COMPILE-TIME constant, not proof data
  | { src: 'pow' };

export type SampleRef =
  | { dst: 'alpha'; lane: number }
  | { dst: 'beta'; layer: number; lane: number }
  /** The `query_pow_bits = 16` grind's own sample. It lands in no slot — the
   *  circuit asserts its low 16 bits are zero and drops it — but it CONSUMES an
   *  output-buffer position, and a schedule that skipped it would draw all 19
   *  query indices one position early. */
  | { dst: 'pow' }
  | { dst: 'qidx'; query: number };

export type Segment =
  /** One challenger permutation, with the lanes it absorbed and the challenges
   *  drawn from its output buffer before the next one. */
  | { t: 'duplex'; absorbs: AbsorbRef[]; samples: SampleRef[]; rows: number }
  /** One `PaddingFreeSponge` block over the concatenated opened rows at one
   *  height of one input round. `first` starts the sponge, `last` finishes it
   *  into a digest. */
  | {
      t: 'inBlock';
      q: number;
      round: number;
      height: number;
      block: number;
      lanes: number;
      first: boolean;
      last: boolean;
      /** TRUE when this digest is the round's TALLEST — it seeds `cur`;
       *  otherwise it is compressed in as a mixed-height injection. */
      seeds: boolean;
      rows: number;
    }
  /** One Merkle level of an input-round opening, plus the injection that
   *  follows it when a shorter matrix's height is reached here. */
  | { t: 'inLevel'; q: number; round: number; level: number; inject: number | null; rows: number }
  /** `cur == commitment` for an input round. */
  | { t: 'inRoot'; q: number; round: number; rows: number }
  /** A DEEP-quotient term run: columns `[from, to)` of one (matrix, point).
   *  `open` computes `1/(z − x)` and `close` folds the result into the height's
   *  accumulator and advances `alpha_pow`. */
  | {
      t: 'deep';
      q: number;
      round: number;
      mat: number;
      point: number;
      from: number;
      to: number;
      open: boolean;
      close: boolean;
      rows: number;
    }
  /** The commit-phase row's leaf sponge — exactly one block, 8 lanes. */
  | { t: 'cpLeaf'; q: number; r: number; rows: number }
  | { t: 'cpLevel'; q: number; r: number; level: number; rows: number }
  | { t: 'cpRoot'; q: number; r: number; rows: number }
  /** `fold_row` at β, the coset descent, and the roll-in scheduled here. */
  | { t: 'cpFold'; q: number; r: number; rollIn: number | null; rows: number }
  /** The chain lands on the final polynomial. */
  | { t: 'final'; q: number; rows: number };

export type SegmentedWalk = {
  shape: FriShape;
  slots: SlotLayout;
  segs: Segment[];
  reads: number[][];
  writes: number[][];
  /** `liveIn[k]` — the slots that must cross the boundary BEFORE segment `k`. */
  liveIn: number[][];
  /** Total modelled rows. */
  totalRows: number;
};

const ceilDiv = (a: number, b: number) => Math.ceil(a / b);

/** The concatenated opened-row width at one height of one round. */
export function rowWidthAt(round: RoundSpec, height: number): number {
  return round.matrices.filter((m) => m.logHeight === height).reduce((a, m) => a + m.width, 0);
}

/** The heights present in a round, DESCENDING. */
export function roundHeights(round: RoundSpec): number[] {
  return [...new Set(round.matrices.map((m) => m.logHeight))].sort((a, b) => b - a);
}

/**
 * **THE SEGMENT LIST.** The whole walk, in the order a verifier runs it:
 * the FRI transcript, then per query the input-phase openings, the DEEP
 * quotient, and the fold chain onto the final polynomial.
 */
export function segmentWalk(shape: FriShape, opts: { deepCols?: number } = {}): SegmentedWalk {
  const slots = slotLayout(shape);
  const deepCols = opts.deepCols ?? 128;
  const K = shape.knobs;
  const segs: Segment[] = [];
  const reads: number[][] = [];
  const writes: number[][] = [];
  const push = (s: Segment, rd: number[], wr: number[]) => {
    segs.push(s);
    reads.push(rd);
    writes.push(wr);
  };

  // ---- the FRI transcript -------------------------------------------------
  // The schedule is `verify_fri`'s, simulated so the duplex boundaries — the
  // only places a cut may fall inside the transcript — are compile-time facts.
  {
    let inBuf: AbsorbRef[] = [];
    let outCount = 0;
    let pending: SampleRef[] = [];
    let absorbed: AbsorbRef[] = [];
    const flush = () => {
      push({ t: 'duplex', absorbs: absorbed, samples: pending, rows: PRICE.perm }, [...slots.chal], [
        ...slots.chal,
        ...pending.flatMap(sampleSlots),
      ]);
      absorbed = [];
      pending = [];
    };
    const sampleSlots = (s: SampleRef): number[] => {
      if (s.dst === 'alpha') return [slots.alpha[s.lane]];
      if (s.dst === 'beta') return [slots.beta[s.layer][s.lane]];
      if (s.dst === 'pow') return [];
      return [slots.qidx[s.query]];
    };
    let open = false; //  a duplex has happened and its samples are still open
    const duplex = () => {
      if (open) flush();
      absorbed = inBuf;
      inBuf = [];
      outCount = CHAL_RATE;
      open = true;
    };
    const observe = (a: AbsorbRef) => {
      outCount = 0;
      inBuf.push(a);
      if (inBuf.length === CHAL_RATE) duplex();
    };
    const sample = (dst: SampleRef) => {
      if (inBuf.length > 0 || outCount === 0) duplex();
      outCount--;
      pending.push(dst);
    };
    for (let l = 0; l < EXT_LANES; l++) sample({ dst: 'alpha', lane: l });
    for (let r = 0; r < K.layers; r++) {
      for (let j = 0; j < LANES_PER_DIGEST; j++) observe({ src: 'commit', layer: r, lane: j });
      //  commit_pow_bits = 0: `check_witness` returns BEFORE observing.
      for (let l = 0; l < EXT_LANES; l++) sample({ dst: 'beta', layer: r, lane: l });
    }
    for (let i = 0; i < K.finalPolyLen; i++)
      for (let l = 0; l < EXT_LANES; l++) observe({ src: 'finalPoly', i, lane: l });
    for (let r = 0; r < K.layers; r++) observe({ src: 'arity' });
    //  query_pow_bits = 16: the witness IS observed, and the next sample's low
    //  16 bits are forced to zero. That sample is charged to its duplex.
    observe({ src: 'pow' });
    sample({ dst: 'pow' });
    for (let q = 0; q < K.numQueries; q++) sample({ dst: 'qidx', query: q });
    if (open) flush();
  }

  // ---- the queries --------------------------------------------------------
  const lgmh = K.logGlobalMaxHeight;
  for (let q = 0; q < K.numQueries; q++) {
    const idxSlot = [slots.qidx[q]];

    // -- the input-phase openings, one per PCS round.
    shape.rounds.forEach((round, ri) => {
      const hs = roundHeights(round);
      const top = hs[0];
      // Every height's opened rows are sponged; the tallest seeds `cur`, the
      // rest wait to be injected at the level their height names.
      for (const h of hs) {
        const w = rowWidthAt(round, h);
        const nb = ceilDiv(w, CHAL_RATE);
        for (let b = 0; b < nb; b++) {
          const lanes = Math.min(CHAL_RATE, w - b * CHAL_RATE);
          const first = b === 0;
          const last = b === nb - 1;
          const seeds = h === top;
          push(
            {
              t: 'inBlock',
              q,
              round: ri,
              height: h,
              block: b,
              lanes,
              first,
              last,
              seeds,
              rows: PRICE.perm + lanes * PRICE.witnessLane,
            },
            first ? [] : [...slots.sponge],
            last ? [...slots.cur] : [...slots.sponge],
          );
        }
      }
      // `MerkleTreeMmcs::verify_batch`: `top` levels of compress against the
      // witnessed siblings, with the shorter matrices' digests compressed in at
      // the level whose padded height they match.
      for (let lv = 0; lv < top; lv++) {
        const nextH = top - 1 - lv;
        const inject = hs.includes(nextH) ? nextH : null;
        push(
          {
            t: 'inLevel',
            q,
            round: ri,
            level: lv,
            inject,
            rows: PRICE.merkleLevel + (inject === null ? 0 : PRICE.merkleInject),
          },
          [...slots.cur, ...idxSlot],
          [...slots.cur],
        );
      }
      push({ t: 'inRoot', q, round: ri, rows: 8 }, [...slots.cur], []);
    });

    // -- the DEEP quotient. The accumulator and `alpha_pow` are keyed by
    //    HEIGHT and advance in ENCOUNTER order across rounds, which is the
    //    convention a per-matrix counter gets wrong.
    //
    //    ⚑ THE COLUMN RUN IS SUBDIVIDED, AND IT MUST BE. The widest matrix is
    //    452 columns, which at 49 rows a Horner step plus the range checks on
    //    the opened value is ~34,000 rows — a segment that fits in a step only
    //    if it is alone in one. Horner runs from the TOP column DOWN, so a run
    //    splits cleanly into descending column ranges with the accumulator
    //    crossing in `dh`; `open` seeds it and `close` computes `1/(z − x)` and
    //    folds it into the height's slot.
    shape.rounds.forEach((round, ri) => {
      round.matrices.forEach((m, mi) => {
        const hi = shape.heights.indexOf(m.logHeight);
        for (let p = 0; p < m.numPoints; p++) {
          const cuts: [number, number][] = [];
          for (let hiCol = m.width; hiCol > 0; hiCol -= deepCols)
            cuts.push([Math.max(0, hiCol - deepCols), hiCol]);
          cuts.forEach(([a, b], ci) => {
            const open = ci === 0;
            const close = a === 0;
            push(
              {
                t: 'deep',
                q,
                round: ri,
                mat: mi,
                point: p,
                from: a,
                to: b,
                open,
                close,
                rows:
                  (close ? PRICE.extInverse + 2 * PRICE.extMul + PRICE.extAdd : 0) +
                  (b - a) * (PRICE.horner + EXT_LANES * PRICE.witnessLane),
              },
              [
                ...slots.alpha,
                ...(open ? [] : slots.dh),
                ...(close ? [...slots.dacc[hi], ...slots.dpow[hi]] : []),
                ...idxSlot,
              ],
              close ? [...slots.dacc[hi], ...slots.dpow[hi]] : [...slots.dh],
            );
          });
        }
      });
    });
    // The reduced openings become the chain's `initial` and its roll-ins.
    shape.heights.forEach((h, hi) => {
      push(
        { t: 'deep', q, round: -1, mat: -1, point: -1, from: 0, to: 0, open: false, close: false, rows: 4 },
        [...slots.dacc[hi]],
        [...(hi === 0 ? slots.folded : slots.ro[hi])],
      );
    });

    // -- the fold chain.
    for (let r = 0; r < K.layers; r++) {
      const depth = lgmh - 1 - r;
      push({ t: 'cpLeaf', q, r, rows: PRICE.perm + 8 * PRICE.witnessLane }, [...slots.folded, ...idxSlot], [
        ...slots.cur,
      ]);
      for (let lv = 0; lv < depth; lv++)
        push({ t: 'cpLevel', q, r, level: lv, rows: PRICE.merkleLevel }, [...slots.cur, ...idxSlot], [
          ...slots.cur,
        ]);
      push({ t: 'cpRoot', q, r, rows: 8 }, [...slots.cur], []);
      const rollHeight = shape.heights.indexOf(lgmh - 1 - r);
      const rollIn = rollHeight > 0 ? rollHeight : null;
      push(
        {
          t: 'cpFold',
          q,
          r,
          rollIn,
          rows: PRICE.foldRow + PRICE.descent + (rollIn === null ? 0 : PRICE.rollIn),
        },
        [
          ...slots.folded,
          slots.x,
          ...slots.beta[r],
          ...idxSlot,
          ...(rollIn === null ? [] : slots.ro[rollIn]),
        ],
        [...slots.folded, slots.x],
      );
    }
    push({ t: 'final', q, rows: PRICE.extAdd + 8 }, [...slots.folded, ...idxSlot], []);
  }

  // ---- liveness, backwards ------------------------------------------------
  const liveIn: number[][] = new Array(segs.length + 1);
  let live = new Set<number>();
  liveIn[segs.length] = [];
  for (let k = segs.length - 1; k >= 0; k--) {
    for (const w of writes[k]) live.delete(w);
    for (const r of reads[k]) live.add(r);
    liveIn[k] = [...live].sort((a, b) => a - b);
  }

  return {
    shape,
    slots,
    segs,
    reads,
    writes,
    liveIn,
    totalRows: segs.reduce((a, s) => a + s.rows, 0),
  };
}

// ===========================================================================
// 6. The planner.
// ===========================================================================

export type FriSlice = {
  index: number;
  /** Segments `[from, to)`. */
  from: number;
  to: number;
  /** Slots crossing IN and OUT. */
  liveIn: number[];
  liveOut: number[];
  /** AIR-side and FRI-side column chunks this slice must load. */
  readsAirChunks: number[];
  readsFriChunks: number[];
  workRows: number;
  carryRows: number;
};

export type FriPlan = {
  slices: FriSlice[];
  nAirChunks: number;
  nFriChunks: number;
  chunkSize: number;
  totalWork: number;
  totalCarry: number;
};

/** Which opened values a segment reads, as `(where, extIndex)` pairs. */
export function openedReads(w: SegmentedWalk, plan: OpenedPlan, k: number): OpenedRef[] {
  const s = w.segs[k];
  if (s.t !== 'deep' || s.mat < 0) return [];
  const cols = plan.refs[s.round][s.mat][s.point];
  const out: OpenedRef[] = [];
  for (let c = s.from; c < s.to; c++) out.push(cols[c]);
  return out;
}

/**
 * **THE PLANNER.** Greedy-maximal slices under a row budget, exactly as
 * `planRootAirChain` cuts the AIR: extend while work + carry fits, then cut.
 *
 * The carry is recomputed at every candidate end because it is a function of
 * the CUT rather than of the slice's length — a boundary that falls inside a
 * DEEP run carries five height accumulators and their `alpha_pow`s; one that
 * falls between two queries carries almost nothing but the derived challenges.
 * That spread is the whole reason a boundary here is not a constant, and §3.20
 * measured its two ends at 34,566 and 762 rows.
 */
export function planFriWalk(
  w: SegmentedWalk,
  op: OpenedPlan,
  opts: { usableRows: number; chunkSize: number; maxSlices?: number },
): FriPlan {
  const { chunkSize } = opts;
  const air = airColumnIndex();
  const nAirChunks = Math.ceil((air.nBase + air.nExt) / chunkSize);
  const nFriChunks = Math.max(1, Math.ceil(op.nFri / chunkSize));
  const slices: FriSlice[] = [];
  let from = 0;
  while (from < w.segs.length) {
    let work = 0;
    const airSet = new Set<number>();
    const friSet = new Set<number>();
    let best = -1;
    let bestCarry = 0;
    let bestWork = 0;
    let bestAir: number[] = [];
    let bestFri: number[] = [];
    let to = from;
    while (to < w.segs.length) {
      work += w.segs[to].rows;
      for (const r of openedReads(w, op, to))
        (r.where === 'air' ? airSet : friSet).add(Math.floor(r.at / chunkSize));
      to++;
      const carry =
        (w.liveIn[from].length + w.liveIn[to].length) * PRICE.witnessLane +
        (airSet.size * chunkSize + friSet.size * chunkSize) * EXT_LANES * PRICE.witnessLane +
        (nAirChunks + nFriChunks) * PRICE.witnessLane * EXT_LANES;
      if (work + carry > opts.usableRows) {
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
        `no slice fits at segment ${from} (${w.segs[from].t}, ${Math.round(w.segs[from].rows)} rows) ` +
          `plus its carry, under ${opts.usableRows} rows`,
      );
    slices.push({
      index: slices.length,
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
    if (opts.maxSlices && slices.length >= opts.maxSlices) break;
  }
  return {
    slices,
    nAirChunks,
    nFriChunks,
    chunkSize,
    totalWork: slices.reduce((a, s) => a + s.workRows, 0),
    totalCarry: slices.reduce((a, s) => a + s.carryRows, 0),
  };
}

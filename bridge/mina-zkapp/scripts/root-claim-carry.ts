import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { FeatureFlags, Field, Poseidon, Provable, ZkProgram } from 'o1js';
import {
  DagTable,
  RealInstance,
  RealRootAir,
  bindRealInstance,
  rootAirDag,
} from '../src/RootAirDag.js';
import { digestOfLanes, stepBoundary } from '../src/RootAirChain.js';
import {
  AbsorbRef,
  FriPlan,
  FriShape,
  FriSlice,
  PreambleMeta,
  RealRootFri,
  airColumnIndex,
  friLaneTable,
  planOpenedValues,
  preambleOps,
  rootFriShape,
  rootPreambleMeta,
  segmentWalk,
} from '../src/RootFriWalk.js';
import {
  AIR_CHUNK_LANES,
  airLaneValues,
  auxLanes,
  chunkDigestsBigInt,
  chunkedCommitment,
  friLaneValues,
  runSegments,
  walkTwin,
} from '../src/RootFriSlice.js';
import { dagDigestOfChunkDigests } from '../src/RootAirChain.js';
import {
  UniformLayout,
  UniformPlan,
  assertHomogeneous,
  makeUniformSliceProgram,
  planUniform,
  uniformLaneTable,
  uniformLayout,
} from '../src/RootFriUniform.js';
import {
  ChainClaim,
  ClaimIndex,
  ClaimedBoundary,
  NUM_CHAIN_CLAIMS,
  SEG_ANCHOR_WIDTH,
  SEG_COUNT,
  SEG_DIGEST_FIRST,
  SEG_DIGEST_WIDTH,
  SEG_FIRST_OLD,
  SEG_LAST_NEW,
  assertClaimCarried,
  assertClaimSeal,
  claimBindSlice,
  claimChunks,
  claimIndex,
  claimOfLanes,
  claimOfLanesBigInt,
  laneOfChunks,
  octetBigInt,
  readClaimLanes,
} from '../src/RootClaim.js';

// ---------------------------------------------------------------------------
// LEG 21 — THE CHAIN SAYS WHICH PROOF IT VERIFIED.
//
// §3.29 derived the challenger state and named the last of the three: "the chain
// verifies a proof and never says what the proof claims." Every statement is
// relative to `dagDigest`/`friDigest`, digests of lane tables the PROVER
// supplies; slice 0 enters `stepBoundary(dagDigest, GENESIS_LIVE_DIGEST, 0)`, a
// genesis constant. A Mina-side verifier handed the whole 905-slice chain learns
// "*some* batch of seven AIRs with these column digests verifies".
//
// This is the third instance of ONE disease and the arc has closed the other
// two: the fold chain's `initial` (§3.15, closed by the DEEP quotient binding),
// then the challenger state (§3.29, closed by deriving it from the batch's own
// commitments). Each time: a prover-chosen value feeding everything downstream.
//
// ⚑ AND THE FIX IS ONE RUNG. The claim is ALREADY in the lane table as
// `expose_claim`'s 25 public values — `[digest₈][digest₈][3][digest₈]`, the
// artifact's `numTurns` is 3, and the preamble already absorbs all 25. Closing
// it means carrying those lanes OUT as a public output of the chain.
//
// ⚑ THE DIFFERENTIAL LEADS AND THE CIRCUIT CONFIRMS. Every real defect in this
// arc came from an out-of-circuit twin running in seconds — four silent wrongs
// across 11,303 segments, all 19 block joins broken across 820 boundaries, two
// challenger readings that would have compiled and PROVED cleanly. Six hours of
// injection self-test found nothing. Phase [1] decodes the claim out of circuit
// against three independent oracles and phase [2] requires every plausible
// misreading to decode to something else.
// ---------------------------------------------------------------------------

const PHASE = process.env.CLAIM_PHASE ?? 'all';
const WORK = process.env.CLAIM_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const BUDGET = Number(process.env.CLAIM_BUDGET ?? 50_000);
const CHUNK = Number(process.env.CLAIM_CHUNK ?? 256);

let checks = 0;
const ok = (m: string) => {
  checks++;
  console.log(`  ✓ ${m}`);
};
const fail = (m: string): never => {
  console.error(`\n✗ ${m}`);
  process.exit(1);
};
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');
const hex = (x: bigint) => `0x${x.toString(16).padStart(8, '0').slice(0, 16)}…`;

/** ⚑ EVERY CAUGHT ERROR MUST BE A CONSTRAINT FAILURE. §3.28's rule verbatim, and
 *  §3.29's near-miss is why it is repeated: the first run of that leg's table
 *  "refused" on the bound side and DIED on the control side, both from a padding
 *  bug in the witness builder. A `TypeError` inside a bare `catch {}` is
 *  indistinguishable from a refusal, and that is what makes a splice table a
 *  green that measures the harness. */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read|ENOENT/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|Bool\.assertTrue/i.test(m);
}

// ===========================================================================
// The context.
// ===========================================================================

function readReal(): { air: RealRootAir; fri: RealRootFri } {
  const a = resolve(WORK, 'real-root-air.json');
  const f = resolve(WORK, 'real-root-fri.json');
  //  ⚑ MISSING TOOLCHAIN IS A FAILURE, NOT A SKIP.
  if (!existsSync(a)) fail(`${a} is missing — run \`npm run root-air-fullchain\``);
  if (!existsSync(f))
    fail(
      `${f} is missing — build and run the dumper:\n` +
        '    cargo build -p dregg-circuit-prove --release --bin root_fri_instance\n' +
        `    ./target/release/root_fri_instance ${f}`,
    );
  return { air: JSON.parse(readFileSync(a, 'utf8')), fri: JSON.parse(readFileSync(f, 'utf8')) };
}

function realColumns(real: RealRootAir) {
  const d = rootAirDag();
  const byName: Record<string, RealInstance> = {};
  for (const i of real.instances)
    byName[i.table.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_')] = i;
  const pairs: [DagTable, RealInstance][] = d.tables.map((t) => {
    const i = byName[t.name] ?? byName[t.name.toLowerCase()];
    if (!i) fail(`no real instance for table ${t.name}`);
    return [t, i];
  });
  const base: bigint[][] = [];
  const ext: bigint[][] = [];
  for (const [t, inst] of pairs) {
    const b = bindRealInstance(t, inst);
    base.push(...b.base);
    ext.push(...b.ext);
  }
  return { base, ext, byName };
}

type Ctx = {
  shape: FriShape;
  meta: PreambleMeta;
  w: ReturnType<typeof segmentWalk>;
  op: ReturnType<typeof planOpenedValues>;
  ft: ReturnType<typeof friLaneTable>;
  L: UniformLayout;
  plan: UniformPlan;
  airLanes: bigint[];
  friLanes: bigint[];
  twin: ReturnType<typeof walkTwin>;
  realAir: RealRootAir;
  realFri: RealRootFri;
  ix: ClaimIndex;
  chunks: number[];
  bindPos: number;
};

function context(): Ctx {
  const { air: realAir, fri: realFri } = readReal();
  const shape = rootFriShape(realFri);
  const air = airColumnIndex();
  const meta = rootPreambleMeta(realAir, air);
  //  ⚑ ONE `OpenedPlan` PER LANE TABLE. `friLaneTable` MUTATES `op.refs` in
  //  place (it re-points the fri refs at absolute lanes), so a second lane table
  //  built from the same plan double-applies the offset — and it surfaces as
  //  `assertHomogeneous` failing at a query-block position for a reason that has
  //  nothing to do with what changed. §3.29 measured this on its first run.
  const op = planOpenedValues(shape, air);
  //  ⚑ WITH the preamble: 905 instances / 131 programs is the §3.29 shape, and
  //  a plan built without it is the 820/46 one.
  const w = segmentWalk(shape, { preamble: meta });
  const ftD = friLaneTable(shape, op);
  const L = uniformLayout(w, shape, ftD, CHUNK);
  const ft = uniformLaneTable(shape, ftD, L);
  assertHomogeneous(w, op, ft, L);
  const plan = planUniform(w, op, ft, L, { usableRows: BUDGET });

  const cols = realColumns(realAir);
  const airLanes = airLaneValues(cols.base, cols.ext);
  const friLanes = friLaneValues(realFri, shape, ft, op);
  const twin = walkTwin(w, shape, ft, op, friLanes, airLanes, realFri);

  const ix = claimIndex(air);
  const chunks = claimChunks(ix, CHUNK);
  const bindPos = claimBindSlice(plan.head, chunks);
  if (bindPos < 0)
    fail(
      `no head slice loads every AIR chunk the claim lives in (${chunks}) — the seal would have to ` +
        'add a chunk to a slice, which moves the planner\'s carry and therefore the 905',
    );
  return { shape, meta, w, op, ft, L, plan, airLanes, friLanes, twin, realAir, realFri, ix, chunks, bindPos };
}

// ===========================================================================
// [1] THE DIFFERENTIAL — the claim, decoded out of circuit against three
//     independent oracles.
// ===========================================================================

function differential(c: Ctx) {
  console.log('\n[1] THE DIFFERENTIAL — the claim decoded out of circuit\n');
  const ec = c.realAir.instances.find((i) => i.table === 'expose_claim');
  if (!ec) fail('the root proof carries no `expose_claim` instance — there is no claim to carry out');

  console.log(
    `    AIR extension indices ${c.ix.at[0]}..${c.ix.at[NUM_CHAIN_CLAIMS - 1]} ` +
      `(stride ${c.ix.at[1] - c.ix.at[0]}), lanes ${c.ix.lanes[0]}..${c.ix.lanes[NUM_CHAIN_CLAIMS - 1]}, ` +
      `AIR chunks [${c.chunks}]`,
  );

  //  ORACLE 1 — the dumped instance's own `public_values` vector.
  const lanes = c.ix.lanes.map((g) => c.airLanes[g]);
  if (lanes.length !== ec!.publicValues.length)
    fail(`the legend names ${lanes.length} public values and the proof carries ${ec!.publicValues.length}`);
  for (let i = 0; i < lanes.length; i++)
    if (lanes[i] !== BigInt(ec!.publicValues[i]))
      fail(`claim lane ${i}: the AIR assignment holds ${lanes[i]} and the proof's public value is ${ec!.publicValues[i]}`);
  ok(`all ${lanes.length} claim lanes = the root proof's own \`expose_claim\` public values`);

  //  ⚑ A PUBLIC VALUE IS A BASE ELEMENT, AND THE OTHER THREE LANES SAY SO. If
  //  the assignment carried a non-zero X-coefficient then reading lane `4·at`
  //  alone would be dropping data — and `verify_batch` absorbs it as a base
  //  element, so the transcript would be absorbing something the claim is not.
  for (let i = 0; i < c.ix.at.length; i++)
    for (let l = 1; l < 4; l++)
      if (c.airLanes[c.ix.at[i] * 4 + l] !== 0n)
        fail(`claim lane ${i}: extension limb ${l} is ${c.airLanes[c.ix.at[i] * 4 + l]}, not zero — a public value is a BASE element`);
  ok('every claim value is a BASE element — limbs 1..3 are zero in all 25');

  const LANE_MAX = (1n << 31n) - 1n;
  for (let i = 0; i < lanes.length; i++)
    if (lanes[i] < 0n || lanes[i] > LANE_MAX) fail(`claim lane ${i} = ${lanes[i]} is not canonical`);
  ok('all 25 lanes are canonical (< 2^31) — the octet packing is injective');

  //  ORACLE 2 — the artifact's own `numTurns`, recorded independently of the
  //  column assignment.
  const claim = claimOfLanesBigInt(lanes);
  console.log(`    genesisRoot  ${hex(claim.genesisRoot)}   (lanes ${SEG_FIRST_OLD}..${SEG_FIRST_OLD + SEG_ANCHOR_WIDTH - 1})`);
  console.log(`    finalRoot    ${hex(claim.finalRoot)}   (lanes ${SEG_LAST_NEW}..${SEG_LAST_NEW + SEG_ANCHOR_WIDTH - 1})`);
  console.log(`    numTurns     ${claim.numTurns}                    (lane ${SEG_COUNT})`);
  console.log(`    chainDigest  ${hex(claim.chainDigest)}   (lanes ${SEG_DIGEST_FIRST}..${SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH - 1})`);
  if (c.realAir.numTurns === undefined)
    fail('the artifact does not record `numTurns` — the decode has no independent oracle');
  if (claim.numTurns !== BigInt(c.realAir.numTurns))
    fail(`the claim's lane ${SEG_COUNT} decodes to ${claim.numTurns} and the artifact records numTurns = ${c.realAir.numTurns}`);
  ok(`\`numTurns\` decodes to ${claim.numTurns} = the artifact's own \`numTurns\` — an oracle OUTSIDE the assignment`);

  //  ORACLE 3 — the preamble's own absorb set. If the transcript absorbed a
  //  different set of public values then the claim is not the thing the seal
  //  pins, and bending it would NOT move ζ.
  const absorbed = new Set<number>();
  for (const o of preambleOps(c.shape, c.meta))
    if (o.t === 'observe' && (o.a as AbsorbRef & { src: 'publicValue' }).src === 'publicValue')
      absorbed.add((o.a as any).at as number);
  if (absorbed.size !== NUM_CHAIN_CLAIMS)
    fail(`the preamble absorbs ${absorbed.size} public values and the claim is ${NUM_CHAIN_CLAIMS} lanes`);
  for (const g of c.ix.at)
    if (!absorbed.has(g)) fail(`the preamble does NOT absorb AIR index ${g} — a claim lane outside the transcript`);
  ok('the preamble absorbs EXACTLY these 25 — bending one moves ζ and §3.29\'s seal refuses');

  //  The round trip: packing is a bijection on canonical lanes, checked rather
  //  than asserted.
  const unpack = (f: bigint) => Array.from({ length: 8 }, (_, j) => (f >> (31n * BigInt(j))) & ((1n << 31n) - 1n));
  const rt = [
    ...unpack(claim.genesisRoot),
    ...unpack(claim.finalRoot),
    claim.numTurns,
    ...unpack(claim.chainDigest),
  ];
  if (rt.length !== lanes.length || rt.some((v, i) => v !== lanes[i]))
    fail('the packed claim does not unpack to the lanes it was packed from');
  ok('the 4-field packing round-trips to all 25 lanes — a verifier reads the claim, it does not recompute it');

  //  ⚑ THE TWO NUMBERINGS. `laneOfChunks` repeats `runSegments`'s own chunk
  //  arithmetic, and two numberings of one table is the shape that drifts
  //  (`assertPreambleSealLanes` exists for exactly this). Checked here, before
  //  anything compiles.
  const sl = c.plan.head[c.bindPos];
  const loaded: bigint[] = [];
  for (const ch of sl.readsAirChunks) for (let i = 0; i < CHUNK; i++) loaded.push(c.airLanes[ch * CHUNK + i] ?? 0n);
  for (let i = 0; i < c.ix.lanes.length; i++) {
    const via = laneOfChunks(sl.readsAirChunks, CHUNK, loaded, c.ix.lanes[i]);
    if (via !== lanes[i])
      fail(`the chunk accessor resolves claim lane ${i} to ${via} and the flat table says ${lanes[i]}`);
  }
  ok(`the chunk accessor and the flat lane table agree on all 25 (head slice ${c.bindPos})`);

  console.log(
    `\n    the seal lands on HEAD SLICE ${c.bindPos} — segments [${sl.from}, ${sl.to}), AIR chunks ` +
      `[${sl.readsAirChunks}] ⊇ [${c.chunks}]`,
  );
  ok('the binding slice loads the claim chunks ALREADY — zero extra chunk loads, so the plan does not move');
  return { lanes, claim };
}

// ===========================================================================
// [2] THE DISCRIMINATING POLARITIES.
// ===========================================================================

type Decoded = { genesisRoot: bigint; finalRoot: bigint; numTurns: bigint; chainDigest: bigint } | null;
type Variant = { name: string; f: (c: Ctx) => Decoded };

const eqC = (a: Decoded, b: Decoded) =>
  a !== null &&
  b !== null &&
  a.genesisRoot === b.genesisRoot &&
  a.finalRoot === b.finalRoot &&
  a.numTurns === b.numTurns &&
  a.chainDigest === b.chainDigest;

/** Every one of these is a reading a careful person could arrive at, and the
 *  table fails if ANY of them decodes to the same claim — a layout that survives
 *  only because nobody tried to falsify it is not a finding. */
const VARIANTS: Variant[] = [
  {
    //  The single most plausible error in the whole layout: the AIR legend's
    //  index is an EXTENSION index and the table is lane-major, so a claim lane
    //  is `4·at` and not `at`. Both resolve, both are in range, and the wrong
    //  one reads 25 real numbers out of the middle of somebody else's columns.
    name: 'the AIR index read as a LANE index, not an EXTENSION index (`at`, not `4·at`)',
    f: (c) => claimOfLanesBigInt(c.ix.at.map((g) => c.airLanes[g])),
  },
  {
    //  ⚑ A HISTORICALLY REAL SHAPE, NOT AN INVENTED ONE. `SEG_ANCHOR_WIDTH` was
    //  4 lanes (~62-bit birthday) before the FAITHFUL-FLOOR lift widened it to 8
    //  (`ivc_turn_chain.rs:268-278`). Anyone working from the pre-lift record
    //  reads `[old4][new4][count][acc…]` and gets a claim out of it.
    name: 'the PRE-LIFT anchor width — 4-lane state anchors, not 8',
    f: (c) => {
      const l = c.ix.lanes.map((g) => c.airLanes[g]);
      const pad4 = (x: bigint[]) => octetBigInt([...x, 0n, 0n, 0n, 0n]);
      return {
        genesisRoot: pad4(l.slice(0, 4)),
        finalRoot: pad4(l.slice(4, 8)),
        numTurns: l[8],
        chainDigest: octetBigInt(l.slice(9, 17)),
      };
    },
  },
  {
    //  The 25 public columns are NOT contiguous in the legend — measured at
    //  stride 3, interleaved with `prep[]` and `main[]`. Assuming contiguity is
    //  a reading that resolves, decodes and is wrong.
    name: 'the 25 public columns as CONTIGUOUS extension indices',
    f: (c) => claimOfLanesBigInt(Array.from({ length: NUM_CHAIN_CLAIMS }, (_, i) => c.airLanes[(c.ix.at[0] + i) * 4])),
  },
  {
    name: '`count` LAST — `[old8][new8][acc8][count]` rather than `[old8][new8][count][acc8]`',
    f: (c) => {
      const l = c.ix.lanes.map((g) => c.airLanes[g]);
      return {
        genesisRoot: octetBigInt(l.slice(0, 8)),
        finalRoot: octetBigInt(l.slice(8, 16)),
        numTurns: l[24],
        chainDigest: octetBigInt(l.slice(16, 24)),
      };
    },
  },
  {
    name: 'the two state anchors SWAPPED — `last_new8` first',
    f: (c) => {
      const l = c.ix.lanes.map((g) => c.airLanes[g]);
      return {
        genesisRoot: octetBigInt(l.slice(8, 16)),
        finalRoot: octetBigInt(l.slice(0, 8)),
        numTurns: l[16],
        chainDigest: octetBigInt(l.slice(17, 25)),
      };
    },
  },
  {
    name: 'POSITIONAL packing — `packLanes` over the flat 25, not per named block',
    f: (c) => {
      const l = c.ix.lanes.map((g) => c.airLanes[g]);
      return {
        genesisRoot: octetBigInt(l.slice(0, 8)),
        finalRoot: octetBigInt(l.slice(8, 16)),
        //  the third positional field straddles `count` and seven digest lanes
        numTurns: octetBigInt(l.slice(16, 24)),
        chainDigest: l[24],
      };
    },
  },
  {
    name: 'an octet packed MOST-significant lane first',
    f: (c) => {
      const l = c.ix.lanes.map((g) => c.airLanes[g]);
      const rev = (x: bigint[]) => octetBigInt([...x].reverse());
      return {
        genesisRoot: rev(l.slice(0, 8)),
        finalRoot: rev(l.slice(8, 16)),
        numTurns: l[16],
        chainDigest: rev(l.slice(17, 25)),
      };
    },
  },
  {
    //  `Public` is a different table with a `public[]`-shaped name and ZERO
    //  public values. A reading that goes there must not resolve at all.
    name: 'the claim read off the `Public` table instead of `expose_claim`',
    f: () => {
      const air = airColumnIndex();
      const at: number[] = [];
      for (let i = 0; i < NUM_CHAIN_CLAIMS; i++) {
        const g = air.byLabel.get(`Public|public[${i}]`);
        if (g === undefined) return null;
        at.push(g);
      }
      return claimOfLanesBigInt(at.map(() => 0n));
    },
  },
];

/** ⚑ THE WHOLE CLAIM, NOT ONE FIELD OF IT. Two of these misreadings leave
 *  `numTurns` at 3 and move only the octets, so a table keyed on `numTurns`
 *  would show them as identical and the reader would have to trust the verdict
 *  column. Every row is signed on all four fields. */
const sig = (d: Decoded) =>
  d === null
    ? 'unresolved'
    : `turns ${String(d.numTurns).slice(0, 10).padEnd(10)} final …${(d.finalRoot % 100000000n)
        .toString()
        .padStart(8, '0')}`;

function polarities(c: Ctx, ref: Decoded) {
  console.log('\n[2] THE DISCRIMINATING POLARITIES — every plausible misreading must decode elsewhere\n');
  console.log(`    ${'THE READING THIS LEG TAKES'.padEnd(72)} ——     ${sig(ref)}`);
  let same = 0;
  for (const v of VARIANTS) {
    let got: Decoded = null;
    let threw = '';
    try {
      got = v.f(c);
    } catch (e) {
      threw = String((e as Error).message).slice(0, 60);
    }
    const s = eqC(got, ref);
    if (s) same++;
    console.log(
      `    ${v.name.padEnd(72)} ${s ? 'SAME ' : 'diff '}  ${threw ? `threw: ${threw}` : sig(got)}`,
    );
  }
  if (same > 0)
    fail(`${same} misreading(s) decode to the SAME claim — the layout is not pinned by this table`);
  ok(`all ${VARIANTS.length} misreadings decode to a different claim (or do not resolve at all)`);
}

// ===========================================================================
// [3] THE COST — what the claim adds to 905 / 131 / 42,245,547.
// ===========================================================================

function cost(c: Ctx) {
  console.log('\n[3] THE COST — against the §3.29 shape\n');
  const p = c.plan;
  console.log(
    `    the plan is UNCHANGED: head ${p.head.length} slices, block ${p.block.length} × ` +
      `${p.layout.numQueries} ⇒ ${fmt(p.totalSlices)} INSTANCES from ${p.distinctPrograms} PROGRAMS, ` +
      `${fmt(p.totalWork + p.totalCarry)} modelled rows`,
  );
  ok('the claim adds no segment, no slice and no chunk load — the walk and the cut points are §3.29\'s');
  const seals = 1;
  const carries = p.totalSlices - 1;
  console.log(
    `    the claim carry: ${fmt(carries)} slices propagate (4 equalities each), ` +
      `${seals} slice SEALS (25 range checks + 3 packings + 4 equalities)`,
  );
  return { seals, carries };
}

// ===========================================================================
// [4] THE CIRCUIT — the emitted-row price, measured, bound against unbound.
// ===========================================================================

type Mode = 'none' | 'carry' | 'seal' | 'unsealed';

/** A slice's private-input widths under the FLAT FRI commitment this probe uses.
 *  ⚑ The probe measures the CLAIM's delta with everything else held fixed, so
 *  the FRI-side digest shape is irrelevant to it and the simpler one is used;
 *  the deployed two-level commitment is measured in `[4b]` on the real program. */
function probeShape(c: Ctx, sl: FriSlice) {
  let aux = 0;
  for (let k = sl.from; k < sl.to; k++) aux += auxLanes(c.w.segs[k], c.w.hash);
  return {
    nLiveIn: c.w.liveIn[sl.from].length,
    nAirRead: sl.readsAirChunks.length * CHUNK,
    nAirOther: Math.ceil(c.airLanes.length / CHUNK) - sl.readsAirChunks.length,
    nFriRead: sl.readsFriChunks.length * CHUNK,
    nFriOther: c.L.nFriChunks - sl.readsFriChunks.length,
    nAux: aux,
  };
}

function probePlan(c: Ctx, sl: FriSlice): FriPlan {
  return {
    slices: [sl],
    nAirChunks: Math.ceil(c.airLanes.length / CHUNK),
    nFriChunks: c.L.nFriChunks,
    chunkSize: CHUNK,
    totalWork: 0,
    totalCarry: 0,
  };
}

/**
 * ONE slice, standalone — the boundary, the walk, and the claim. It is the
 * deployed body minus the side-loaded predecessor, which is what lets the four
 * variants be built and measured in ONE process (a `DynamicProof` class is
 * process-global and carries ONE public-output type, so `none` and `seal` could
 * not otherwise share a run).
 */
function probeProgram(c: Ctx, sl: FriSlice, mode: Mode, tag: string) {
  const sh = probeShape(c, sl);
  const rp = probePlan(c, sl);
  const arr = (n: number) => Provable.Array(Field, Math.max(n, 1));
  const carrying = mode !== 'none';
  const priv: any[] = [
    arr(sh.nLiveIn),
    arr(sh.nAirRead),
    arr(sh.nAirOther),
    arr(sh.nFriRead),
    arr(sh.nFriOther),
    arr(sh.nAux),
  ];
  if (carrying) priv.push(ChainClaim, ChainClaim);
  return ZkProgram({
    name: `dregg-root-claim-${tag}-${mode}`,
    publicInput: Field,
    publicOutput: (carrying ? ClaimedBoundary : Field) as any,
    methods: {
      slice: {
        privateInputs: priv as any,
        async method(
          bIn: Field,
          liveIn: Field[],
          airLanes: Field[],
          airOther: Field[],
          friLanes: Field[],
          friOther: Field[],
          aux: Field[],
          claimIn?: ChainClaim,
          prevClaim?: ChainClaim,
        ) {
          const dagDigest = chunkedCommitment(
            rp.nAirChunks,
            CHUNK,
            sl.readsAirChunks,
            airLanes.slice(0, sh.nAirRead),
            airOther.slice(0, sh.nAirOther),
          );
          const friDigest = chunkedCommitment(
            rp.nFriChunks,
            CHUNK,
            sl.readsFriChunks,
            friLanes.slice(0, sh.nFriRead),
            friOther.slice(0, sh.nFriOther),
          );
          const friCommit = Poseidon.hash([dagDigest, friDigest]);
          friCommit.assertEquals(bIn);
          if (carrying) assertClaimCarried(prevClaim!, claimIn!);
          if (mode === 'seal' || mode === 'unsealed')
            assertClaimSeal(
              claimIn!,
              claimOfLanes(
                readClaimLanes(c.ix, sl.readsAirChunks, CHUNK, airLanes.slice(0, sh.nAirRead)),
              ),
              mode === 'seal',
            );
          const sto = new Map<number, Field>();
          c.w.liveIn[sl.from].forEach((slot, i) => sto.set(slot, liveIn[i]));
          runSegments(c.w, c.shape, c.ft, c.op, rp, 0, sto, {
            airLanes: airLanes.slice(0, sh.nAirRead),
            airOther: airOther.slice(0, sh.nAirOther),
            friLanes: friLanes.slice(0, sh.nFriRead),
            friOther: friOther.slice(0, sh.nFriOther),
            aux: aux.slice(0, sh.nAux),
          });
          const boundary = stepBoundary(
            friCommit,
            digestOfLanes(c.w.liveIn[sl.to].map((s) => sto.get(s)!)),
            sl.index + 1,
          );
          return {
            publicOutput: carrying ? new ClaimedBoundary({ boundary, claim: claimIn! }) : boundary,
          };
        },
      },
    },
  });
}

async function rowsOf(c: Ctx, sl: FriSlice, mode: Mode, tag: string) {
  const prog = probeProgram(c, sl, mode, tag);
  const meta = (await (prog as any).analyzeMethods()) as any;
  return meta.slice.rows as number;
}

async function circuit(c: Ctx) {
  console.log('\n[4] THE CIRCUIT — the emitted-row price of the claim\n');
  const bind = c.plan.head[c.bindPos];
  //  A slice that only PROPAGATES: the next head slice, which reads no claim
  //  lane at all.
  const propPos = c.plan.head.findIndex(
    (s, i) => i !== c.bindPos && !c.chunks.every((ch) => s.readsAirChunks.includes(ch)),
  );
  if (propPos < 0) fail('every head slice loads the claim chunks — there is no propagating slice to price');
  const prop = c.plan.head[propPos];

  const out: Record<string, number> = {};
  for (const [tag, sl, modes] of [
    ['bind', bind, ['none', 'seal', 'unsealed'] as Mode[]],
    ['prop', prop, ['none', 'carry'] as Mode[]],
  ] as [string, FriSlice, Mode[]][]) {
    for (const m of modes) {
      const t = Date.now();
      out[`${tag}.${m}`] = await rowsOf(c, sl, m, tag);
      console.log(
        `    ${tag} slice ${tag === 'bind' ? c.bindPos : propPos} [${sl.from}, ${sl.to})  ` +
          `${m.padEnd(9)} ${fmt(out[`${tag}.${m}`]).padStart(8)} EMITTED rows  ` +
          `${((Date.now() - t) / 1000).toFixed(1)}s`,
      );
    }
  }
  const dSeal = out['bind.seal'] - out['bind.none'];
  const dUnsealed = out['bind.unsealed'] - out['bind.none'];
  const dCarry = out['prop.carry'] - out['prop.none'];
  console.log(
    `\n    ⇒ the SEAL costs   +${fmt(dSeal)} rows on one slice (of which +${fmt(dUnsealed)} is the read,\n` +
      `      the packing and the carry, and +${fmt(dSeal - dUnsealed)} is the four closing equalities)\n` +
      `    ⇒ the CARRY costs  +${fmt(dCarry)} rows on a slice that only propagates`,
  );
  if (dSeal <= dUnsealed)
    fail(
      `the sealed slice costs ${fmt(dSeal)} and the unsealed control ${fmt(dUnsealed)} — a seal that ` +
        'emits no more rows than its control is not being emitted',
    );
  ok('the armed seal emits MORE rows than the unsealed control — the equalities are in the circuit');

  const total = dSeal + dCarry * (c.plan.totalSlices - 1);
  const base = c.plan.totalWork + c.plan.totalCarry;
  console.log(
    `\n    ⇒ the whole chain: +${fmt(dSeal)} once + ${fmt(dCarry)} × ${fmt(c.plan.totalSlices - 1)} = ` +
      `+${fmt(total)} rows on ${fmt(base)} — ${((total / base) * 100).toFixed(4)}%`,
  );
  //  ⚑ ZERO IS NOT "NOT THERE", AND THIS IS EXACTLY THE PLACE THAT MISREADS. An
  //  equality between two WITNESS variables compiles to a Kimchi COPY
  //  CONSTRAINT: the permutation argument enforces it and no gate row is
  //  emitted. So the carry is free AND enforced, and the row count is silent
  //  about which. §3.29's own note — "row count is the only signal for derived,
  //  not witnessed" — does not transfer here, and phase [5]'s CARRY row is what
  //  says the equality bites.
  if (dCarry === 0)
    console.log(
      '    ⚑ THE CARRY IS FREE IN ROWS AND THAT IS NOT AN ABSENCE. An equality between two witness\n' +
        '      variables is a Kimchi COPY CONSTRAINT — enforced by the permutation argument, no gate\n' +
        '      row. The row count therefore CANNOT witness the carry, and [5]\'s CARRY row is the only\n' +
        '      thing in this leg that does.',
    );
  console.log(
    `    ⚑ Instances and programs are UNCHANGED at ${fmt(c.plan.totalSlices)} / ${c.plan.distinctPrograms}: the\n` +
      '      claim adds no segment, no slice and no chunk load, so the cut points are §3.29\'s.',
  );
  return { dSeal, dUnsealed, dCarry, total, base };
}

// ===========================================================================
// [4b] THE DEPLOYED PROGRAM — the real uniform slice, with the claim in its
//      public output.
// ===========================================================================

async function deployed(c: Ctx) {
  const sp = { kind: 'head', pos: c.bindPos } as const;
  const { prog } = makeUniformSliceProgram(
    { w: c.w, shape: c.shape, ft: c.ft, op: c.op, plan: c.plan, real: c.realFri },
    sp,
    {
      prevFlags: FeatureFlags.allMaybe,
      claim: { ix: c.ix, seals: true, armed: true },
    },
  );
  const meta = (await (prog as any).analyzeMethods()) as any;
  console.log(`    ${(prog as any).name}: ${fmt(meta.slice.rows)} EMITTED rows`);
  return meta.slice.rows as number;
}

// ===========================================================================
// [5] THE FORGERY — a chain whose public output claims a different proof.
// ===========================================================================

/**
 * ⚑ THE LANE TABLE IS UNTOUCHED, AND THAT IS THE WHOLE POINT. Bending an
 * `expose_claim` lane moves ζ and §3.29's preamble seal refuses — that hole is
 * already closed. This forgery keeps every committed lane exactly as dregg
 * emitted it, so every Merkle root, every DEEP quotient, every fold and the
 * preamble seal itself still pass, and lies only about WHAT THE PROOF IS OF.
 * Today that is not even a lie, because the chain says nothing.
 */
function forge(real: ChainClaim): ChainClaim {
  return new ChainClaim({
    genesisRoot: real.genesisRoot,
    //  a different chain head …
    finalRoot: real.finalRoot.add(1),
    //  … reached in a different number of turns.
    numTurns: real.numTurns.add(1),
    chainDigest: real.chainDigest,
  });
}

function witnessOf(c: Ctx, sl: FriSlice) {
  const sh = probeShape(c, sl);
  const rp = probePlan(c, sl);
  const pad = (a: Field[], n: number) => (a.length ? a : [Field(0)]).slice(0, Math.max(n, 1));
  const airRead: Field[] = [];
  for (const ch of sl.readsAirChunks)
    for (let i = 0; i < CHUNK; i++) airRead.push(Field(c.airLanes[ch * CHUNK + i] ?? 0n));
  const airOther: Field[] = [];
  for (let ch = 0; ch < rp.nAirChunks; ch++)
    if (!sl.readsAirChunks.includes(ch))
      airOther.push(digestOfLanes(c.airLanes.slice(ch * CHUNK, (ch + 1) * CHUNK).map((x) => Field(x))));
  const friRead: Field[] = [];
  for (const ch of sl.readsFriChunks)
    for (let i = 0; i < CHUNK; i++) friRead.push(Field(c.friLanes[ch * CHUNK + i] ?? 0n));
  const friOther: Field[] = [];
  for (let ch = 0; ch < rp.nFriChunks; ch++)
    if (!sl.readsFriChunks.includes(ch))
      friOther.push(digestOfLanes(c.friLanes.slice(ch * CHUNK, (ch + 1) * CHUNK).map((x) => Field(x))));
  const aux: Field[] = [];
  for (let k = sl.from; k < sl.to; k++) for (const v of c.twin.aux[k]) aux.push(Field(v));
  const dag = dagDigestOfChunkDigests(chunkDigestsBigInt(c.airLanes, rp.nAirChunks, CHUNK));
  const fri = dagDigestOfChunkDigests(chunkDigestsBigInt(c.friLanes, rp.nFriChunks, CHUNK));
  return {
    bIn: Poseidon.hash([dag, fri]),
    liveIn: pad(c.twin.carry[sl.from].map(Field), sh.nLiveIn),
    airRead: pad(airRead, sh.nAirRead),
    airOther: pad(airOther, sh.nAirOther),
    friRead: pad(friRead, sh.nFriRead),
    friOther: pad(friOther, sh.nFriOther),
    aux: pad(aux, sh.nAux),
    sh,
    rp,
  };
}

/** Run the binding slice's body in circuit, exactly as `probeProgram` builds it,
 *  and report whether it accepted — and, when it did, the public output a
 *  Mina-side verifier would read.
 *
 *  ⚑ `prevClaim` IS A SEPARATE WITNESS AND THAT IS THE POINT. The first version
 *  of this harness called `assertClaimCarried(claimIn, claimIn)` — the claim
 *  against ITSELF — which is a tautology that passes for every input and would
 *  have reported the carry as gated while nothing gated it. */
async function runSlice(
  c: Ctx,
  sl: FriSlice,
  mode: Mode,
  claim: ChainClaim | null,
  prevClaim: ChainClaim | null = claim,
): Promise<{ accepted: boolean; why: string; out: string }> {
  const wit = witnessOf(c, sl);
  let accepted = true;
  let why = '';
  let out = '';
  try {
    await Provable.runAndCheck(async () => {
      //  ⚑ SLICED TO THE REAL WIDTHS, NOT THE PADDED ONES. §3.29's table
      //  "refused" on the bound side and DIED on the control side because the
      //  padding `witnessOf` adds (o1js has no zero-length `Provable.Array`) was
      //  handed to `runSegments`, whose aux-length check then threw a HARNESS
      //  error that reads exactly like a refusal.
      const airLanes = wit.airRead.slice(0, wit.sh.nAirRead).map((v) => Provable.witness(Field, () => v));
      const friLanes = wit.friRead.slice(0, wit.sh.nFriRead).map((v) => Provable.witness(Field, () => v));
      const dagDigest = chunkedCommitment(
        wit.rp.nAirChunks,
        CHUNK,
        sl.readsAirChunks,
        airLanes,
        wit.airOther.slice(0, wit.sh.nAirOther),
      );
      const friDigest = chunkedCommitment(
        wit.rp.nFriChunks,
        CHUNK,
        sl.readsFriChunks,
        friLanes,
        wit.friOther.slice(0, wit.sh.nFriOther),
      );
      const friCommit = Poseidon.hash([dagDigest, friDigest]);
      friCommit.assertEquals(wit.bIn);
      const claimIn = claim === null ? null : Provable.witness(ChainClaim, () => claim);
      const prevIn = prevClaim === null ? null : Provable.witness(ChainClaim, () => prevClaim);
      if (claimIn !== null) assertClaimCarried(prevIn!, claimIn);
      if (mode === 'seal' || mode === 'unsealed')
        assertClaimSeal(
          claimIn!,
          claimOfLanes(readClaimLanes(c.ix, sl.readsAirChunks, CHUNK, airLanes)),
          mode === 'seal',
        );
      const sto = new Map<number, Field>();
      c.w.liveIn[sl.from].forEach((slot, i) =>
        sto.set(slot, Provable.witness(Field, () => wit.liveIn[i])),
      );
      runSegments(c.w, c.shape, c.ft, c.op, wit.rp, 0, sto, {
        airLanes,
        airOther: wit.airOther.slice(0, wit.sh.nAirOther),
        friLanes,
        friOther: wit.friOther.slice(0, wit.sh.nFriOther),
        aux: wit.aux.slice(0, wit.sh.nAux).map((v) => Provable.witness(Field, () => v)),
      });
      const boundary = stepBoundary(
        friCommit,
        digestOfLanes(c.w.liveIn[sl.to].map((s) => sto.get(s)!)),
        sl.index + 1,
      );
      //  What the chain HANDS ON — the thing a Mina-side verifier reads.
      //  ⚑ INSIDE `asProver`. `toString()` on a variable field element throws in
      //  provable code, and that throw is a HARNESS error that `isConstraintFailure`
      //  would have to reject — the run would die on the CONTROL rows and read
      //  like the table found something.
      Provable.asProver(() => {
        out =
          claimIn === null
            ? boundary.toBigInt().toString()
            : [boundary, claimIn.genesisRoot, claimIn.finalRoot, claimIn.numTurns, claimIn.chainDigest]
                .map((f) => f.toBigInt().toString())
                .join('|');
      });
    });
  } catch (e) {
    accepted = false;
    why = String((e as Error).message).split('\n')[0].slice(0, 110);
    if (!isConstraintFailure(e))
      fail(`a row of the table failed with a HARNESS error, not a constraint failure: ${why}`);
  }
  return { accepted, why, out };
}

async function forgery(c: Ctx, realLanes: bigint[]) {
  console.log('\n[5] THE FORGERY — a chain whose public output claims a DIFFERENT proof\n');
  const sl = c.plan.head[c.bindPos];
  const realClaim = claimOfLanes(realLanes.map((x) => Field(x)));
  const bad = forge(realClaim);
  //  ⚑ THE TAIL, NOT THE HEAD. A packed octet is `Σ laneⱼ·2^31ʲ`, so `+1` moves
  //  lane 0 and therefore the LOW digits; printing the first 22 characters shows
  //  two identical-looking numbers and reads as a no-op forgery.
  const tail = (f: Field) => `…${(f.toBigInt() % 10n ** 14n).toString().padStart(14, '0')}`;
  console.log(`    real   finalRoot ${tail(realClaim.finalRoot)}  numTurns ${realClaim.numTurns}`);
  console.log(`    forged finalRoot ${tail(bad.finalRoot)}  numTurns ${bad.numTurns}`);
  if (bad.finalRoot.toBigInt() === realClaim.finalRoot.toBigInt() && bad.numTurns.toBigInt() === realClaim.numTurns.toBigInt())
    fail('the forged claim IS the real claim — the forgery is a no-op and the table would be vacuous');
  console.log('    ⚑ the LANE TABLE IS UNTOUCHED: every Merkle root, every fold and §3.29\'s preamble seal still pass\n');

  //  ⚑ FIVE ROWS, BECAUSE THERE ARE TWO EQUALITIES AND ONLY ONE OF THEM COSTS
  //  ROWS. The SEAL (`claim == the lanes under dagDigest`) emits 23 rows and the
  //  CARRY (`claim == predecessor's claim`) emits ZERO — o1js compiles an
  //  equality between two witness variables to a Kimchi COPY CONSTRAINT, which
  //  the permutation argument enforces without a gate row. So the row count
  //  cannot witness the carry AT ALL, and a table that only exercised the seal
  //  would leave the 904 propagating slices gated by something nothing measured.
  //  Row 5 is that falsifier, and row 2 is its control.
  const rows: [string, Mode, ChainClaim | null, ChainClaim | null, boolean][] = [
    ['BOUND    (seal armed)    forged claim', 'seal', bad, bad, false],
    ['UNSEALED (seal removed)  forged claim', 'unsealed', bad, bad, true],
    ['BOUND    (seal armed)    REAL claim', 'seal', realClaim, realClaim, true],
    ['UNBOUND  (the §3.29 chain)  forged claim', 'none', null, null, true],
    ['CARRY    (seal removed)  claim ≠ PREDECESSOR\'s', 'unsealed', realClaim, bad, false],
  ];
  const outs: Record<string, string> = {};
  for (const [label, mode, claim, prev, expect] of rows) {
    const r = await runSlice(c, sl, mode, claim, prev);
    outs[label] = r.out;
    const good = r.accepted === expect;
    console.log(
      `    ${good ? '✓' : '✗'} ${label.padEnd(42)} ${r.accepted ? 'ACCEPTED' : 'REFUSED '}` +
        `${r.why ? ` — ${r.why}` : ''}`,
    );
    if (!good) fail(`${label}: expected ${expect ? 'accept' : 'refusal'}`);
    checks++;
  }
  ok('the refusal is ATTRIBUTABLE: the same forged claim is accepted with the seal removed, same slice, same reads');
  ok('the CARRY equality bites too — and it emits ZERO rows, so this table is the ONLY thing that says so');

  //  ⚑ AND THE §3.29 ROW IS A MEASUREMENT, NOT A TAUTOLOGY. The unbound chain's
  //  public output is IDENTICAL under the real claim and the forged one — there
  //  is nothing in it that mentions either. That is the gap, exhibited.
  const unboundReal = await runSlice(c, sl, 'none', null);
  if (unboundReal.out !== outs['UNBOUND  (the §3.29 chain)  forged claim'])
    fail('the §3.29 slice emitted two different outputs for one lane table — the probe is not deterministic');
  const boundReal = await runSlice(c, sl, 'seal', realClaim);
  const boundForgedOut = await runSlice(c, sl, 'unsealed', bad);
  if (boundReal.out === boundForgedOut.out)
    fail('the claim-carrying output is the same under the real and forged claims — the claim is not in it');
  //  ⚑ SHOWN ON THE FIELDS THAT MOVE. The boundary is 77 digits and the claim's
  //  octets differ in their LOW digits, so a truncated dump of either prints two
  //  identical-looking lines and the row reads as a no-op.
  const claimOf = (s: string) => {
    const p = s.split('|');
    return `finalRoot …${(BigInt(p[2]) % 10n ** 14n).toString().padStart(14, '0')}  numTurns ${p[3]}`;
  };
  console.log(
    `\n    the §3.29 public output is ONE field and it is the SAME either way:\n` +
      `      real   ${unboundReal.out.slice(0, 60)}…\n` +
      `      forged ${outs['UNBOUND  (the §3.29 chain)  forged claim'].slice(0, 60)}…\n` +
      `    the claim-carrying output DIFFERS, and a Mina-side verifier can see it:\n` +
      `      real   ${claimOf(boundReal.out)}\n` +
      `      forged ${claimOf(boundForgedOut.out)}`,
  );
  ok('the §3.29 output cannot distinguish the two claims and the claim-carrying one does — the gap, exhibited');
}

// ===========================================================================
// THE RATCHET — 2% on rows, EXACT on every count.
// ===========================================================================

const RATCHET = {
  claimLanes: 25,
  claimStride: 3,
  claimChunks: [17, 18],
  bindHeadSlice: 1,
  sealEqualities: 4,
  numTurns: 3,
  uniformInstances: 905,
  uniformPrograms: 131,
  uniformRows: 42_245_547,
  /** The emitted-row price of the WHOLE carry across 905 instances, at 2%. It is
   *  the seal's slice alone, because the propagation is a copy constraint and
   *  costs nothing — 0.0004% of the walk. */
  claimRows: 185,
  /** The four closing equalities, in emitted rows on the sealing slice. */
  sealEqualityRows: 23,
};

function ratchet(
  c: Ctx,
  decoded: { numTurns: bigint },
  m: { total: number; dSeal: number; dUnsealed: number } | null,
) {
  console.log('\n[6] THE RATCHET\n');
  const exact: [string, number | string, number | string][] = [
    ['claim lanes', NUM_CHAIN_CLAIMS, RATCHET.claimLanes],
    ['claim column stride', c.ix.at[1] - c.ix.at[0], RATCHET.claimStride],
    ['claim AIR chunks', c.chunks.join(','), RATCHET.claimChunks.join(',')],
    ['binding head slice', c.bindPos, RATCHET.bindHeadSlice],
    ['numTurns', Number(decoded.numTurns), RATCHET.numTurns],
    ['uniform instances', c.plan.totalSlices, RATCHET.uniformInstances],
    ['uniform programs', c.plan.distinctPrograms, RATCHET.uniformPrograms],
  ];
  for (const [n, got, want] of exact) {
    if (String(got) !== String(want)) fail(`${n}: ${got}, pinned EXACTLY at ${want}`);
    console.log(`    ${n.padEnd(22)} ${String(got).padStart(11)}  exact`);
  }
  const banded: [string, number, number][] = [
    ['uniform modelled rows', c.plan.totalWork + c.plan.totalCarry, RATCHET.uniformRows],
    ...(m
      ? ([
          ['claim emitted rows', m.total, RATCHET.claimRows],
          ['seal equality rows', m.dSeal - m.dUnsealed, RATCHET.sealEqualityRows],
        ] as [string, number, number][])
      : []),
  ];
  for (const [n, got, want] of banded) {
    const d = Math.abs(got - want) / want;
    if (d > 0.02) fail(`${n}: ${fmt(got)} is ${(d * 100).toFixed(1)}% from the pinned ${fmt(want)}`);
    console.log(`    ${n.padEnd(22)} ${fmt(got).padStart(11)}  ±2% of ${fmt(want)}`);
  }
  ok('every figure is ratcheted; the counts exactly, the rows at 2%');
}

// ===========================================================================

async function main() {
  mkdirSync(WORK, { recursive: true });
  console.log('\n=== LEG 21 — THE CHAIN SAYS WHICH PROOF IT VERIFIED ===');
  const c = context();
  console.log(
    `\n    vk ${c.realFri.vkFingerprint.slice(0, 16)}...  ${c.meta.instances.length} instances  ` +
      `numTurns ${c.realAir.numTurns}`,
  );

  const d = differential(c);
  polarities(c, d.claim);
  cost(c);

  if (PHASE === 'plan') {
    ratchet(c, d.claim, null);
    console.log(`\n=== ${checks} checks passed (plan only) ===\n`);
    return;
  }

  const m = await circuit(c);

  console.log('\n[4b] THE DEPLOYED PROGRAM — the uniform slice with the claim in its public output\n');
  //  ⚑ ONE `DynamicProof` class per process, so the §3.29 baseline for the SAME
  //  position is measured in a child rather than beside it.
  const t = Date.now();
  const mine = await deployed(c);
  const child = spawnSync(
    process.execPath,
    ['--max-old-space-size=16384', process.argv[1]],
    { env: { ...process.env, CLAIM_PHASE: 'deployed-none' }, encoding: 'utf8', maxBuffer: 1 << 26 },
  );
  const line = (child.stdout ?? '').split('\n').find((l) => l.startsWith('DEPLOYED-NONE '));
  if (child.status !== 0 || line === undefined)
    return fail(
      `the §3.29 baseline child did not report a row count (status ${child.status}): ` +
        `${(child.stderr ?? '').split('\n').slice(-3).join(' ')}`,
    );
  const base = Number(line.split(' ')[1]);
  console.log(
    `    the SAME position without the claim (child process): ${fmt(base)} EMITTED rows\n` +
      `    ⇒ the deployed delta is +${fmt(mine - base)} rows on the sealing slice, ` +
      `measured in ${((Date.now() - t) / 1000).toFixed(1)}s`,
  );
  if (mine <= base) fail(`the claim-carrying deployed program emits ${fmt(mine)} rows against ${fmt(base)} without it`);
  ok('the DEPLOYED uniform slice builds with the claim in its public output and emits more rows for it');

  await forgery(c, d.lanes);
  ratchet(c, d.claim, m);
  console.log(`\n=== ${checks} checks passed ===\n`);
}

/** The child: the SAME deployed program at the SAME position, without the
 *  claim. One line on stdout, so the parent parses a number and not prose. */
async function deployedNone() {
  const c = context();
  const { prog } = makeUniformSliceProgram(
    { w: c.w, shape: c.shape, ft: c.ft, op: c.op, plan: c.plan, real: c.realFri },
    { kind: 'head', pos: c.bindPos },
    { prevFlags: FeatureFlags.allMaybe },
  );
  const meta = (await (prog as any).analyzeMethods()) as any;
  console.log(`DEPLOYED-NONE ${meta.slice.rows}`);
}

(PHASE === 'deployed-none' ? deployedNone() : main()).catch((e) => {
  console.error(e);
  process.exit(1);
});

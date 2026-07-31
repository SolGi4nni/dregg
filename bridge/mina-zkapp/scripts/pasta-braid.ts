import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { Cache, FeatureFlags, Field, Poseidon, Provable, VerificationKey } from 'o1js';
import { BbExt } from '../src/FriQueryStep.js';
import {
  DagTable,
  RealInstance,
  RealRootAir,
  bindRealInstance,
  rootAirDag,
  unifiedDag,
} from '../src/RootAirDag.js';
import { dagDigestOfChunkDigests, digestOfLanes } from '../src/RootAirChain.js';
import {
  BABYBEAR_WALK_HASH,
  PASTA_WALK_HASH,
  RealRootFri,
  WalkHash,
  airColumnIndex,
  friLaneTable,
  planFriWalk,
  planOpenedValues,
  priceForSuite,
  rootFriShape,
  segmentWalk,
} from '../src/RootFriWalk.js';
import {
  AIR_CHUNK_LANES,
  AIR_SLICES,
  FriBraidCtx,
  airLaneValues,
  auxLanes,
  chunkDigestsBigInt,
  friBoundaryIn,
  friLaneValues,
  friSliceShape,
  makeFriSliceProgram,
  walkTwin,
} from '../src/RootFriSlice.js';
import {
  assertHomogeneous,
  planUniform,
  uniformLaneTable,
  uniformLayout,
} from '../src/RootFriUniform.js';
import { babyBearSuite, pastaSuite } from '../src/HashSuites.js';
import type { MerkleSuite } from '../src/HashSuiteType.js';
import { ROOT_CHALLENGE_STATUS, rehashRealRootFri } from '../src/RootConsume.js';
import { PICKLES } from '../src/CostModel.js';

// ---------------------------------------------------------------------------
// [LEG] THE SLICED CHAIN AT THE PASTA HASH — the walk, the plan, the twin, the
// falsifiers and the per-instance latency, on dregg's committed root proof.
//
//   npm run pasta-braid
//
// ⚑ WHAT THIS MEASURES AND WHY IT IS THE JOIN'S COST. `root-consume-rows`
// measures the FLAT consumer at both hashes (539 -> 61 slices). This measures
// the SLICED chain — the braid and the uniform ring, the objects the 905-instance
// join is actually made of — which until now ran the deployed BabyBear hash
// whatever `priceForSuite` returned, because the executor was called at its
// default suite and the lane table canonicalised every lane as a BabyBear one.
//
// ⚑ THE OBJECT IS RE-HASHED AND IT SAYS SO EVERYWHERE. dregg's root commits with
// Poseidon2-over-BabyBear; a Pasta-hashed root is a RE-MINT
// (`DreggMinaConfig`), which is a Rust prove run over a 2^22 batch. So
// `rehashRealRootFri` re-commits the MMCS digests this proof's own openings
// imply under the Pasta suite. REAL at both hashes: every opened row, every
// opened evaluation, every opening point, the 19 indices, ζ, α, the FRI α, the
// 16 βs, the final polynomial, the roll-in schedule, the mixed-height injection
// schedule. RE-HASHED: the four round commitments, the sixteen commit-phase
// commitments, every path sibling.
//
// ⚑ THE TRANSCRIPT IS CARRIED AND THAT IS THE HONEST ANSWER, not a deferral.
// `WalkHash.transcript = 'carried'`: FRI's α, the βs and the query indices are
// committed lanes read into their slots, which is `ROOT_CHALLENGE_STATUS`'s
// existing status for the root path at BOTH hashes and §3.14's residual 1.
//
// ⚠ AND THAT IS A REAL DIFFERENCE FROM THE 905/131 CHAIN, SAID BEFORE ANY RATIO.
// The deployed BabyBear chain has the OPTION of the batch-STARK preamble and
// this one does not, so `905 -> 199` is not a like-for-like comparison and this
// leg does not print one. The like-for-like figure is `827 -> 199`: both
// challenge-carrying, both over the same committed proof. What a Pasta preamble
// would need is TWO things — a `MultiField32Challenger` emitter and executor
// (unbuilt; `challengerRun` emits `DuplexChallenger` boundaries and
// `runSegments` runs the BabyBear permutation inline) and an oracle for the
// ROOT's preamble script at Pasta (absent; the CHALLENGER itself is
// oracle-checked by `npm run pasta-verify`, the root-scale script is not).
// ---------------------------------------------------------------------------

const PHASE = process.env.PASTA_BRAID_PHASE ?? 'main';
const WORK = process.env.PASTA_BRAID_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const OUT = (n: string) => resolve(WORK, `pasta-braid-${process.env.PASTA_BRAID_TIME ?? 'pasta'}-${n}`);
const BUDGET = Number(process.env.PASTA_BRAID_BUDGET ?? 50_000);
const CHUNK = Number(process.env.PASTA_BRAID_CHUNK ?? 256);
/** How many slices this run COMPILES AND PROVES. Everything past it is a rate
 *  multiplied out and is labelled PROJECTED. */
const LIMIT = Number(process.env.PASTA_BRAID_LIMIT ?? 2);
/**
 * ⚑ WHICH HASH `[7]` TIMES — and the CONTROL EXISTS BECAUSE THE OBVIOUS CLAIM
 * TURNED OUT TO BE FALSE.
 *
 * The expected story was: every slice is packed to the same row budget at either
 * hash, so a step costs what a ~50,000-row Pickles step costs and the whole win
 * is the INSTANCE COUNT. `PASTA_BRAID_TIME=babybear` was added to measure that
 * rather than assert it — same harness, same box, same backend, the other hash —
 * and it does not hold. MEASURED on the first three slices of each chain: Pasta
 * 13.0 / 8.0 / 9.4 s against BabyBear 19.7 / 32.6 / … s at similar row counts.
 * A `getRows()` figure is not a prover-time figure; the emulated permutation's
 * gate mix costs more per row.
 *
 * ⚠ AND THE SAMPLE IS HEAD SLICES, WHICH IS NOT THE CHAIN. Slices 0-2 hold the
 * transcript and the `permBind` bridge; the 19 query blocks that dominate both
 * chains are a different gate mix. Proving into a block means proving every
 * slice before it, which no affordable run reaches — so the rate is reported as
 * a THREE-SLICE HEAD measurement and the join figure that uses it says so.
 */
const TIME_HASH = (process.env.PASTA_BRAID_TIME ?? 'pasta') as 'pasta' | 'babybear';
const NO_CACHE = Cache.None;

let checks = 0;
let failures = 0;
const ok = (m: string) => {
  checks++;
  console.log(`  ✓ ${m}`);
};
const fail = (m: string): never => {
  failures++;
  console.error(`\n  ✗ ${m}`);
  throw new Error(m);
};
const need = (c: boolean, m: string) => (c ? ok(m) : fail(m));
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');
const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(1)}s`;

/** ⚑ A CAUGHT ERROR MUST BE A CONSTRAINT FAILURE. A `TypeError` inside a bare
 *  `catch` is indistinguishable from a refusal, which is what turns a falsifier
 *  table into a measurement of the harness. */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read|ENOENT/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|Bool\.assertTrue/i.test(m);
}

// ===========================================================================
// The context, at either hash, rebuilt deterministically by every process.
// ===========================================================================

const P = 2013265921n;
const md = (x: bigint) => ((x % P) + P) % P;
const eAdd = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x + b[i]));
const eMul = (a: bigint[], b: bigint[]) => {
  const acc = Array(7).fill(0n) as bigint[];
  for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) acc[i + j] = md(acc[i + j] + a[i] * b[j]);
  return Array.from({ length: 4 }, (_, i) => (i + 4 < 7 ? md(acc[i] + 11n * acc[i + 4]) : acc[i]));
};
const ePow = (a: bigint[], n: number) => {
  let r = [1n, 0n, 0n, 0n];
  for (let i = 0; i < n; i++) r = eMul(r, a);
  return r;
};

function readReal(): { air: RealRootAir; fri: RealRootFri } {
  const a = resolve(WORK, 'real-root-air.json');
  const f = resolve(WORK, 'real-root-fri.json');
  if (!existsSync(a) || !existsSync(f))
    fail(
      `${existsSync(a) ? f : a} is missing — this leg runs on dregg's COMMITTED root proof and has ` +
        'no synthetic fallback. `npm run root-air-fullchain` mints the AIR half; ' +
        '`cargo run -p dregg-circuit-prove --release --bin root_fri_instance` the FRI half.',
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
  return { pairs, base, ext, alpha: real.challenges.alpha.map((x) => BigInt(x)) };
}

type Ctx = FriBraidCtx & {
  label: string;
  hash: WalkHash;
  airLanes: bigint[];
  friLanes: bigint[];
  twin: ReturnType<typeof walkTwin>;
  dagDigest: Field;
  friDigest: Field;
  friCommit: Field;
  acc: bigint[];
  realFri: RealRootFri;
  merges: number;
};

function context(which: 'babybear' | 'pasta'): Ctx {
  const { air: realAir, fri: realBb } = readReal();
  const suite: MerkleSuite<any> = which === 'pasta' ? pastaSuite : babyBearSuite;
  const hash = which === 'pasta' ? PASTA_WALK_HASH : BABYBEAR_WALK_HASH;
  let realFri = realBb;
  let merges = 0;
  if (which === 'pasta') {
    const r = rehashRealRootFri(realBb, pastaSuite);
    realFri = r.real;
    merges = r.merges;
  }
  const shape = rootFriShape(realFri);
  const op = planOpenedValues(shape, airColumnIndex());
  const ft = friLaneTable(shape, op, hash);
  const w = segmentWalk(shape, { hash, price: priceForSuite(suite.name) });
  const plan = planFriWalk(w, op, ft, { usableRows: BUDGET, chunkLanes: CHUNK });

  const cols = realColumns(realAir);
  const airLanes = airLaneValues(cols.base, cols.ext);
  const friLanes = friLaneValues(realFri, shape, ft, op);
  const twin = walkTwin(w, shape, ft, op, friLanes, airLanes, realFri, suite);

  const nAir = airLanes.length / AIR_CHUNK_LANES;
  const dagDigest = dagDigestOfChunkDigests(chunkDigestsBigInt(airLanes, nAir, AIR_CHUNK_LANES));
  const friDigest = dagDigestOfChunkDigests(chunkDigestsBigInt(friLanes, plan.nFriChunks, CHUNK));
  const friCommit = Poseidon.hash([dagDigest, friDigest]);

  const u = unifiedDag(rootAirDag());
  const R = u.roots.length;
  let acc = [0n, 0n, 0n, 0n];
  u.tableSpans.forEach((span, i) => {
    const p3 = cols.pairs[i][1].accumulator.map((x) => BigInt(x));
    acc = eAdd(acc, eMul(p3, ePow(cols.alpha, R - span.rootTo)));
  });

  return {
    label: which,
    hash,
    w,
    shape,
    ft,
    op,
    plan,
    suite,
    airLanes,
    friLanes,
    twin,
    dagDigest,
    friDigest,
    friCommit,
    acc,
    realFri,
    merges,
  };
}

/** One slice's private inputs, at this context's hash. */
function witnessOf(c: Ctx, si: number) {
  const sl = c.plan.slices[si];
  const sh = friSliceShape(c, si);
  const F = (x: bigint) => Field(x);
  const pad = (a: Field[], n: number) => (a.length ? a : [Field(0)]).slice(0, Math.max(n, 1));
  const airRead: Field[] = [];
  for (const ch of sl.readsAirChunks)
    for (let i = 0; i < CHUNK; i++) airRead.push(F(c.airLanes[ch * CHUNK + i] ?? 0n));
  const nAirTot = Math.ceil(c.airLanes.length / CHUNK);
  const airOther: Field[] = [];
  for (let ch = 0; ch < nAirTot; ch++)
    if (!sl.readsAirChunks.includes(ch))
      airOther.push(digestOfLanes(c.airLanes.slice(ch * CHUNK, (ch + 1) * CHUNK).map((x) => Field(x))));
  const friRead: Field[] = [];
  for (const ch of sl.readsFriChunks)
    for (let i = 0; i < CHUNK; i++) friRead.push(F(c.friLanes[ch * CHUNK + i] ?? 0n));
  const friOther: Field[] = [];
  for (let ch = 0; ch < c.plan.nFriChunks; ch++)
    if (!sl.readsFriChunks.includes(ch))
      friOther.push(digestOfLanes(c.friLanes.slice(ch * CHUNK, (ch + 1) * CHUNK).map((x) => Field(x))));
  const aux: Field[] = [];
  for (let k = sl.from; k < sl.to; k++) for (const v of c.twin.aux[k]) aux.push(F(v));
  return {
    sh,
    acc: BbExt.from(c.acc),
    bIn: friBoundaryIn(c, c.twin, si, c.dagDigest, c.friCommit, c.acc),
    liveIn: pad(c.twin.carry[sl.from].map(F), sh.nLiveIn),
    airRead: pad(airRead, sh.nAirRead),
    airOther: pad(airOther, sh.nAirOther),
    friRead: pad(friRead, sh.nFriRead),
    friOther: pad(friOther, sh.nFriOther),
    aux: pad(aux, sh.nAux),
  };
}

// ===========================================================================
// PHASE `slice` — ONE slice, its own process (`DynamicProof.tag()` is
// process-global, so a second side-loaded class in one process gets an
// order-dependent identifier).
// ===========================================================================

if (PHASE === 'slice') {
  const si = Number(process.env.PASTA_BRAID_SLICE ?? '0');
  const c = context(TIME_HASH);
  const airVk = JSON.parse(readFileSync(resolve(WORK, 'vk-6.json'), 'utf8'));
  const airFlags: FeatureFlags = JSON.parse(readFileSync(resolve(WORK, 'flags-6.json'), 'utf8'));
  const prevVk = si === 0 ? airVk : JSON.parse(readFileSync(OUT(`vk-${si - 1}.json`), 'utf8'));
  const prevFlags: FeatureFlags =
    si === 0 ? airFlags : JSON.parse(readFileSync(OUT(`flags-${si - 1}.json`), 'utf8'));

  const { prog, Prev } = makeFriSliceProgram(c, si, {
    prevVkHash: BigInt(prevVk.hash),
    prevFlags,
  });
  let t = Date.now();
  const meta = (await (prog as any).analyzeMethods()) as any;
  const rows = meta.slice.rows as number;
  const analyzeMs = Date.now() - t;
  const myFlags = FeatureFlags.fromGates(meta.slice.gates);

  t = Date.now();
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });
  const compileMs = Date.now() - t;
  mkdirSync(WORK, { recursive: true });
  writeFileSync(OUT(`vk-${si}.json`), JSON.stringify(verificationKey));
  writeFileSync(OUT(`flags-${si}.json`), JSON.stringify(myFlags));

  const wit = witnessOf(c, si);
  const prevRaw = JSON.parse(
    readFileSync(si === 0 ? resolve(WORK, 'proof-6.json') : OUT(`proof-${si - 1}.json`), 'utf8'),
  );
  const prev = await (Prev as any).fromJSON(prevRaw);
  t = Date.now();
  const { proof } = await (prog as any).slice(
    wit.bIn,
    prev,
    VerificationKey.fromJSON(prevVk),
    wit.acc,
    wit.liveIn,
    wit.airRead,
    wit.airOther,
    wit.friRead,
    wit.friOther,
    wit.aux,
  );
  const proveMs = Date.now() - t;
  writeFileSync(OUT(`proof-${si}.json`), JSON.stringify(proof.toJSON()));
  const verified = await prog.verify(proof);
  console.log(
    '##JSON##' +
      JSON.stringify({ si, rows, analyzeMs, compileMs, proveMs, verified, out: String(proof.publicOutput) }),
  );
  process.exit(0);
}

function childSlice(si: number): any {
  const out = execFileSync(process.execPath, ['--max-old-space-size=16384', process.argv[1]], {
    encoding: 'utf8',
    maxBuffer: 1 << 26,
    env: {
      ...process.env,
      PASTA_BRAID_PHASE: 'slice',
      PASTA_BRAID_SLICE: String(si),
      PASTA_BRAID_WORKDIR: WORK,
      PASTA_BRAID_TIME: TIME_HASH,
    },
    stdio: ['ignore', 'pipe', 'inherit'],
  });
  const line = out.split('\n').find((l) => l.startsWith('##JSON##'));
  if (!line) fail(`slice ${si} produced no result line:\n${out.slice(-3000)}`);
  return JSON.parse(line!.slice(8));
}

// ===========================================================================
// PHASE `main`.
// ===========================================================================

console.log('\n=== THE SLICED CHAIN AT THE PASTA HASH, ON dregg\'s COMMITTED ROOT ===');
console.log(`    budget ${fmt(BUDGET)} rows/step, chunk ${CHUNK} lanes, backend ${process.env.O1JS_BACKEND ?? 'wasm'}`);
console.log(`    challenges: ${ROOT_CHALLENGE_STATUS}\n`);

// ---------------------------------------------------------------------------
console.log('[1] the two objects — one proof, two hashes');
let t = Date.now();
const BB = context('babybear');
const PA = context('pasta');
console.log(`    (both contexts built, ${secs(t)})`);
need(
  BB.w.hash.transcript === 'implemented' && PA.w.hash.transcript === 'carried',
  `the BabyBear walk DERIVES its transcript and the Pasta walk CARRIES it — ${PA.w.hash.name}'s ` +
    'challenger is `MultiField32Challenger` and dregg mints no Pasta-hashed root to check a model of it against',
);
need(PA.w.priced === 'shaped', 'the Pasta walk is SHAPED at Pasta, not a BabyBear walk priced at Pasta prices');
need(
  PA.realFri.kind.includes('rehashed:mina-poseidon-pasta'),
  `the Pasta object is LABELLED a re-hash (${PA.realFri.kind}) — dregg's root commits with Poseidon2-over-BabyBear`,
);
need(
  String(PA.realFri.commits[0]) !== String(BB.realFri.commits[0]),
  `and it is a DIFFERENT object: commit-phase root 0 is ${String(PA.realFri.commits[0]).slice(0, 14)}… ` +
    `against ${String(BB.realFri.commits[0]).slice(0, 14)}…`,
);
need(
  BB.realFri.queries.every((q, qi) =>
    q.inputBatches.every((b, ri) =>
      b.rows.every((row, mi) => row.every((v, c) => v === PA.realFri.queries[qi].inputBatches[ri].rows[mi][c])),
    ),
  ),
  'every opened ROW is IDENTICAL across the two — the re-hash moves MMCS digests and nothing else',
);
ok(`the sparse re-hash merged ${fmt(PA.merges)} shared path nodes (two queries meeting in one tree)`);

// ---------------------------------------------------------------------------
console.log('\n[2] the LANE KINDS — the blocker that used to refuse this walk outright');
const nativeLanes = [...PA.ft.kinds].filter((k) => k === 1).length;
const bbNative = [...BB.ft.kinds].filter((k) => k === 1).length;
need(
  bbNative === 0,
  `the BabyBear table has ZERO native lanes of ${fmt(BB.ft.nLanes)} — every lane is canonicalised, exactly as before`,
);
need(
  nativeLanes === PA.shape.knobs.layers + PA.shape.rounds.length,
  `the Pasta table has ${nativeLanes} NATIVE lanes — the ${PA.shape.knobs.layers} commit-phase roots and the ` +
    `${PA.shape.rounds.length} input-round roots, and NOTHING else (opened values, points, the final polynomial ` +
    'and the carried challenges are BabyBear at both hashes)',
);
const nativeSlots = [...PA.w.slots.kinds].filter((k) => k === 1).length;
need(
  nativeSlots === PA.hash.digestLanes * (1 + PA.shape.heights.length) + PA.hash.spongeStateLanes,
  `and ${nativeSlots} native SLOTS — \`cur\`, the ${PA.shape.heights.length} mixed-height injection registers and ` +
    'the leaf sponge state; a boundary canonicalising one of those refuses every honest proof',
);
need(
  PA.ft.carried !== null && BB.ft.carried === null,
  'the Pasta table commits α, the 16 βs and the 19 query indices; the BabyBear one commits the entering ' +
    'challenger state instead — exactly one of the two regions exists in any table',
);

// ---------------------------------------------------------------------------
console.log('\n[3] the TWIN at the Pasta hash — does the walk close on the re-hashed object');
const eq = (a: bigint[], b: readonly (number | string | bigint)[]) =>
  a.length === b.length && a.every((x, i) => x === BigInt(b[i] as any));
let roots = 0;
let ros = 0;
let folds = 0;
let finals = 0;
for (const chk of PA.twin.checks) {
  if (chk.kind === 'inputRoot') {
    const want = PA.realFri.inputRounds[chk.round!].commit;
    if (!eq(chk.got, want))
      fail(
        `query ${chk.q} input round ${chk.round}: the mixed-height Pasta opening lands on ` +
          `${chk.got[0]} and the re-hashed commitment is ${want[0]}`,
      );
    roots++;
  } else if (chk.kind === 'ro') {
    const want = PA.realFri.queries[chk.q].reducedOpenings[chk.i!];
    if (!eq(chk.got, want.ro)) fail(`query ${chk.q} height ${chk.h}: reduced opening disagrees with dregg's own`);
    ros++;
  } else if (chk.kind === 'fold') {
    const want = PA.realFri.queries[chk.q].foldedAfterRound[chk.i!];
    if (!eq(chk.got, want)) fail(`query ${chk.q} layer ${chk.i}: the fold value disagrees with dregg's own`);
    folds++;
  } else if (chk.kind === 'final') finals++;
}
ok(
  `${fmt(roots)} input-round openings close on the RE-HASHED Pasta commitments — the mixed-height ` +
    'injection schedule, the leaf sponge and every Merkle level ran the Pasta hash',
);
ok(`${fmt(ros)} reduced openings and ${fmt(folds)} fold values are dregg's OWN — the DEEP quotient and the fold chain are hash-independent and stayed identical`);
ok(`${fmt(finals)} queries reach the final-polynomial landing`);

// ---------------------------------------------------------------------------
console.log('\n[4] the walk, and what the hash did to it');
const rowsBy = (c: Ctx) => {
  const by = new Map<string, { n: number; rows: number }>();
  for (const s of c.w.segs) {
    const e = by.get(s.t) ?? { n: 0, rows: 0 };
    e.n++;
    e.rows += s.rows;
    by.set(s.t, e);
  }
  return by;
};
const bbBy = rowsBy(BB);
const paBy = rowsBy(PA);
console.log(`    ${'segment'.padEnd(10)} ${'BabyBear'.padStart(24)}   ${'Pasta'.padStart(24)}`);
for (const k of new Set([...bbBy.keys(), ...paBy.keys()])) {
  const b = bbBy.get(k);
  const p = paBy.get(k);
  console.log(
    `    ${k.padEnd(10)} ${(b ? `${fmt(b.n)} segs ${fmt(b.rows)} rows` : '—').padStart(24)}   ` +
      `${(p ? `${fmt(p.n)} segs ${fmt(p.rows)} rows` : '—').padStart(24)}`,
  );
}
console.log(
  `    TOTAL      ${`${fmt(BB.w.segs.length)} segs ${fmt(BB.w.totalRows)} rows`.padStart(24)}   ` +
    `${`${fmt(PA.w.segs.length)} segs ${fmt(PA.w.totalRows)} rows`.padStart(24)}   ` +
    `${(BB.w.totalRows / PA.w.totalRows).toFixed(2)}x`,
);
console.log(`    lane table ${`${fmt(BB.ft.nLanes)} lanes`.padStart(24)}   ${`${fmt(PA.ft.nLanes)} lanes`.padStart(24)}`);

// ---------------------------------------------------------------------------
console.log('\n[5] THE PLAN — what one JOIN is made of');
function uniform(c: Ctx) {
  const L = uniformLayout(c.w, c.shape, c.ft, CHUNK);
  const ftU = uniformLaneTable(c.shape, c.ft, L);
  const hom = assertHomogeneous(c.w, c.op, ftU, L);
  const p = planUniform(c.w, c.op, ftU, L, { usableRows: BUDGET });
  return { L, ftU, hom, p };
}
const bbU = uniform(BB);
const paU = uniform(PA);
const row = (label: string, a: string, b: string) =>
  console.log(`    ${label.padEnd(28)} ${a.padStart(14)}   ${b.padStart(14)}`);
row('', 'BabyBear', 'Pasta');
row('deployed braid slices', fmt(BB.plan.slices.length), fmt(PA.plan.slices.length));
row('uniform head programs', fmt(bbU.p.head.length), fmt(paU.p.head.length));
row('uniform block programs', fmt(bbU.p.block.length), fmt(paU.p.block.length));
row('PROGRAMS (compiles, keys)', fmt(bbU.p.distinctPrograms), fmt(paU.p.distinctPrograms));
row('INSTANCES (uniform)', fmt(bbU.p.totalSlices), fmt(paU.p.totalSlices));
row('+ AIR chain', fmt(AIR_SLICES), fmt(AIR_SLICES));
row('CHAIN LENGTH', fmt(bbU.p.totalSlices + AIR_SLICES), fmt(paU.p.totalSlices + AIR_SLICES));
row('work + carry rows', fmt(bbU.p.totalWork + bbU.p.totalCarry), fmt(paU.p.totalWork + paU.p.totalCarry));
const instRatio = bbU.p.totalSlices / paU.p.totalSlices;
ok(
  `the uniform ring is ${fmt(bbU.p.totalSlices)} instances at BabyBear and ${fmt(paU.p.totalSlices)} at Pasta — ` +
    `${instRatio.toFixed(2)}x FEWER SEQUENTIAL STEPS. ⚠ NOT the whole of the join's cost: ` +
    "`PASTA_BRAID_TIME=babybear` measures the per-instance rate too, and it is NOT equal at the " +
    'two hashes (24.0 s against 10.1 s at similar row counts) — a `getRows()` figure is not a ' +
    'prover-time figure',
);

// ---------------------------------------------------------------------------
console.log('\n[6] THE FALSIFIERS — run in circuit at the Pasta hash');
/** The first slice that consumes a witnessed sibling AND closes the round that
 *  sibling feeds, positioned after it — the only cut at which a bent Pasta
 *  digest has something to fail against. */
function attributingSlice(c: Ctx): number {
  for (let si = 0; si < c.plan.slices.length; si++) {
    const sl = c.plan.slices[si];
    let firstAux = -1;
    let tag: string | null = null;
    for (let k = sl.from; k < sl.to; k++) {
      const s = c.w.segs[k];
      const a = auxLanes(s, c.w.hash);
      if (a > 0 && firstAux < 0) {
        firstAux = k;
        tag = s.t === 'inLevel' ? `r${(s as any).round}` : `L${(s as any).r}`;
      }
      if (firstAux >= 0 && k > firstAux) {
        const cl = s.t === 'inRoot' ? `r${(s as any).round}` : s.t === 'cpRoot' ? `L${(s as any).r}` : null;
        if (cl !== null && cl === tag) return si;
      }
    }
  }
  return -1;
}
const at = attributingSlice(PA);
need(at >= 0, `slice ${at} is the first cut that consumes a Pasta sibling AND closes the round it feeds`);

/** ⚑ THE SLICE A BENT LEAF LANE IS ATTRIBUTABLE AT, which is NOT the same cut.
 *  A bent opened row changes a leaf digest, and what refuses it is the
 *  `cur == commitment` of that row's OWN round — so the cut has to hold the
 *  `inBlock` AND the `inRoot` of one round. Bending a lane at any other cut is
 *  ACCEPTED CORRECTLY, and asserting a refusal there measures nothing. (The
 *  first version of this table did exactly that and went red on its own
 *  falsifier.) */
function rowAttributingSlice(c: Ctx): { si: number; lane: number } {
  for (let si = 0; si < c.plan.slices.length; si++) {
    const sl = c.plan.slices[si];
    for (let k = sl.from; k < sl.to; k++) {
      const s = c.w.segs[k];
      if (s.t !== 'inBlock') continue;
      let closes = false;
      for (let j = k + 1; j < sl.to; j++) {
        const t2 = c.w.segs[j];
        if (t2.t === 'inRoot' && t2.round === s.round && t2.q === s.q) closes = true;
      }
      if (!closes) continue;
      const [lo] = c.ft.blockLanes(s.q, s.round, s.height, s.block);
      return { si, lane: lo };
    }
  }
  return { si: -1, lane: -1 };
}

/** Where a committed lane sits inside the flat read region a slice is handed. */
function friReadIndex(c: Ctx, si: number, lane: number): number {
  const sl = c.plan.slices[si];
  const ch = Math.floor(lane / CHUNK);
  const at2 = sl.readsFriChunks.indexOf(ch);
  if (at2 < 0) return -1;
  return at2 * CHUNK + (lane - ch * CHUNK);
}

const rowCut = rowAttributingSlice(PA);
need(
  rowCut.si >= 0,
  `slice ${rowCut.si} holds both an \`inBlock\` and the \`inRoot\` of its own round — the only shape at ` +
    'which a bent opened row lane has something to fail against',
);
/** The Pasta ROUND COMMITMENT a cut closes against — a NATIVE lane, and the one
 *  the old `assertLanesAreBabyBear` refusal existed to keep out of this table. */
const commitCut = (() => {
  for (let si = 0; si < PA.plan.slices.length; si++) {
    const sl = PA.plan.slices[si];
    for (let k = sl.from; k < sl.to; k++) {
      const s = PA.w.segs[k];
      if (s.t === 'inRoot') return { si, lane: PA.ft.inputCommit[s.round] };
    }
  }
  return { si: -1, lane: -1 };
})();
need(commitCut.si >= 0, `slice ${commitCut.si} closes a Merkle walk against a NATIVE Pasta round commitment`);

async function runSlice(c: Ctx, si: number, bend?: (w: ReturnType<typeof witnessOf>) => void) {
  const wit = witnessOf(c, si);
  bend?.(wit);
  const { runSegments } = await import('../src/RootFriSlice.js');
  await Provable.runAndCheck(async () => {
    const sto = new Map<number, Field>();
    const sl = c.plan.slices[si];
    c.w.liveIn[sl.from].forEach((slot, i) => sto.set(slot, Provable.witness(Field, () => wit.liveIn[i])));
    runSegments(
      c.w,
      c.shape,
      c.ft,
      c.op,
      c.plan,
      si,
      sto,
      {
        airLanes: wit.airRead.slice(0, wit.sh.nAirRead).map((v) => Provable.witness(Field, () => v)),
        airOther: wit.airOther.slice(0, wit.sh.nAirOther),
        friLanes: wit.friRead.slice(0, wit.sh.nFriRead).map((v) => Provable.witness(Field, () => v)),
        friOther: wit.friOther.slice(0, wit.sh.nFriOther),
        aux: wit.aux.slice(0, wit.sh.nAux).map((v) => Provable.witness(Field, () => v)),
      } as any,
      c.suite,
    );
  });
}

const bendAt = (idx: number) => (w: ReturnType<typeof witnessOf>) => {
  if (idx < 0 || idx >= w.friRead.length) fail(`the falsifier's lane is not in the slice's read region`);
  w.friRead[idx] = w.friRead[idx].add(1);
};
const cases: [string, number, (w: ReturnType<typeof witnessOf>) => void, boolean][] = [
  ['the HONEST slice', at, () => {}, true],
  ['a bent Pasta Merkle SIBLING', at, (w) => (w.aux[0] = w.aux[0].add(1)), false],
  [
    'a bent opened ROW lane, at the cut that closes its round',
    rowCut.si,
    bendAt(friReadIndex(PA, rowCut.si, rowCut.lane)),
    false,
  ],
  [
    'a bent NATIVE Pasta round commitment',
    commitCut.si,
    bendAt(friReadIndex(PA, commitCut.si, commitCut.lane)),
    false,
  ],
  ['the HONEST slice at the leaf cut', rowCut.si, () => {}, true],
];
for (const [label, si, bend, expect] of cases) {
  t = Date.now();
  let accepted = true;
  let why = '';
  try {
    await runSlice(PA, si, bend);
  } catch (e) {
    accepted = false;
    why = String((e as Error).message).split('\n')[0].slice(0, 110);
    if (!isConstraintFailure(e)) fail(`${label} failed with a HARNESS error, not a constraint failure: ${why}`);
  }
  need(
    accepted === expect,
    `slice ${si}: ${label} is ${accepted ? 'ACCEPTED' : 'REFUSED'}${why ? ` — ${why}` : ''} (${secs(t)})`,
  );
}

// ---------------------------------------------------------------------------
// ⚑ THE ROW MODEL, CHECKED AT EVERY CUT AND NOT AT THE THREE THAT GET PROVED.
//
// `[7]` proves three slices. The plan has 207, and a segment type this leg
// UNDER-prices at Pasta would produce a cut that models under the budget and
// blows the Pickles domain — discovered at instance 130 of a prove run nobody
// can afford to repeat. `Provable.constraintSystem` over `runSegments` alone
// needs no side-loaded predecessor and therefore no process boundary, so every
// cut can be measured in one pass at about a second each.
//
// ⚠ IT IS THE WALK'S ROWS, NOT THE SLICE'S. The commitment, the boundary and the
// recursive verification are not in this body; the headroom below is therefore
// the walk against the whole budget, which is the conservative reading.
// ---------------------------------------------------------------------------
console.log('\n[7a] THE ROW MODEL at every cut — is any Pasta segment UNDER-priced');
if (process.env.PASTA_BRAID_ALLCUTS === '0') {
  console.log('    (skipped: PASTA_BRAID_ALLCUTS=0)');
} else {
  const { runSegments } = await import('../src/RootFriSlice.js');
  t = Date.now();
  let worst = { si: -1, rows: 0, modelled: 0 };
  let worstRatio = { si: -1, ratio: 0, rows: 0, modelled: 0 };
  const N = PA.plan.slices.length;
  for (let si = 0; si < N; si++) {
    const wit = witnessOf(PA, si);
    const cs = await Provable.constraintSystem(async () => {
      const sto = new Map<number, Field>();
      const sl = PA.plan.slices[si];
      PA.w.liveIn[sl.from].forEach((slot, i) => sto.set(slot, Provable.witness(Field, () => wit.liveIn[i])));
      runSegments(
        PA.w,
        PA.shape,
        PA.ft,
        PA.op,
        PA.plan,
        si,
        sto,
        {
          airLanes: wit.airRead.slice(0, wit.sh.nAirRead).map((v) => Provable.witness(Field, () => v)),
          airOther: wit.airOther.slice(0, wit.sh.nAirOther),
          friLanes: wit.friRead.slice(0, wit.sh.nFriRead).map((v) => Provable.witness(Field, () => v)),
          friOther: wit.friOther.slice(0, wit.sh.nFriOther),
          aux: wit.aux.slice(0, wit.sh.nAux).map((v) => Provable.witness(Field, () => v)),
        } as any,
        PA.suite,
      );
    });
    const modelled = PA.plan.slices[si].workRows;
    if (cs.rows > worst.rows) worst = { si, rows: cs.rows, modelled };
    const ratio = cs.rows / Math.max(modelled, 1);
    if (ratio > worstRatio.ratio) worstRatio = { si, ratio, rows: cs.rows, modelled };
  }
  console.log(`    (${N} cuts measured, ${secs(t)})`);
  need(
    worst.rows <= PICKLES.usableRowsMpv1,
    `the WIDEST of all ${N} Pasta cuts is slice ${worst.si} at ${fmt(worst.rows)} MEASURED walk rows ` +
      `(modelled ${fmt(worst.modelled)}), inside the ${fmt(PICKLES.usableRowsMpv1)}-row Pickles budget ` +
      `— ${((worst.rows / PICKLES.usableRowsMpv1) * 100).toFixed(1)}%`,
  );
  need(
    worstRatio.ratio <= 1,
    `and the model never UNDER-prices: the worst measured/modelled ratio over all ${N} cuts is ` +
      `${worstRatio.ratio.toFixed(3)} at slice ${worstRatio.si} (${fmt(worstRatio.rows)} measured vs ` +
      `${fmt(worstRatio.modelled)} modelled)`,
  );
}

// ---------------------------------------------------------------------------
console.log('\n[7] SECONDS PER INSTANCE — compiled and PROVED, in a fresh process each');
if (LIMIT < 1) {
  console.log('    (skipped: PASTA_BRAID_LIMIT=0 — this run measures the PLAN and the walk, not the rate)');
} else if (!existsSync(resolve(WORK, 'proof-6.json'))) {
  console.log('    (skipped: `.fullchain/proof-6.json` — the AIR chain\'s terminal proof — is not on disk)');
} else {
  //  ⚑ WHICH CHAIN IS BEING TIMED, SAID IN THE OUTPUT. The default is Pasta;
  //  `PASTA_BRAID_TIME=babybear` runs the CONTROL through the same harness on
  //  the same box, which is what turns "the win is the instance count, not the
  //  latency" from a sentence into a comparison.
  const TC = TIME_HASH === 'pasta' ? PA : BB;
  const TU = TIME_HASH === 'pasta' ? paU : bbU;
  console.log(`    timing the ${TIME_HASH.toUpperCase()} chain (${fmt(TC.plan.slices.length)} braid slices)`);
  const results: any[] = [];
  for (let si = 0; si < Math.min(LIMIT, TC.plan.slices.length); si++) {
    t = Date.now();
    const r = childSlice(si);
    results.push(r);
    console.log(
      `    slice ${String(si).padStart(3)}  ${fmt(r.rows).padStart(7)} rows  ` +
        `compile ${(r.compileMs / 1000).toFixed(1)}s  PROVE ${(r.proveMs / 1000).toFixed(1)}s  ` +
        `verify ${r.verified ? 'ok' : 'FAILED'}  (wall ${secs(t)})`,
    );
    if (!r.verified) fail(`slice ${si}'s proof does not verify under its own key`);
  }
  const proveS = results.reduce((a, r) => a + r.proveMs, 0) / results.length / 1000;
  const total = TU.p.totalSlices + AIR_SLICES;
  ok(
    `MEASURED ${proveS.toFixed(1)} s/instance over ${results.length} proved slices at the ` +
      `${TIME_HASH.toUpperCase()} hash (${process.env.O1JS_BACKEND === 'native' ? 'NATIVE backend' : 'wasm backend'})`,
  );
  console.log(
    `\n    PROJECTED join cost = ${fmt(total)} instances x ${proveS.toFixed(1)} s = ` +
      `${((total * proveS) / 3600).toFixed(2)} h  (the instance count is MEASURED; the rate is a ` +
      `${results.length}-slice measurement multiplied out)`,
  );
  writeFileSync(
    OUT('measurement.json'),
    JSON.stringify(
      {
        budget: BUDGET,
        chunk: CHUNK,
        backend: process.env.O1JS_BACKEND ?? 'wasm',
        timedHash: TIME_HASH,
        babybear: {
          segments: BB.w.segs.length,
          modelledRows: BB.w.totalRows,
          laneTable: BB.ft.nLanes,
          braidSlices: BB.plan.slices.length,
          uniformPrograms: bbU.p.distinctPrograms,
          uniformInstances: bbU.p.totalSlices,
        },
        pasta: {
          segments: PA.w.segs.length,
          modelledRows: PA.w.totalRows,
          laneTable: PA.ft.nLanes,
          braidSlices: PA.plan.slices.length,
          uniformPrograms: paU.p.distinctPrograms,
          uniformInstances: paU.p.totalSlices,
        },
        proved: results,
        secondsPerInstance: proveS,
      },
      null,
      2,
    ),
  );
}

if (failures > 0) {
  console.error(`\n${failures} FAILURES\n`);
  process.exit(1);
}
console.log(`\n=== ${checks} checks passed ===\n`);

// THE SCHEDULER — where to cut a dregg-proof verifier, and what the schedule
// costs.
//
//   npm run schedule
//
// §3.20 ran the partition and priced a boundary, and the price turned out to
// depend entirely on WHERE the boundary is: 34,566 rows at a query ENTRY — 69.8%
// of a `max_proofs_verified = 2` step — and 762 rows INSIDE a query. So the
// deployed step count was left as a BAND, 564-1,838 work-carrying steps, with
// the note that which end it lands on is "the scheduler `KimchiPartition` names
// as its remainder". A 3.3x spread is the difference between a feasible
// engineering project and an infeasible one.
//
// ⚑ THIS LEG COLLAPSES THE BAND, AND IT IS NOT ONLY A PLACEMENT. The reason a
// query-entry boundary costs 34,566 rows is that `rootCommitDigest` is the
// digest of ONE FLAT LANE LIST, so any step that re-derives it re-witnesses all
// 9,103 deployed root lanes — 8,920 of which are claimed opened evaluations a
// FOLD CHAIN NEVER READS. Commit to the VECTOR OF CHUNK DIGESTS instead and a
// step re-witnesses only the chunks it reads; the boundary is still ONE field
// element and `KimchiPartition.StepPublicInput` is unchanged. The scheduler is a
// dynamic program over the measured carry; the commitment is what gives it
// somewhere cheap to cut.
//
// ⚑ AND IT IS DEMONSTRATED, NOT COMPUTED. A schedule that is only arithmetic is
// the thing this leg exists to stop — §3.20 exists because "573 steps" was a
// division nobody had run. So the chain the scheduler describes is PROVED at the
// geometry that runs: one transcript step and TWO steps per query, cut INSIDE
// the query at the DEEP/fold seam, every step proved and verified, with the
// splice refused nine ways and an unbound control required to ACCEPT what the
// bound one refuses.
//
// ⚑ THE THREE WALLS §3.20 MEASURED ARE OBEYED, NOT REDISCOVERED. Four compiled
// step circuits in one process hang at the first `prove`, so this is ONE program
// with THREE methods. o1js's default prover-key cache aborts first, so
// `Cache.None`. Hashing raw lanes costs 2.96x packing them 8-to-a-Pasta-field,
// so the carrier packs.
//
// Needs cargo (the emitter) and a 16 GB node heap.

import { Bool, Cache, Field, Provable, ZkProgram } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { resolve } from 'node:path';
import { assertLaneLt2p31 } from '../src/Poseidon2BabyBearW16.js';
import { BbExt } from '../src/FriQueryStep.js';
import {
  claimOf,
  makeDreggProofVerifyProgram,
  minaFixtureConstraints,
  runQueryInputAndDeep,
  shapeOf,
  verifyPlan,
  witnessOf,
  zetaPointsOf,
} from '../src/DreggProofVerify.js';
import {
  GENESIS_CHALLENGE_DIGEST,
  carriedLaneCount,
  challengeLanes,
  digestOfLanes,
  rootCommitLanes,
  stepBoundary,
  partitionTerminalSeal,
} from '../src/DreggProofPartition.js';
import {
  chainSideOf,
  deepStepArgs,
  foldStepArgs,
  makeScheduledVerify,
  rcdOfDigests,
  scheduleSideOf,
  scheduledSteps,
} from '../src/DreggProofSchedule.js';
import {
  DEPLOYED_COLS,
  KIMCHI_ROWS,
  MEASURED,
  PICKLES_OVERHEAD,
  bestSchedule,
  deployedProgram,
  deployedShapeOf,
  schedule,
  scheduleFlatCarry,
  usableRows,
} from '../src/PartitionSchedule.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const secs = (t: number) => ((Date.now() - t) / 1000).toFixed(1) + 's';
const n = (x: number) => Math.round(x).toLocaleString();

/** §3.19: the row count at which `compile()` was watched to abort. */
const MEASURED_COMPILE_WALL = 73_259;
/** §3.20: o1js's prover-key cache serializes inside kimchi's 32-bit wasm heap
 *  and aborts before anything else does. Named, not quietly passed. */
const NO_CACHE = Cache.None;

/** ⚑ `degree_bits = 2`, AND THAT IS NOT §3.20's GEOMETRY — IT IS A FALSIFIER
 *  REQUIREMENT. At `degree_bits = 1` the trace polynomials are LINEAR, so every
 *  DEEP quotient `(p(x) - p(z))/(x - z)` is a CONSTANT and all three queries
 *  produce the SAME reduced opening — measured, not feared: `[3,0,2]` gave one
 *  value three times. The intra-query splice this leg exists to refuse — handing
 *  the fold half another query's reduced openings — is then not a substitution
 *  at all, exactly as §3.19 [8]'s fold-order falsifier is blind at
 *  `degree_bits = 1` and §3.20's skip falsifier is blind when two query indices
 *  collide. [2] asserts the premise before [6] uses it. Three queries is still
 *  what takes the one-step assembly past the domain. */
const DB = 2;
const LB = 1;
const NQ = 3;
const QPOW = 16;
/** The fixture's 56 opened lanes over 32-lane chunks is TWO open chunks — the
 *  multi-chunk rebinding is exercised rather than described. `PartitionSchedule`
 *  sweeps this parameter at the deployed lane count; here it only has to be
 *  small enough that more than one chunk exists. */
const OPEN_CHUNK_LANES = 32;

const PHASE = process.env.SCHEDULE_PHASE ?? 'main';
const WORKDIR = process.env.SCHEDULE_WORKDIR ?? mkdtempSync(resolve(tmpdir(), 'dregg-schedule-'));

// ---------------------------------------------------------------------------
// The dregg-side emitter.
// ---------------------------------------------------------------------------

function repoRoot(): string {
  const d = process.env.DREGG_REPO_ROOT ?? resolve(process.cwd(), '../..');
  if (!existsSync(resolve(d, 'circuit/src/bin/mina_stark_fixture.rs')))
    throw new Error(`the dregg-side proof emitter is not under ${d} — set DREGG_REPO_ROOT`);
  return d;
}
const ROOT = repoRoot();
let emitterBuilt = false;
function mint(seed: number) {
  if (!emitterBuilt) {
    // ⚑ `--bin`, not `--example`: an example compiles dev-dependencies, which
    // reach `dregg-lean-ffi`, whose build script fails closed while the Lean
    // tree is mid-edit. This leg is about Mina and must not go red for that.
    execFileSync('cargo', ['build', '-p', 'dregg-circuit', '--release', '--bin', 'mina_stark_fixture'], {
      cwd: ROOT,
      stdio: ['ignore', 'ignore', 'inherit'],
    });
    emitterBuilt = true;
  }
  return JSON.parse(
    execFileSync(
      resolve(ROOT, 'target/release/mina_stark_fixture'),
      [DB, LB, NQ, QPOW, seed].map(String).concat(['none']),
      { encoding: 'utf8', maxBuffer: 1 << 26 },
    ),
  );
}

const rowsOf = async (prog: any, method: string) =>
  ((await prog.analyzeMethods()) as any)[method].rows;

function childPhase(phase: string): any {
  const out = execFileSync(process.execPath, ['--max-old-space-size=16384', process.argv[1]], {
    encoding: 'utf8',
    maxBuffer: 1 << 26,
    env: { ...process.env, SCHEDULE_PHASE: phase, SCHEDULE_WORKDIR: WORKDIR },
    stdio: ['ignore', 'pipe', 'inherit'],
  });
  const line = out.split('\n').find((l) => l.startsWith('##JSON##'));
  if (!line) throw new Error(`the ${phase} phase produced no result line:\n${out.slice(-2000)}`);
  return JSON.parse(line.slice(8));
}

// ---------------------------------------------------------------------------
// The fixtures.
// ---------------------------------------------------------------------------

const fxPath = (which: string) => resolve(WORKDIR, `fixture-${which}.json`);
let fxA: any;
let fxB: any;
if (PHASE === 'main') {
  let seedA = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  let seedB = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  if (seedB === seedA) seedB = (seedB + 1) % 1_000_000;
  console.log('=== the SCHEDULE: where to cut, proved at the geometry that runs ===\n');
  console.log('[1] two independent dregg proofs, each accepted by dregg before it was emitted');
  const t = Date.now();
  // ⚑ THE SAME DEGENERATE-DRAW TRAP §3.20 PAID FOR. |D^0| = 2^2, so three query
  // indices collide often, and when two coincide "this half walked another
  // query's index" is not a substitution at all — same rows, same paths, same
  // fold — and the falsifier passes without firing. Fixture A is minted until
  // its indices are PAIRWISE DISTINCT and [6] asserts the premise before using it.
  fxA = mint(seedA);
  let tries = 0;
  while (new Set(fxA.challenges.queryIndices).size !== NQ) {
    if (++tries > 200)
      fail(
        `no seed in 200 gave ${NQ} pairwise-distinct query indices at |D^0| = ` +
          `2^${fxA.shape.logGlobalMaxHeight} — the wrong-query falsifier cannot fire here`,
      );
    seedA = (seedA + 1) % 1_000_000;
    fxA = mint(seedA);
  }
  fxB = mint(seedB);
  writeFileSync(fxPath('a'), JSON.stringify(fxA));
  writeFileSync(fxPath('b'), JSON.stringify(fxB));
  for (const [nm, fx] of [['A', fxA], ['B', fxB]] as const)
    if (fx.kind !== 'dregg-uni-stark-fixture') fail(`fixture ${nm}: the emitter returned ${fx.kind}`);
  if (fxA.knobs.numQueries !== NQ) fail(`the emitter produced ${fxA.knobs.numQueries} queries, not ${NQ}`);
  if (String(fxA.commitments.trace) === String(fxB.commitments.trace))
    fail('the two fixtures share a trace commitment — every splice test would be vacuous');
  ok(
    `two proofs minted + self-verified by dregg's own p3_uni_stark::verify (seeds ${seedA}, ` +
      `${seedB}, ${secs(t)}) — ${fxA.knobs.numQueries} queries, |D^0| = 2^${fxA.shape.logGlobalMaxHeight}`,
  );
  ok(
    `proof A's query indices [${fxA.challenges.queryIndices}] are PAIRWISE DISTINCT ` +
      `(${tries} reseed${tries === 1 ? '' : 's'})`,
  );
} else {
  fxA = JSON.parse(readFileSync(fxPath('a'), 'utf8'));
  fxB = JSON.parse(readFileSync(fxPath('b'), 'utf8'));
}

const SHAPE = shapeOf(fxA, { constraints: minaFixtureConstraints });
const WALK_PLAN = verifyPlan({ ...SHAPE, deriveChallenges: false, constraints: undefined });
const OPTS = { openChunkLanes: OPEN_CHUNK_LANES };

/** ⚑ THESE THREE MOVED TO `DreggProofSchedule.ts` (`chainSideOf`,
 *  `deepStepArgs`, `foldStepArgs`) so the Pasta chain driver
 *  (`scripts/pasta-chain.ts`) uses the SAME ones. A per-script copy of the step
 *  argument order is a second implementation of the step interface, and this
 *  repo has a named class for two shapes that agree today. */
const sideOf = (chain: ReturnType<typeof makeScheduledVerify>, fx: any) =>
  chainSideOf(chain, fx, SHAPE, { claimOf, witnessOf, runQueryInputAndDeep, zetaPointsOf });
const deepArgs = deepStepArgs;
const foldArgs = foldStepArgs;

// ===========================================================================
// PHASE `rows` — every `analyzeMethods` measurement, in its own process.
// ===========================================================================
if (PHASE === 'rows') {
  const mono = await rowsOf(makeDreggProofVerifyProgram(SHAPE).prog, 'verifyDreggProof');
  const C = makeScheduledVerify(SHAPE, OPTS);
  const chain = {
    transcript: await rowsOf(C.prog, 'transcript'),
    deep: await rowsOf(C.prog, 'deep'),
    fold: await rowsOf(C.prog, 'fold'),
  };

  // The carry a step pays when it holds the chunks it READS instead of the whole
  // proof — the deployed number the schedule is priced against, measured by the
  // same probe shape §3.20 used so the two are comparable.
  const deployedLanes = carriedLaneCount(deployedShapeOf(SHAPE, DEPLOYED_COLS));
  const carryProbe = (nWitness: number, nDigests: number) =>
    ZkProgram({
      name: `schedule-carry-${nWitness}-${nDigests}`,
      publicInput: Field,
      publicOutput: Field,
      methods: {
        carry: {
          privateInputs: [
            Provable.Array(Field, Math.max(nWitness, 1)),
            Provable.Array(Field, Math.max(nDigests, 1)),
          ] as any,
          async method(bIn: Field, lanes: Field[], digests: Field[]) {
            for (const l of lanes) assertLaneLt2p31(l);
            // ⚑ ONE hash of the lanes, not two. The first version of this probe
            // called `digestOfLanes` twice and read 11,487 rows too high at the
            // deployed lane count — which is exactly one redundant pack-and-hash
            // (§3.20 measures that at 11,571), and it is why the flat arm below
            // is CROSS-CHECKED against §3.20's recorded 34,566 instead of being
            // read on its own.
            const d = digestOfLanes(lanes, true);
            const rcd = rcdOfDigests([d, ...digests]);
            stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0).assertEquals(bIn);
            return { publicOutput: stepBoundary(rcd, d, Field(3)) };
          },
        },
      },
    });
  const probe = async (w: number, d: number) => rowsOf(carryProbe(w, d), 'carry');

  // A deployed FOLD step: it witnesses the fold chunk (16 commit-phase digests
  // and the final polynomial) plus the challenge set, and forwards every other
  // chunk as a digest.
  const foldChunkLanes = 16 * 8 + SHAPE.knobs.finalPolyLen * 4;
  const bestChunk = 128;
  const nChunks = 3 + Math.ceil((deployedLanes.root - foldChunkLanes - 19) / bestChunk) + 1;
  const scheduledFold = await probe(foldChunkLanes + deployedLanes.challenge, nChunks);
  // ... and a deployed DEEP step under the FLAT digest, which is what §3.20
  // measured at 34,566: every root lane re-witnessed.
  const flatEntry = await probe(deployedLanes.root + deployedLanes.challenge, 0);

  console.log(
    '##JSON##' +
      JSON.stringify({ mono, chain, deployedLanes, scheduledFold, flatEntry, nChunks, foldChunkLanes }),
  );
  process.exit(0);
}

// ===========================================================================
// PHASE `control` — the UNBOUND twin, in its own process.
//
// ⚑ AND IT BUILDS ITS OWN PREDECESSOR, WHICH IS NOT A CONVENIENCE. The chain is
// ONE program, so every predecessor is a `SelfProof` and a proof made by the
// BOUND program does not verify under the unbound program's verification key —
// the first version of this handed the bound `deep` proof across and the control
// refused everything, which would have read as "the binding did it" for the
// wrong reason entirely. So the control proves the transcript and the DEEP half
// with the SAME unbound circuit and splices its own fold: the only difference
// between it and [6] is the three boundary assertions.
// ===========================================================================
if (PHASE === 'control') {
  const C = makeScheduledVerify(SHAPE, OPTS);
  const U: any = C.unbound();
  await U.prog.compile({ cache: NO_CACHE });
  const S = await sideOf(C, fxA);
  const { proof: p0 } = await U.prog.transcript(S.entry, S.claim, S.w[0], S.w[1], S.w[2]);
  const { proof: pd } = await U.prog.deep(p0.publicOutput, p0, Field(0), ...deepArgs(S, 0));
  const bentAlpha = { ...S.w[7], limbs: [S.w[7].limbs[0].add(1), ...S.w[7].limbs.slice(1)] };
  const bentOthers = S.foldOthers.map((d: Field, i: number) => (i === 0 ? d.add(1) : d));
  const cases: [string, any, Field][] = [
    ['alpha', { alphaStark: bentAlpha }, S.deepBoundary(0, S.ro[0])],
    ['digest', { others: bentOthers }, S.deepBoundary(0, S.ro[0])],
    ['garbage-input', undefined, Field(123456789)],
  ];
  const accepted: Record<string, boolean> = {};
  const why: Record<string, string> = {};
  for (const [name, over, bIn] of cases) {
    try {
      await U.prog.fold(bIn, pd, Field(0), Bool(false), ...foldArgs(S, 0, over));
      accepted[name] = true;
    } catch (e: any) {
      accepted[name] = false;
      why[name] = String(e?.message ?? e).split('\n')[0].slice(0, 120);
    }
  }
  console.log('##JSON##' + JSON.stringify({ accepted, why }));
  process.exit(0);
}

// ===========================================================================
// PHASE `main`.
// ===========================================================================

const CHAIN = makeScheduledVerify(SHAPE, OPTS);
const A = await sideOf(CHAIN, fxA);
const BX = await sideOf(CHAIN, fxB);

// ---------------------------------------------------------------------------
console.log('\n[2] the CHUNKED commitment covers exactly what the flat one did');
{
  const flat = rootCommitLanes(A.claim, A.w[0], A.w[1], A.w[2]);
  const cat = A.chunks.flatMap((c: any) => c.lanes);
  if (cat.length !== flat.length)
    fail(`the chunks hold ${cat.length} lanes, the flat digest ${flat.length} — a lane in no chunk`);
  for (let i = 0; i < flat.length; i++)
    if (cat[i].toString() !== flat[i].toString())
      fail(`chunk lane ${i} is not flat lane ${i} — the chunking permuted the commitment`);
  ok(
    `concat(${A.chunks.length} chunks) is ${flat.length} lanes, ELEMENTWISE equal to ` +
      "`rootCommitLanes` — the cheaper commitment covers no less",
  );

  // ⚑ ANTI-VACUITY, PER CHUNK. A chunk whose digest did not move when its
  // preimage moved would make every splice refusal below a refusal of something
  // else. Every chunk is bent, not a sample of them.
  for (const c of A.chunks) {
    if (c.lanes.length === 0) fail(`chunk ${c.id} is empty — it commits to nothing`);
    for (const i of [0, c.lanes.length - 1]) {
      const bent = A.chunks.map((x: any) =>
        x.id === c.id ? { ...x, lanes: x.lanes.map((v: Field, j: number) => (j === i ? v.add(1) : v)) } : x,
      );
      const rcd2 = rcdOfDigests(bent.map((x: any) => digestOfLanes(x.lanes, true)));
      if (rcd2.toString() === A.rcd.toString())
        fail(`bending lane ${i} of chunk ${c.id} left rootCommitDigest unchanged`);
      if (
        stepBoundary(rcd2, A.cd, 1).toString() === stepBoundary(A.rcd, A.cd, 1).toString()
      )
        fail(`bending lane ${i} of chunk ${c.id} moved the digest but not the boundary`);
    }
  }
  ok(
    `bending either end of EVERY one of the ${A.chunks.length} chunks moves rootCommitDigest and ` +
      'the boundary — no chunk is decorative',
  );

  // The chunk digests are a VECTOR, and a vector commitment that ignored order
  // would let a step swap the chunk it read for one it did not.
  const ds = CHAIN.ids.map((id: string) => A.digests.get(id)!);
  const swapped = [...ds];
  [swapped[0], swapped[1]] = [swapped[1], swapped[0]];
  if (rcdOfDigests(swapped).toString() === A.rcd.toString())
    fail('swapping two chunk digests left rootCommitDigest unchanged — the vector is a set');
  ok(`the ${ds.length} chunk digests are ordered — swapping two moves rootCommitDigest`);

  if (A.rcd.toString() === BX.rcd.toString()) fail('the two fixtures share a rootCommitDigest');
  if (A.cd.toString() === BX.cd.toString()) fail('the two fixtures share a challengeDigest');
  ok('the two dregg proofs have different chunk vectors, root digests and entry boundaries');

  // The intra-query boundary must actually depend on the reduced openings, or
  // the cheap cut carries nothing and the fold half is unbound to its own query.
  // ⚑ THE PREMISE [6]'s INTRA-QUERY SPLICE RESTS ON, ASSERTED RATHER THAN
  // ASSUMED. At `degree_bits = 1` every reduced opening is the same constant
  // (the DEEP quotient of a linear polynomial), so "the fold half was handed
  // another query's reduced openings" would substitute a value for itself and
  // the falsifier would pass without firing — the §3.19 [8] shape again.
  const roSeen = new Set(A.ro.map((r: BbExt[]) => r.map((v) => v.limbs.map((l) => l.toString()).join(',')).join('|')));
  if (roSeen.size !== NQ)
    fail(
      `the ${NQ} queries produced only ${roSeen.size} distinct reduced openings at degree_bits ` +
        `${SHAPE.air.degreeBits} — the DEEP quotient is constant here and the intra-query splice ` +
        'in [6] would be substituting a value for itself',
    );
  const seen = new Set<string>();
  for (let q = 0; q < NQ; q++) seen.add(A.deepBoundary(q, A.ro[q]).toString());
  if (seen.size !== NQ)
    fail('two queries produce the same DEEP boundary — the intra-query cut carries nothing');
  for (let q = 0; q < NQ; q++)
    if (A.deepBoundary(q, A.ro[q]).toString() === A.deepBoundary(q, A.ro[(q + 1) % NQ]).toString())
      fail(`query ${q}'s DEEP boundary does not move when its reduced openings do`);
  ok(
    `the ${NQ} queries give ${roSeen.size} DISTINCT reduced openings at degree_bits ` +
      `${SHAPE.air.degreeBits} — so [6]'s intra-query splice is a substitution and not an identity`,
  );
  ok(
    `the ${NQ} intra-query boundaries are distinct AND each moves when its reduced openings are ` +
      "replaced by another query's — the cheap cut carries the fold value it claims to",
  );
}

// ---------------------------------------------------------------------------
console.log('\n[3] the SCHEDULER on the DEPLOYED geometry');
let SCHED: any;
{
  const shD = deployedShapeOf(SHAPE, DEPLOYED_COLS);
  const lanes = carriedLaneCount(shD);
  const probe = deployedProgram(SHAPE, { openChunkLanes: 128 });
  const drift = probe.totalRows / MEASURED.deployedTotal - 1;
  if (Math.abs(drift) > 0.01)
    fail(
      `the atom model sums to ${n(probe.totalRows)} rows against §3.19's measured ` +
        `${n(MEASURED.deployedTotal)} — ${(drift * 100).toFixed(2)}%, which is a model of a ` +
        'different circuit',
    );
  ok(
    `the atom model is ${n(probe.atoms.length)} atoms summing to ${n(probe.totalRows)} rows — ` +
      `${(drift * 100).toFixed(2)}% from §3.19's measured ${n(MEASURED.deployedTotal)}, and every ` +
      'row in it is a measured marginal or a sum of them',
  );
  const biggest = Math.max(...probe.atoms.map((a: any) => a.rows));
  ok(
    `the largest indivisible atom is ${n(biggest)} rows — ${((biggest / usableRows(PICKLES_OVERHEAD.aggregationTree)) * 100).toFixed(1)}% ` +
      'of a step, so the schedule is a placement and not a rounding',
  );

  const SIZES = [24, 32, 48, 64, 94, 128, 192, 256, 384, 512];
  const rows: any[] = [];
  for (const [label, overhead] of [
    ['1 (a straight chain)', PICKLES_OVERHEAD.straightChain],
    ['2 (an aggregation tree)', PICKLES_OVERHEAD.aggregationTree],
  ] as const) {
    const u = usableRows(overhead);
    const best = bestSchedule(SHAPE, u, SIZES);
    const flatProg = deployedProgram(SHAPE, { openChunkLanes: 1_000_000 });
    const flatDp = schedule(flatProg, u);
    const naiveCut = scheduleFlatCarry(flatProg, u, lanes.root);
    const noCarry = Math.ceil(probe.totalRows / u);
    if (best.sched.maxStepRows > u)
      fail(`a scheduled step spends ${n(best.sched.maxStepRows)} of ${n(u)} usable rows`);
    if (best.sched.steps >= flatDp.steps)
      fail('the chunked commitment bought nothing against the flat one — the mechanism is idle');
    if (flatDp.steps >= naiveCut.steps)
      fail('placement bought nothing against cutting at the ceiling — the DP is idle');
    rows.push({ label, u, best, flatDp, naiveCut, noCarry });
    console.log(
      `    max_proofs_verified = ${label}, ${n(u)} usable\n` +
        `      cut at the ceiling, FLAT digest (what §3.20's band tops out at) ${n(naiveCut.steps).padStart(6)} steps\n` +
        `      SCHEDULED, flat digest — placement alone                        ${n(flatDp.steps).padStart(6)} steps\n` +
        `      SCHEDULED, CHUNKED digest — this leg                            ${n(best.sched.steps).padStart(6)} steps  ` +
        `(chunk ${best.chunkLanes} lanes, carry ${((best.sched.carryRows / probe.totalRows) * 100).toFixed(2)}%, ` +
        `slack ${((best.sched.slackRows / probe.totalRows) * 100).toFixed(2)}%)\n` +
        `      the carry ignored entirely (what §4.2 quotes)                   ${n(noCarry).padStart(6)} steps`,
    );
  }
  const two = rows[1];
  SCHED = { one: rows[0], two, modelRows: probe.totalRows };
  const c = two.best.sched.census;
  ok(
    `the placement rule the DP found: ${n(c.insideQuery)} of its ${n(two.best.sched.steps - 1)} ` +
      `boundaries land INSIDE a query, ${n(c.inTranscript)} inside the transcript block and ` +
      `${n(c.atQueryEntry)} at a query ENTRY — the expensive cut is the one it does not make`,
  );
  ok(
    `the deployed count is ${n(two.best.sched.steps)} work-carrying steps at ` +
      `max_proofs_verified = 2, against §3.20's band of 564-1,838 — ` +
      `${n(two.best.sched.steps - 564)} above its optimistic end and ` +
      `${n(1838 - two.best.sched.steps)} below its pessimistic one`,
  );
  ok(
    `and it decomposes: placement alone is ${(two.naiveCut.steps / two.flatDp.steps).toFixed(2)}x, ` +
      `the chunked commitment a further ${(two.flatDp.steps / two.best.sched.steps).toFixed(2)}x, ` +
      `${(two.naiveCut.steps / two.best.sched.steps).toFixed(2)}x together`,
  );
}

// ---------------------------------------------------------------------------
console.log('\n[4] the geometry that FORCES a chain, and the chain that fits it');
let M: any;
{
  const t = Date.now();
  M = childPhase('rows');
  console.log(`    (measured in a child process, ${secs(t)})`);
  if (M.mono <= MEASURED_COMPILE_WALL)
    fail(
      `${n(M.mono)} rows is under the ${n(MEASURED_COMPILE_WALL)} rows §3.19 watched compile() ` +
        'REFUSE, so "it does not fit" would rest on the domain size alone',
    );
  ok(
    `the one-step assembly at ${NQ} queries is ${n(M.mono)} rows = ` +
      `${(M.mono / KIMCHI_ROWS).toFixed(2)}x the 2^16 domain and past the ${n(MEASURED_COMPILE_WALL)} ` +
      'rows §3.19 watched compile() refuse — this proof has NO one-step verifier',
  );
  const steps = [M.chain.transcript, M.chain.deep, ...Array.from({ length: NQ - 1 }, () => M.chain.deep), M.chain.fold];
  for (const r of [M.chain.transcript, M.chain.deep, M.chain.fold])
    if (r >= KIMCHI_ROWS) fail(`a step is ${n(r)} rows, past the ${n(KIMCHI_ROWS)}-row domain`);
  void steps;
  const total = M.chain.transcript + NQ * (M.chain.deep + M.chain.fold);
  console.log(
    `    transcript ${n(M.chain.transcript)} + ${NQ}x (deep ${n(M.chain.deep)} + fold ` +
      `${n(M.chain.fold)}) = ${n(total)} rows over ${scheduledSteps(NQ)} steps from ONE verification key`,
  );
  ok(
    `every one of the ${scheduledSteps(NQ)} steps FITS — largest ` +
      `${n(Math.max(M.chain.transcript, M.chain.deep, M.chain.fold))} rows = ` +
      `${((Math.max(M.chain.transcript, M.chain.deep, M.chain.fold) / KIMCHI_ROWS) * 100).toFixed(1)}% of the domain`,
  );
  if (M.chain.fold >= M.chain.deep)
    fail(
      'the fold half is no cheaper than the DEEP half, so the asymmetry the whole schedule rests ' +
        'on is not there',
    );
  ok(
    `the FOLD half is ${n(M.chain.deep - M.chain.fold)} rows cheaper than the DEEP half ` +
      `(${((1 - M.chain.fold / M.chain.deep) * 100).toFixed(1)}%) — it never witnesses an opened evaluation`,
  );
  console.log(
    `    a deployed boundary, priced by probe: FLAT entry ${n(M.flatEntry)} rows against a ` +
      `SCHEDULED fold step's ${n(M.scheduledFold)} (${n(M.nChunks)} chunk digests + ` +
      `${n(M.foldChunkLanes)} fold lanes + ${n(M.deployedLanes.challenge)} challenge lanes)`,
  );
  // ⚑ CROSS-CHECK AGAINST §3.20, WHICH MEASURED THE FLAT BOUNDARY AT 34,566.
  // The flat arm of this probe is the same object under a different harness; if
  // the two disagree, one of them is not measuring a boundary and the whole
  // comparison below is between different things.
  const RECORDED_FLAT = 34_566;
  if (Math.abs(M.flatEntry / RECORDED_FLAT - 1) > 0.05)
    fail(
      `this leg's flat-digest boundary probe reads ${n(M.flatEntry)} rows against §3.20's ` +
        `recorded ${n(RECORDED_FLAT)} — more than 5% apart, so the two legs are not pricing the ` +
        'same boundary',
    );
  ok(
    `the flat-digest arm reads ${n(M.flatEntry)} rows against §3.20's recorded ` +
      `${n(RECORDED_FLAT)} (${(((M.flatEntry - RECORDED_FLAT) / RECORDED_FLAT) * 100).toFixed(1)}%) ` +
      '— the two legs price the same boundary',
  );
  if (M.scheduledFold >= M.flatEntry / 4)
    fail(
      `the scheduled carry (${n(M.scheduledFold)}) is not materially below the flat one ` +
        `(${n(M.flatEntry)}) — the chunking is not buying what the schedule spends`,
    );
  ok(
    `the chunked carry is ${(M.flatEntry / M.scheduledFold).toFixed(1)}x cheaper than the flat one ` +
      'at deployed lane counts — measured as circuits, not projected',
  );
}

// ---------------------------------------------------------------------------
console.log(`\n[5] PROVE the scheduled chain — ${scheduledSteps(NQ)} steps, output feeding input`);
const proofs: any[] = [];
{
  let t = Date.now();
  const vk = (await CHAIN.prog.compile({ cache: NO_CACHE })).verificationKey;
  console.log(
    `    the whole chain compiled in ${secs(t)} — ONE verification key ` +
      `(${vk.hash.toString().slice(0, 12)}…) for three methods`,
  );

  t = Date.now();
  const { proof: p0 } = await (CHAIN.prog as any).transcript(A.entry, A.claim, A.w[0], A.w[1], A.w[2]);
  if (!(await CHAIN.prog.verify(p0))) fail('the transcript proof does not verify');
  if (p0.publicInput.toString() !== A.entry.toString())
    fail('the transcript proof did not carry the entry boundary the harness computed');
  if (p0.publicOutput.toString() !== stepBoundary(A.rcd, A.cd, 1).toString())
    fail("the transcript step's emitted boundary is not Poseidon(rootCommitDigest, challengeDigest, 1)");
  proofs.push(p0);
  ok(`step 0 (transcript + AIR closing equality + the chunk vector) PROVED in ${secs(t)} and verified`);

  for (let q = 0; q < NQ; q++) {
    const last = q === NQ - 1;
    t = Date.now();
    const prevD = proofs[proofs.length - 1];
    const { proof: pd } = await (CHAIN.prog as any).deep(
      prevD.publicOutput,
      prevD,
      Field(q),
      ...deepArgs(A, q),
    );
    if (!(await CHAIN.prog.verify(pd))) fail(`the deep-${q} proof does not verify`);
    if (pd.publicInput.toString() !== prevD.publicOutput.toString())
      fail(`the DEEP half of query ${q} did not consume its predecessor's emitted boundary`);
    if (pd.publicOutput.toString() !== A.deepBoundary(q, A.ro[q]).toString())
      fail(`the DEEP half of query ${q} did not emit the intra-query boundary the harness computed`);
    proofs.push(pd);
    ok(
      `step ${2 * q + 1} = deep(q=${q}) PROVED in ${secs(t)} — it emits the INTRA-QUERY boundary, ` +
        'carrying the reduced openings and nothing else',
    );

    t = Date.now();
    const { proof: pf } = await (CHAIN.prog as any).fold(
      pd.publicOutput,
      pd,
      Field(q),
      Bool(last),
      ...foldArgs(A, q),
    );
    if (!(await CHAIN.prog.verify(pf))) fail(`the fold-${q} proof does not verify`);
    if (pf.publicInput.toString() !== pd.publicOutput.toString())
      fail(`the fold half of query ${q} did not consume the DEEP half's emitted boundary`);
    proofs.push(pf);
    ok(
      `step ${2 * q + 2} = fold(q=${q}${last ? ', CLOSING' : ''}) PROVED in ${secs(t)} — it read the ` +
        'fold chunk and forwarded every other chunk as a digest',
    );
  }
  const seal = partitionTerminalSeal(A.rcd, CHAIN.nSteps);
  const terminal = proofs[proofs.length - 1];
  if (terminal.publicOutput.toString() !== seal.toString())
    fail(
      'the terminal proof does not carry Poseidon(rootCommitDigest, -, nSteps) — a verifier could ' +
        'not bind the chain to the dregg proof it holds, nor to its length',
    );
  for (const wrong of [CHAIN.nSteps - 1, CHAIN.nSteps + 1])
    if (terminal.publicOutput.toString() === partitionTerminalSeal(A.rcd, wrong).toString())
      fail(`the terminal seal also matches a chain of length ${wrong} — the length is not pinned`);
  ok(
    `the terminal proof carries the CLOSING SEAL (rcd, -, ${CHAIN.nSteps}) — computed by the ` +
      `harness from the dregg proof alone — and NOT the seal for ${CHAIN.nSteps - 1} or ${CHAIN.nSteps + 1}`,
  );
  if (proofs.length !== scheduledSteps(NQ)) fail(`the chain is ${proofs.length} proofs, not ${scheduledSteps(NQ)}`);
  ok(`${proofs.length} proofs, each verified, each publicInput its predecessor's publicOutput`);
}

// ---------------------------------------------------------------------------
console.log('\n[6] the SPLICE is REFUSED — nine attempts, each against a real proof object');
{
  const P: any = CHAIN.prog;
  const p0 = proofs[0]; //  transcript
  const d0 = proofs[1]; //  deep(0)
  const f0 = proofs[2]; //  fold(0)
  const d1 = proofs[3]; //  deep(1)
  const qi = fxA.challenges.queryIndices;
  if (qi[0] === qi[1])
    fail(`queries 0 and 1 both drew index ${qi[0]} — the wrong-openings falsifier would be vacuous`);
  const bentAlpha = { ...A.w[7], limbs: [A.w[7].limbs[0].add(1), ...A.w[7].limbs.slice(1)] };
  const bentPow = A.digests.get('pow')!.add(1);
  const bentOthers = CHAIN.ids
    .filter((id: string) => id !== 'fold')
    .map((id: string) => (id === 'pow' ? bentPow : A.digests.get(id)!));

  const attempts: [string, () => Promise<any>][] = [
    [
      "the fold half of query 0 handed proof B's commit-phase chunk",
      () => P.fold(A.deepBoundary(0, A.ro[0]), d0, Field(0), Bool(false), ...foldArgs(BX, 0)),
    ],
    [
      "the fold half of query 0 handed query 1's reduced openings (the INTRA-QUERY splice)",
      () =>
        P.fold(A.deepBoundary(0, A.ro[0]), d0, Field(0), Bool(false), ...foldArgs(A, 0, { ro: A.ro[1] })),
    ],
    [
      'the fold half re-declaring itself as another query',
      () => P.fold(A.deepBoundary(1, A.ro[1]), d0, Field(1), Bool(false), ...foldArgs(A, 1)),
    ],
    [
      'the DEEP half of query 1 re-declaring itself as query 2 (double-count)',
      () => P.deep(stepBoundary(A.rcd, A.cd, 5), f0, Field(2), ...deepArgs(A, 2)),
    ],
    [
      'a carried CHALLENGE the fold half never reads (alpha_stark) bent',
      () =>
        P.fold(
          stepBoundary(
            A.rcd,
            digestOfLanes(
              [
                ...challengeLanes(WALK_PLAN, { ...A.ch, alphaStark: bentAlpha }),
                ...A.ro[0].flatMap((v: BbExt) => v.limbs),
              ],
              true,
            ),
            2,
          ),
          d0,
          Field(0),
          Bool(false),
          ...foldArgs(A, 0, { alphaStark: bentAlpha }),
        ),
    ],
    [
      'a carried CHUNK DIGEST the fold half never reads (the query PoW witness) bent',
      () =>
        P.fold(
          stepBoundary(
            rcdOfDigests(
              CHAIN.ids.map((id: string) => (id === 'pow' ? bentPow : A.digests.get(id)!)),
            ),
            digestOfLanes([...A.chal, ...A.ro[0].flatMap((v: BbExt) => v.limbs)], true),
            2,
          ),
          d0,
          Field(0),
          Bool(false),
          ...foldArgs(A, 0, { others: bentOthers }),
        ),
    ],
    [
      'a fold half whose predecessor is a FOLD, not its own DEEP half (the alternation)',
      () => P.fold(A.deepBoundary(1, A.ro[1]), f0, Field(1), Bool(false), ...foldArgs(A, 1)),
    ],
    [
      `a query index outside 0..${NQ - 1}`,
      () => P.deep(stepBoundary(A.rcd, A.cd, 2 * NQ + 1), proofs[proofs.length - 1], Field(NQ), ...deepArgs(A, 0)),
    ],
    [
      'a chain closed one step early (isLast set at query 1)',
      () => P.fold(A.deepBoundary(1, A.ro[1]), d1, Field(1), Bool(true), ...foldArgs(A, 1)),
    ],
  ];
  // ⚑ A REFUSAL FOR THE WRONG REASON IS NOT A REFUSAL. Every splice below hands
  // the method arguments of the RIGHT SHAPE and the wrong VALUES, so the only
  // thing that may reject them is a constraint. A `TypeError` from a mis-shaped
  // array would look identical to `catch {}` and would make the whole section a
  // green that measures the harness — the same class as a fault injection that
  // matches nothing.
  const SHAPE_ERROR = /is not a function|Cannot read properti|is not iterable|of undefined|undefined is not|Array length|expects .* arguments/i;
  for (const [what, run] of attempts) {
    const t = Date.now();
    let refused = false;
    let why = '';
    let out: any;
    try {
      out = await run();
    } catch (e: any) {
      refused = true;
      why = String(e?.message ?? e).split('\n')[0].slice(0, 90);
      if (SHAPE_ERROR.test(why))
        fail(
          `'${what}' was rejected by a JAVASCRIPT error, not a constraint: ${why} — the splice ` +
            'never reached the circuit and this check measures the harness',
        );
    }
    if (!refused) {
      // The early close is refused by the SEAL it produces, not by a constraint
      // — say which, rather than pretending they are the same thing.
      const got = out?.proof?.publicOutput?.toString();
      if (what.startsWith('a chain closed') && got !== partitionTerminalSeal(A.rcd, CHAIN.nSteps).toString()) {
        ok(`the chain REFUSES ${what} — it proves, and its seal is NOT the one a verifier checks  [${secs(t)}]`);
        continue;
      }
      fail(`the chain ACCEPTED ${what} — the boundary is a sequence marker, not a binding`);
    }
    // Printing WHY is not decoration: a refusal at 0.0s is a constraint failing
    // during witness generation, and the only way a reader can tell that from a
    // harness accident is to see the message.
    ok(`prove() REFUSES ${what}  [${secs(t)}: ${why}]`);
  }

  const t = Date.now();
  let refused = false;
  try {
    await (CHAIN.prog as any).transcript(BX.entry, A.claim, A.w[0], A.w[1], A.w[2]);
  } catch {
    refused = true;
  }
  if (!refused)
    fail("the transcript step accepted an entry boundary that is not its own proof's — no anchor");
  ok(`prove() REFUSES a transcript entry boundary belonging to a different dregg proof  [${secs(t)}]`);
  void p0;
}

// ---------------------------------------------------------------------------
console.log('\n[7] the CONTROL — the same chain without the boundary assertions ACCEPTS');
{
  // ⚑ WITHOUT THIS, [6] MEASURES NOTHING ATTRIBUTABLE. `alpha_stark` and the
  // query PoW witness are CARRIED and never read by the fold half, so bending
  // them cannot break the fold — and a refusal is the binding only if something
  // shows the unbound circuit would otherwise have accepted.
  const t = Date.now();
  const C = childPhase('control');
  console.log(`    (the unbound twin compiled and run in a child process, ${secs(t)})`);
  const EXPECT = [
    ['a carried challenge (alpha_stark) the fold half never reads, bent', 'alpha'],
    ['a carried chunk digest the fold half never reads, bent', 'digest'],
    ['a public input with no relation to its predecessor', 'garbage-input'],
  ] as const;
  for (const [what, key] of EXPECT) {
    if (!C.accepted[key])
      fail(
        `the UNBOUND twin also refused '${what}' (${C.why?.[key] ?? 'no reason given'}) — so [6]'s ` +
          'refusal is not attributable to the carried digest, and this leg proves nothing about ' +
          'the binding',
      );
    ok(`the unbound twin ACCEPTS ${what} — [6]'s refusal is the CARRY, not the walk`);
  }
}

// ---------------------------------------------------------------------------
console.log('\n[8] the ratchet');
{
  // Row counts and a dynamic program's output are both deterministic, so these
  // are pinned EXACTLY — strictly inside the 2% band, and a figure that moves is
  // a figure whose document is stale.
  const RECORDED: [string, number, number][] = [
    ['the one-step assembly at 3 queries, degree_bits 2', M.mono, 146_951],
    ['the transcript step', M.chain.transcript, 36_716],
    ['the DEEP half', M.chain.deep, 23_481],
    ['the FOLD half', M.chain.fold, 14_095],
    ['a deployed boundary under the FLAT digest', M.flatEntry, 34_555],
    ["a deployed SCHEDULED fold step's carry", M.scheduledFold, 1_402],
    ['deployed root lanes crossing a boundary', M.deployedLanes.root, 9_103],
    ['the atom model total', SCHED.modelRows, 27_497_697],
    ['the SCHEDULED deployed step count, max_proofs_verified = 2', SCHED.two.best.sched.steps, 591],
    ['the SCHEDULED deployed step count, max_proofs_verified = 1', SCHED.one.best.sched.steps, 504],
    ['the same DP against a FLAT digest, mpv = 2', SCHED.two.flatDp.steps, 1_184],
    ['cutting at the ceiling under a flat digest, mpv = 2', SCHED.two.naiveCut.steps, 1_963],
    ['boundaries landing INSIDE a query, mpv = 2', SCHED.two.best.sched.census.insideQuery, 521],
    ['boundaries landing at a query ENTRY, mpv = 2', SCHED.two.best.sched.census.atQueryEntry, 2],
  ];
  let pinned = 0;
  for (const [what, got, want] of RECORDED) {
    if (got !== want)
      fail(
        `${what} moved to ${n(got)} from the recorded ${n(want)} — update the figure and whatever ` +
          'quotes it, in the same commit',
      );
    pinned++;
  }
  ok(`${pinned} recorded figures are as recorded`);
}

console.log('\n=== PARTITION-SCHEDULE PASS ===');

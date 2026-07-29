// THE PARTITION — a dregg proof that does NOT fit in one Pickles step, verified
// by a CHAIN of steps that does.
//
//   npm run partition
//
// §3.19 built one ZkProgram that performs the whole of `p3_uni_stark::verify` on
// a real dregg STARK proof, at 56,927 rows — 86.9% of the 2^16 Pickles step
// domain — and measured the ceiling: the same program at `degree_bits 2` is
// 73,259 rows and `compile()` aborts inside kimchi's wasm. The deployed root
// projects to ~2.75e7 rows and ~500-573 steps.
//
// ⚑ AND NOBODY HAD RUN THE PARTITION. "573 steps" was `ceil(rows / usable)`: an
// arithmetic over a mechanism that did not exist. A step's output had never fed
// the next step, no pair had ever been proved and checked, and the thing that
// makes a sequence of steps a CHAIN rather than N unrelated proofs — the
// step-boundary contract of `Dregg2/Circuit/Emit/KimchiPartition.lean` — was a
// design with no object under it.
//
// This leg is the mechanism. A work step's public input is ONE field element,
//
//     boundary_k = Poseidon(rootCommitDigest, challengeDigest, k)
//
// and this runs it: a 3-query dregg proof — 103,554 rows as one program, 1.58x
// the step domain and well past the row count at which the compiler was watched
// to REFUSE — verified by FOUR chained Pickles steps built from TWO verification
// keys — a transcript step and ONE walk circuit invoked three times — each step
// proved, each verified, with the splice REFUSED and the carry priced.
//
// ⚑ EVERY REFUSAL IS A REAL `prove()` REFUSAL AGAINST REAL PROOF OBJECTS, and
// every "the binding did it" claim is backed by a CONTROL: the same walk circuit
// with the carried-digest checks removed, shown ACCEPTING what the real one
// refuses. §3.15e — a check that cannot be watched saying no is a check nobody
// has measured.
//
// ⚑ WHY THIS RUNS IN THREE PROCESSES. Measuring rows with `analyzeMethods`
// leaves circuit state in kimchi's 32-bit wasm heap, and a `compile()` after
// enough of it aborts in `rust_oom` — measured, and it is why the row phase and
// the control phase are child processes rather than blocks. The numbers they
// return are checked here.
//
// Needs cargo (the emitter) and a 16 GB node heap. ~10 min warm.

import { Bool, Cache, Field, Provable, ZkProgram } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { resolve } from 'node:path';
import { assertLaneLt2p31 } from '../src/Poseidon2BabyBearW16.js';
import {
  claimOf,
  makeDreggProofVerifyProgram,
  minaFixtureConstraints,
  shapeOf,
  verifyPlan,
  witnessOf,
} from '../src/DreggProofVerify.js';
import { DEPLOYED_COLS, deployedShapeOf } from '../src/PartitionSchedule.js';
import {
  GENESIS_CHALLENGE_DIGEST,
  carriedLaneCount,
  challengeLanes,
  digestOfLanes,
  makeChainedProofVerify,
  rootCommitLanes,
  stepBoundary,
  terminalSeal,
} from '../src/DreggProofPartition.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const secs = (t: number) => ((Date.now() - t) / 1000).toFixed(1) + 's';
const n = (x: number) => Math.round(x).toLocaleString();

/** The Kimchi step domain (`kimchi_pasta_basic.ml:16-17`, `Step = Nat.N16`). */
const KIMCHI_ROWS = 65536;
/** §3.19: the row count at which `compile()` was watched to abort. */
const MEASURED_COMPILE_WALL = 73_259;

// ⚑ o1js writes every compiled prover key to `~/.cache/o1js`, and the write goes
// through `caml_pasta_fp_plonk_index_encode` — a serialization INSIDE kimchi's
// 32-bit wasm heap. With several step circuits live it is the first thing to
// abort. Skipping the cache is what lets three step circuits share one process;
// it is named rather than quietly passed.
const NO_CACHE = Cache.None;

// The geometry. `degree_bits 1` is what §3.19 measured; THREE queries is what
// takes it past the step domain — a chain that only ever carried a proof which
// already fitted would be demonstrating nothing — and it is also what makes the
// walk's `step` method get invoked more than once, and the terminal bit both ways.
const DB = 1;
const LB = 1;
const NQ = 3;
const QPOW = 16;

const PHASE = process.env.PARTITION_PHASE ?? 'main';
const WORKDIR = process.env.PARTITION_WORKDIR ?? mkdtempSync(resolve(tmpdir(), 'dregg-partition-'));

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
    const t = Date.now();
    // ⚑ `--bin`, not `--example`: an example compiles DEV-dependencies, which
    // reach `dregg-lean-ffi`, whose build script fails closed while the Lean
    // tree is mid-edit. This leg is about Mina and must not go red for that.
    execFileSync('cargo', ['build', '-p', 'dregg-circuit', '--release', '--bin', 'mina_stark_fixture'], {
      cwd: ROOT,
      stdio: ['ignore', 'ignore', 'inherit'],
    });
    if (PHASE === 'main') console.log(`    emitter built in ${secs(t)}`);
    emitterBuilt = true;
  }
  const out = execFileSync(
    resolve(ROOT, 'target/release/mina_stark_fixture'),
    [DB, LB, NQ, QPOW, seed].map(String).concat(['none']),
    { encoding: 'utf8', maxBuffer: 1 << 26 },
  );
  return JSON.parse(out);
}

const rowsOf = async (prog: any, method: string) =>
  ((await prog.analyzeMethods()) as any)[method].rows;

/** Run this same script in a fresh process, so its wasm heap starts empty. */
function childPhase(phase: string, extraEnv: Record<string, string> = {}): any {
  const out = execFileSync(
    process.execPath,
    ['--max-old-space-size=16384', process.argv[1]],
    {
      encoding: 'utf8',
      maxBuffer: 1 << 26,
      env: { ...process.env, PARTITION_PHASE: phase, PARTITION_WORKDIR: WORKDIR, ...extraEnv },
      stdio: ['ignore', 'pipe', 'inherit'],
    },
  );
  const line = out.split('\n').find((l) => l.startsWith('##JSON##'));
  if (!line) throw new Error(`the ${phase} phase produced no result line:\n${out.slice(-2000)}`);
  return JSON.parse(line.slice(8));
}

// ---------------------------------------------------------------------------
// The fixtures. Minted once by `main`, read by every phase, so all three agree
// on the proof under discussion.
// ---------------------------------------------------------------------------

const fxPath = (which: string) => resolve(WORKDIR, `fixture-${which}.json`);
let fxA: any;
let fxB: any;
if (PHASE === 'main') {
  let seedA = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  let seedB = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  if (seedB === seedA) seedB = (seedB + 1) % 1_000_000;
  console.log('=== the PARTITION: a dregg proof too big for one Pickles step, CHAINED ===\n');
  console.log('[1] two independent dregg proofs, each accepted by dregg before it was emitted');
  const t = Date.now();
  // ⚑ A FALSIFIER THAT IS BLIND AT A DEGENERATE DRAW, AND IT WENT GREEN BY
  // ACCIDENT ONCE. |D^0| = 2^2, so three query indices collide often — and when
  // two of them are EQUAL, "step 2 walked query 2 instead of its own query 1" is
  // not a substitution at all: the rows, the paths and the fold are the same
  // object, and the skip falsifier in [6] passes without firing. A run drew
  // [0,0,0] and did exactly that. So fixture A is minted until its indices are
  // PAIRWISE DISTINCT, and [6] asserts that premise before using it. The same
  // shape as the `degree_bits 1` boundary-constraint blindness in §3.19 [8]:
  // the falsifier is fine, the PARAMETER was not.
  fxA = mint(seedA);
  let tries = 0;
  while (new Set(fxA.challenges.queryIndices).size !== NQ) {
    if (++tries > 200)
      fail(
        `no seed in 200 gave ${NQ} pairwise-distinct query indices at |D^0| = ` +
          `2^${fxA.shape.logGlobalMaxHeight} — the skip falsifier cannot fire at this geometry`,
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
  ok(
    `two proofs minted + self-verified by dregg's own p3_uni_stark::verify ` +
      `(seeds ${seedA}, ${seedB}, ${secs(t)}) — degree_bits ${fxA.shape.degreeBits}, ` +
      `${fxA.knobs.numQueries} queries, ${fxA.shape.layers} fold layer(s), |D^0| = 2^${fxA.shape.logGlobalMaxHeight}`,
  );
  // Two proofs whose challenges coincided would make every splice below vacuous.
  if (String(fxA.challenges.zeta) === String(fxB.challenges.zeta))
    fail('the two fixtures drew the same zeta — every splice test would be vacuous');
  if (String(fxA.commitments.trace) === String(fxB.commitments.trace))
    fail('the two fixtures share a trace commitment — every splice test would be vacuous');
  ok('the two proofs differ in their trace commitment AND in every challenge drawn from it');
  ok(
    `proof A's ${NQ} query indices [${fxA.challenges.queryIndices}] are PAIRWISE DISTINCT ` +
      `(${tries} reseed${tries === 1 ? '' : 's'}) — without that the "step walked the wrong query" ` +
      'falsifier in [6] cannot fire',
  );
} else {
  fxA = JSON.parse(readFileSync(fxPath('a'), 'utf8'));
  fxB = JSON.parse(readFileSync(fxPath('b'), 'utf8'));
}

const SHAPE = shapeOf(fxA, { constraints: minaFixtureConstraints });
const WALK_PLAN = verifyPlan({ ...SHAPE, deriveChallenges: false, constraints: undefined });

/** Everything the harness needs about one fixture, computed with the SAME
 *  functions the circuit calls — there is no second implementation of the
 *  boundary anywhere in this leg. */
function sideOf(fx: any, Claim: any, pack = true) {
  const claim = claimOf(fx, Claim);
  const w = witnessOf(fx, SHAPE);
  const ch = { alphaStark: w[7], zeta: w[8], friAlpha: w[9], betas: w[10], queryBits: w[11] };
  const rcd = digestOfLanes(rootCommitLanes(claim, w[0], w[1], w[2]), pack);
  const cd = digestOfLanes(challengeLanes(WALK_PLAN, ch), pack);
  return { claim, w, ch, rcd, cd, entry: stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0) };
}

/** The carried + own-query arguments a walk method takes, for query `q`. */
const walkTail = (side: any, q: number, over?: { alphaStark?: any; queryPow?: Field }) => [
  side.claim,
  side.w[0],
  side.w[1],
  over?.queryPow ?? side.w[2],
  over?.alphaStark ?? side.w[7],
  side.w[8],
  side.w[9],
  side.w[10],
  side.w[11],
  [side.w[3][q]],
  [side.w[4][q]],
  [side.w[5][q]],
  [side.w[6][q]],
];

// ===========================================================================
// PHASE `rows` — every `analyzeMethods` measurement, in its own process.
// ===========================================================================
if (PHASE === 'rows') {
  const mono = await rowsOf(makeDreggProofVerifyProgram(SHAPE).prog, 'verifyDreggProof');
  const chains: any = {};
  for (const pack of [true, false]) {
    const C = makeChainedProofVerify(SHAPE, { pack });
    chains[pack ? 'packed' : 'unpacked'] = {
      step0: await rowsOf(C.step0, 'transcriptAndAir'),
      first: await rowsOf(C.walk, 'first'),
      step: await rowsOf(C.walk, 'step'),
    };
  }

  // The deployed FRI geometry (§1.2) carrying the deployed COLUMN count (§1.3:
  // 940 main + 175 preprocessed, each opened at two points).
  // ⚑ ONE DEFINITION, SHARED WITH §3.21's SCHEDULER. The schedule is priced
  // against the lane count this leg MEASURES a boundary at; two copies of the
  // deployed shape that agree today are two that will disagree later, and the
  // 9,103 in [10]'s ratchet is what both are pinned to.
  const deployedLanes = carriedLaneCount(deployedShapeOf(SHAPE, DEPLOYED_COLS));
  const fixtureLanes = carriedLaneCount(SHAPE);

  /** A step's carry, as a circuit and nothing else: re-witness `nRoot + nChal`
   *  lanes, range-check them (a re-witnessed lane is unconstrained until it is),
   *  pack, hash, and emit the boundary hashes a walk step computes. */
  const carryProbe = (nRoot: number, nChal: number, withRangeChecks: boolean) =>
    ZkProgram({
      name: `carry-probe-${nRoot}-${nChal}-${withRangeChecks ? 'rc' : 'norc'}`,
      publicInput: Field,
      publicOutput: Field,
      methods: {
        carry: {
          privateInputs: [Provable.Array(Field, nRoot), Provable.Array(Field, nChal)] as any,
          async method(bIn: Field, rootL: Field[], chalL: Field[]) {
            if (withRangeChecks) {
              for (const l of rootL) assertLaneLt2p31(l);
              for (const l of chalL) assertLaneLt2p31(l);
            }
            const rcd = digestOfLanes(rootL, true);
            const cd = digestOfLanes(chalL, true);
            stepBoundary(rcd, cd, Field(2)).assertEquals(bIn);
            stepBoundary(rcd, GENESIS_CHALLENGE_DIGEST, 0).assertEquals(bIn);
            return { publicOutput: stepBoundary(rcd, cd, Field(3)) };
          },
        },
      },
    });
  const probe = async (nRoot: number, nChal: number, rc: boolean) =>
    rowsOf(carryProbe(nRoot, nChal, rc), 'carry');

  // Three sizes, so the linearity the projection rests on is CHECKED rather than
  // assumed — a per-lane price read off two points cannot see a non-linear term.
  const sizes = [fixtureLanes.root, 1024, deployedLanes.root];
  const probes: number[] = [];
  for (const s of sizes) probes.push(await probe(s, deployedLanes.challenge, true));
  const probeNoRc = await probe(deployedLanes.root, deployedLanes.challenge, false);

  console.log(
    '##JSON##' +
      JSON.stringify({ mono, chains, deployedLanes, fixtureLanes, sizes, probes, probeNoRc }),
  );
  process.exit(0);
}

// ===========================================================================
// PHASE `control` — the UNBOUND twin, in its own process, fed the real step-0
// proof through the filesystem. That the proof survives the crossing is not
// incidental: a chain of hundreds of steps is proved across processes, not in
// one.
// ===========================================================================
if (PHASE === 'control') {
  const C = makeChainedProofVerify(SHAPE, {});
  await C.step0.compile({ cache: NO_CACHE });
  const unbound: any = C.unboundWalk();
  await unbound.compile({ cache: NO_CACHE });
  const p0 = await (C.Step0Proof as any).fromJSON(
    JSON.parse(readFileSync(resolve(WORKDIR, 'step0-proof.json'), 'utf8')),
  );
  const A = sideOf(fxA, C.Claim);
  const bentAlpha = { ...A.w[7], limbs: [A.w[7].limbs[0].add(1), ...A.w[7].limbs.slice(1)] };
  const cases: [string, any, Field][] = [
    ['alpha', { alphaStark: bentAlpha }, stepBoundary(A.rcd, A.cd, 1)],
    ['querypow', { queryPow: A.w[2].add(1) }, stepBoundary(A.rcd, A.cd, 1)],
    ['garbage-input', undefined, Field(123456789)],
  ];
  const accepted: Record<string, boolean> = {};
  for (const [name, over, bIn] of cases) {
    try {
      await unbound.first(bIn, p0, Bool(false), ...walkTail(A, 0, over));
      accepted[name] = true;
    } catch (e) {
      accepted[name] = false;
    }
  }
  console.log('##JSON##' + JSON.stringify({ accepted }));
  process.exit(0);
}

// ===========================================================================
// PHASE `main`.
// ===========================================================================

// ---------------------------------------------------------------------------
console.log('\n[2] the geometry that FORCES a chain — one step is not an option here');
let M: any;
{
  const t = Date.now();
  M = childPhase('rows');
  console.log(`    (measured in a child process, ${secs(t)})`);
  console.log(`    the one-step assembly at ${NQ} queries: ${n(M.mono)} rows`);
  if (M.mono <= KIMCHI_ROWS)
    fail(
      `${n(M.mono)} rows still fits the ${n(KIMCHI_ROWS)}-row step domain — this leg would be ` +
        'chaining something that did not need chaining. Raise the query count.',
    );
  if (M.mono <= MEASURED_COMPILE_WALL)
    fail(
      `${n(M.mono)} rows is under the ${n(MEASURED_COMPILE_WALL)}-row geometry §3.19 watched the ` +
        'compiler REFUSE, so "it does not fit" would rest on the domain size alone',
    );
  ok(
    `${n(M.mono)} rows = ${(M.mono / KIMCHI_ROWS).toFixed(2)}x the 2^16 step domain, and past the ` +
      `${n(MEASURED_COMPILE_WALL)} rows §3.19 watched compile() refuse — this proof has NO one-step verifier`,
  );
}

// ---------------------------------------------------------------------------
console.log('\n[3] the boundary contract, and it is not a constant');
{
  const C = makeChainedProofVerify(SHAPE, {});
  const A = sideOf(fxA, C.Claim);
  const Bx = sideOf(fxB, C.Claim);

  // ⚑ ANTI-VACUITY, AND IT IS WHY THE REFUSALS IN [6] MEAN ANYTHING. A boundary
  // that did not move when its preimage moved would make every splice refusal a
  // refusal of something else. Each REGION of each preimage is bent by one lane
  // and the boundary is required to move — the §3.15e lesson that a polarity
  // comparing only some regions cannot see a bend in the others, applied to the
  // carrier.
  const lanesRoot = rootCommitLanes(A.claim, A.w[0], A.w[1], A.w[2]);
  const lanesChal = challengeLanes(WALK_PLAN, A.ch);
  const bend = (ls: Field[], i: number) => ls.map((v, j) => (j === i ? v.add(1) : v));
  const nb = C.planHead.nBatches * 8;
  const regions: [string, Field[], number][] = [
    ['the trace commitment', lanesRoot, 0],
    ['a commit-phase commitment', lanesRoot, nb],
    ['a final-polynomial coefficient', lanesRoot, nb + SHAPE.knobs.layers * 8],
    ['a claimed opened evaluation', lanesRoot, lanesRoot.length - 2],
    ['the query PoW witness', lanesRoot, lanesRoot.length - 1],
    ['alpha_stark', lanesChal, 0],
    ['zeta', lanesChal, 4],
    ['the FRI alpha', lanesChal, 8],
    ['a fold challenge beta', lanesChal, 12],
    ['a derived query index', lanesChal, lanesChal.length - 1],
  ];
  for (const [label, ls, i] of regions) {
    const isRoot = ls === lanesRoot;
    const d0 = digestOfLanes(ls, true);
    const d1 = digestOfLanes(bend(ls, i), true);
    if (d0.toString() === d1.toString())
      fail(`bending ${label} (lane ${i}) left the ${isRoot ? 'root' : 'challenge'} digest unchanged`);
    const b0 = isRoot ? stepBoundary(d0, A.cd, 1) : stepBoundary(A.rcd, d0, 1);
    const b1 = isRoot ? stepBoundary(d1, A.cd, 1) : stepBoundary(A.rcd, d1, 1);
    if (b0.toString() === b1.toString()) fail(`bending ${label} moved the digest but not the boundary`);
  }
  ok(`bending any of ${regions.length} carried regions moves the boundary — the carrier is not a constant`);

  // The step INDEX is the third slot, and it is what forbids the chain
  // double-counting or skipping a step.
  const seen = new Set<string>();
  for (let k = 0; k <= C.nSteps; k++) seen.add(stepBoundary(A.rcd, A.cd, k).toString());
  if (seen.size !== C.nSteps + 1)
    fail('two step indices give the same boundary for one proof and one transcript — the index is dead');
  ok(`the same proof and transcript at ${C.nSteps + 1} different step indices are ${seen.size} different boundaries`);

  // The entry and the closing seal are the two ends a verifier can compute.
  if (A.entry.toString() === terminalSeal(A.rcd, C.nSteps).toString())
    fail('the entry boundary and the terminal seal coincide — a chain of length 0 would close');
  ok(
    `the chain's two verifier-computable ends — entry (rcd, -, 0) and seal (rcd, -, ${C.nSteps}) — ` +
      'are distinct, so a zero-length chain cannot close',
  );

  if (A.rcd.toString() === Bx.rcd.toString()) fail('the two fixtures share a rootCommitDigest');
  if (A.cd.toString() === Bx.cd.toString()) fail('the two fixtures share a challengeDigest');
  ok('the two dregg proofs have different root, challenge and entry boundaries');

  // ⚑ THE PACKING IS LOSSLESS, SHOWN RATHER THAN ARGUED. Eight 31-bit lanes into
  // one 254-bit Pasta field is injective only if the lanes really are 31-bit; a
  // collision here would make the carry measurement a price for an unsound
  // carrier.
  const distinct = new Set<string>();
  for (let i = 0; i < lanesRoot.length; i++)
    distinct.add(digestOfLanes(bend(lanesRoot, i), true).toString());
  if (distinct.size !== lanesRoot.length)
    fail(
      `${lanesRoot.length} single-lane bends produced only ${distinct.size} distinct packed digests ` +
        '— the packing is not injective and the carrier is unsound',
    );
  ok(`all ${lanesRoot.length} single-lane bends give distinct PACKED digests — the packing loses nothing`);
}

// ---------------------------------------------------------------------------
console.log('\n[4] the split, and what the carry costs');
let carryPacked = 0;
let carryUnpacked = 0;
let stepRows: number[] = [];
{
  for (const key of ['packed', 'unpacked'] as const) {
    const c = M.chains[key];
    // The chain is `step0` once, `walk.first` once and `walk.step` NQ-1 times —
    // the same circuit, so the same rows, which is the whole point of a uniform
    // walk VK.
    const all = [c.step0, c.first, ...Array.from({ length: NQ - 1 }, () => c.step)];
    const sum = all.reduce((a: number, b: number) => a + b, 0);
    const carry = sum - M.mono;
    if (key === 'packed') {
      stepRows = [c.step0, c.first, c.step];
      carryPacked = carry;
    } else carryUnpacked = carry;
    console.log(
      `    ${key.padEnd(8)}: step0 ${n(c.step0)} + walk.first ${n(c.first)} + ` +
        `${NQ - 1}x walk.step ${n(c.step)} = ${n(sum)} rows over ${NQ + 1} steps, ` +
        `carry ${n(carry)} (${((carry / M.mono) * 100).toFixed(1)}%)`,
    );
    for (const r of all)
      if (r >= KIMCHI_ROWS) fail(`a step is ${n(r)} rows, past the ${n(KIMCHI_ROWS)}-row domain`);
  }
  if (carryPacked <= 0)
    fail(
      `the split came out ${n(carryPacked)} rows CHEAPER than the one-step program — a boundary ` +
        'that costs nothing is a boundary that is not there',
    );
  if (carryUnpacked <= carryPacked)
    fail('hashing the raw lanes came out no dearer than packing them — the packing measures nothing');
  const biggest = Math.max(...stepRows);
  ok(
    `${NQ + 1} steps from TWO verification keys, largest ${n(biggest)} rows = ` +
      `${((biggest / KIMCHI_ROWS) * 100).toFixed(1)}% of the domain — every step FITS`,
  );
  ok(
    `the carry costs ${n(carryPacked)} rows over the whole chain ` +
      `(${((carryPacked / M.mono) * 100).toFixed(2)}%), ${n(carryPacked / NQ)} rows per boundary crossed`,
  );
  ok(
    `packing 8 lanes to a Pasta field saves ${n(carryUnpacked - carryPacked)} rows ` +
      `(${(carryUnpacked / carryPacked).toFixed(2)}x) — the carrier was chosen by measurement`,
  );
}

// ---------------------------------------------------------------------------
console.log(`\n[5] PROVE the chain — ${NQ + 1} steps, each verified, output feeding input`);
const CHAIN = makeChainedProofVerify(SHAPE, {});
const A = sideOf(fxA, CHAIN.Claim);
const BB = sideOf(fxB, CHAIN.Claim);
const proofs: any[] = [];
{
  let t = Date.now();
  const vk0 = (await CHAIN.step0.compile({ cache: NO_CACHE })).verificationKey;
  console.log(`    step0 compiled in ${secs(t)} (vk ${vk0.hash.toString().slice(0, 12)}…)`);
  t = Date.now();
  const vkw = (await CHAIN.walk.compile({ cache: NO_CACHE })).verificationKey;
  console.log(`    the walk (first/step) compiled in ${secs(t)} (vk ${vkw.hash.toString().slice(0, 12)}…)`);
  if (vk0.hash.toString() === vkw.hash.toString()) fail('step0 and the walk share a verification key');
  ok(`the whole chain is TWO verification keys — one transcript step, one walk step reused ${NQ} times`);

  // -- step 0: the transcript and the AIR closing equality.
  t = Date.now();
  const { proof: p0 } = await (CHAIN.step0 as any).transcriptAndAir(A.entry, A.claim, A.w[0], A.w[1], A.w[2]);
  const t0 = secs(t);
  if (!(await CHAIN.step0.verify(p0))) fail('the step-0 proof does not verify');
  if (p0.publicInput.toString() !== A.entry.toString())
    fail('the step-0 proof did not carry the entry boundary the harness computed');
  if (p0.publicOutput.toString() !== stepBoundary(A.rcd, A.cd, 1).toString())
    fail("step 0's emitted boundary is not Poseidon(rootCommitDigest, challengeDigest, 1)");
  proofs.push(p0);
  ok(`step 0 (transcript + AIR closing equality) PROVED in ${t0} and verified — emits boundary_1`);
  // The control phase needs this proof, and it is a different process.
  writeFileSync(resolve(WORKDIR, 'step0-proof.json'), JSON.stringify(p0.toJSON()));

  // -- the walk, invoked once per query, from ONE circuit.
  for (let k = 1; k <= NQ; k++) {
    const prev = proofs[k - 1];
    const terminal = k === NQ;
    const methodName = k === 1 ? 'first' : 'step';
    const args =
      k === 1
        ? [prev.publicOutput, prev, Bool(terminal), ...walkTail(A, 0)]
        : [prev.publicOutput, prev, Field(k), Bool(terminal), ...walkTail(A, k - 1)];
    t = Date.now();
    const { proof } = await (CHAIN.walk as any)[methodName](...args);
    const tp = secs(t);
    if (!(await CHAIN.walk.verify(proof))) fail(`the step-${k} proof does not verify`);
    if (proof.publicInput.toString() !== prev.publicOutput.toString())
      fail(`step ${k} did not consume step ${k - 1}'s emitted boundary`);
    proofs.push(proof);
    ok(
      `step ${k} = walk.${methodName}(k=${k}, query ${k - 1}${terminal ? ', CLOSING' : ''}) PROVED in ` +
        `${tp} and verified — it consumed step ${k - 1}'s OUTPUT as its INPUT`,
    );
  }

  // -- the chain's single external check.
  const seal = terminalSeal(A.rcd, CHAIN.nSteps);
  const terminalProof = proofs[proofs.length - 1];
  if (terminalProof.publicOutput.toString() !== seal.toString())
    fail(
      'the terminal proof does not carry Poseidon(rootCommitDigest, -, nSteps) — a verifier could ' +
        'not bind the chain to the dregg proof it holds, nor to its length',
    );
  ok(
    `the terminal proof carries the CLOSING SEAL (rcd, -, ${CHAIN.nSteps}) — computed by the ` +
      'harness from the dregg proof alone, and it matches',
  );
  // A seal at any other length must NOT match, or the chain's length is unpinned.
  for (const wrong of [CHAIN.nSteps - 1, CHAIN.nSteps + 1])
    if (terminalProof.publicOutput.toString() === terminalSeal(A.rcd, wrong).toString())
      fail(`the terminal seal also matches a chain of length ${wrong} — the length is not pinned`);
  ok(`the same seal does NOT match a chain of length ${CHAIN.nSteps - 1} or ${CHAIN.nSteps + 1}`);
  ok(`the carried challengeDigest commits to p3's own query indices [${fxA.challenges.queryIndices}]`);
}

// ---------------------------------------------------------------------------
console.log('\n[6] the SPLICE is REFUSED — eight attempts, each with a real proof object');
{
  const walk: any = CHAIN.walk;
  const p0 = proofs[0];
  const p1 = proofs[1];
  const p2 = proofs[2];
  const bentAlpha = { ...A.w[7], limbs: [A.w[7].limbs[0].add(1), ...A.w[7].limbs.slice(1)] };
  const bentPow = A.w[2].add(1);
  const cdAlphaBent = digestOfLanes(challengeLanes(WALK_PLAN, { ...A.ch, alphaStark: bentAlpha }), true);
  const rcdPowBent = digestOfLanes(rootCommitLanes(A.claim, A.w[0], A.w[1], bentPow), true);
  // Pre-flight: a bend that did not move its digest would make the refusal
  // attributable to something else entirely.
  if (cdAlphaBent.toString() === A.cd.toString()) fail('bending alpha_stark did not move the challenge digest');
  if (rcdPowBent.toString() === A.rcd.toString()) fail('bending the query PoW witness did not move the root digest');
  // The skip falsifier substitutes query 2's opening for query 1's. If the two
  // drew the same index they are the same object and it tests nothing.
  const qi = fxA.challenges.queryIndices;
  if (qi[1] === qi[2])
    fail(`queries 1 and 2 both drew index ${qi[1]} — the skip falsifier below would be vacuous`);

  const attempts: [string, () => Promise<any>][] = [
    [
      'a step-0 proof over dregg proof A, and everything else from dregg proof B',
      () => walk.first(stepBoundary(BB.rcd, BB.cd, 1), p0, Bool(false), ...walkTail(BB, 0)),
    ],
    [
      "proof A's boundary and predecessor, but proof B's witness",
      () => walk.first(stepBoundary(A.rcd, A.cd, 1), p0, Bool(false), ...walkTail(BB, 0)),
    ],
    [
      'a carried CHALLENGE the walk never reads (alpha_stark) bent',
      () =>
        walk.first(stepBoundary(A.rcd, cdAlphaBent, 1), p0, Bool(false), ...walkTail(A, 0, { alphaStark: bentAlpha })),
    ],
    [
      'a carried PROOF DATUM the walk never reads (the query PoW witness) bent',
      () =>
        walk.first(stepBoundary(rcdPowBent, A.cd, 1), p0, Bool(false), ...walkTail(A, 0, { queryPow: bentPow })),
    ],
    [
      'step 2 re-declaring itself as step 3 (double-count)',
      () => walk.step(stepBoundary(A.rcd, A.cd, 3), p1, Field(3), Bool(false), ...walkTail(A, 1)),
    ],
    [
      'step 2 walking query 2 instead of its own query 1 (skip)',
      () => walk.step(p1.publicOutput, p1, Field(2), Bool(false), ...walkTail(A, 2)),
    ],
    [
      `a step index outside 1..${NQ}`,
      () =>
        walk.step(stepBoundary(A.rcd, A.cd, NQ + 1), p2, Field(NQ + 1), Bool(false), ...walkTail(A, NQ - 1)),
    ],
    [
      'a chain closed one step early (isLast set at step 2)',
      () => walk.step(p1.publicOutput, p1, Field(2), Bool(true), ...walkTail(A, 1)),
    ],
  ];
  for (const [what, run] of attempts) {
    const t = Date.now();
    let refused = false;
    let out: any;
    try {
      out = await run();
    } catch {
      refused = true;
    }
    if (!refused) {
      // The last case is REFUSED only by the seal it produces, not by a
      // constraint — say which, rather than pretending they are the same thing.
      const got = out?.proof?.publicOutput?.toString();
      if (what.startsWith('a chain closed') && got !== terminalSeal(A.rcd, CHAIN.nSteps).toString()) {
        ok(`the chain REFUSES ${what} — it proves, and its seal is NOT the one a verifier checks  [${secs(t)}]`);
        continue;
      }
      fail(`the chain ACCEPTED ${what} — the boundary is a sequence marker, not a binding`);
    }
    ok(`prove() REFUSES ${what}  [${secs(t)}]`);
  }

  // And the head cannot lie about its own entry either.
  {
    const t = Date.now();
    let refused = false;
    try {
      await (CHAIN.step0 as any).transcriptAndAir(BB.entry, A.claim, A.w[0], A.w[1], A.w[2]);
    } catch {
      refused = true;
    }
    if (!refused) fail("step 0 accepted an entry boundary that is not its own proof's — the chain has no anchor");
    ok(`prove() REFUSES a step-0 entry boundary belonging to a different dregg proof  [${secs(t)}]`);
  }
}

// ---------------------------------------------------------------------------
console.log('\n[7] the CONTROL — the same walk without the carried-digest checks ACCEPTS');
{
  // ⚑ WITHOUT THIS, [6] MEASURES NOTHING ATTRIBUTABLE. Refusals are consistent
  // with "the walk was broken by the bend". The unbound twin is the SAME circuit
  // against the SAME predecessor type with the three boundary assertions
  // removed; that it accepts what the bound one refused makes the refusal the
  // binding and nothing else.
  const t = Date.now();
  const C = childPhase('control');
  console.log(`    (the unbound twin compiled and run in a child process, ${secs(t)})`);
  const EXPECT = [
    ['a carried challenge (alpha_stark) bent', 'alpha'],
    ['a carried proof datum (query PoW witness) bent', 'querypow'],
    ['a public input with no relation to its predecessor', 'garbage-input'],
  ] as const;
  for (const [what, key] of EXPECT) {
    if (!C.accepted[key])
      fail(
        `the UNBOUND twin also refused '${what}' — so [6]'s refusal is not attributable to the ` +
          'carried digest, and this leg proves nothing about the binding',
      );
    ok(`the unbound twin ACCEPTS ${what} — [6]'s refusal is the CARRY, not the walk`);
  }
}

// ---------------------------------------------------------------------------
console.log('\n[8] what a boundary costs at DEPLOYED geometry — measured, not extrapolated');
let deployedCarry = 0;
{
  console.log(
    `    lanes crossing ONE deployed boundary: ${n(M.deployedLanes.root)} root + ` +
      `${n(M.deployedLanes.challenge)} challenge = ${n(M.deployedLanes.root + M.deployedLanes.challenge)}`,
  );
  for (let i = 0; i < M.sizes.length; i++)
    console.log(`    the carry circuit at ${n(M.sizes[i]).padStart(6)} root lanes: ${n(M.probes[i]).padStart(7)} rows`);
  const s01 = (M.probes[1] - M.probes[0]) / (M.sizes[1] - M.sizes[0]);
  const s12 = (M.probes[2] - M.probes[1]) / (M.sizes[2] - M.sizes[1]);
  if (Math.abs(s12 - s01) / s01 > 0.05)
    fail(
      `the carry is not linear in the carried lane count (${s01.toFixed(2)} vs ${s12.toFixed(2)} ` +
        'rows/lane) — a per-lane price would be a guess',
    );
  ok(
    `the carry is linear in carried lanes at ${s12.toFixed(2)} rows/lane across ` +
      `${n(M.sizes[0])}..${n(M.sizes[2])} (two independent slopes agree within 5%)`,
  );
  deployedCarry = M.probes[2];
  ok(
    `ONE deployed boundary costs ${n(deployedCarry)} rows: ${n(M.probeNoRc)} to pack, hash and bind, ` +
      `and ${n(deployedCarry - M.probeNoRc)} to RANGE-CHECK the re-witnessed lanes`,
  );
  const perBoundary = carryPacked / NQ;
  if (M.probes[0] < perBoundary * 0.4 || M.probes[0] > perBoundary * 2.5)
    fail(
      `the probe at the fixture's own lane count (${n(M.probes[0])}) and the PROVED chain ` +
        `(${n(perBoundary)} rows/boundary) disagree by more than a factor of 2.5 — one of them is ` +
        'not measuring a boundary',
    );
  ok(
    `cross-check: the probe at the fixture's ${n(M.fixtureLanes.root)} lanes is ${n(M.probes[0])} rows ` +
      `against the proved chain's ${n(perBoundary)} rows per boundary — the same object`,
  );
}

// ---------------------------------------------------------------------------
console.log('\n[9] the deployed step count, with the measured carry in it');
{
  // §3.19's projection of the deployed root, recorded in
  // `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md`. It is a FLOOR: the AIR term in it is
  // the fixture's four constraints, not the root's 1,093 (§3.17).
  const DEPLOYED_TOTAL_ROWS = 2.75e7;
  const ZK_ROWS = 3;
  const N_PUB = 1; //   `StepPublicInput` is ONE field element, which is the point
  // ⚑ THE CARRIED SET IS NOT THE SAME AT EVERY BOUNDARY, AND A SINGLE NUMBER HERE
  // WOULD BE A WORST CASE WEARING A TOTAL. A boundary at a QUERY entry carries the
  // whole opened-value set, because the next step's DEEP quotient reads all of it
  // — that is `deployedCarry`. A boundary INSIDE a query, after the DEEP quotient
  // has been formed, carries the transcript state and a fold value and nothing
  // else — measured by the same probe at the small lane count. One deployed query
  // is 827,887 rows (§3.19), so MOST deployed boundaries are the second kind.
  // `KimchiPartition` already names the smarter scheduler as its remainder; this
  // is what the remainder is worth.
  const minCarry = M.probes[0];
  for (const [label, overhead] of [
    ['max_proofs_verified = 1 (a straight chain, §4.1: ~6,000-8,000)', 8000],
    ['max_proofs_verified = 2 (an aggregation tree, §4.1: ~12,000-16,000)', 16000],
  ] as const) {
    const usable = KIMCHI_ROWS - ZK_ROWS - N_PUB - overhead;
    const worst = usable - deployedCarry;
    const best = usable - minCarry;
    if (worst <= 0) fail(`the carry (${n(deployedCarry)}) exceeds the usable budget (${n(usable)})`);
    console.log(
      `    ${label}\n` +
        `      usable                       ${n(usable).padStart(9)} rows\n` +
        `      every boundary full-carry    ${n(deployedCarry).padStart(9)} rows  ` +
        `(${((deployedCarry / usable) * 100).toFixed(1)}% of the step) => ` +
        `${n(Math.ceil(DEPLOYED_TOTAL_ROWS / worst))} steps\n` +
        `      intra-query boundaries       ${n(minCarry).padStart(9)} rows  ` +
        `(${((minCarry / usable) * 100).toFixed(1)}% of the step) => ` +
        `${n(Math.ceil(DEPLOYED_TOTAL_ROWS / best))} steps\n` +
        `      the carry ignored entirely   ${''.padStart(9)}       => ` +
        `${n(Math.ceil(DEPLOYED_TOTAL_ROWS / usable))} steps  (what §4.2 quotes)`,
    );
  }
  const usable2 = KIMCHI_ROWS - ZK_ROWS - N_PUB - 16000;
  const worst2 = Math.ceil(DEPLOYED_TOTAL_ROWS / (usable2 - deployedCarry));
  const best2 = Math.ceil(DEPLOYED_TOTAL_ROWS / (usable2 - minCarry));
  const naive2 = Math.ceil(DEPLOYED_TOTAL_ROWS / usable2);
  if (best2 <= naive2)
    fail('even the cheapest boundary came out free — the carry is not being subtracted at all');
  ok(
    `the deployed count is a BAND, and the scheduler picks the end: ${n(best2)} steps if only the ` +
      `${19} query entries carry the opened-value set, ${n(worst2)} if every boundary does — ` +
      `against the ${n(naive2)} §4.2 quotes with the carry ignored`,
  );
  ok(
    `the full carry is ${((deployedCarry / usable2) * 100).toFixed(1)}% of a step and ` +
      `${((M.probeNoRc / deployedCarry) * 100).toFixed(0)}% of it is the pack+hash; the other ` +
      `${(((deployedCarry - M.probeNoRc) / deployedCarry) * 100).toFixed(0)}% is RANGE-CHECKING ` +
      'lanes a one-step verifier range-checks once — which is what a boundary is',
  );
}

console.log('\n[10] the ratchet');
{
  // Row counts are deterministic, so these are pinned EXACTLY — strictly inside
  // the 2% band, and a figure that moves is a figure whose document is stale.
  const RECORDED: [string, number, number][] = [
    ['the one-step assembly at 3 queries', M.mono, 103_554],
    ['step 0 (transcript + AIR + carry)', stepRows[0], 33_834],
    ['walk.first', stepRows[1], 23_623],
    ['walk.step (the reused circuit)', stepRows[2], 23_612],
    ['the whole chain carry, packed', carryPacked, 1_127],
    ['the whole chain carry, unpacked', carryUnpacked, 3_335],
    ['ONE deployed boundary, full carry', deployedCarry, 34_566],
    ['a boundary carrying the transcript state only', M.probes[0], 762],
    ['deployed root lanes crossing a boundary', M.deployedLanes.root, 9_103],
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

console.log('\n=== PARTITION-CHAIN PASS ===');

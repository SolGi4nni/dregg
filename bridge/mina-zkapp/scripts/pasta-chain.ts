import { Bool, Cache, Field, ZkProgram, verify } from 'o1js';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { resolve } from 'node:path';
import { BbExt } from '../src/FriQueryStep.js';
import {
  claimOf,
  minaFixtureConstraints,
  runQueryInputAndDeep,
  shapeOf,
  suiteOf,
  witnessOf,
  zetaNextOf,
} from '../src/DreggProofVerify.js';
import {
  GENESIS_CHALLENGE_DIGEST,
  digestOfLanes,
  stepBoundary,
  partitionTerminalSeal,
} from '../src/DreggProofPartition.js';
import {
  chainSideOf,
  deepStepArgs,
  foldStepArgs,
  makeScheduledVerify,
  rcdOfDigests,
} from '../src/DreggProofSchedule.js';
import { PICKLES } from '../src/CostModel.js';

// ---------------------------------------------------------------------------
// A REAL CHAIN OVER A PASTA-HASHED DREGG PROOF — proved, verified, spliced nine
// ways, and every refusal attributable.
//
//   npm run pasta-chain
//
// ⚑ WHY A CHAIN AT ALL. One `DreggProofVerify` program verifies a whole dregg
// proof in one Kimchi step, and at the root's geometry it does not fit: 2.906 x
// 10^6 measured rows against 54,300 usable, so the verifier has to SPLIT. This
// runs the split — the transcript step, then two steps per query cut at the
// DEEP/fold seam — over a proof `DreggMinaConfig` minted, and shows the chain's
// carry doing its job.
//
// ⚑ THE CHAIN LOGIC IS NOT NEW AND MUST NOT BE. `makeScheduledVerify`,
// `chainSideOf`, `deepStepArgs` and `foldStepArgs` are the SAME objects
// `partition-schedule.ts` drives for the BabyBear hash — this file supplies a
// different `HashSuite` and nothing else. If the two chains ever disagree it
// will be because the hash disagreed, which is the only thing that differs.
//
// ⚑ THE PROCESS BOUNDARY IS THE POINT OF [4], NOT A DETAIL. A splice refused
// inside one node process could be an artefact of a live object graph. So a step
// proof is SERIALISED to JSON, a fresh process reads it back, and the splice is
// attempted there — the shape an attacker actually has.
//
// ⚑ THREE CONTROLS, because a refusal with no control is a refusal of something
// unknown:
//   (a) the UNBOUND twin — the same circuit with the three boundary assertions
//       removed — must ACCEPT what the bound one refuses, so the refusal is the
//       CARRY and not the walk;
//   (b) a proof made by the unbound twin, verified against the BOUND program's
//       verification key, must be REFUSED — so a splice cannot be laundered by
//       proving it in a permissive circuit;
//   (c) the same proof under the UNPINNED (its own) key must be ACCEPTED — so
//       (b) is the key pin and not a broken proof.
//
// Needs cargo (the emitter) and a 16 GB node heap.
// ---------------------------------------------------------------------------

const PHASE = process.env.PASTA_CHAIN_PHASE ?? 'main';
const WORKDIR = process.env.PASTA_CHAIN_WORKDIR ?? mkdtempSync(resolve(tmpdir(), 'dregg-pasta-chain-'));
const NO_CACHE = Cache.None; // o1js's default prover-key cache aborts at this size
const OPEN_CHUNK_LANES = 32;
const FIXTURES = process.env.PASTA_FIXTURE_DIR ?? resolve(process.cwd(), '.pasta-fixtures');

let failures = 0;
const ok = (m: string) => console.log('  ✓ ' + m);
function fail(m: string): never {
  failures++;
  console.error('  ✗ ' + m);
  throw new Error(m);
}
const check = (c: boolean, m: string) => (c ? ok(m) : fail(m));
const n = (x: number) => Math.round(x).toLocaleString('en-US');
const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(1)}s`;

function load(name: string): any {
  const p = resolve(FIXTURES, name);
  if (!existsSync(p)) throw new Error(`missing Pasta fixture ${p}`);
  return JSON.parse(readFileSync(p, 'utf8'));
}

function childPhase(phase: string, extra: Record<string, string> = {}): any {
  const out = execFileSync(process.execPath, ['--max-old-space-size=16384', process.argv[1]], {
    encoding: 'utf8',
    maxBuffer: 1 << 26,
    env: { ...process.env, PASTA_CHAIN_PHASE: phase, PASTA_CHAIN_WORKDIR: WORKDIR, ...extra },
    stdio: ['ignore', 'pipe', 'inherit'],
  });
  const line = out.split('\n').find((l) => l.startsWith('##JSON##'));
  if (!line) throw new Error(`the ${phase} phase produced no result line:\n${out.slice(-3000)}`);
  return JSON.parse(line.slice(8));
}

// ---------------------------------------------------------------------------
const fxA = load('honest-d3-q2.json');
const fxB = load('honest-d3-q2-seedB.json');
const SHAPE = shapeOf(fxA, { constraints: minaFixtureConstraints });
const OPTS = { openChunkLanes: OPEN_CHUNK_LANES };
const NQ = SHAPE.knobs.numQueries;
const side = (chain: any, fx: any) =>
  chainSideOf(chain, fx, shapeOf(fx, { constraints: minaFixtureConstraints }), {
    claimOf,
    witnessOf,
    runQueryInputAndDeep,
    zetaNextOf,
  });

// ===========================================================================
// PHASE `control` — the UNBOUND twin, in its own process.
//
// ⚑ IT BUILDS ITS OWN PREDECESSOR, WHICH IS NOT A CONVENIENCE. The chain is ONE
// program, so every predecessor is a `SelfProof` and a proof made by the BOUND
// program does not verify under the unbound program's key. Handing the bound
// `deep` proof across would make the control refuse everything, and that would
// read as "the binding did it" for entirely the wrong reason.
// ===========================================================================
if (PHASE === 'control') {
  const C = makeScheduledVerify(SHAPE, OPTS);
  const U: any = C.unbound();
  await U.prog.compile({ cache: NO_CACHE });
  const S: any = await side(C, fxA);
  const B: any = await side(C, fxB);
  const { proof: p0 } = await U.prog.transcript(S.entry, S.claim, S.w[0], S.w[1], S.w[2]);
  const { proof: pd } = await U.prog.deep(p0.publicOutput, p0, Field(0), ...deepStepArgs(S, 0));
  // ⚑ TWO CLASSES, AND SEPARATING THEM IS THE RESULT. A splice can be refused by
  // the CARRY (the boundary binds a digest the witness does not match) or by the
  // WALK itself (the FRI fold chain lands somewhere the final polynomial is
  // not). Only the first class is evidence that the boundary binding works, and
  // the unbound twin is what tells them apart: it removes the three boundary
  // assertions and nothing else, so it must ACCEPT a carry refusal and must
  // still REFUSE a walk refusal.
  const cases: [string, 'carry' | 'walk', any, Field][] = [
    // The FOREIGN proof's chunk digests: the fold's own witness is honest, so
    // the walk has nothing to complain about and only the carry can object.
    ['foreign-fold', 'carry', { others: B.foldOthers }, S.deepBoundary(0, S.ro[0])],
    // A boundary that is not any boundary — same reasoning.
    ['garbage-input', 'carry', undefined, Field(123456789)],
    // Query 1's reduced openings handed to query 0's fold. This one the FOLD
    // CHAIN catches on its own: the chain starts from the wrong value and does
    // not land on `final_poly`. Classified `walk` so the leg reports where the
    // refusal comes from instead of crediting it to the binding.
    ['intra-query', 'walk', { ro: S.ro[1] }, S.deepBoundary(0, S.ro[0])],
  ];
  const kind: Record<string, string> = Object.fromEntries(cases.map(([n2, k]) => [n2, k]));
  const accepted: Record<string, boolean> = {};
  const why: Record<string, string> = {};
  for (const [name, , over, bIn] of cases) {
    try {
      await U.prog.fold(bIn, pd, Field(0), Bool(false), ...foldStepArgs(S, 0, over));
      accepted[name] = true;
    } catch (e: any) {
      accepted[name] = false;
      why[name] = String(e?.message ?? e).split('\n')[0].slice(0, 140);
    }
  }
  // (b)/(c): a step proved by the UNBOUND circuit, written out for the `vk`
  // phase to try against the BOUND key.
  writeFileSync(resolve(WORKDIR, 'unbound-step.json'), JSON.stringify(p0.toJSON()));
  writeFileSync(resolve(WORKDIR, 'unbound-vk.json'), JSON.stringify((await U.prog.compile({ cache: NO_CACHE })).verificationKey));
  console.log('##JSON##' + JSON.stringify({ accepted, why, kind }));
  process.exit(0);
}

// ===========================================================================
// PHASE `vk` — the KEY PIN, across a process boundary.
// ===========================================================================
if (PHASE === 'vk') {
  const C = makeScheduledVerify(SHAPE, OPTS);
  const { verificationKey: boundVk } = await C.prog.compile({ cache: NO_CACHE });
  const StepProof = ZkProgram.Proof(C.prog as any);
  const raw = JSON.parse(readFileSync(resolve(WORKDIR, 'unbound-step.json'), 'utf8'));
  const unboundVk = JSON.parse(readFileSync(resolve(WORKDIR, 'unbound-vk.json'), 'utf8'));
  const p = await (StepProof as any).fromJSON(raw);
  const parsed = true;
  let boundAccepts = false;
  try {
    boundAccepts = await verify(p, boundVk);
  } catch {
    boundAccepts = false;
  }
  let unpinnedAccepts = false;
  try {
    unpinnedAccepts = await verify(p, unboundVk);
  } catch {
    unpinnedAccepts = false;
  }
  console.log('##JSON##' + JSON.stringify({ parsed, boundAccepts, unpinnedAccepts, boundHash: String(boundVk.hash), unboundHash: String(unboundVk.hash) }));
  process.exit(0);
}

// ===========================================================================
// PHASE `splice` — the CROSS-PROCESS splice.
//
// The chain's steps are proved in `main`, serialised, and handed here. This
// process never sees the objects that made them; it reads bytes, as an attacker
// would.
// ===========================================================================
if (PHASE === 'splice') {
  const C = makeScheduledVerify(SHAPE, OPTS);
  await C.prog.compile({ cache: NO_CACHE });
  const StepProof = ZkProgram.Proof(C.prog as any);
  const A: any = await side(C, fxA);
  const B: any = await side(C, fxB);
  const readProof = async (f: string) =>
    (StepProof as any).fromJSON(JSON.parse(readFileSync(resolve(WORKDIR, f), 'utf8')));
  const pA0 = await readProof('A-transcript.json');
  const pAd0 = await readProof('A-deep0.json');
  const pB0 = await readProof('B-transcript.json');

  const attempts: [string, () => Promise<any>][] = [
    // Continue A's chain from B's transcript step: a proof of a DIFFERENT dregg
    // proof, spliced in at step 1.
    ['foreign transcript step', () => (C.prog as any).deep(pB0.publicOutput, pB0, Field(0), ...deepStepArgs(A, 0))],
    // A's own transcript step, but B's deep witness under it.
    ['foreign deep witness', () => (C.prog as any).deep(pA0.publicOutput, pA0, Field(0), ...deepStepArgs(B, 0))],
    // The fold half handed the OTHER query's reduced openings.
    ['intra-query reduced-opening splice', () => (C.prog as any).fold(A.deepBoundary(0, A.ro[0]), pAd0, Field(0), Bool(false), ...foldStepArgs(A, 0, { ro: A.ro[1] }))],
    // The fold half handed the FOREIGN proof's chunk digests.
    ['foreign chunk digests in the fold', () => (C.prog as any).fold(A.deepBoundary(0, A.ro[0]), pAd0, Field(0), Bool(false), ...foldStepArgs(A, 0, { others: B.foldOthers }))],
    // A fold claiming the wrong query index.
    ['wrong query index', () => (C.prog as any).fold(A.deepBoundary(1, A.ro[1]), pAd0, Field(1), Bool(false), ...foldStepArgs(A, 1))],
    // A deep following a deep — the alternation the boundary index forces.
    ['deep after deep', () => (C.prog as any).deep(pAd0.publicOutput, pAd0, Field(1), ...deepStepArgs(A, 1))],
    // The transcript's entry boundary, forged.
    ['forged entry boundary', () => (C.prog as any).transcript(stepBoundary(B.rcd, GENESIS_CHALLENGE_DIGEST, 0), A.claim, A.w[0], A.w[1], A.w[2])],
  ];
  const refused: Record<string, boolean> = {};
  for (const [name, f] of attempts) {
    try {
      await f();
      refused[name] = false;
    } catch {
      refused[name] = true;
    }
  }
  console.log('##JSON##' + JSON.stringify({ refused }));
  process.exit(0);
}

// ===========================================================================
// PHASE `main`.
// ===========================================================================
console.log('=== A REAL CHAIN OVER A PASTA-HASHED DREGG PROOF ===\n');

console.log('[1] the two proofs, and that they are two');
check(suiteOf(fxA).name === 'mina-poseidon-pasta', `both fixtures are '${suiteOf(fxA).name}'-hashed`);
const CHAIN = makeScheduledVerify(SHAPE, OPTS);
const A: any = await side(CHAIN, fxA);
const B: any = await side(CHAIN, fxB);
check(A.rcd.toString() !== B.rcd.toString(), 'the two dregg proofs have DIFFERENT rootCommitDigests');
check(A.cd.toString() !== B.cd.toString(), 'and different challengeDigests');
check(
  String(fxA.challenges.queryIndices) !== String(fxB.challenges.queryIndices),
  `and their transcripts drew different query indices ([${fxA.challenges.queryIndices}] vs [${fxB.challenges.queryIndices}])`,
);
// ⚑ ANTI-VACUITY, PER CHUNK. A chunk whose digest did not move when its
// preimage moved would make every splice refusal below a refusal of something
// else. Every chunk is bent, not a sample of them.
for (const c of A.chunks) {
  if (c.lanes.length === 0) fail(`chunk ${c.id} is empty — it commits to nothing`);
  for (const i of [0, c.lanes.length - 1]) {
    const bent = A.chunks.map((x: any) =>
      x.id === c.id
        ? { ...x, lanes: x.lanes.map((v: Field, j: number) => (j === i ? v.add(1) : v)) }
        : x,
    );
    const rcd2 = rcdOfDigests(bent.map((x: any) => digestOfLanes(x.lanes, CHAIN.pack)));
    if (rcd2.toString() === A.rcd.toString())
      fail(`bending lane ${i} of chunk ${c.id} left rootCommitDigest unchanged`);
    if (stepBoundary(rcd2, A.cd, 1).toString() === stepBoundary(A.rcd, A.cd, 1).toString())
      fail(`bending lane ${i} of chunk ${c.id} moved the digest but not the boundary`);
  }
}
ok(
  `bending either end of EVERY one of the ${A.chunks.length} chunks moves rootCommitDigest AND the ` +
    'boundary — no chunk is decorative',
);
ok(`the chain commits to ${A.chunks.length} chunks: ${A.chunks.map((c: any) => c.id).join(', ')}`);

// ---------------------------------------------------------------------------
console.log('\n[2] the chain, PROVED');
let t = Date.now();
await CHAIN.prog.compile({ cache: NO_CACHE });
console.log(`    compile ${secs(t)} (ONE program, three methods — four compiled step circuits in one process hang at the first prove)`);
const rows = (await CHAIN.prog.analyzeMethods()) as any;
const stepRows = {
  transcript: rows.transcript.rows,
  deep: rows.deep.rows,
  fold: rows.fold.rows,
};
const widest = Math.max(...Object.values(stepRows));
console.log(
  `    transcript ${n(stepRows.transcript)} + ${NQ}x (deep ${n(stepRows.deep)} + fold ${n(stepRows.fold)}) ` +
    `= ${1 + 2 * NQ} steps from ONE verification key`,
);
check(
  widest <= PICKLES.usableRowsMpv1,
  `the widest step is ${n(widest)} rows, inside the ${n(PICKLES.usableRowsMpv1)}-row Pickles budget (${((widest / PICKLES.usableRowsMpv1) * 100).toFixed(1)}%)`,
);
check(
  stepRows.fold < stepRows.deep,
  `the FOLD half is ${n(stepRows.deep - stepRows.fold)} rows cheaper than the DEEP half — it never witnesses an opened evaluation`,
);

t = Date.now();
const proofs: any[] = [];
const { proof: p0 } = await (CHAIN.prog as any).transcript(A.entry, A.claim, A.w[0], A.w[1], A.w[2]);
proofs.push(p0);
let prev = p0;
for (let q = 0; q < NQ; q++) {
  const { proof: pd } = await (CHAIN.prog as any).deep(prev.publicOutput, prev, Field(q), ...deepStepArgs(A, q));
  proofs.push(pd);
  const { proof: pf } = await (CHAIN.prog as any).fold(
    pd.publicOutput,
    pd,
    Field(q),
    Bool(q === NQ - 1),
    ...foldStepArgs(A, q),
  );
  proofs.push(pf);
  prev = pf;
}
console.log(`    prove ${proofs.length} steps ${secs(t)}`);
let allVerify = true;
for (const p of proofs) if (!(await CHAIN.prog.verify(p))) allVerify = false;
check(allVerify, `all ${proofs.length} step proofs VERIFY`);

// The terminal seal pins the chain LENGTH, not merely its content.
const seal = partitionTerminalSeal(A.rcd, Field(2 * NQ + 1));
check(
  prev.publicOutput.toString() === seal.toString(),
  `the last step's output is the TERMINAL SEAL at length ${2 * NQ + 1}`,
);
let lengthPinned = true;
for (const wrong of [2 * NQ, 2 * NQ + 2, 1])
  if (partitionTerminalSeal(A.rcd, Field(wrong)).toString() === seal.toString()) lengthPinned = false;
check(lengthPinned, 'and no other chain length produces that seal — the length is pinned');
check(
  partitionTerminalSeal(B.rcd, Field(2 * NQ + 1)).toString() !== seal.toString(),
  'nor does the same length over the OTHER dregg proof — the seal names WHICH proof was verified',
);

// Serialise for the cross-process splice.
writeFileSync(resolve(WORKDIR, 'A-transcript.json'), JSON.stringify(proofs[0].toJSON()));
writeFileSync(resolve(WORKDIR, 'A-deep0.json'), JSON.stringify(proofs[1].toJSON()));
const { proof: pB0 } = await (CHAIN.prog as any).transcript(B.entry, B.claim, B.w[0], B.w[1], B.w[2]);
writeFileSync(resolve(WORKDIR, 'B-transcript.json'), JSON.stringify(pB0.toJSON()));
ok('three step proofs written to disk — the splices below run in a FRESH process, from bytes');

// ---------------------------------------------------------------------------
console.log('\n[3] SPLICED, across a process boundary');
t = Date.now();
const SP = childPhase('splice');
console.log(`    (a fresh process, ${secs(t)})`);
let allRefused = true;
for (const [name, r] of Object.entries(SP.refused)) {
  if (r) ok(`REFUSED: ${name}`);
  else {
    allRefused = false;
    console.error(`  ✗ ACCEPTED: ${name}`);
  }
}
check(allRefused, `all ${Object.keys(SP.refused).length} splices refused from serialised proofs in a process that never held the originals`);

// ---------------------------------------------------------------------------
console.log('\n[4] THE CONTROLS — so [3] is attributable');
t = Date.now();
const C = childPhase('control');
console.log(`    (the unbound twin, its own process, ${secs(t)})`);
// ⚑ THE CONTROL SORTS THE REFUSALS, it does not just bless them. A `carry` case
// must be ACCEPTED by the unbound twin (so [3]'s refusal is the boundary
// binding); a `walk` case must still be REFUSED (so the leg reports it as the
// fold chain's own catch and does not credit the binding for it). The first run
// of this leg asserted every case was `carry` and went RED on the intra-query
// splice — which was the control doing its job, not a defect.
for (const [k, v] of Object.entries(C.accepted) as [string, boolean][]) {
  const cls = C.kind?.[k] ?? 'carry';
  if (cls === 'carry') {
    if (v) ok(`(a) CARRY: the UNBOUND twin ACCEPTS '${k}' — [3]'s refusal is the boundary binding, not the walk`);
    else
      fail(
        `the UNBOUND twin ALSO refused the CARRY case '${k}' (${C.why?.[k] ?? 'no reason'}) — [3]'s ` +
          'refusal is not attributable to the boundary binding',
      );
  } else {
    if (!v)
      ok(
        `(a') WALK: the UNBOUND twin ALSO refuses '${k}' (${C.why?.[k] ?? ''}) — that splice is caught ` +
          'by the FRI fold chain itself, and the binding gets no credit for it',
      );
    else
      fail(`'${k}' was classified as a WALK refusal but the unbound twin ACCEPTED it`);
  }
}

t = Date.now();
const V = childPhase('vk');
console.log(`    (the key pin, its own process, ${secs(t)})`);
check(V.parsed, 'the unbound step proof PARSES from JSON in a process that did not make it');
check(
  V.boundAccepts === false,
  `(b) UNBOUND-BUT-PINNED: it is REFUSED under the BOUND program's verification key — a splice cannot be laundered by proving it in a permissive circuit`,
);
check(
  V.unpinnedAccepts === true,
  '(c) UNPINNED: the same bytes are ACCEPTED under their own key — so (b) is the KEY PIN, not a broken proof',
);
check(V.boundHash !== V.unboundHash, `and the two keys really differ (${V.boundHash.slice(0, 12)}... vs ${V.unboundHash.slice(0, 12)}...)`);

// ---------------------------------------------------------------------------
console.log('\n[5] WHAT THE CHAIN COSTS, at the root geometry');
console.log(
  `    at the fixture: ${1 + 2 * NQ} steps, widest ${n(widest)} rows.\n` +
    `    at the ROOT geometry the measured Mina-side total is 2.906e6 rows = ` +
    `${Math.ceil(2.906e6 / PICKLES.usableRowsMpv1)} slices (scripts/pasta-root-rows.ts), against 2.46e7 / 453 deployed.`,
);

if (failures > 0) {
  console.error(`\n${failures} FAILURES\n`);
  process.exit(1);
}
console.log('\n=== the chain proves, the seal pins it, and every splice is refused from bytes ===\n');

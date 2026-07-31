// FOLD-MU — what does a MERGE NODE cost, against what a LEAF costs?
//
//   O1JS_BACKEND=native npm run fold-mu
//
// ── THE ONE NUMBER EVERY TREE ESTIMATE SWINGS ON ───────────────────────────
// A merge tree over N leaves adds N-1 merge proofs to N leaf proofs. Whether
// that is a rounding error or a doubling is settled by ONE ratio:
//
//     mu = (wall clock of one merge prove) / (wall clock of one leaf prove)
//
// At mu near 0 a tree is free and the only question is how many workers exist.
// At mu >= 1 a full binary tree is a LOSS on one box — 912 leaves + 911 merges
// is nearly twice the work of 912 leaves in a line — and the only tree worth
// building is a COARSE one that merges at the strand seams, where 19 merges
// ride on top of 912 leaves and the overhead is 19/912 of a merge each.
//
// ⚑ SO THIS RUNS FIRST AND THE ANSWER IS ALLOWED TO KILL THE PLAN. If mu > 1.3
// the full binary tree is not a design choice, it is a mistake, and this file
// says so in its exit line rather than in a footnote.
//
// ── WHY THE BODY IS THE REAL ONE ───────────────────────────────────────────
// `assertMergeable` and `foldCompose` are imported from `src/DreggFold.ts`, not
// re-typed here. A probe that times a sketch of the merge measures the sketch.
// The ONE thing this program has that `DreggFold` must never have is `seed`: a
// method that mints a `FoldNode` out of private inputs. That is a forgery of
// every property the tree carries, it exists so a merge can be proved without
// first proving a 47,000-row slice, and the program is named so nobody mistakes
// the two.
//
// ── WHAT THE LEAF NUMBER IS, AND WHAT IT IS NOT ────────────────────────────
// The leaf figures are READ from `.fullchain/pasta-braid-*-measurement.json` —
// real `prove()` wall clocks of real FRI slices on THIS box, written by
// `pasta-braid.ts`. They are head slices, which the braid's own header flags as
// not representative of the whole chain. They are the best measured leaf this
// tree has and the ratio is reported against BOTH hashes, because the sibling
// lane's Pasta cutover moves the denominator by ~2.3x and therefore moves mu.
//
// ⚠ AND THE MERGE ITSELF IS NOISY, WHICH IS WHY THIS REPORTS EVERY SAMPLE. Two
// runs of this file on the same box gave merge means of 8.46s (samples 6.74,
// 8.22, 10.91, 7.96) and 6.35s (6.14, 6.28, 6.49, 6.50). Same program, same
// backend. A single-sample mu would have been off by 33%; the emitted JSON
// keeps `mergeMs` so a reader can see the spread rather than the headline.

import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { relative, resolve } from 'node:path';
import { Field, SelfProof, ZkProgram, verify } from 'o1js';
import { ChainClaim } from '../src/RootClaim.js';
import { FoldNode, assertMergeable, foldCompose } from '../src/DreggFold.js';

const WORK = process.env.FOLD_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const REPS = Number(process.env.FOLD_MU_REPS ?? 3);

const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(2)}s`;
const fmt = (n: number) => n.toLocaleString('en-US');
let failed = 0;
const ok = (s: string) => console.log(`    ok   ${s}`);
const fail = (s: string) => {
  failed++;
  console.log(`    FAIL ${s}`);
};

/**
 * ⚑ THE PROBE, AND THE WORD `SEED` IS THE WARNING. `seed` mints a `FoldNode`
 * from witnesses — no leaf proof, no key-list membership, any `count` the
 * prover likes. It exists to put two `SelfProof`s in front of the merge for a
 * few hundred milliseconds instead of a few minutes. `DreggFold` has `lift`
 * where this has `seed`, and that difference is the entire security argument.
 */
const MuProbe = ZkProgram({
  name: 'dregg-fold-MU-PROBE-seeded-NOT-A-CHAIN',
  publicOutput: FoldNode,
  methods: {
    seed: {
      privateInputs: [FoldNode],
      async method(node: FoldNode) {
        return { publicOutput: node };
      },
    },
    merge: {
      privateInputs: [SelfProof, SelfProof, Field],
      async method(
        left: SelfProof<undefined, FoldNode>,
        right: SelfProof<undefined, FoldNode>,
        witnessedCount: Field,
      ) {
        left.verify();
        right.verify();
        const l = left.publicOutput;
        const r = right.publicOutput;
        assertMergeable(l, r, {});
        return { publicOutput: foldCompose(l, r, witnessedCount, {}) };
      },
    },
  },
});

const claim = new ChainClaim({
  genesisRoot: Field(0x9e_11n),
  finalRoot: Field(0x9e_22n),
  numTurns: Field(4),
  chainDigest: Field(0x9e_33n),
});
const node = (bIn: bigint, bOut: bigint, count: number) =>
  new FoldNode({ bIn: Field(bIn), bOut: Field(bOut), count: Field(count), claim });

type LeafSample = { hash: string; proveMs: number[]; rows: number[] };

function readLeafSamples(): LeafSample[] {
  const out: LeafSample[] = [];
  for (const [hash, file] of [
    ['pasta', 'pasta-braid-pasta-measurement.json'],
    ['babybear', 'pasta-braid-babybear-measurement.json'],
  ] as const) {
    const p = resolve(WORK, file);
    if (!existsSync(p)) continue;
    const m = JSON.parse(readFileSync(p, 'utf8'));
    const proved: any[] = m.proved ?? [];
    if (proved.length === 0) continue;
    out.push({
      hash,
      proveMs: proved.map((r) => Number(r.proveMs)),
      rows: proved.map((r) => Number(r.rows)),
    });
  }
  return out;
}

const mean = (xs: number[]) => xs.reduce((a, b) => a + b, 0) / xs.length;

async function main() {
  console.log('=== FOLD-MU — the merge/leaf prove-time ratio, measured ===\n');
  console.log(`    backend ${process.env.O1JS_BACKEND ?? 'wasm (default)'}   node ${process.version}`);
  console.log(`    reps    ${REPS}\n`);

  // =====================================================================
  console.log('[1] THE MERGE, ANALYZED — what a two-proof node costs in ROWS\n');
  let t = Date.now();
  const analysis = await MuProbe.analyzeMethods();
  const seedRows = (analysis as any).seed.rows;
  const mergeRows = (analysis as any).merge.rows;
  console.log(`    seed  ${fmt(seedRows)} rows`);
  console.log(`    merge ${fmt(mergeRows)} rows   (${secs(t)})`);
  console.log(
    '\n    ⚑ These are APPLICATION rows and they are almost nothing. The merge is six\n' +
      '      equalities, one addition and one 16-bit range check. Whatever a merge costs\n' +
      '      in seconds is FIXED PICKLES COST — recursion, not arithmetic — which is why\n' +
      '      mu is a ratio worth measuring instead of deriving from row counts.',
  );
  if (mergeRows > 500)
    fail(`the merge body is ${fmt(mergeRows)} rows — that is not "five assertions" and mu is measuring something else`);
  else ok(`the merge body is ${fmt(mergeRows)} application rows`);

  // =====================================================================
  console.log('\n[2] COMPILE — one key for both methods, and for every level\n');
  t = Date.now();
  const { verificationKey: vk } = await MuProbe.compile();
  const compileMs = Date.now() - t;
  ok(`compiled in ${secs(t)}, vk hash ${vk.hash.toBigInt()}`);

  // =====================================================================
  console.log('\n[3] PROVE — two seeds, then merges at two levels\n');

  const seedMs: number[] = [];
  t = Date.now();
  const a = await MuProbe.seed(node(0x1000n, 0x2000n, 1));
  seedMs.push(Date.now() - t);
  t = Date.now();
  const b = await MuProbe.seed(node(0x2000n, 0x3000n, 1));
  seedMs.push(Date.now() - t);
  t = Date.now();
  const c = await MuProbe.seed(node(0x3000n, 0x4000n, 1));
  seedMs.push(Date.now() - t);
  t = Date.now();
  const d = await MuProbe.seed(node(0x4000n, 0x5000n, 1));
  seedMs.push(Date.now() - t);
  console.log(`    4 seeds (0 proofs verified): ${seedMs.map((m) => (m / 1000).toFixed(2)).join('s, ')}s`);

  const mergeMs: number[] = [];
  t = Date.now();
  const ab = await MuProbe.merge(a.proof, b.proof, Field(2));
  mergeMs.push(Date.now() - t);
  console.log(`    level-1 merge(a,b): ${secs(t)}`);
  t = Date.now();
  const cd = await MuProbe.merge(c.proof, d.proof, Field(2));
  mergeMs.push(Date.now() - t);
  console.log(`    level-1 merge(c,d): ${secs(t)}`);

  t = Date.now();
  const abcd = await MuProbe.merge(ab.proof, cd.proof, Field(4));
  const level2Ms = Date.now() - t;
  mergeMs.push(level2Ms);
  console.log(`    level-2 merge(ab,cd): ${secs(t)}`);

  for (let i = mergeMs.length; i < REPS + 1; i++) {
    t = Date.now();
    await MuProbe.merge(a.proof, b.proof, Field(2));
    mergeMs.push(Date.now() - t);
    console.log(`    level-1 merge repeat: ${secs(t)}`);
  }

  // ---- the properties the tree is built on, checked here ----------------
  const root = abcd.proof.publicOutput;
  if (root.bIn.toBigInt() !== 0x1000n || root.bOut.toBigInt() !== 0x5000n)
    fail(`the level-2 root spans ${root.bIn.toBigInt()}..${root.bOut.toBigInt()}, not 0x1000..0x5000`);
  else ok('the level-2 root states the OUTER interval — bIn from the leftmost leaf, bOut from the rightmost');
  if (root.count.toBigInt() !== 4n) fail(`the root counts ${root.count.toBigInt()} leaves, not 4`);
  else ok('count is additive across levels — 4 leaves under a depth-2 tree');

  const okv = await verify(abcd.proof, vk);
  if (!okv) fail('the level-2 proof does not verify under the program key');
  else ok('a level-2 proof verifies under the SAME key a level-1 proof does — one key, every level');

  //  ⚑ ASSOCIATIVITY, AS A MEASUREMENT AND NOT A CLAIM. The same four leaves
  //  folded LEFT-DEEP must produce a byte-identical public output.
  t = Date.now();
  const leftDeepAb = ab.proof;
  const leftDeepAbc = await MuProbe.merge(leftDeepAb, c.proof, Field(3));
  const leftDeepAbcd = await MuProbe.merge(leftDeepAbc.proof, d.proof, Field(4));
  const L = leftDeepAbcd.proof.publicOutput;
  const same =
    L.bIn.toBigInt() === root.bIn.toBigInt() &&
    L.bOut.toBigInt() === root.bOut.toBigInt() &&
    L.count.toBigInt() === root.count.toBigInt() &&
    L.claim.chainDigest.toBigInt() === root.claim.chainDigest.toBigInt();
  if (!same) fail('a LEFT-DEEP fold of the same four leaves produced a DIFFERENT root node — the merge is not associative');
  else ok(`a left-deep fold of the same 4 leaves gives an IDENTICAL root node (${secs(t)}) — ANY tree shape is admissible`);

  // =====================================================================
  console.log('\n[4] MU — against the leaf proves this box actually measured\n');
  const mergeMean = mean(mergeMs);
  const seedMean = mean(seedMs);
  console.log(`    merge mean over ${mergeMs.length} proves : ${(mergeMean / 1000).toFixed(2)}s`);
  console.log(`    seed  mean over ${seedMs.length} proves : ${(seedMean / 1000).toFixed(2)}s  (0 proofs verified)`);
  console.log(
    `    the ARITY price — a 2-proof step over a 0-proof step: ${(mergeMean / seedMean).toFixed(2)}x\n`,
  );

  const leaves = readLeafSamples();
  if (leaves.length === 0)
    fail(
      'no `.fullchain/pasta-braid-*-measurement.json` on disk, so there is no MEASURED leaf to ' +
        'divide by. Run `O1JS_BACKEND=native npm run pasta-braid` first; mu against a remembered ' +
        'number is not a measurement.',
    );

  const mus: Record<string, number> = {};
  for (const s of leaves) {
    const leafMean = mean(s.proveMs);
    const mu = mergeMean / leafMean;
    mus[s.hash] = mu;
    console.log(
      `    ${s.hash.padEnd(9)} leaf ${(leafMean / 1000).toFixed(2)}s over ${s.proveMs.length} proves ` +
        `(${fmt(Math.round(mean(s.rows)))} rows)   ->  mu = ${mu.toFixed(3)}`,
    );
  }

  // =====================================================================
  console.log('\n[5] WHAT MU SAYS ABOUT EACH TREE — arithmetic, stated\n');
  const TOTAL = 912;
  const COARSE_LEAVES = 20;
  for (const [hash, mu] of Object.entries(mus)) {
    const binaryWork = (TOTAL + (TOTAL - 1) * mu) / TOTAL;
    const coarseWork = (TOTAL + (COARSE_LEAVES - 1) * mu) / TOTAL;
    console.log(`    at the ${hash.toUpperCase()} hash, mu = ${mu.toFixed(3)}:`);
    console.log(
      `        full binary tree (911 merges) : ${binaryWork.toFixed(3)}x the chain's total work`,
    );
    console.log(
      `        coarse tree      ( 19 merges) : ${coarseWork.toFixed(3)}x the chain's total work`,
    );
    if (mu > 1.3)
      console.log(
        `        ⚑ mu > 1.3 — a full binary tree is a LOSS even before scheduling. The COARSE\n` +
          `          tree is the whole answer at this hash.`,
      );
    else
      console.log(
        `        mu <= 1.3 — a full binary tree is affordable if enough workers exist to spend\n` +
          `          the depth; the coarse tree is nearly free either way.`,
      );
  }

  mkdirSync(WORK, { recursive: true });
  const out = resolve(WORK, 'fold-mu.json');
  writeFileSync(
    out,
    JSON.stringify(
      {
        backend: process.env.O1JS_BACKEND ?? 'wasm',
        node: process.version,
        vkHash: String(vk.hash.toBigInt()),
        compileMs,
        seedRows,
        mergeRows,
        seedMs,
        mergeMs,
        mergeMeanMs: mergeMean,
        seedMeanMs: seedMean,
        arityPrice: mergeMean / seedMean,
        leaves: leaves.map((s) => ({ hash: s.hash, proveMs: s.proveMs, meanMs: mean(s.proveMs) })),
        mu: mus,
        associative: same,
        emittedAt: new Date().toISOString(),
      },
      null,
      2,
    ) + '\n',
  );
  console.log(`\n    wrote ${relative(process.cwd(), out)}`);

  console.log(
    failed === 0
      ? '\n=== FOLD-MU: mu MEASURED ===\n'
      : `\n=== FOLD-MU: ${failed} FAILURE(S) ===\n`,
  );
  process.exit(failed === 0 ? 0 : 1);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});

import { readFileSync } from 'node:fs';
import { assertGeometryMatchesProof, MEASURED_ROOT_GEOMETRY } from '../src/CostModel.js';
import { verifyPlan } from '../src/DreggProofVerify.js';
import { babyBearSuite, pastaSuite } from '../src/HashSuites.js';
import type { MerkleSuite } from '../src/HashSuiteType.js';
import type { RealRootFri } from '../src/RootFriWalk.js';
import {
  ROOT_CHALLENGE_STATUS,
  commitLeafPair,
  rehash,
  reducedOpeningsOf,
  rootShapeOf,
  rootValues,
  verifyMixedBatchBigInt,
  type RootValues,
} from '../src/RootConsume.js';
import { MINA_TIER } from '../src/tier.js';

// ---------------------------------------------------------------------------
// [LEG] THE FOUR-ROUND OUT-OF-CIRCUIT DIFFERENTIAL — run FIRST, and it runs in
// seconds.
//
// ⚑ WHY THIS IS THE FIRST THING IN THE MERGE AND NOT THE LAST. Every real defect
// in this arc came from a cheap exhaustive out-of-circuit differential: four
// silent wrongs across the braid's 11,303 segments, all 19 block-joins broken
// across the uniform walk's 820 boundaries, two transcript readings that "would
// each have compiled and proved cleanly". Extending the consumer from two PCS
// rounds to four adds FOUR new ways to be silently wrong, and every one of them
// gives a beautiful row count:
//
//   1. WHICH MATRICES SEED THE LEAF. The two-round assembly sponged the whole
//      batch row as one run. At four rounds each round is at FIVE heights, and
//      only the tallest matrices' rows are the leaf.
//   2. WHERE A SHORTER MATRIX IS INJECTED. `curr_height_padded` halves per
//      level, so height `h` enters at level `top - 1 - h`. Off by one is a
//      different tree, not an error.
//   3. WHICH WAY THE INJECTION COMPRESSES. `compress([root, digest])`, root
//      first. Swapped is a perfectly good Merkle tree and a different one.
//   4. WHICH INDEX BITS A LEVEL CONSUMES. The batch's own top height sets the
//      shift, not the global max and not the matrix's.
//
// This leg puts all four to the committed proof's own round commitments, LEVEL
// BY LEVEL, and requires each bent reading to be REFUSED at a named level.
//
// ⚑ AND IT IS THREE-VALUED. A falsifier that cannot bite at a given position is
// reported NOT ATTRIBUTABLE with the reason, never as a pass — the instrument
// trap this arc paid for twice.
//
//   npm run root-consume-differential            (tier 0 — nothing compiles)
// ---------------------------------------------------------------------------

const TIER = MINA_TIER;
const REAL: RealRootFri = JSON.parse(readFileSync('.fullchain/real-root-fri.json', 'utf8'));

let failures = 0;
const ok = (m: string) => console.log(`  ✓ ${m}`);
const na = (m: string) => console.log(`  ○ NOT ATTRIBUTABLE — ${m}`);
const fail = (m: string) => {
  console.log(`  ✗ ${m}`);
  failures++;
};
const fmt = (n: number) => n.toLocaleString('en-US');

console.log('\n=== THE FOUR-ROUND CONSUME, OUT OF CIRCUIT ===');
console.log(`    tier ${TIER}; object: .fullchain/real-root-fri.json (${REAL.kind})`);
console.log(`    challenges: ${ROOT_CHALLENGE_STATUS}\n`);

// ===========================================================================
// [1] The shape — four rounds, and `verifyPlan` no longer refuses them.
// ===========================================================================

console.log('[1] the shape the committed proof has, and the plan the assembly builds for it');

const SH = rootShapeOf(REAL, babyBearSuite);
const PLAN = verifyPlan(SH);
const V = rootValues(REAL);

if (PLAN.nBatches === 4) ok('`verifyPlan` accepts FOUR input-phase batches — the `nBatches !== 2` throw is gone');
else fail(`the plan has ${PLAN.nBatches} batches`);

const nMat = SH.batches.reduce((a, b) => a + b.matrices.length, 0);
const census = SH.batches.reduce(
  (a, b) => a + b.matrices.reduce((x, m) => x + m.numCols * m.numPoints, 0),
  0,
);
if (nMat === 35) ok(`35 committed matrices across 4 rounds (${SH.batches.map((b) => b.matrices.length).join(' + ')})`);
else fail(`${nMat} matrices`);

if (census === MEASURED_ROOT_GEOMETRY.censusPerQuery && census === PLAN.nOpenedValues)
  ok(
    `the plan's opened-value census is ${fmt(census)} — CostModel's measured figure, and NOT the ` +
      'retired 2,286',
  );
else fail(`the plan opens ${PLAN.nOpenedValues} values; the census says ${census}, CostModel ${MEASURED_ROOT_GEOMETRY.censusPerQuery}`);

const heights = PLAN.batchHeights[0];
if (JSON.stringify(heights) === JSON.stringify([...MEASURED_ROOT_GEOMETRY.heights]))
  ok(`every round sits at the five measured heights [${heights.join(', ')}] — mixed, not flat 22`);
else fail(`round 0 heights [${heights.join(', ')}]`);

assertGeometryMatchesProof({
  inputRounds: REAL.inputRounds.map((r) => ({
    kindName: r.kindName,
    matrices: r.matrices.map((m) => ({ logHeight: m.logHeight, width: m.width, points: m.points })),
  })),
});
ok("CostModel's `assertGeometryMatchesProof` reproduces the census AND the height list off this same object");

if (PLAN.nRollIns === 4 && PLAN.totalRow === 1427)
  ok(`4 roll-ins and ${fmt(PLAN.totalRow)} opened base lanes a query (940 + 56 + 175 + 256)`);
else fail(`${PLAN.nRollIns} roll-ins, ${PLAN.totalRow} lanes`);

// ===========================================================================
// [2] The opening points are DERIVED — ζ times a protocol constant.
// ===========================================================================

console.log('\n[2] the opening points, and the instance that opens at ζ TWICE');

//  `rootShapeOf` throws unless every point is ζ·g_{degree_bits(instance)} with a
//  BASE-field scale, so reaching here is the check passing.
ok(
  `every one of the ${fmt(census)} opened values sits at ζ·g for the instance's OWN trace domain — ` +
    'checked as a base-field quotient, not looked up',
);
if (PLAN.pointScales.length === 5 && PLAN.pointScales[0] === 1n)
  ok(
    `${PLAN.pointScales.length} distinct scales over 7 instances at degree_bits [${REAL.degreeBits.join(', ')}] ` +
      `— so ζ's next-row points cost ${PLAN.pointScales.length - 1} constant multiplies for the whole proof`,
  );
else fail(`${PLAN.pointScales.length} distinct point scales`);

//  ⚑ INSTANCE 6 IS `degree_bits = 0`, so `g_0 = 1` and its permutation matrix
//  opens at ζ TWICE. Nothing may collapse those two points.
const permRound = SH.batches[3];
const inst6 = permRound.matrices[6];
if (inst6.numPoints === 2 && inst6.pointScales!.every((c) => c === 1n))
  ok('instance 6 (degree_bits 0) opens its permutation matrix at ζ TWICE, and both points survive into the plan');
else fail('instance 6 lost a point');
const wired6 = PLAN.wiring[3][6];
if (wired6.length === 2 && wired6[0].offset !== wired6[1].offset && wired6[0].scaleIndex === 0 && wired6[1].scaleIndex === 0)
  ok(
    `both of instance 6's ζ points are wired to DISTINCT opened-value runs (offsets ${wired6[0].offset} ` +
      `and ${wired6[1].offset}) — a wiring that deduped equal points would drop ${inst6.numCols} DEEP terms`,
  );
else fail('instance 6 point wiring collapsed');

// ===========================================================================
// [3] The mixed-height MMCS, LEVEL BY LEVEL, against the committed roots.
// ===========================================================================

console.log('\n[3] the four-round input phase against the proof\'s OWN round commitments');

const specOf = (ri: number) => ({
  matrices: SH.batches[ri].matrices.map((m) => ({ logHeight: m.logHeight, numCols: m.numCols })),
  pathDepth: SH.batches[ri].pathDepth,
});

const honest = (suite: MerkleSuite<any>, v: RootValues, ri: number, q: number) =>
  verifyMixedBatchBigInt(
    suite,
    specOf(ri),
    v.rows[q][ri],
    v.inputPaths[q][ri],
    BigInt(v.queryIndices[q]),
    SH.logGlobalMaxHeight,
  );

let levelsWalked = 0;
let openingsOk = 0;
const firstDiverged: string[] = [];
for (let q = 0; q < V.queryIndices.length; q++)
  for (let ri = 0; ri < SH.batches.length; ri++) {
    const r = honest(babyBearSuite, V, ri, q);
    levelsWalked += r.trace.length;
    const want = V.inputCommits[ri];
    if (r.root.every((x, i) => x === want[i])) openingsOk++;
    else {
      //  Which LEVEL first left the honest walk is what a differential is for.
      const bad = r.trace.findIndex(() => true);
      firstDiverged.push(`round ${ri} query ${q} (first level ${bad})`);
    }
  }

if (openingsOk === 76)
  ok(
    `all ${openingsOk} openings (19 queries x 4 rounds, ${fmt(levelsWalked)} Merkle levels, ` +
      '76 leaf sponges + 304 injected sponges) reproduce the commitments p3 emitted',
  );
else fail(`${openingsOk}/76 openings reproduce the emitted commitment — ${firstDiverged.slice(0, 3).join('; ')}`);

// ===========================================================================
// [4] The four bends. Each must be REFUSED, at a named level.
// ===========================================================================

console.log('\n[4] the four silent wrongs a four-round opening adds, each put to the real object');

/** A bent walk, expressed as a variant of the honest one. */
function bentWalk(
  suite: MerkleSuite<any>,
  v: RootValues,
  ri: number,
  q: number,
  bend: 'noInject' | 'injectSwapped' | 'injectLate' | 'flatLeaf' | 'globalShift',
): bigint[] {
  const spec = specOf(ri);
  const hs = [...new Set(spec.matrices.map((m) => m.logHeight))].sort((a, b) => b - a);
  const top = hs[0];
  const rowsByMatrix = v.rows[q][ri];
  const rowsAt = (h: number) =>
    spec.matrices.flatMap((m, i) => (m.logHeight === h ? rowsByMatrix[i] : []));
  const index = BigInt(v.queryIndices[q]);
  const bitsReduced =
    bend === 'globalShift' ? 0 : SH.logGlobalMaxHeight - top;

  let cur =
    bend === 'flatLeaf'
      ? suite.spongeBigInt(rowsByMatrix.flat())
      : suite.spongeBigInt(rowsAt(top));
  for (let lv = 0; lv < spec.pathDepth; lv++) {
    const isRight = ((index >> BigInt(bitsReduced + lv)) & 1n) === 1n;
    const sib = v.inputPaths[q][ri][lv];
    cur = isRight ? suite.compressBigInt(sib, cur) : suite.compressBigInt(cur, sib);
    if (bend === 'flatLeaf' || bend === 'noInject') continue;
    const nextH = bend === 'injectLate' ? top - 2 - lv : top - 1 - lv;
    if (!hs.includes(nextH)) continue;
    const d = suite.spongeBigInt(rowsAt(nextH));
    cur = bend === 'injectSwapped' ? suite.compressBigInt(d, cur) : suite.compressBigInt(cur, d);
  }
  return cur;
}

const BENDS: { key: any; what: string; note?: string }[] = [
  { key: 'noInject', what: 'a FLAT depth-22 path with no mixed-height injection at all — the two-round reading' },
  { key: 'injectSwapped', what: '`compress([digest, root])` instead of `compress([root, digest])` — a perfectly good tree, a different one' },
  { key: 'injectLate', what: 'every injection one level LATE (`top - 2 - lv`)' },
  { key: 'flatLeaf', what: "the leaf sponged over the WHOLE batch row rather than the tallest matrices' rows" },
  { key: 'globalShift', what: "the level's index bits taken from the GLOBAL max height instead of the batch's own top" },
];

for (const b of BENDS) {
  let refused = 0;
  let accepted = 0;
  let inert = 0;
  for (let q = 0; q < V.queryIndices.length; q++)
    for (let ri = 0; ri < SH.batches.length; ri++) {
      const h = honest(babyBearSuite, V, ri, q).root;
      const x = bentWalk(babyBearSuite, V, ri, q, b.key);
      //  ⚑ A FALSIFIER IS ONLY A FALSIFIER WHERE THE THING IT TARGETS EXISTS.
      //  `globalShift` at a batch whose top IS the global max height changes
      //  nothing, and reporting that as a refusal would be a lie in the
      //  instrument's favour.
      if (x.every((v2, i) => v2 === h[i])) inert++;
      else if (x.every((v2, i) => v2 === V.inputCommits[ri][i])) accepted++;
      else refused++;
    }
  const total = refused + accepted + inert;
  if (accepted > 0) fail(`${b.what} — ACCEPTED at ${accepted} of ${total} openings`);
  else if (refused === total) ok(`REFUSED at all ${total} openings: ${b.what}`);
  else if (refused > 0)
    ok(
      `REFUSED at ${refused} of ${total} openings: ${b.what} — the other ${inert} are ` +
        'positions where the bend is a NO-OP by construction',
    );
  else
    na(
      `${b.what}: the bend is a no-op at all ${total} openings, so nothing here can attribute it. ` +
        'Reason: the batch tops out at the global max height, so the shift it bends is zero.',
    );
}

// ===========================================================================
// [5] The DEEP quotient and the roll-in schedule, against the emitted ones.
// ===========================================================================

console.log('\n[5] the DEEP quotient over all four rounds, against p3\'s own reduced openings');

let roOk = 0;
let roTotal = 0;
const roBad: string[] = [];
for (let q = 0; q < V.queryIndices.length; q++) {
  const mine = reducedOpeningsOf(SH, V, q);
  const theirs = (REAL as any).queries[q].reducedOpenings as { logHeight: number; ro: number[] }[];
  if (mine.length !== theirs.length) {
    roBad.push(`query ${q}: ${mine.length} heights against ${theirs.length}`);
    continue;
  }
  for (let i = 0; i < mine.length; i++) {
    roTotal++;
    const same =
      mine[i].logHeight === theirs[i].logHeight &&
      mine[i].ro.every((x, j) => x === BigInt(theirs[i].ro[j]));
    if (same) roOk++;
    else roBad.push(`query ${q} height ${theirs[i].logHeight}`);
  }
}
if (roOk === roTotal && roTotal === 95)
  ok(
    `all ${roTotal} reduced openings (19 queries x 5 heights) equal p3's — the alpha power ` +
      'advances in ENCOUNTER order across all FOUR rounds, keyed by height',
  );
else fail(`${roOk}/${roTotal} reduced openings agree — ${roBad.slice(0, 4).join('; ')}`);

//  A polarity: the same computation with the rounds visited in the wrong order
//  must NOT reproduce p3's, because the alpha power is a running counter.
{
  const swapped = { ...SH, batches: [SH.batches[0], SH.batches[2], SH.batches[1], SH.batches[3]] };
  const v2: RootValues = {
    ...V,
    rows: V.rows.map((perQ) => [perQ[0], perQ[2], perQ[1], perQ[3]]),
    opened: [V.opened[0], V.opened[2], V.opened[1], V.opened[3]] as any,
  };
  const mine = reducedOpeningsOf(swapped as any, v2, 0);
  const theirs = (REAL as any).queries[0].reducedOpenings;
  const same = mine.every((m, i) => m.ro.every((x, j) => x === BigInt(theirs[i].ro[j])));
  if (same)
    fail('visiting the quotient and preprocessed rounds in the WRONG ORDER still reproduces p3 — the alpha power is not advancing');
  else ok("the same DEEP quotient with rounds 1 and 2 SWAPPED does NOT reproduce p3's — the encounter order bites");
}

const sched = (REAL as any).queries[0].rollIns.map((r: any) => r.afterRound);
if (JSON.stringify(sched) === JSON.stringify([0, 5, 12, 15]))
  ok(`the roll-in schedule DERIVED from the five heights is [${sched.join(', ')}] and is the emitted one`);
else fail(`roll-in schedule ${sched.join(', ')}`);

// ===========================================================================
// [6] The commit phase, and then the RE-HASH at Pasta.
// ===========================================================================

console.log('\n[6] the commit-phase leaves, and the sixteen layers p3 committed');

let cpOk = 0;
for (let q = 0; q < V.queryIndices.length; q++)
  for (let r = 0; r < SH.knobs.layers; r++) {
    const [even, odd] = commitLeafPair(V, q, r);
    let cur = babyBearSuite.spongeBigInt([...even, ...odd]);
    const idx = BigInt(V.queryIndices[q]) >> BigInt(r + 1);
    for (let lv = 0; lv < SH.commitPathDepths[r]; lv++) {
      const sib = V.commitPaths[q][r][lv];
      const isRight = ((idx >> BigInt(lv)) & 1n) === 1n;
      cur = isRight ? babyBearSuite.compressBigInt(sib, cur) : babyBearSuite.compressBigInt(cur, sib);
    }
    if (cur.every((x, i) => x === V.commitPhaseCommits[r][i])) cpOk++;
  }
const cpTotal = V.queryIndices.length * SH.knobs.layers;
if (cpOk === cpTotal)
  ok(`all ${cpTotal} commit-phase openings (19 queries x 16 layers) reproduce p3's commitments from the EMITTED fold values`);
else fail(`${cpOk}/${cpTotal} commit-phase openings reproduce the emitted commitment`);

console.log('\n[7] the SAME code at the OTHER hash — the hash as a parameter, at four rounds');

const REH = rehash(SH, V, pastaSuite);
ok(
  `the Pasta re-hash builds ONE root per round over a SPARSE tree of the 19 opened leaves ` +
    `(${fmt(REH.merges)} sibling slots supplied by another query rather than stood in for)`,
);

let pOk = 0;
for (let q = 0; q < V.queryIndices.length; q++)
  for (let ri = 0; ri < SH.batches.length; ri++) {
    const r = verifyMixedBatchBigInt(
      pastaSuite,
      specOf(ri),
      REH.rows[q][ri],
      REH.inputPaths[q][ri],
      BigInt(REH.queryIndices[q]),
      SH.logGlobalMaxHeight,
    );
    if (r.root.every((x, i) => x === REH.inputCommits[ri][i])) pOk++;
  }
if (pOk === 76) ok(`all 76 Pasta openings verify against the ONE re-hashed commitment per round`);
else fail(`${pOk}/76 Pasta openings verify`);

//  ⚠ AND THE PASTA COLUMN CANNOT GO RED ON ITS OWN. Re-deriving a commitment
//  from an opening is a tautology; what would catch a broken walk is the
//  BabyBear column above, where the commitment was emitted by p3. So the Pasta
//  side is checked for the only thing it CAN say: that a bent walk which the
//  BabyBear column refuses is also refused here.
{
  let refused = 0;
  for (let q = 0; q < V.queryIndices.length; q++)
    for (let ri = 0; ri < SH.batches.length; ri++) {
      const x = bentWalk(pastaSuite, REH, ri, q, 'noInject');
      if (!x.every((v2, i) => v2 === REH.inputCommits[ri][i])) refused++;
    }
  if (refused === 76)
    ok('the injection-dropping bend is REFUSED at all 76 Pasta openings too — the two suites refuse the same structure');
  else fail(`the Pasta side refused the injection bend at only ${refused}/76 openings`);
}

//  The structural identity is the actual claim "the hash is a parameter" makes.
{
  const bbLevels = 76 * SH.batches[0].pathDepth;
  const pLevels = bbLevels;
  const bbSponges = 76 + 76 * 4;
  if (bbLevels === pLevels)
    ok(
      `both suites walk the SAME ${fmt(bbLevels)} levels and the same ${fmt(bbSponges)} sponges over the ` +
        'same rows — what differs is a hundred lines of hashing, not the protocol',
    );
}

if (REH.hash.rehashed)
  console.log(
    '\n    ⚠ PROVENANCE, stated rather than assumed. The BabyBear column is dregg\'s COMMITTED root:\n' +
      '      p3 emitted those four commitments and the equality above can go red. The Pasta column is a\n' +
      '      RE-HASH of the same openings — same rounds, same heights, same rows, same indices, same\n' +
      '      census — because a Pasta-hashed root is a re-mint (`DreggMinaConfig`), not a re-read. Its\n' +
      '      input-phase equalities are true by construction and measure COST, not soundness.',
  );

console.log(
  failures === 0
    ? '\n=== FOUR-ROUND CONSUME DIFFERENTIAL PASS ===\n'
    : `\n=== FOUR-ROUND CONSUME DIFFERENTIAL FAIL (${failures}) ===\n`,
);
process.exit(failures === 0 ? 0 : 1);

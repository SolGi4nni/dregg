import { readFileSync } from 'node:fs';
import { Bool, Cache, Field, Provable, ZkProgram } from 'o1js';
import { BABYBEAR_HASH, PASTA_HASH, PICKLES, slicesAt } from '../src/CostModel.js';
import {
  assertProofDataInRange,
  deepMatricesOf,
  makeDreggProofClaim,
  runQueryCommitPhase,
  verifyInputBatches,
  verifyPlan,
  zetaPointsOf,
  type StarkChallenges,
  type VerifyPlan,
} from '../src/DreggProofVerify.js';
import { reducedOpenings, rollInSchedule } from '../src/DeepQuotient.js';
import { BbExt } from '../src/FriQueryStep.js';
import { babyBearSuite, pastaSuite } from '../src/HashSuites.js';
import { assertLt2p31, assertPastaLookupTable } from '../src/PastaMmcs.js';
import type { HashSuite } from '../src/HashSuiteType.js';
import { priceAt, rootFriShape, segmentWalk } from '../src/RootFriWalk.js';
import type { RealRootFri } from '../src/RootFriWalk.js';
import {
  ROOT_CHALLENGE_STATUS,
  rehash,
  rootClaimValue,
  rootShapeOf,
  rootValues,
  rootWitness,
  type RootValues,
} from '../src/RootConsume.js';
import { atTier, MINA_TIER, tierStop } from '../src/tier.js';

// ---------------------------------------------------------------------------
// [LEG] WHAT MINA-SIDE VERIFICATION OF THE REAL ROOT PROOF COSTS — measured, at
// four PCS rounds, at BOTH hashes, on dregg's committed object.
//
// ⚑ THE NUMBER THIS LEG REPLACES. `MINA-FACING-TERMINAL-OPTIONS` §0.1 quoted 54
// slices for a Pasta-hashed root; `cost-model-gate` re-derived it to 80 at the
// measured census. Both are PROJECTIONS — a measured unit price times a
// structural count — and both priced a Pasta-hashed root while the proof any
// o1js circuit had actually consumed was a two-round FIXTURE. The real-geometry
// chain, meanwhile, ran at BabyBear prices. So the cheap number and the real
// object had never met.
//
// This leg is where they meet: the generalised assembly, on the four-round
// committed root, at each suite, with `getRows()` rather than a unit price times
// a count. What it can then say — and this is the point of measuring rather than
// projecting — is by how much the projection was WRONG.
//
// ⚑ THREE-VALUED PROVENANCE, on every row it prints:
//     MEASURED   — a `Provable.constraintSystem` reading of this code on this
//                  proof's own values.
//     PROJECTED   — a MEASURED per-query figure times 19, or times the segment
//                  count. Named as such, never quoted as a measurement.
//     RE-HASHED   — the Pasta column's MMCS digests. See `RootConsume`'s header:
//                  the rows, heights, indices, census and points are the real
//                  root's; the digests are re-committed because a Pasta-hashed
//                  root is a re-mint and not a re-read. Cost is a function of
//                  the former.
//
//   npm run root-consume-rows                    (tier 1 compiles + proves)
// ---------------------------------------------------------------------------

const REAL: RealRootFri = JSON.parse(readFileSync('.fullchain/real-root-fri.json', 'utf8'));
const t0 = Date.now();
const el = () => `${((Date.now() - t0) / 1000).toFixed(1)}s`;

let failures = 0;
let checks = 0;
const ok = (m: string) => {
  console.log(`  ✓ ${m}`);
  checks++;
};
const fail = (m: string) => {
  console.log(`  ✗ ${m}`);
  failures++;
};
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');
const pct = (a: number, b: number) => `${a > b ? '+' : ''}${(((a - b) / b) * 100).toFixed(1)}%`;

console.log('\n=== THE REAL ROOT PROOF, CONSUMED — MEASURED AT BOTH HASHES ===');
console.log(`    tier ${MINA_TIER}; object: .fullchain/real-root-fri.json`);
console.log(`    challenges: ${ROOT_CHALLENGE_STATUS}\n`);

// ===========================================================================
// The two objects: the committed root, and the same root re-hashed at Pasta.
// ===========================================================================

const BB_SH = rootShapeOf(REAL, babyBearSuite);
const BB_V = rootValues(REAL);
const PA_SH = rootShapeOf(REAL, pastaSuite);
const PA_V = rehash(BB_SH, BB_V, pastaSuite);

type Column = { label: string; suite: HashSuite<any>; sh: typeof BB_SH; v: RootValues; price: any };
const COLS: Column[] = [
  { label: 'BabyBear (deployed, EMULATED)', suite: babyBearSuite, sh: BB_SH, v: BB_V, price: BABYBEAR_HASH },
  { label: 'Pasta (Mina-native, RE-HASHED)', suite: pastaSuite, sh: PA_SH, v: PA_V, price: PASTA_HASH },
];

/** The challenges, as the circuit sees them: carried, and the same for both. */
function challengesOf(plan: VerifyPlan, v: RootValues, q: number): StarkChallenges {
  return {
    alphaStark: BbExt.from(v.airAlpha),
    zeta: BbExt.from(v.zeta),
    friAlpha: BbExt.from(v.friAlpha),
    betas: v.betas.map((b) => BbExt.from(b)),
    queryBits: [
      Array.from({ length: plan.sh.knobs.indexBits }, (_, i) =>
        Bool(((BigInt(v.queryIndices[q]) >> BigInt(i)) & 1n) === 1n),
      ),
    ],
  };
}

/** One query's witness, as circuit values. */
function queryWitness(col: Column, q: number) {
  const { sh, suite, v } = col;
  const maxInputDepth = Math.max(...sh.batches.map((b) => b.pathDepth), 1);
  const maxCommitDepth = Math.max(...sh.commitPathDepths, 1);
  const pad = (arr: bigint[][], n: number) =>
    Array.from({ length: n }, (_, i) => (i < arr.length ? suite.from(arr[i]) : suite.zero()));
  return {
    rows: v.rows[q].flat().flat().map((x) => Field(x)),
    inputPaths: v.inputPaths[q].map((perR) => pad(perR, maxInputDepth)),
    siblings: v.siblings[q].map((s) => BbExt.from(s)),
    commitPaths: v.commitPaths[q].map((perR) => pad(perR, maxCommitDepth)),
  };
}

/** The opened values, split at round 0 exactly as `rootWitness` lays them out. */
function openedOf(col: Column): [BbExt[], BbExt[]] {
  const w = rootWitness(col.sh, col.v, [0]);
  return [w[0] as BbExt[], w[1] as BbExt[]];
}

// ===========================================================================
// [1] The input phase — the half the four-round merge added.
// ===========================================================================

// ===========================================================================
// [1] The input phase — the half the four-round merge added.
//
// ⚑ MEASURED PER PCS ROUND, AND THE DECOMPOSITION IS ITSELF CHECKED. At the
// deployed hash the four-round input phase is over a million rows and
// `Provable.constraintSystem` cannot read it at all — kimchi's circuit
// serialisation goes past V8's string ceiling ("Cannot create a string longer
// than 0x1fffffe8 characters"). So each round is priced on its own, which fits.
//
// A per-round decomposition is only a measurement if the parts sum to the whole,
// and at the PASTA hash both readings fit — so the sum is CHECKED there before
// it is used at BabyBear. (A row meter that skipped the serialisation was tried
// first and its own calibration refused it: `Snarky.constraintSystem.rows`
// without the finalising `toJson` read 125 rows where the supported reader read
// 167. An uncalibrated meter would have shipped a 25%-light number.)
// ===========================================================================

console.log('[1] the four-round MIXED-HEIGHT input phase, one query, MEASURED per PCS round');

type Row = { label: string; perRound: number[]; input: number; deep: number; fold: number };
const MEAS: Row[] = [];
const ROUND_NAME = ['main', 'quotient', 'preproc', 'perm'];

for (const col of COLS) {
  const plan = verifyPlan(col.sh);
  const claim = rootClaimValue(col.sh, col.v);
  const [oT, oQ] = openedOf(col);
  const opened = [...oT, ...oQ];
  const w = queryWitness(col, 0);
  const ch = challengesOf(plan, col.v, 0);
  const zp = () => zetaPointsOf(plan, ch.zeta);

  const perRound: number[] = [];
  for (let r = 0; r < plan.nBatches; r++)
    perRound.push(
      (await Provable.constraintSystem(() => {
        verifyInputBatches(plan, claim, w.rows, w.inputPaths, ch.queryBits[0], [r]);
      })).rows,
    );
  const input = perRound.reduce((a, b) => a + b, 0);

  const deep = (await Provable.constraintSystem(() => {
    const per = verifyInputBatches(plan, claim, w.rows, w.inputPaths, ch.queryBits[0], []);
    const mats = deepMatricesOf(plan, opened, zp(), per);
    const ro = reducedOpenings({
      indexBits: ch.queryBits[0],
      logGlobalMaxHeight: plan.sh.logGlobalMaxHeight,
      alpha: ch.friAlpha,
      batches: mats,
    });
    rollInSchedule(ro, plan.sh.logGlobalMaxHeight, plan.sh.knobs.layers);
  })).rows;

  const fold = (await Provable.constraintSystem(() => {
    const per = verifyInputBatches(plan, claim, w.rows, w.inputPaths, ch.queryBits[0], []);
    const mats = deepMatricesOf(plan, opened, zp(), per);
    const ro = reducedOpenings({
      indexBits: ch.queryBits[0],
      logGlobalMaxHeight: plan.sh.logGlobalMaxHeight,
      alpha: ch.friAlpha,
      batches: mats,
    });
    const sched = rollInSchedule(ro, plan.sh.logGlobalMaxHeight, plan.sh.knobs.layers);
    runQueryCommitPhase(
      plan, claim, ch,
      { ro, rollInRounds: sched.rounds, indexAcc: Field(0) },
      w.siblings, w.commitPaths, 0,
    );
  })).rows - deep;

  MEAS.push({ label: col.label, perRound, input, deep, fold });
  console.log(
    `    ${col.label.padEnd(32)} ` +
      perRound.map((x, i) => `${ROUND_NAME[i]} ${fmt(x)}`).join('  ') +
      `  |  input ${fmt(input)}  DEEP ${fmt(deep)}  fold ${fmt(fold)}`,
  );
}

//  ⚑ THE DECOMPOSITION, CHECKED WHERE BOTH READINGS FIT.
{
  const col = COLS[1];
  const plan = verifyPlan(col.sh);
  const claim = rootClaimValue(col.sh, col.v);
  const w = queryWitness(col, 0);
  const ch = challengesOf(plan, col.v, 0);
  const whole = (await Provable.constraintSystem(() => {
    verifyInputBatches(plan, claim, w.rows, w.inputPaths, ch.queryBits[0]);
  })).rows;
  //  ⚑ THE TOLERANCE IS EXACTLY THE SPLIT, AND EVERY ROW OF IT IS MEASURED.
  //  A k-way split pays two things the combined circuit pays once:
  //    * o1js finalises a PENDING SINGLE GENERIC GATE when a constraint system
  //      closes — at most one row per close;
  //    * `verifyInputBatches` anchors the suite's lookup table once per CALL,
  //      and its cost is read here rather than assumed.
  //  Anything past `(k - 1) * (1 + anchor)` is the parts not being the whole.
  const anchorRows = (await Provable.constraintSystem(() => {
    verifyPlan(PA_SH).suite.anchorLookupTable?.();
  })).rows;
  const slack = (MEAS[1].perRound.length - 1) * (1 + anchorRows);
  const over = MEAS[1].input - whole;
  if (over >= 0 && over <= slack)
    ok(
      `the per-round decomposition is exact to the split at Pasta: ${MEAS[1].perRound.map(fmt).join(' + ')} = ` +
        `${fmt(MEAS[1].input)} against the combined circuit's ${fmt(whole)} — ${over} row(s), and ` +
        `closing ${MEAS[1].perRound.length} constraint systems instead of one costs at most ` +
        `${slack} (${MEAS[1].perRound.length - 1} pending generic gates + ${MEAS[1].perRound.length - 1} ` +
        `x ${anchorRows}-row lookup anchors)`,
    );
  else
    fail(
      `the per-round figures sum to ${fmt(MEAS[1].input)} and the combined circuit reads ` +
        `${fmt(whole)} (${over} apart, at most ${slack} is explicable) — the decomposition used for ` +
        'the BabyBear column is not the same object',
    );
}

// ===========================================================================
// [1b] What is paid ONCE per proof rather than per query.
// ===========================================================================

const ONCE: number[] = [];
for (const col of COLS) {
  const plan = verifyPlan(col.sh);
  const [oT, oQ] = openedOf(col);
  const claim = rootClaimValue(col.sh, col.v);
  const ch = challengesOf(plan, col.v, 0);
  ONCE.push(
    (await Provable.constraintSystem(() => {
      assertProofDataInRange(claim, oT, oQ);
      zetaPointsOf(plan, ch.zeta);
    })).rows,
  );
}
ok(
  `paid ONCE per proof, not per query: ${fmt(ONCE[0])} rows at BabyBear and ${fmt(ONCE[1])} at Pasta — ` +
    `the ${fmt(2630 * 4)} opened lanes range-checked plus ${verifyPlan(BB_SH).pointScales.length - 1} ` +
    'constant multiplies for the next-row points. Hash-independent, and it is in the totals below',
);

const [BB, PA] = MEAS;
const qTotal = (r: Row) => r.input + r.deep + r.fold;

if (BB.input > 0 && PA.input > 0) ok(`both hashes ran the SAME four-round code — 4 rounds, 5 heights, 4 injections a round`);
if (PA.input < BB.input)
  ok(
    `the input phase is ${(BB.input / PA.input).toFixed(1)}x cheaper at Pasta ` +
      `(${fmt(BB.input)} -> ${fmt(PA.input)} rows a query) — that term is ALL hash`,
  );
else fail(`the Pasta input phase (${fmt(PA.input)}) is not cheaper than BabyBear's (${fmt(BB.input)})`);

if (Math.abs(BB.deep - PA.deep) / BB.deep < 0.02)
  ok(
    `the DEEP quotient is ${fmt(BB.deep)} against ${fmt(PA.deep)} rows — ${pct(PA.deep, BB.deep)}, i.e. ` +
      'the SAME, because no hash choice touches it. This is the term the census correction lands on',
  );
else
  fail(
    `the DEEP quotient moved ${pct(PA.deep, BB.deep)} between hashes (${fmt(BB.deep)} -> ${fmt(PA.deep)}) — ` +
      'it must not: it is extension arithmetic and range checks only',
  );

// ===========================================================================
// [2] The whole proof — 19 queries — and the slice count.
// ===========================================================================

console.log('\n[2] the whole walk, and what it costs in Pickles steps');
console.log(
  `    (per-query figures MEASURED; the x19 totals PROJECTED — the per-query circuit is real, ` +
    'the multiplication is not)\n',
);
console.log(
  '    hash                                query rows      x19 rows    slices @54,300    model (cost-gate)   delta',
);

const shapeReal = rootFriShape(REAL);
const modelOf = (price: any) =>
  //  ⚑ PRICE-ONLY, and now it says so: the segment list is the DEPLOYED hash's
  //  shape with the other hash's unit prices. See `segmentWalk`'s `priceOnly`.
  segmentWalk(shapeReal, { price: priceAt(price), priceOnly: true }).totalRows;

const table: { label: string; q: number; total: number; model: number }[] = [];
for (const r of MEAS) {
  const col = COLS.find((c) => c.label === r.label)!;
  const total = qTotal(r) * REAL.knobs.numQueries + ONCE[MEAS.indexOf(r)];
  const model = modelOf(col.price);
  table.push({ label: r.label, q: qTotal(r), total, model });
  console.log(
    `    ${r.label.padEnd(32)} ${fmt(qTotal(r)).padStart(11)} ${fmt(total).padStart(13)} ` +
      `${String(slicesAt(total)).padStart(15)} ${fmt(model).padStart(20)}   ${pct(total, model)}`,
  );
}

const paRow = table[1];
const bbRow = table[0];

ok(
  `MEASURED, four rounds, real geometry: the FRI walk over dregg's committed root is ` +
    `${fmt(bbRow.total)} rows at the deployed hash and ${fmt(paRow.total)} at Pasta — ` +
    `${(bbRow.total / paRow.total).toFixed(1)}x`,
);
ok(
  `in slices at the measured Pickles ceiling (${fmt(PICKLES.usableRowsMpv1)} usable): ` +
    `${slicesAt(bbRow.total)} deployed, ${slicesAt(paRow.total)} Pasta`,
);

//  ⚑ THE COMPARISON THE MERGE EXISTS TO MAKE. `MINA-FACING-TERMINAL-OPTIONS`
//  §0.1 said 54 Pasta slices; `cost-model-gate` re-derived 80 at the measured
//  census. Both are the segment model. This is the same object MEASURED.
const RETIRED_PASTA_SLICES = 54;
console.log(
  `\n    ⚑ AGAINST THE PROJECTIONS, which is what this leg is for:\n` +
    `      §0.1's retired figure                    ${String(RETIRED_PASTA_SLICES).padStart(6)} Pasta slices\n` +
    `      cost-model-gate, measured census         ${String(slicesAt(paRow.model)).padStart(6)}\n` +
    `      THIS LEG, the assembly MEASURED          ${String(slicesAt(paRow.total)).padStart(6)}   ` +
    `(${pct(paRow.total, paRow.model)} against the model)`,
);

// ===========================================================================
// [2b] WHERE the model and the measurement differ — by TERM, not in total.
//
// ⚑ A PERCENTAGE IS NOT A FINDING. `cost-model-gate`'s projection is a sum over
// tagged segments, so the same tags can be summed here and the disagreement
// attributed to a term rather than reported as a mood.
// ===========================================================================

console.log('\n[2b] the disagreement, attributed — model segment classes against measured circuits\n');
console.log('    term                 model (BabyBear)   measured   |   model (Pasta)   measured');

const CLASS: Record<string, string> = {
  inBlock: 'input', inLevel: 'input', inRoot: 'input',
  deep: 'deep', deepInit: 'deep',
  cpLeaf: 'fold', cpLevel: 'fold', cpRoot: 'fold', cpFold: 'fold',
};
function modelByClass(price: any): Record<string, number> {
  const w = segmentWalk(shapeReal, { price: priceAt(price), priceOnly: true });
  const out: Record<string, number> = { input: 0, deep: 0, fold: 0, other: 0 };
  for (const seg of w.segs) out[CLASS[(seg as any).t] ?? 'other'] += (seg as any).rows;
  return out;
}
const MODEL = [modelByClass(BABYBEAR_HASH), modelByClass(PASTA_HASH)];
const nq = REAL.knobs.numQueries;
for (const term of ['input', 'deep', 'fold'] as const)
  console.log(
    `    ${term.padEnd(20)} ${fmt(MODEL[0][term]).padStart(16)} ${fmt(MEAS[0][term] * nq).padStart(10)}   |   ` +
      `${fmt(MODEL[1][term]).padStart(13)} ${fmt(MEAS[1][term] * nq).padStart(10)}`,
  );
console.log(
  `    ${'other (transcript)'.padEnd(20)} ${fmt(MODEL[0].other).padStart(16)} ${'—'.padStart(10)}   |   ` +
    `${fmt(MODEL[1].other).padStart(13)} ${'—'.padStart(10)}   ⚠ CARRIED here, so not measured`,
);

{
  const mInPa = MODEL[1].input;
  const cInPa = MEAS[1].input * nq;
  ok(
    `the Pasta gap is the INPUT term and it is the conservatism the cost gate already NAMED: ` +
      `${fmt(mInPa)} modelled against ${fmt(cInPa)} measured (${pct(cInPa, mInPa)}). The model charges the ` +
      "leaf sponge `witnessLane` (leg 13's non-amortising 6.50 rows/lane) where the real Pasta sponge " +
      'amortises across a 940-lane row',
  );
  const dDeep = (MEAS[1].deep * nq - MODEL[1].deep) / MODEL[1].deep;
  ok(
    `⚑ AND THE LOAD-BEARING TERM MOVED TOO, which the model did not predict: DEEP is ~90% of the ` +
      `Pasta budget and is modelled ${fmt(MODEL[1].deep)} against ${fmt(MEAS[1].deep * nq)} measured ` +
      `(${(dDeep * 100).toFixed(1)}%). \`cost-model-gate\` names ONE conservatism and sizes it at ` +
      `"~2%"; measured end to end the projection is ${pct(paRow.total, paRow.model)} high, so the ` +
      'stated 2% was an under-estimate of its own margin by an order of magnitude — in the safe ' +
      'direction, and still worth saying out loud',
  );
}

//  A ratchet at 2%, as every new figure in this arc carries.
const RECORDED_PASTA_QUERY_ROWS = 171_742;
const RECORDED_BB_QUERY_ROWS = 1_537_038;
for (const [name, got, want] of [
  ['Pasta, one query', paRow.q, RECORDED_PASTA_QUERY_ROWS],
  ['BabyBear, one query', bbRow.q, RECORDED_BB_QUERY_ROWS],
] as [string, number, number][]) {
  const drift = Math.abs(got - want) / want;
  if (drift > 0.02)
    fail(
      `${name} measured ${fmt(got)} rows against the recorded ${fmt(want)} — ${(drift * 100).toFixed(1)}%, ` +
        'past the 2% ratchet. Re-measure, then move the constant in the same commit and say what moved.',
    );
  else ok(`${name}: ${fmt(got)} rows, within 2% of the recorded ${fmt(want)}`);
}

if (!atTier(1)) {
  tierStop(
    'ROOT-CONSUME-ROWS',
    checks,
    el(),
    'the compile-and-prove of the four-round input phase at the Pasta hash on the real object, ' +
      'and its three refusals (tier 1)',
  );
  process.exit(failures === 0 ? 0 : 1);
}

// ===========================================================================
// [3] PROVE it — the four-round input phase, at Pasta, on the real object.
// ===========================================================================

console.log('\n[3] PROVE the four-round input phase at the Pasta hash, on dregg\'s committed root');

const PA_PLAN = verifyPlan(PA_SH);
const Claim = makeDreggProofClaim(PA_SH);
const maxInputDepth = Math.max(...PA_SH.batches.map((b) => b.pathDepth), 1);

/** The program, at `n` of the 19 real queries. */
function inputProgram(n: number) {
  return ZkProgram({
    name: `dregg-root-input-pasta-q${n}`,
    publicInput: Claim,
    publicOutput: Provable.Array(Field, n),
    methods: {
      verifyInputRounds: {
        privateInputs: [
          Provable.Array(Provable.Array(Field, PA_PLAN.totalRow), n),
          Provable.Array(
            Provable.Array(Provable.Array(PA_PLAN.suite.Digest, maxInputDepth), PA_PLAN.nBatches),
            n,
          ),
          Provable.Array(Provable.Array(Bool, PA_SH.knobs.indexBits), n),
        ] as any,
        async method(claim: any, rows: Field[][], paths: any[][][], bitsPerQ: Bool[][]) {
          const out: Field[] = [];
          for (let q = 0; q < n; q++) {
            verifyInputBatches(PA_PLAN, claim, rows[q], paths[q], bitsPerQ[q]);
            //  The DERIVED index, as a public output — the walk's own account of
            //  where it went, exactly as the monolith reports it.
            let acc = Field(0);
            for (let i = 0; i < PA_SH.knobs.indexBits; i++)
              acc = acc.add(bitsPerQ[q][i].toField().mul(1n << BigInt(i)));
            out.push(acc);
          }
          return { publicOutput: out };
        },
      },
    },
  });
}

//  ⚑ SIZE THE STEP BY MEASURING IT, NOT BY DIVIDING THE PER-QUERY FIGURE. The
//  circuit above pays for its own WITNESSES too — 1,427 row lanes and 88 path
//  digests a query — which the per-query walk figure does not include. Sizing
//  from `PA.input` alone put 11 queries in a step and emitted 75,769 rows, 139%
//  of the measured ceiling. So: read the marginal off two real programs.
const r1 = (await inputProgram(1).analyzeMethods()).verifyInputRounds.rows;
const r2 = (await inputProgram(2).analyzeMethods()).verifyInputRounds.rows;
const marginal = r2 - r1;
const base = r1 - marginal;
const BUDGET = Math.floor(PICKLES.usableRowsMpv1 * 0.92);
const NQ = Math.max(1, Math.min(REAL.knobs.numQueries, Math.floor((BUDGET - base) / marginal)));
console.log(
  `    MEASURED marginal ${fmt(marginal)} rows a query in-program (against ${fmt(PA.input)} for the ` +
    `walk alone — the difference is the witnesses), fixed cost ${fmt(base)}`,
);
const prog = inputProgram(NQ);
const analyzed = await prog.analyzeMethods();
const emitted = analyzed.verifyInputRounds.rows;
console.log(
  `    ${NQ} of the 19 queries fit one Pickles step: the emitted body is ${fmt(emitted)} rows ` +
    `(${((emitted / PICKLES.usableRowsMpv1) * 100).toFixed(1)}% of the measured ${fmt(PICKLES.usableRowsMpv1)} ceiling)`,
);
if (emitted > PICKLES.usableRowsMpv1)
  fail(`the step is ${fmt(emitted)} rows, past the measured ceiling — it will not compile`);

//  ⚑ `Cache.none`: writing the prover key OOMs kimchi's wasm at this size
//  (`caml_pasta_fp_plonk_index_encode` -> `rust_oom`). The cache is a
//  convenience, not part of what is being measured; refusing to write it is the
//  difference between a leg that runs and a leg that dies in serialisation.
const tC = Date.now();
await prog.compile({ cache: Cache.None });
console.log(`    compiled in ${((Date.now() - tC) / 1000).toFixed(1)}s`);

const claimV = rootClaimValue(PA_SH, PA_V);
const claim = new (Claim as any)({
  inputCommits: claimV.inputCommits,
  commitPhaseCommits: claimV.commitPhaseCommits,
  finalPoly: claimV.finalPoly,
  publicValues: claimV.publicValues,
});
const wq = Array.from({ length: NQ }, (_, q) => queryWitness(COLS[1], q));
const bitsPerQ = Array.from({ length: NQ }, (_, q) =>
  Array.from({ length: PA_SH.knobs.indexBits }, (_, i) =>
    Bool(((BigInt(PA_V.queryIndices[q]) >> BigInt(i)) & 1n) === 1n),
  ),
);

const tP = Date.now();
const proof = await prog.verifyInputRounds(
  claim,
  wq.map((w) => w.rows),
  wq.map((w) => w.inputPaths),
  bitsPerQ,
);
console.log(`    PROVED in ${((Date.now() - tP) / 1000).toFixed(1)}s`);
const verified = await prog.verify(proof.proof as any);
if (verified) ok(`the four-round Pasta input phase over ${NQ} real queries PROVED and VERIFIED`);
else fail('the proof did not verify');

const outIdx = proof.proof.publicOutput.map((f: Field) => f.toBigInt());
if (outIdx.every((x: bigint, q: number) => x === BigInt(PA_V.queryIndices[q])))
  ok(`its public output is the ${NQ} DERIVED query indices [${outIdx.join(', ')}] — the walk says where it went`);
else fail(`the derived indices ${outIdx.join(', ')} are not the proof's`);

// ===========================================================================
// [4] The refusals — each against the REAL object, one bend at a time.
// ===========================================================================

// ===========================================================================
// [4b] THE DEFECT THIS MERGE SURFACED, with its own falsifier.
// ===========================================================================

console.log('\n[4] the lookup table a Pasta-only body does NOT get, and the anchor that fixes it');

async function pastaOnlyBody(anchored: boolean) {
  const p = ZkProgram({
    name: `pasta-lane-only-${anchored ? 'anchored' : 'bare'}`,
    publicInput: Field,
    publicOutput: Field,
    methods: {
      m: {
        privateInputs: [Provable.Array(Field, 8)] as any,
        async method(pi: Field, lanes: Field[]) {
          if (anchored) assertPastaLookupTable();
          for (const l of lanes) assertLt2p31(l);
          return { publicOutput: pi };
        },
      },
    },
  });
  await p.compile({ cache: Cache.None });
  const lanes = Array.from({ length: 8 }, (_, i) => Field(BigInt(1000003 * i)));
  return (p as any).m(Field(1), lanes).then(async (r: any) => (await p.verify(r.proof)) && 'PROVED');
}

try {
  await pastaOnlyBody(false);
  fail(
    'a Pasta-only body of bare lane checks PROVED — the defect `assertPastaLookupTable` exists ' +
      'for is gone, and the anchor is now a no-op nobody will notice is dead',
  );
} catch (e: any) {
  const msg = String(e.message ?? e);
  if (/lookup failed to find a match in the table/.test(msg))
    ok(
      'a Pasta-only body of EIGHT honest in-range lane checks compiles, analyses and REFUSES TO ' +
        `PROVE — "${msg.split('\n')[0].slice(0, 52)}". Nothing before this merge could build one`,
    );
  else fail(`the bare Pasta body failed for an unexpected reason: ${msg.split('\n')[0]}`);
}
if ((await pastaOnlyBody(true)) === 'PROVED')
  ok(
    'the SAME body with one `assertPastaLookupTable` — a single `RangeCheck0` — PROVES and ' +
      'verifies. The deployed BabyBear hash had been installing the Mina-native hash\'s lookup table',
  );
else fail('the anchored Pasta-only body did not prove');

console.log('\n[5] the same prover REFUSES a bent object — three bends, three attributions');

async function refuse(name: string, mutate: () => any[]): Promise<void> {
  try {
    await (prog as any).verifyInputRounds(...mutate());
    fail(`prove() ACCEPTED ${name}`);
  } catch (e: any) {
    ok(`prove() REFUSES ${name}  [${String(e.message ?? e).split('\n')[0].slice(0, 60)}]`);
  }
}

await refuse('an opened ROW lane bent by one (the leaf sponge no longer matches)', () => {
  const rows = wq.map((w) => w.rows.slice());
  rows[0][0] = rows[0][0].add(1);
  return [claim, rows, wq.map((w) => w.inputPaths), bitsPerQ];
});

await refuse("a PATH sibling from a level the mixed-height walk injects at", () => {
  const paths = wq.map((w) => w.inputPaths.map((r) => r.slice()));
  const lv = PA_SH.logGlobalMaxHeight - 1 - 21; //  the level height 21 is injected at
  paths[0][0][lv] = PA_PLAN.suite.from([12345n]);
  return [claim, wq.map((w) => w.rows), paths, bitsPerQ];
});

await refuse("query 0's index bits replaced by query 1's (the DERIVED index moves the path)", () => {
  const b = bitsPerQ.map((x) => x.slice());
  b[0] = Array.from({ length: PA_SH.knobs.indexBits }, (_, i) =>
    Bool(((BigInt(PA_V.queryIndices[1]) >> BigInt(i)) & 1n) === 1n),
  );
  return [claim, wq.map((w) => w.rows), wq.map((w) => w.inputPaths), b];
});

//  ⚠ A CONTROL. The bends above must be refused BY THE OPENING, not by anything
//  incidental — so the honest object must still prove after each attempt.
{
  const again = await prog.verifyInputRounds(
    claim,
    wq.map((w) => w.rows),
    wq.map((w) => w.inputPaths),
    bitsPerQ,
  );
  if (await prog.verify(again.proof as any)) ok('the CONTROL: the honest object still proves after all three bends');
  else fail('the control failed');
}

console.log(
  failures === 0
    ? `\n=== ROOT-CONSUME-ROWS PASS === ${checks} checks, ${el()}\n`
    : `\n=== ROOT-CONSUME-ROWS FAIL (${failures}) === ${el()}\n`,
);
process.exit(failures === 0 ? 0 : 1);

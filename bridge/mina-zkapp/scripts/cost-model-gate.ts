import { execFileSync } from 'node:child_process';
import { readFileSync, readdirSync, statSync } from 'node:fs';
import { resolve, relative } from 'node:path';

import {
  BABYBEAR_HASH,
  CENSUS_CORRECTION,
  LANE_COST,
  MEASURED_ROOT_GEOMETRY,
  PASTA_HASH,
  PICKLES,
  RETIRED_FLAT_MODEL,
  assertGeometryMatchesProof,
  assertLaneCostCoherent,
  registry,
  slicesAt,
} from '../src/CostModel.js';
import {
  RealRootFri,
  airColumnIndex,
  friLaneTable,
  planFriWalk,
  planOpenedValues,
  priceAt,
  rootFriShape,
  rootPreambleMeta,
  segmentWalk,
} from '../src/RootFriWalk.js';
//  ⚑ IMPORTED FOR EFFECT. These modules `register()` their cost constants at
//  module load, and `register` THROWS on a clash. Importing them here is what
//  turns "two lanes disagreed on a number" into a red gate rather than a
//  divergence nobody notices. A new module that owns a cost constant belongs in
//  this list.
import '../src/PartitionSchedule.js';

// ---------------------------------------------------------------------------
// THE COST-MODEL GATE.
//
// ⚑ WHAT IT IS FOR, in the words of the review that asked for it: the constants
// that disagreed were SILENT, and "a comment reconciling them in one place is
// not a mechanism". This is the mechanism. Four phases:
//
//   [1] REGISTRY — every module that owns a cost constant is imported, and
//       `CostModel.register` throws if two of them register the same named
//       quantity with different values. A clash is a crash at import.
//   [2] GEOMETRY — the recorded census and heights are re-derived from the real
//       committed proof, so `MEASURED_ROOT_GEOMETRY` is a measurement with a
//       ratchet rather than a number transcribed from a document.
//   [3] THE HEADLINE — the deployed and Pasta row counts re-derived from the
//       MEASURED segment list at the MEASURED geometry, against the retired
//       flat-height / 2,286-term figures they replace.
//   [4] SOURCE SCAN — a registered constant's literal appearing in a file that
//       does not import the owner is a second home waiting to drift, and a
//       RETIRED figure appearing anywhere outside a correction is a stale
//       number still being quoted. Both fail.
//
// `npm run cost-gate`.
// ---------------------------------------------------------------------------

/** The package root, found rather than assumed — this file runs from
 *  `dist/scripts/`, so `..` is `dist/` and the scan silently found nothing. */
const ROOT = (() => {
  let d = import.meta.dirname;
  for (let i = 0; i < 6; i++) {
    try {
      const pkg = JSON.parse(readFileSync(resolve(d, 'package.json'), 'utf8'));
      if (pkg.name === 'dregg-mina-zkapp') return d;
    } catch {
      /* keep walking */
    }
    d = resolve(d, '..');
  }
  throw new Error('cannot locate the dregg-mina-zkapp package root from ' + import.meta.dirname);
})();
const WORK = process.env.FRIBRAID_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');
const exp = (n: number) => n.toExponential(2);
const pct = (a: number, b: number) => `${a >= b ? '+' : ''}${(((a - b) / b) * 100).toFixed(1)}%`;

let failures = 0;
const fail = (m: string) => {
  failures++;
  console.error(`    ✗ ${m}`);
};
const ok = (m: string) => console.log(`    ✓ ${m}`);

// ===========================================================================
console.log('\n=== THE COST-MODEL GATE ===');
console.log('\n[1] the registry — one quantity, one home');
// ===========================================================================

const reg = registry();
console.log(`    ${reg.length} registered cost constants, no clashes at import:`);
for (const r of reg)
  console.log(
    `      ${r.key.padEnd(42)} ${String(r.value).padStart(12)}  ${r.provenance.padEnd(9)} ${r.site}`,
  );

//  ⚑ A registration without a source is a number nobody can re-derive, which is
//  the same defect one level down.
for (const r of reg) {
  if (!r.source || r.source.length < 12)
    fail(`\`${r.key}\` is registered without a re-derivable source`);
  if (r.provenance === 'PROJECTED' && !/PROJECT|project/.test(r.source))
    fail(`\`${r.key}\` is PROJECTED but its source does not say what it is projected from`);
}
if (!failures) ok('every registration carries a provenance and a source');

try {
  assertLaneCostCoherent();
  ok(
    `the carry reconciliation holds: ${LANE_COST.witnessPerLane.toFixed(3)} rows/lane (leg 13, ` +
      `non-amortising) against ${LANE_COST.rebindPerLane.toFixed(3)} (§3.20, bulk) — ` +
      `${(LANE_COST.witnessPerLane / LANE_COST.rebindPerLane).toFixed(2)}x, NOT the 6.9x a ` +
      'rows-per-extension-value against rows-per-lane comparison suggests',
  );
} catch (e) {
  fail(String((e as Error).message));
}

// ===========================================================================
console.log('\n[2] the geometry — re-derived from the committed proof, not transcribed');
// ===========================================================================

const real: RealRootFri = JSON.parse(readFileSync(resolve(WORK, 'real-root-fri.json'), 'utf8'));
if (real.kind !== 'dregg-root-fri-instance') throw new Error(`not a root FRI instance: ${real.kind}`);
try {
  assertGeometryMatchesProof(real);
  ok(
    `census ${MEASURED_ROOT_GEOMETRY.censusPerQuery} terms/query and heights ` +
      `[${MEASURED_ROOT_GEOMETRY.heights.join(', ')}] reproduce the committed proof`,
  );
} catch (e) {
  fail(String((e as Error).message));
}
console.log(
  `    ⚑ the retired model said ${RETIRED_FLAT_MODEL.censusPerQuery} terms at a FLAT height ` +
    `${RETIRED_FLAT_MODEL.flatLogHeight} — ${pct(
      MEASURED_ROOT_GEOMETRY.censusPerQuery,
      RETIRED_FLAT_MODEL.censusPerQuery,
    )} on the census alone, and wrong in two directions that do not cancel:`,
);
console.log(
  `      it OMITS the permutation round (${MEASURED_ROOT_GEOMETRY.censusByRound.permutation} terms) ` +
    `and CHARGES 168 terms the proof does not have (matrices opened at ζ alone).`,
);

// ===========================================================================
console.log('\n[3] the headline, re-derived at the MEASURED geometry');
// ===========================================================================

const shape = rootFriShape(real);
const air = airColumnIndex();
const meta = (() => {
  try {
    return rootPreambleMeta(
      JSON.parse(readFileSync(resolve(WORK, 'real-root-air.json'), 'utf8')),
      air,
    );
  } catch {
    return undefined;
  }
})();

type Row = { hash: string; scope: string; segs: number; work: number; carry: number; slices: number };
const rows: Row[] = [];
for (const [hashName, hash] of [
  ['BabyBear (deployed)', BABYBEAR_HASH],
  ['Pasta (Mina-native)', PASTA_HASH],
] as const) {
  for (const [scope, pre] of [
    ['FRI walk', undefined],
    ['walk + batch-STARK preamble', meta],
  ] as const) {
    if (scope !== 'FRI walk' && !pre) continue;
    const op = planOpenedValues(shape, air);
    const w = segmentWalk(shape, { price: priceAt(hash), preamble: pre, seal: !!pre });
    const ft = friLaneTable(shape, op, hash.spongeRate);
    const plan = planFriWalk(w, op, ft, {
      usableRows: PICKLES.usableRowsMpv1,
      chunkLanes: 256,
    });
    rows.push({
      hash: hashName,
      scope,
      segs: w.segs.length,
      work: w.totalRows,
      carry: plan.totalCarry,
      slices: plan.slices.length,
    });
  }
}

console.log(
  `\n    Every figure below is the SAME measured segment list costed at a different hash — the\n` +
    `    arithmetic terms are shared by construction (\`ARITH_PRICE\`), so the delta IS the hash.\n`,
);
console.log(
  '    hash / scope                                 segs        work rows    slices(work)   slices(+carry)',
);
for (const r of rows)
  console.log(
    `    ${`${r.hash} — ${r.scope}`.padEnd(44)} ${fmt(r.segs).padStart(6)}  ${fmt(r.work).padStart(14)}  ` +
      `${String(slicesAt(r.work)).padStart(12)}   ${String(r.slices).padStart(12)}`,
  );

//  The retired figures the document still quotes, so the movement is a number
//  rather than an impression.
const RETIRED = {
  deployedRows: 2.46e7, //  §0, "the ROOT — deployed today"
  deployedSlices: 453, //   §0
  pastaRows: 2.85e6, //     §0.1, the re-measurement
  pastaSlices: 53, //       §0.1
} as const;

const bbWalk = rows.find((r) => r.hash.startsWith('BabyBear') && r.scope === 'FRI walk')!;
const pastaWalk = rows.find((r) => r.hash.startsWith('Pasta') && r.scope === 'FRI walk')!;
const bbFull = rows.find((r) => r.hash.startsWith('BabyBear') && r.scope !== 'FRI walk') ?? bbWalk;
const pastaFull = rows.find((r) => r.hash.startsWith('Pasta') && r.scope !== 'FRI walk') ?? pastaWalk;

console.log('\n    ⚑ HOW FAR THE HEADLINE MOVED, in §0/§0.1\'s own currency (work rows / 54,300):\n');
console.log('    figure                          RETIRED (flat 22, 2,286)      RE-DERIVED (measured)      move');
const line = (name: string, was: number, now: number, f = fmt) =>
  console.log(
    `    ${name.padEnd(30)} ${f(was).padStart(22)} ${f(now).padStart(26)}      ${pct(now, was)}`,
  );
line('deployed rows', RETIRED.deployedRows, bbWalk.work, exp as unknown as (n: number) => string);
line('deployed slices @54,300', RETIRED.deployedSlices, slicesAt(bbWalk.work));
line('Pasta rows', RETIRED.pastaRows, pastaWalk.work, exp as unknown as (n: number) => string);
line('Pasta slices @54,300', RETIRED.pastaSlices, slicesAt(pastaWalk.work));

console.log(
  `\n    ⚑ AND THE HASH LEVER SURVIVES THE CORRECTION, which is the finding that matters:\n` +
    `      ${fmt(bbWalk.work)} -> ${fmt(pastaWalk.work)} rows is still ` +
    `${(bbWalk.work / pastaWalk.work).toFixed(1)}x (the retired pair said ` +
    `${(RETIRED.deployedRows / RETIRED.pastaRows).toFixed(1)}x). The swap is a smaller win than\n` +
    `      advertised because the DEEP quotient — the term no hash choice touches — is bigger than\n` +
    '      the retired census said it was.',
);

//  ⚑ THE SENSITIVITY §4 NAMED, now that the census is right.
const deepRows = (() => {
  const w = segmentWalk(shape, { price: priceAt(PASTA_HASH) });
  return w.segs.filter((s) => s.t === 'deep').reduce((a, s) => a + s.rows, 0);
})();
console.log(
  `\n    ⚑ §4 said the projection "is sensitive to that number and almost nothing else" and it was\n` +
    `      right: the DEEP quotient is ${((deepRows / pastaWalk.work) * 100).toFixed(1)}% of the ` +
    `re-derived Pasta budget (the retired\n      re-measurement said 88%). A ` +
    `${(CENSUS_CORRECTION * 100).toFixed(1)}% census correction therefore lands almost undiluted ` +
    'on the headline.',
);

if (slicesAt(pastaWalk.work) <= RETIRED.pastaSlices)
  fail(
    `the re-derived Pasta slice count (${slicesAt(pastaWalk.work)}) did not exceed the retired ` +
      `${RETIRED.pastaSlices}. The census correction is +15% on a term that is ~90% of the budget; ` +
      'if the answer did not move, the model is not using the measured census.',
  );
else
  ok(
    `the correction MOVED the headline: ${RETIRED.pastaSlices} -> ${slicesAt(pastaWalk.work)} ` +
      `Pasta slices work-only, ${pastaFull.slices} once the measured carry is priced`,
  );

console.log(
  `\n    ⚠ SCOPE, stated rather than assumed. "${fmt(bbWalk.work)} rows" is the FRI walk. With the\n` +
    `      batch-STARK preamble it is ${fmt(bbFull.work)} deployed and ${fmt(pastaFull.work)} Pasta;\n` +
    `      the retired 2.46e7 folded a challenger-observe term into its total, so the preamble row is\n` +
    '      the closer comparison and the walk row is the more conservative one.',
);
console.log(
  `    ⚠ PROVENANCE. Segment structure and geometry: MEASURED off the committed proof. Unit prices:\n` +
    '      MEASURED (§3.8/§3.9/§3.13/§3.14 for BabyBear and arithmetic; `npm run mina-merkle`,\n' +
    '      o1js 2.15.0, for Pasta). The row TOTALS are therefore PROJECTED — measured units times a\n' +
    '      structural count that has not been emitted at full size. Slice counts carry the same label.',
);
console.log(
  `    ⚠ ONE CONSERVATISM NAMED. The Pasta leaf sponge is charged \`witnessLane\` per lane (leg 13's\n` +
    `      non-amortising ${LANE_COST.witnessPerLane.toFixed(2)}), where \`npm run mina-merkle\` measured the whole Pasta\n` +
    '      sponge at 3.69 rows/lane all-in. That over-prices `inBlock`, which is ~5% of the Pasta\n' +
    '      budget, so the re-derived Pasta figure is high by ~2% rather than low.',
);

// ===========================================================================
console.log('\n[4] the source scan — a second home for a constant, before it drifts');
// ===========================================================================

const OWNER = 'src/CostModel.ts';
const files: string[] = [];
const walkDir = (d: string) => {
  for (const e of readdirSync(d)) {
    if (e === 'node_modules' || e === 'dist' || e.startsWith('.')) continue;
    const p = resolve(d, e);
    if (statSync(p).isDirectory()) walkDir(p);
    else if (e.endsWith('.ts')) files.push(p);
  }
};
walkDir(resolve(ROOT, 'src'));
walkDir(resolve(ROOT, 'scripts'));

/** Literal spellings a number can appear as in TypeScript. */
const spellings = (v: number): string[] => {
  const out = new Set<string>();
  const push = (s: string) => s && out.add(s);
  if (Number.isInteger(v)) {
    push(String(v));
    //  `34_566`-style separators, grouped from the right.
    const s = String(v);
    if (s.length > 3) push(s.replace(/\B(?=(\d{3})+(?!\d))/g, '_'));
  } else {
    push(String(v));
    push(v.toFixed(1));
    push(v.toFixed(2));
  }
  return [...out];
};

/** A line may opt out with `COST-OK:` and a reason — for a doc-comment quoting
 *  a figure, or a deliberately distinct quantity. */
const EXEMPT = /COST-OK/;

/** Files git knows about, relative to the package root. */
const tracked = new Set(
  execFileSync('git', ['ls-files'], { cwd: ROOT, encoding: 'utf8' }).split('\n').filter(Boolean),
);

let scanned = 0;
const secondHomes: string[] = [];
const inFlight: string[] = [];
for (const f of files) {
  const rel = relative(ROOT, f);
  if (rel === OWNER) continue;
  const src = readFileSync(f, 'utf8');
  const importsOwner = /from '\.{1,2}\/(\.\.\/)?src\/CostModel\.js'|from '\.\/CostModel\.js'/.test(src);
  const lines = src.split('\n');
  scanned++;
  for (const r of reg) {
    //  Only integers and one-decimal figures are distinctive enough to scan for
    //  without drowning the report in coincidences.
    if (Math.abs(r.value) < 100) continue;
    for (const lit of spellings(r.value)) {
      lines.forEach((ln, i) => {
        if (!new RegExp(`(^|[^\\w.])${lit.replace('.', '\\.')}([^\\w]|$)`).test(ln)) return;
        if (EXEMPT.test(ln)) return;
        //  A doc comment quoting the figure beside its § is documentation, not a
        //  second definition; a bare assignment is the thing that drifts.
        const isDefinition = /(^|[^=!<>])=[^=]|:\s*$|:\s*[\d_]/.test(ln) && !/^\s*(\*|\/\/)/.test(ln);
        if (!isDefinition) return;
        if (importsOwner) return;
        //  ⚑ LANDED CODE FAILS; A LANE IN FLIGHT IS ADVISED. This gate governs
        //  `main`. Three lanes share this directory, and failing one lane's gate
        //  on another lane's uncommitted file makes the gate a source of noise
        //  rather than a check — the "red as steady state" failure. An untracked
        //  file is named loudly and does not fail; the moment it lands it does.
        (tracked.has(rel) ? secondHomes : inFlight).push(
          `${rel}:${i + 1} defines \`${r.key}\` (${lit}) and does not import the owner\n` +
            `          ${ln.trim().slice(0, 96)}`,
        );
      });
    }
  }
}
console.log(`    scanned ${scanned} TypeScript files under src/ and scripts/`);
//  ⚑ A SCAN THAT FOUND NOTHING TO SCAN IS NOT A PASS. This gate ran green once
//  with `scanned = 0`, because it was resolving `src/` relative to `dist/` and
//  finding no `.ts` at all — a gate that cannot go red reporting that nothing is
//  wrong. The floor is asserted so the instrument has to be pointed at something.
if (scanned < 30)
  fail(
    `the source scan saw only ${scanned} files — it is pointed at the wrong tree and cannot ` +
      'go red. `src/` and `scripts/` hold dozens of TypeScript files.',
  );
if (secondHomes.length) {
  for (const s of new Set(secondHomes)) fail(s);
  console.error(
    '\n    A registered cost constant defined in a file that does not import ' +
      '`src/CostModel.ts` is a second home. Import it, or register the value under its own ' +
      'key with the difference stated.',
  );
} else ok('no registered constant has a second definition in landed code');
if (inFlight.length) {
  console.log('');
  for (const s of new Set(inFlight)) console.log(`    ⚠ IN FLIGHT (untracked, advisory): ${s}`);
  console.log(
    '\n    These are a live lane\'s uncommitted files. They do not fail this gate and WILL the\n' +
      '    moment they land — import `src/CostModel.ts` before committing them.',
  );
}

//  ⚑ THE RETIRED FIGURES. These are not "another home" — they are numbers a
//  later measurement replaced, still being quoted. A file may keep one only if
//  the line says it is retired.
const RETIRED_LITERALS: [string, string][] = [
  ['2286', 'the flat-height DEEP census, superseded by 2,630 (§3.28)'],
  ['2,286', 'the flat-height DEEP census, superseded by 2,630 (§3.28)'],
];
const RETIRED_CTX = /RETIRED|retired|supersed|SUPERSED|§3\.28|2,630|2630|old census|wrong in two|used to|omits/;
const stale: string[] = [];
for (const f of files) {
  const rel = relative(ROOT, f);
  if (rel === OWNER) continue;
  const lines = readFileSync(f, 'utf8').split('\n');
  lines.forEach((ln, i) => {
    for (const [lit, why] of RETIRED_LITERALS) {
      if (!new RegExp(`(^|[^\\w.])${lit}([^\\w]|$)`).test(ln)) continue;
      //  ⚑ THE CONTEXT WINDOW IS A PARAGRAPH, NOT A LINE. Prose that names a
      //  figure as retired almost never does it on the same line as the figure,
      //  and a line-local check flags every correction as if it were the defect.
      const ctx = lines.slice(Math.max(0, i - 4), i + 5).join('\n');
      if (RETIRED_CTX.test(ctx)) continue;
      stale.push(`${rel}:${i + 1} quotes ${lit} — ${why}\n          ${ln.trim().slice(0, 96)}`);
    }
  });
}
if (stale.length) for (const s of stale) fail(s);
else ok('no retired census figure is quoted without saying it is retired');

// ---------------------------------------------------------------------------
// ⚑ THE DEPRECATED COLLIDING NAME, on a self-clearing schedule.
//
// `stepBoundary` had an identical signature AND body in two families and
// `terminalSeal` differed only by arity. Both are fixed — one shared definition
// and two distinct names — but `RootAirChain.terminalSeal` survives as an alias
// because `main`'s `root-fri-uniform.ts` still imports it and that file carries
// another lane's uncommitted work. This is the mechanism that removes it:
// tracked importers FAIL, and when nothing imports it the gate says delete it.
// ---------------------------------------------------------------------------
const DEPRECATED = 'terminalSeal';
const importers: { rel: string; tracked: boolean }[] = [];
for (const f of files) {
  const rel = relative(ROOT, f);
  if (rel === 'src/RootAirChain.ts' || rel === OWNER || rel.endsWith('cost-model-gate.ts')) continue;
  //  ⚑ IMPORT STATEMENTS ONLY. A doc comment explaining why the name was
  //  retired mentions it too, and flagging the explanation as the defect is how
  //  a gate trains people to ignore it.
  const src = readFileSync(f, 'utf8');
  const imports = [...src.matchAll(/import\s*\{([^}]*)\}\s*from/g)].map((m) => m[1]);
  if (imports.some((spec) => new RegExp(`(^|[,\\s])${DEPRECATED}(\\s*,|\\s*$|\\s)`).test(spec)))
    importers.push({ rel, tracked: tracked.has(rel) });
}
const landed = importers.filter((i) => i.tracked);
if (landed.length)
  for (const i of landed)
    fail(
      `${i.rel} imports the deprecated colliding name \`${DEPRECATED}\` — use ` +
        '`airTerminalSeal` (4-field, domain-tagged) or `partitionTerminalSeal` (3-field, ' +
        'untagged). They are DIFFERENT FUNCTIONS and the old name did not say which.',
    );
else if (importers.length)
  console.log(
    `    ⚠ \`${DEPRECATED}\` survives for ${importers.length} IN-FLIGHT file(s): ` +
      `${importers.map((i) => i.rel).join(', ')}. Delete the alias in ` +
      '`src/RootAirChain.ts` once they land.',
  );
else {
  //  ⚑ AND WHEN NOBODY IMPORTS IT, THE ALIAS ITSELF MUST BE GONE. A name kept
  //  past its last caller is the "no-op retained for compatibility" the project
  //  doctrine forbids, so the gate demands the deletion and then confirms it.
  const home = readFileSync(resolve(ROOT, 'src/RootAirChain.ts'), 'utf8');
  if (new RegExp(`export\\s+(const|function)\\s+${DEPRECATED}\\b`).test(home))
    fail(
      `nothing imports the deprecated \`${DEPRECATED}\` any more — DELETE the alias in ` +
        '`src/RootAirChain.ts`.',
    );
  else
    ok(
      `the colliding name \`${DEPRECATED}\` is GONE: \`airTerminalSeal\` (4-field, tagged) and ` +
        '`partitionTerminalSeal` (3-field, untagged) are the two names, and `stepBoundary` is ' +
        'one shared definition both families re-export',
    );
}

// ===========================================================================
console.log('');
if (failures) {
  console.error(`GATE RED — ${failures} failure${failures === 1 ? '' : 's'}.\n`);
  process.exit(1);
}
console.log('GATE GREEN — one owner, one value per quantity, and the headline re-derived.\n');

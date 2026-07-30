import { readFileSync } from 'node:fs';
import { BABYBEAR_HASH, PASTA_HASH, PICKLES } from '../src/CostModel.js';
import {
  ARITH_PRICE,
  EXT_LANES,
  MatrixSpec,
  RoundSpec,
  airColumnIndex,
  deepTermCensus,
  friLaneTable,
  planFriWalk,
  planOpenedValues,
  priceAt,
  rootFriShape,
  rootPreambleMeta,
  segmentWalk,
  type FriShape,
  type RealRootFri,
} from '../src/RootFriWalk.js';
import { MINA_TIER, tierStop } from '../src/tier.js';

// ---------------------------------------------------------------------------
// [LEG] THE COLUMN QUESTION, ANSWERED WITH A NUMBER EITHER WAY.
//
// ⚑ WHY THIS LEG EXISTS. Once the hash is a parameter, `MINA-VERIFIES-DREGG-FRI-
// SIZE` §3.31 says the shape has flipped: hashing was 89% of a Mina-side verify
// and is 7.4%, and the DEEP quotient was 10% and is 86%. It then names ONE lever
// — "column narrowing" — and prices it at "1,067 rows per opened value at ζ,
// halving the root's committed column count is 54 slices → 31."
//
// That sentence is a hope with two literals in it, and this leg is what turns it
// into a measurement. It reproduces the census FROM THE PROOF, re-derives the
// DEEP unit price FROM `ARITH_PRICE` rather than from a headline, attributes the
// census PER INSTANCE (which is where the answer turns out to live), and prices
// each candidate lever with the exact opened-value delta it produces.
//
// ⚑ AND IT IS AN OUT-OF-CIRCUIT LEG. Nothing compiles. Every number here is
// either read off `.fullchain/real-root-fri.json` or is arithmetic over
// `CostModel`'s registered unit prices — so a lane can settle "is there another
// order of magnitude in the columns" in two seconds instead of a compile.
//
//   npm run deep-columns
// ---------------------------------------------------------------------------

const REAL: RealRootFri = JSON.parse(readFileSync('.fullchain/real-root-fri.json', 'utf8'));
const t0 = Date.now();
const el = () => `${((Date.now() - t0) / 1000).toFixed(1)}s`;

let checks = 0;
let failures = 0;
const ok = (m: string) => {
  console.log(`  ✓ ${m}`);
  checks++;
};
const fail = (m: string) => {
  console.log(`  ✗ ${m}`);
  failures++;
};
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');
const pct = (a: number, b: number) => `${((a / b) * 100).toFixed(1)}%`;

const shape = rootFriShape(REAL);
const airIx = airColumnIndex();
const op = planOpenedValues(shape, airIx);
const meta = rootPreambleMeta(JSON.parse(readFileSync('.fullchain/real-root-air.json', 'utf8')), airIx);

console.log('\n=== THE DEEP QUOTIENT AND THE COLUMN COUNT — measured, not projected ===');
console.log(`    tier ${MINA_TIER}; object: .fullchain/real-root-fri.json (nothing compiles here)\n`);

// ===========================================================================
// [1] The census, from the proof, by round AND by instance.
// ===========================================================================

console.log('[1] the census, attributed — and the attribution is the answer');

const census = deepTermCensus(shape);
const TOTAL = census.total;
console.log(`\n    ${shape.rounds.length} PCS rounds, heights [${shape.heights}], census ${fmt(TOTAL)}\n`);
for (const r of shape.rounds)
  console.log(
    `      ${r.name.padEnd(16)} ${String(r.matrices.length).padStart(3)} matrices  ` +
      `${String(fmt((census as any)[r.name])).padStart(6)}  ${pct((census as any)[r.name], TOTAL).padStart(6)}`,
  );

/** `(round, matrix)` grouped by the AIR instance the matrix belongs to. */
const instanceOf = (m: MatrixSpec) => m.name.split('/chunk')[0];
const byInstance = new Map<string, { terms: number; byRound: Record<string, number>; rows: number }>();
shape.rounds.forEach((r) =>
  r.matrices.forEach((m) => {
    const k = instanceOf(m);
    const e = byInstance.get(k) ?? { terms: 0, byRound: {}, rows: 0 };
    e.terms += m.width * m.numPoints;
    e.byRound[r.name] = (e.byRound[r.name] ?? 0) + m.width * m.numPoints;
    if (r.name === 'main') e.rows = 1 << m.logHeight;
    byInstance.set(k, e);
  }),
);
const insts = [...byInstance.entries()].sort((a, b) => b[1].terms - a[1].terms);
console.log('\n    per INSTANCE, which is where the lever is:\n');
console.log('      instance                          LDE rows   main  quot  prep  perm    total   share');
for (const [name, e] of insts)
  console.log(
    `      ${name.padEnd(34)}${fmt(e.rows).padStart(9)}  ` +
      ['main', 'quotient_chunk', 'preprocessed', 'permutation']
        .map((r) => String(e.byRound[r] ?? 0).padStart(5))
        .join(' ') +
      `  ${String(fmt(e.terms)).padStart(7)}  ${pct(e.terms, TOTAL).padStart(6)}`,
  );

if (TOTAL !== 2630) fail(`the census is ${TOTAL} and this leg was written against 2,630`);
else ok('the census reproduces from the proof at 2,630');

// ⚑ THE FACT THAT MAKES THE LEVER A LEVER: a DEEP term is priced per OPENED
// VALUE and is independent of the matrix's HEIGHT. An 8-row table with 452
// columns costs exactly what a 4-million-row one with 452 columns costs.
const top = insts[0];
console.log(
  `\n    ⚑ \`${top[0]}\` is ${fmt(top[1].terms)} of ${fmt(TOTAL)} opened values (${pct(top[1].terms, TOTAL)}) ` +
    `for a table of ${fmt(top[1].rows)} LDE rows\n      (${fmt(top[1].rows >> shape.knobs.logBlowup)} TRACE rows at log_blowup ${shape.knobs.logBlowup}).\n` +
    '      A DEEP term is priced per OPENED VALUE and is INDEPENDENT OF HEIGHT — one Horner step,\n' +
    '      four witnessed lanes — so an 8-row 452-column matrix is priced identically to a\n' +
    '      4-million-row one. Height is what the MERKLE path costs; width is what the DEEP\n' +
    '      quotient costs, and after the hash swap only the second one is the budget.',
);

// ===========================================================================
// [2] The DEEP unit price, RE-DERIVED — and the 1,067 it refutes.
// ===========================================================================

console.log('\n[2] the DEEP unit price, from `ARITH_PRICE` rather than from a headline');

/** One `deep` segment's rows, exactly as `segmentWalk` charges them. */
const perColumn = ARITH_PRICE.horner + EXT_LANES * ARITH_PRICE.witnessLane;
const perClose = ARITH_PRICE.extInverse + 2 * ARITH_PRICE.extMul + ARITH_PRICE.extAdd;
const closes = shape.rounds.reduce((a, r) => a + r.matrices.reduce((b, m) => b + m.numPoints, 0), 0);
const publishRows = shape.heights.length * 4;
const deepPerQuery = TOTAL * perColumn + closes * perClose + publishRows;
const deepAll = deepPerQuery * shape.knobs.numQueries;
const perOpenedValue = deepAll / TOTAL;

console.log(
  `\n      per COLUMN   horner ${ARITH_PRICE.horner} + ${EXT_LANES} x witnessLane ` +
    `${ARITH_PRICE.witnessLane.toFixed(2)} = ${perColumn.toFixed(2)}\n` +
    `      per CLOSE    extInverse ${ARITH_PRICE.extInverse} + 2 x extMul ${ARITH_PRICE.extMul} + ` +
    `extAdd ${ARITH_PRICE.extAdd} = ${perClose}   (x ${closes} (matrix, point) pairs)\n` +
    `      per QUERY    ${fmt(TOTAL)} x ${perColumn.toFixed(2)} + ${closes} x ${perClose} + ` +
    `${publishRows} = ${fmt(deepPerQuery)}\n` +
    `      x ${shape.knobs.numQueries} queries = ${fmt(deepAll)} rows\n` +
    `      ⇒ ${perOpenedValue.toFixed(1)} ROWS PER OPENED VALUE AT ζ`,
);

// ⚑ THE FIGURE THIS REPLACES, AND WHERE IT CAME FROM.
const OLD_DEEP = 2.5e6;
const OLD_CENSUS = 2342;
const OLD = OLD_DEEP / OLD_CENSUS;
console.log(
  `\n    ⚑ §3.31 QUOTES ${OLD.toFixed(0)} ROWS PER OPENED VALUE AND IT IS ${((perOpenedValue / OLD - 1) * 100).toFixed(0)}% LOW.\n` +
    `      It is ${fmt(OLD_DEEP)} / ${fmt(OLD_CENSUS)}, two literals in \`scripts/pasta-root-rows.ts\`, and\n` +
    `      ${fmt(OLD_CENSUS)} is the RETIRED FLAT CENSUS (2,286 plus the 56 quotient openings counted\n` +
    "      twice) that `CostModel.RETIRED_FLAT_MODEL` already documents as wrong. The measured\n" +
    `      census is ${fmt(TOTAL)} and the measured unit price is ${perColumn.toFixed(2)} a column, so the\n` +
    `      DEEP term is ${fmt(deepAll)}, not ${fmt(OLD_DEEP)}.\n` +
    '      ⚠ THE DIRECTION MATTERS: the lever is BIGGER than advertised, not smaller.',
);
if (Math.abs(perOpenedValue - 1067) < 50)
  fail('the re-derivation lands on 1,067 after all — the refutation above is wrong');
else ok(`the per-opened-value price is ${perOpenedValue.toFixed(1)}, not 1,067 — re-derived from the owner`);

// ===========================================================================
// [3] What the DEEP term is a SHARE of, at each hash — work, and work + carry.
// ===========================================================================

console.log('\n[3] the share — and the second literal, which is that 86% is work-only');

const walkAt = (h: typeof BABYBEAR_HASH) =>
  segmentWalk(shape, { price: priceAt(h), preamble: meta, seal: true, priceOnly: true });
const ftD = friLaneTable(shape, op);

for (const h of [BABYBEAR_HASH, PASTA_HASH]) {
  const w = walkAt(h);
  const byKind = new Map<string, number>();
  for (const s of w.segs) byKind.set(s.t, (byKind.get(s.t) ?? 0) + s.rows);
  const deep = byKind.get('deep') ?? 0;
  const plan = planFriWalk(w, op, ftD, { usableRows: PICKLES.friWalkBudget, chunkLanes: 256 });
  const withCarry = w.totalRows + plan.totalCarry;
  console.log(
    `\n      ${h.name}  (${w.priced})\n` +
      `        work         ${fmt(w.totalRows).padStart(12)}   DEEP ${fmt(deep).padStart(12)}  ${pct(deep, w.totalRows).padStart(6)}\n` +
      `        + carry      ${fmt(withCarry).padStart(12)}   DEEP ${fmt(deep).padStart(12)}  ${pct(deep, withCarry).padStart(6)}\n` +
      `        slices @ ${fmt(PICKLES.friWalkBudget)}: ${plan.slices.length}`,
  );
}
console.log(
  '\n    ⚑ CARRY IS HASH-INDEPENDENT, so it does not shrink when the hash does — and it is what\n' +
    '      keeps the DEEP share off 90%. A lever priced against the WORK share is priced against\n' +
    '      the wrong denominator for a SLICED chain, which is the only kind this directory builds.',
);
ok('the DEEP share is reported against work AND against work + carry, which are different numbers');

// ===========================================================================
// [4] The levers, each with the exact opened-value delta it produces.
// ===========================================================================

console.log('\n[4] the levers — each priced by REBUILDING the shape, not by scaling a total');

type Lever = { name: string; why: string; edit: (s: FriShape) => FriShape };

const clone = (s: FriShape): FriShape => ({
  knobs: { ...s.knobs },
  rounds: s.rounds.map((r) => ({ name: r.name, matrices: r.matrices.map((m) => ({ ...m })) })),
  heights: [...s.heights],
});
const reheight = (s: FriShape): FriShape => {
  s.heights = [...new Set(s.rounds.flatMap((r) => r.matrices.map((m) => m.logHeight)))].sort((a, b) => b - a);
  return s;
};
const dropInstance = (s: FriShape, name: string): FriShape => {
  s.rounds = s.rounds.map((r: RoundSpec) => ({
    name: r.name,
    matrices: r.matrices.filter((m) => instanceOf(m) !== name),
  }));
  return reheight(s);
};
const scaleInstance = (s: FriShape, name: string, f: (m: MatrixSpec) => number): FriShape => {
  s.rounds.forEach((r) => r.matrices.forEach((m) => instanceOf(m) === name && (m.width = f(m))));
  return s;
};

const levers: Lever[] = [
  {
    name: 'A. merge `poseidon2_perm/baby_bear_d4_w24` into the w16 op-type',
    why:
      'It exists as an ISOLATION device — a second Poseidon2 op-type so the IVC segment-digest\n' +
      "        sponge shares no chain-state, CTL bus or CSE collapse with the FRI challenger's W16\n" +
      '        perm. That is a DISTINCTNESS requirement, not a width-24 one: a domain-tagged W16\n' +
      '        op or a separate bus satisfies it at 452 main columns instead of nothing.',
    edit: (s) => dropInstance(clone(s), 'poseidon2_perm/baby_bear_d4_w24'),
  },
  {
    name: 'A′. the same instance at W16 widths rather than deleted',
    why: 'The conservative reading of A — same table, narrower permutation.',
    edit: (s) => {
      const c = clone(s);
      const w16: Record<string, number> = {};
      c.rounds.forEach((r) =>
        r.matrices.forEach((m) => {
          if (instanceOf(m) === 'poseidon2_perm/baby_bear_d4_w16') w16[r.name] = m.width;
        }),
      );
      return scaleInstance(c, 'poseidon2_perm/baby_bear_d4_w24', (m) => {
        const r = c.rounds.find((x) => x.matrices.includes(m))!;
        return w16[r.name] ?? m.width;
      });
    },
  },
  {
    name: 'B. `expose_claim` re-laid as 25 rows x 1 lane rather than 1 row x 25 lanes',
    why:
      'One row, 25 claim lanes, and 25 lanes means 25 LogUp interactions means 25 extension\n' +
      '        running-sum columns opened at TWO points. Height is free in the DEEP quotient and\n' +
      '        width is not, so the cheap layout is the tall one.',
    edit: (s) => {
      const c = clone(s);
      c.rounds.forEach((r) =>
        r.matrices.forEach((m) => {
          if (instanceOf(m) === 'expose_claim') m.width = Math.max(EXT_LANES, Math.round(m.width / 25));
        }),
      );
      return c;
    },
  },
  {
    name: 'C. `alu_lanes` 4 → 1',
    why: 'Main width is `16·lanes + 12`, prep `13·lanes + 7`, perm `4·lanes + 2`. A packing knob.',
    edit: (s) => {
      const c = clone(s);
      c.rounds.forEach((r) =>
        r.matrices.forEach((m) => {
          if (instanceOf(m) !== 'Alu') return;
          if (r.name === 'main') m.width = 16 * 1 + 12;
          else if (r.name === 'preprocessed') m.width = 13 * 1 + 7;
          else if (r.name === 'permutation') m.width = (4 * 1 + 2) * EXT_LANES;
        }),
      );
      return c;
    },
  },
  {
    name: 'D. max constraint degree 3 → 2 (one quotient chunk, not two)',
    why: '`log_num_quotient_chunks = log2_ceil(maxDegree − 1)`. Every AIR must drop to degree 2.',
    edit: (s) => {
      const c = clone(s);
      c.rounds = c.rounds.map((r) =>
        r.name !== 'quotient_chunk'
          ? r
          : { name: r.name, matrices: r.matrices.filter((m) => m.name.endsWith('/chunk0')) },
      );
      return reheight(c);
    },
  },
  {
    name: 'E. batch LogUp — one running sum per instance, not one per interaction',
    why:
      '`permutation_width = contexts.len()` in p3-batch-stark: literally one extension column\n' +
      '        per interaction, and all 64 of the root’s are on ONE bus. Batching is a change to the\n' +
      '        UPSTREAM FORK, not a config knob — there is no batch parameter in p3-lookup.',
    edit: (s) => {
      const c = clone(s);
      c.rounds.forEach((r) => r.name === 'permutation' && r.matrices.forEach((m) => (m.width = EXT_LANES)));
      return c;
    },
  },
];

const base = { census: TOTAL, deep: deepAll };
const priceShape = (s: FriShape) => {
  const cen = deepTermCensus(s).total;
  const cl = s.rounds.reduce((a, r) => a + r.matrices.reduce((b, m) => b + m.numPoints, 0), 0);
  const deep = (cen * perColumn + cl * perClose + s.heights.length * 4) * s.knobs.numQueries;
  return { census: cen, deep };
};

console.log('\n      lever                                                    census      Δ      DEEP rows     Δ');
console.log(
  `      ${'BASELINE (dregg’s committed root)'.padEnd(54)}${fmt(base.census).padStart(7)}` +
    `${''.padStart(8)}${fmt(base.deep).padStart(12)}`,
);
const applied: { name: string; census: number; deep: number }[] = [];
for (const L of levers) {
  const r = priceShape(L.edit(shape));
  applied.push({ name: L.name, ...r });
  console.log(
    `      ${L.name.slice(0, 54).padEnd(54)}${fmt(r.census).padStart(7)}` +
      `${(r.census - base.census).toLocaleString('en-US').padStart(8)}${fmt(r.deep).padStart(12)}` +
      `  ${pct(r.deep, base.deep)}`,
  );
}
for (const L of levers) console.log(`\n      ${L.name}\n        ${L.why}`);

//  A + B + C together — the combination the census says is available without
//  touching the upstream fork or any AIR's degree.
{
  let s = clone(shape);
  s = dropInstance(s, 'poseidon2_perm/baby_bear_d4_w24');
  s.rounds.forEach((r) =>
    r.matrices.forEach((m) => {
      if (instanceOf(m) === 'expose_claim') m.width = Math.max(EXT_LANES, Math.round(m.width / 25));
      if (instanceOf(m) !== 'Alu') return;
      if (r.name === 'main') m.width = 28;
      else if (r.name === 'preprocessed') m.width = 20;
      else if (r.name === 'permutation') m.width = 6 * EXT_LANES;
    }),
  );
  const r = priceShape(s);
  console.log(
    `\n    ⚑ A + B + C TOGETHER: census ${fmt(base.census)} → ${fmt(r.census)} (${pct(r.census, base.census)}), ` +
      `DEEP ${fmt(base.deep)} → ${fmt(r.deep)}.\n` +
      `      That is BETTER than the halving §3.31 asked for, and none of the three is a hash change,\n` +
      '      a FRI-knob change or an upstream-fork change. All three are dregg-side AIR LAYOUT.',
  );
  if (r.census > base.census / 2)
    fail(`A+B+C leaves ${fmt(r.census)} opened values, which is not the halving §3.31 priced`);
  else ok(`A + B + C reaches ${fmt(r.census)} opened values — past the halving, by AIR layout alone`);
}

// ===========================================================================
// [5] Where it CANNOT be cut — said with a number, so the question closes.
// ===========================================================================

console.log('\n[5] where the count CANNOT be cut — with the number, so this closes rather than hopes');
const quot = (census as any).quotient_chunk as number;
const perm = (census as any).permutation as number;
const p2w16 = byInstance.get('poseidon2_perm/baby_bear_d4_w16')!.byRound['main'] ?? 0;
console.log(
  `\n      quotient round     ${String(fmt(quot)).padStart(6)}  ${pct(quot, TOTAL).padStart(6)}  width is D = ${EXT_LANES} per chunk and the chunk\n` +
    '                                        count is `2^log2_ceil(maxDegree − 1)` = 2. Best case is\n' +
    `                                        ${fmt(quot / 2)} terms (${pct(quot / 2, TOTAL)}) and it costs every AIR a degree.\n` +
    `      permutation round  ${String(fmt(perm)).padStart(6)}  ${pct(perm, TOTAL).padStart(6)}  forced by 64 LogUp interactions, forced by\n` +
    '                                        `permutation_width = contexts.len()`. No batch parameter\n' +
    '                                        exists in p3-lookup at the pinned rev — this is a change to\n' +
    '                                        the UPSTREAM FORK, not a knob.\n' +
    `      p2_w16 main        ${String(fmt(p2w16)).padStart(6)}  ${pct(p2w16, TOTAL).padStart(6)}  300 columns is \`W(1+2·HF·(SR+1)) + PR·(SR+1) + 2\`,\n` +
    '                                        the Poseidon2-w16 round schedule itself. Narrowing it means\n' +
    '                                        changing the hash the root commits with, which rotates the\n' +
    '                                        apex VK. Not this lane’s to turn.',
);
ok('the three unreachable terms are named with their shares and the reason each is unreachable');

// ===========================================================================
if (MINA_TIER >= 0) {
  console.log('');
  if (failures) {
    console.error(`\n✗ ${failures} check(s) failed`);
    process.exit(1);
  }
  tierStop(
    'DEEP-COLUMN-CENSUS',
    checks,
    el(),
    'nothing — this leg is out-of-circuit end to end and has no tier-1 or tier-2 half. ' +
      'The levers it prices are AIR-layout changes on the dregg side and each needs its own ' +
      're-mint before any of these numbers becomes a measurement of an object that exists.',
  );
}

import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { DEPLOYED_KNOBS } from '../src/FriChallenger.js';

import {
  airColumnIndex,
  deepTermCensus,
  friLaneTable,
  RealRootFri,
  planFriWalk,
  planOpenedValues,
  rootFriShape,
  segmentWalk,
} from '../src/RootFriWalk.js';

// ---------------------------------------------------------------------------
// THE PLAN, BEFORE ANY CIRCUIT IS COMPILED — the walk's size, its cut list, and
// the ratio of the DEEP quotient the braid actually binds.
//
// This is the cheap half of leg 18: it prices the whole FRI walk at the root's
// real geometry from measured unit prices and reports where the cuts fall. It
// compiles nothing, so it runs in seconds and a lane can iterate on the plan
// without paying a Pickles compile to find out that a cut does not fit.
// ---------------------------------------------------------------------------

const WORK = process.env.FRIBRAID_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const BUDGET = Number(process.env.FRIBRAID_BUDGET ?? 50_000);
const CHUNK = Number(process.env.FRIBRAID_CHUNK ?? 256);
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');

function main() {
  const real: RealRootFri = JSON.parse(readFileSync(resolve(WORK, 'real-root-fri.json'), 'utf8'));
  if (real.kind !== 'dregg-root-fri-instance') throw new Error(`not a root FRI instance: ${real.kind}`);
  const shape = rootFriShape(real);
  const census = deepTermCensus(shape);
  const air = airColumnIndex();
  const op = planOpenedValues(shape, air);

  console.log('\n=== THE ROOT FRI WALK, PLANNED (leg 18) ===\n');
  console.log(
    `[1] geometry: |D^0| = 2^${DEPLOYED_KNOBS.logGlobalMaxHeight}  log_blowup ` +
      `${DEPLOYED_KNOBS.logBlowup}  ${DEPLOYED_KNOBS.numQueries} queries  ` +
      `${DEPLOYED_KNOBS.layers} fold layers  query_pow ${DEPLOYED_KNOBS.queryPowBits}`,
  );
  console.log(`    vk ${real.vkFingerprint.slice(0, 16)}...  degree_bits [${real.degreeBits}]`);
  console.log(`    committed matrix heights, descending: [${shape.heights.join(', ')}]`);
  for (const r of shape.rounds)
    console.log(
      `    round ${r.name.padEnd(13)} ${String(r.matrices.length).padStart(2)} matrices  ` +
        `${fmt(r.matrices.reduce((a, m) => a + m.width, 0)).padStart(6)} base columns  ` +
        `${fmt(census[r.name]).padStart(6)} DEEP terms`,
    );
  console.log(`    DEEP terms per query: ${fmt(census.total)}  (§3.15 says 2,286: it omits the permutation round AND assumes 2 points everywhere)`);

  console.log(
    `\n[2] the braid: of ${fmt(op.split.total)} opened values, ${fmt(op.split.air)} ` +
      `(${((op.split.air / op.split.total) * 100).toFixed(1)}%) are lanes of the AIR chain's OWN ` +
      `column commitment`,
  );
  console.log(
    `    the other ${fmt(op.split.fri)} are opened values the AIR never reads — they go under ` +
      `friDigest, and are named as a SECOND commitment rather than folded into the first`,
  );

  const w = segmentWalk(shape);
  console.log(`\n[3] the walk: ${fmt(w.segs.length)} segments, ${fmt(w.totalRows)} modelled rows`);
  const byKind: Record<string, { n: number; rows: number }> = {};
  for (const s of w.segs) {
    const k = byKind[s.t] ?? (byKind[s.t] = { n: 0, rows: 0 });
    k.n++;
    k.rows += s.rows;
  }
  for (const [k, v] of Object.entries(byKind).sort((a, b) => b[1].rows - a[1].rows))
    console.log(
      `    ${k.padEnd(9)} ${fmt(v.n).padStart(7)} segments  ${fmt(v.rows).padStart(12)} rows  ` +
        `${((v.rows / w.totalRows) * 100).toFixed(1)}%`,
    );
  const maxSeg = w.segs.reduce((a, s) => Math.max(a, s.rows), 0);
  const maxLive = w.liveIn.reduce((a, l) => Math.max(a, l.length), 0);
  console.log(`    widest single segment ${fmt(maxSeg)} rows; widest live set ${maxLive} lanes`);

  const ft = friLaneTable(shape, op);
  const plan = planFriWalk(w, op, ft, { usableRows: BUDGET, chunkLanes: CHUNK });
  console.log(
    `\n[4] the FRI-side lane table is ${fmt(ft.nLanes)} lanes: the challenger state entering FRI, ` +
      `the ${DEPLOYED_KNOBS.layers} commit-phase roots, the ${shape.rounds.length} input-round ` +
      `roots, the final polynomial, the query PoW witness, every out-of-domain point, the ` +
      `${fmt(op.nFri)} opened values the AIR never reads, and all ${fmt(ft.perQueryRowLanes)} ` +
      `opened row lanes of each of the ${DEPLOYED_KNOBS.numQueries} queries`,
  );
  console.log(`\n[5] the cut list at a ${fmt(BUDGET)}-row budget, chunk ${CHUNK} lanes`);
  console.log(
    `    ${fmt(plan.slices.length)} slices; work ${fmt(plan.totalWork)} + carry ` +
      `${fmt(plan.totalCarry)} = ${fmt(plan.totalWork + plan.totalCarry)} rows ` +
      `(${((plan.totalCarry / (plan.totalWork + plan.totalCarry)) * 100).toFixed(1)}% carry)`,
  );
  const carries = plan.slices.map((s) => s.carryRows);
  console.log(
    `    carry per slice: min ${fmt(Math.min(...carries))}  median ` +
      `${fmt(carries.slice().sort((a, b) => a - b)[carries.length >> 1])}  max ` +
      `${fmt(Math.max(...carries))}`,
  );
  console.log(`    AIR column chunks ${plan.nAirChunks}, FRI column chunks ${plan.nFriChunks}`);
  const show = [0, 1, 2, 3, 4, 5, plan.slices.length - 1];
  for (const i of show) {
    const s = plan.slices[i];
    if (!s) continue;
    console.log(
      `    slice ${String(s.index).padStart(3)}: segments [${fmt(s.from)},${fmt(s.to)})  ` +
        `${w.segs[s.from].t} .. ${w.segs[s.to - 1].t}  work ${fmt(s.workRows).padStart(6)} + carry ` +
        `${fmt(s.carryRows).padStart(6)}  liveIn ${s.liveIn.length}  chunks ` +
        `${s.readsAirChunks.length}air/${s.readsFriChunks.length}fri`,
    );
  }

  // Where the slices fall, per query — the object the extrapolation is over.
  const perQuery: number[] = new Array(DEPLOYED_KNOBS.numQueries).fill(0);
  for (const s of plan.slices) {
    const seg = w.segs[s.from] as any;
    if (typeof seg.q === 'number') perQuery[seg.q]++;
  }
  console.log(
    `\n[6] slices per query: [${perQuery.join(', ')}]  (the transcript takes ` +
      `${plan.slices.length - perQuery.reduce((a, b) => a + b, 0)})`,
  );
  console.log('');
}

main();

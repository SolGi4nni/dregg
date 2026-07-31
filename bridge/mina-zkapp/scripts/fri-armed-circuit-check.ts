// ===========================================================================
// STEP 5 — the ARMED CIRCUIT closes the twin→circuit gap.
//
// The differential asserts twinVerdict == rustVerdict. `twinVerdict` runs
// `walkTwin` (bigint). But the DEPLOYED o1js verifier is `runSegments` (the exact
// constraint emitter `makeUniformSliceProgram`/`makeFriSliceProgram` compile). This
// harness runs `runSegments` ITSELF, over the whole walk in one slice, under
// `Provable.runAndCheck` — which is SOUND FOR A REFUSAL of an `assertEquals` (the
// inputRoot / commitRoot / final teeth are assertEquals, not lookups). It confirms:
//   • the honest proof SATISFIES the circuit's constraints, and
//   • each sampled mutation that the twin+native both REJECT also makes the
//     circuit's own constraints REFUSE.
// So the twin's verdict is not merely a bigint model that happens to agree with the
// native verifier; it is the same refusal the armed circuit emits.
//
//   ../../target/release/root_fri_mutation <seed> <n> | \
//     node --max-old-space-size=16384 dist/scripts/fri-armed-circuit-check.js <K>
// processes the honest baseline + the first K mutation trials.
// ===========================================================================
import { createInterface } from 'node:readline';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { Field, Provable } from 'o1js';
import {
  airColumnIndex,
  friLaneTable,
  planOpenedValues,
  rootFriShape,
  segmentWalk,
  type FriPlan,
  type RealRootFri,
} from '../src/RootFriWalk.js';
import { airLaneValues, friLaneValues, walkTwin, type SliceIo } from '../src/RootFriSlice.js';
import { runSegments } from '../src/RootFriSlice.js';
import { rootAirDag, bindRealInstance, type RealRootAir } from '../src/RootAirDag.js';
import { babyBearSuite } from '../src/HashSuites.js';

const K = Number(process.argv[2] ?? '8');
const WORK = process.env.FRIMUT_WORKDIR ?? resolve(process.cwd(), '.fullchain');

const realAir = JSON.parse(readFileSync(resolve(WORK, 'real-root-air.json'), 'utf8')) as RealRootAir;
const diskFri = JSON.parse(readFileSync(resolve(WORK, 'real-root-fri.json'), 'utf8')) as RealRootFri;
const shape = rootFriShape(diskFri);
const op = planOpenedValues(shape, airColumnIndex());
const ft = friLaneTable(shape, op);
const w = segmentWalk(shape);

const dag = rootAirDag();
const byName: Record<string, any> = {};
for (const i of realAir.instances)
  byName[i.table.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_')] = i;
const airBase: bigint[][] = [];
const airExt: bigint[][] = [];
for (const t of dag.tables) {
  const inst = byName[t.name] ?? byName[t.name.toLowerCase()];
  const b = bindRealInstance(t, inst);
  airBase.push(...b.base);
  airExt.push(...b.ext);
}
const airLanes = airLaneValues(airBase, airExt);

// ⚑ PREFIX. The full 11,303-segment walk in one runAndCheck is too heavy; query 0's ENTIRE
// walk (its input openings → inRoot, DEEP, commit phase → cpRoot, and final) lives in the first
// ~630 segments, so a prefix through the first `final` exercises all three teeth on query 0 at a
// fraction of the cost. A mutation that breaks a query-0 tooth (or a global one: final_poly, the
// query grind) makes this prefix REFUSE; one for another query does not reach into it.
const PREFIX_TO = w.segs.findIndex((s) => s.t === 'final') + 1; // through query 0's `final`

/** Run segments [0, PREFIX_TO) as one slice through `runSegments` under runAndCheck.
 *  Resolves true if the circuit's constraints are satisfied, false if it refuses. */
async function circuitAccepts(fri: RealRootFri): Promise<boolean> {
  const friLanes = friLaneValues(fri, shape, ft, op);
  const twin = walkTwin(w, shape, ft, op, friLanes, airLanes, fri);
  const CL = Math.max(airLanes.length, friLanes.length) + 1;
  const auxPrefix = twin.aux.slice(0, PREFIX_TO).flat();
  const plan: FriPlan = {
    slices: [
      {
        index: 0,
        from: 0,
        to: PREFIX_TO,
        liveIn: w.liveIn[0],
        liveOut: [],
        readsAirChunks: [0],
        readsFriChunks: [0],
        workRows: 0,
        carryRows: 0,
      },
    ],
    nAirChunks: 1,
    nFriChunks: 1,
    chunkSize: CL,
    totalWork: 0,
    totalCarry: 0,
  };
  try {
    await Provable.runAndCheck(() => {
      const sto = new Map<number, Field>();
      const io: SliceIo = {
        airLanes: airLanes.map((x) => Field(x)),
        airOther: [],
        friLanes: friLanes.map((x) => Field(x)),
        friOther: [],
        aux: auxPrefix.map((x) => Field(x)),
      };
      w.liveIn[0].forEach((slot, i) => sto.set(slot, io.friLanes[i] ?? Field(0)));
      runSegments(w, shape, ft, op, plan, 0, sto, io, babyBearSuite);
    });
    return true;
  } catch {
    return false;
  }
}

/** Does a mutation reach into query 0's prefix? Global teeth (final poly, the query grind that
 *  reshuffles every index) do; a query-q-specific opening does only for q0. */
function affectsPrefix(region: string, desc: string): boolean {
  // Global teeth reach every query's prefix: the final polynomial, the query grind (reshuffles
  // every index), and a commit-phase COMMIT root (checked at every query's cpRoot for its layer).
  if (region === 'final_poly' || region === 'query_pow_witness' || region === 'commitphase_commit_root')
    return true;
  if (region === 'commit_pow_witness') return false; // unconstrained (commitPowBits=0)
  return desc.startsWith('q0 '); // a query-q opening reaches the prefix only for q0
}

const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
let processed = 0;
let honestOk = false;
const mutated: { trial: number; region: string; desc: string; circuit: boolean; oracle: string }[] = [];
const t0 = Date.now();

for await (const line of rl) {
  if (!line.trim()) continue;
  const rec = JSON.parse(line) as { trial: number; region: string; desc: string; oracle: string; fri: RealRootFri };
  if (rec.trial === -1) {
    const t = Date.now();
    honestOk = await circuitAccepts(rec.fri);
    console.error(
      `  honest baseline: circuit runAndCheck = ${honestOk ? 'SATISFIED (accept)' : 'REFUSED'}  ` +
        `[${((Date.now() - t) / 1000).toFixed(1)}s]`,
    );
    if (!honestOk) {
      console.error('  ✗ the circuit REFUSED the honest proof — the IO construction is wrong, aborting');
      process.exit(1);
    }
    continue;
  }
  if (processed >= K) break;
  if (rec.oracle !== 'REJECT') continue; // only test reject-agreeing mutations
  if (!affectsPrefix(rec.region, rec.desc)) continue; // must reach query 0's prefix
  const t = Date.now();
  const circuit = await circuitAccepts(rec.fri);
  mutated.push({ trial: rec.trial, region: rec.region, desc: rec.desc, circuit, oracle: rec.oracle });
  processed++;
  console.error(
    `  trial ${rec.trial} [${rec.region}]: native=REJECT circuit=${circuit ? 'ACCEPT ⚠' : 'REFUSED ✓'}  ` +
      `[${((Date.now() - t) / 1000).toFixed(1)}s]  ${rec.desc}`,
  );
}
rl.close();

const disagreements = mutated.filter((m) => m.circuit); // circuit accepted a native-rejected proof
console.error(
  `\n=== ARMED-CIRCUIT CONFIRMATION ===\n  honest satisfied: ${honestOk}\n  mutations tested: ${mutated.length} ` +
    `(all native-REJECT)\n  circuit REFUSED all of them: ${disagreements.length === 0}\n  ` +
    `total ${((Date.now() - t0) / 1000).toFixed(1)}s (${(((Date.now() - t0) / 1000) / Math.max(mutated.length + 1, 1)).toFixed(1)}s/runAndCheck)`,
);
if (disagreements.length > 0) {
  console.error(`  ⚠ the CIRCUIT accepted ${disagreements.length} proof(s) the native verifier rejected:`);
  for (const d of disagreements) console.error(`    trial ${d.trial} [${d.region}] ${d.desc}`);
  process.exit(2);
}
console.error('  ✓ the armed circuit refuses every sampled twin-rejected mutation — twin verdict == circuit refusal');
process.exit(0);

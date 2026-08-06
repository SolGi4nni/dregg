// ===========================================================================
// THE MUTATION DIFFERENTIAL — twin half.
//
// A proof-systems review ranked in-circuit verifier fidelity the #1 live risk:
// there is no systematic differential that the o1js FRI verifier accepts iff
// dregg's native verifier accepts. This is that differential, generalised from
// the braid's hand-picked tampers to RANDOM single-felt mutation.
//
//   ../../target/release/root_fri_mutation <seed> <ntrials> | \
//     node --max-old-space-size=16384 dist/scripts/fri-mutation-differential.js [floor]
//
// The Rust side (`circuit-prove/src/bin/root_fri_mutation.rs`) mutates dregg's REAL
// committed root proof one field element at a time, runs the DEPLOYED FRI/PCS
// verifier (`TwoAdicFriPcs::verify`, the object `RootFriWalk.ts` mirrors) as the
// ORACLE, and streams a faithful structural decode per trial. This side walks each
// with the SAME `segmentWalk`/`walkTwin` the armed slice circuit (`runSegments`)
// executes, reduces to a verdict from RAW proof data only, and asserts agreement.
//
// ⚑ VERDICT TEETH — RAW-ONLY. The twin verdict compares reconstructed values only
// against RAW proof commitments the mutation cannot move in lockstep:
//   inputRoot  — input-batch Merkle root == committed input-round root
//   commitRoot — commit-phase Merkle root == committed commit-phase root
//   final      — the fold chain lands on the committed final polynomial
//   preSeal    — derived ζ / LogUp challenges == the committed ones (AIR/FRI seal)
// The `ro` and `fold` checks compare against p3's EMITTED intermediates, which this
// harness re-emits per mutation, so they are vacuous here and are NOT teeth.
//
// ⚑ THREE-VALUED. A bare agreement % is worthless. We report:
//   bothReject          — agree, proof invalid (the expected case)
//   bothAccept          — agree, neither verifier binds this position (a FREE LANE:
//                         an unconstrained field, itself a finding)
//   twinAccept_rustReject — ⚠ FORGERY-SHAPED: the twin would accept what the native
//                         verifier rejects. NO floor beneath it.
//   twinReject_rustAccept — completeness: the twin rejects a proof the native accepts.
// ===========================================================================
import { createInterface } from 'node:readline';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
  airColumnIndex,
  friLaneTable,
  planOpenedValues,
  rootFriShape,
  segmentWalk,
  type RealRootFri,
} from '../src/RootFriWalk.js';
import { airLaneValues, friLaneValues, walkTwin } from '../src/RootFriSlice.js';
import { rootAirDag, bindRealInstance, type RealRootAir } from '../src/RootAirDag.js';

const FLOOR = Number(process.argv[2] ?? '1.0'); // required agreement fraction (default: exact)
const WORK = process.env.FRIMUT_WORKDIR ?? resolve(process.cwd(), '.fullchain');

// ⚑ EXIT CODES, AND WHY THEY ARE NOT ALL 1.
//   0  green
//   1  FAIL     — a real defect in the instrument's own premise (the baseline decode drifted from
//                 the committed proof, the twin rejects the honest proof, the stream is malformed)
//   2  FAIL     — a forgery-shaped disagreement: the twin ACCEPTS what the native verifier rejects
//   3  BLOCKED  — a PREREQUISITE is absent (no `.fullchain/real-root-*.json` on this box). The gate
//                 DID NOT RUN. `scripts/local-gates.sh` prints exit 3 as BLOCKED rather than FAIL
//                 precisely so "there is no proof on this machine" and "the verifiers diverged" are
//                 not the same red line. Anything below-floor must therefore NOT use 3.
//   4  FAIL     — a free lane (both-accept) in a region not allow-listed as unconstrained
//   5  FAIL     — agreement below the floor (was 3, which collided with BLOCKED)
//   6  FAIL     — VACUOUS POPULATION: the run produced too few trials, or an adversary that never
//                 moved anything, to have measured what it reports
const EXIT_FAIL = 1;
const EXIT_FORGERY = 2;
const EXIT_BLOCKED = 3;
const EXIT_FREE_LANE = 4;
const EXIT_BELOW_FLOOR = 5;
const EXIT_VACUOUS = 6;

function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  process.exit(EXIT_FAIL);
}
function blocked(msg: string): never {
  console.error('  ⊘ BLOCKED — ' + msg);
  process.exit(EXIT_BLOCKED);
}

// ---- invariant scaffold (shape + AIR side), built once. -------------------
// ⚑ An ABSENT input is BLOCKED, not FAIL. `.fullchain/` is gitignored and no clone carries it.
const readInput = (name: string): any => {
  const p = resolve(WORK, name);
  try {
    return JSON.parse(readFileSync(p, 'utf8'));
  } catch (e) {
    blocked(
      `${p} is absent or unreadable (${(e as Error).message}). This differential needs dregg's ` +
        'REAL committed root proof; it cannot be synthesised and there is no default. Emit it on a ' +
        'box that has the chain, or point FRIMUT_WORKDIR at one that does.',
    );
  }
};
const realAir = readInput('real-root-air.json') as RealRootAir;
const baseFriDisk = readInput('real-root-fri.json') as RealRootFri;
const shape = rootFriShape(baseFriDisk);
const airIx = airColumnIndex();
const op = planOpenedValues(shape, airIx);
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
  if (!inst) fail(`no real AIR instance for table ${t.name}`);
  const b = bindRealInstance(t, inst);
  airBase.push(...b.base);
  airExt.push(...b.ext);
}
const airLanes = airLaneValues(airBase, airExt);

const eq = (a: bigint[], b: readonly (number | string | bigint)[]) =>
  a.length === b.length && a.every((x, i) => x === BigInt(b[i] as any));

// ⚑ FALSIFIABILITY CONTROL. A gate that cannot go red is not a gate. `FRIMUT_DISABLE_TEETH`
// (comma-separated: inputRoot,commitRoot,final,preSeal) drops named teeth so a control run can
// show that a removed tooth turns the region it guards into forgery-shaped disagreements — i.e.
// the tooth is load-bearing and the instrument CAN detect a twin-accepts/native-rejects hole.
const DISABLED = new Set((process.env.FRIMUT_DISABLE_TEETH ?? '').split(',').map((s) => s.trim()).filter(Boolean));
if (DISABLED.size > 0) console.error(`  ⚑ CONTROL: teeth disabled = {${[...DISABLED].join(', ')}}`);

/** The twin verdict on a proof, out of circuit, from RAW proof data only. */
function twinVerdict(fri: RealRootFri): 'ACCEPT' | 'REJECT' {
  const friLanes = friLaneValues(fri, shape, ft, op);
  const twin = walkTwin(w, shape, ft, op, friLanes, airLanes, fri);
  for (const chk of twin.checks) {
    if (chk.kind === 'inputRoot') {
      if (!DISABLED.has('inputRoot') && !eq(chk.got, fri.inputRounds[chk.round!].commit)) return 'REJECT';
    } else if (chk.kind === 'commitRoot') {
      if (!DISABLED.has('commitRoot') && !eq(chk.got, chk.want!)) return 'REJECT';
    } else if (chk.kind === 'final') {
      if (!DISABLED.has('final') && !eq(chk.got, fri.finalPoly[0])) return 'REJECT';
    } else if (chk.kind === 'preSealZeta' || chk.kind === 'preSealChal') {
      if (!DISABLED.has('preSeal') && !eq(chk.got, chk.want!)) return 'REJECT';
    }
    // 'ro' / 'fold' are cross-checks against re-emitted intermediates — vacuous here.
  }
  return 'ACCEPT';
}

type Outcome = 'bothReject' | 'bothAccept' | 'twinAccept_rustReject' | 'twinReject_rustAccept';
type RegionStat = Record<Outcome, number> & { total: number };
const zero = (): RegionStat => ({
  total: 0,
  bothReject: 0,
  bothAccept: 0,
  twinAccept_rustReject: 0,
  twinReject_rustAccept: 0,
});

const perRegion = new Map<string, RegionStat>();
const forgeries: { trial: number; region: string; desc: string }[] = [];
const completeness: { trial: number; region: string; desc: string }[] = [];
const freeLanes: { trial: number; region: string; desc: string }[] = [];
let trials = 0;
let baselineSeen = false;
/** Trials whose reported `old->new` differ — i.e. the adversary actually moved a field. */
let moved = 0;
/** Trials whose `desc` carried no `old->new` pair at all: the oracle's report shape moved and the
 *  no-op detector below would go blind rather than red. Blind is the failure mode, so it reds. */
let descUnparsed = 0;
/** Trials whose reported mutation left the field where it was — a DEAD ADVERSARY, one at a time. */
const noOpDeltas: { trial: number; region: string; desc: string }[] = [];

function classify(
  trial: number,
  region: string,
  desc: string,
  twin: 'ACCEPT' | 'REJECT',
  rust: 'ACCEPT' | 'REJECT',
) {
  const st = perRegion.get(region) ?? zero();
  st.total++;
  let outcome: Outcome;
  if (twin === rust) outcome = twin === 'REJECT' ? 'bothReject' : 'bothAccept';
  else if (twin === 'ACCEPT') outcome = 'twinAccept_rustReject';
  else outcome = 'twinReject_rustAccept';
  st[outcome]++;
  perRegion.set(region, st);
  if (outcome === 'twinAccept_rustReject') forgeries.push({ trial, region, desc });
  if (outcome === 'twinReject_rustAccept') completeness.push({ trial, region, desc });
  if (outcome === 'bothAccept') freeLanes.push({ trial, region, desc });
}

const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
const t0 = Date.now();

for await (const line of rl) {
  if (!line.trim()) continue;
  const rec = JSON.parse(line) as {
    trial: number;
    region: string;
    desc: string;
    oracle: 'ACCEPT' | 'REJECT';
    fri: RealRootFri;
  };
  if (rec.trial === -1) {
    // Baseline: the on-disk emitter is trusted; assert this streamed decode equals it AND that
    // the twin accepts it. Pins the whole run to the committed proof.
    const tv = twinVerdict(rec.fri);
    if (rec.oracle !== 'ACCEPT') fail('baseline oracle verdict is not ACCEPT — the oracle is broken');
    if (tv !== 'ACCEPT') fail('baseline TWIN verdict is not ACCEPT — the twin or AIR side is broken');
    if (JSON.stringify(rec.fri) !== JSON.stringify(baseFriDisk))
      fail('baseline streamed decode != committed real-root-fri.json — the structural emit drifted');
    baselineSeen = true;
    console.error('  ✓ baseline: streamed decode == committed proof; oracle ACCEPT; twin ACCEPT');
    continue;
  }
  const tv = twinVerdict(rec.fri);
  classify(rec.trial, rec.region, rec.desc, tv, rec.oracle);
  //  ⚑ DID THE FIELD ACTUALLY MOVE. The oracle prints the mutated position's `old->new` canonical
  //  values as the LAST token of `desc`. This reads them back and requires old != new — the direct
  //  detector for the wound this tree has already paid for once, where a mutation quietly became a
  //  no-op and the hostile input equalled the honest one. Nothing else in the pipeline notices: a
  //  no-op mutation yields a valid proof, both verifiers accept, and the run reports agreement.
  const d = /(\d+)->(\d+)\s*$/.exec(rec.desc);
  if (d === null) descUnparsed++;
  else if (d[1] === d[2]) noOpDeltas.push({ trial: rec.trial, region: rec.region, desc: rec.desc });
  else moved++;
  trials++;
  if (trials % 250 === 0)
    console.error(
      `  … ${trials} trials  (${((Date.now() - t0) / trials).toFixed(0)} ms/trial)  ` +
        `forgeries=${forgeries.length} completeness=${completeness.length} freeLanes=${freeLanes.length}`,
    );
}

if (!baselineSeen) fail('no baseline (trial -1) line was seen — the stream is malformed');

// ---- report ----------------------------------------------------------------
const agree = [...perRegion.values()].reduce((a, s) => a + s.bothReject + s.bothAccept, 0);
const agreeFrac = trials === 0 ? 1 : agree / trials;

console.error('\n=== MUTATION DIFFERENTIAL — per-region three-valued ===');
const pad = (s: string, n: number) => s.padEnd(n);
console.error(
  `  ${pad('region', 28)} ${pad('trials', 7)} ${pad('bothRej', 8)} ${pad('bothAcc', 8)} ` +
    `${pad('TWIN>RUST', 10)} ${pad('twin<rust', 10)}`,
);
for (const [rg, s] of [...perRegion.entries()].sort()) {
  console.error(
    `  ${pad(rg, 28)} ${pad(String(s.total), 7)} ${pad(String(s.bothReject), 8)} ` +
      `${pad(String(s.bothAccept), 8)} ${pad(String(s.twinAccept_rustReject), 10)} ` +
      `${pad(String(s.twinReject_rustAccept), 10)}`,
  );
}

const totalForge = forgeries.length;
const totalComp = completeness.length;
const totalFree = freeLanes.length;
console.error(
  `\n  TOTALS: ${trials} trials | agreement ${(agreeFrac * 100).toFixed(3)}% ` +
    `(${agree}/${trials}) | ⚠ forgery-shaped(twin-accept/rust-reject)=${totalForge} | ` +
    `completeness(twin-reject/rust-accept)=${totalComp} | free-lanes(both-accept)=${totalFree}`,
);

const show = (label: string, xs: { trial: number; region: string; desc: string }[]) => {
  if (xs.length === 0) return;
  console.error(`\n  ${label} (${xs.length}):`);
  for (const x of xs.slice(0, 25))
    console.error(`    trial ${x.trial}  [${x.region}]  ${x.desc}`);
  if (xs.length > 25) console.error(`    … and ${xs.length - 25} more`);
};
show('⚠ FORGERY-SHAPED — twin ACCEPTS what native REJECTS (mutating field named)', forgeries);
show('completeness — twin REJECTS what native ACCEPTS', completeness);
show('free lanes — BOTH ACCEPT (unconstrained position — the mutating field is unbound)', freeLanes);

// ---- gate ------------------------------------------------------------------
// Three ways to go red:
//   (1) a forgery-shaped disagreement (twin accepts what native rejects) — hard fail;
//   (2) agreement below the floor (any twin/native disagreement);
//   (3) a free lane (both accept) in a region NOT known to be unconstrained. The commit-phase
//       PoW witnesses are unconstrained BY DESIGN (commitPowBits = 0, so `check_witness` returns
//       true without absorbing them); that region is allow-listed. A free lane anywhere else is a
//       NEWLY unconstrained position — the mutation harness catching a binding that was dropped.
const EXPECTED_FREE = new Set(
  (process.env.FRIMUT_EXPECTED_FREE ?? 'commit_pow_witness').split(',').map((s) => s.trim()).filter(Boolean),
);
const unexpectedFree = [...perRegion.entries()].filter(
  ([rg, s]) => s.bothAccept > 0 && !EXPECTED_FREE.has(rg),
);

// ── ⚑ THE NON-VACUITY FLOOR — three clauses, and the reason each exists ──────
//
// This gate's headline is a NEGATIVE assertion ("no forgery-shaped disagreement"), and every
// negative assertion passes just as happily on a population of zero. `agreeFrac` above was
// literally `trials === 0 ? 1 : …` — an oracle that emitted its baseline and then died would have
// printed `0 trials | agreement 100.000%` and exited GREEN.
//
// ⚠ AND THIS TREE HAS THE EXACT PRECEDENT, one level meaner: a mutation gate whose MUTATION became
// a no-op, so the hostile input equalled the honest one. The gate could still go red; the
// ADVERSARY had died, and nothing measured the adversary. So the floors are on the ADVERSARY, not
// only on the arithmetic:
//
//   [a] DELIVERED — the oracle promised `FRIMUT_MIN_TRIALS` mutations and must have delivered them.
//       A short stream is a broken run, never a clean one.
//   [b] THE FIELD MOVED — every trial's reported `old->new` must differ. This is the DIRECT
//       detector: a mutation that became a no-op produces a valid proof, both verifiers accept, and
//       the run reports agreement. `descUnparsed` reds too, because a report shape that moved would
//       make this clause blind rather than red, and blind is the failure this file exists to refuse.
//   [c] STILL BITES — at least one trial must have been REJECTED BY BOTH sides: the smallest
//       statement that a moved field actually reached a BOUND position rather than a free one.
//   [d] SPREAD — the sampler stratifies over regions; a run that only ever landed in the
//       allow-listed unconstrained region has measured nothing about the bound ones.
//
// The FIFTH floor is not here because it runs earlier and harder: the trial `-1` baseline asserts
// that the streamed decode is BYTE-EQUAL to the committed `real-root-fri.json`. That is what stops
// this gate from mutating a fixture that has since moved out from under it.
//
// ⚠ ORDERING IS LOAD-BEARING AND WAS WRONG ON THE FIRST DRAFT. Vacuity was checked BEFORE the
// forgery arm, and the self-test caught it: with every tooth removed the twin accepts everything, so
// `bothReject` is 0 — the run was reported VACUOUS (6) when the correct verdict was FORGERY (2).
// A forgery-shaped disagreement is itself proof the adversary is alive, so it is decided first.
// The reverse cannot happen: a no-op mutation leaves a proof both sides accept, never a forgery.
const MIN_TRIALS = Number(process.env.FRIMUT_MIN_TRIALS ?? '1');
const boundRegions = [...perRegion.entries()].filter(([rg]) => !EXPECTED_FREE.has(rg));
const totalBothReject = [...perRegion.values()].reduce((a, s) => a + s.bothReject, 0);
const vacuity: string[] = [];
if (trials < MIN_TRIALS)
  vacuity.push(
    `the oracle delivered ${trials} trial(s) against ${MIN_TRIALS} requested — a short stream is a ` +
      'broken run, and a verdict over a population that small is not the verdict it prints',
  );
if (noOpDeltas.length > 0)
  vacuity.push(
    `${noOpDeltas.length} trial(s) report a mutation that LEFT THE FIELD WHERE IT WAS (old == new) ` +
      `— e.g. trial ${noOpDeltas[0].trial} [${noOpDeltas[0].region}] ${noOpDeltas[0].desc}. The ` +
      'hostile input equals the honest one there, so those trials measured nothing',
  );
if (descUnparsed > 0)
  vacuity.push(
    `${descUnparsed} trial(s) carried no \`old->new\` pair in their description, so this run cannot ` +
      'tell a real mutation from a no-op. The oracle\'s report shape moved; re-point the reader ' +
      'rather than dropping the clause',
  );
if (moved === 0)
  vacuity.push('NOT ONE trial moved a field — the adversary is dead');
if (totalBothReject === 0)
  vacuity.push(
    'NOT ONE trial was rejected by both verifiers — every mutation left the proof acceptable. ' +
      'A moved field that never reaches a bound position measures nothing about either verifier',
  );
if (boundRegions.length < 2)
  vacuity.push(
    `only ${boundRegions.length} region(s) outside the allow-listed unconstrained set were sampled ` +
      `(${boundRegions.map(([rg]) => rg).join(', ') || 'none'}) — the stratified sampler is not ` +
      'reaching the bound positions this gate exists to test',
  );

let rc = 0;
if (totalForge > 0) {
  console.error(`\n  ✗ GATE RED: ${totalForge} forgery-shaped disagreement(s) — the twin accepts a proof the native rejects.`);
  rc = EXIT_FORGERY;
} else if (vacuity.length > 0) {
  console.error('\n  ✗ GATE RED (VACUOUS): this run did not measure what its headline claims.');
  for (const v of vacuity) console.error(`      · ${v}`);
  rc = EXIT_VACUOUS;
} else if (agreeFrac < FLOOR) {
  console.error(`\n  ✗ GATE RED: agreement ${(agreeFrac * 100).toFixed(3)}% < floor ${(FLOOR * 100).toFixed(3)}%.`);
  rc = EXIT_BELOW_FLOOR;
} else if (unexpectedFree.length > 0) {
  console.error(
    `\n  ✗ GATE RED: free lanes (both-accept) in unexpected region(s): ` +
      unexpectedFree.map(([rg, s]) => `${rg}=${s.bothAccept}`).join(', ') +
      ` — a position that should be bound is not.`,
  );
  rc = EXIT_FREE_LANE;
} else {
  console.error(
    `\n  ✓ GATE GREEN: no forgery-shaped disagreement; agreement ${(agreeFrac * 100).toFixed(3)}% >= floor ` +
      `${(FLOOR * 100).toFixed(3)}%; free lanes only in the allow-listed unconstrained region(s) {${[...EXPECTED_FREE].join(', ')}}.` +
      `\n    ADVERSARY ALIVE: baseline decode == committed real-root-fri.json; ${trials}/${MIN_TRIALS} trials ` +
      `delivered; ${moved}/${trials} moved a field (0 no-ops); ${totalBothReject} mutation(s) rejected by ` +
      `BOTH verifiers across ${boundRegions.length} bound region(s).`,
  );
}
process.exit(rc);

// ===========================================================================
// THE JOINT (FRI + AIR) MUTATION DIFFERENTIAL — twin half.
//
// A proof-systems review ranked in-circuit verifier fidelity the #1 live risk. A sibling measured
// the FRI half (scripts/fri-mutation-differential.ts). This is the AIR half AND the JOINT proof:
// for each single-felt mutation of dregg's REAL committed root proof, run BOTH out-of-circuit twins
// — the FRI walk (`walkTwin`, sharing `segmentWalk` with the armed slice circuit `runSegments`) and
// the AIR closing equality (the DAG fold `evalDagBigInt`/`foldRootsP3BigInt`, sharing node-walk code
// with the armed `RootAirProcessChain` circuit `sliceWork`, plus a quotient recompose) — and assert
// each agrees with its native oracle, three-valued, per structural region. THEN the JOINT verdict:
// a proof is valid iff BOTH halves accept, so a joint forgery is a mutation the combined TWIN
// accepts and the combined ORACLE rejects — the thing with no floor beneath it.
//
//   ../../target/release/root_proof_mutation <seed> <ntrials> | \
//     node --max-old-space-size=16384 dist/scripts/proof-mutation-differential.js [floor]
//
// The Rust side (`circuit-prove/src/bin/root_proof_mutation.rs`) mutates ONE decoded proof and runs
// BOTH native verifiers on it — the deployed `TwoAdicFriPcs::verify` and the deployed per-instance
// AIR closing equality — then streams a faithful FRI decode AND AIR decode of the SAME proof. One
// proof, one mutation, both decodes: a SHARED position (a commitment, an opened value at zeta) is
// mutated once and both halves see it in lockstep — there is no FRI/AIR copy to desync.
//
// ⚑ AIR TWIN TEETH — RAW-ONLY. The AIR verdict recomputes, from RAW opened values, the two sides of
// the closing equality and compares them:
//   accRecompute      — the accumulator = foldRootsP3(alpha, evalDag(table, opened)) over the RAW
//                       opened trace/prep/perm/public columns (the armed circuit's `sliceWork` fold)
//   quotientRecompute — quotient(zeta) = Σ_j zps[j]·fromExtBasis(rawChunk_j) over the RAW opened
//                       quotient chunks (`zps` are the Lagrange weights at zeta the emitter carries)
// The emitted `accumulator` / `quotientAtZeta` are the Rust side's OWN values; reading them instead
// of recomputing would be blind to opened-value forgeries — which is exactly what the
// `PROOFMUT_DISABLE_TEETH` control demonstrates.
//
// ⚑ THREE-VALUED, three verifiers (FRI / AIR / JOINT):
//   bothReject            — agree, proof invalid (expected).
//   bothAccept            — agree, this verifier does not bind this position (a FREE LANE — for the
//                           JOINT verifier a free lane outside the by-design-unconstrained region is
//                           a position NEITHER half binds, itself a finding).
//   twinAccept_oracleReject — ⚠ FORGERY-SHAPED: the twin accepts what the native rejects.
//   twinReject_oracleAccept — completeness: the twin rejects what the native accepts.
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
import { rootAirDag, bindRealInstance } from '../src/RootAirDag.js';

const FLOOR = Number(process.argv[2] ?? '1.0');
const WORK = process.env.PROOFMUT_WORKDIR ?? resolve(process.cwd(), '.fullchain');

function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  process.exit(1);
}

// ---- FRI scaffold (shape + walk plan), built once from the trusted baseline. ---------------
const baseFriDisk = JSON.parse(readFileSync(resolve(WORK, 'real-root-fri.json'), 'utf8')) as RealRootFri;
const shape = rootFriShape(baseFriDisk);
const airIx = airColumnIndex();
const op = planOpenedValues(shape, airIx);
const ft = friLaneTable(shape, op);
const w = segmentWalk(shape);
const dag = rootAirDag();

// ---- bigint extension arithmetic (BabyBear^4, W = 11), as RootAirDag's twin. ---------------
const P = 2013265921n;
const EXT_W = 11n;
const md = (x: bigint) => ((x % P) + P) % P;
const eAdd = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x + b[i]));
function eMul(a: bigint[], b: bigint[]): bigint[] {
  const acc = Array(7).fill(0n) as bigint[];
  for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) acc[i + j] = md(acc[i + j] + a[i] * b[j]);
  return Array.from({ length: 4 }, (_, i) => (i + 4 < 7 ? md(acc[i] + EXT_W * acc[i + 4]) : acc[i]));
}
/** `Challenge::from_ext_basis_coefficients(ch)` = Σ_k ch[k]·X^k, X^4 folded by W. `ch` is D EF. */
function fromExtBasis(ch: bigint[][]): bigint[] {
  const out = [0n, 0n, 0n, 0n];
  for (let k = 0; k < ch.length; k++)
    for (let i = 0; i < 4; i++) {
      const dd = k + i;
      const slot = dd < 4 ? dd : dd - 4;
      const scale = dd < 4 ? 1n : EXT_W;
      out[slot] = md(out[slot] + scale * ch[k][i]);
    }
  return out;
}
const evalDagBigInt = (t: any, base: bigint[][], ext: bigint[][]): bigint[][] => {
  const KIND = { var: 0, cst: 1, add: 2, sub: 3, neg: 4, mul: 5, evar: 6, ecst: 7 };
  const v: bigint[][] = new Array(t.nodes.length);
  for (let i = 0; i < t.nodes.length; i++) {
    const n = t.nodes[i];
    switch (n[0]) {
      case KIND.var: v[i] = base[n[1]]; break;
      case KIND.cst: v[i] = [md(BigInt(n[1])), 0n, 0n, 0n]; break;
      case KIND.add: v[i] = eAdd(v[n[1]], v[n[2]]); break;
      case KIND.sub: v[i] = v[n[1]].map((x, k) => md(x - v[n[2]][k])); break;
      case KIND.neg: v[i] = v[n[1]].map((x) => md(-x)); break;
      case KIND.mul: v[i] = eMul(v[n[1]], v[n[2]]); break;
      case KIND.evar: v[i] = ext[n[1]]; break;
      case KIND.ecst: v[i] = [md(BigInt(n[1])), md(BigInt(n[2])), md(BigInt(n[3])), md(BigInt(n[4]))]; break;
      default: throw new Error(`unknown kind ${n[0]}`);
    }
  }
  return t.roots.map((r: number) => v[r]);
};
const foldRootsP3BigInt = (alpha: bigint[], roots: bigint[][]): bigint[] => {
  let acc = [0n, 0n, 0n, 0n];
  for (const c of roots) acc = eAdd(eMul(acc, alpha), c);
  return acc;
};

const eqB = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);
const eq = (a: bigint[], b: readonly (number | string | bigint)[]) =>
  a.length === b.length && a.every((x, i) => x === BigInt(b[i] as any));

// ⚑ FALSIFIABILITY CONTROL. `PROOFMUT_DISABLE_TEETH` (comma-separated) drops named teeth so a
// control run shows the guarded region turning forgery-shaped — proving the tooth is load-bearing.
//   FRI teeth: inputRoot, commitRoot, final, preSeal
//   AIR teeth: accRecompute, quotientRecompute
const DISABLED = new Set((process.env.PROOFMUT_DISABLE_TEETH ?? '').split(',').map((s) => s.trim()).filter(Boolean));
if (DISABLED.size > 0) console.error(`  ⚑ CONTROL: teeth disabled = {${[...DISABLED].join(', ')}}`);

// ---- FRI twin verdict (walkTwin + RAW-only teeth), airLanes supplied PER TRIAL. -------------
function friTwinVerdict(fri: RealRootFri, airLanes: bigint[]): 'ACCEPT' | 'REJECT' {
  if ((fri as any).kind === 'degenerate') return 'REJECT';
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
  }
  return 'ACCEPT';
}

// ---- AIR twin verdict (per-instance closing equality, RAW-only recompute). ------------------
type AirInst = {
  table: string;
  accumulator: number[];
  quotientAtZeta: number[];
  quotientChunks: number[][][];
  zps: number[][];
  selectors: { invVanishing: number[] };
};
function airTwinVerdict(air: any): 'ACCEPT' | 'REJECT' {
  if (air.kind === 'degenerate') return 'REJECT';
  // ⚑ THE DEPLOYED-PATH CONTROL. `PROOFMUT_DISABLE_TEETH=airClosing` drops the closing equality
  // entirely — modelling the DEPLOYED o1js AIR path, which recomputes acc from the opened trace and
  // seals it but NEVER checks `acc·invZ == quotient(zeta)` against the opened quotient chunks
  // (root-air-fullchain [7] compares acc against the RUST-emitted per-instance accumulators; there is
  // no `recomposeQuotient`/`invVanishing` binding for the root). Under it, every AIR-bound opened
  // position becomes forgery-shaped against the native AIR oracle — the tooth is load-bearing — while
  // the JOINT stays sound because FRI independently binds those opened values.
  if (DISABLED.has('airClosing')) return 'ACCEPT';
  const alpha = air.challenges.alpha.map((x: number) => BigInt(x));
  const byName: Record<string, AirInst> = {};
  for (const inst of air.instances as AirInst[])
    byName[inst.table.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_')] = inst;
  for (const t of dag.tables) {
    const inst = byName[t.name] ?? byName[t.name.toLowerCase()];
    if (!inst) fail(`AIR decode has no instance for DAG table ${t.name}`);
    // acc — recomputed from RAW opened values via the DAG (the armed circuit's fold), unless the
    // tooth is disabled, in which case the Rust side's emitted accumulator stands in (blind).
    let acc: bigint[];
    if (DISABLED.has('accRecompute')) acc = inst.accumulator.map((x) => BigInt(x));
    else {
      const { base, ext } = bindRealInstance(t as any, inst as any);
      acc = foldRootsP3BigInt(alpha, evalDagBigInt(t, base, ext));
    }
    // quotient — recomposed from RAW opened chunks via the emitted Lagrange weights, unless disabled.
    let quot: bigint[];
    if (DISABLED.has('quotientRecompute')) quot = inst.quotientAtZeta.map((x) => BigInt(x));
    else {
      const zps = inst.zps.map((z) => z.map((x) => BigInt(x)));
      const chunks = inst.quotientChunks.map((c) => c.map((v) => v.map((x) => BigInt(x))));
      quot = [0n, 0n, 0n, 0n];
      for (let j = 0; j < chunks.length; j++) quot = eAdd(quot, eMul(zps[j], fromExtBasis(chunks[j])));
    }
    const invVan = inst.selectors.invVanishing.map((x) => BigInt(x));
    if (!eqB(eMul(acc, invVan), quot)) return 'REJECT';
  }
  return 'ACCEPT';
}

/** airLanes for the FRI twin, rebuilt from THIS trial's AIR decode so a shared opened-value
 *  mutation is reflected in the FRI reduced-opening reconstruction too. */
function airLanesOf(air: any): bigint[] {
  if (air.kind === 'degenerate') return [];
  const byName: Record<string, any> = {};
  for (const i of air.instances)
    byName[i.table.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_')] = i;
  const airBase: bigint[][] = [];
  const airExt: bigint[][] = [];
  for (const t of dag.tables) {
    const inst = byName[t.name] ?? byName[t.name.toLowerCase()];
    const b = bindRealInstance(t as any, inst);
    airBase.push(...b.base);
    airExt.push(...b.ext);
  }
  return airLaneValues(airBase, airExt);
}

// ---- three-valued bookkeeping, per verifier. ----------------------------------------------
type Outcome = 'bothReject' | 'bothAccept' | 'twinAccept_oracleReject' | 'twinReject_oracleAccept';
type RegionStat = Record<Outcome, number> & { total: number };
const zero = (): RegionStat => ({ total: 0, bothReject: 0, bothAccept: 0, twinAccept_oracleReject: 0, twinReject_oracleAccept: 0 });
type Verifier = 'FRI' | 'AIR' | 'JOINT';
const perRegion: Record<Verifier, Map<string, RegionStat>> = { FRI: new Map(), AIR: new Map(), JOINT: new Map() };
const forgeries: Record<Verifier, { trial: number; region: string; desc: string }[]> = { FRI: [], AIR: [], JOINT: [] };
const completeness: Record<Verifier, { trial: number; region: string; desc: string }[]> = { FRI: [], AIR: [], JOINT: [] };
const freeLanes: Record<Verifier, { trial: number; region: string; desc: string }[]> = { FRI: [], AIR: [], JOINT: [] };

function classify(v: Verifier, trial: number, region: string, desc: string, twin: 'ACCEPT' | 'REJECT', oracle: 'ACCEPT' | 'REJECT') {
  const st = perRegion[v].get(region) ?? zero();
  st.total++;
  let outcome: Outcome;
  if (twin === oracle) outcome = twin === 'REJECT' ? 'bothReject' : 'bothAccept';
  else if (twin === 'ACCEPT') outcome = 'twinAccept_oracleReject';
  else outcome = 'twinReject_oracleAccept';
  st[outcome]++;
  perRegion[v].set(region, st);
  if (outcome === 'twinAccept_oracleReject') forgeries[v].push({ trial, region, desc });
  if (outcome === 'twinReject_oracleAccept') completeness[v].push({ trial, region, desc });
  if (outcome === 'bothAccept') freeLanes[v].push({ trial, region, desc });
}

const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
const t0 = Date.now();
let trials = 0;
let baselineSeen = false;

for await (const line of rl) {
  if (!line.trim()) continue;
  const rec = JSON.parse(line) as {
    trial: number; region: string; desc: string;
    friOracle: 'ACCEPT' | 'REJECT'; airOracle: 'ACCEPT' | 'REJECT';
    fri: RealRootFri; air: any;
  };
  const airLanes = airLanesOf(rec.air);
  const friTwin = friTwinVerdict(rec.fri, airLanes);
  const airTwin = airTwinVerdict(rec.air);

  if (rec.trial === -1) {
    if (rec.friOracle !== 'ACCEPT' || rec.airOracle !== 'ACCEPT') fail('baseline oracle verdict is not ACCEPT — an oracle is broken');
    if (friTwin !== 'ACCEPT') fail('baseline FRI twin is not ACCEPT — the FRI twin or AIR-lane scaffold is broken');
    if (airTwin !== 'ACCEPT') fail('baseline AIR twin is not ACCEPT — the AIR closing-equality twin is broken');
    if (JSON.stringify(rec.fri) !== JSON.stringify(baseFriDisk)) fail('baseline FRI decode != committed real-root-fri.json — the structural emit drifted');
    baselineSeen = true;
    console.error('  ✓ baseline: FRI decode == committed proof; both oracles ACCEPT; both twins ACCEPT');
    continue;
  }

  const friOracle = rec.friOracle;
  const airOracle = rec.airOracle;
  const jointTwin: 'ACCEPT' | 'REJECT' = friTwin === 'ACCEPT' && airTwin === 'ACCEPT' ? 'ACCEPT' : 'REJECT';
  const jointOracle: 'ACCEPT' | 'REJECT' = friOracle === 'ACCEPT' && airOracle === 'ACCEPT' ? 'ACCEPT' : 'REJECT';

  classify('FRI', rec.trial, rec.region, rec.desc, friTwin, friOracle);
  classify('AIR', rec.trial, rec.region, rec.desc, airTwin, airOracle);
  classify('JOINT', rec.trial, rec.region, rec.desc, jointTwin, jointOracle);
  trials++;
  if (trials % 250 === 0)
    console.error(
      `  … ${trials} trials  (${((Date.now() - t0) / trials).toFixed(0)} ms/trial)  ` +
        `forgeries FRI=${forgeries.FRI.length} AIR=${forgeries.AIR.length} JOINT=${forgeries.JOINT.length}`,
    );
}

if (!baselineSeen) fail('no baseline (trial -1) line was seen — the stream is malformed');

// ---- report ----------------------------------------------------------------
const pad = (s: string, n: number) => s.padEnd(n);
function reportVerifier(v: Verifier) {
  const agree = [...perRegion[v].values()].reduce((a, s) => a + s.bothReject + s.bothAccept, 0);
  const frac = trials === 0 ? 1 : agree / trials;
  console.error(`\n=== ${v} MUTATION DIFFERENTIAL — per-region three-valued ===`);
  console.error(`  ${pad('region', 28)} ${pad('trials', 7)} ${pad('bothRej', 8)} ${pad('bothAcc', 8)} ${pad('TWIN>ORAC', 10)} ${pad('twin<orac', 10)}`);
  for (const [rg, s] of [...perRegion[v].entries()].sort())
    console.error(
      `  ${pad(rg, 28)} ${pad(String(s.total), 7)} ${pad(String(s.bothReject), 8)} ${pad(String(s.bothAccept), 8)} ` +
        `${pad(String(s.twinAccept_oracleReject), 10)} ${pad(String(s.twinReject_oracleAccept), 10)}`,
    );
  console.error(
    `  TOTALS ${v}: ${trials} trials | agreement ${(frac * 100).toFixed(3)}% (${agree}/${trials}) | ` +
      `⚠ forgery-shaped=${forgeries[v].length} | completeness=${completeness[v].length} | free-lanes=${freeLanes[v].length}`,
  );
  return frac;
}
const fracFri = reportVerifier('FRI');
const fracAir = reportVerifier('AIR');
const fracJoint = reportVerifier('JOINT');

const show = (label: string, xs: { trial: number; region: string; desc: string }[]) => {
  if (xs.length === 0) return;
  console.error(`\n  ${label} (${xs.length}):`);
  for (const x of xs.slice(0, 25)) console.error(`    trial ${x.trial}  [${x.region}]  ${x.desc}`);
  if (xs.length > 25) console.error(`    … and ${xs.length - 25} more`);
};
for (const v of ['FRI', 'AIR', 'JOINT'] as Verifier[]) {
  show(`⚠ ${v} FORGERY-SHAPED — twin ACCEPTS what native REJECTS`, forgeries[v]);
  show(`${v} completeness — twin REJECTS what native ACCEPTS`, completeness[v]);
}

// ---- gate ------------------------------------------------------------------
// The JOINT verifier is what closes Fable's #1: a proof is valid iff BOTH halves accept. A free lane
// (both-accept) in the JOINT verifier is a position NEITHER half binds; commit_pow_witness is
// unconstrained by design (commitPowBits = 0), so it is allow-listed. Anywhere else it is a finding.
const EXPECTED_FREE = new Set(
  (process.env.PROOFMUT_EXPECTED_FREE ?? 'commit_pow_witness').split(',').map((s) => s.trim()).filter(Boolean),
);
const jointForge = forgeries.JOINT.length;
const friForge = forgeries.FRI.length;
const airForge = forgeries.AIR.length;
const unexpectedFreeJoint = [...perRegion.JOINT.entries()].filter(([rg, s]) => s.bothAccept > 0 && !EXPECTED_FREE.has(rg));

let rc = 0;
if (jointForge > 0 || friForge > 0 || airForge > 0) {
  console.error(`\n  ✗ GATE RED: forgery-shaped disagreement(s) — FRI=${friForge} AIR=${airForge} JOINT=${jointForge}. A twin accepts what a native verifier rejects.`);
  rc = 2;
} else if (fracJoint < FLOOR || fracFri < FLOOR || fracAir < FLOOR) {
  console.error(`\n  ✗ GATE RED: agreement below floor ${(FLOOR * 100).toFixed(3)}% — FRI=${(fracFri * 100).toFixed(3)}% AIR=${(fracAir * 100).toFixed(3)}% JOINT=${(fracJoint * 100).toFixed(3)}%.`);
  rc = 3;
} else if (unexpectedFreeJoint.length > 0) {
  console.error(
    `\n  ✗ GATE RED: JOINT free lanes (both-accept) in unexpected region(s): ` +
      unexpectedFreeJoint.map(([rg, s]) => `${rg}=${s.bothAccept}`).join(', ') +
      ` — a position NEITHER verifier binds.`,
  );
  rc = 4;
} else {
  console.error(
    `\n  ✓ GATE GREEN: no forgery-shaped disagreement (FRI/AIR/JOINT); agreement ` +
      `FRI=${(fracFri * 100).toFixed(3)}% AIR=${(fracAir * 100).toFixed(3)}% JOINT=${(fracJoint * 100).toFixed(3)}% >= floor ${(FLOOR * 100).toFixed(3)}%; ` +
      `JOINT free lanes only in the allow-listed unconstrained region(s) {${[...EXPECTED_FREE].join(', ')}}.`,
  );
}
process.exit(rc);

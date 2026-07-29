import { execFile } from 'node:child_process';
import {
  Cache,
  DynamicProof,
  FeatureFlags,
  Field,
  Poseidon,
  Provable,
  SelfProof,
  VerificationKey,
  ZkProgram,
} from 'o1js';
import { BbExt, extAdd, extMul } from '../src/FriQueryStep.js';
import { canonicalLane } from '../src/Poseidon2BabyBearW16.js';
import { UnifiedDag, rootAirDag, unifiedDag } from '../src/RootAirDag.js';
import {
  ChainPlan,
  digestOfLanes,
  extLanes,
  makeRootAirChain,
  planRootAirChain,
  sliceCommitment,
  sliceWork,
  stepBoundary,
} from '../src/RootAirChain.js';
import { makeSliceProgram } from '../src/RootAirProcessChain.js';
import { MEASURED_CEILING } from '../src/PartitionSchedule.js';

// ---------------------------------------------------------------------------
// LEG 16 — THE COMPILE CEILING, BISECTED.
//
// §3.24 left a named follow-up with two numbers and a gap between them: at
// §4.1's arithmetic budget of 57,532 usable rows the three-slice chain FAILS to
// compile with `length mismatch in Array.map2_exn: 1 <> 2`, and at 50,000 it
// compiles. Every step count in the record — §3.23's 519 and 448 — is computed
// against §4.1's ARITHMETIC overhead (~8,000 at `max_proofs_verified = 1`,
// ~16,000 at 2), so all of them are optimistic by however much that arithmetic
// is wrong, and nobody had measured it.
//
// ⚑ WHAT THE CEILING ACTUALLY IS, AND WHY IT IS A ROW COUNT AND NOT A DOMAIN.
// Pickles builds each branch as `method body + recursive verifier`. The DOMAIN
// is the next power of two at or above that sum, and `numChunks` is that domain
// over 2^16. `analyzeMethods` reports the BODY only, so a body comfortably under
// 65,536 can still put its branch over — and when one branch crosses while
// another does not, the two disagree on `numChunks` and Pickles dies inside
// `Array.map2_exn`. So the ceiling is
//
//     usable = 65536 - OVERHEAD(shape)
//
// and OVERHEAD is a property of the branch's shape — how many proofs it
// verifies, and whether the verification key is baked in or side-loaded. This
// leg MEASURES it for the four shapes the record quotes or needs, instead of
// quoting §4.1's estimate.
//
// ⚑ THE INSTRUMENT IS TWO INDEPENDENT MEASUREMENTS THAT MUST AGREE.
//
//   [A] THE REAL OBJECT. Narrow the three-slice root-AIR chain's row budget
//       between 50,000 (compiles) and 57,532 (does not). This is the honest
//       ceiling for the shape §3.24 measured, and it needs no model at all.
//   [B] A DIALABLE PROBE, same gate vocabulary (witnessed BabyBear-quartic lanes
//       through `canonicalLane`, then an `extMul`/`extAdd` chain), with a
//       ONE-ROW knob on top so the crossing can be found to well under the
//       cheapest atom in the schedule.
//
// [B]'s `mpv1` arm is the same shape as [A], so [A] BRACKETS it and the leg
// FAILS if they disagree. That is what licenses `mpv2` — the shape §3.23's
// headline 519 is priced against, which no circuit in this repo has — and
// `sideload`, the shape leg 17's process-per-slice chain runs at.
//
// ⚑ AND A LONE BRANCH IS A DIFFERENT QUESTION FROM A BRANCH WITH A SIBLING.
// `Array.map2_exn: 1 <> 2` is a DISAGREEMENT between branches, so a program with
// ONE branch might have no ceiling here at all. `sideload` is measured solo,
// because that is how leg 17 compiles it: one method per program, one program
// per process.
//
// ⚑ WHY THE SEARCH IS PARALLEL AND NOT A BISECT. A failing compile is SLOWER
// than a passing one (it builds a 2^17 domain before it dies): 5.9 min against
// 1.9 min, measured. A sequential bisect over four arms is hours. Each round
// therefore evaluates FIVE points at once in five child processes and keeps the
// tightest bracket, which divides the interval by six per round instead of two —
// and it checks MONOTONICITY, because "the largest budget that compiles" is only
// a ceiling if everything below it compiles too.
// ---------------------------------------------------------------------------

const MODE = process.env.CEILING_MODE ?? 'main';
const NO_CACHE = Cache.None;
const CHUNK_SIZE = 64;
const LANE_MAX = (1n << 31n) - 1n;
const KIMCHI_ROWS = 65_536;
/** Interior points per shape per round. Three shapes narrow in the SAME waves,
 *  so a round is twelve child processes; each measures ~2 cores and a few GB of
 *  wasm heap. Four per shape divides every bracket by five per round. */
const PER_ARM = 4;
/** The search stops when the bracket is under this many rows. The cheapest atom
 *  in the whole emitted schedule is an 18-row extension add and the ratchet is
 *  at 2%, so 128 rows is below the resolution the number is used at. */
const TOL = 128;
/** ⚑ FULL narrowing is opt-in. An ordinary run re-CHECKS the recorded crossings
 *  instead of re-searching for them: eight compiles instead of eighty, and it
 *  can still go red, which is the only property that matters for a gate. */
const FULL = process.env.CEILING_FULL === '1';

/**
 * ⚑ THE RECORDED CROSSINGS, from the full narrowing. `ok*` COMPILES and `fail*`
 * does not; `*Rows` is what `analyzeMethods` measured for the widest branch at
 * that point. Every ordinary run re-runs exactly those four pairs and fails if
 * either side has moved — a recorded ceiling nobody holds to anything is how
 * §4.1's arithmetic survived being wrong for as long as it did.
 */
const RECORDED = {
  /** ⚑ NARROWED, both sides. */
  mpv1: { okBudget: 54_289, failBudget: 54_324, okRows: 54_300, failRows: 54_376 },
  /** ⚠ ONE-SIDED. `failBudget: 0` means this shape's crossing has NOT been
   *  narrowed and the re-check is therefore only the COMPILING half: it can go
   *  red if the envelope stops holding, and it CANNOT notice the ceiling moving
   *  up. That is a named hole, not a rounding — `CEILING_FULL=1` closes it. */
  mpv2: { okBudget: 40_000, failBudget: 0, okRows: 40_073, failRows: 0 },
  sideload: { okBudget: 50_000, failBudget: 0, okRows: 51_136, failRows: 0 },
};

let checks = 0;
const ok = (m: string) => {
  checks++;
  console.log(`  ✓ ${m}`);
};
const fail = (m: string): never => {
  console.error(`\n✗ ${m}`);
  process.exit(1);
};
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');
const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(1)}s`;

/** ⚑ A COMPILE FAILURE MUST BE THE CHUNKING FAILURE. An out-of-memory abort, a
 *  `TypeError` from a mis-shaped program or a missing binding is a HARNESS
 *  error, and recording one as "the ceiling" would put the ceiling wherever the
 *  harness happened to break. The search refuses a failure it cannot attribute. */
const CHUNK_FAILURE = /map2_exn|numChunks|chunk/i;

/** §4.1's implied overhead for a stated usable-row figure. */
const usable41 = (usable: number) => KIMCHI_ROWS - 4 - usable;

// ===========================================================================
// The dialable probe.
// ===========================================================================

export type Arm = 'mpv1' | 'mpv2' | 'sideload' | 'shape';

/**
 * ⚑ THE ARMS ARE REAL SLICE BODIES, AND THE FIRST VERSION OF THIS LEG WAS WRONG
 * ABOUT THAT.
 *
 * The first instrument here was a DIALABLE PROBE — the same gate vocabulary
 * (`canonicalLane`, `extMul`/`extAdd`) plus a one-row knob — on the theory that
 * the ceiling is `65536 − OVERHEAD(proof arity)` and the body only has to supply
 * rows. It is not, and the probe refuted itself:
 *
 *   * at **57,769** body rows, one `SelfProof` branch beside a small sibling,
 *     built from the extension-arithmetic mix — `compile()` FAILS with
 *     `Array.map2_exn: 1 <> 2`;
 *   * at **63,300** body rows, the SAME arm, the same sibling, with the extra
 *     rows supplied by single-row field multiplies — `compile()` SUCCEEDS.
 *
 * A bigger circuit compiling where a smaller one does not is not a ceiling in
 * rows at all. Kimchi's row count is not what crosses 2^16: range checks and
 * lookups carry a table and a domain requirement that `analyzeMethods` does not
 * report, so **the crossing is a function of the gate MIX and not of the row
 * count**. That kills the idea `usableRows` names — a per-`max_proofs_verified`
 * constant good for any circuit — and it means the only honest ceiling for a
 * shape is measured ON that shape.
 *
 * So every arm below is a REAL slice: `sliceCommitment` and `sliceWork`,
 * imported from the chain the leg exists to price, dialled by the planner's own
 * budget. `shape` is what is left of the probe — TWO fixed points, kept as a
 * permanent control, so that a future reader who reinstates a single-number
 * ceiling has to walk past a green test saying it cannot be one.
 */

/** One real slice body, with an optional predecessor boundary. */
function realSliceBody(
  u: UnifiedDag,
  plan: ChainPlan,
  si: number,
  bIn: Field,
  prevOut: Field | null,
  alpha: BbExt,
  accIn: BbExt,
  liveInVals: BbExt[],
  readLanes: Field[],
  otherDigests: Field[],
): Field {
  const s = plan.slices[si];
  const dagDigest = sliceCommitment(plan, s, readLanes, otherDigests);
  for (const e of [...liveInVals, accIn, alpha]) for (const x of e.limbs) canonicalLane(x, LANE_MAX);
  const liveInDigest =
    si === 0
      ? Field(0)
      : digestOfLanes([...liveInVals.flatMap(extLanes), ...extLanes(accIn), ...extLanes(alpha)]);
  stepBoundary(dagDigest, liveInDigest, si).assertEquals(bIn);
  if (prevOut) prevOut.assertEquals(bIn);
  const { acc, liveOutVals } = sliceWork(u, plan, s, alpha, accIn, liveInVals, readLanes);
  return stepBoundary(
    dagDigest,
    digestOfLanes([...liveOutVals.flatMap(extLanes), ...extLanes(acc), ...extLanes(alpha)]),
    si + 1,
  );
}

const sliceInputs = (plan: ChainPlan, si: number) => {
  const s = plan.slices[si];
  return {
    nLiveIn: s.liveIn.length,
    nReadLanes: s.readsChunks.length * plan.chunkSize * 4,
    nOtherDigests: plan.nColChunks - s.readsChunks.length,
    wide: [
      BbExt,
      BbExt,
      Provable.Array(BbExt, Math.max(s.liveIn.length, 1)),
      Provable.Array(Field, Math.max(s.readsChunks.length * plan.chunkSize * 4, 1)),
      Provable.Array(Field, Math.max(plan.nColChunks - s.readsChunks.length, 1)),
    ],
  };
};

/**
 * ⚑ THE `max_proofs_verified = 2` SHAPE, WHICH NO CIRCUIT IN THIS REPO HAS AND
 * WHICH §3.23's HEADLINE 519 IS PRICED AGAINST. Two REAL slice bodies — slice 0
 * with no predecessor, slice 1 with TWO — so the program's `maxProofsVerified`
 * is 2 and Pickles builds the aggregation-tree verifier into every branch. The
 * bodies are the chain's own; only the arity is new.
 */
function makeMpv2Program(u: UnifiedDag, plan: ChainPlan) {
  const a = sliceInputs(plan, 0);
  const b = sliceInputs(plan, 1);
  return ZkProgram({
    name: 'ceiling-mpv2',
    publicInput: Field,
    publicOutput: Field,
    methods: {
      first: {
        privateInputs: a.wide,
        async method(bIn: Field, alpha: BbExt, accIn: BbExt, live: BbExt[], lanes: Field[], others: Field[]) {
          return {
            publicOutput: realSliceBody(u, plan, 0, bIn, null, alpha, accIn,
              live.slice(0, a.nLiveIn), lanes.slice(0, a.nReadLanes), others.slice(0, a.nOtherDigests)),
          };
        },
      },
      merge: {
        privateInputs: [SelfProof, SelfProof, ...b.wide],
        async method(
          bIn: Field,
          p1: SelfProof<Field, Field>,
          p2: SelfProof<Field, Field>,
          alpha: BbExt,
          accIn: BbExt,
          live: BbExt[],
          lanes: Field[],
          others: Field[],
        ) {
          p1.verify();
          p2.verify();
          return {
            publicOutput: realSliceBody(u, plan, 1, bIn, p1.publicOutput, alpha, accIn,
              live.slice(0, b.nLiveIn), lanes.slice(0, b.nReadLanes), others.slice(0, b.nOtherDigests)),
          };
        },
      },
    } as any,
  });
}

// --- what is left of the synthetic probe: a two-point SHAPE control ----------

const PROBE_INPUTS = 4;
/** 48 rows per coarse step: one 30-row `extMul` and one 18-row `extAdd`. */
export const PROBE_ROWS_PER_COARSE = 48;

function probeBody(pub: Field, xs: BbExt[], coarse: number, fine: number): Field {
  for (const e of xs) for (const l of e.limbs) canonicalLane(l, LANE_MAX);
  let a = xs[0];
  let b = xs[1];
  for (let i = 0; i < coarse; i++) {
    const n = extMul(a, b);
    b = extAdd(a, b);
    a = n;
  }
  let f = pub.add(a.limbs[0]);
  for (let i = 0; i < fine; i++) f = f.mul(f);
  return Poseidon.hash([f, ...a.limbs, ...b.limbs]);
}

function makeShapeProgram(coarse: number, fine: number) {
  const wide = Provable.Array(BbExt, PROBE_INPUTS);
  return ZkProgram({
    name: `ceiling-shape-${coarse}-${fine}`,
    publicInput: Field,
    publicOutput: Field,
    methods: {
      wide: {
        privateInputs: [SelfProof, wide],
        async method(pub: Field, prev: SelfProof<Field, Field>, xs: BbExt[]) {
          prev.verify();
          return { publicOutput: probeBody(pub, xs, coarse, fine) };
        },
      },
      small: {
        privateInputs: [wide],
        async method(pub: Field, xs: BbExt[]) {
          return { publicOutput: probeBody(pub, xs, 8, 0) };
        },
      },
    } as any,
  });
}

// ===========================================================================
// The child phases — one compile attempt per process, so a wasm abort is a
// FAILED TRIAL rather than a dead search.
// ===========================================================================

const CHUNK = CHUNK_SIZE;

/**
 * The emitted rows of slice `si`'s BODY, measured through the chain's own
 * `sliceCommitment`/`sliceWork` in this process. It is the body a side-loaded
 * branch carries; the side-loaded verifier Pickles puts on top is what the
 * compile attempt then prices.
 */
async function sliceBodyRows(u: UnifiedDag, plan: ChainPlan, si: number): Promise<number> {
  const { nLiveIn, nReadLanes, nOtherDigests } = sliceInputs(plan, si);
  const cs = await Provable.constraintSystem(() => {
    const bIn = Provable.witness(Field, () => Field(0));
    const alpha = Provable.witness(BbExt, () => BbExt.zero());
    const accIn = Provable.witness(BbExt, () => BbExt.zero());
    const live = Array.from({ length: nLiveIn }, () => Provable.witness(BbExt, () => BbExt.zero()));
    const lanes = Array.from({ length: nReadLanes }, () => Provable.witness(Field, () => Field(0)));
    const others = Array.from({ length: nOtherDigests }, () => Provable.witness(Field, () => Field(0)));
    realSliceBody(u, plan, si, bIn, null, alpha, accIn, live, lanes, others);
  });
  return cs.rows;
}

const attempt = async (prog: any, extra: Record<string, unknown>) => {
  const out: any = { ...extra };
  let t = Date.now();
  const meta = (await prog.analyzeMethods()) as any;
  out.rows = Math.max(...Object.values(meta).map((m: any) => m.rows as number));
  out.perBranch = Object.fromEntries(Object.entries(meta).map(([k, m]: any) => [k, m.rows]));
  out.analyzeMs = Date.now() - t;
  t = Date.now();
  try {
    await prog.compile({ cache: NO_CACHE });
    out.ok = true;
  } catch (e) {
    out.ok = false;
    out.err = String((e as Error)?.message ?? e).slice(0, 400);
  }
  out.compileMs = Date.now() - t;
  console.log(`##JSON##${JSON.stringify(out)}`);
};

/** [A] the REAL three-slice chain, `max_proofs_verified = 1`. */
async function chainTrial() {
  const budget = Number(process.env.CEILING_BUDGET ?? '50000');
  const u = unifiedDag(rootAirDag());
  const plan = planRootAirChain(u, { usableRows: budget, chunkSize: CHUNK, maxSlices: 3 });
  await attempt(makeRootAirChain(u, plan, {}).prog, { arm: 'mpv1', budget });
}

/** [B] two REAL slice bodies, one of them verifying TWO previous proofs. */
async function mpv2Trial() {
  const budget = Number(process.env.CEILING_BUDGET ?? '40000');
  const u = unifiedDag(rootAirDag());
  const plan = planRootAirChain(u, { usableRows: budget, chunkSize: CHUNK, maxSlices: 2 });
  await attempt(makeMpv2Program(u, plan), { arm: 'mpv2', budget });
}

/**
 * [C] leg 17's OWN shape: one side-loaded slice, alone in its program.
 *
 * ⚑ IT MEASURES THE WIDEST SIDE-LOADED SLICE AND NOT A CONVENIENT ONE. The
 * planner's model says every slice at a given budget is within ~40 rows of every
 * other; EMITTED they spread 48,181 to 51,136 at a budget of 50,000. A ceiling is
 * about the widest branch, so the trial analyses every slice that takes a
 * predecessor and compiles the one that came out largest — analysing six bodies
 * costs about as much as one compile and picking the wrong branch would put the
 * recorded envelope 3,000 rows below what leg 17 actually compiles.
 */
async function sideloadTrial() {
  const budget = Number(process.env.CEILING_BUDGET ?? '50000');
  const u = unifiedDag(rootAirDag());
  const plan = planRootAirChain(u, { usableRows: budget, chunkSize: CHUNK });
  // The predecessor's feature flags, from the predecessor's own program — which
  // is exactly how leg 17 gets them across a process boundary.
  const prevFlags = await FeatureFlags.fromZkProgram(makeSliceProgram(u, plan, 0, {}).prog);
  let widest = 1;
  let widestRows = -1;
  const perSlice: Record<number, number> = {};
  for (let si = 1; si < plan.slices.length; si++) {
    // ⚑ A fresh child would be needed to BUILD each of these as a program (one
    // side-loaded class per process), so the row count is taken from the body
    // through the chain's own functions instead, in this process.
    const rows = await sliceBodyRows(u, plan, si);
    perSlice[si] = rows;
    if (rows > widestRows) {
      widestRows = rows;
      widest = si;
    }
  }
  // ⚑ The pinned hash is ONE constant and its VALUE cannot change the circuit's
  // size, so a placeholder here measures the same branch the chain compiles.
  const { prog } = makeSliceProgram(u, plan, widest, { prevVkHash: 1n, prevFlags });
  await attempt(prog, { arm: 'sideload', budget, widest, perSlice });
}

/** The two-point SHAPE control: same arm, same sibling, MORE rows, and the
 *  bigger one compiles. */
async function shapeTrial() {
  const coarse = Number(process.env.CEILING_COARSE ?? '1200');
  const fine = Number(process.env.CEILING_FINE ?? '0');
  await attempt(makeShapeProgram(coarse, fine), { arm: 'shape', coarse, fine });
}

function child(env: Record<string, string>): Promise<any> {
  return new Promise((resolve) => {
    execFile(
      process.execPath,
      ['--max-old-space-size=16384', process.argv[1]],
      {
        encoding: 'utf8',
        maxBuffer: 1 << 26,
        env: { ...process.env, ...env },
      },
      (err, stdout) => {
        const line = String(stdout).split('\n').find((l) => l.startsWith('##JSON##'));
        if (line) return resolve(JSON.parse(line.slice(8)));
        resolve({
          crashed: true,
          ok: false,
          err: String(err?.message ?? 'no result line').slice(0, 300),
        });
      },
    );
  });
}

// ===========================================================================
// The parallel narrowing.
// ===========================================================================

type Trial = { ok: boolean; crashed?: boolean; err?: string; rows: number; fine: number; [k: string]: any };

/**
 * Narrow several shapes AT ONCE.
 *
 * ⚑ WHY CONCURRENT ACROSS ARMS AND NOT ONE AFTER ANOTHER. A wave costs what its
 * SLOWEST trial costs, and a failing compile is slower than a passing one (it
 * builds a 2^17 domain before it dies) — measured, 5.9 min against 1.9. Four
 * shapes narrowed one after the other is four times the waves for the same wall
 * clock per wave. Interleaved, every shape advances in every wave.
 *
 * ⚑ AND IT CHECKS MONOTONICITY PER SHAPE AND SAYS SO. If a point above a failing
 * point compiles, "the largest budget that compiles" is not a ceiling and
 * reporting one number would be a fiction; the leg fails instead of picking a
 * side.
 */
type Bracket = {
  label: string;
  lo: number;
  hi: number;
  run: (x: number, rows?: boolean) => Promise<Trial>;
  rounds: number;
};

async function validateBracket(b: Bracket, widen: number) {
  // `lo` must COMPILE and `hi` must FAIL. A seeded bracket that is wrong is
  // widened rather than believed — a search that assumes its own answer is not
  // a measurement.
  for (let i = 0; i < 4; i++) {
    const [rLo, rHi] = await Promise.all([b.run(b.lo), b.run(b.hi)]);
    if (rLo.crashed) fail(`${b.label}: the trial at ${fmt(b.lo)} CRASHED — ${rLo.err}`);
    if (rHi.crashed) fail(`${b.label}: the trial at ${fmt(b.hi)} CRASHED — ${rHi.err}`);
    if (!rHi.ok && !CHUNK_FAILURE.test(rHi.err ?? ''))
      fail(`${b.label}: the failure at ${fmt(b.hi)} is not the chunking wall — ${rHi.err}`);
    if (rLo.ok && !rHi.ok) {
      console.log(`      ${b.label}: bracket [${fmt(b.lo)}+, ${fmt(b.hi)}-] confirmed`);
      return;
    }
    if (!rLo.ok) {
      console.log(`      ${b.label}: ${fmt(b.lo)} does NOT compile — widening down`);
      b.hi = b.lo;
      b.lo = Math.max(0, b.lo - widen);
    } else {
      console.log(`      ${b.label}: ${fmt(b.hi)} COMPILES — widening up`);
      b.lo = b.hi;
      b.hi = b.hi + widen;
    }
  }
  fail(`${b.label}: no bracket found after four widenings — the shape does not cross where expected`);
}

async function narrowAll(brackets: Bracket[], perArm: number) {
  let round = 0;
  for (;;) {
    const work: { b: Bracket; pts: number[] }[] = [];
    for (const b of brackets) {
      if (b.hi - b.lo <= TOL) continue;
      const step = (b.hi - b.lo) / (perArm + 1);
      const pts = [...new Set(Array.from({ length: perArm }, (_, i) => Math.round(b.lo + step * (i + 1))))].filter(
        (p) => p > b.lo && p < b.hi,
      );
      if (pts.length) work.push({ b, pts });
    }
    if (!work.length) return;
    round++;
    const t = Date.now();
    const results = await Promise.all(work.map((w) => Promise.all(w.pts.map((p) => w.b.run(p)))));
    for (let k = 0; k < work.length; k++) {
      const { b, pts } = work[k];
      const rs = results[k];
      for (let i = 0; i < pts.length; i++) {
        if (rs[i].crashed) fail(`${b.label}: the trial at ${fmt(pts[i])} CRASHED — ${rs[i].err}`);
        if (!rs[i].ok && !CHUNK_FAILURE.test(rs[i].err ?? ''))
          fail(`${b.label}: the failure at ${fmt(pts[i])} is not the chunking wall — ${rs[i].err}`);
      }
      const lastOk = Math.max(b.lo, ...pts.filter((_, i) => rs[i].ok));
      const firstFail = Math.min(b.hi, ...pts.filter((_, i) => !rs[i].ok));
      if (lastOk > firstFail)
        fail(
          `${b.label}: NOT MONOTONE — ${fmt(lastOk)} compiles and ${fmt(firstFail)} does not, so ` +
            '"the largest that compiles" is not a ceiling and one number would be a fiction',
        );
      b.lo = lastOk;
      b.hi = firstFail;
      b.rounds++;
      console.log(
        `      round ${round} ${b.label.padEnd(22)} ${pts.map((p, i) => `${fmt(p)}${rs[i].ok ? '+' : '-'}`).join('  ')}` +
          `  ⇒ [${fmt(b.lo)}, ${fmt(b.hi)}]`,
      );
    }
    console.log(`      round ${round} took ${secs(t)} over ${work.reduce((a, w) => a + w.pts.length, 0)} trials`);
  }
}

// ===========================================================================
// The arms, and the two ways to run them.
// ===========================================================================

const ARMS: { arm: Arm; label: string; why: string; seed: [number, number] }[] = [
  {
    arm: 'mpv1',
    label: 'the 3-slice chain',
    why: "§3.24's object: three real slices, one previous proof each",
    seed: [50_000, 57_532],
  },
  {
    arm: 'mpv2',
    label: 'two real slices, mpv 2',
    why: "the aggregation-tree shape §3.23's headline 519 is priced against",
    seed: [38_000, 46_000],
  },
  {
    arm: 'sideload',
    label: 'one side-loaded slice',
    why: "leg 17's own shape: one branch per program, key at runtime",
    seed: [50_000, 57_000],
  },
];

const armRun = (arm: Arm) => (budget: number) => child({ CEILING_MODE: arm, CEILING_BUDGET: String(budget) });

/** The two-point control that says the ceiling is not a row count. */
const SHAPE_FAIL = { coarse: 1200, fine: 0 };
const SHAPE_OK = { coarse: 600, fine: 34_331 };
const shapeRun = (p: { coarse: number; fine: number }) =>
  child({ CEILING_MODE: 'shape', CEILING_COARSE: String(p.coarse), CEILING_FINE: String(p.fine) });

async function shapeControl() {
  console.log('\n[S] the SHAPE control — the ceiling is not a row count, and here are two rows');
  const t = Date.now();
  const [bigger, smaller] = await Promise.all([shapeRun(SHAPE_OK), shapeRun(SHAPE_FAIL)]);
  if (bigger.crashed || smaller.crashed) fail(`the shape control CRASHED — ${bigger.err ?? smaller.err}`);
  console.log(
    `    same program shape (one SelfProof branch + a small sibling), same inputs:\n` +
      `      ${fmt(smaller.rows).padStart(6)} rows, extension-arithmetic mix   ${smaller.ok ? 'COMPILES' : 'FAILS'}\n` +
      `      ${fmt(bigger.rows).padStart(6)} rows, generic-multiply mix        ${bigger.ok ? 'COMPILES' : 'FAILS'}   (${secs(t)})`,
  );
  if (smaller.ok || !bigger.ok)
    fail(
      'the shape control no longer shows a BIGGER circuit compiling where a smaller one does not ' +
        `(${fmt(smaller.rows)} ${smaller.ok ? 'compiles' : 'fails'}, ${fmt(bigger.rows)} ` +
        `${bigger.ok ? 'compiles' : 'fails'}) — if that is genuinely gone, the ceiling may be a row ` +
        'count after all and §4.1\'s `usableRows` can be rehabilitated; until then it cannot',
    );
  if (!CHUNK_FAILURE.test(smaller.err ?? ''))
    fail(`the shape control's failure is not the chunking wall — ${smaller.err}`);
  ok(
    `a ${fmt(bigger.rows)}-row branch COMPILES where a ${fmt(smaller.rows)}-row branch of the same ` +
      `shape FAILS — the crossing is a function of the GATE MIX, not of the row count, so a ` +
      `per-\`max_proofs_verified\` "usable rows" constant cannot exist`,
  );
  return { bigger, smaller };
}

async function recheck() {
  console.log('[1] the RECORDED crossings, re-checked — three shapes, six compiles');
  console.log(
    '    ⚑ this run does NOT re-search. `CEILING_FULL=1` narrows from scratch; an ordinary run\n' +
      '      re-runs exactly the recorded pair for each shape, which is what can go red.',
  );
  for (const { arm } of ARMS) {
    const r = (RECORDED as any)[arm];
    if (!r || !r.okBudget || !r.okRows)
      fail(
        `nothing is recorded for ${arm} — run \`CEILING_FULL=1 npm run root-air-ceiling\`. A ceiling ` +
          'nobody recorded is a ceiling nobody is holding to anything.',
      );
  }
  const twoSided = ARMS.filter(({ arm }) => (RECORDED as any)[arm].failBudget > 0).length;
  console.log(
    `    ${twoSided} of ${ARMS.length} shapes are NARROWED and get both halves; the rest are ` +
      `ENVELOPES and get the compiling half only — said out loud because a one-sided check cannot\n` +
      `    notice a ceiling moving UP.`,
  );
  const t = Date.now();
  const trials = await Promise.all(
    ARMS.flatMap(({ arm }) => {
      const r = (RECORDED as any)[arm];
      return [armRun(arm)(r.okBudget), r.failBudget ? armRun(arm)(r.failBudget) : Promise.resolve(null)];
    }),
  );
  console.log(`    ${ARMS.length + twoSided} compiles in ${secs(t)}`);
  const seen: Record<string, { okRows: number; failRows: number }> = {};
  console.log(
    `\n    ${'shape'.padEnd(24)}${'ceiling'.padStart(10)}${'first fail'.padStart(12)}` +
      `${'implied overhead'.padStart(18)}`,
  );
  ARMS.forEach(({ arm, label }, k) => {
    const r = (RECORDED as any)[arm];
    const rOk = trials[2 * k]!;
    const rFail = trials[2 * k + 1];
    if (rOk.crashed) fail(`${label}: the recorded ceiling trial CRASHED — ${rOk.err}`);
    if (rOk.rows !== r.okRows)
      fail(`${label}: the recorded ceiling is ${fmt(r.okRows)} rows and this run measures ${fmt(rOk.rows)}`);
    if (!rOk.ok) fail(`${label}: the RECORDED CEILING of ${fmt(rOk.rows)} rows NO LONGER COMPILES — ${rOk.err}`);
    if (rFail) {
      if (rFail.crashed) fail(`${label}: the recorded failure trial CRASHED — ${rFail.err}`);
      if (rFail.rows !== r.failRows)
        fail(`${label}: the recorded first failure is ${fmt(r.failRows)} rows and this run measures ${fmt(rFail.rows)}`);
      if (rFail.ok)
        fail(
          `${label}: the RECORDED FIRST FAILURE of ${fmt(rFail.rows)} rows now COMPILES — the ceiling ` +
            'has moved and every step count priced against it is wrong in the flattering direction',
        );
      if (!CHUNK_FAILURE.test(rFail.err ?? ''))
        fail(`${label}: the failure at ${fmt(rFail.rows)} rows is not the chunking wall — ${rFail.err}`);
    }
    console.log(
      `    ${label.padEnd(24)}${fmt(rOk.rows).padStart(10)}` +
        `${(rFail ? fmt(rFail.rows) : 'NOT NARROWED').padStart(12)}` +
        `${(rFail ? fmt(KIMCHI_ROWS - rOk.rows) : '>= ' + fmt(KIMCHI_ROWS - rOk.rows)).padStart(18)}`,
    );
    seen[arm] = { okRows: rOk.rows, failRows: rFail ? rFail.rows : 0 };
  });
  ok('the RECORDED ceiling still compiles, for all three shapes');
  ok(
    `the RECORDED first failure still FAILS for the ${twoSided} NARROWED shape` +
      `${twoSided === 1 ? '' : 's'}, with Pickles' \`length mismatch in Array.map2_exn: 1 <> 2\` — a ` +
      'chunked branch, not an out-of-memory abort',
  );
  return seen;
}

// ===========================================================================
// main
// ===========================================================================

async function main() {
  console.log('\n=== ROOT-AIR-CEILING — the compile ceiling, MEASURED (leg 16) ===\n');
  const T0 = Date.now();

  let seen: Record<string, { okRows: number; failRows: number }>;
  if (FULL) {
    console.log('[1] narrowing all three shapes in the SAME waves');
    const brackets: Bracket[] = ARMS.map(({ arm, label, seed }) => {
      const r = (RECORDED as any)[arm];
      const s0 = r && r.okBudget ? ([r.okBudget, r.failBudget] as [number, number]) : seed;
      return { label, lo: s0[0], hi: s0[1], run: armRun(arm), rounds: 0 };
    });
    for (const { arm, label, why } of ARMS) console.log(`      ${label.padEnd(24)} — ${why} (${arm})`);
    await Promise.all(brackets.map((b) => validateBracket(b, 6_000)));
    await narrowAll(brackets, PER_ARM);
    const finals = await Promise.all(
      brackets.map(async (b) => {
        const [okT, failT] = await Promise.all([b.run(b.lo), b.run(b.hi)]);
        return { b, okT, failT };
      }),
    );
    seen = {};
    console.log(
      `\n    ${'shape'.padEnd(24)}${'ok budget'.padStart(11)}${'ceiling'.padStart(10)}` +
        `${'fail budget'.padStart(13)}${'first fail'.padStart(12)}`,
    );
    ARMS.forEach(({ arm }, k) => {
      const { b, okT, failT } = finals[k];
      seen[arm] = { okRows: okT.rows, failRows: failT.rows };
      console.log(
        `    ${b.label.padEnd(24)}${fmt(b.lo).padStart(11)}${fmt(okT.rows).padStart(10)}` +
          `${fmt(b.hi).padStart(13)}${fmt(failT.rows).padStart(12)}`,
      );
    });
    ok(`all three crossings narrowed to under ${TOL} rows of budget, on REAL slice bodies`);
    console.log(
      `##RECORD##${JSON.stringify(
        Object.fromEntries(
          ARMS.map(({ arm }, k) => [
            arm,
            {
              okBudget: finals[k].b.lo,
              failBudget: finals[k].b.hi,
              okRows: finals[k].okT.rows,
              failRows: finals[k].failT.rows,
            },
          ]),
        ),
      )}`,
    );
  } else {
    seen = await recheck();
  }

  await shapeControl();

  // ── `PartitionSchedule` must be carrying these numbers ──────────────────
  console.log('\n[2] what the scheduler is packing against');
  // ⚑ The NARROWED number is pinned exactly. The two BOUNDS are pinned as
  // bounds: a run that finds the shape compiling WIDER than recorded has moved
  // the envelope and must say so, and a run that finds it failing INSIDE the
  // recorded envelope is a red.
  if (MEASURED_CEILING.mpv1 !== seen.mpv1.okRows || MEASURED_CEILING.mpv1Fails !== seen.mpv1.failRows)
    fail(
      `\`MEASURED_CEILING.mpv1\` is ${fmt(MEASURED_CEILING.mpv1)}/${fmt(MEASURED_CEILING.mpv1Fails)} ` +
        `and this run measures ${fmt(seen.mpv1.okRows)}/${fmt(seen.mpv1.failRows)} — the scheduler ` +
        'is packing steps against a budget nothing checks',
    );
  for (const [name, bound, measured] of [
    ['mpv2AtLeast', MEASURED_CEILING.mpv2AtLeast, seen.mpv2.okRows],
    ['sideloadAtLeast', MEASURED_CEILING.sideloadAtLeast, seen.sideload.okRows],
  ] as [string, number, number][])
    if (measured < bound)
      fail(
        `\`MEASURED_CEILING.${name}\` claims ${fmt(bound)} rows of this shape compile and this run ` +
          `only gets ${fmt(measured)} — the recorded envelope is not real`,
      );
  ok(
    '`PartitionSchedule.MEASURED_CEILING` carries the narrowed mpv = 1 crossing exactly, and the ' +
      'two unnarrowed shapes are inside the envelopes it records for them',
  );
  const arith1 = KIMCHI_ROWS - 4 - 57_532;
  console.log(
    `\n    ⚑ §4.1 put the mpv = 1 overhead at ${fmt(arith1)}; on the real object it is ` +
      `${fmt(KIMCHI_ROWS - seen.mpv1.okRows)} — ${((KIMCHI_ROWS - seen.mpv1.okRows) / arith1).toFixed(2)}x.\n` +
      `      Its mpv = 2 row of the table is NOT narrowed here: two real slice bodies, one of them\n` +
      `      verifying TWO previous proofs, are only shown to compile at ${fmt(seen.mpv2.okRows)} rows — a\n` +
      `      LOWER bound, so an UPPER bound on the step count. A SIDE-LOADED branch alone in its\n` +
      `      program is shown to compile at ${fmt(seen.sideload.okRows)}. Neither is a ceiling and neither is\n` +
      `      quoted as one.`,
  );

  console.log(`\n=== ROOT-AIR-CEILING PASS === ${checks} checks, ${secs(T0)}\n`);
}

const TRIALS: Record<string, () => Promise<void>> = {
  chain: chainTrial,
  mpv2: mpv2Trial,
  sideload: sideloadTrial,
  shape: shapeTrial,
};
const phase = TRIALS[MODE] ? TRIALS[MODE]() : main();
phase.catch((e) => {
  console.error(e);
  process.exit(1);
});

import { execFileSync } from 'node:child_process';
import { Cache, Field, Provable } from 'o1js';
import { BbExt } from '../src/FriQueryStep.js';
import {
  Lcg,
  liveness,
  rootAirDag,
  unifiedDag,
  UnifiedDag,
} from '../src/RootAirDag.js';
import {
  ChainPlan,
  chainSideOf,
  chunkCount,
  dagDigestOfChunkDigests,
  digestOfLanes,
  makeRootAirChain,
  planRootAirChain,
  stepBoundary,
  terminalSeal,
} from '../src/RootAirChain.js';
import { PICKLES_OVERHEAD, usableRows } from '../src/PartitionSchedule.js';

// ---------------------------------------------------------------------------
// LEG 15 — THE ROOT'S OWN AIR, PROVED AS A CHAIN.
//
// Leg 13 emits the root's 1,093 constraints and measures them at 275,143 Kimchi
// rows. That is 4.8x the 65,536-row Pickles step domain, so dregg's root
// constraint system HAS NO ONE-STEP VERIFIER — the same situation §3.20
// constructed deliberately with three queries, arrived at here by the object
// itself rather than by choosing a geometry.
//
// ⚑ AND ONE THING IS STRUCTURALLY DIFFERENT FROM §3.20/§3.21, WHICH IS WHY THIS
// IS A SEPARATE LEG AND NOT A PARAMETER. Their chains are ONE circuit invoked N
// times, because 19 query walks are the same shape. The AIR's slices are
// DIFFERENT programs — different nodes, different operands — so a uniform
// circuit would need an in-circuit multiplexer over the live set, priced in leg
// 14b at ~27x. What makes a verification key per slice acceptable here and not
// there: the AIR is a FIXED program, so its slice VKs are protocol CONSTANTS
// emitted once, not a per-proof cost.
//
// ⚑ THE PROCESS WALL IS WHAT CAPS THIS RUN AND IT IS MEASURED, NOT GUESSED.
// §3.20: a node process that has compiled FOUR step circuits HANGS at the first
// `prove` (kimchi's wasm heap is 32-bit; the worker dies and the promise never
// settles). So this process proves THREE slices — the largest chain one process
// holds — and the unbound control runs in a CHILD process with its own three.
//
// ⚑ AND THE CONTROL BUILDS ITS OWN PREDECESSOR. §3.21 paid for this: a proof
// made by the BOUND program does not verify under the UNBOUND program's VK, so
// handing the bound proof across makes the control refuse everything, which is
// exactly the shape of a control that appears to confirm the binding while
// testing nothing.
// ---------------------------------------------------------------------------

const PHASE = process.env.AIR_CHAIN_PHASE ?? '';
const NO_CACHE = Cache.None; //  o1js's default prover-key cache aborts with `rust_oom`
const CHUNK_SIZE = 64;
const MAX_SLICES = 3;
const KAT_SEED = 0x4169_7243_6861_696en;

/**
 * ⚑ THE PER-BRANCH CEILING, MEASURED HERE AND LOWER THAN §4.1's ARITHMETIC.
 *
 * §4.1 computes a `max_proofs_verified = 1` budget of 65,536 − 3 zk_rows − 1
 * public input − ~8,000 recursive-verifier overhead = 57,532 usable. At that
 * budget this program's slices measure 56,772 / 55,715 / 57,430 rows by
 * `analyzeMethods` — all under the domain — and `compile()` FAILS:
 *
 *     length mismatch in Array.map2_exn: 1 <> 2
 *
 * That is Pickles refusing a CHUNKED branch. `analyzeMethods` reports the
 * method body's rows; the branch Pickles actually builds carries the recursive
 * verifier on top, and one branch crosses 2^16 while another does not, so the
 * two branches disagree on `numChunks` and `Array.map2_exn` is where that shows
 * up. Measured: 50,000 compiles (50,398 / 48,179 rows), 57,532 does not.
 *
 * ⚑ SO §4.1's ~8,000 IS TOO SMALL FOR THIS SHAPE, and the honest budget is the
 * one that compiles. It is used here rather than the arithmetic one, and the
 * gap is reported as a finding rather than absorbed.
 */
const USABLE_MEASURED = 50_000;
const USABLE_ARITHMETIC_4_1 = 57_532;

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

/** ⚑ EVERY CAUGHT ERROR MUST BE A CONSTRAINT FAILURE. A `TypeError` from a
 *  mis-shaped argument is indistinguishable from a real refusal inside a bare
 *  `catch {}` — §3.21 names this as what would make the section "a green that
 *  measures the harness". */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|Bool\.assertTrue/.test(m);
}

// ===========================================================================
// The instance the chain runs on.
// ===========================================================================

function instance(u: UnifiedDag) {
  const g = new Lcg(KAT_SEED);
  const alpha = g.nextExt();
  const base = Array.from({ length: u.nBaseCols }, () => g.nextExt());
  const ext = Array.from({ length: u.nExtCols }, () => g.nextExt());
  return { alpha, base, ext };
}

const toBb = (l: bigint[]) => BbExt.from(l);

/** The private arguments of slice `si`, from the out-of-circuit twin. */
function argsOf(plan: ChainPlan, side: any, si: number, alpha: bigint[]) {
  const s = plan.slices[si];
  const ps = side.perSlice[si];
  const liveIn = s.liveIn.length ? ps.liveIn.map(toBb) : [BbExt.zero()];
  const readLanes = ps.readLanes.length
    ? ps.readLanes.map((x: bigint) => Field(x))
    : [Field(0)];
  const others: Field[] = [];
  for (let c = 0; c < plan.nColChunks; c++)
    if (!s.readsChunks.includes(c)) others.push(digestOfLanes(side.chunks[c].map((x: bigint) => Field(x))));
  return {
    alpha: toBb(alpha),
    accIn: toBb(side.accs[si]),
    liveIn,
    readLanes,
    others: others.length ? others : [Field(0)],
  };
}

/** The boundary entering slice `si`, computed OUT OF CIRCUIT by the same
 *  functions the circuit calls. */
function boundaryIn(plan: ChainPlan, side: any, si: number, alpha: bigint[]): Field {
  const dag = dagDigestOfChunkDigests(
    side.chunks.map((c: bigint[]) => digestOfLanes(c.map((x) => Field(x)))),
  );
  if (si === 0) return stepBoundary(dag, Field(0), 0);
  const s = plan.slices[si];
  const live = digestOfLanes([
    ...side.perSlice[si - 1].liveOut.flatMap((v: bigint[]) => v.map((x) => Field(x))),
    ...side.accs[si].map((x: bigint) => Field(x)),
    ...alpha.map((x) => Field(x)),
  ]);
  void s;
  return stepBoundary(dag, live, si);
}

function terminalOf(plan: ChainPlan, side: any): Field {
  const dag = dagDigestOfChunkDigests(
    side.chunks.map((c: bigint[]) => digestOfLanes(c.map((x) => Field(x)))),
  );
  const last = plan.slices.length - 1;
  return terminalSeal(
    dag,
    digestOfLanes([
      ...side.accs[last + 1].map((x: bigint) => Field(x)),
      ...side.perSlice[last].liveOut.flatMap((v: bigint[]) => v.map((x) => Field(x))),
    ]),
    plan.slices.length,
  );
}

// ===========================================================================
// The CONTROL phase — a child process, so its three circuits do not join this
// process's three.
// ===========================================================================

async function controlPhase() {
  const u = unifiedDag(rootAirDag());
  const plan = planRootAirChain(u, {
    usableRows: USABLE_MEASURED,
    chunkSize: CHUNK_SIZE,
    maxSlices: MAX_SLICES,
  });
  const { alpha, base, ext } = instance(u);
  const side = chainSideOf(u, plan, base, ext, alpha);
  const C = makeRootAirChain(u, plan, { bindCarry: false });
  await C.prog.compile({ cache: NO_CACHE });

  const a0 = argsOf(plan, side, 0, alpha);
  const p0 = await (C.prog as any).slice0(
    boundaryIn(plan, side, 0, alpha),
    a0.alpha,
    a0.accIn,
    a0.liveIn,
    a0.readLanes,
    a0.others,
  );
  const a1 = argsOf(plan, side, 1, alpha);
  const results: Record<string, boolean> = {};

  // (a) a public input with NO relation to its predecessor.
  try {
    await (C.prog as any).slice1(
      Field(0x1234),
      p0.proof,
      a1.alpha,
      a1.accIn,
      a1.liveIn,
      a1.readLanes,
      a1.others,
    );
    results.unrelatedInput = true;
  } catch {
    results.unrelatedInput = false;
  }

  // (b) a chunk digest slice 1 NEVER READS, bent.
  const bent = a1.others.slice();
  bent[0] = bent[0].add(Field(1));
  try {
    await (C.prog as any).slice1(
      boundaryIn(plan, side, 1, alpha),
      p0.proof,
      a1.alpha,
      a1.accIn,
      a1.liveIn,
      a1.readLanes,
      bent,
    );
    results.unreadDigestBent = true;
  } catch {
    results.unreadDigestBent = false;
  }

  console.log(`##JSON##${JSON.stringify(results)}`);
}

// ===========================================================================
// The main leg.
// ===========================================================================

async function main() {
  console.log('\n=== ROOT-AIR-CHAIN — the root AIR, proved as a chain (leg 15) ===\n');

  const d = rootAirDag();
  const u = unifiedDag(d);
  const lv = liveness(u);
  const USABLE = USABLE_MEASURED;

  // -----------------------------------------------------------------------
  // [1] The object has no one-step verifier, and the full plan.
  // -----------------------------------------------------------------------
  console.log('[1] the root AIR does not fit in a Pickles step');
  const full = planRootAirChain(u, { usableRows: USABLE, chunkSize: CHUNK_SIZE });
  console.log(
    `    ${fmt(u.nodes.length)} DAG nodes, ${fmt(u.roots.length)} constraints, ` +
      `275,143 EMITTED rows = 4.20x the 65,536-row step domain`,
  );
  console.log(
    `    the FULL chain is ${full.slices.length} slices: work ${fmt(full.totalWork)} + carry ` +
      `${fmt(full.totalCarry)} (${((full.totalCarry / (full.totalWork + full.totalCarry)) * 100).toFixed(1)}%)`,
  );
  console.log(`    cut width across the whole DAG: at most ${lv.maxWidth} live values`);
  console.log(
    `    ⚑ the per-branch budget is the MEASURED ${fmt(USABLE_MEASURED)}, not §4.1's arithmetic ` +
      `${fmt(USABLE_ARITHMETIC_4_1)}:\n      at ${fmt(USABLE_ARITHMETIC_4_1)} the slices measure ` +
      `56,772 / 55,715 / 57,430 rows — all under the 65,536 domain — and \`compile()\` fails with\n` +
      `      "length mismatch in Array.map2_exn: 1 <> 2", Pickles refusing a CHUNKED branch.`,
  );
  ok(`the root's constraint system needs ${full.slices.length} chained steps — it has no one-step verifier`);

  // -----------------------------------------------------------------------
  // [2] The largest chain ONE PROCESS holds.
  // -----------------------------------------------------------------------
  console.log(`\n[2] the largest chain one process holds — ${MAX_SLICES} slices`);
  const plan = planRootAirChain(u, {
    usableRows: USABLE,
    chunkSize: CHUNK_SIZE,
    maxSlices: MAX_SLICES,
  });
  const covered = plan.slices[plan.slices.length - 1].to;
  const coveredConstraints = plan.slices[plan.slices.length - 1].foldTo;
  for (const s of plan.slices)
    console.log(
      `    slice ${s.index}: nodes [${fmt(s.from)},${fmt(s.to)})  constraints ` +
        `[${fmt(s.foldFrom)},${fmt(s.foldTo)})  liveIn ${s.liveIn.length}  liveOut ` +
        `${s.liveOut.length}  chunks ${s.readsChunks.length}/${plan.nColChunks}  ` +
        `work ${fmt(s.workRows)} + carry ${fmt(s.carryRows)}`,
    );
  console.log(
    `    ⇒ ${fmt(covered)} of ${fmt(u.nodes.length)} nodes ` +
      `(${((covered / u.nodes.length) * 100).toFixed(1)}%), ${fmt(coveredConstraints)} of ` +
      `${fmt(u.roots.length)} constraints (${((coveredConstraints / u.roots.length) * 100).toFixed(1)}%)`,
  );
  const tables = u.tableSpans.filter((t) => t.to <= covered).map((t) => t.name);
  console.log(`    whole tables covered: ${tables.join(', ') || '(none)'}`);
  if (plan.slices.length !== MAX_SLICES)
    fail(`the capped plan is ${plan.slices.length} slices, not ${MAX_SLICES}`);

  // ⚑ A FOUR-SLICE PLAN MUST BE REFUSED, not silently hung.
  try {
    makeRootAirChain(u, planRootAirChain(u, { usableRows: USABLE, chunkSize: CHUNK_SIZE }), {});
    fail('a 6-slice chain built in one process — the wall is not enforced and this would HANG');
  } catch (e) {
    if (!/FOUR hanging|compiled circuits/.test(String((e as Error).message)))
      fail(`the refusal is not the wall's: ${String((e as Error).message)}`);
    ok('a 6-slice chain is REFUSED at build time with the measured wall, not left to hang');
  }

  // -----------------------------------------------------------------------
  // [3] The instance, and the out-of-circuit twin.
  // -----------------------------------------------------------------------
  console.log('\n[3] the instance');
  const { alpha, base, ext } = instance(u);
  const side = chainSideOf(u, plan, base, ext, alpha);
  const accFinal = side.accs[plan.slices.length];
  if (accFinal.every((x) => x === 0n))
    fail('the accumulator after the chain is ZERO — the instance cannot discriminate');
  // ⚑ Anti-vacuity: the per-slice accumulators must MOVE, or a chain that
  // dropped a slice's folds would be indistinguishable from one that did them.
  const accStrs = side.accs.map((a: bigint[]) => a.join(','));
  if (new Set(accStrs).size !== accStrs.length)
    fail('two slice boundaries carry the SAME accumulator — a dropped fold would be invisible');
  ok(
    `the accumulator is non-zero and moves at every boundary — ${plan.slices.length + 1} ` +
      `pairwise-distinct values`,
  );

  // -----------------------------------------------------------------------
  // [4] Compile, and the emitted rows per slice.
  // -----------------------------------------------------------------------
  console.log('\n[4] the chain, compiled');
  const CH = makeRootAirChain(u, plan, {});
  let t = Date.now();
  const rows = (await (CH.prog as any).analyzeMethods()) as any;
  const rowList = plan.slices.map((s, i) => rows[`slice${i}`].rows as number);
  console.log(`    analyzeMethods in ${secs(t)}`);
  rowList.forEach((r, i) =>
    console.log(
      `    slice ${i}: ${fmt(r).padStart(8)} EMITTED rows  ` +
        `(planned ${fmt(plan.slices[i].workRows + plan.slices[i].carryRows)}, ` +
        `${(((r - plan.slices[i].workRows - plan.slices[i].carryRows) / (plan.slices[i].workRows + plan.slices[i].carryRows)) * 100).toFixed(1)}%)  ` +
        `${((r / 65536) * 100).toFixed(1)}% of the domain`,
    ),
  );
  for (const r of rowList)
    if (r > 65536 - 3 - 1) fail(`a slice is ${fmt(r)} rows — past the Kimchi step domain`);
  ok(
    `every slice fits: max ${fmt(Math.max(...rowList))} rows, ` +
      `${((Math.max(...rowList) / 65536) * 100).toFixed(1)}% of the domain`,
  );
  t = Date.now();
  await CH.prog.compile({ cache: NO_CACHE });
  console.log(`    compiled ${plan.slices.length} circuits in ${secs(t)}`);

  // -----------------------------------------------------------------------
  // [5] PROVE.
  // -----------------------------------------------------------------------
  console.log('\n[5] the chain, PROVED');
  const proofs: any[] = [];
  for (let si = 0; si < plan.slices.length; si++) {
    const a = argsOf(plan, side, si, alpha);
    const bIn = boundaryIn(plan, side, si, alpha);
    t = Date.now();
    const r =
      si === 0
        ? await (CH.prog as any).slice0(bIn, a.alpha, a.accIn, a.liveIn, a.readLanes, a.others)
        : await (CH.prog as any)[`slice${si}`](
            bIn,
            proofs[si - 1],
            a.alpha,
            a.accIn,
            a.liveIn,
            a.readLanes,
            a.others,
          );
    const okv = await (CH.prog as any).verify(r.proof);
    if (!okv) fail(`slice ${si}'s proof does not verify`);
    if (r.proof.publicInput.toString() !== bIn.toString())
      fail(`slice ${si}'s publicInput is not the boundary the twin computed`);
    if (si > 0 && r.proof.publicInput.toString() !== proofs[si - 1].publicOutput.toString())
      fail(`slice ${si}'s publicInput is not its predecessor's publicOutput`);
    const want =
      si + 1 === plan.slices.length
        ? terminalOf(plan, side)
        : boundaryIn(plan, side, si + 1, alpha);
    if (r.proof.publicOutput.toString() !== want.toString())
      fail(`slice ${si}'s publicOutput is not the boundary the twin computed`);
    proofs.push(r.proof);
    console.log(`    slice ${si}: proved + verified in ${secs(t)}`);
  }
  ok(
    `${plan.slices.length} chained Pickles steps over dregg's OWN root AIR, each proved and ` +
      `verified, each step's publicInput its predecessor's publicOutput, every public field ` +
      `checked against an out-of-circuit twin`,
  );
  ok(
    `the terminal seal carries the accumulator over ${fmt(coveredConstraints)} of the root's ` +
      `1,093 constraints`,
  );

  // -----------------------------------------------------------------------
  // [6] The splices.
  // -----------------------------------------------------------------------
  console.log('\n[6] the splice is REFUSED');
  const a1 = argsOf(plan, side, 1, alpha);
  const b1 = boundaryIn(plan, side, 1, alpha);
  const refuse = async (what: string, f: () => Promise<unknown>) => {
    try {
      await f();
    } catch (e) {
      if (!isConstraintFailure(e))
        fail(`${what}: the error is not a constraint failure — ${String((e as Error)?.message ?? e).slice(0, 300)}`);
      ok(`REFUSED: ${what}`);
      return;
    }
    fail(`${what}: ACCEPTED`);
  };

  await refuse('slice 1 entering a boundary with no relation to its predecessor', () =>
    (CH.prog as any).slice1(Field(0x1234), proofs[0], a1.alpha, a1.accIn, a1.liveIn, a1.readLanes, a1.others),
  );
  await refuse('one carried LIVE value bent', () => {
    const bent = a1.liveIn.map((x: BbExt) => x);
    bent[0] = BbExt.from(
      a1.liveIn[0].toBigInts().map((v: bigint, i: number) => (i === 0 ? (v + 1n) % 2013265921n : v)),
    );
    return (CH.prog as any).slice1(b1, proofs[0], a1.alpha, a1.accIn, bent, a1.readLanes, a1.others);
  });
  await refuse('one COLUMN LANE bent in a chunk slice 1 DOES read', () => {
    const bent = a1.readLanes.slice();
    bent[0] = bent[0].add(Field(1));
    return (CH.prog as any).slice1(b1, proofs[0], a1.alpha, a1.accIn, a1.liveIn, bent, a1.others);
  });
  await refuse('a chunk DIGEST slice 1 NEVER READS, bent', () => {
    const bent = a1.others.slice();
    bent[0] = bent[0].add(Field(1));
    return (CH.prog as any).slice1(b1, proofs[0], a1.alpha, a1.accIn, a1.liveIn, a1.readLanes, bent);
  });
  await refuse('the incoming ACCUMULATOR bent', () => {
    const acc = BbExt.from(
      a1.accIn.toBigInts().map((v: bigint, i: number) => (i === 0 ? (v + 1n) % 2013265921n : v)),
    );
    return (CH.prog as any).slice1(b1, proofs[0], a1.alpha, acc, a1.liveIn, a1.readLanes, a1.others);
  });
  await refuse('slice 2 handed slice 0\'s proof — the middle slice SKIPPED', () => {
    const a2 = argsOf(plan, side, 2, alpha);
    return (CH.prog as any).slice2(
      boundaryIn(plan, side, 2, alpha),
      proofs[0],
      a2.alpha,
      a2.accIn,
      a2.liveIn,
      a2.readLanes,
      a2.others,
    );
  });

  // -----------------------------------------------------------------------
  // [7] THE CONTROL — in a child process, with its own predecessor.
  // -----------------------------------------------------------------------
  console.log('\n[7] the UNBOUND control ACCEPTS what the bound chain refused');
  console.log('    (a child process: three more compiled circuits would hit the wall here)');
  t = Date.now();
  const out = execFileSync(process.execPath, ['--max-old-space-size=16384', process.argv[1]], {
    encoding: 'utf8',
    maxBuffer: 1 << 26,
    env: { ...process.env, AIR_CHAIN_PHASE: 'control' },
    stdio: ['ignore', 'pipe', 'inherit'],
  });
  const line = out.split('\n').find((l) => l.startsWith('##JSON##'));
  if (!line) fail(`the control phase produced no result line:\n${out.slice(-2000)}`);
  const ctl = JSON.parse(line!.slice(8)) as Record<string, boolean>;
  console.log(`    control ran in ${secs(t)}`);
  if (!ctl.unrelatedInput)
    fail(
      'the UNBOUND circuit REFUSED a public input unrelated to its predecessor — the control is ' +
        'not testing the binding, and the six refusals above are consistent with "the bend broke ' +
        'the work"',
    );
  ok('UNBOUND: a public input with no relation to its predecessor is ACCEPTED');
  if (!ctl.unreadDigestBent)
    fail(
      'the UNBOUND circuit REFUSED a bend in a chunk digest it never reads — so the bound ' +
        'circuit\'s refusal of the same bend is not attributable to the digest',
    );
  ok(
    'UNBOUND: a bent digest of a chunk the slice never reads is ACCEPTED — so the bound ' +
      'refusal IS the commitment biting, not the work breaking',
  );

  // -----------------------------------------------------------------------
  // [8] Ratchet.
  // -----------------------------------------------------------------------
  console.log('\n[8] RATCHET');
  const RECORDED: [string, number, number][] = [
    ['the FULL chain, slices at the measured budget', full.slices.length, 7],
    ['the cut width across the whole DAG', lv.maxWidth, 102],
    ['nodes covered by the 3-slice chain', covered, 4798],
    ['constraints covered by the 3-slice chain', coveredConstraints, 543],
    ['slice 0, EMITTED rows', rowList[0], 50398],
    ['slice 1, EMITTED rows', rowList[1], 48181],
    ['slice 2, EMITTED rows', rowList[2], 49774],
  ];
  let drifted = 0;
  for (const [label, got, want] of RECORDED) {
    if (want === 0) {
      console.log(`    · ${label.padEnd(44)} ${fmt(got).padStart(10)} (first recording)`);
      continue;
    }
    const mark = got === want ? '✓' : '✗';
    console.log(`    ${mark} ${label.padEnd(44)} ${fmt(got).padStart(10)} (recorded ${fmt(want)})`);
    if (got !== want) drifted++;
  }
  if (drifted) fail(`${drifted} recorded figure(s) drifted`);
  ok('the recorded figures are as recorded');

  console.log(`\n=== ROOT-AIR-CHAIN PASS === ${checks} checks\n`);
}

(PHASE === 'control' ? controlPhase() : main()).catch((e) => {
  console.error(e);
  process.exit(1);
});

import { execFile, execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { Cache, FeatureFlags, Field, VerificationKey, verify } from 'o1js';
import { BbExt } from '../src/FriQueryStep.js';
import {
  DagTable,
  RealInstance,
  RealRootAir,
  bindRealInstance,
  liveness,
  rootAirDag,
  unifiedDag,
  UnifiedDag,
} from '../src/RootAirDag.js';
import {
  ChainPlan,
  chainSideOf,
  dagDigestOfChunkDigests,
  digestOfLanes,
  planRootAirChain,
  stepBoundary,
  airTerminalSeal,
} from '../src/RootAirChain.js';
import { makeSliceProgram, sliceMaxProofsVerified } from '../src/RootAirProcessChain.js';
import { MEASURED_CEILING } from '../src/PartitionSchedule.js';

// ---------------------------------------------------------------------------
// LEG 17 — THE FULL CHAIN, ONE PROCESS PER SLICE, ON DREGG'S COMMITTED ROOT
// PROOF.
//
// §3.24 proves the largest chain ONE process holds — three slices, 4,798 of
// 10,417 nodes — and names the rest: "the full AIR chain is 7 slices and one
// process carries 3 (a process-per-slice architecture is priced, not built)."
// This leg builds it, and runs it on the values `root_air_instance.rs` decodes
// out of `whole_history_proof.bin` rather than on an LCG instance.
//
// ⚑ WHAT A BOUNDARY CARRIES ACROSS A PROCESS. Three files and nothing else:
// the predecessor's proof (`toJSON` — one base64 string plus its two public
// fields), its verification key (`{data, hash}`), and its feature flags. There
// is no shared memory, no shared prover key, and no compiled tag: slice k's
// process has never seen slice k−1's program object. `RootAirProcessChain`'s
// header says why that forces side-loading and what the side-loading takes away.
//
// ⚑ THE CHAIN'S PUBLIC ALGEBRA IS §3.24's, UNFORKED. `stepBoundary(dagDigest,
// liveDigest, k)` in and out, `airTerminalSeal(dagDigest, digest(acc), nSteps)` at
// the end, and the node walk and α-fold are the SAME functions the
// single-process chain calls — `sliceCommitment` and `sliceWork`, imported, not
// re-implemented. Two implementations of what dregg's AIR means is exactly the
// thing this repo keeps finding.
//
// ⚑ AND THE CLOSING VALUE IS VERIFIER-COMPUTABLE FROM THE PROOF ALONE, which is
// the whole point of running on the real instance. Folding p3's way over the
// CONCATENATED constraint list gives
//
//     acc_unified = Σ_T acc_T · α^(R − b_T)
//
// for tables T with root spans ending at b_T out of R = 1,093 — because the fold
// is Horner and the spans are contiguous. Every acc_T is p3's OWN per-instance
// accumulator, which the root proof's own closing equality pins to its opened
// quotient. So the terminal seal is not an internal number: a Mina-side verifier
// holding dregg's proof can compute what it must be. [6] checks that identity
// against the Rust side's accumulators.
// ---------------------------------------------------------------------------

const PHASE = process.env.FULLCHAIN_PHASE ?? 'main';
const NO_CACHE = Cache.None; //  o1js's default prover-key cache aborts with `rust_oom`
const CHUNK_SIZE = 64;
const WORK = process.env.FULLCHAIN_WORKDIR ?? resolve(process.cwd(), '.fullchain');
/** ⚑ OFF BY DEFAULT. Reusing a slice's artifacts turns a chain into a claim
 *  about files on disk; the flag exists so a lane can iterate on slice 6 without
 *  re-proving 0-5, and a gate run never sets it. */
const REUSE = process.env.FULLCHAIN_REUSE === '1';
/** ⚑ THE BUDGET IS LEG 16's MEASUREMENT AND MISSING IT IS A FAILURE, NOT A
 *  SKIP. The env override exists so a lane can shake the architecture out at a
 *  budget it already trusts; a gate run never sets it, and the leg says which it
 *  used. */
/**
 * ⚑ THE BUDGET, AND WHY IT IS THIS AND NOT LEG 16's NARROWED CEILING.
 *
 * Leg 16 narrows the ceiling for the shape §3.24 built — three real slices, one
 * baked-in previous proof each — at **54,300** emitted rows in the widest branch.
 * It does NOT narrow the shape THIS leg compiles: one side-loaded branch alone in
 * its program. And leg 16's own shape control says a ceiling does not transfer
 * between shapes, so borrowing 54,300 here would be exactly the move §4.1 made.
 *
 * So the budget is one this chain has been WATCHED to compile, prove and verify
 * end to end at, and [3] asserts every slice's emitted rows landed inside the
 * envelope leg 16 records as observed-compiling for this shape. The planner's
 * model understates the emitted rows — at 50,000 the seven slices emit up to
 * 51,136, 2.3% over, because the plan prices node work at leg 13's per-operation
 * marginals and the circuit pays a little more in context — so the check is on
 * the EMITTED number and never on the budget.
 */
const BUDGET_PROVED = 50_000;
const BUDGET = Number(process.env.FULLCHAIN_BUDGET ?? BUDGET_PROVED);
if (!Number.isFinite(BUDGET) || BUDGET <= 0)
  throw new Error(
    'no per-branch budget: `MEASURED_CEILING.sideload` is unmeasured and no `FULLCHAIN_BUDGET` ' +
      'was given. Run `npm run root-air-ceiling` — this leg must NOT fall back to §4.1\'s ' +
      'arithmetic, which §3.24 measured failing to compile.',
  );

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
 *  `catch {}` — which is what would make this leg "a green that measures the
 *  harness". A side-loaded verification failure is a constraint failure too and
 *  is named here explicitly rather than caught by accident. */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read|ENOENT/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|Bool\.assertTrue|verification key|proof.*invalid|invalid.*proof/i.test(
    m,
  );
}

// ===========================================================================
// The instance: dregg's COMMITTED root proof.
// ===========================================================================

function repoRoot(): string {
  const d = process.env.DREGG_REPO_ROOT ?? resolve(process.cwd(), '../..');
  if (!existsSync(resolve(d, 'circuit-prove/src/bin/root_air_instance.rs')))
    fail(`the root-proof dumper is not under ${d} — set DREGG_REPO_ROOT`);
  return d;
}

/** ⚑ MISSING TOOLCHAIN IS A FAILURE, NOT A SKIP: there is no synthetic fallback
 *  instance here, because "the chain runs on dregg's proof" is the claim. */
function realRootAir(): RealRootAir {
  // ⚑ The DRIVER mints this once and the seven slice processes read it. Ten
  // `cargo build` invocations racing one cargo lock is how a lane blinds itself;
  // the driver clears the whole workdir on a fresh run, so a stale copy cannot
  // survive into one.
  //
  // ⚑ THE CACHE IS CHECKED BEFORE THE REPO ROOT, AND THE ORDER WAS BACKWARDS.
  // `repoRoot()` ran first, so a workdir that ALREADY HELD the dumped instance
  // still refused unless the Rust tree sat two directories up — which is exactly
  // a build-lane layout (`/tank/dregg-build/<lane>/`, sources rsynced, no
  // `circuit-prove/`). The repo root is needed to BUILD the dumper and for
  // nothing else, so it is resolved where it is used.
  const cached = resolve(WORK, 'real-root-air.json');
  if (existsSync(cached)) return JSON.parse(readFileSync(cached, 'utf8'));
  const ROOT = repoRoot();
  execFileSync('cargo', ['build', '-p', 'dregg-circuit-prove', '--release', '--bin', 'root_air_instance'], {
    cwd: ROOT,
    stdio: ['ignore', 'ignore', 'inherit'],
  });
  const out = execFileSync(resolve(ROOT, 'target/release/root_air_instance'), [], {
    encoding: 'utf8',
    maxBuffer: 1 << 26,
  });
  const real = JSON.parse(out) as RealRootAir;
  if (real.kind !== 'dregg-root-air-instance') fail(`the dumper returned ${real.kind}`);
  mkdirSync(WORK, { recursive: true });
  writeFileSync(cached, out);
  return real;
}

/** The unified column assignment, bound to the real proof's opened values in the
 *  SAME table order `unifiedDag` concatenates them. */
function realColumns(real: RealRootAir) {
  const d = rootAirDag();
  const byName: Record<string, RealInstance> = {};
  for (const i of real.instances) byName[i.table.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_')] = i;
  const pairs: [DagTable, RealInstance][] = d.tables.map((t) => {
    const i = byName[t.name] ?? byName[t.name.toLowerCase()];
    if (!i) fail(`no real instance for table ${t.name} (have ${Object.keys(byName).join(', ')})`);
    return [t, i];
  });
  const base: bigint[][] = [];
  const ext: bigint[][] = [];
  for (const [t, inst] of pairs) {
    const b = bindRealInstance(t, inst);
    base.push(...b.base);
    ext.push(...b.ext);
  }
  return { pairs, base, ext, alpha: real.challenges.alpha.map((x) => BigInt(x)) };
}

// ===========================================================================
// The context every phase rebuilds deterministically.
// ===========================================================================

type Ctx = {
  u: UnifiedDag;
  plan: ChainPlan;
  side: ReturnType<typeof chainSideOf>;
  alpha: bigint[];
  real: RealRootAir;
  pairs: [DagTable, RealInstance][];
};

function context(): Ctx {
  const u = unifiedDag(rootAirDag());
  const plan = planRootAirChain(u, { usableRows: BUDGET, chunkSize: CHUNK_SIZE });
  const real = realRootAir();
  const { pairs, base, ext, alpha } = realColumns(real);
  const side = chainSideOf(u, plan, base, ext, alpha);
  return { u, plan, side, alpha, real, pairs };
}

const toBb = (l: bigint[]) => BbExt.from(l);

function argsOf(plan: ChainPlan, side: any, si: number, alpha: bigint[]) {
  const s = plan.slices[si];
  const ps = side.perSlice[si];
  const liveIn = s.liveIn.length ? ps.liveIn.map(toBb) : [BbExt.zero()];
  const readLanes = ps.readLanes.length ? ps.readLanes.map((x: bigint) => Field(x)) : [Field(0)];
  const others: Field[] = [];
  for (let c = 0; c < plan.nColChunks; c++)
    if (!s.readsChunks.includes(c))
      others.push(digestOfLanes(side.chunks[c].map((x: bigint) => Field(x))));
  return {
    alpha: toBb(alpha),
    accIn: toBb(side.accs[si]),
    liveIn,
    readLanes,
    others: others.length ? others : [Field(0)],
  };
}

function dagDigestOf(side: any): Field {
  return dagDigestOfChunkDigests(
    side.chunks.map((c: bigint[]) => digestOfLanes(c.map((x) => Field(x)))),
  );
}

function boundaryIn(plan: ChainPlan, side: any, si: number, alpha: bigint[]): Field {
  const dag = dagDigestOf(side);
  if (si === 0) return stepBoundary(dag, Field(0), 0);
  return stepBoundary(
    dag,
    digestOfLanes([
      ...side.perSlice[si - 1].liveOut.flatMap((v: bigint[]) => v.map((x) => Field(x))),
      ...side.accs[si].map((x: bigint) => Field(x)),
      ...alpha.map((x) => Field(x)),
    ]),
    si,
  );
}

function terminalOf(plan: ChainPlan, side: any): Field {
  const last = plan.slices.length - 1;
  return airTerminalSeal(
    dagDigestOf(side),
    digestOfLanes([
      ...side.accs[last + 1].map((x: bigint) => Field(x)),
      ...side.perSlice[last].liveOut.flatMap((v: bigint[]) => v.map((x) => Field(x))),
    ]),
    plan.slices.length,
  );
}

// ===========================================================================
// The boundary on disk — the ONLY thing that crosses a process.
// ===========================================================================

const vkPath = (si: number, tag = '') => resolve(WORK, `vk-${si}${tag}.json`);
const flagsPath = (si: number) => resolve(WORK, `flags-${si}.json`);
const proofPath = (si: number) => resolve(WORK, `proof-${si}.json`);
const metaPath = (si: number) => resolve(WORK, `meta-${si}.json`);

const readVk = (si: number): { data: string; hash: string } => JSON.parse(readFileSync(vkPath(si), 'utf8'));
const vkObject = (v: { data: string; hash: string }) =>
  new VerificationKey({ data: v.data, hash: Field(v.hash) });

// ===========================================================================
// PHASE `slice` — compile and prove ONE slice.
// ===========================================================================

async function slicePhase() {
  const si = Number(process.env.FULLCHAIN_SLICE ?? '0');
  const { u, plan, side, alpha } = context();
  const prevVk = si === 0 ? null : readVk(si - 1);
  const prevFlags: FeatureFlags | undefined =
    si === 0 ? undefined : JSON.parse(readFileSync(flagsPath(si - 1), 'utf8'));

  const { prog, PrevProof } = makeSliceProgram(u, plan, si, {
    prevVkHash: prevVk ? BigInt(prevVk.hash) : undefined,
    prevFlags,
  });

  let t = Date.now();
  const meta = (await (prog as any).analyzeMethods()) as any;
  const rows = meta.slice.rows as number;
  const analyzeMs = Date.now() - t;
  // The flags the NEXT slice must declare for this one's proofs. Taken from the
  // gates `analyzeMethods` already produced, so it costs nothing extra.
  const myFlags = FeatureFlags.fromGates(meta.slice.gates);

  t = Date.now();
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });
  const compileMs = Date.now() - t;
  writeFileSync(vkPath(si), JSON.stringify({ data: verificationKey.data, hash: verificationKey.hash.toString() }));
  writeFileSync(flagsPath(si), JSON.stringify(myFlags));

  const a = argsOf(plan, side, si, alpha);
  const bIn = boundaryIn(plan, side, si, alpha);
  t = Date.now();
  const r =
    si === 0
      ? await (prog as any).slice(bIn, a.alpha, a.accIn, a.liveIn, a.readLanes, a.others)
      : await (prog as any).slice(
          bIn,
          await (PrevProof as any).fromJSON(JSON.parse(readFileSync(proofPath(si - 1), 'utf8'))),
          vkObject(prevVk!),
          a.alpha,
          a.accIn,
          a.liveIn,
          a.readLanes,
          a.others,
        );
  const proveMs = Date.now() - t;
  const verified = await verify(r.proof, verificationKey);
  writeFileSync(proofPath(si), JSON.stringify(r.proof.toJSON()));
  const out = {
    si,
    rows,
    analyzeMs,
    compileMs,
    proveMs,
    verified,
    vkHash: verificationKey.hash.toString(),
    pinnedPrevVkHash: prevVk?.hash ?? null,
    publicInput: r.proof.publicInput.toString(),
    publicOutput: r.proof.publicOutput.toString(),
    proofBytes: JSON.stringify(r.proof.toJSON()).length,
    maxProofsVerified: r.proof.maxProofsVerified,
  };
  writeFileSync(metaPath(si), JSON.stringify(out));
  console.log(`##JSON##${JSON.stringify(out)}`);
}

// ===========================================================================
// PHASE `splice` — the bends, in a process that has only ever compiled slice
// `si`, against a predecessor proof that came out of a DIFFERENT process.
// ===========================================================================

async function splicePhase() {
  const si = Number(process.env.FULLCHAIN_SLICE ?? '0');
  const foreign = Number(process.env.FULLCHAIN_FOREIGN ?? String(si - 2));
  const { u, plan, side, alpha } = context();
  const prevVk = readVk(si - 1);
  const prevFlags: FeatureFlags = JSON.parse(readFileSync(flagsPath(si - 1), 'utf8'));
  const { prog, PrevProof } = makeSliceProgram(u, plan, si, {
    prevVkHash: BigInt(prevVk.hash),
    prevFlags,
  });
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });

  const a = argsOf(plan, side, si, alpha);
  const b = boundaryIn(plan, side, si, alpha);
  const prevProof = await (PrevProof as any).fromJSON(JSON.parse(readFileSync(proofPath(si - 1), 'utf8')));
  const prevVkObj = vkObject(prevVk);
  const foreignVk = readVk(foreign);
  const foreignProof = await (PrevProof as any).fromJSON(JSON.parse(readFileSync(proofPath(foreign), 'utf8')));

  const results: Record<string, { refused: boolean; err?: string }> = {};
  const attempt = async (name: string, f: () => Promise<unknown>) => {
    try {
      await f();
      results[name] = { refused: false };
    } catch (e) {
      results[name] = {
        refused: true,
        err: String((e as Error)?.message ?? e).slice(0, 300),
      };
    }
  };
  const call = (bIn: Field, p: any, vk: VerificationKey, args: any) =>
    (prog as any).slice(bIn, p, vk, args.alpha, args.accIn, args.liveIn, args.readLanes, args.others);

  await attempt('unrelatedInput', () => call(Field(0x1234), prevProof, prevVkObj, a));
  await attempt('liveBent', () => {
    const bent = a.liveIn.slice();
    bent[0] = BbExt.from(
      a.liveIn[0].toBigInts().map((v: bigint, i: number) => (i === 0 ? (v + 1n) % 2013265921n : v)),
    );
    return call(b, prevProof, prevVkObj, { ...a, liveIn: bent });
  });
  await attempt('readLaneBent', () => {
    const bent = a.readLanes.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, prevVkObj, { ...a, readLanes: bent });
  });
  await attempt('unreadDigestBent', () => {
    const bent = a.others.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, prevVkObj, { ...a, others: bent });
  });
  await attempt('accBent', () => {
    const acc = BbExt.from(
      a.accIn.toBigInts().map((v: bigint, i: number) => (i === 0 ? (v + 1n) % 2013265921n : v)),
    );
    return call(b, prevProof, prevVkObj, { ...a, accIn: acc });
  });
  // ⚑ THE SPLICE SIDE-LOADING MAKES POSSIBLE, and the one a SelfProof chain
  // cannot even express: a DIFFERENT slice's proof, handed together with THAT
  // slice's own verification key, so `prev.verify(vk)` is perfectly satisfied.
  await attempt('foreignProofAndKey', () =>
    call(boundaryIn(plan, side, si, alpha), foreignProof, vkObject(foreignVk), a),
  );
  // The predecessor's real proof, paired with a key it was not made under.
  await attempt('rightProofWrongKey', () => call(b, prevProof, vkObject(foreignVk), a));

  console.log(
    `##JSON##${JSON.stringify({ si, foreign, vkHash: verificationKey.hash.toString(), results })}`,
  );
}

// ===========================================================================
// PHASE `control` — the same slice with a binding removed, handed the BOUND
// chain's own proof objects.
// ===========================================================================

async function controlPhase() {
  const si = Number(process.env.FULLCHAIN_SLICE ?? '0');
  const foreign = Number(process.env.FULLCHAIN_FOREIGN ?? String(si - 2));
  const pin = process.env.FULLCHAIN_PIN !== '0';
  const { u, plan, side, alpha } = context();
  const prevVk = readVk(si - 1);
  const prevFlags: FeatureFlags = JSON.parse(readFileSync(flagsPath(si - 1), 'utf8'));
  const { prog, PrevProof } = makeSliceProgram(u, plan, si, {
    prevVkHash: BigInt(prevVk.hash),
    prevFlags,
    bindCarry: false,
    pinVk: pin,
  });
  await prog.compile({ cache: NO_CACHE });

  const a = argsOf(plan, side, si, alpha);
  const b = boundaryIn(plan, side, si, alpha);
  const prevProof = await (PrevProof as any).fromJSON(JSON.parse(readFileSync(proofPath(si - 1), 'utf8')));
  const prevVkObj = vkObject(prevVk);
  const foreignVk = readVk(foreign);
  const foreignProof = await (PrevProof as any).fromJSON(JSON.parse(readFileSync(proofPath(foreign), 'utf8')));

  const results: Record<string, boolean> = {};
  const accepts = async (name: string, f: () => Promise<unknown>) => {
    try {
      await f();
      results[name] = true;
    } catch {
      results[name] = false;
    }
  };
  const call = (bIn: Field, p: any, vk: VerificationKey, args: any) =>
    (prog as any).slice(bIn, p, vk, args.alpha, args.accIn, args.liveIn, args.readLanes, args.others);

  await accepts('unrelatedInput', () => call(Field(0x1234), prevProof, prevVkObj, a));
  await accepts('unreadDigestBent', () => {
    const bent = a.others.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, prevVkObj, { ...a, others: bent });
  });
  await accepts('foreignProofAndKey', () => call(b, foreignProof, vkObject(foreignVk), a));

  console.log(`##JSON##${JSON.stringify({ si, pin, foreign, results })}`);
}

// ===========================================================================
// Children.
// ===========================================================================

function child(env: Record<string, string>, label: string): Promise<any> {
  return new Promise((res, rej) => {
    execFile(
      process.execPath,
      ['--max-old-space-size=16384', process.argv[1]],
      { encoding: 'utf8', maxBuffer: 1 << 26, env: { ...process.env, ...env } },
      (err, stdout, stderr) => {
        const line = String(stdout).split('\n').find((l) => l.startsWith('##JSON##'));
        if (line) return res(JSON.parse(line.slice(8)));
        rej(
          new Error(
            `the ${label} phase produced no result line` +
              `${err ? ` (exit: ${err.message})` : ''}\n${String(stderr).slice(-2500)}`,
          ),
        );
      },
    );
  });
}

// ===========================================================================
// main
// ===========================================================================

async function main() {
  console.log('\n=== ROOT-AIR-FULLCHAIN — all 7 slices, one process each (leg 17) ===\n');
  const T0 = Date.now();
  //  ⚑ THE CLEAR MUST NOT DELETE WHAT THIS LEG DOES NOT PRODUCE. It used to
  //  `rmSync(WORK)` outright, which took `real-root-fri.json` with it — an
  //  artifact this leg NEVER re-mints (the `root_fri_instance` dumper writes it,
  //  and nothing here calls that dumper). So every non-REUSE run of this leg
  //  silently broke `root-fri-uniform`, `root-claim-carry`, `root-fri-preamble`
  //  and `head-anchor-pins`, all of which refuse without it.
  //
  //  ⚑ AND THE ORDER WAS THE OTHER HALF. The clear ran BEFORE the dumper, so a
  //  dumper that panics leaves an EMPTY workdir and no way back — which is
  //  exactly what happened on 2026-07-30 when `d7ba0c4d3` (fork rev 4aead01 →
  //  fc3c6df, D value columns into ConstAir's preprocessed trace) made
  //  `root_air_instance` panic at `const_air.rs:203`, `index out of bounds: the
  //  len is 2 but the index is 2`. A destructive step that runs before the step
  //  that can fail is a destructive step with no undo.
  //
  //  These two are INPUTS, produced by the two `dregg-circuit-prove` dumpers and
  //  read by six legs. Preserved across the clear, restored after it.
  const PRESERVE = ['real-root-air.json', 'real-root-fri.json'];
  if (!REUSE && existsSync(WORK)) {
    const kept: [string, Buffer][] = [];
    for (const n of PRESERVE) {
      const p = resolve(WORK, n);
      if (existsSync(p)) kept.push([n, readFileSync(p)]);
    }
    rmSync(WORK, { recursive: true, force: true });
    mkdirSync(WORK, { recursive: true });
    for (const [n, buf] of kept) writeFileSync(resolve(WORK, n), buf);
    if (kept.length)
      console.log(
        `    (kept ${kept.map(([n]) => n).join(', ')} across the clear — this leg does not mint them)`,
      );
  }
  mkdirSync(WORK, { recursive: true });

  // -----------------------------------------------------------------------
  // [1] The plan, at the MEASURED budget.
  // -----------------------------------------------------------------------
  console.log('[1] the plan, at leg 16\'s MEASURED per-branch budget');
  const { u, plan, side, alpha, real, pairs } = context();
  const lv = liveness(u);
  console.log(
    `    ${fmt(u.nodes.length)} DAG nodes / ${fmt(u.roots.length)} constraints, cut width <= ` +
      `${lv.maxWidth}, budget ${fmt(BUDGET)} rows/branch` +
      `${process.env.FULLCHAIN_BUDGET ? ' (OVERRIDDEN — not leg 16\'s measurement)' : ''}`,
  );
  for (const s of plan.slices)
    console.log(
      `    slice ${s.index}: nodes [${fmt(s.from)},${fmt(s.to)})  constraints ` +
        `[${fmt(s.foldFrom)},${fmt(s.foldTo)})  liveIn ${s.liveIn.length}  liveOut ` +
        `${s.liveOut.length}  chunks ${s.readsChunks.length}/${plan.nColChunks}  ` +
        `work ${fmt(s.workRows)} + carry ${fmt(s.carryRows)}`,
    );
  const N = plan.slices.length;
  const lastSlice = plan.slices[N - 1];
  if (lastSlice.to !== u.nodes.length)
    fail(`the plan covers ${fmt(lastSlice.to)} of ${fmt(u.nodes.length)} nodes — it is not the FULL chain`);
  if (lastSlice.foldTo !== u.roots.length)
    fail(`the plan folds ${fmt(lastSlice.foldTo)} of ${fmt(u.roots.length)} constraints`);
  if (lastSlice.liveOut.length !== 0)
    fail(`the terminal slice hands on ${lastSlice.liveOut.length} live values — the seal is not closed`);
  ok(
    `the plan is ${N} slices covering ALL ${fmt(u.nodes.length)} nodes and ALL ` +
      `${fmt(u.roots.length)} constraints, with an EMPTY terminal live set`,
  );

  // -----------------------------------------------------------------------
  // [2] The instance is dregg's committed root proof.
  // -----------------------------------------------------------------------
  console.log('\n[2] the instance: dregg\'s COMMITTED root proof');
  console.log(
    `    vk ${real.vkFingerprint.slice(0, 16)}...  ${real.numTurns} turns  ` +
      `degree_bits [${real.degreeBits.join(', ')}]`,
  );
  if (real.degreeBits.join(',') !== '10,10,16,15,3,16,0')
    fail(`degree_bits ${real.degreeBits} is not §1.2's [10,10,16,15,3,16,0] — a different root`);
  const accFinal = side.accs[N];
  if (accFinal.every((x) => x === 0n)) fail('the accumulator after the chain is ZERO');
  const accStrs = side.accs.map((a: bigint[]) => a.join(','));
  if (new Set(accStrs).size !== accStrs.length)
    fail('two slice boundaries carry the SAME accumulator — a dropped fold would be invisible');
  ok(
    `the chain's columns ARE the root proof's opened values at ζ; the accumulator moves at all ` +
      `${N + 1} boundaries and is non-zero`,
  );

  // -----------------------------------------------------------------------
  // [3] Seven processes.
  // -----------------------------------------------------------------------
  console.log(`\n[3] ${N} slices, ${N} processes — compile and prove`);
  const metas: any[] = [];
  for (let si = 0; si < N; si++) {
    if (REUSE && existsSync(metaPath(si))) {
      const m = JSON.parse(readFileSync(metaPath(si), 'utf8'));
      metas.push(m);
      console.log(`    slice ${si}: REUSED from ${WORK}`);
      continue;
    }
    const t = Date.now();
    const m = await child({ FULLCHAIN_PHASE: 'slice', FULLCHAIN_SLICE: String(si) }, `slice ${si}`);
    metas.push(m);
    console.log(
      `    slice ${si}: ${fmt(m.rows).padStart(6)} rows  ` +
        `${((m.rows / 65536) * 100).toFixed(1)}% of the domain  ` +
        `compile ${(m.compileMs / 1000).toFixed(1)}s  prove ${(m.proveMs / 1000).toFixed(1)}s  ` +
        `${m.verified ? 'VERIFIED' : 'NOT VERIFIED'}  (${secs(t)})`,
    );
    if (!m.verified) fail(`slice ${si}'s proof does not verify under its own key`);
  }
  for (const m of metas) {
    if (m.rows > 65536 - 4) fail(`slice ${m.si} is ${fmt(m.rows)} rows — past the Kimchi step domain`);
    // ⚑ AND PAST THE MEASURED CEILING IS THE REAL FAILURE, which is lower than
    // the domain by the recursive verifier Pickles puts on top of the body.
    if (m.rows > MEASURED_CEILING.sideloadAtLeast)
      fail(
        `slice ${m.si} emits ${fmt(m.rows)} rows, OUTSIDE the ${fmt(MEASURED_CEILING.sideloadAtLeast)}-row ` +
          'envelope this shape has been observed to compile in. It may well compile — but then the ' +
          'envelope is stale and `MEASURED_CEILING.sideloadAtLeast` is the thing to move, with a run ' +
          'behind it',
      );
  }
  ok(
    `${N} distinct slice circuits, each compiled and proved in its OWN process — no process ` +
      `compiled more than ONE (the wall §3.20 measured at four is never approached)`,
  );

  // -----------------------------------------------------------------------
  // [4] The chain, checked by a process that compiled NOTHING.
  // -----------------------------------------------------------------------
  console.log('\n[4] the chain, verified end to end');
  for (let si = 0; si < N; si++) {
    const vk = readVk(si);
    const pj = JSON.parse(readFileSync(proofPath(si), 'utf8'));
    if (!(await verify(pj, vk.data)))
      fail(`slice ${si}'s proof does not verify against slice ${si}'s verification key`);
    const wantIn = boundaryIn(plan, side, si, alpha).toString();
    if (pj.publicInput[0] !== wantIn)
      fail(`slice ${si}'s publicInput is not the boundary the out-of-circuit twin computed`);
    const wantOut = (si + 1 === N ? terminalOf(plan, side) : boundaryIn(plan, side, si + 1, alpha)).toString();
    if (pj.publicOutput[0] !== wantOut)
      fail(`slice ${si}'s publicOutput is not the boundary the out-of-circuit twin computed`);
    if (si > 0) {
      const prev = JSON.parse(readFileSync(proofPath(si - 1), 'utf8'));
      if (pj.publicInput[0] !== prev.publicOutput[0])
        fail(`slice ${si}'s publicInput is not slice ${si - 1}'s publicOutput`);
      if (metas[si].pinnedPrevVkHash !== readVk(si - 1).hash)
        fail(`slice ${si} pinned ${metas[si].pinnedPrevVkHash}, not slice ${si - 1}'s key hash`);
    }
    if (metas[si].maxProofsVerified !== sliceMaxProofsVerified(si))
      fail(`slice ${si}'s proof declares maxProofsVerified ${metas[si].maxProofsVerified}`);
  }
  ok(
    `all ${N} proofs verify against their own keys; every step's publicInput IS its predecessor's ` +
      `publicOutput; every public field matches the out-of-circuit twin — checked in a process ` +
      `that compiled NOTHING`,
  );
  const vkChain = metas.map((m) => m.vkHash);
  if (new Set(vkChain).size !== N) fail('two slices share a verification key hash');
  ok(
    `the ${N} verification keys are pairwise distinct and PINNED in a chain: slice k's circuit ` +
      `contains slice k−1's key hash as a CONSTANT, so the chain ends in one field element ` +
      `(${vkChain[N - 1].slice(0, 12)}…) a verifier holds`,
  );

  // -----------------------------------------------------------------------
  // [5] The splices, ACROSS the process boundary.
  // -----------------------------------------------------------------------
  const SPLICE_AT = Math.min(3, N - 1);
  const FOREIGN = SPLICE_AT - 2;
  console.log(
    `\n[5] the splice is REFUSED at slice ${SPLICE_AT} — in a process that compiled only slice ` +
      `${SPLICE_AT}, against a predecessor proof another process made`,
  );
  const sp = await child(
    {
      FULLCHAIN_PHASE: 'splice',
      FULLCHAIN_SLICE: String(SPLICE_AT),
      FULLCHAIN_FOREIGN: String(FOREIGN),
    },
    'splice',
  );
  if (sp.vkHash !== metas[SPLICE_AT].vkHash)
    fail(
      `slice ${SPLICE_AT} compiled to key ${sp.vkHash.slice(0, 12)}… in the splice process and ` +
        `${metas[SPLICE_AT].vkHash.slice(0, 12)}… in its own — the circuit is not REPRODUCIBLE ` +
        'across processes, and a pinned key hash means nothing if the key is not a constant',
    );
  ok(
    `slice ${SPLICE_AT} compiles to the SAME verification key in a second, independent process — ` +
      'the pin is a constant, not an accident of one run',
  );
  const SPLICES: [string, string][] = [
    ['unrelatedInput', `slice ${SPLICE_AT} entering a boundary with no relation to its predecessor`],
    ['liveBent', 'one carried LIVE value bent'],
    ['readLaneBent', 'one COLUMN LANE bent in a chunk the slice DOES read'],
    ['unreadDigestBent', 'a chunk DIGEST the slice NEVER READS, bent'],
    ['accBent', 'the incoming ACCUMULATOR bent'],
    [
      'foreignProofAndKey',
      `slice ${FOREIGN}'s proof handed with slice ${FOREIGN}'s OWN key — a valid proof of the ` +
        'wrong program',
    ],
    ['rightProofWrongKey', 'the right proof paired with a key it was not made under'],
  ];
  for (const [key, label] of SPLICES) {
    const r = sp.results[key];
    if (!r) fail(`the splice process did not attempt ${key}`);
    if (!r.refused) fail(`${label}: ACCEPTED`);
    if (!isConstraintFailure(r.err))
      fail(`${label}: the error is not a constraint failure — ${r.err}`);
    ok(`REFUSED: ${label}`);
  }

  // -----------------------------------------------------------------------
  // [6] The controls.
  // -----------------------------------------------------------------------
  console.log('\n[6] the controls — the same slice with ONE binding removed');
  console.log(
    '    ⚑ and they take the BOUND chain\'s OWN proof objects. §3.21 and §3.24 both had to build\n' +
      '      a parallel predecessor because a bound `SelfProof` cannot verify under an unbound VK.\n' +
      '      Side-loading dissolves that: the key is an input, so the control refutes the binding\n' +
      '      on the very proofs the chain produced.',
  );
  const ctlUnbound = await child(
    {
      FULLCHAIN_PHASE: 'control',
      FULLCHAIN_SLICE: String(SPLICE_AT),
      FULLCHAIN_FOREIGN: String(FOREIGN),
      FULLCHAIN_PIN: '1',
    },
    'control (unbound, pinned)',
  );
  if (!ctlUnbound.results.unrelatedInput)
    fail(
      'the UNBOUND control REFUSED a public input unrelated to its predecessor — the control is ' +
        'not testing the binding, and the refusals above are consistent with "the bend broke the work"',
    );
  ok('UNBOUND: a public input with no relation to its predecessor is ACCEPTED');
  if (!ctlUnbound.results.unreadDigestBent)
    fail('the UNBOUND control REFUSED a bend in a chunk digest it never reads');
  ok(
    'UNBOUND: a bent digest of a chunk the slice never reads is ACCEPTED — so the bound refusal ' +
      'IS the commitment biting, not the work breaking',
  );
  if (ctlUnbound.results.foreignProofAndKey)
    fail(
      'the UNBOUND-but-PINNED control ACCEPTED a foreign proof — the pin is not what refuses it ' +
        'and the attribution below would be wrong',
    );
  ok(
    `UNBOUND but PINNED: slice ${FOREIGN}'s proof under its own key is still REFUSED — so the ` +
      'foreign-proof refusal is the VK pin and not the boundary',
  );
  const ctlUnpinned = await child(
    {
      FULLCHAIN_PHASE: 'control',
      FULLCHAIN_SLICE: String(SPLICE_AT),
      FULLCHAIN_FOREIGN: String(FOREIGN),
      FULLCHAIN_PIN: '0',
    },
    'control (unbound, unpinned)',
  );
  if (!ctlUnpinned.results.foreignProofAndKey)
    fail(
      'the UNPINNED control REFUSED a foreign proof under its own key — then the pin is not what ' +
        'the refusal above is attributable to, and side-loading\'s named hole is not shown open',
    );
  ok(
    'UNPINNED: the same foreign proof under its own key is ACCEPTED — the hole side-loading opens ' +
      'is REAL, and one constant closes it',
  );

  // -----------------------------------------------------------------------
  // [7] The terminal seal is verifier-computable from the proof.
  // -----------------------------------------------------------------------
  console.log('\n[7] the terminal seal, recomputed from p3\'s OWN per-instance accumulators');
  const P = 2013265921n;
  const md = (x: bigint) => ((x % P) + P) % P;
  const eAdd = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x + b[i]));
  const eMul = (a: bigint[], b: bigint[]) => {
    const acc = Array(7).fill(0n) as bigint[];
    for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) acc[i + j] = md(acc[i + j] + a[i] * b[j]);
    return Array.from({ length: 4 }, (_, i) => (i + 4 < 7 ? md(acc[i] + 11n * acc[i + 4]) : acc[i]));
  };
  const ePow = (a: bigint[], n: number) => {
    let r = [1n, 0n, 0n, 0n];
    for (let i = 0; i < n; i++) r = eMul(r, a);
    return r;
  };
  const R = u.roots.length;
  let recomposed = [0n, 0n, 0n, 0n];
  u.tableSpans.forEach((span, i) => {
    const p3acc = pairs[i][1].accumulator.map((x) => BigInt(x));
    recomposed = eAdd(recomposed, eMul(p3acc, ePow(alpha, R - span.rootTo)));
  });
  if (recomposed.join(',') !== accFinal.join(','))
    fail(
      `the chain's terminal accumulator [${accFinal}] is NOT the α-weighted sum of p3's seven ` +
        `per-instance accumulators [${recomposed}] — the seal is an internal number`,
    );
  ok(
    `the terminal accumulator IS Σ_T acc_T·α^(1093−b_T) over p3's OWN seven accumulators — so a ` +
      `verifier holding dregg's root proof can compute the seal the chain seals to`,
  );
  const terminal = terminalOf(plan, side);
  const lastOut = JSON.parse(readFileSync(proofPath(N - 1), 'utf8')).publicOutput[0];
  if (lastOut !== terminal.toString()) fail('the terminal proof does not carry the expected seal');
  ok(`the terminal proof's publicOutput IS that seal: ${terminal.toString().slice(0, 20)}…`);

  // -----------------------------------------------------------------------
  // [8] Cost, and the ratchet.
  // -----------------------------------------------------------------------
  console.log('\n[8] cost');
  const totCompile = metas.reduce((a, m) => a + m.compileMs, 0);
  const totProve = metas.reduce((a, m) => a + m.proveMs, 0);
  const totRows = metas.reduce((a, m) => a + m.rows, 0);
  console.log(
    `    ${N} circuits, ${fmt(totRows)} emitted rows total (${fmt(Math.round(totRows / N))} mean, ` +
      `${fmt(Math.max(...metas.map((m: any) => m.rows)))} max = ` +
      `${((Math.max(...metas.map((m: any) => m.rows)) / 65536) * 100).toFixed(1)}% of the domain)`,
  );
  console.log(
    `    compile ${(totCompile / 1000).toFixed(0)}s total, prove ${(totProve / 1000).toFixed(0)}s ` +
      `total; one boundary on disk is ${fmt(metas[N - 1].proofBytes)} bytes of proof JSON plus a key`,
  );
  console.log(`    wall clock for the whole leg: ${secs(T0)}`);

  console.log('\n[9] RATCHET');
  const RECORDED: [string, number, number][] = [
    ['slices in the FULL chain', N, RATCHET.slices],
    ['nodes covered', lastSlice.to, RATCHET.nodes],
    ['constraints folded', lastSlice.foldTo, RATCHET.constraints],
    ['widest slice, EMITTED rows', Math.max(...metas.map((m: any) => m.rows)), RATCHET.maxRows],
    ['distinct verification keys', new Set(vkChain).size, RATCHET.vks],
    ['splices refused', SPLICES.length, RATCHET.splices],
  ];
  let drifted = 0;
  for (const [label, got, want] of RECORDED) {
    if (want === 0) {
      console.log(`    · ${label.padEnd(34)} ${fmt(got).padStart(10)} (first recording)`);
      continue;
    }
    const mark = got === want ? '✓' : '✗';
    console.log(`    ${mark} ${label.padEnd(34)} ${fmt(got).padStart(10)} (recorded ${fmt(want)})`);
    if (got !== want) drifted++;
  }
  if (drifted) fail(`${drifted} recorded figure(s) drifted`);
  ok('the recorded figures are as recorded');

  console.log(`\n=== ROOT-AIR-FULLCHAIN PASS === ${checks} checks, ${secs(T0)}\n`);
}

/** ⚑ Recorded on the run that first produced them, at `BUDGET_PROVED`. A zero
 *  means "not yet recorded" and prints instead of comparing. */
const RATCHET = { slices: 7, nodes: 10_417, constraints: 1_093, maxRows: 51_136, vks: 7, splices: 7 };

const phase =
  PHASE === 'slice'
    ? slicePhase()
    : PHASE === 'splice'
      ? splicePhase()
      : PHASE === 'control'
        ? controlPhase()
        : main();
phase.catch((e) => {
  console.error(e);
  process.exit(1);
});

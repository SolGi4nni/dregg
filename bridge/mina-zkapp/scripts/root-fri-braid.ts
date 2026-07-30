import { execFile } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { Cache, FeatureFlags, Field, Poseidon, VerificationKey, verify } from 'o1js';
import { BbExt } from '../src/FriQueryStep.js';
import {
  DagTable,
  RealInstance,
  RealRootAir,
  bindRealInstance,
  rootAirDag,
  unifiedDag,
} from '../src/RootAirDag.js';
import { digestOfLanes, airTerminalSeal } from '../src/RootAirChain.js';
import {
  RealRootFri,
  airColumnIndex,
  deepTermCensus,
  friLaneTable,
  planFriWalk,
  planOpenedValues,
  rootFriShape,
  segmentWalk,
} from '../src/RootFriWalk.js';
import {
  AIR_CHUNK_LANES,
  AIR_SLICES,
  FriBraidCtx,
  airLaneValues,
  chunkDigestsBigInt,
  friBoundaryIn,
  friBoundaryOut,
  friLaneValues,
  auxLanes,
  friSliceShape,
  makeFriSliceProgram,
  walkTwin,
} from '../src/RootFriSlice.js';
import { dagDigestOfChunkDigests } from '../src/RootAirChain.js';
import { atTier, belowTier, tierStop } from '../src/tier.js';
import { MEASURED_ROOT_GEOMETRY } from '../src/CostModel.js';

// ---------------------------------------------------------------------------
// LEG 18 — THE BRAID: the AIR chain's terminal seal chained INTO the FRI walk,
// at the root's real geometry, on dregg's committed root proof.
//
// The AIR half (§3.27) is reused, not re-proved: its seven artifacts are on disk
// and this chain's slice 0 side-loads slice 6's proof. That is the point — a
// braid that had to rebuild the thing it braids onto would not be a braid.
// ---------------------------------------------------------------------------

const PHASE = process.env.FRIBRAID_PHASE ?? 'main';
const NO_CACHE = Cache.None; //  o1js's default prover-key cache aborts with `rust_oom`
const WORK = process.env.FRIBRAID_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const FRI = (n: string) => resolve(WORK, `fri-${n}`);
const BUDGET = Number(process.env.FRIBRAID_BUDGET ?? 50_000);
const CHUNK = Number(process.env.FRIBRAID_CHUNK ?? 256);
/** ⚑ HOW MANY OF THE 835 SLICES THIS RUN ACTUALLY PROVES. There is no budget in
 *  which all of them are proved today — the leg reports the MEASURED rate and
 *  the extrapolation separately, and never quotes the second as the first. */
const LIMIT = Number(process.env.FRIBRAID_LIMIT ?? 4);
/** ⚑ OFF BY DEFAULT, for §3.27's reason: reusing a slice's artifacts turns a
 *  chain into a claim about files on disk. The flag exists so a lane can EXTEND
 *  a prefix it already proved instead of re-proving it, and [4] still verifies
 *  every reused proof against its own key and its predecessor's output — so a
 *  stale artifact is caught rather than trusted. */
const REUSE = process.env.FRIBRAID_REUSE === '1';

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
 *  `catch {}`, which is what would make a splice table "a green that measures
 *  the harness". */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read|ENOENT/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|Bool\.assertTrue|verification key|proof.*invalid|invalid.*proof/i.test(
    m,
  );
}

// ===========================================================================
// The context both the driver and every child process rebuild deterministically.
// ===========================================================================

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

function readReal(): { air: RealRootAir; fri: RealRootFri } {
  const a = resolve(WORK, 'real-root-air.json');
  const f = resolve(WORK, 'real-root-fri.json');
  //  ⚑ MISSING TOOLCHAIN IS A FAILURE, NOT A SKIP: there is no synthetic
  //  fallback instance, because "the walk runs on dregg's proof" is the claim.
  if (!existsSync(a))
    fail(`${a} is missing — run \`npm run root-air-fullchain\` (it mints it from the committed proof)`);
  if (!existsSync(f))
    fail(
      `${f} is missing — build and run the dumper:\n` +
        '    cargo build -p dregg-circuit-prove --release --bin root_fri_instance\n' +
        `    ./target/release/root_fri_instance ${f}`,
    );
  return { air: JSON.parse(readFileSync(a, 'utf8')), fri: JSON.parse(readFileSync(f, 'utf8')) };
}

/** The AIR chain's column assignment, bound to the real proof's opened values in
 *  the SAME table order `unifiedDag` concatenates them — the function
 *  `root-air-fullchain.ts` uses, so the two compute the SAME `dagDigest`. */
function realColumns(real: RealRootAir) {
  const d = rootAirDag();
  const byName: Record<string, RealInstance> = {};
  for (const i of real.instances)
    byName[i.table.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_')] = i;
  const pairs: [DagTable, RealInstance][] = d.tables.map((t) => {
    const i = byName[t.name] ?? byName[t.name.toLowerCase()];
    if (!i) fail(`no real instance for table ${t.name}`);
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

type Ctx = FriBraidCtx & {
  airLanes: bigint[];
  friLanes: bigint[];
  twin: ReturnType<typeof walkTwin>;
  dagDigest: Field;
  friDigest: Field;
  friCommit: Field;
  acc: bigint[];
  realAir: RealRootAir;
  realFri: RealRootFri;
};

function context(): Ctx {
  const { air: realAir, fri: realFri } = readReal();
  const shape = rootFriShape(realFri);
  const airIx = airColumnIndex();
  const op = planOpenedValues(shape, airIx);
  const ft = friLaneTable(shape, op);
  const w = segmentWalk(shape);
  const plan = planFriWalk(w, op, ft, { usableRows: BUDGET, chunkLanes: CHUNK });

  const cols = realColumns(realAir);
  const airLanes = airLaneValues(cols.base, cols.ext);
  const friLanes = friLaneValues(realFri, shape, ft, op);
  const twin = walkTwin(w, shape, ft, op, friLanes, airLanes, realFri);

  //  ⚑ `dagDigest` is computed over the AIR chain's OWN chunking (64 extension
  //  values a chunk), which is not this chain's lane chunking. Two chunkings
  //  over one lane table, and the AIR one is the one the seal was made under.
  const nAir = airLanes.length / AIR_CHUNK_LANES;
  const dagDigest = dagDigestOfChunkDigests(chunkDigestsBigInt(airLanes, nAir, AIR_CHUNK_LANES));
  const friDigest = dagDigestOfChunkDigests(
    chunkDigestsBigInt(friLanes, plan.nFriChunks, CHUNK),
  );
  const friCommit = Poseidon.hash([dagDigest, friDigest]);

  //  The AIR chain's terminal accumulator, VERIFIER-COMPUTABLE: p3's own seven
  //  per-instance accumulators, α-weighted by their root spans (§3.27 [7]).
  const u = unifiedDag(rootAirDag());
  const R = u.roots.length;
  let acc = [0n, 0n, 0n, 0n];
  u.tableSpans.forEach((span, i) => {
    const p3 = cols.pairs[i][1].accumulator.map((x) => BigInt(x));
    acc = eAdd(acc, eMul(p3, ePow(cols.alpha, R - span.rootTo)));
  });

  return {
    w,
    shape,
    ft,
    op,
    plan,
    airLanes,
    friLanes,
    twin,
    dagDigest,
    friDigest,
    friCommit,
    acc,
    realAir,
    realFri,
  };
}

// ===========================================================================
// Boundary artifacts on disk — the ONLY thing that crosses a process.
// ===========================================================================

const vkPath = (si: number) => FRI(`vk-${si}.json`);
const flagsPath = (si: number) => FRI(`flags-${si}.json`);
const proofPath = (si: number) => FRI(`proof-${si}.json`);
const metaPath = (si: number) => FRI(`meta-${si}.json`);
const airVk = () => resolve(WORK, 'vk-6.json');
const airFlags = () => resolve(WORK, 'flags-6.json');
const airProof = () => resolve(WORK, 'proof-6.json');

const readVk = (p: string): { data: string; hash: string } => JSON.parse(readFileSync(p, 'utf8'));
const vkObject = (v: { data: string; hash: string }) =>
  new VerificationKey({ data: v.data, hash: Field(v.hash) });

// ===========================================================================
// PHASE `slice` — compile and prove ONE FRI slice.
// ===========================================================================

function witnessOf(c: Ctx, si: number) {
  const sl = c.plan.slices[si];
  const sh = friSliceShape(c, si);
  const F = (x: bigint) => Field(x);
  const pad = (a: Field[], n: number) => (a.length ? a : [Field(0)]).slice(0, Math.max(n, 1));
  const airRead: Field[] = [];
  for (const ch of sl.readsAirChunks)
    for (let i = 0; i < CHUNK; i++) airRead.push(F(c.airLanes[ch * CHUNK + i] ?? 0n));
  const nAirTot = Math.ceil(c.airLanes.length / CHUNK);
  const airOther: Field[] = [];
  for (let ch = 0; ch < nAirTot; ch++)
    if (!sl.readsAirChunks.includes(ch))
      airOther.push(
        digestOfLanes(c.airLanes.slice(ch * CHUNK, (ch + 1) * CHUNK).map((x) => Field(x))),
      );
  const friRead: Field[] = [];
  for (const ch of sl.readsFriChunks)
    for (let i = 0; i < CHUNK; i++) friRead.push(F(c.friLanes[ch * CHUNK + i] ?? 0n));
  const friOther: Field[] = [];
  for (let ch = 0; ch < c.plan.nFriChunks; ch++)
    if (!sl.readsFriChunks.includes(ch))
      friOther.push(
        digestOfLanes(c.friLanes.slice(ch * CHUNK, (ch + 1) * CHUNK).map((x) => Field(x))),
      );
  const aux: Field[] = [];
  for (let k = sl.from; k < sl.to; k++) for (const v of c.twin.aux[k]) aux.push(F(v));
  return {
    acc: BbExt.from(c.acc),
    liveIn: pad(c.twin.carry[sl.from].map(F), sh.nLiveIn),
    airRead: pad(airRead, sh.nAirRead),
    airOther: pad(airOther, sh.nAirOther),
    friRead: pad(friRead, sh.nFriRead),
    friOther: pad(friOther, sh.nFriOther),
    aux: pad(aux, sh.nAux),
  };
}

async function slicePhase() {
  const si = Number(process.env.FRIBRAID_SLICE ?? '0');
  const c = context();
  const prevVkFile = si === 0 ? airVk() : vkPath(si - 1);
  const prevFlagsFile = si === 0 ? airFlags() : flagsPath(si - 1);
  const prevProofFile = si === 0 ? airProof() : proofPath(si - 1);
  const prevVk = readVk(prevVkFile);
  const prevFlags: FeatureFlags = JSON.parse(readFileSync(prevFlagsFile, 'utf8'));

  const { prog, Prev } = makeFriSliceProgram(c, si, {
    prevVkHash: BigInt(prevVk.hash),
    prevFlags,
  });

  let t = Date.now();
  const meta = (await (prog as any).analyzeMethods()) as any;
  const rows = meta.slice.rows as number;
  const analyzeMs = Date.now() - t;
  const myFlags = FeatureFlags.fromGates(meta.slice.gates);

  t = Date.now();
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });
  const compileMs = Date.now() - t;
  mkdirSync(WORK, { recursive: true });
  writeFileSync(
    vkPath(si),
    JSON.stringify({ data: verificationKey.data, hash: verificationKey.hash.toString() }),
  );
  writeFileSync(flagsPath(si), JSON.stringify(myFlags));

  const wit = witnessOf(c, si);
  const bIn = friBoundaryIn(c, c.twin, si, c.dagDigest, c.friCommit, c.acc);
  t = Date.now();
  const r = await (prog as any).slice(
    bIn,
    await (Prev as any).fromJSON(JSON.parse(readFileSync(prevProofFile, 'utf8'))),
    vkObject(prevVk),
    wit.acc,
    wit.liveIn,
    wit.airRead,
    wit.airOther,
    wit.friRead,
    wit.friOther,
    wit.aux,
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
    pinnedPrevVkHash: prevVk.hash,
    publicInput: r.proof.publicInput.toString(),
    publicOutput: r.proof.publicOutput.toString(),
    segFrom: c.plan.slices[si].from,
    segTo: c.plan.slices[si].to,
    modelRows: c.plan.slices[si].workRows + c.plan.slices[si].carryRows,
    proofBytes: JSON.stringify(r.proof.toJSON()).length,
    maxProofsVerified: r.proof.maxProofsVerified,
  };
  writeFileSync(metaPath(si), JSON.stringify(out));
  console.log(`##JSON##${JSON.stringify(out)}`);
}

// ===========================================================================
// PHASE `splice` / `control`.
// ===========================================================================

async function splicePhase() {
  const si = Number(process.env.FRIBRAID_SLICE ?? '1');
  const c = context();
  const prevVk = readVk(si === 0 ? airVk() : vkPath(si - 1));
  const prevFlags: FeatureFlags = JSON.parse(readFileSync(si === 0 ? airFlags() : flagsPath(si - 1), 'utf8'));
  const { prog, Prev } = makeFriSliceProgram(c, si, {
    prevVkHash: BigInt(prevVk.hash),
    prevFlags,
  });
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });

  const wit = witnessOf(c, si);
  const b = friBoundaryIn(c, c.twin, si, c.dagDigest, c.friCommit, c.acc);
  const prevProof = await (Prev as any).fromJSON(
    JSON.parse(readFileSync(si === 0 ? airProof() : proofPath(si - 1), 'utf8')),
  );
  //  ⚑ THE FOREIGN PROOF IS THE AIR CHAIN'S SLICE 5 — a valid proof of a real
  //  program, under its own real key, made in a different process. There is no
  //  more realistic wrong predecessor available anywhere in this repo.
  const foreignVk = readVk(resolve(WORK, 'vk-5.json'));
  const foreignProof = await (Prev as any).fromJSON(
    JSON.parse(readFileSync(resolve(WORK, 'proof-5.json'), 'utf8')),
  );

  const results: Record<string, { refused: boolean; err?: string }> = {};
  const attempt = async (name: string, f: () => Promise<unknown>) => {
    try {
      await f();
      results[name] = { refused: false };
    } catch (e) {
      results[name] = { refused: true, err: String((e as Error)?.message ?? e).slice(0, 300) };
    }
  };
  const call = (bIn: Field, p: any, vk: VerificationKey, wt: any) =>
    (prog as any).slice(bIn, p, vk, wt.acc, wt.liveIn, wt.airRead, wt.airOther, wt.friRead, wt.friOther, wt.aux);

  await attempt('unrelatedInput', () => call(Field(0x1234), prevProof, vkObject(prevVk), wit));
  await attempt('accBent', () =>
    call(b, prevProof, vkObject(prevVk), {
      ...wit,
      acc: BbExt.from(c.acc.map((v, i) => (i === 0 ? (v + 1n) % P : v))),
    }),
  );
  await attempt('airDigestBent', () => {
    const bent = wit.airOther.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, vkObject(prevVk), { ...wit, airOther: bent });
  });
  await attempt('friDigestBent', () => {
    const bent = wit.friOther.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, vkObject(prevVk), { ...wit, friOther: bent });
  });
  await attempt('carryBent', () => {
    const bent = wit.liveIn.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, vkObject(prevVk), { ...wit, liveIn: bent });
  });
  if (wit.aux.length > 1)
    await attempt('auxBent', () => {
      const bent = wit.aux.slice();
      bent[0] = bent[0].add(Field(1));
      return call(b, prevProof, vkObject(prevVk), { ...wit, aux: bent });
    });
  await attempt('foreignProofAndKey', () => call(b, foreignProof, vkObject(foreignVk), wit));
  await attempt('rightProofWrongKey', () => call(b, prevProof, vkObject(foreignVk), wit));

  console.log(
    `##JSON##${JSON.stringify({ si, vkHash: verificationKey.hash.toString(), results })}`,
  );
}

async function controlPhase() {
  const si = Number(process.env.FRIBRAID_SLICE ?? '1');
  const pin = process.env.FRIBRAID_PIN !== '0';
  const c = context();
  const prevVk = readVk(si === 0 ? airVk() : vkPath(si - 1));
  const prevFlags: FeatureFlags = JSON.parse(readFileSync(si === 0 ? airFlags() : flagsPath(si - 1), 'utf8'));
  const { prog, Prev } = makeFriSliceProgram(c, si, {
    prevVkHash: BigInt(prevVk.hash),
    prevFlags,
    bindCarry: false,
    pinVk: pin,
  });
  await prog.compile({ cache: NO_CACHE });

  const wit = witnessOf(c, si);
  const b = friBoundaryIn(c, c.twin, si, c.dagDigest, c.friCommit, c.acc);
  const prevProof = await (Prev as any).fromJSON(
    JSON.parse(readFileSync(si === 0 ? airProof() : proofPath(si - 1), 'utf8')),
  );
  const foreignVk = readVk(resolve(WORK, 'vk-5.json'));
  const foreignProof = await (Prev as any).fromJSON(
    JSON.parse(readFileSync(resolve(WORK, 'proof-5.json'), 'utf8')),
  );

  const results: Record<string, boolean> = {};
  const accepts = async (name: string, f: () => Promise<unknown>) => {
    try {
      await f();
      results[name] = true;
    } catch {
      results[name] = false;
    }
  };
  const call = (bIn: Field, p: any, vk: VerificationKey, wt: any) =>
    (prog as any).slice(bIn, p, vk, wt.acc, wt.liveIn, wt.airRead, wt.airOther, wt.friRead, wt.friOther, wt.aux);

  await accepts('unrelatedInput', () => call(Field(0x1234), prevProof, vkObject(prevVk), wit));
  await accepts('airDigestBent', () => {
    const bent = wit.airOther.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, vkObject(prevVk), { ...wit, airOther: bent });
  });
  await accepts('foreignProofAndKey', () => call(b, foreignProof, vkObject(foreignVk), wit));

  console.log(`##JSON##${JSON.stringify({ si, pin, results })}`);
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
            `the ${label} phase produced no result line${err ? ` (exit: ${err.message})` : ''}\n` +
              `${String(stderr).slice(-2500)}`,
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
  console.log('\n=== ROOT-FRI-BRAID — the AIR seal chained into the FRI walk (leg 18) ===\n');
  const T0 = Date.now();
  mkdirSync(WORK, { recursive: true });
  const c = context();
  const K = c.shape.knobs;
  const census = deepTermCensus(c.shape);

  // -----------------------------------------------------------------------
  // [1] The walk, at the ROOT's real geometry.
  // -----------------------------------------------------------------------
  console.log('[1] the walk, at the root\'s REAL geometry, on dregg\'s committed root proof');
  console.log(
    `    vk ${c.realFri.vkFingerprint.slice(0, 16)}...  degree_bits [${c.realFri.degreeBits}]  ` +
      `|D^0| = 2^${K.logGlobalMaxHeight}  log_blowup ${K.logBlowup}  ${K.numQueries} queries  ` +
      `${K.layers} layers  query_pow ${K.queryPowBits}`,
  );
  if (c.realFri.kind !== 'dregg-root-fri-instance') fail(`not a root FRI instance: ${c.realFri.kind}`);
  if (c.realAir.vkFingerprint !== c.realFri.vkFingerprint)
    fail('the AIR dump and the FRI dump are of DIFFERENT proofs — their vk fingerprints differ');
  if (c.realAir.challenges.zeta.join(',') !== c.realFri.zeta.join(','))
    fail(
      'the AIR dump and the FRI dump disagree on ζ — two replays of one transcript that reached ' +
        'different points, and every opened value below would be at a different place',
    );
  ok(
    'the AIR dump and the FRI dump are the SAME proof at the SAME ζ — the two halves are braiding ' +
      'over one object, checked and not assumed',
  );
  const idxs = c.realFri.queries.map((q) => q.index);
  if (new Set(idxs).size !== idxs.length)
    fail('two query indices COLLIDE — a substitution falsifier over them would be a no-op');
  ok(`the ${K.numQueries} query indices are pairwise distinct: ${idxs.slice(0, 4).join(', ')}, …`);
  console.log(
    `    ${fmt(c.w.segs.length)} segments, ${fmt(c.w.totalRows)} modelled work rows; DEEP terms ` +
      `per query ${fmt(census.total)}; ${fmt(c.plan.slices.length)} slices at a ${fmt(BUDGET)}-row budget`,
  );
  console.log(
    `    the braid binds ${fmt(c.op.split.air)} of ${fmt(c.op.split.total)} opened values ` +
      `(${((c.op.split.air / c.op.split.total) * 100).toFixed(1)}%) to the AIR chain's own column ` +
      `commitment; the other ${fmt(c.op.split.fri)} are under friDigest`,
  );

  // -----------------------------------------------------------------------
  // [2] The braid's arithmetic, BEFORE a single circuit is compiled.
  // -----------------------------------------------------------------------
  console.log('\n[2] the seal AIR slice 6 emitted, recomputed from the FRI side');
  //  ⚑ THE ONE OUT-OF-CIRCUIT CHECK THAT NEEDS AN ARTIFACT. `.fullchain/
  //  proof-6.json` is a Pickles proof only a tier-2 run mints, and it is
  //  gitignored, so on a fresh tree there is nothing here to compare against.
  //  It is stated rather than skipped: the tier-0 PASS line names it.
  if (atTier(1) || existsSync(airProof())) {
  if (!existsSync(airProof())) fail(`${airProof()} is missing — the AIR half has not been proved`);
  const air6 = JSON.parse(readFileSync(airProof(), 'utf8'));
  const want = airTerminalSeal(c.dagDigest, digestOfLanes(c.acc.map((x) => Field(x))), AIR_SLICES);
  if (air6.publicOutput[0] !== want.toString())
    fail(
      `AIR slice 6's publicOutput is ${String(air6.publicOutput[0]).slice(0, 18)}… and the FRI side ` +
        `recomputes ${want.toString().slice(0, 18)}… — the two halves do not agree on dagDigest or ` +
        'on the accumulator, and the braid would be a coincidence if it matched later',
    );
  ok(
    'the FRI side recomputes AIR slice 6\'s ENTIRE public output from (a) the AIR column ' +
      'assignment it loads and (b) the α-weighted sum of p3\'s own seven accumulators — so the ' +
      'braid is over one column commitment, checked out of circuit before anything compiled',
  );
  } else {
    console.log(
      `    NOT CHECKED at MINA_TIER=0: ${airProof()} is absent. It is a Pickles proof only a ` +
        'tier-2 run mints and it is gitignored; when it IS on disk this check runs at tier 0 too.',
    );
  }

  // -----------------------------------------------------------------------
  // [2b] THE WHOLE WALK, OUT OF CIRCUIT, AGAINST P3'S OWN NUMBERS.
  //
  // ⚑ THIS IS THE INSTRUMENT THAT CAN SEE A WRONG CONVENTION, AND THE SLICES
  // CANNOT. A slice run proves the first N cuts of the walk; the first
  // assertion against a committed Merkle root does not occur until slice ~12,
  // and the fold chain not until slice ~30. So a mis-ordered mixed-height
  // injection, a path direction taken from the wrong index bit, or an
  // `alpha_pow` advanced per matrix instead of per height would all COMPILE AND
  // PROVE cleanly for as far as any affordable run reaches. The twin runs the
  // entire 11,270-segment walk in seconds and compares against the numbers p3's
  // own verifier produced, so every convention is checked before a circuit is.
  // -----------------------------------------------------------------------
  console.log('\n[2b] the whole walk, out of circuit, against p3\'s own numbers');
  {
    const S = c.w.slots;
    const eq = (a: bigint[], b: number[] | bigint[]) =>
      a.length === b.length && a.every((x, i) => x === BigInt(b[i] as any));
    const alphaGot = S.alpha.map((i) => c.twin.at.get(i)!);
    if (!eq(alphaGot, c.realFri.friAlpha))
      fail(`the walk derives FRI α [${alphaGot}] and p3 drew [${c.realFri.friAlpha}]`);
    for (let r = 0; r < K.layers; r++) {
      const got = S.beta[r].map((i) => c.twin.at.get(i)!);
      if (!eq(got, c.realFri.betas[r])) fail(`the walk derives β${r} [${got}] and p3 drew [${c.realFri.betas[r]}]`);
    }
    const gotIdx = c.realFri.queries.map((_, q) => c.twin.at.get(S.qidx[q])!);
    if (!gotIdx.every((v, q) => v === BigInt(idxs[q])))
      fail(`the walk derives query indices [${gotIdx}] and p3 drew [${idxs}]`);
    ok(
      `starting from dregg's OWN challenger state, the walk derives p3's OWN α, all ${K.layers} βs ` +
        `and all ${K.numQueries} query indices — the transcript is not a re-implementation that ` +
        'happens to run, it reproduces the numbers the deployed verifier drew',
    );
    let roots = 0;
    let folds = 0;
    for (const chk of c.twin.checks) {
      if (chk.kind === 'inputRoot') {
        const want = c.realFri.inputRounds[chk.round!].commit;
        if (!eq(chk.got, want))
          fail(
            `query ${chk.q} input round ${chk.round} opens to [${chk.got.slice(0, 3)}…] and dregg's ` +
              `commitment is [${want.slice(0, 3)}…] — the mixed-height opening is wrong`,
          );
        roots++;
      } else if (chk.kind === 'ro') {
        const want = c.realFri.queries[chk.q].reducedOpenings[chk.i!];
        if (want.logHeight !== chk.h) fail(`reduced-opening ${chk.i} is at height ${chk.h}, p3 says ${want.logHeight}`);
        if (!eq(chk.got, want.ro))
          fail(
            `query ${chk.q}'s reduced opening at height ${chk.h} is [${chk.got}] and p3's ` +
              `open_input gives [${want.ro}] — the DEEP quotient disagrees with the deployed one`,
          );
      } else if (chk.kind === 'fold') {
        const want = c.realFri.queries[chk.q].foldedAfterRound[chk.i!];
        if (!eq(chk.got, want))
          fail(
            `query ${chk.q}'s folded value after round ${chk.i} is [${chk.got}] and p3's is ` +
              `[${want}] — the fold chain diverges at round ${chk.i}`,
          );
        folds++;
      } else if (chk.kind === 'final') {
        if (!eq(chk.got, c.realFri.finalPoly[0]))
          fail(`query ${chk.q}'s chain lands on [${chk.got}] and the final polynomial is [${c.realFri.finalPoly[0]}]`);
      }
    }
    ok(
      `${roots} mixed-height input openings reproduce dregg's OWN four commitments; all ` +
        `${K.numQueries * c.shape.heights.length} reduced openings reproduce p3's OWN open_input; ` +
        `${folds} fold steps reproduce p3's OWN chain; all ${K.numQueries} queries land on the ` +
        'committed final polynomial',
    );
  }

  // ── THE TIER-0 STOP ───────────────────────────────────────────────────────
  //  ⚑ EVERYTHING ABOVE IS THE INSTRUMENT THAT FOUND THIS LEG'S DEFECTS, and
  //  everything below is the one that did not. [2b] walks all 11,303 segments
  //  against p3's own numbers in seconds; [3]-[8] compile Pickles circuits for
  //  minutes to prove a PREFIX of the same walk. Four defects — a full output
  //  buffer on entry, `sample_bits` on the low bits, `alpha_pow` starting at
  //  one, an undefined path direction — were each caught above and would each
  //  have compiled and proved cleanly below.
  if (belowTier(1)) {
    tierStop(
      'ROOT-FRI-BRAID',
      checks,
      secs(T0),
      `[3] ${Math.min(LIMIT, c.plan.slices.length)} FRI slices compiled+proved one process each, ` +
        '[4] the chain verified end to end, [5] the cross-process splices, [6] the unbound ' +
        'controls, [7] cost, [8] the row ratchet — MINA_TIER=1 or 2 runs them',
    );
    return;
  }

  // -----------------------------------------------------------------------
  // [3] The slices.
  // -----------------------------------------------------------------------
  const N = Math.min(LIMIT, c.plan.slices.length);
  console.log(
    `\n[3] ${N} of ${fmt(c.plan.slices.length)} FRI slices, one process each — compile and prove`,
  );
  const metas: any[] = [];
  let proved = 0;
  for (let si = 0; si < N; si++) {
    const t = Date.now();
    if (REUSE && existsSync(metaPath(si))) {
      const m = JSON.parse(readFileSync(metaPath(si), 'utf8'));
      metas.push(m);
      console.log(`    fri slice ${String(si).padStart(3)}: REUSED (${fmt(m.rows)} rows)`);
      continue;
    }
    const m = await child({ FRIBRAID_PHASE: 'slice', FRIBRAID_SLICE: String(si) }, `slice ${si}`);
    metas.push(m);
    proved++;
    const sl = c.plan.slices[si];
    console.log(
      `    fri slice ${String(si).padStart(3)}: segments [${fmt(sl.from)},${fmt(sl.to)}) ` +
        `${c.w.segs[sl.from].t.padEnd(7)} ${fmt(m.rows).padStart(6)} rows ` +
        `(model ${fmt(m.modelRows)}, ${(((m.rows - m.modelRows) / m.modelRows) * 100).toFixed(1)}%)  ` +
        `compile ${(m.compileMs / 1000).toFixed(1)}s  prove ${(m.proveMs / 1000).toFixed(1)}s  ` +
        `${m.verified ? 'VERIFIED' : 'NOT VERIFIED'}  (${secs(t)})`,
    );
    if (!m.verified) fail(`FRI slice ${si}'s proof does not verify under its own key`);
    if (m.rows > 65536 - 4) fail(`FRI slice ${si} is ${fmt(m.rows)} rows — past the Kimchi step domain`);
  }
  ok(
    `${N} FRI slice circuits, each compiled and proved in its OWN process — no process compiled ` +
      'more than ONE, so the four-circuits-per-process wall is never approached',
  );

  // -----------------------------------------------------------------------
  // [4] The chain, checked by a process that compiled NOTHING.
  // -----------------------------------------------------------------------
  console.log('\n[4] the braided chain, verified end to end');
  for (let si = 0; si < N; si++) {
    const vk = readVk(vkPath(si));
    const pj = JSON.parse(readFileSync(proofPath(si), 'utf8'));
    if (!(await verify(pj, vk.data)))
      fail(`FRI slice ${si}'s proof does not verify against its own verification key`);
    const wantIn = friBoundaryIn(c, c.twin, si, c.dagDigest, c.friCommit, c.acc).toString();
    if (pj.publicInput[0] !== wantIn)
      fail(`FRI slice ${si}'s publicInput is not the boundary the out-of-circuit twin computed`);
    const wantOut = friBoundaryOut(c, c.twin, si, c.friCommit, c.acc).toString();
    if (pj.publicOutput[0] !== wantOut)
      fail(`FRI slice ${si}'s publicOutput is not the boundary the out-of-circuit twin computed`);
    const prevOut =
      si === 0
        ? JSON.parse(readFileSync(airProof(), 'utf8')).publicOutput[0]
        : JSON.parse(readFileSync(proofPath(si - 1), 'utf8')).publicOutput[0];
    if (pj.publicInput[0] !== prevOut)
      fail(`FRI slice ${si}'s publicInput is not its predecessor's publicOutput`);
    const prevVkHash = si === 0 ? readVk(airVk()).hash : readVk(vkPath(si - 1)).hash;
    if (metas[si].pinnedPrevVkHash !== prevVkHash)
      fail(`FRI slice ${si} pinned ${metas[si].pinnedPrevVkHash}, not its predecessor's key hash`);
  }
  ok(
    `all ${N} FRI proofs verify against their own keys; every step's publicInput IS its ` +
      'predecessor\'s publicOutput — and FRI slice 0\'s predecessor is AIR SLICE 6, so the chain ' +
      'is ONE key-pinned side-loaded chain of ' +
      `${AIR_SLICES + N} steps and not two chains`,
  );

  // -----------------------------------------------------------------------
  // [5] The splices, ACROSS the process boundary.
  // -----------------------------------------------------------------------
  //  ⚑ SPLICE AT A SLICE THAT CARRIES MERKLE DATA. A transcript-only slice has
  //  no `aux`, so the `auxBent` attempt cannot fire there and the table would
  //  quietly report seven of eight — a falsifier that is absent reads exactly
  //  like one that passed. The cut is chosen to be the LAST proved slice that
  //  consumes a witnessed sibling.
  //
  //  ⚑⚑ KNOWN DEFECT, FLAGGED AND NOT FIXED HERE — DO NOT READ THIS RULE AS
  //  COVERED. It selects on the presence of the WITNESS (`aux > 0`) and not on
  //  the presence of the ASSERTION THAT CLOSES OVER IT. A bent Merkle sibling is
  //  only caught by the `cur == commitment` check of its round, which can be
  //  several cuts later — so a cut chosen this way can carry `aux`, accept a
  //  bent sibling CORRECTLY, and have that accept read as a failed falsifier.
  //  The uniform-walk lane MEASURED it in its own splice suite: at `block7` a
  //  bent sibling was accepted because the first closing root is three cuts on
  //  at `block9`, and of 43 block positions 25 carry `aux` while only 16 close
  //  a root.
  //
  //  ⚑ AND BOTH OBVIOUS HANDLINGS ARE WRONG, which is why this is a flag and
  //  not a quick patch: asserting the refusal is a FALSE RED (the bend genuinely
  //  cannot be caught at that cut), and dropping the attempt is an ABSENT
  //  FALSIFIER READING AS A PASS. The uniform lane's fix is THREE-VALUED — the
  //  cut must contain a CLOSER, and at an aux-only cut `auxBent` is reported
  //  NOT ATTRIBUTABLE with its reason rather than asserted or skipped. Whoever
  //  next edits this table should carry that treatment across; leg 21 (the claim
  //  carry) touched neither the cut rule nor the splice table and did not.
  let AT = Math.min(1, N - 1);
  for (let si = N - 1; si >= 0; si--) {
    const sl = c.plan.slices[si];
    let aux = 0;
    for (let k = sl.from; k < sl.to; k++) aux += auxLanes(c.w.segs[k]);
    if (aux > 0) {
      AT = si;
      break;
    }
  }
  console.log(
    `\n[5] the splice is REFUSED at FRI slice ${AT} — in a process that compiled only that slice`,
  );
  const sp = await child({ FRIBRAID_PHASE: 'splice', FRIBRAID_SLICE: String(AT) }, 'splice');
  if (sp.vkHash !== metas[AT].vkHash)
    fail(
      `FRI slice ${AT} compiled to a DIFFERENT verification key in a second process — the circuit ` +
        'is not reproducible, and a pinned key hash means nothing if the key is not a constant',
    );
  ok(
    `FRI slice ${AT} compiles to the SAME verification key in a second, independent process — the ` +
      'pin is a constant, not an accident of one run',
  );
  const SPLICES: [string, string][] = [
    ['unrelatedInput', 'a boundary with no relation to its predecessor'],
    ['accBent', 'the carried AIR ACCUMULATOR bent — the AIR half\'s own result'],
    ['airDigestBent', 'a digest of an AIR column chunk this slice never reads, bent'],
    ['friDigestBent', 'a digest of a FRI lane chunk this slice never reads, bent'],
    ['carryBent', 'one carried live lane bent'],
    ['auxBent', 'one Merkle sibling bent'],
    ['foreignProofAndKey', 'AIR slice 5\'s proof with AIR slice 5\'s OWN key — a valid proof of the wrong program'],
    ['rightProofWrongKey', 'the right proof paired with a key it was not made under'],
  ];
  let attempted = 0;
  for (const [key, label] of SPLICES) {
    const r = sp.results[key];
    if (!r) {
      console.log(`    · ${label}: not attempted at this cut`);
      continue;
    }
    attempted++;
    if (!r.refused) fail(`${label}: ACCEPTED`);
    if (!isConstraintFailure(r.err)) fail(`${label}: the error is not a constraint failure — ${r.err}`);
    ok(`REFUSED: ${label}`);
  }
  if (attempted !== SPLICES.length)
    fail(
      `${SPLICES.length - attempted} splice(s) were NOT ATTEMPTED at this cut — an absent falsifier ` +
        'reads exactly like one that passed, and this table is only worth what it fired',
    );

  // -----------------------------------------------------------------------
  // [6] The controls.
  // -----------------------------------------------------------------------
  console.log('\n[6] the controls — the same slice with ONE binding removed');
  const ctl = await child(
    { FRIBRAID_PHASE: 'control', FRIBRAID_SLICE: String(AT), FRIBRAID_PIN: '1' },
    'control (unbound, pinned)',
  );
  if (!ctl.results.unrelatedInput)
    fail(
      'the UNBOUND control REFUSED a public input unrelated to its predecessor — the control is not ' +
        'testing the binding, and the refusals above are consistent with "the bend broke the work"',
    );
  ok('UNBOUND: a public input with no relation to its predecessor is ACCEPTED');
  if (!ctl.results.airDigestBent)
    fail('the UNBOUND control REFUSED a bend in an AIR chunk digest it never reads');
  ok(
    'UNBOUND: a bent digest of an AIR column chunk the slice never reads is ACCEPTED — so the bound ' +
      'refusal IS the braid biting, not the work breaking',
  );
  if (ctl.results.foreignProofAndKey)
    fail('the UNBOUND-but-PINNED control ACCEPTED a foreign proof — the pin is not what refuses it');
  ok('UNBOUND but PINNED: a foreign proof under its own key is still REFUSED — the refusal is the PIN');
  const ctl2 = await child(
    { FRIBRAID_PHASE: 'control', FRIBRAID_SLICE: String(AT), FRIBRAID_PIN: '0' },
    'control (unbound, unpinned)',
  );
  if (!ctl2.results.foreignProofAndKey)
    fail(
      'the UNPINNED control REFUSED a foreign proof under its own key — then the pin is not what the ' +
        "refusal above is attributable to, and side-loading's named hole is not shown open",
    );
  ok(
    'UNPINNED: the same foreign proof under its own key is ACCEPTED — the hole side-loading opens ' +
      'is REAL, and one constant closes it',
  );

  // -----------------------------------------------------------------------
  // [7] Cost, MEASURED, and the extrapolation kept separate from it.
  // -----------------------------------------------------------------------
  console.log('\n[7] cost');
  console.log(`    ${proved} slices proved in this run, ${N - proved} reused from a prior one`);
  const totC = metas.reduce((a, m) => a + m.compileMs, 0);
  const totP = metas.reduce((a, m) => a + m.proveMs, 0);
  const totR = metas.reduce((a, m) => a + m.rows, 0);
  const totM = metas.reduce((a, m) => a + m.modelRows, 0);
  const perSlice = (totC + totP) / N / 1000;
  console.log(
    `    MEASURED over ${N} slices: ${fmt(totR)} emitted rows (model said ${fmt(totM)}, ` +
      `${(((totR - totM) / totM) * 100).toFixed(1)}%); compile ${(totC / 1000).toFixed(0)}s, ` +
      `prove ${(totP / 1000).toFixed(0)}s; ${perSlice.toFixed(0)}s per slice`,
  );
  const segsDone = c.plan.slices[N - 1].to;
  console.log(
    `    that is segments [0,${fmt(segsDone)}) of ${fmt(c.w.segs.length)} — ` +
      `${((segsDone / c.w.segs.length) * 100).toFixed(2)}% of the walk, PROVED`,
  );
  console.log(
    `    EXTRAPOLATED, and it is an extrapolation: ${fmt(c.plan.slices.length)} slices × ` +
      `${perSlice.toFixed(0)}s = ${((c.plan.slices.length * perSlice) / 3600).toFixed(1)} hours ` +
      'serial, for the whole 19-query walk',
  );
  console.log(`    wall clock for this leg: ${secs(T0)}`);

  console.log('\n[8] RATCHET');
  const RECORDED: [string, number, number][] = [
    ['segments in the walk', c.w.segs.length, RATCHET.segments],
    ['slices in the full plan', c.plan.slices.length, RATCHET.slices],
    ['DEEP terms per query', census.total, RATCHET.deepTerms],
    ['opened values bound to the AIR', c.op.split.air, RATCHET.airBound],
    ['FRI-side lane table', c.ft.nLanes, RATCHET.friLanes],
  ];
  let drifted = 0;
  for (const [label, got, wantN] of RECORDED) {
    if (wantN === 0) {
      console.log(`    · ${label.padEnd(34)} ${fmt(got).padStart(10)} (first recording)`);
      continue;
    }
    const mark = got === wantN ? '✓' : '✗';
    console.log(`    ${mark} ${label.padEnd(34)} ${fmt(got).padStart(10)} (recorded ${fmt(wantN)})`);
    if (got !== wantN) drifted++;
  }
  if (drifted) fail(`${drifted} recorded figure(s) drifted`);
  ok('the recorded figures are as recorded');

  console.log(`\n=== ROOT-FRI-BRAID PASS === ${checks} checks, ${secs(T0)}\n`);
}

/** Recorded on the run that first produced them. A zero prints instead of
 *  comparing. */
const RATCHET = {
  segments: 11_303,
  slices: 839,
  deepTerms: MEASURED_ROOT_GEOMETRY.censusPerQuery,
  airBound: 1_236,
  friLanes: 33_062,
};

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

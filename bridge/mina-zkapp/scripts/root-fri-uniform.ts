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
import { dagDigestOfChunkDigests, digestOfLanes, terminalSeal } from '../src/RootAirChain.js';
import {
  RealRootFri,
  airColumnIndex,
  friLaneTable,
  planFriWalk,
  planOpenedValues,
  rootFriShape,
  segmentWalk,
} from '../src/RootFriWalk.js';
import {
  AIR_CHUNK_LANES,
  AIR_SLICES,
  airLaneValues,
  auxLanes,
  chunkDigestsBigInt,
  friLaneValues,
  walkTwin,
} from '../src/RootFriSlice.js';
import {
  UniformCtx,
  UniformSpec,
  assertHomogeneous,
  auxOf,
  carriedLanes,
  leafOf,
  makeUniformSliceProgram,
  otherQdOf,
  planUniform,
  prevLeaf,
  specName,
  stepIndexOf,
  totalSteps,
  uniformBoundaryIn,
  uniformBoundaryOut,
  uniformFriDigestOf,
  uniformLaneTable,
  uniformLayout,
  uniformShape,
  uniformSlice,
  vkTreePath,
  vkTreeRoot,
} from '../src/RootFriUniform.js';

// ---------------------------------------------------------------------------
// LEG 19 — THE WALK COMPILES ONCE PER POSITION, NOT ONCE PER SLICE.
//
// `docs/MINA-FACING-TERMINAL-OPTIONS.md` §5.1 measured the deployed walk at 839
// slices ⇒ 839 compiles ⇒ 839 verification keys, and 12.6 hours of compile at
// the FRI legs' own measured 53.6 s. It also measured the planner's output —
// `[45,45,45,45,44,…]` — and named the redundancy without drawing it.
//
// This leg draws it. The 19 query blocks are checked to be IDENTICAL (segments,
// modelled rows, and committed lane reads after the per-query shift), the cuts
// are forced onto one repeated grid, and the step index and query index become
// WITNESSES pinned by the chain instead of constants baked into a program name.
//
// ⚑ WHAT IS MEASURED HERE AND WHAT IS EXTRAPOLATED IS KEPT APART. The plan, the
// homogeneity and the row counts are measured on the real geometry with nothing
// compiled. The compile count and wall time are measured by compiling every
// distinct program, one process each. The proofs are measured on as much of the
// chain as a run affords, and the rest is named as unproved.
// ---------------------------------------------------------------------------

const PHASE = process.env.UNIFORM_PHASE ?? 'main';
const NO_CACHE = Cache.None; //  o1js's default prover-key cache aborts with `rust_oom`
const WORK = process.env.FRIBRAID_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const UWORK = process.env.UNIFORM_WORKDIR ?? resolve(WORK, 'uniform');
const BUDGET = Number(process.env.FRIBRAID_BUDGET ?? 50_000);
const CHUNK = Number(process.env.FRIBRAID_CHUNK ?? 256);
/** How many distinct programs to COMPILE in this run; `all` for every one. */
const KEYS_LIMIT = process.env.UNIFORM_KEYS === 'all' ? -1 : Number(process.env.UNIFORM_KEYS ?? 0);
/** How many slice INSTANCES to prove, in chain order (`0` = none). */
const PROVE_LIMIT = Number(process.env.UNIFORM_PROVE ?? 0);
/** Row probes cost an `analyzeMethods` each and compile nothing. */
const ROW_PROBES = process.env.UNIFORM_ROWS !== '0';
const REUSE = process.env.UNIFORM_REUSE !== '0';

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
// The context every process rebuilds deterministically.
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
  if (!existsSync(a)) fail(`${a} is missing — run \`npm run root-air-fullchain\``);
  if (!existsSync(f)) fail(`${f} is missing — run the \`root_fri_instance\` dumper`);
  return { air: JSON.parse(readFileSync(a, 'utf8')), fri: JSON.parse(readFileSync(f, 'utf8')) };
}

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

type Ctx = UniformCtx & {
  airLanes: bigint[];
  friLanes: bigint[];
  twin: ReturnType<typeof walkTwin>;
  dagDigest: Field;
  friDigest: Field;
  friCommit: Field;
  acc: bigint[];
  realAir: RealRootAir;
  deployedSlices: number;
  /** The same query-aligned plan under the DEPLOYED one-level commitment — what
   *  the alignment costs on its own, with nothing else changed. */
  flatSlices: number;
  qds: Field[];
};

function context(): Ctx {
  const { air: realAir, fri: real } = readReal();
  const shape = rootFriShape(real);
  const op = planOpenedValues(shape, airColumnIndex());
  const ftDeployed = friLaneTable(shape, op);
  const w = segmentWalk(shape);
  const L = uniformLayout(w, shape, ftDeployed, CHUNK);
  const ft = uniformLaneTable(shape, ftDeployed, L);
  const plan = planUniform(w, op, ft, L, { usableRows: BUDGET });

  const cols = realColumns(realAir);
  const airLanes = airLaneValues(cols.base, cols.ext);
  //  ⚑ The lane VALUES are filled through the UNIFORM table, so every query's
  //  opened rows land on their own chunk boundary and the padding is zero.
  const friLanes = friLaneValues(real, shape, ft, op);
  const twin = walkTwin(w, shape, ft, op, friLanes, airLanes, real);

  const nAir = airLanes.length / AIR_CHUNK_LANES;
  const dagDigest = dagDigestOfChunkDigests(chunkDigestsBigInt(airLanes, nAir, AIR_CHUNK_LANES));
  const friDigest = uniformFriDigestOf(L, friLanes);
  const friCommit = Poseidon.hash([dagDigest, friDigest]);
  const qds = otherQdOf(L, friLanes);

  const u = unifiedDag(rootAirDag());
  const R = u.roots.length;
  let acc = [0n, 0n, 0n, 0n];
  u.tableSpans.forEach((span, i) => {
    const p3 = cols.pairs[i][1].accumulator.map((x) => BigInt(x));
    acc = eAdd(acc, eMul(p3, ePow(cols.alpha, R - span.rootTo)));
  });

  //  The deployed plan, for the comparison this leg exists to make, and the
  //  query-aligned plan under the deployed commitment, to price the two apart.
  const deployed = planFriWalk(w, op, ftDeployed, { usableRows: BUDGET, chunkLanes: CHUNK });
  const flat = planUniform(w, op, ft, L, { usableRows: BUDGET, flatDigests: true });

  return {
    w,
    shape,
    ft,
    op,
    plan,
    real,
    airLanes,
    friLanes,
    twin,
    dagDigest,
    friDigest,
    friCommit,
    acc,
    realAir,
    deployedSlices: deployed.slices.length,
    flatSlices: flat.totalSlices,
    qds,
  };
}

// ===========================================================================
// The chain, as an ordered list of instances.
// ===========================================================================

type Instance = { sp: UniformSpec; q: number; k: number };

function chainOrder(c: Ctx): Instance[] {
  const out: Instance[] = [];
  for (let p = 0; p < c.plan.head.length; p++)
    out.push({ sp: { kind: 'head', pos: p }, q: 0, k: AIR_SLICES + p });
  for (let q = 0; q < c.plan.layout.numQueries; q++)
    for (let p = 0; p < c.plan.block.length; p++) {
      const sp: UniformSpec = { kind: 'block', pos: p };
      out.push({ sp, q, k: stepIndexOf(c.plan, sp, q) });
    }
  return out;
}

function programList(c: Ctx): UniformSpec[] {
  const out: UniformSpec[] = [];
  for (let p = 0; p < c.plan.head.length; p++) out.push({ kind: 'head', pos: p });
  for (let p = 0; p < c.plan.block.length; p++) out.push({ kind: 'block', pos: p });
  return out;
}

// ===========================================================================
// Artifacts on disk — the ONLY thing that crosses a process.
// ===========================================================================

const U = (n: string) => resolve(UWORK, n);
const keyPath = (sp: UniformSpec) => U(`key-${specName(sp)}.json`);
const proofPath = (sp: UniformSpec, q: number) => U(`proof-${specName(sp)}-q${q}.json`);
const metaPath = (sp: UniformSpec, q: number) => U(`meta-${specName(sp)}-q${q}.json`);
const airVk = () => resolve(WORK, 'vk-6.json');
const airProof = () => resolve(WORK, 'proof-6.json');

const readVk = (p: string): { data: string; hash: string } => JSON.parse(readFileSync(p, 'utf8'));
const vkObject = (v: { data: string; hash: string }) =>
  new VerificationKey({ data: v.data, hash: Field(v.hash) });

/** ⚑ ONE FEATURE-FLAG SETTING FOR THE WHOLE CHAIN, AND IT IS A DECISION.
 *  Position 0 of a query block has TWO possible predecessors — the head's last
 *  slice at q = 0 and the block's last position after that — and a
 *  `DynamicProof` class carries ONE flag set. `allMaybe` is what lets one class
 *  stand for both; it costs verifier-circuit generality and NOT identity, which
 *  the key pin supplies. */
const PREV_FLAGS: FeatureFlags = FeatureFlags.allMaybe;

/** The key list as it stands on disk. Missing programs are `Field(0)` leaves,
 *  which makes a partial run's root a DIFFERENT constant — named, not hidden. */
function keyList(c: Ctx): { hashes: Field[]; known: number; root: Field } {
  const specs = programList(c);
  let known = 0;
  const hashes = specs.map((sp) => {
    if (!existsSync(keyPath(sp))) return Field(0);
    known++;
    return Field(JSON.parse(readFileSync(keyPath(sp), 'utf8')).hash);
  });
  return { hashes, known, root: vkTreeRoot(hashes) };
}

// ===========================================================================
// The witness of one slice instance.
// ===========================================================================

function witnessOf(c: Ctx, sp: UniformSpec, q: number, vkRoot: Field, path: Field[]) {
  const L = c.plan.layout;
  const sh = uniformShape(c, sp);
  const sl = uniformSlice(c.plan, sp);
  const F = (x: bigint) => Field(x);
  const pad = (a: Field[], n: number) => (a.length ? a : [Field(0)]).slice(0, Math.max(n, 1));
  const qBase = L.qBase + q * L.chunksPerQuery * L.chunkLanes;

  const airRead: Field[] = [];
  for (const ch of sl.readsAirChunks)
    for (let i = 0; i < CHUNK; i++) airRead.push(F(c.airLanes[ch * CHUNK + i] ?? 0n));
  const nAirTot = Math.ceil(c.airLanes.length / CHUNK);
  const airOther: Field[] = [];
  for (let ch = 0; ch < nAirTot; ch++)
    if (!sl.readsAirChunks.includes(ch))
      airOther.push(digestOfLanes(c.airLanes.slice(ch * CHUNK, (ch + 1) * CHUNK).map((x) => Field(x))));

  //  ⚑ THE SUBSTITUTION THAT MAKES ONE CIRCUIT SERVE NINETEEN POSITIONS: the
  //  circuit addresses query 0's chunks; the driver hands it query `q`'s lanes.
  const friRead: Field[] = [];
  for (const ch of sl.readsFriChunks) {
    const base = ch < L.nGlobalChunks ? ch * CHUNK : qBase + (ch - L.nGlobalChunks) * CHUNK;
    for (let i = 0; i < CHUNK; i++) friRead.push(F(c.friLanes[base + i] ?? 0n));
  }
  const dig = (base: number) =>
    digestOfLanes(c.friLanes.slice(base, base + CHUNK).map((x) => Field(x ?? 0n)));
  const otherGlobal: Field[] = [];
  for (let ch = 0; ch < L.nGlobalChunks; ch++)
    if (!sh.readsGlobal.includes(ch)) otherGlobal.push(dig(ch * CHUNK));
  const otherQuery: Field[] = [];
  for (let ch = 0; ch < L.chunksPerQuery; ch++)
    if (!sh.readsQuery.includes(ch)) otherQuery.push(dig(qBase + ch * CHUNK));

  const aux = auxOf(c, c.twin, sp, q).map(F);
  return {
    k: Field(stepIndexOf(c.plan, sp, q)),
    q: Field(q),
    vkRoot,
    path,
    acc: BbExt.from(c.acc),
    liveIn: pad(carriedLanes(c, c.twin, sp, q, 'in').map(F), sh.nLiveIn),
    airRead: pad(airRead, sh.nAirRead),
    airOther: pad(airOther, sh.nAirOther),
    friRead: pad(friRead, sh.nFriRead),
    otherGlobal: pad(otherGlobal, sh.nOtherGlobal),
    otherQuery: pad(otherQuery, sh.nOtherQuery),
    otherQd: c.qds,
    aux: pad(aux, sh.nAux),
  };
}

const call = (prog: any, bIn: Field, p: any, vk: VerificationKey, wt: any) =>
  prog.slice(
    bIn,
    p,
    vk,
    wt.k,
    wt.q,
    wt.vkRoot,
    wt.path,
    wt.acc,
    wt.liveIn,
    wt.airRead,
    wt.airOther,
    wt.friRead,
    wt.otherGlobal,
    wt.otherQuery,
    wt.otherQd,
    wt.aux,
  );

function specOfEnv(): UniformSpec {
  const kind = (process.env.UNIFORM_KIND ?? 'head') as 'head' | 'block';
  return { kind, pos: Number(process.env.UNIFORM_POS ?? '0') };
}

// ===========================================================================
// PHASE `rows` — the uniformity cost, measured on the real shape.
// ===========================================================================

async function rowsPhase() {
  const c = context();
  const sp = specOfEnv();
  const airVkHash = BigInt(readVk(airVk()).hash);
  //  ⚑ ONE side-loaded class for all three variants: `DynamicProof.tag()` names
  //  itself off a process-global counter, so a second class would change the
  //  circuit for a reason that has nothing to do with what is being measured.
  const base = makeUniformSliceProgram(c, sp, { prevFlags: PREV_FLAGS, airVkHash });
  const Prev = base.Prev;
  const rowsOf = async (p: any) => ((await p.prog.analyzeMethods()) as any).slice.rows as number;
  const uniform = await rowsOf(base);
  const baked = await rowsOf(
    makeUniformSliceProgram(c, sp, {
      prevFlags: PREV_FLAGS,
      prevClass: Prev,
      airVkHash,
      uniform: false,
      bakedQuery: 0,
    }),
  );
  //  Baked indices AND a compile-time key pin — the DEPLOYED shape, which a ring
  //  cannot have. The difference between this and `baked` is what the key tree
  //  costs; the difference between `baked` and `uniform` is what witnessing the
  //  indices costs.
  const deployedShape = await rowsOf(
    makeUniformSliceProgram(c, sp, {
      prevFlags: PREV_FLAGS,
      prevClass: Prev,
      airVkHash,
      uniform: false,
      bakedQuery: 0,
      constKeyPin: airVkHash,
    }),
  );
  const sh = uniformShape(c, sp);
  console.log(
    `##JSON##${JSON.stringify({
      spec: specName(sp),
      uniform,
      baked,
      deployedShape,
      indexCost: uniform - baked,
      keyTreeCost: baked - deployedShape,
      total: uniform - deployedShape,
      modelRows: sh.sl.workRows + sh.sl.carryRows,
      segFrom: sh.sl.from,
      segTo: sh.sl.to,
    })}`,
  );
}

// ===========================================================================
// PHASE `key` — compile ONE program and record its verification key.
// ===========================================================================

async function keyPhase() {
  const c = context();
  const sp = specOfEnv();
  const airVkHash = BigInt(readVk(airVk()).hash);
  const { prog } = makeUniformSliceProgram(c, sp, { prevFlags: PREV_FLAGS, airVkHash });
  const t0 = Date.now();
  const meta = (await (prog as any).analyzeMethods()) as any;
  const rows = meta.slice.rows as number;
  const analyzeMs = Date.now() - t0;
  const t = Date.now();
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });
  const compileMs = Date.now() - t;
  mkdirSync(UWORK, { recursive: true });
  const out = {
    spec: specName(sp),
    rows,
    analyzeMs,
    compileMs,
    hash: verificationKey.hash.toString(),
    data: verificationKey.data,
  };
  writeFileSync(keyPath(sp), JSON.stringify(out));
  console.log(`##JSON##${JSON.stringify({ ...out, data: undefined })}`);
}

// ===========================================================================
// PHASE `slice` — prove ONE instance.
// ===========================================================================

async function slicePhase() {
  const c = context();
  const sp = specOfEnv();
  const q = Number(process.env.UNIFORM_Q ?? '0');
  const airVkHash = BigInt(readVk(airVk()).hash);
  const { hashes, root } = keyList(c);
  const path = vkTreePath(hashes, prevLeaf(c.plan, sp, q));
  const { prog, Prev } = makeUniformSliceProgram(c, sp, { prevFlags: PREV_FLAGS, airVkHash });

  const t0 = Date.now();
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });
  const compileMs = Date.now() - t0;
  const declared = existsSync(keyPath(sp)) ? readVk(keyPath(sp)).hash : null;
  if (declared !== null && declared !== verificationKey.hash.toString())
    fail(
      `${specName(sp)} compiled to a key that is not the one the chain's key list names — the ` +
        'program is not reproducible and a key tree over it means nothing',
    );

  //  The predecessor: the AIR chain for head 0, the previous position otherwise,
  //  and the previous QUERY's last position at a block's position 0.
  const prevSpec: UniformSpec | null =
    sp.kind === 'head'
      ? sp.pos === 0
        ? null
        : { kind: 'head', pos: sp.pos - 1 }
      : sp.pos > 0
        ? { kind: 'block', pos: sp.pos - 1 }
        : q === 0
          ? { kind: 'head', pos: c.plan.head.length - 1 }
          : { kind: 'block', pos: c.plan.block.length - 1 };
  const prevQ = sp.kind === 'block' && sp.pos === 0 && q > 0 ? q - 1 : q;
  const prevVkFile = prevSpec === null ? airVk() : keyPath(prevSpec);
  const prevProofFile = prevSpec === null ? airProof() : proofPath(prevSpec, prevQ);
  const prevVk = readVk(prevVkFile);

  const wit = witnessOf(c, sp, q, root, path);
  const bIn = uniformBoundaryIn(c, c.twin, sp, q, c.dagDigest, c.friCommit, c.acc, root);
  const t = Date.now();
  const r = await call(
    prog as any,
    bIn,
    await (Prev as any).fromJSON(JSON.parse(readFileSync(prevProofFile, 'utf8'))),
    vkObject(prevVk),
    wit,
  );
  const proveMs = Date.now() - t;
  const verified = await verify(r.proof, verificationKey);
  mkdirSync(UWORK, { recursive: true });
  writeFileSync(proofPath(sp, q), JSON.stringify(r.proof.toJSON()));
  const sl = uniformSlice(c.plan, sp);
  const out = {
    spec: specName(sp),
    q,
    k: stepIndexOf(c.plan, sp, q),
    compileMs,
    proveMs,
    verified,
    vkHash: verificationKey.hash.toString(),
    prevVkHash: prevVk.hash,
    publicInput: r.proof.publicInput.toString(),
    publicOutput: r.proof.publicOutput.toString(),
    modelRows: sl.workRows + sl.carryRows,
  };
  writeFileSync(metaPath(sp, q), JSON.stringify(out));
  console.log(`##JSON##${JSON.stringify(out)}`);
}

// ===========================================================================
// PHASE `splice` / `control`.
// ===========================================================================

async function splicePhase() {
  const c = context();
  const sp = specOfEnv();
  const q = Number(process.env.UNIFORM_Q ?? '0');
  const L = c.plan.layout;
  const airVkHash = BigInt(readVk(airVk()).hash);
  const { hashes, root } = keyList(c);
  const path = vkTreePath(hashes, prevLeaf(c.plan, sp, q));
  const { prog, Prev } = makeUniformSliceProgram(c, sp, { prevFlags: PREV_FLAGS, airVkHash });
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });

  const prevSpec: UniformSpec =
    sp.kind === 'block' && sp.pos === 0
      ? { kind: 'head', pos: c.plan.head.length - 1 }
      : sp.kind === 'block'
        ? { kind: 'block', pos: sp.pos - 1 }
        : { kind: 'head', pos: sp.pos - 1 };
  const prevVk = readVk(keyPath(prevSpec));
  const prevProof = await (Prev as any).fromJSON(
    JSON.parse(readFileSync(proofPath(prevSpec, q), 'utf8')),
  );
  //  ⚑ THE FOREIGN PROOF IS A REAL PROOF OF A REAL PROGRAM UNDER ITS OWN REAL
  //  KEY, made in a different process: the AIR chain's slice 5.
  const foreignVk = readVk(resolve(WORK, 'vk-5.json'));
  const foreignProof = await (Prev as any).fromJSON(
    JSON.parse(readFileSync(resolve(WORK, 'proof-5.json'), 'utf8')),
  );
  //  ⚑ AND A SECOND FOREIGN KEY THAT IS INSIDE THE CHAIN'S OWN KEY LIST but at
  //  the WRONG LEAF — the falsifier a compile-time pin cannot express and a key
  //  tree can. It is the chain's own head slice 0.
  const siblingSpec: UniformSpec = { kind: 'head', pos: 0 };
  const siblingVk = readVk(keyPath(siblingSpec));
  const siblingProof = existsSync(proofPath(siblingSpec, 0))
    ? await (Prev as any).fromJSON(JSON.parse(readFileSync(proofPath(siblingSpec, 0), 'utf8')))
    : null;

  const wit = witnessOf(c, sp, q, root, path);
  const b = uniformBoundaryIn(c, c.twin, sp, q, c.dagDigest, c.friCommit, c.acc, root);

  const results: Record<string, { refused: boolean; err?: string }> = {};
  const attempt = async (name: string, f: () => Promise<unknown>) => {
    try {
      await f();
      results[name] = { refused: false };
    } catch (e) {
      results[name] = { refused: true, err: String((e as Error)?.message ?? e).slice(0, 300) };
    }
  };
  const pv = vkObject(prevVk);

  await attempt('unrelatedInput', () => call(prog as any, Field(0x1234), prevProof, pv, wit));
  await attempt('accBent', () =>
    call(prog as any, b, prevProof, pv, {
      ...wit,
      acc: BbExt.from(c.acc.map((v, i) => (i === 0 ? (v + 1n) % P : v))),
    }),
  );
  await attempt('airDigestBent', () => {
    const bent = wit.airOther.slice();
    bent[0] = bent[0].add(Field(1));
    return call(prog as any, b, prevProof, pv, { ...wit, airOther: bent });
  });
  await attempt('friGlobalDigestBent', () => {
    const bent = wit.otherGlobal.slice();
    bent[0] = bent[0].add(Field(1));
    return call(prog as any, b, prevProof, pv, { ...wit, otherGlobal: bent });
  });
  await attempt('otherQueryDigestBent', () => {
    const bent = wit.otherQd.slice();
    bent[(q + 1) % L.numQueries] = bent[(q + 1) % L.numQueries].add(Field(1));
    return call(prog as any, b, prevProof, pv, { ...wit, otherQd: bent });
  });
  await attempt('carryBent', () => {
    const bent = wit.liveIn.slice();
    bent[0] = bent[0].add(Field(1));
    return call(prog as any, b, prevProof, pv, { ...wit, liveIn: bent });
  });
  if (wit.aux.length > 1)
    await attempt('auxBent', () => {
      const bent = wit.aux.slice();
      bent[0] = bent[0].add(Field(1));
      return call(prog as any, b, prevProof, pv, { ...wit, aux: bent });
    });
  // ---- the falsifiers a WITNESSED index makes possible, and must refuse ----
  await attempt('stepIndexSkipped', () =>
    call(prog as any, b, prevProof, pv, { ...wit, k: wit.k.add(1) }),
  );
  await attempt('stepIndexRepeated', () =>
    call(prog as any, b, prevProof, pv, { ...wit, k: wit.k.sub(1) }),
  );
  if (sp.kind === 'block') {
    await attempt('queryDoubleCounted', () => {
      //  The same k, claiming a DIFFERENT query — the double-count. `k` and `q`
      //  are tied by one equation, so this is the shape a witnessed index has to
      //  refuse and the reason the tie exists.
      const other = (q + 1) % L.numQueries;
      return call(prog as any, b, prevProof, pv, { ...wit, q: Field(other) });
    });
    //  ⚑ THE ONE THE AFFINE TIE CANNOT CATCH, and the reason the boundary is
    //  still doing work: `k + |block|` with `q + 1` SATISFIES `k = f(q)`. It is
    //  this slice replayed one whole query later — the splice a witnessed index
    //  makes available and nothing else in the table reaches. Only the boundary
    //  refuses it, which is exactly what the control below shows.
    await attempt('positionShiftedConsistently', () =>
      call(prog as any, b, prevProof, pv, {
        ...wit,
        k: wit.k.add(c.plan.block.length),
        q: Field(q + 1),
      }),
    );
  }
  await attempt('vkRootBent', () =>
    call(prog as any, b, prevProof, pv, { ...wit, vkRoot: wit.vkRoot.add(1) }),
  );
  await attempt('vkPathBent', () => {
    const bent = wit.path.slice();
    bent[0] = bent[0].add(Field(1));
    return call(prog as any, b, prevProof, pv, { ...wit, path: bent });
  });
  await attempt('foreignProofAndKey', () =>
    call(prog as any, b, foreignProof, vkObject(foreignVk), wit),
  );
  await attempt('rightProofWrongKey', () =>
    call(prog as any, b, prevProof, vkObject(foreignVk), wit),
  );
  if (siblingProof !== null)
    await attempt('inListWrongLeaf', () =>
      //  A key that IS in the chain's key list, at the wrong position, with its
      //  own path. The pin is a LEAF INDEX, not membership.
      call(prog as any, b, siblingProof, vkObject(siblingVk), {
        ...wit,
        path: vkTreePath(hashes, leafOf(c.plan, siblingSpec)),
      }),
    );

  console.log(
    `##JSON##${JSON.stringify({
      spec: specName(sp),
      q,
      vkHash: verificationKey.hash.toString(),
      results,
    })}`,
  );
}

async function controlPhase() {
  const c = context();
  const sp = specOfEnv();
  const q = Number(process.env.UNIFORM_Q ?? '0');
  const pin = process.env.UNIFORM_PIN !== '0';
  const airVkHash = BigInt(readVk(airVk()).hash);
  const { hashes, root } = keyList(c);
  const path = vkTreePath(hashes, prevLeaf(c.plan, sp, q));
  const { prog, Prev } = makeUniformSliceProgram(c, sp, {
    prevFlags: PREV_FLAGS,
    airVkHash,
    bindCarry: false,
    pinVk: pin,
  });
  await prog.compile({ cache: NO_CACHE });

  const prevSpec: UniformSpec =
    sp.kind === 'block' && sp.pos === 0
      ? { kind: 'head', pos: c.plan.head.length - 1 }
      : sp.kind === 'block'
        ? { kind: 'block', pos: sp.pos - 1 }
        : { kind: 'head', pos: sp.pos - 1 };
  const prevVk = readVk(keyPath(prevSpec));
  const prevProof = await (Prev as any).fromJSON(
    JSON.parse(readFileSync(proofPath(prevSpec, q), 'utf8')),
  );
  const foreignVk = readVk(resolve(WORK, 'vk-5.json'));
  const foreignProof = await (Prev as any).fromJSON(
    JSON.parse(readFileSync(resolve(WORK, 'proof-5.json'), 'utf8')),
  );
  const wit = witnessOf(c, sp, q, root, path);
  const b = uniformBoundaryIn(c, c.twin, sp, q, c.dagDigest, c.friCommit, c.acc, root);

  const results: Record<string, boolean> = {};
  const accepts = async (name: string, f: () => Promise<unknown>) => {
    try {
      await f();
      results[name] = true;
    } catch {
      results[name] = false;
    }
  };
  await accepts('unrelatedInput', () =>
    call(prog as any, Field(0x1234), prevProof, vkObject(prevVk), wit),
  );
  await accepts('positionShiftedConsistently', () =>
    call(prog as any, b, prevProof, vkObject(prevVk), {
      ...wit,
      k: wit.k.add(c.plan.block.length),
      q: Field(q + 1),
    }),
  );
  await accepts('foreignProofAndKey', () =>
    call(prog as any, b, foreignProof, vkObject(foreignVk), wit),
  );
  console.log(`##JSON##${JSON.stringify({ spec: specName(sp), q, pin, results })}`);
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
  console.log('\n=== ROOT-FRI-UNIFORM — one circuit per POSITION, not per slice (leg 19) ===\n');
  const T0 = Date.now();
  mkdirSync(UWORK, { recursive: true });
  const c = context();
  const L = c.plan.layout;
  const K = c.shape.knobs;

  // -----------------------------------------------------------------------
  // [1] The homogeneity, CHECKED.
  // -----------------------------------------------------------------------
  console.log('[1] the walk is a head and nineteen identical query blocks — checked, not assumed');
  const h = assertHomogeneous(c.w, c.op, c.ft, L);
  ok(
    `${fmt(L.headSegs)} head segments (${fmt(h.headRows)} modelled rows), then ${K.numQueries} ` +
      `blocks of ${fmt(L.blockSegs)} segments — every block STRUCTURALLY IDENTICAL to query 0's, ` +
      `carrying the same ${fmt(h.rowsPerBlock)} rows, and reading the same committed lanes after ` +
      `the ${fmt(L.qStride)}-lane per-query shift`,
  );
  console.log(
    `    lane table: ${fmt(L.globalLanes)} global lanes + ${K.numQueries} x ${fmt(L.qStride)} ` +
      `opened-row lanes; chunk-aligned per query it is ${fmt(L.nLanes)} lanes in ` +
      `${L.nGlobalChunks} global + ${K.numQueries} x ${L.chunksPerQuery} per-query chunks ` +
      `(${L.nFriChunks} against the deployed table's ${Math.ceil((L.globalLanes + K.numQueries * L.qStride) / CHUNK)})`,
  );

  // -----------------------------------------------------------------------
  // [2] The plan.
  // -----------------------------------------------------------------------
  console.log('\n[2] the cut list, forced onto ONE repeated grid');
  console.log(
    `    ${fmt(c.plan.head.length)} head slices + ${K.numQueries} x ${fmt(c.plan.block.length)} ` +
      `block slices = ${fmt(c.plan.totalSlices)} slice INSTANCES`,
  );
  console.log(
    `    DISTINCT programs, compiles and verification keys: ${fmt(c.plan.distinctPrograms)}  ` +
      `(the deployed walk: ${fmt(c.deployedSlices)})`,
  );
  const carry = (c.plan.totalCarry / (c.plan.totalWork + c.plan.totalCarry)) * 100;
  console.log(
    `    work ${fmt(c.plan.totalWork)} + carry ${fmt(c.plan.totalCarry)} = ` +
      `${fmt(c.plan.totalWork + c.plan.totalCarry)} rows (${carry.toFixed(1)}% carry)`,
  );
  //  ⚑ TWO EFFECTS, PRICED APART. Forcing the cuts onto one grid WASTES slack;
  //  the two-level commitment RECOVERS carry. Quoting the net as either one
  //  would be the laundering this repo has paid for.
  const sign = (n: number) => `${n >= 0 ? '+' : ''}${fmt(n)}`;
  const alignOnly = c.flatSlices - c.deployedSlices;
  const net = c.plan.totalSlices - c.deployedSlices;
  console.log(
    `    ⚑ THE ALIGNMENT SLACK, which §5.1 said was the first thing to price: ` +
      `${sign(alignOnly)} slice instances (${((alignOnly / c.deployedSlices) * 100).toFixed(1)}%) ` +
      'at the DEPLOYED one-level commitment — that is the alignment alone',
  );
  console.log(
    `    ⚑ and the two-level commitment gives ${fmt(c.flatSlices - c.plan.totalSlices)} back, so ` +
      `the NET against the deployed greedy-global plan is ${sign(net)} ` +
      `(${((net / c.deployedSlices) * 100).toFixed(1)}%)`,
  );
  const cRows = c.plan.block.map((s) => s.carryRows);
  console.log(
    `    carry per block slice: min ${fmt(Math.min(...cRows))}  max ${fmt(Math.max(...cRows))}`,
  );

  // -----------------------------------------------------------------------
  // [3] The chain's arithmetic, before anything compiles.
  // -----------------------------------------------------------------------
  console.log('\n[3] the seal AIR slice 6 emitted, recomputed from the uniform FRI side');
  if (!existsSync(airProof())) fail(`${airProof()} is missing — the AIR half has not been proved`);
  const air6 = JSON.parse(readFileSync(airProof(), 'utf8'));
  const want = terminalSeal(c.dagDigest, digestOfLanes(c.acc.map((x) => Field(x))), AIR_SLICES);
  if (air6.publicOutput[0] !== want.toString())
    fail(
      'AIR slice 6\'s publicOutput is not what the uniform FRI side recomputes — the braid would ' +
        'be a coincidence if it matched later',
    );
  ok(
    'the uniform chain enters at AIR slice 6\'s OWN terminal seal, recomputed from the AIR column ' +
      'chunks it loads — the braid and its compile-time key pin are untouched by any of this',
  );
  console.log(
    `    the chain closes at step ${fmt(totalSteps(c.plan))} = ${AIR_SLICES} AIR + ` +
      `${fmt(c.plan.totalSlices)} FRI`,
  );

  // -----------------------------------------------------------------------
  // [3b] THE WHOLE CHAIN'S BOUNDARY ARITHMETIC, OUT OF CIRCUIT.
  //
  // ⚑ THIS IS THE INSTRUMENT A PARTIAL PROOF RUN CANNOT BE, and it is the same
  // argument §3.27's twin makes. A run proves a prefix; the joins this leg
  // actually changes — a block's LAST position handing on to the NEXT query's
  // position 0, and the current-query register moving with it — do not occur
  // until instance 46, and the terminal seal not until 820. Running every
  // boundary here costs seconds and checks all 820.
  // -----------------------------------------------------------------------
  console.log('\n[3b] all 820 boundaries, out of circuit — every join, not the ones a run reaches');
  {
    const order = chainOrder(c);
    const root = keyList(c).root;
    let prevOut = terminalSeal(
      c.dagDigest,
      digestOfLanes(c.acc.map((x) => Field(x))),
      AIR_SLICES,
    ).toString();
    for (const { sp, q, k } of order) {
      const bIn = uniformBoundaryIn(c, c.twin, sp, q, c.dagDigest, c.friCommit, c.acc, root);
      if (bIn.toString() !== prevOut)
        fail(
          `${specName(sp)} at q${q} (step ${k}) enters a boundary its predecessor did not emit — ` +
            'the uniform chain does not join',
        );
      prevOut = uniformBoundaryOut(c, c.twin, sp, q, c.friCommit, c.acc, root).toString();
    }
    const finalOut = order[order.length - 1];
    const seal = uniformBoundaryOut(
      c,
      c.twin,
      finalOut.sp,
      finalOut.q,
      c.friCommit,
      c.acc,
      root,
    ).toString();
    if (seal !== prevOut) fail('the terminal seal is not what the last slice emits');
    ok(
      `every one of ${fmt(order.length)} slice instances enters exactly the boundary its ` +
        'predecessor emits, across all 19 query blocks and both joins the deployed chain does not ' +
        'have — the current-query register moves with the block, and the chain closes on the seal',
    );
  }

  // -----------------------------------------------------------------------
  // [4] The uniformity cost, MEASURED.
  // -----------------------------------------------------------------------
  console.log('\n[4] what uniformity costs, measured on the real shape by building the same cut twice');
  const probes: UniformSpec[] = [
    { kind: 'head', pos: Math.min(1, c.plan.head.length - 1) },
    { kind: 'block', pos: 0 },
    { kind: 'block', pos: Math.min(1, c.plan.block.length - 1) },
    { kind: 'block', pos: c.plan.block.length - 1 },
  ];
  const rowRuns: any[] = [];
  for (const sp of ROW_PROBES ? probes : []) {
    const r = await child(
      { UNIFORM_PHASE: 'rows', UNIFORM_KIND: sp.kind, UNIFORM_POS: String(sp.pos) },
      `rows ${specName(sp)}`,
    );
    rowRuns.push(r);
    console.log(
      `    ${r.spec.padEnd(9)} deployed-shape ${fmt(r.deployedShape).padStart(6)} rows  ` +
        `+ key tree ${String(r.keyTreeCost).padStart(5)}  + witnessed k,q ${String(r.indexCost).padStart(5)}` +
        `  = ${fmt(r.uniform).padStart(6)}  (${((r.total / r.deployedShape) * 100).toFixed(2)}%)`,
    );
    if (r.uniform > 65536 - 4)
      fail(`${r.spec} is ${fmt(r.uniform)} rows — past the Kimchi step domain`);
  }
  if (rowRuns.length) {
    const worst = rowRuns.reduce((a, r) => Math.max(a, r.total), 0);
    ok(
      `the whole uniformity cost is at most ${fmt(worst)} rows a slice — the index witnessing ` +
        `itself is ${rowRuns.map((r) => r.indexCost).join('/')} rows, against §3.20's 11 on its ` +
        'own shape',
    );
  } else console.log('    (skipped: UNIFORM_ROWS=0)');

  // -----------------------------------------------------------------------
  // [5] The compiles.
  // -----------------------------------------------------------------------
  const specs = programList(c);
  const nKeys = KEYS_LIMIT < 0 ? specs.length : Math.min(KEYS_LIMIT, specs.length);
  console.log(
    `\n[5] ${nKeys} of ${specs.length} distinct programs compiled, ONE PROCESS EACH — the ` +
      'verification keys the walk needs',
  );
  const keys: any[] = [];
  let compiled = 0;
  let compileMs = 0;
  for (let i = 0; i < nKeys; i++) {
    const sp = specs[i];
    if (REUSE && existsSync(keyPath(sp))) {
      const k = JSON.parse(readFileSync(keyPath(sp), 'utf8'));
      keys.push(k);
      compileMs += k.compileMs;
      console.log(`    ${k.spec.padEnd(9)} REUSED  ${fmt(k.rows)} rows  vk ${k.hash.slice(0, 12)}…`);
      continue;
    }
    const t = Date.now();
    const k = await child(
      { UNIFORM_PHASE: 'key', UNIFORM_KIND: sp.kind, UNIFORM_POS: String(sp.pos) },
      `key ${specName(sp)}`,
    );
    keys.push(k);
    compiled++;
    compileMs += k.compileMs;
    console.log(
      `    ${k.spec.padEnd(9)} ${fmt(k.rows).padStart(6)} rows  compile ` +
        `${(k.compileMs / 1000).toFixed(1)}s  vk ${k.hash.slice(0, 12)}…  (${secs(t)})`,
    );
  }
  if (nKeys === specs.length) {
    const uniq = new Set(keys.map((k) => k.hash));
    if (uniq.size !== keys.length)
      fail(`two distinct programs compiled to the SAME verification key — ${uniq.size} of ${keys.length}`);
    ok(
      `${keys.length} verification keys for a ${fmt(c.plan.totalSlices)}-slice walk, all distinct — ` +
        `against ${fmt(c.deployedSlices)} keys for the deployed ${fmt(c.deployedSlices)}-slice walk`,
    );
    const perProgram = compileMs / keys.length / 1000;
    console.log(
      `    MEASURED: ${(compileMs / 1000 / 60).toFixed(1)} min of compile for the WHOLE walk ` +
        `(${perProgram.toFixed(1)}s per program, ${compiled} compiled in this run)`,
    );
    console.log(
      `    the deployed walk at the same per-compile rate: ${fmt(c.deployedSlices)} x ` +
        `${perProgram.toFixed(1)}s = ${((c.deployedSlices * perProgram) / 3600).toFixed(1)} hours`,
    );
  }

  // -----------------------------------------------------------------------
  // [6] The proofs.
  // -----------------------------------------------------------------------
  const order = chainOrder(c);
  const nProve = Math.min(PROVE_LIMIT, order.length);
  if (nProve > 0) {
    console.log(`\n[6] ${nProve} of ${fmt(order.length)} slice instances proved, one process each`);
    for (let i = 0; i < nProve; i++) {
      const { sp, q, k } = order[i];
      const t = Date.now();
      if (REUSE && existsSync(metaPath(sp, q))) {
        const m = JSON.parse(readFileSync(metaPath(sp, q), 'utf8'));
        console.log(`    ${m.spec.padEnd(9)} q${String(m.q).padStart(2)} k=${m.k}  REUSED`);
        continue;
      }
      const m = await child(
        {
          UNIFORM_PHASE: 'slice',
          UNIFORM_KIND: sp.kind,
          UNIFORM_POS: String(sp.pos),
          UNIFORM_Q: String(q),
        },
        `slice ${specName(sp)} q${q}`,
      );
      console.log(
        `    ${m.spec.padEnd(9)} q${String(m.q).padStart(2)} k=${String(m.k).padStart(3)}  ` +
          `compile ${(m.compileMs / 1000).toFixed(1)}s  prove ${(m.proveMs / 1000).toFixed(1)}s  ` +
          `${m.verified ? 'VERIFIED' : 'NOT VERIFIED'}  (${secs(t)})`,
      );
      if (!m.verified) fail(`${m.spec} at q${m.q} does not verify under its own key`);
      if (m.k !== k) fail(`${m.spec} at q${m.q} proved at step ${m.k}, not ${k}`);
    }
    // The chain, checked by a process that compiled NOTHING.
    console.log('\n[7] the chain, verified end to end by a process that compiled nothing');
    const { root } = keyList(c);
    for (let i = 0; i < nProve; i++) {
      const { sp, q } = order[i];
      const vk = readVk(keyPath(sp));
      const pj = JSON.parse(readFileSync(proofPath(sp, q), 'utf8'));
      if (!(await verify(pj, vk.data))) fail(`${specName(sp)} q${q} does not verify under its own key`);
      const wantIn = uniformBoundaryIn(c, c.twin, sp, q, c.dagDigest, c.friCommit, c.acc, root);
      if (pj.publicInput[0] !== wantIn.toString())
        fail(`${specName(sp)} q${q}'s publicInput is not the boundary the out-of-circuit twin computed`);
      const wantOut = uniformBoundaryOut(c, c.twin, sp, q, c.friCommit, c.acc, root);
      if (pj.publicOutput[0] !== wantOut.toString())
        fail(`${specName(sp)} q${q}'s publicOutput is not the boundary the twin computed`);
      const prev = i === 0 ? JSON.parse(readFileSync(airProof(), 'utf8')) : null;
      const prevOut =
        i === 0
          ? prev.publicOutput[0]
          : JSON.parse(
              readFileSync(proofPath(order[i - 1].sp, order[i - 1].q), 'utf8'),
            ).publicOutput[0];
      if (pj.publicInput[0] !== prevOut)
        fail(`${specName(sp)} q${q}'s publicInput is not its predecessor's publicOutput`);
    }
    ok(
      `${nProve} proofs verify under their own keys; every step's publicInput IS its ` +
        "predecessor's publicOutput, and step 0's predecessor is AIR SLICE 6",
    );
    //  ⚑ THE MEASUREMENT THE WHOLE LEG IS FOR, when the run reaches it.
    const reused = new Map<string, number[]>();
    for (let i = 0; i < nProve; i++) {
      const { sp, q } = order[i];
      const a = reused.get(specName(sp)) ?? [];
      a.push(q);
      reused.set(specName(sp), a);
    }
    const multi = [...reused.entries()].filter(([, qs]) => qs.length > 1);
    if (multi.length)
      ok(
        `ONE verification key proved at more than one position: ` +
          multi.map(([s, qs]) => `${s} at q${qs.join(',q')}`).join('; '),
      );
    else
      console.log(
        `    ⚠ no program was proved at two queries in this run — reaching a block's position 0 at ` +
          `q=1 needs ${c.plan.head.length + c.plan.block.length + 1} instances`,
      );

    // ---------------------------------------------------------------------
    // [7b] The splices, ACROSS the process boundary.
    //
    // ⚑ SPLICE AT A SLICE THAT CARRIES MERKLE DATA and whose predecessor is
    // proved. A transcript-only slice has no `aux`, so the `auxBent` attempt
    // cannot fire there and the table would quietly report one short — a
    // falsifier that is absent reads exactly like one that passed.
    // ---------------------------------------------------------------------
    let at: Instance | null = null;
    for (let i = nProve - 1; i >= 1; i--) {
      const { sp, q } = order[i];
      const sl = uniformSlice(c.plan, sp);
      let aux = 0;
      for (let k2 = sl.from; k2 < sl.to; k2++) aux += auxLanes(c.w.segs[k2]);
      if (aux > 0) {
        at = order[i];
        break;
      }
    }
    if (at === null) {
      console.log('\n[7b] no proved slice carries Merkle data yet — the splice table is not run');
    } else {
      const env = {
        UNIFORM_KIND: at.sp.kind,
        UNIFORM_POS: String(at.sp.pos),
        UNIFORM_Q: String(at.q),
      };
      console.log(
        `\n[7b] the splice is REFUSED at ${specName(at.sp)} q${at.q} (chain step ${at.k}) — in a ` +
          'process that compiled only that program',
      );
      const sp2 = await child({ ...env, UNIFORM_PHASE: 'splice' }, 'splice');
      const declared = readVk(keyPath(at.sp)).hash;
      if (sp2.vkHash !== declared)
        fail(
          `${specName(at.sp)} compiled to a DIFFERENT verification key in a second process — the ` +
            'circuit is not reproducible, and a key tree over it means nothing',
        );
      ok(
        `${specName(at.sp)} compiles to the SAME verification key in a second, independent ` +
          'process — the key list is a constant, not an accident of one run',
      );
      const SPLICES: [string, string][] = [
        ['unrelatedInput', 'a boundary with no relation to its predecessor'],
        ['accBent', "the carried AIR ACCUMULATOR bent — the AIR half's own result"],
        ['airDigestBent', 'a digest of an AIR column chunk this slice never reads, bent'],
        ['friGlobalDigestBent', 'a digest of a GLOBAL FRI lane chunk this slice never reads, bent'],
        ['otherQueryDigestBent', "ANOTHER QUERY's opened-row digest bent — the two-level commitment"],
        ['carryBent', 'one carried live lane bent'],
        ['auxBent', 'one Merkle sibling bent'],
        ['stepIndexSkipped', '⚑ the witnessed step index k ADVANCED by one — a SKIP'],
        ['stepIndexRepeated', '⚑ the witnessed step index k HELD BACK by one — a DOUBLE-COUNT'],
        ['queryDoubleCounted', '⚑ the same k claiming a DIFFERENT query — the same block walked twice'],
        ['positionShiftedConsistently', '⚑ k AND q shifted together so k = f(q) still HOLDS — this slice replayed one whole query later'],
        ['vkRootBent', 'the carried key-list root bent'],
        ['vkPathBent', "the predecessor key's path bent"],
        ['foreignProofAndKey', "the AIR chain's slice 5 proof with its OWN key — a valid proof of the wrong program"],
        ['rightProofWrongKey', 'the right proof paired with a key it was not made under'],
        ['inListWrongLeaf', "⚑ a key that IS in this chain's key list, at the WRONG LEAF, with its own path"],
      ];
      let attempted = 0;
      for (const [key, label] of SPLICES) {
        const r = sp2.results[key];
        if (!r) {
          console.log(`    · ${label}: not attempted at this cut`);
          continue;
        }
        attempted++;
        if (!r.refused) fail(`${label}: ACCEPTED`);
        if (!isConstraintFailure(r.err))
          fail(`${label}: the error is not a constraint failure — ${r.err}`);
        ok(`REFUSED: ${label}`);
      }
      if (attempted < SPLICES.length - 1)
        fail(
          `${SPLICES.length - attempted} splice(s) were NOT ATTEMPTED at this cut — an absent ` +
            'falsifier reads exactly like one that passed',
        );

      // -------------------------------------------------------------------
      // [7c] The controls — the same slice with ONE binding removed.
      // -------------------------------------------------------------------
      console.log('\n[7c] the controls — the same slice with ONE binding removed');
      const ctl = await child(
        { ...env, UNIFORM_PHASE: 'control', UNIFORM_PIN: '1' },
        'control (unbound, pinned)',
      );
      if (!ctl.results.unrelatedInput)
        fail(
          'the UNBOUND control REFUSED a public input unrelated to its predecessor — the control ' +
            'is not testing the binding, and the refusals above are consistent with "the bend ' +
            'broke the work"',
        );
      ok('UNBOUND: a public input with no relation to its predecessor is ACCEPTED');
      if (!ctl.results.positionShiftedConsistently)
        fail(
          'the UNBOUND control REFUSED k and q shifted TOGETHER — then the boundary is not what ' +
            'refuses a replay at another position, and the k = f(q) tie is being credited with ' +
            'work it does not do',
        );
      ok(
        '⚑ UNBOUND: this slice replayed one whole query later, with k = f(q) still satisfied, is ' +
          'ACCEPTED — so the bound refusal of it is the BOUNDARY CHAIN pinning the position, and ' +
          'the affine tie and the boundary are each shown doing their own half',
      );
      if (ctl.results.foreignProofAndKey)
        fail('the UNBOUND-but-PINNED control ACCEPTED a foreign proof — the pin is not what refuses it');
      ok('UNBOUND but PINNED: a foreign proof under its own key is still REFUSED — the refusal is the PIN');
      const ctl2 = await child(
        { ...env, UNIFORM_PHASE: 'control', UNIFORM_PIN: '0' },
        'control (unbound, unpinned)',
      );
      if (!ctl2.results.foreignProofAndKey)
        fail(
          'the UNPINNED control REFUSED a foreign proof under its own key — then the pin is not ' +
            "what the refusal above is attributable to, and side-loading's named hole is not shown open",
        );
      ok(
        'UNPINNED: the same foreign proof under its own key is ACCEPTED — the hole side-loading ' +
          'opens is REAL on a witnessed-index chain too, and the carried key tree closes it',
      );
    }
  } else {
    console.log('\n[6] no instances proved in this run (UNIFORM_PROVE=0)');
  }

  console.log('\n[8] RATCHET');
  const RECORDED: [string, number, number][] = [
    ['head segments', L.headSegs, RATCHET.headSegs],
    ['segments per query block', L.blockSegs, RATCHET.blockSegs],
    ['head slices', c.plan.head.length, RATCHET.headSlices],
    ['slices per query block', c.plan.block.length, RATCHET.blockSlices],
    ['slice instances', c.plan.totalSlices, RATCHET.totalSlices],
    ['DISTINCT programs / VKs', c.plan.distinctPrograms, RATCHET.distinctPrograms],
    ['deployed slices, for contrast', c.deployedSlices, RATCHET.deployedSlices],
    ['uniform FRI chunks', L.nFriChunks, RATCHET.friChunks],
  ];
  let drifted = 0;
  for (const [label, got, wantN] of RECORDED) {
    if (wantN === 0) {
      console.log(`    · ${label.padEnd(32)} ${fmt(got).padStart(9)} (first recording)`);
      continue;
    }
    const mark = got === wantN ? '✓' : '✗';
    console.log(`    ${mark} ${label.padEnd(32)} ${fmt(got).padStart(9)} (recorded ${fmt(wantN)})`);
    if (got !== wantN) drifted++;
  }
  if (drifted) fail(`${drifted} recorded figure(s) drifted`);
  ok('the recorded figures are as recorded');

  console.log(`\n=== ROOT-FRI-UNIFORM PASS === ${checks} checks, ${secs(T0)}\n`);
}

/** Recorded on the run that first produced them. A zero prints instead of
 *  comparing. */
const RATCHET = {
  headSegs: 36,
  blockSegs: 593,
  headSlices: 3,
  blockSlices: 43,
  totalSlices: 820,
  distinctPrograms: 46,
  deployedSlices: 839,
  friChunks: 138,
};

const phase =
  PHASE === 'rows'
    ? rowsPhase()
    : PHASE === 'key'
      ? keyPhase()
      : PHASE === 'slice'
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

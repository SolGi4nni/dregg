import { execFile } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { relative, resolve } from 'node:path';
import { Cache, FeatureFlags, Field, VerificationKey } from 'o1js';
import { RealRootAir, rootAirDag } from '../src/RootAirDag.js';
import {
  RealRootFri,
  airColumnIndex,
  friLaneTable,
  planOpenedValues,
  rootFriShape,
  rootPreambleMeta,
  segmentWalk,
} from '../src/RootFriWalk.js';
import {
  UniformCtx,
  UniformSpec,
  VK_TREE_DEPTH,
  VK_TREE_LEAVES,
  assertHomogeneous,
  assertLeavesFit,
  leafOf,
  makeUniformSliceProgram,
  planUniform,
  specName,
  totalSteps,
  uniformLaneTable,
  uniformLayout,
  uniformProgramName,
  uniformShape,
  vkTreeRoot,
} from '../src/RootFriUniform.js';
import { claimBindSlice, claimChunks, claimIndex, NUM_CHAIN_CLAIMS } from '../src/RootClaim.js';

// ---------------------------------------------------------------------------
// THE KEY RING — the 131 claim-carrying verification keys, compiled.
//
// ⚑ WHAT THIS IS AND WHY IT DID NOT EXIST. Every leg that needed these keys
// stopped short of minting them, and each stopped for its own good reason, so
// the gap read as a compute budget rather than as missing code:
//
//   * `root-fri-uniform.ts` HAS a one-program-per-process compile driver and it
//     builds the §3.29 shape — `segmentWalk(shape)` with no preamble, no
//     `claim:` ever passed to `makeUniformSliceProgram`. Its 46 keys are a
//     different chain, and `head-anchor-pins` says so.
//   * `root-claim-carry.ts` builds the CLAIM-CARRYING program and only ever
//     calls `analyzeMethods()` — a row measurement — at one position, twice.
//     Nothing in it compiles.
//   * `head-anchor-pins.ts` printed "compiled — 131 programs, one process each
//     — into HEAD_KEYS" as an instruction to a human.
//
// So `.fullchain/uniform-claim/` had never been written by anything. This is
// the driver that writes it.
//
// ⚑ IT REPRODUCES `root-claim-carry`'s CONTEXT, IT DOES NOT RESTATE IT. Same
// calls, same order, same `CLAIM_CHUNK`/`CLAIM_BUDGET` defaults, and the same
// ratchet as a REFUSAL: 905 instances / 131 programs / 912 steps. A plan that
// has drifted fails here rather than emitting keys for a chain nobody built.
//
// ⚑ ONE PROCESS PER PROGRAM, NOT AN OPTIMISATION. `RootFriUniform`'s
// `makePrevProofClass` throws on a second side-loaded class in one process:
// `DynamicProof.tag()` names itself `o1js-sideloaded-${counter}` off a
// process-global counter, so a second class in one process gets an identifier
// that depends on creation ORDER — a verification key that does not reproduce,
// which is the one thing a key-tree pin cannot tolerate.
//
// ⚑ RESUMABLE, AND THE SKIP IS SHAPE-CHECKED. 131 compiles is hours. A key on
// disk is reused only if its recorded SHAPE is the one this run would compile
// (program name, claim geometry, plan counts, private-input widths, the AIR pin
// where it is in circuit, o1js version). A stale key from a different shape is
// RECOMPILED, never trusted — that is the difference between a resume and a
// directory of keys for three different chains.
//
//   npm run uniform-claim-keys              # compile every missing key
//   npm run uniform-claim-keys -- --plan    # enumerate and check, compile nothing
//   CLAIM_KEYS_LIMIT=4 npm run uniform-claim-keys
//
// ⚠ `Cache.None` IS REQUIRED. o1js's default prover-key cache aborts with
// `rust_oom` on bodies this size (the 4 GiB wasm address-space wall). Every
// other leg in this directory sets it for the same reason.
// ---------------------------------------------------------------------------

const PHASE = process.env.CLAIMKEYS_PHASE ?? 'main';
const NO_CACHE = Cache.None;
const WORK = process.env.CLAIM_WORKDIR ?? resolve(process.cwd(), '.fullchain');
/** ⚑ THE SAME NAME `head-anchor-pins` READS (`HEAD_KEYS`), defaulted the same. */
const KEYS = process.env.HEAD_KEYS ?? resolve(WORK, 'uniform-claim');
const BUDGET = Number(process.env.CLAIM_BUDGET ?? 50_000);
const CHUNK = Number(process.env.CLAIM_CHUNK ?? 256);
/** How many MISSING keys to compile in this run; unset = all of them. */
const LIMIT = Number(process.env.CLAIM_KEYS_LIMIT ?? -1);
const PLAN_ONLY = process.argv.includes('--plan');

/** `root-claim-carry`'s ratchet and `head-anchor-pins`'s, restated as a REFUSAL. */
const EXPECT = { instances: 905, programs: 131, steps: 912 };

/** ⚑ ONE FEATURE-FLAG SETTING FOR THE WHOLE CHAIN. A block's position 0 has two
 *  possible predecessors and a `DynamicProof` class carries ONE flag set;
 *  `allMaybe` is what lets one class stand for both. It costs verifier-circuit
 *  generality and NOT identity, which the key pin supplies. */
const PREV_FLAGS: FeatureFlags = FeatureFlags.allMaybe;

const O1JS_VERSION = '2.15.0';

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

// ===========================================================================
// The context — `root-claim-carry`'s, call for call.
// ===========================================================================

function readReal(): { air: RealRootAir; fri: RealRootFri } {
  const a = resolve(WORK, 'real-root-air.json');
  const f = resolve(WORK, 'real-root-fri.json');
  if (!existsSync(a)) fail(`${a} is missing — run \`npm run root-air-fullchain\``);
  if (!existsSync(f))
    fail(
      `${f} is missing — build and run the dumper:\n` +
        '    cargo build -p dregg-circuit-prove --release --bin root_fri_instance\n' +
        `    ./target/release/root_fri_instance ${f}`,
    );
  return { air: JSON.parse(readFileSync(a, 'utf8')), fri: JSON.parse(readFileSync(f, 'utf8')) };
}

type Ctx = UniformCtx & {
  realAir: RealRootAir;
  ix: ReturnType<typeof claimIndex>;
  chunks: number[];
  bindPos: number;
};

function context(): Ctx {
  const { air: realAir, fri: real } = readReal();
  const shape = rootFriShape(real);
  const air = airColumnIndex();
  const meta = rootPreambleMeta(realAir, air);
  //  ⚑ ONE `OpenedPlan` PER LANE TABLE — `friLaneTable` MUTATES `op.refs`.
  const op = planOpenedValues(shape, air);
  //  ⚑ WITH the preamble: 905 / 131 is the §3.30 shape, 820 / 46 is the one
  //  without it, and the one without it is what `.fullchain/uniform` holds.
  const w = segmentWalk(shape, { preamble: meta });
  const ftD = friLaneTable(shape, op);
  const L = uniformLayout(w, shape, ftD, CHUNK);
  const ft = uniformLaneTable(shape, ftD, L);
  assertHomogeneous(w, op, ft, L);
  const plan = planUniform(w, op, ft, L, { usableRows: BUDGET });

  const ix = claimIndex(air);
  const chunks = claimChunks(ix, CHUNK);
  const bindPos = claimBindSlice(plan.head, chunks);
  if (bindPos < 0)
    fail(
      `no head slice loads every AIR chunk the claim lives in (${chunks}) — the seal would have to ` +
        "add a chunk to a slice, which moves the planner's carry and therefore the 905",
    );
  return { w, shape, ft, op, plan, real, realAir, ix, chunks, bindPos };
}

function programList(c: Ctx): UniformSpec[] {
  return [
    ...c.plan.head.map((_, pos) => ({ kind: 'head' as const, pos })),
    ...c.plan.block.map((_, pos) => ({ kind: 'block' as const, pos })),
  ];
}

/** ⚑ THE SEAL IS A COMPILE-TIME FACT AND IT IS ONE POSITION. `assertClaimSeal`
 *  reads the 25 claim lanes out of the AIR chunks the slice ALREADY loads, so
 *  only a slice covering chunks `[17, 18]` can seal at all — every other
 *  position propagates, and its claim is pinned inductively by the carry. */
const sealsAt = (c: Ctx, sp: UniformSpec) => sp.kind === 'head' && sp.pos === c.bindPos;

function optsFor(c: Ctx, sp: UniformSpec, airVkHash: bigint) {
  return {
    prevFlags: PREV_FLAGS,
    airVkHash,
    claim: { ix: c.ix, seals: sealsAt(c, sp), armed: true },
  };
}

// ===========================================================================
// The shape a key file records, and what a resume compares.
// ===========================================================================

/**
 * ⚑ EVERYTHING THE COMPILED CIRCUIT IS A FUNCTION OF, so a key on disk is reused
 * only when re-compiling it would produce the same one. The private-input widths
 * come from `uniformShape`, which is what actually sizes the arrays; the plan
 * counts catch a re-cut; the claim lanes catch a moved `expose_claim`; the AIR
 * pin catches a rotated AIR chain — recorded as `null` where it is not in
 * circuit, because only head slice 0 asserts it and forcing 130 recompiles for a
 * constant they never saw would be a lie about what changed.
 */
type KeyShape = {
  program: string;
  spec: string;
  seals: boolean;
  armed: boolean;
  claimLanes: string;
  airVkHashPinned: string | null;
  prevFlags: string;
  vkTreeDepth: number;
  leaf: number;
  plan: {
    instances: number;
    programs: number;
    steps: number;
    head: number;
    block: number;
    chunk: number;
    budget: number;
  };
  widths: Record<string, number>;
  o1js: string;
};

function shapeOf(c: Ctx, sp: UniformSpec, airVkHash: bigint): KeyShape {
  const sh = uniformShape(c, sp);
  const isHead0 = sp.kind === 'head' && sp.pos === 0;
  return {
    program: uniformProgramName(sp, optsFor(c, sp, airVkHash) as any),
    spec: specName(sp),
    seals: sealsAt(c, sp),
    armed: true,
    claimLanes: c.ix.lanes.join(','),
    airVkHashPinned: isHead0 ? airVkHash.toString() : null,
    prevFlags: 'allMaybe',
    vkTreeDepth: VK_TREE_DEPTH,
    leaf: leafOf(c.plan, sp),
    plan: {
      instances: c.plan.totalSlices,
      programs: c.plan.distinctPrograms,
      steps: totalSteps(c.plan),
      head: c.plan.head.length,
      block: c.plan.block.length,
      chunk: CHUNK,
      budget: BUDGET,
    },
    widths: {
      nLiveIn: sh.nLiveIn,
      nLiveOut: sh.nLiveOut,
      nAirRead: sh.nAirRead,
      nAirOther: sh.nAirOther,
      nFriRead: sh.nFriRead,
      nOtherGlobal: sh.nOtherGlobal,
      nOtherQuery: sh.nOtherQuery,
      nAux: sh.nAux,
    },
    o1js: O1JS_VERSION,
  };
}

const keyPath = (sp: UniformSpec) => resolve(KEYS, `key-${specName(sp)}.json`);

/** A key file is reusable only if it records the shape this run would compile.
 *  Anything else — including no shape at all — is recompiled. */
function reusable(sp: UniformSpec, want: KeyShape): { ok: true; key: any } | { ok: false; why: string } {
  const p = keyPath(sp);
  if (!existsSync(p)) return { ok: false, why: 'absent' };
  let k: any;
  try {
    k = JSON.parse(readFileSync(p, 'utf8'));
  } catch (e) {
    return { ok: false, why: `unreadable (${String((e as Error).message).slice(0, 60)})` };
  }
  if (typeof k?.hash !== 'string' || typeof k?.data !== 'string')
    return { ok: false, why: 'no verification key in the file' };
  if (!k.shape) return { ok: false, why: 'records no shape — from a driver that did not write one' };
  const a = JSON.stringify(k.shape);
  const b = JSON.stringify(want);
  if (a !== b) {
    //  Name the first field that differs, so a re-compile says WHY.
    const ka = k.shape as Record<string, unknown>;
    const kb = want as unknown as Record<string, unknown>;
    const diff =
      Object.keys(kb).find((f) => JSON.stringify(ka[f]) !== JSON.stringify(kb[f])) ?? '(ordering)';
    return {
      ok: false,
      why: `shape differs at \`${diff}\`: has ${JSON.stringify(ka[diff])}, wants ${JSON.stringify(kb[diff])}`,
    };
  }
  return { ok: true, key: k };
}

// ===========================================================================
// PHASE `key` — ONE program, ONE process.
// ===========================================================================

const airVkPath = () => resolve(WORK, 'vk-6.json');

function airVkHashOf(): bigint {
  const p = airVkPath();
  if (!existsSync(p))
    fail(
      `${p} is missing, and head slice 0 pins AIR slice 6's verification key as a COMPILE-TIME\n` +
        '      CONSTANT — without it the braid is unpinned and the chain is not a chain. Mint it:\n' +
        '        npm run build\n' +
        '        for i in 0 1 2 3 4 5 6; do FULLCHAIN_REUSE=1 FULLCHAIN_PHASE=slice FULLCHAIN_SLICE=$i \\\n' +
        '          node --max-old-space-size=16384 dist/scripts/root-air-fullchain.js; done',
    );
  return BigInt(JSON.parse(readFileSync(p, 'utf8')).hash);
}

function specOfEnv(): UniformSpec {
  const kind = (process.env.CLAIMKEYS_KIND ?? 'head') as 'head' | 'block';
  return { kind, pos: Number(process.env.CLAIMKEYS_POS ?? '0') };
}

async function keyPhase() {
  const c = context();
  const sp = specOfEnv();
  const airVkHash = airVkHashOf();
  const shape = shapeOf(c, sp, airVkHash);
  const { prog } = makeUniformSliceProgram(c, sp, optsFor(c, sp, airVkHash));
  const t0 = Date.now();
  const meta = (await (prog as any).analyzeMethods()) as any;
  const rows = meta.slice.rows as number;
  const analyzeMs = Date.now() - t0;
  //  ⚑ THE KIMCHI STEP DOMAIN IS A WALL, NOT A BUDGET. A program past it does
  //  not compile slowly, it does not compile.
  if (rows > 65536 - 4)
    fail(`${specName(sp)} emits ${fmt(rows)} rows — past the Kimchi step domain (65,532)`);
  const t = Date.now();
  const { verificationKey } = await prog.compile({ cache: NO_CACHE });
  const compileMs = Date.now() - t;
  //  ⚑ THE KEY MUST LOAD BACK AS A KEY. A `data` blob that `VerificationKey`
  //  refuses is a file the prove run discovers at instance 1 of 905.
  new VerificationKey({ data: verificationKey.data, hash: verificationKey.hash });
  mkdirSync(KEYS, { recursive: true });
  const out = {
    spec: specName(sp),
    rows,
    analyzeMs,
    compileMs,
    hash: verificationKey.hash.toString(),
    data: verificationKey.data,
    shape,
    compiledAt: new Date().toISOString(),
  };
  writeFileSync(keyPath(sp), JSON.stringify(out));
  console.log(`##JSON##${JSON.stringify({ ...out, data: undefined, shape: undefined })}`);
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
            `the ${label} compile produced no result line${err ? ` (exit: ${err.message})` : ''}\n` +
              `${String(stdout).split('\n').slice(-6).join('\n')}\n${String(stderr).slice(-2500)}`,
          ),
        );
      },
    );
  });
}

// ===========================================================================
// main — the parent.
// ===========================================================================

async function main() {
  console.log('\n=== UNIFORM-CLAIM-KEYS — the 131 claim-carrying verification keys ===\n');
  const T0 = Date.now();
  const c = context();
  const specs = programList(c);
  const T = totalSteps(c.plan);

  // -----------------------------------------------------------------------
  // [1] The plan, checked against the ratchet BEFORE anything compiles.
  // -----------------------------------------------------------------------
  console.log('[1] the chain this run is the key ring of');
  console.log(
    `    instances     ${c.plan.totalSlices} uniform + 7 AIR = ${T} steps  (the \`totalSteps\` pin)`,
  );
  console.log(
    `    programs      ${specs.length}  (${c.plan.head.length} head + ${c.plan.block.length} block)`,
  );
  if (
    c.plan.totalSlices !== EXPECT.instances ||
    specs.length !== EXPECT.programs ||
    T !== EXPECT.steps
  )
    fail(
      `the plan is ${c.plan.totalSlices} instances / ${specs.length} programs / ${T} steps and the ` +
        `ratchet pins ${EXPECT.instances} / ${EXPECT.programs} / ${EXPECT.steps}. The plan moved; ` +
        'keys emitted from it would be the key ring of a chain nobody built.',
    );
  ok(`the plan matches root-claim-carry's ratchet exactly (${EXPECT.instances} / ${EXPECT.programs} / ${EXPECT.steps})`);

  //  ⚑ THE TREE HAS TO HOLD THE RING. `bitsOf` truncates in circuit rather than
  //  refusing, so this is checked once here as well as per-program.
  assertLeavesFit(
    c.plan.distinctPrograms,
    specs.map((sp) => leafOf(c.plan, sp)),
    'the key ring',
  );
  ok(
    `every one of ${specs.length} leaves is inside the depth-${VK_TREE_DEPTH} key tree ` +
      `(${VK_TREE_LEAVES} leaves; the terminal is leaf ${leafOf(c.plan, { kind: 'block', pos: c.plan.block.length - 1 })})`,
  );

  console.log(
    `    claim         ${NUM_CHAIN_CLAIMS} lanes, AIR chunks [${c.chunks}], sealed at ` +
      `head${c.bindPos} — every other position propagates`,
  );
  const sealers = specs.filter((sp) => sealsAt(c, sp));
  if (sealers.length !== 1)
    fail(`${sealers.length} programs would seal the claim — the seal is ONE compile-time position`);
  ok('exactly one program seals the claim; 130 carry it under an equality');

  if (PLAN_ONLY) {
    console.log(`\n=== PLAN ONLY === ${checks} checks, ${secs(T0)}, nothing compiled\n`);
    return;
  }

  // -----------------------------------------------------------------------
  // [2] The compiles, one process each, resumable.
  // -----------------------------------------------------------------------
  const airVkHash = airVkHashOf();
  console.log(
    `\n[2] ${specs.length} programs into ${relative(process.cwd(), KEYS)}, ONE PROCESS EACH\n` +
      `    AIR slice 6's key, pinned by head0: ${airVkHash.toString().slice(0, 18)}…`,
  );
  mkdirSync(KEYS, { recursive: true });

  const keys = new Map<string, any>();
  let reused = 0;
  let compiled = 0;
  let compileMs = 0;
  const todo: UniformSpec[] = [];
  for (const sp of specs) {
    const r = reusable(sp, shapeOf(c, sp, airVkHash));
    if (r.ok) {
      keys.set(specName(sp), r.key);
      compileMs += r.key.compileMs ?? 0;
      reused++;
    } else {
      todo.push(sp);
      if (r.why !== 'absent')
        console.log(`    ${specName(sp).padEnd(9)} RECOMPILE — ${r.why}`);
    }
  }
  console.log(
    `    ${reused} of ${specs.length} keys already on disk at this exact shape; ${todo.length} to compile`,
  );

  const n = LIMIT < 0 ? todo.length : Math.min(LIMIT, todo.length);
  for (let i = 0; i < n; i++) {
    const sp = todo[i];
    const t = Date.now();
    const k = await child(
      { CLAIMKEYS_PHASE: 'key', CLAIMKEYS_KIND: sp.kind, CLAIMKEYS_POS: String(sp.pos) },
      `key ${specName(sp)}`,
    );
    keys.set(k.spec, k);
    compiled++;
    compileMs += k.compileMs;
    const done = reused + compiled;
    const rate = compiled ? (Date.now() - T0) / compiled : 0;
    console.log(
      `    [${String(done).padStart(3)}/${specs.length}] ${k.spec.padEnd(9)} ${fmt(k.rows).padStart(6)} rows  ` +
        `compile ${(k.compileMs / 1000).toFixed(1)}s  vk ${k.hash.slice(0, 12)}…  (${secs(t)}` +
        `, eta ${(((n - i - 1) * rate) / 60000).toFixed(0)}m)`,
    );
  }

  // -----------------------------------------------------------------------
  // [3] The ring, and the root it gives.
  // -----------------------------------------------------------------------
  if (keys.size !== specs.length) {
    console.log(
      `\n    ◌ ${specs.length - keys.size} of ${specs.length} keys still missing — re-run to continue ` +
        '(this driver resumes; a key is reused only at its recorded shape)',
    );
    console.log(`\n=== INCOMPLETE === ${checks} checks, ${secs(T0)}\n`);
    process.exit(2);
  }
  const hashes = specs.map((sp) => Field(keys.get(specName(sp))!.hash));
  const uniq = new Set(hashes.map((h) => h.toString()));
  if (uniq.size !== hashes.length)
    fail(
      `two distinct programs compiled to the SAME verification key — ${uniq.size} of ${hashes.length}. ` +
        'A key tree cannot tell those two positions apart and the ring is not a ring.',
    );
  ok(`${hashes.length} verification keys, all distinct`);
  const root = vkTreeRoot(hashes);
  const terminal: UniformSpec = { kind: 'block', pos: c.plan.block.length - 1 };
  console.log(
    `\n    chainVkRoot    ${root.toBigInt()}\n` +
      `    terminalVkHash ${keys.get(specName(terminal))!.hash}   (${specName(terminal)}, leaf ${leafOf(c.plan, terminal)})`,
  );
  const rows = specs.map((sp) => keys.get(specName(sp))!.rows as number);
  console.log(
    `    rows           ${fmt(Math.min(...rows))} … ${fmt(Math.max(...rows))} ` +
      `(mean ${fmt(rows.reduce((a, b) => a + b, 0) / rows.length)}), Kimchi domain 65,532`,
  );
  console.log(
    `    compile        ${(compileMs / 1000 / 60).toFixed(1)} min total ` +
      `(${(compileMs / specs.length / 1000).toFixed(1)}s per program; ${compiled} compiled here, ${reused} reused)`,
  );
  console.log(
    '\n    next:  HEAD_KEYS=' + relative(process.cwd(), KEYS) + ' npm run head-anchor-pins -- --emit',
  );
  console.log(`\n=== UNIFORM-CLAIM-KEYS PASS === ${checks} checks, ${secs(T0)}\n`);
}

const phase = PHASE === 'key' ? keyPhase() : main();
phase.catch((e) => {
  console.error(e);
  process.exit(1);
});

import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { Cache, Field, Poseidon, Provable, ZkProgram, verify } from 'o1js';
import { permBigInt } from '../src/Poseidon2BabyBearW16.js';
import { RealRootAir, bindRealInstance, rootAirDag, DagTable, RealInstance } from '../src/RootAirDag.js';
import { digestOfLanes } from '../src/RootAirChain.js';
import {
  AbsorbRef,
  PreOp,
  PreambleMeta,
  RealRootFri,
  SegmentedWalk,
  airColumnIndex,
  assertPreambleSealLanes,
  friLaneTable,
  permChalAssignment,
  planFriWalk,
  planOpenedValues,
  preambleOps,
  rootFriShape,
  rootPreambleMeta,
  segmentWalk,
} from '../src/RootFriWalk.js';
import {
  AIR_CHUNK_LANES,
  FriBraidCtx,
  airLaneValues,
  auxLanes,
  chunkDigestsBigInt,
  chunkedCommitment,
  friLaneValues,
  friSliceShape,
  runSegments,
  walkTwin,
} from '../src/RootFriSlice.js';
import { dagDigestOfChunkDigests } from '../src/RootAirChain.js';

// ---------------------------------------------------------------------------
// LEG 19 — THE PREAMBLE: the challenger state entering FRI, DERIVED.
//
// §3.28 closes the braid and names what it does not close: "the challenger state
// entering FRI is a committed WITNESS (`friDigest` covers it), emitted by the
// Rust side. That is §3.14 residual 1 and it is now the largest thing between
// this chain and a verifier."
//
// It is the same shape rung 6 closed one level down. Before `DeepQuotient` the
// fold chain started from a value the prover chose; binding it turned the walk
// from "authenticates a number" into "authenticates a claim". A prover who picks
// the challenger state picks FRI's α, all 16 βs and all 19 query indices, and
// the 11,303-segment walk then authenticates a transcript nobody forced.
//
// ⚑ THE DIFFERENTIAL LEADS AND THE CIRCUIT CONFIRMS. Phase [1] runs the whole
// batch-STARK preamble out of circuit against p3's own α, ζ and challenger
// state, and phase [2] requires every plausible misreading of the script to land
// somewhere else. Both run in seconds. Four silent wrongs in this arc were found
// exactly this way and none of them would have been found by a slice run.
// ---------------------------------------------------------------------------

const PHASE = process.env.FRIPRE_PHASE ?? 'all';
const WORK = process.env.FRIPRE_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const OUT = (n: string) => resolve(WORK, `pre-${n}`);
const BUDGET = Number(process.env.FRIPRE_BUDGET ?? 50_000);
const CHUNK = Number(process.env.FRIPRE_CHUNK ?? 256);
/** How many preamble slices this run actually compiles and proves. The rest is a
 *  rate multiplied out, and it is labelled as one. */
const LIMIT = Number(process.env.FRIPRE_LIMIT ?? 2);
const NO_CACHE = Cache.None;

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
const eqA = (a: (bigint | number)[], b: (bigint | number)[]) =>
  a.length === b.length && a.every((x, i) => BigInt(x) === BigInt(b[i]));

/** ⚑ EVERY CAUGHT ERROR MUST BE A CONSTRAINT FAILURE. §3.28's rule, verbatim: a
 *  `TypeError` from a mis-shaped argument inside a bare `catch {}` is
 *  indistinguishable from a real refusal, and that is what makes a splice table
 *  a green that measures the harness. */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read|ENOENT/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|Bool\.assertTrue/i.test(m);
}

// ===========================================================================
// The context.
// ===========================================================================

function readReal(): { air: RealRootAir; fri: RealRootFri } {
  const a = resolve(WORK, 'real-root-air.json');
  const f = resolve(WORK, 'real-root-fri.json');
  //  ⚑ MISSING TOOLCHAIN IS A FAILURE, NOT A SKIP.
  if (!existsSync(a)) fail(`${a} is missing — run \`npm run root-air-fullchain\``);
  if (!existsSync(f))
    fail(
      `${f} is missing — build and run the dumper:\n` +
        '    cargo build -p dregg-circuit-prove --release --bin root_fri_instance\n' +
        `    ./target/release/root_fri_instance ${f}`,
    );
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
  return { base, ext };
}

type Ctx = FriBraidCtx & {
  meta: PreambleMeta;
  airLanes: bigint[];
  friLanes: bigint[];
  twin: ReturnType<typeof walkTwin>;
  realAir: RealRootAir;
  realFri: RealRootFri;
  /** The segment index the FRI transcript starts at — one past `preSeal`. */
  friFrom: number;
};

/** `bind` false = the walk as §3.28 left it: NO preamble, the challenger state
 *  read straight out of `ft.chalState` as a witness. `seal` false = the preamble
 *  with its closing equalities removed and everything else identical. */
function context(opts: { bind: boolean; seal?: boolean }): Ctx {
  const { air: realAir, fri: realFri } = readReal();
  const shape = rootFriShape(realFri);
  const airIx = airColumnIndex();
  const op = planOpenedValues(shape, airIx);
  const ft = friLaneTable(shape, op);
  assertPreambleSealLanes(shape, ft);
  const meta = rootPreambleMeta(realAir, airIx);
  const w = segmentWalk(shape, opts.bind ? { preamble: meta, seal: opts.seal } : {});
  const plan = planFriWalk(w, op, ft, { usableRows: BUDGET, chunkLanes: CHUNK });

  const cols = realColumns(realAir);
  const airLanes = airLaneValues(cols.base, cols.ext);
  const friLanes = friLaneValues(realFri, shape, ft, op);
  const twin = walkTwin(w, shape, ft, op, friLanes, airLanes, realFri);
  const friFrom = opts.bind ? w.segs.findIndex((s) => s.t === 'preSeal') + 1 : 0;
  return { w, shape, ft, op, plan, meta, airLanes, friLanes, twin, realAir, realFri, friFrom };
}

// ===========================================================================
// [1] THE DIFFERENTIAL — the derived state against p3's own.
// ===========================================================================

/** Run the preamble op list on a plain `DuplexChallenger`, from the all-zero
 *  sponge, resolving every absorb against the two lane tables. This is the twin
 *  the circuit is compared to; `segmentWalk` cuts the SAME op list into duplex
 *  segments, so agreement between the two is agreement about the cutting. */
function runOps(
  ops: PreOp[],
  ctx: Ctx,
): { sponge: bigint[]; inBuf: bigint[]; outBuf: bigint[]; perms: number; samples: Map<string, bigint> } {
  const P = 2013265921n;
  const RATE = 8;
  const W = 16;
  let state = new Array<bigint>(W).fill(0n);
  let inBuf: bigint[] = [];
  let outBuf: bigint[] = [];
  let perms = 0;
  const samples = new Map<string, bigint>();
  const duplexing = () => {
    for (let i = 0; i < inBuf.length; i++) state[i] = inBuf[i];
    inBuf = [];
    state = permBigInt(state);
    perms++;
    outBuf = state.slice(0, RATE);
  };
  const value = (a: AbsorbRef): bigint => {
    switch (a.src) {
      case 'shape':
        return BigInt(a.v);
      case 'roundCommit':
        return ctx.friLanes[ctx.ft.inputCommit[a.round] + a.lane];
      case 'publicValue':
        return ctx.airLanes[a.at * 4];
      case 'cumSum':
        return ctx.airLanes[a.at * 4 + a.lane];
      case 'opened': {
        const r = ctx.op.refs[a.round][a.mat][a.point][a.col];
        return r.where === 'air' ? ctx.airLanes[r.at * 4 + a.lane] : ctx.friLanes[r.at + a.lane];
      }
      default:
        throw new Error(`runOps: ${a.src} is not a preamble source`);
    }
  };
  for (const op of ops) {
    if (op.t === 'observe') {
      outBuf = [];
      inBuf.push(((value(op.a) % P) + P) % P);
      if (inBuf.length === RATE) duplexing();
    } else {
      if (inBuf.length > 0 || outBuf.length === 0) duplexing();
      const v = outBuf.pop()!;
      const s = op.s;
      if (s.dst !== 'permChal' && s.dst !== 'airAlpha' && s.dst !== 'zeta')
        throw new Error(`runOps: ${s.dst} is not a preamble destination`);
      const key = s.dst === 'permChal' ? `permChal${s.i}.${s.lane}` : `${s.dst}.${s.lane}`;
      samples.set(key, v);
    }
  }
  return { sponge: state, inBuf, outBuf, perms, samples };
}

function differential(ctx: Ctx) {
  console.log('\n[1] THE DIFFERENTIAL — the whole batch-STARK preamble, out of circuit\n');
  const ops = preambleOps(ctx.shape, ctx.meta);
  const nObs = ops.filter((o) => o.t === 'observe').length;
  const nSmp = ops.length - nObs;
  const r = runOps(ops, ctx);
  const want = ctx.realFri.challengerStateBeforeFriAlpha;

  console.log(
    `    the script: ${fmt(ops.length)} ops — ${fmt(nObs)} observes, ${fmt(nSmp)} samples, ` +
      `${fmt(r.perms)} permutations`,
  );
  const ext = (p: string) => [0, 1, 2, 3].map((l) => r.samples.get(`${p}.${l}`)!);
  const got = { airAlpha: ext('airAlpha'), zeta: ext('zeta') };

  if (!eqA(got.airAlpha, ctx.realFri.airAlpha))
    fail(`derived α_stark ${got.airAlpha} ≠ p3's ${ctx.realFri.airAlpha}`);
  ok(`α_stark  = p3's own  [${got.airAlpha.join(', ')}]`);
  if (!eqA(got.zeta, ctx.realFri.zeta)) fail(`derived ζ ${got.zeta} ≠ p3's ${ctx.realFri.zeta}`);
  ok(`ζ        = p3's own  [${got.zeta.join(', ')}]`);
  if (!eqA(r.sponge, want.sponge)) fail('the derived sponge state is not the one p3 entered verify_fri with');
  ok(`sponge   = p3's own, all 16 lanes  [${want.sponge.slice(0, 3).join(', ')}, ...]`);
  if (!eqA(r.inBuf, want.inputBuffer)) fail(`input buffer: derived ${r.inBuf.length} lanes, p3 ${want.inputBuffer.length}`);
  if (!eqA(r.outBuf, want.outputBuffer))
    fail(`output buffer: derived ${r.outBuf.length} lanes, p3 ${want.outputBuffer.length}`);
  ok(
    `buffers  = p3's own — input EMPTY, output FULL (${want.outputBuffer.length}). ⚑ That is why ` +
      "`verify_fri` draws α by POPPING, with no permutation.",
  );

  //  The LogUp challenges, against the ones the AIR chain folded with.
  const { base } = permChalAssignment(ctx.meta);
  let nChal = 0;
  ctx.realAir.instances.forEach((inst, i) => {
    (base[i] ?? []).forEach((b, j) => {
      for (let c = 0; c < ctx.meta.challengesPerLookup; c++) {
        const used = (inst as any).permChallenges[ctx.meta.challengesPerLookup * j + c] as number[];
        const drew = [0, 1, 2, 3].map((l) => r.samples.get(`permChal${b + c}.${l}`)!);
        if (!eqA(drew, used))
          fail(`instance ${i} lookup ${j} challenge ${c}: derived [${drew}] ≠ the AIR chain's [${used}]`);
        nChal++;
      }
    });
  });
  ok(`${nChal} LogUp challenges = the ones the AIR half folds with (${permChalAssignment(ctx.meta).total} distinct, one bus)`);
  return r;
}

// ===========================================================================
// [2] THE DISCRIMINATING POLARITIES.
// ===========================================================================

type Variant = { name: string; f: (ops: PreOp[], ctx: Ctx) => PreOp[] };

/** Every one of these is a reading a careful person could arrive at. The table
 *  fails if ANY of them reaches the same state, because a script that survives
 *  only because nobody tried to falsify it is not a finding. */
const VARIANTS: Variant[] = [
  {
    name: 'commitments in PCS-ROUND order, not transcript order',
    //  p3 absorbs main, preprocessed, permutation, quotient. `coms_to_verify` is
    //  built main, quotient, preprocessed, permutation — and IS the order the
    //  opened values are absorbed in. Reading one for the other is the single
    //  most plausible error in the whole script.
    f: (ops) => {
      const rc = ops.filter((o) => o.t === 'observe' && o.a.src === 'roundCommit') as PreOp[];
      const order = [0, 1, 2, 3];
      const byRound = new Map<number, PreOp[]>();
      for (const o of rc) {
        const r = (o as any).a.round as number;
        (byRound.get(r) ?? byRound.set(r, []).get(r)!).push(o);
      }
      //  swap the 2nd and 4th commitment BLOCKS in the script
      const slots: number[] = [];
      ops.forEach((o, i) => o.t === 'observe' && o.a.src === 'roundCommit' && slots.push(i));
      const out = ops.slice();
      const blocks = [slots.slice(0, 8), slots.slice(8, 16), slots.slice(16, 24), slots.slice(24, 32)];
      const vals = blocks.map((b) => b.map((i) => ops[i]));
      const perm = [0, 2, 3, 1];
      blocks.forEach((b, bi) => b.forEach((i, j) => (out[i] = vals[perm[bi]][j])));
      void order;
      void byRound;
      return out;
    },
  },
  {
    name: 'observe_usize as ONE base element, not [v,0,0,0]',
    f: (ops) => ops.filter((o) => !(o.t === 'observe' && o.a.src === 'shape' && /#pad/.test(o.a.what))),
  },
  {
    name: 'instance binding fields in a different order',
    f: (ops) => {
      const out = ops.slice();
      const idx: number[] = [];
      ops.forEach((o, i) => o.t === 'observe' && o.a.src === 'shape' && /^inst\d+\.(logExtDegree|logDegree|width|numQuotientChunks)$/.test(o.a.what) && idx.push(i));
      //  (ext_db, base_db, width, n_chunks) -> (width, n_chunks, ext_db, base_db), per instance
      for (let i = 0; i + 15 < idx.length; i += 16) {
        const g = idx.slice(i, i + 16).map((j) => ops[j]);
        const re = [...g.slice(8, 16), ...g.slice(0, 8)];
        idx.slice(i, i + 16).forEach((j, k) => (out[j] = re[k]));
      }
      return out;
    },
  },
  {
    name: 'a fresh challenge pair per LOOKUP, not per BUS',
    f: (ops, ctx) => {
      const nLookups = ctx.meta.lookupBuses.reduce((a, l) => a + l.length, 0);
      const extra: PreOp[] = [];
      for (let k = 1; k < nLookups; k++)
        for (let c = 0; c < ctx.meta.challengesPerLookup; c++)
          for (let l = 0; l < 4; l++) extra.push({ t: 'sample', s: { dst: 'permChal', i: 0, lane: l } });
      const at = ops.findIndex((o) => o.t === 'sample' && o.s.dst === 'permChal');
      return [...ops.slice(0, at), ...ops.slice(at, at + 8), ...extra, ...ops.slice(at + 8)];
    },
  },
  {
    name: 'public values BEFORE the main commitment',
    f: (ops) => {
      const first = ops.findIndex((o) => o.t === 'observe' && o.a.src === 'roundCommit');
      const pv = ops.filter((o) => o.t === 'observe' && o.a.src === 'publicValue');
      const rest = ops.filter((o) => !(o.t === 'observe' && o.a.src === 'publicValue'));
      const at = rest.findIndex((o) => o.t === 'observe' && o.a.src === 'roundCommit');
      void first;
      return [...rest.slice(0, at), ...pv, ...rest.slice(at)];
    },
  },
  {
    name: 'cumulative sums BEFORE the permutation commitment',
    f: (ops) => {
      const cs = ops.filter((o) => o.t === 'observe' && o.a.src === 'cumSum');
      const rest = ops.filter((o) => !(o.t === 'observe' && o.a.src === 'cumSum'));
      //  the permutation commitment is the 3rd `roundCommit` block
      const slots: number[] = [];
      rest.forEach((o, i) => o.t === 'observe' && o.a.src === 'roundCommit' && slots.push(i));
      const at = slots[16];
      return [...rest.slice(0, at), ...cs, ...rest.slice(at)];
    },
  },
  {
    name: 'opened values in TRANSCRIPT round order, not PCS order',
    f: (ops) => {
      const head = ops.filter((o) => !(o.t === 'observe' && o.a.src === 'opened'));
      const op2 = ops.filter((o) => o.t === 'observe' && o.a.src === 'opened') as PreOp[];
      const order = [0, 2, 3, 1];
      const sorted = op2
        .slice()
        .sort((a, b) => order.indexOf((a as any).a.round) - order.indexOf((b as any).a.round));
      return [...head, ...sorted];
    },
  },
  {
    name: 'opened values POINT-major within a round',
    f: (ops) => {
      const head = ops.filter((o) => !(o.t === 'observe' && o.a.src === 'opened'));
      const op2 = ops.filter((o) => o.t === 'observe' && o.a.src === 'opened') as PreOp[];
      const sorted = op2
        .slice()
        .sort(
          (a: any, b: any) =>
            a.a.round - b.a.round || a.a.point - b.a.point || a.a.mat - b.a.mat || a.a.col - b.a.col || a.a.lane - b.a.lane,
        );
      return [...head, ...sorted];
    },
  },
];

function polarities(ctx: Ctx, ref: ReturnType<typeof runOps>) {
  console.log('\n[2] THE DISCRIMINATING POLARITIES — every plausible misreading must land elsewhere\n');
  const ops = preambleOps(ctx.shape, ctx.meta);
  let same = 0;
  for (const v of VARIANTS) {
    let r: ReturnType<typeof runOps> | undefined;
    try {
      r = runOps(v.f(ops, ctx), ctx);
    } catch (e) {
      fail(`variant "${v.name}" threw instead of producing a state: ${(e as Error).message}`);
    }
    if (r === undefined) return fail(`variant "${v.name}" produced no state`);
    const sponge = eqA(r.sponge, ref.sponge) && eqA(r.inBuf, ref.inBuf) && eqA(r.outBuf, ref.outBuf);
    const zeta = eqA([0, 1, 2, 3].map((l) => r.samples.get(`zeta.${l}`)!), [0, 1, 2, 3].map((l) => ref.samples.get(`zeta.${l}`)!));
    if (sponge) same++;
    console.log(
      `    ${v.name.padEnd(54)} ζ ${zeta ? 'SAME' : 'diff'}  state ${sponge ? 'SAME' : 'diff'}  ` +
        `${fmt(r.perms)} perms`,
    );
  }
  if (same > 0) fail(`${same} misreading(s) reach the SAME challenger state — the script is not pinned by this table`);
  ok(`all ${VARIANTS.length} misreadings land on a different challenger state`);
}

// ===========================================================================
// [3] THE COST.
// ===========================================================================

function cost(bound: Ctx, unbound: Ctx) {
  console.log('\n[3] THE COST — what deriving the state adds to the walk\n');
  const pre = bound.w.segs.slice(0, bound.friFrom);
  const perms = pre.filter((s) => s.t === 'duplex' && s.perm).length;
  const preRows = pre.reduce((a, s) => a + s.rows, 0);
  const dRows = bound.w.totalRows - unbound.w.totalRows;
  const dSegs = bound.w.segs.length - unbound.w.segs.length;
  console.log(
    `    preamble segments ${fmt(pre.length)}  (${fmt(perms)} permutations + 1 closing equality)`,
  );
  console.log(`    preamble rows     ${fmt(preRows)}   ⚑ ${((preRows / bound.w.totalRows) * 100).toFixed(1)}% of the whole walk`);
  console.log(`    walk WITHOUT it   ${fmt(unbound.w.segs.length)} segments, ${fmt(unbound.w.totalRows)} rows, ${fmt(unbound.plan.slices.length)} slices`);
  console.log(`    walk WITH it      ${fmt(bound.w.segs.length)} segments, ${fmt(bound.w.totalRows)} rows, ${fmt(bound.plan.slices.length)} slices`);
  console.log(
    `    ⇒ delta           +${fmt(dSegs)} segments, +${fmt(dRows)} rows, ` +
      `+${fmt(bound.plan.slices.length - unbound.plan.slices.length)} slices at a ${fmt(BUDGET)}-row budget`,
  );
  //  §3.12 measured the FRI transcript alone at 62,637 rows / 23 permutations.
  console.log(
    `\n    for scale: the FRI transcript this authorises is 23 permutations (§3.12, 62,637 rows). ` +
      `The preamble is ${(perms / 23).toFixed(0)}× that, and 1,315 of its ${fmt(perms)} permutations ` +
      'are the opened-value absorb alone.',
  );
  return { perms, preRows, dRows };
}

// ===========================================================================
// [4] THE CIRCUIT — the state DERIVED, and the row delta that says so.
// ===========================================================================

function programFor(ctx: Ctx, si: number, tag: string) {
  const { w, shape, ft, op, plan } = ctx;
  const sl = plan.slices[si];
  const sh = friSliceShape(ctx, si);
  const CL = plan.chunkSize;
  const arr = (n: number) => Provable.Array(Field, Math.max(n, 1));
  const prog = ZkProgram({
    name: `dregg-root-fri-preamble-${si}-${tag}`,
    publicInput: Field,
    publicOutput: Field,
    methods: {
      slice: {
        privateInputs: [arr(sh.nLiveIn), arr(sh.nAirRead), arr(sh.nAirOther), arr(sh.nFriRead), arr(sh.nFriOther), arr(sh.nAux)],
        async method(
          bIn: Field,
          liveIn: Field[],
          airLanes: Field[],
          airOther: Field[],
          friLanes: Field[],
          friOther: Field[],
          aux: Field[],
        ) {
          const dagDigest = chunkedCommitment(plan.nAirChunks, CL, sl.readsAirChunks, airLanes.slice(0, sh.nAirRead), airOther.slice(0, sh.nAirOther));
          const friDigest = chunkedCommitment(plan.nFriChunks, CL, sl.readsFriChunks, friLanes.slice(0, sh.nFriRead), friOther.slice(0, sh.nFriOther));
          //  ⚑ The slice is ABOUT the committed lane tables: forging a lane
          //  changes this, so a forger must present the forged commitment. That
          //  is what makes the forged transcript a consistent object rather than
          //  a malformed one.
          Poseidon.hash([dagDigest, friDigest]).assertEquals(bIn);
          const sto = new Map<number, Field>();
          w.liveIn[sl.from].forEach((slot, i) => sto.set(slot, liveIn[i]));
          runSegments(w, shape, ft, op, plan, si, sto, {
            airLanes: airLanes.slice(0, sh.nAirRead),
            airOther: airOther.slice(0, sh.nAirOther),
            friLanes: friLanes.slice(0, sh.nFriRead),
            friOther: friOther.slice(0, sh.nFriOther),
            aux: aux.slice(0, sh.nAux),
          });
          return { publicOutput: digestOfLanes(w.liveIn[sl.to].map((s) => sto.get(s)!)) };
        },
      },
    },
  });
  return prog;
}

function witnessOf(c: Ctx, si: number) {
  const sl = c.plan.slices[si];
  const sh = friSliceShape(c, si);
  const CL = c.plan.chunkSize;
  const pad = (a: Field[], n: number) => (a.length ? a : [Field(0)]).slice(0, Math.max(n, 1));
  const airRead: Field[] = [];
  for (const ch of sl.readsAirChunks) for (let i = 0; i < CL; i++) airRead.push(Field(c.airLanes[ch * CL + i] ?? 0n));
  const nAirTot = c.plan.nAirChunks;
  const airOther: Field[] = [];
  for (let ch = 0; ch < nAirTot; ch++)
    if (!sl.readsAirChunks.includes(ch))
      airOther.push(digestOfLanes(c.airLanes.slice(ch * CL, (ch + 1) * CL).map((x) => Field(x))));
  const friRead: Field[] = [];
  for (const ch of sl.readsFriChunks) for (let i = 0; i < CL; i++) friRead.push(Field(c.friLanes[ch * CL + i] ?? 0n));
  const friOther: Field[] = [];
  for (let ch = 0; ch < c.plan.nFriChunks; ch++)
    if (!sl.readsFriChunks.includes(ch))
      friOther.push(digestOfLanes(c.friLanes.slice(ch * CL, (ch + 1) * CL).map((x) => Field(x))));
  const aux: Field[] = [];
  for (let k = sl.from; k < sl.to; k++) for (const v of c.twin.aux[k]) aux.push(Field(v));
  const dagDigest = dagDigestOfChunkDigests(chunkDigestsBigInt(c.airLanes, Math.ceil(c.airLanes.length / AIR_CHUNK_LANES), AIR_CHUNK_LANES));
  void dagDigest;
  const dag = dagDigestOfChunkDigests(chunkDigestsBigInt(c.airLanes, c.plan.nAirChunks, CL));
  const fri = dagDigestOfChunkDigests(chunkDigestsBigInt(c.friLanes, c.plan.nFriChunks, CL));
  return {
    bIn: Poseidon.hash([dag, fri]),
    liveIn: pad(c.twin.carry[sl.from].map(Field), sh.nLiveIn),
    airRead: pad(airRead, sh.nAirRead),
    airOther: pad(airOther, sh.nAirOther),
    friRead: pad(friRead, sh.nFriRead),
    friOther: pad(friOther, sh.nFriOther),
    aux: pad(aux, sh.nAux),
  };
}

async function rowsOf(ctx: Ctx, si: number, tag: string) {
  const prog = programFor(ctx, si, tag);
  const meta = (await (prog as any).analyzeMethods()) as any;
  return { prog, rows: meta.slice.rows as number, gates: meta.slice.gates };
}

// ===========================================================================
// [5] THE FORGERY — a DIFFERENT but internally consistent transcript.
// ===========================================================================

/** Bend ONE absorbed input and re-derive the whole preamble honestly from it.
 *  The result is a perfectly self-consistent transcript of a batch-STARK that
 *  is not this one: the state is reachable, ζ and α_stark and the LogUp
 *  challenges all follow from it, and nothing about it is malformed. */
function forge(ctx: Ctx): { airLanes: bigint[]; friLanes: bigint[]; bentAt: number } {
  const airLanes = ctx.airLanes.slice();
  const friLanes = ctx.friLanes.slice();
  //  A public value: `expose_claim|public[0]`, a lane of the AIR chain's OWN
  //  committed assignment that the preamble absorbs and the walk otherwise
  //  never reads.
  const g = airColumnIndex().byLabel.get('expose_claim|public[0]');
  if (g === undefined) return fail('the AIR legend does not name `expose_claim|public[0]`');
  const bentAt = g * 4;
  airLanes[bentAt] = (airLanes[bentAt] + 1n) % 2013265921n;
  //  Re-derive the state the forged batch really reaches, and write it into
  //  `chalState` so the UNBOUND walk gets a consistent transcript too.
  const r = runOps(preambleOps(ctx.shape, ctx.meta), { ...ctx, airLanes, friLanes });
  r.sponge.forEach((v, i) => (friLanes[ctx.ft.chalState + i] = v));
  //  And write the forged ζ back into every matrix's point-0 lanes, so the
  //  forgery is consistent with what the proof CLAIMS it was opened at.
  const zeta = [0, 1, 2, 3].map((l) => r.samples.get(`zeta.${l}`)!);
  ctx.shape.rounds.forEach((rd, ri) =>
    rd.matrices.forEach((_, mi) => zeta.forEach((v, l) => (friLanes[ctx.ft.z[ri][mi][0] + l] = v))),
  );
  return { airLanes, friLanes, bentAt };
}

// ===========================================================================

async function main() {
  mkdirSync(WORK, { recursive: true });
  console.log('\n=== LEG 19 — THE CHALLENGER STATE ENTERING FRI, DERIVED ===');
  const bound = context({ bind: true });
  const unbound = context({ bind: false });
  console.log(
    `\n    vk ${bound.realFri.vkFingerprint.slice(0, 16)}...  degree_bits [${bound.realFri.degreeBits}]  ` +
      `${bound.meta.instances.length} instances`,
  );

  const ref = differential(bound);
  polarities(bound, ref);
  const c = cost(bound, unbound);

  //  The twin's own seal check — the preamble's closing equality, out of circuit.
  const zc = bound.twin.checks.filter((k) => k.kind === 'preSealZeta');
  const cc = bound.twin.checks.filter((k) => k.kind === 'preSealChal');
  for (const k of [...zc, ...cc])
    if (!eqA(k.got, k.want!)) fail(`the preamble seal disagrees out of circuit: ${k.kind}[${k.q}] ${k.got} vs ${k.want}`);
  ok(`the seal holds out of circuit: ζ against all ${zc.length} committed matrices, ${cc.length} challenge lanes`);

  if (PHASE === 'plan') {
    console.log(`\n=== ${checks} checks passed (plan only) ===\n`);
    return;
  }

  // ---- [4] the circuit ----------------------------------------------------
  console.log('\n[4] THE CIRCUIT — compiled, and the row delta that says DERIVED\n');
  const sealSliceIx = bound.plan.slices.findIndex((sl) => {
    for (let k = sl.from; k < sl.to; k++) if (bound.w.segs[k].t === 'preSeal') return true;
    return false;
  });
  //  ⚑ THE SEAL SLICE IS ALWAYS IN THE LIST. A run that measures only the cheap
  //  head would report a cost and never touch the segment that refuses.
  const want = process.env.FRIPRE_SLICES
    ? process.env.FRIPRE_SLICES.split(',').map(Number)
    : [...Array.from({ length: Math.max(LIMIT, 0) }, (_, i) => i), sealSliceIx];
  const list = [...new Set(want)].filter((i) => i >= 0 && i < bound.plan.slices.length);
  const rowsB: number[] = [];
  for (const si of list) {
    const t = Date.now();
    const { prog, rows } = await rowsOf(bound, si, 'bound');
    console.log(
      `    slice ${si}: segments [${bound.plan.slices[si].from}, ${bound.plan.slices[si].to}) — ` +
        `${fmt(rows)} EMITTED rows (model ${fmt(bound.plan.slices[si].workRows + bound.plan.slices[si].carryRows)}), ` +
        `${((Date.now() - t) / 1000).toFixed(1)}s to analyze`,
    );
    rowsB.push(rows);
    if (process.env.FRIPRE_PROVE === '1') {
      const t2 = Date.now();
      const { verificationKey } = await prog.compile({ cache: NO_CACHE });
      const wit = witnessOf(bound, si);
      const r = await (prog as any).slice(wit.bIn, wit.liveIn, wit.airRead, wit.airOther, wit.friRead, wit.friOther, wit.aux);
      const okv = await verify(r.proof, verificationKey);
      if (!okv) fail(`slice ${si} produced a proof that does not verify`);
      ok(`slice ${si} compiled, proved and verified in ${((Date.now() - t2) / 1000).toFixed(1)}s`);
      writeFileSync(OUT(`meta-${si}.json`), JSON.stringify({ si, rows, publicOutput: r.proof.publicOutput.toString() }));
    }
  }
  ok(`${list.length} preamble slices analyzed (including the seal slice ${sealSliceIx}); ${fmt(rowsB.reduce((a, b) => a + b, 0))} emitted rows`);
  console.log(
    `    ⚑ ROW COUNT IS THE ONLY SIGNAL FOR "DERIVED, NOT WITNESSED". A derived variable is\n` +
      `      indistinguishable from a witness carrying its value to runAndCheck, prove AND\n` +
      `      getRows(). The unbound walk reaches the same challenger state in ZERO rows because\n` +
      `      it reads it; this one pays ${fmt(c.preRows)} modelled rows to compute it.`,
  );

  // ---- [5] the forgery ----------------------------------------------------
  console.log('\n[5] THE FORGERY — a different but internally consistent transcript\n');
  const f = forge(bound);
  const forgedBound: Ctx = { ...bound, airLanes: f.airLanes, friLanes: f.friLanes };
  forgedBound.twin = walkTwin(bound.w, bound.shape, bound.ft, bound.op, f.friLanes, f.airLanes, bound.realFri);
  const fz = forgedBound.twin.checks.find((k) => k.kind === 'preSealZeta')!;
  console.log(`    bent AIR lane ${f.bentAt} (\`expose_claim|public[0]\`, +1) and re-derived the whole preamble`);
  console.log(`    the forged ζ  [${fz.got.join(', ')}]`);
  console.log(`    the real ζ    [${bound.realFri.zeta.join(', ')}]`);
  if (eqA(fz.got, bound.realFri.zeta)) fail('the forged transcript reaches the SAME ζ — the forgery is a no-op');
  ok('the forged transcript is a DIFFERENT transcript, and internally consistent by construction');

  //  The unsealed control: identical segments, identical rows, seal removed.
  const unsealed = context({ bind: true, seal: false });
  if (unsealed.w.segs.length !== bound.w.segs.length || Math.abs(unsealed.w.totalRows - bound.w.totalRows) > 0)
    fail(
      `the unsealed control has ${unsealed.w.segs.length} segments / ${unsealed.w.totalRows} rows and the ` +
        `bound walk has ${bound.w.segs.length} / ${bound.w.totalRows} — a control that differs in shape ` +
        'explains a refusal by shape',
    );
  ok('the unsealed control is segment-for-segment and row-for-row identical to the bound walk');

  const sealSlice = bound.plan.slices.findIndex((sl) => {
    for (let k = sl.from; k < sl.to; k++) if (bound.w.segs[k].t === 'preSeal') return true;
    return false;
  });
  if (sealSlice < 0) fail('no slice contains the preamble seal');
  console.log(`    the seal falls in slice ${sealSlice} of ${bound.plan.slices.length}`);

  if (process.env.FRIPRE_FORGE === '1') {
    const forgedUnsealed: Ctx = { ...unsealed, airLanes: f.airLanes, friLanes: f.friLanes };
    forgedUnsealed.twin = walkTwin(unsealed.w, unsealed.shape, unsealed.ft, unsealed.op, f.friLanes, f.airLanes, unsealed.realFri);
    //  ⚑ AND THE WALK AS §3.28 LEFT IT, ON THE SAME FORGED STATE. Slice 0 of the
    //  unbound walk is the FRI transcript's entry: it reads `ft.chalState`
    //  straight out of the lane table and draws α from it. The forgery wrote the
    //  forged sponge there, so this row is §3.14 residual 1 exhibited rather
    //  than described — a prover who picks the state picks every challenge, and
    //  the circuit has no opinion about it.
    const forgedUnbound: Ctx = { ...unbound, airLanes: f.airLanes, friLanes: f.friLanes };
    forgedUnbound.twin = walkTwin(unbound.w, unbound.shape, unbound.ft, unbound.op, f.friLanes, f.airLanes, unbound.realFri);
    const pairs: [string, Ctx, number, boolean][] = [
      ['BOUND    (seal armed)    forged transcript', forgedBound, sealSlice, false],
      ['UNSEALED (seal removed)  forged transcript', forgedUnsealed, sealSlice, true],
      ['BOUND    (seal armed)    REAL transcript', bound, sealSlice, true],
      ['UNBOUND  (§3.28 walk)    forged CHALLENGER STATE', forgedUnbound, 0, true],
    ];
    for (const [label, cx, whichSlice, expectAccept] of pairs) {
      const sealSliceLocal = whichSlice;
      const wit = witnessOf(cx, sealSliceLocal);
      let accepted = true;
      let why = '';
      try {
        await Provable.runAndCheck(async () => {
          const sto = new Map<number, Field>();
          const sl = cx.plan.slices[sealSliceLocal];
          const sh = friSliceShape(cx, sealSliceLocal);
          void sh;
          cx.w.liveIn[sl.from].forEach((slot, i) => sto.set(slot, Provable.witness(Field, () => wit.liveIn[i])));
          //  ⚑ SLICED TO THE REAL WIDTHS, NOT THE PADDED ONES. `witnessOf` pads
          //  every array to at least 1 because o1js has no zero-length
          //  `Provable.Array`; handing the padding to `runSegments` trips its
          //  aux-length check, which throws a HARNESS error that reads exactly
          //  like a refusal. The first run of this table "refused" on the bound
          //  side and died on the control side for that reason.
          runSegments(cx.w, cx.shape, cx.ft, cx.op, cx.plan, sealSliceLocal, sto, {
            airLanes: wit.airRead.slice(0, sh.nAirRead).map((v) => Provable.witness(Field, () => v)),
            airOther: wit.airOther.slice(0, sh.nAirOther),
            friLanes: wit.friRead.slice(0, sh.nFriRead).map((v) => Provable.witness(Field, () => v)),
            friOther: wit.friOther.slice(0, sh.nFriOther),
            aux: wit.aux.slice(0, sh.nAux).map((v) => Provable.witness(Field, () => v)),
          });
        });
      } catch (e) {
        accepted = false;
        why = String((e as Error).message).split('\n')[0].slice(0, 120);
        if (!isConstraintFailure(e))
          fail(`${label} failed with a HARNESS error, not a constraint failure: ${why}`);
      }
      const good = accepted === expectAccept;
      console.log(`    ${good ? '✓' : '✗'} ${label.padEnd(46)} slice ${String(sealSliceLocal).padStart(3)}  ${accepted ? 'ACCEPTED' : 'REFUSED '}${why ? ` — ${why}` : ''}`);
      if (!good) fail(`${label}: expected ${expectAccept ? 'accept' : 'refusal'}`);
      checks++;
    }
    ok('the refusal is ATTRIBUTABLE: the same forged transcript is accepted with the seal removed');
    ok('and the walk WITHOUT the preamble accepts the forged challenger state outright — residual 1, exhibited');
  } else {
    console.log('    (set FRIPRE_FORGE=1 to run the three-way accept/refuse table in circuit)');
  }

  console.log(`\n=== ${checks} checks passed ===\n`);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});

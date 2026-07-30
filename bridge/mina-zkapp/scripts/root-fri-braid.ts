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
  Segment,
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

// ── THE CUT-RULE FIGURES, RECORDED ───────────────────────────────────────────
// Measured 2026-07-30 on the deployed 839-slice plan at the root's real
// geometry. `[2c]` re-measures and compares them on EVERY run including tier 0,
// and `recorded-constants.tsv` pins them, so neither the measurement nor the
// figure can move alone.
/** Cuts in the full plan that CONSUME at least one witnessed Merkle sibling. */
const RECORDED_CUTS_WITH_AUX = 489;
/** …and of those, the ones that also CLOSE the round their FIRST sibling feeds
 *  — the only cuts at which a bent sibling has something to fail against. */
const RECORDED_CUTS_ATTRIBUTING = 330;
/** The `block9` shape: carries siblings, contains a closer, and that closer is
 *  for a DIFFERENT round or sits BEFORE the siblings. ZERO on this geometry —
 *  which is a property of the DEPLOYED SLICING, not of the rule. If the slicing
 *  changes and this shape appears, the figure drifts and the leg goes red. */
const RECORDED_CUTS_STRAY_CLOSER = 0;
/** The first cut that can attribute a bent sibling. `FRIBRAID_LIMIT` must reach
 *  past it for `[5]`'s `auxBent` row to be more than a stated reason. */
const RECORDED_FIRST_ATTRIBUTING_CUT = 11;
/** How many of `[5]`'s eight falsifiers are ATTRIBUTABLE at the cut the default
 *  budget can reach. Seven: every one but `auxBent`, whose first attributing cut
 *  is slice 11 and this run proves four. */
const RECORDED_SPLICES_ATTRIBUTED = 7;

/** ⚑ THE SPLICE CUT IS PART OF THE EXPERIMENT, NOT OF THE BUDGET. `[5]` chooses
 *  it explicitly (see THE CUT RULE below) and PRINTS the choice; this forces it
 *  instead, for a lane that wants a named cut rather than the best one. */
const FORCE_AT = process.env.FRIBRAID_SPLICE_AT;
/** ⚑ THE FLOOR THAT MAKES NARROWING VISIBLE. `[5]`'s result is three-valued, so
 *  a smaller run no longer goes red — it goes QUIETER, attributing fewer of the
 *  eight falsifiers. That is exactly the failure the third value could create,
 *  so the count has a floor: a run that attributes fewer than this must SAY so
 *  by lowering it, in the invocation, where a reader can see it. */
const MIN_ATTRIBUTED = Number(process.env.FRIBRAID_MIN_ATTRIBUTED ?? RECORDED_SPLICES_ATTRIBUTED);

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
// THE CUT RULE — where in the walk a falsifier can be ATTRIBUTED at all.
// ===========================================================================
//
// ⚑ A SPLICE TABLE IS WORTH THE CUT IT WAS TAKEN AT, AND FOR HALF OF THESE
// FALSIFIERS THE CUT DECIDES WHETHER THE ATTEMPT MEANS ANYTHING. §3.27's
// original rule — cut at "the last proved slice that consumes a witnessed
// sibling" — selects on the presence of the WITNESS (`aux > 0`), and what
// refuses a BENT sibling is the ASSERTION THAT CLOSES OVER IT: the
// `cur == commitment` of that sibling's OWN round, which can be several cuts
// later. The uniform-walk lane measured the coarse rule wrong at two positions
// for two different reasons:
//
//   * `block7` — 56 aux lanes, seven `inLevel` steps, NO closer at all. A bent
//     sibling only changes the digest the slice hands on; the first
//     `cur == commitment` is three cuts later. ACCEPTED, and correctly.
//   * `block9` — HAS a closer, and it closes the PREVIOUS round, before any of
//     this slice's own siblings are consumed. ACCEPTED, and correctly, again.
//     "Contains a closer" is NECESSARY AND NOT SUFFICIENT.
//
// ⚑ THE CORRECTED RULE, implemented here: a cut can attribute a bent sibling iff
// it contains a closer for the SAME round (or the same fold layer) as its FIRST
// aux-consuming segment, POSITIONED AFTER that segment. Anywhere else an ACCEPT
// IS CORRECT BEHAVIOUR BY THE CIRCUIT — so asserting a refusal is a FALSE RED
// and dropping the attempt is an ABSENT FALSIFIER READING AS A PASS. Both are
// wrong, which is why the result is THREE-VALUED: refused / accepted / NOT
// ATTRIBUTABLE, with the reason, counted, and floored.
//
// The rule is not only about siblings. Three more of the eight are properties of
// the cut and not of the circuit, and `attribution()` states each one:
//   * `friDigestBent` at cut 0 — cut 0 enters `airTerminalSeal(dagDigest, …)`,
//     which does not close over `friCommit`. The bend changes only the boundary
//     this cut HANDS ON, and its SUCCESSOR is what refuses it.
//   * `carryBent` at cut 0 — the walk starts there and carries nothing in.
//   * `airDigestBent` / `friDigestBent` at a cut that READS every chunk — there
//     is then no unread chunk whose digest could be bent.

/** The segments that CLOSE a witnessed digest — `cur == commitment` for an input
 *  round, for a fold layer, or the final-polynomial landing. */
function closerTag(s: Segment): string | null {
  if (s.t === 'inRoot') return `r${s.round}`;
  if (s.t === 'cpRoot') return `L${s.r}`;
  if (s.t === 'final') return 'final';
  return null;
}

/** The segments that CONSUME a witnessed sibling, tagged by what would close it. */
function auxTag(s: Segment): string | null {
  if (s.t === 'inLevel') return `r${s.round}`;
  if (s.t === 'cpLevel' || s.t === 'cpLeaf') return `L${s.r}`;
  return null;
}

type CutProfile = {
  si: number;
  from: number;
  to: number;
  head: string;
  /** aux lanes this cut consumes. */
  aux: number;
  /** the round/layer of its FIRST sibling, or null when it consumes none. */
  tag: string | null;
  /** the SAME-round closer positioned AFTER that first sibling, if any. */
  closer: string | null;
  /** a closer that is present and does NOT qualify — the `block9` shape. */
  stray: string | null;
  nLiveIn: number;
  nAirOther: number;
  nFriOther: number;
};

function cutProfile(c: Ctx, si: number): CutProfile {
  const sl = c.plan.slices[si];
  let aux = 0;
  let firstAuxAt = -1;
  let tag: string | null = null;
  for (let k = sl.from; k < sl.to; k++) {
    const a = auxLanes(c.w.segs[k], c.w.hash);
    aux += a;
    if (a > 0 && firstAuxAt < 0) {
      firstAuxAt = k;
      tag = auxTag(c.w.segs[k]);
    }
  }
  let closer: string | null = null;
  let stray: string | null = null;
  if (firstAuxAt >= 0) {
    //  A closer BEFORE the first sibling is the `block9` shape by construction:
    //  it closed a round this cut's own siblings do not feed.
    for (let k = sl.from; k < firstAuxAt && stray === null; k++) {
      const t = closerTag(c.w.segs[k]);
      if (t !== null) stray = `${c.w.segs[k].t} ${t} (BEFORE the siblings)`;
    }
    for (let k = firstAuxAt + 1; k < sl.to; k++) {
      const t = closerTag(c.w.segs[k]);
      if (t === null) continue;
      if (t === tag || t === 'final') {
        closer = `${c.w.segs[k].t} ${t}`;
        break;
      }
      if (stray === null) stray = `${c.w.segs[k].t} ${t} (a DIFFERENT round)`;
    }
  }
  const sh = friSliceShape(c, si);
  return {
    si,
    from: sl.from,
    to: sl.to,
    head: c.w.segs[sl.from].t,
    aux,
    tag,
    closer,
    stray: closer === null ? stray : null,
    nLiveIn: sh.nLiveIn,
    nAirOther: sh.nAirOther,
    nFriOther: sh.nFriOther,
  };
}

/** ⚑ THE THIRD VALUE, DERIVED FROM THE CUT AND NOT FROM THE RESULT. This is
 *  computed BEFORE the child runs, so "not attributable" is a PREDICTION the
 *  harness commits to, not an excuse it reaches for after seeing an accept. A
 *  falsifier predicted attributable and then accepted is a hard red. */
function attribution(key: string, p: CutProfile): { can: boolean; why: string } {
  switch (key) {
    case 'unrelatedInput':
    case 'accBent':
      return { can: true, why: 'the entered boundary is asserted in every cut body' };
    case 'foreignProofAndKey':
    case 'rightProofWrongKey':
      return { can: true, why: 'the key pin and `prev.verify` are in every cut body' };
    case 'airDigestBent':
      return p.nAirOther > 0
        ? { can: true, why: `${p.nAirOther} AIR chunks are unread here and enter dagDigest` }
        : { can: false, why: 'this cut READS every AIR chunk — there is no unread chunk to bend' };
    case 'friDigestBent':
      if (p.si === 0)
        return {
          can: false,
          why:
            'cut 0 enters `airTerminalSeal(dagDigest, digest(acc))`, which does NOT close over ' +
            'friCommit — the bend moves only the boundary this cut HANDS ON, and its successor is ' +
            'what refuses it (and [4] checks that boundary out of circuit)',
        };
      return p.nFriOther > 0
        ? { can: true, why: `${p.nFriOther} FRI chunks are unread here and enter friCommit` }
        : { can: false, why: 'this cut READS every FRI chunk — there is no unread chunk to bend' };
    case 'carryBent':
      return p.nLiveIn > 0
        ? { can: true, why: `${p.nLiveIn} live lanes are carried in and are under the entered boundary` }
        : { can: false, why: 'the walk STARTS at this cut — it carries no live lane in to bend' };
    case 'auxBent':
      if (p.aux === 0)
        return { can: false, why: 'this cut consumes no witnessed Merkle sibling at all' };
      if (p.closer === null)
        return {
          can: false,
          why:
            `this cut consumes ${p.aux} sibling lanes of ${p.tag} and contains no closer for ${p.tag} ` +
            `after them${p.stray ? ` — only ${p.stray}` : ''}; the first \`cur == commitment\` they ` +
            'feed is in a LATER cut, so an accept here is correct behaviour by the circuit',
        };
      return { can: true, why: `this cut CLOSES the ${p.closer} its own first sibling feeds` };
    default:
      throw new Error(`no attribution rule for splice '${key}' — every falsifier needs one`);
  }
}

/** The rule applied to the WHOLE plan, out of circuit and in milliseconds. This
 *  is the deliverable figure: how many of the braid's cuts can attribute a
 *  bent Merkle sibling at all. */
function cutCensus(c: Ctx) {
  let withAux = 0;
  let attributing = 0;
  let stray = 0;
  let firstAux = -1;
  let firstAttributing = -1;
  for (let si = 0; si < c.plan.slices.length; si++) {
    const p = cutProfile(c, si);
    if (p.aux === 0) continue;
    withAux++;
    if (firstAux < 0) firstAux = si;
    if (p.closer !== null) {
      attributing++;
      if (firstAttributing < 0) firstAttributing = si;
    } else if (p.stray !== null) stray++;
  }
  return { withAux, attributing, stray, firstAux, firstAttributing };
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

  //  ⚑ EVERY FALSIFIER GETS AN ENTRY, INCLUDING THE ONES THAT CANNOT BE APPLIED
  //  HERE. A bend of a witness lane this cut does not HAVE is sliced away in
  //  circuit and would prove cleanly for a reason that has nothing to do with
  //  the braid — a guaranteed accept carrying no information. Those are declared
  //  `noop`, with the witness width that makes them one, instead of being left
  //  out: an absent key and an inapplicable one are the same silence, and the
  //  driver refuses a table with a hole in it.
  const sh = friSliceShape(c, si);
  const results: Record<string, { refused?: boolean; err?: string; noop?: string }> = {};
  const attempt = async (name: string, f: () => Promise<unknown>) => {
    try {
      await f();
      results[name] = { refused: false };
    } catch (e) {
      results[name] = { refused: true, err: String((e as Error)?.message ?? e).slice(0, 300) };
    }
  };
  const attemptIf = async (name: string, wide: number, what: string, f: () => Promise<unknown>) => {
    if (wide > 0) return attempt(name, f);
    results[name] = { noop: `this cut has no ${what} — the bend is sliced away in circuit` };
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
  await attemptIf('airDigestBent', sh.nAirOther, 'unread AIR chunk', () => {
    const bent = wit.airOther.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, vkObject(prevVk), { ...wit, airOther: bent });
  });
  await attemptIf('friDigestBent', sh.nFriOther, 'unread FRI chunk', () => {
    const bent = wit.friOther.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, vkObject(prevVk), { ...wit, friOther: bent });
  });
  await attemptIf('carryBent', sh.nLiveIn, 'carried live lane', () => {
    const bent = wit.liveIn.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, vkObject(prevVk), { ...wit, liveIn: bent });
  });
  await attemptIf('auxBent', sh.nAux, 'witnessed Merkle sibling', () => {
    const bent = wit.aux.slice();
    bent[0] = bent[0].add(Field(1));
    return call(b, prevProof, vkObject(prevVk), { ...wit, aux: bent });
  });
  await attempt('foreignProofAndKey', () => call(b, foreignProof, vkObject(foreignVk), wit));
  await attempt('rightProofWrongKey', () => call(b, prevProof, vkObject(foreignVk), wit));

  console.log(
    `##JSON##${JSON.stringify({
      si,
      vkHash: verificationKey.hash.toString(),
      shape: { nLiveIn: sh.nLiveIn, nAirOther: sh.nAirOther, nFriOther: sh.nFriOther, nAux: sh.nAux },
      results,
    })}`,
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

  // -----------------------------------------------------------------------
  // [2c] THE CUT RULE, CENSUSED OVER THE WHOLE PLAN — out of circuit, and this
  // is what makes [5]'s third value a measurement rather than an excuse.
  // -----------------------------------------------------------------------
  console.log('\n[2c] the cut rule — which cuts can ATTRIBUTE a bent Merkle sibling, and which cannot');
  const cc = cutCensus(c);
  const pctPlan = ((cc.attributing / c.plan.slices.length) * 100).toFixed(1);
  const pctAux = ((cc.attributing / Math.max(cc.withAux, 1)) * 100).toFixed(1);
  console.log(
    `    of ${fmt(c.plan.slices.length)} cuts in the full plan, ${fmt(cc.withAux)} CONSUME a witnessed ` +
      `Merkle sibling; ${fmt(cc.attributing)} of those also CLOSE the round their FIRST sibling feeds`,
  );
  console.log(
    `    so ${fmt(cc.attributing)} cuts — ${pctPlan}% of the plan, ${pctAux}% of the ones that carry a ` +
      `sibling — can attribute a bend in one. The first is cut ${cc.firstAttributing}; the first cut ` +
      `that carries a sibling AT ALL is cut ${cc.firstAux}`,
  );
  //  ⚑ THE FALSIFIABILITY CONTROLS FOR THE RULE ITSELF, and they are the reason
  //  this census is at tier 0 rather than beside the table it serves. A cut rule
  //  that admits everything, or nothing, is decorative — and a three-valued
  //  result built on a decorative rule launders a non-test as a stated reason.
  if (cc.withAux === 0)
    fail('NO cut in the plan consumes a witnessed Merkle sibling — `auxBent` has nowhere to fire at any budget');
  if (cc.attributing === 0)
    fail(
      'no cut in the plan CLOSES the round its own first sibling feeds — a bent sibling could never be ' +
        'attributed at any cut, and [5]\'s `auxBent` row would be a permanent stated reason',
    );
  if (cc.withAux === cc.attributing)
    fail(
      'every cut that carries a Merkle sibling also closes it — the corrected rule DISCRIMINATES ' +
        'NOTHING on this geometry, so "carries a sibling" would have been the whole rule and the ' +
        'three-valued treatment below is decoration',
    );
  ok(
    `the cut rule is STRICTLY STRONGER than "carries a witnessed sibling": ${fmt(cc.withAux - cc.attributing)} ` +
      'cuts carry one and CANNOT attribute a bend in it — at each of those an ACCEPT is correct ' +
      'behaviour by the circuit, and asserting a refusal there would be a false red',
  );
  console.log(
    `    of those ${fmt(cc.withAux - cc.attributing)}, ${fmt(cc.stray)} have the \`block9\` shape — a closer ` +
      'that is present but for a DIFFERENT round, or positioned before the siblings. On THIS geometry ' +
      'that count is a measured property of the DEPLOYED SLICING and not evidence about the rule; the ' +
      "uniform walk's per-block slicing is where that shape was found.",
  );
  const CUTS: [string, number, number][] = [
    ['cuts consuming a sibling', cc.withAux, RECORDED_CUTS_WITH_AUX],
    ['cuts that can attribute one', cc.attributing, RECORDED_CUTS_ATTRIBUTING],
    ['`block9`-shaped cuts', cc.stray, RECORDED_CUTS_STRAY_CLOSER],
    ['first attributing cut', cc.firstAttributing, RECORDED_FIRST_ATTRIBUTING_CUT],
  ];
  for (const [label, got, want] of CUTS)
    if (got !== want)
      fail(
        `the cut census says ${label} = ${fmt(got)} and the recorded figure is ${fmt(want)} — re-measure, ` +
          'then move recorded-constants.tsv in the SAME commit and say what changed about the slicing',
      );
  ok(
    `the cut-rule census is as recorded (${fmt(cc.withAux)} carry, ${fmt(cc.attributing)} attribute, ` +
      `${fmt(cc.stray)} block9-shaped, first at cut ${cc.firstAttributing})`,
  );

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
  // [5] The splices, ACROSS the process boundary, at an EXPLICITLY CHOSEN cut.
  //
  //  ⚑ THE CUT IS PART OF THE EXPERIMENT AND IS STATED, NOT IMPLIED BY THE RUN
  //  SIZE. THE CUT RULE above is the whole treatment; what is left here is (a)
  //  choosing among the cuts THIS run reached, (b) printing what each of them
  //  could have attributed, and (c) reading every result through the prediction
  //  made before the child ran. A "smaller run of the same test" is only smaller
  //  if the test does not choose its own subject from what the run happened to
  //  do — and this one does, measured: the same `friDigestBent` bend is REFUSED
  //  at cut 1 and ACCEPTED at cut 0, same circuit, same bend, because the cut
  //  moved. So the choice is printed with its reason and every unattributable
  //  row carries the reason it is unattributable.
  // -----------------------------------------------------------------------
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
  console.log('\n[5] the splice cut — CHOSEN and stated, then the table read through that choice');
  const cand = [];
  for (let si = 0; si < N; si++) {
    const p = cutProfile(c, si);
    cand.push({ p, can: SPLICES.filter(([k]) => attribution(k, p).can).length });
  }
  let AT: number;
  if (FORCE_AT !== undefined) {
    AT = Number(FORCE_AT);
    if (!Number.isInteger(AT) || AT < 0 || AT >= N)
      fail(`FRIBRAID_SPLICE_AT='${FORCE_AT}' is not one of the ${N} cuts this run proved (0..${N - 1})`);
  } else {
    //  `>=` keeps the LATEST cut on a tie: deeper into the walk is more of it.
    AT = cand.reduce((best, x) => (x.can >= best.can ? x : best), cand[0]).p.si;
  }
  console.log(`    the ${N} cuts this run proved, and what each of them can attribute:`);
  for (const x of cand)
    console.log(
      `      ${x.p.si === AT ? '→' : ' '} cut ${String(x.p.si).padStart(3)} segments ` +
        `[${fmt(x.p.from)},${fmt(x.p.to)}) ${x.p.head.padEnd(8)} aux ${String(x.p.aux).padStart(4)} ` +
        `${(x.p.closer ? `closes ${x.p.closer}` : x.p.aux > 0 ? `NO closer for ${x.p.tag}` : '—').padEnd(20)} ` +
        `attributes ${x.can} of ${SPLICES.length}`,
    );
  const prof = cutProfile(c, AT);
  console.log(
    `    CHOSEN: cut ${AT}, ${
      FORCE_AT !== undefined
        ? 'because FRIBRAID_SPLICE_AT named it'
        : 'because it attributes more falsifiers than any other cut this run reached (ties to the latest)'
    } — and the choice is the experiment, so a run at another FRIBRAID_LIMIT reaches other cuts and is ` +
      'ANOTHER test, not a smaller one',
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
  //  ⚑ THE HARNESS'S OWN PREDICTION, CHECKED AGAINST THE CHILD'S WITNESS WIDTHS.
  //  `attribution()` reasons from the plan; the child reasons from the shape it
  //  was actually given. If those two ever disagree the third value is being
  //  computed from a picture of the circuit rather than from the circuit.
  for (const [k, got] of [
    ['nLiveIn', prof.nLiveIn],
    ['nAirOther', prof.nAirOther],
    ['nFriOther', prof.nFriOther],
    ['nAux', prof.aux],
  ] as [string, number][])
    if (sp.shape[k] !== got)
      fail(
        `the driver's cut profile says ${k}=${got} at cut ${AT} and the child that built the witness ` +
          `says ${sp.shape[k]} — the three-valued verdicts below would be derived from the wrong shape`,
      );
  ok(
    `the driver's cut profile and the proving child agree on cut ${AT}'s witness widths ` +
      `(liveIn ${fmt(prof.nLiveIn)}, unread AIR ${fmt(prof.nAirOther)}, unread FRI ${fmt(prof.nFriOther)}, ` +
      `siblings ${fmt(sp.shape.nAux)}) — the attribution is over the circuit, not over a picture of it`,
  );
  //  ⚑ THREE-VALUED: refused / accepted / NOT ATTRIBUTABLE, with the reason. The
  //  third is neither a pass nor a fail, it is COUNTED, and the count has a
  //  floor — so a table that went all-reason could never read as green.
  let attributed = 0;
  const unattributable: string[] = [];
  for (const [key, label] of SPLICES) {
    const pred = attribution(key, prof);
    const r = sp.results[key];
    if (!r)
      fail(
        `${label}: the splice child returned NO entry — an absent falsifier reads exactly like one ` +
          'that passed, and every falsifier must report refused, accepted, or why neither applies',
      );
    if (r.noop !== undefined) {
      if (pred.can)
        fail(
          `${label}: the driver predicted this cut could attribute it and the child could not even ` +
            `APPLY it (${r.noop}) — the two halves of the harness disagree about the cut`,
        );
      unattributable.push(label);
      console.log(`    ⚠ ${label}: NOT ATTRIBUTABLE at cut ${AT}, and NOT APPLIED — ${pred.why}`);
      continue;
    }
    if (!pred.can) {
      unattributable.push(label);
      console.log(
        `    ⚠ ${label}: ${r.refused ? 'refused' : 'ACCEPTED'} — NOT ATTRIBUTABLE at cut ${AT}: ${pred.why}`,
      );
      continue;
    }
    attributed++;
    if (!r.refused) fail(`${label}: ACCEPTED, at a cut where ${pred.why}`);
    if (!isConstraintFailure(r.err)) fail(`${label}: the error is not a constraint failure — ${r.err}`);
    ok(`REFUSED: ${label}`);
  }
  console.log(
    `    ${attributed} of ${SPLICES.length} falsifiers ATTRIBUTED at cut ${AT}; ` +
      (unattributable.length
        ? `${unattributable.length} NOT ATTRIBUTABLE, each with its reason above (${unattributable.join('; ')})`
        : 'none unattributable — every falsifier at this cut had something to fail against'),
  );
  if (attributed === 0)
    fail(
      `NO falsifier is attributable at cut ${AT} — this table is all stated reason and no test, and a ` +
        'table of NOT ATTRIBUTABLE must never be able to read as green',
    );
  if (attributed < MIN_ATTRIBUTED)
    fail(
      `cut ${AT} attributes ${attributed} of ${SPLICES.length} falsifiers and the recorded floor is ` +
        `${MIN_ATTRIBUTED}. This run tests strictly LESS than the recorded one — it did not fail, it went ` +
        'QUIETER, which is the failure mode the third value creates. Set FRIBRAID_MIN_ATTRIBUTED in the ' +
        'invocation to accept that, where a reader can see it.',
    );
  ok(
    `the splice table is three-valued and counted: ${attributed} attributed, ${unattributable.length} ` +
      `not attributable with a stated reason, floor ${MIN_ATTRIBUTED}`,
  );
  //  ⚑ AND THE HONEST OUTCOME WHEN THE BUDGET CANNOT REACH A CUT THAT ATTRIBUTES
  //  A BENT SIBLING. It is neither forced to a pass nor asserted into a false
  //  red: the leg says which cut would, and what it would cost to get there.
  if (!attribution('auxBent', prof).can) {
    const need = cc.firstAttributing + 1;
    console.log(
      `    ⚑ 'one Merkle sibling bent' is NOT ATTRIBUTABLE WITHIN THIS BUDGET, and that — not a pass ` +
        `— is the outcome. No cut this run reached (0..${N - 1}) closes a round its own siblings feed; ` +
        `the first that does is cut ${cc.firstAttributing}, so FRIBRAID_LIMIT=${need} is what buys the ` +
        `row, at roughly ${need - N} more slices of proving. ${fmt(cc.attributing)} of the plan's ` +
        `${fmt(c.plan.slices.length)} cuts can attribute it; this run reaches ${
          cand.filter((x) => x.p.closer !== null).length
        }.`,
    );
  }

  // -----------------------------------------------------------------------
  // [6] The controls.
  // -----------------------------------------------------------------------
  console.log(`\n[6] the controls — cut ${AT} again, with ONE binding removed`);
  //  ⚑ THE CONTROL IS SUBJECT TO THE SAME CUT PROBLEM AS THE TABLE. Its
  //  `airDigestBent` arm has to show the UNBOUND circuit ACCEPTING a bend — and
  //  a bend of a chunk this cut READS would be accepted for a reason that has
  //  nothing to do with the binding. That would be a vacuous control reading as
  //  the strongest line in the leg.
  if (prof.nAirOther === 0)
    fail(
      `cut ${AT} reads every AIR chunk, so the unbound control's "bent digest of a chunk it never ` +
        'reads" bends nothing — the control would ACCEPT vacuously and be credited as evidence',
    );
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

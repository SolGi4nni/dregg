// RUNG 6 — THE DEEP QUOTIENT: the reduced opening the fold chain starts from,
// COMPUTED from the opened trace instead of witnessed.
//
//   npm run fri-deep
//
// Rungs 1-5 walk the prover's FRI proof, at the transcript's index, under the
// transcript's betas. All five start the chain from `initial` — a WITNESS. A FRI
// walk over a witnessed starting value certifies a number the prover chose; it
// is a statement about no committed trace at all. This leg is what turns the
// authenticated number into an authenticated CLAIM.
//
// ⚑ THE INSTRUMENT DESIGN IS THE LESSON FROM THE COSET-DESCENT BUG, APPLIED FOUR
// TIMES. That bug survived a deterministic both-polarity check because one round
// never consumes two index bits — the check was right on 100% of the all-zero
// index every row measurement supplies. `open_input` has four conventions with
// exactly that shape:
//
//   1. `x` carries the multiplicative GENERATOR; the fold chain's coset point
//      does not;
//   2. `x` uses `g_L`; the fold chain uses `g_{L+1}` — BOTH are 1 at reversed
//      index 0;
//   3. the index is shifted down by `LGMH - L` before reversal — invisible if
//      every matrix sits at the top height;
//   4. `alpha_pow` is keyed by HEIGHT in ENCOUNTER order — invisible unless two
//      matrices share a height AND a second height exists.
//
// So every fixture below carries TWO heights, TWO matrices sharing a height in
// DIFFERENT batches, and multiple opening points; and each of the four wrong
// readings is kept as a LIVE twin that must diverge on it.

import { Bool, Field, Provable } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { P } from '../src/Poseidon2BabyBearW16.js';
import { BbDigest, spongeBigInt } from '../src/Poseidon2Merkle.js';
import {
  ChallengerBigInt,
  DEPLOYED_KNOBS,
  FriKnobs,
  deriveFriChallenges,
  witnessTranscriptShape,
} from '../src/FriChallenger.js';
import {
  BbExt,
  extAddBigInt,
  extMulBigInt,
  extSubBigInt,
  foldRowArity2BigInt,
  verifyCommitPhase,
} from '../src/FriQueryStep.js';
import {
  BB_GENERATOR,
  DeepMatBigInt,
  DeepMatrix,
  deepPreambleBigInt,
  deepQueryPointBigInt,
  deployedDeepShape,
  assertExtInverse,
  extInvBigInt,
  extInverse,
  makeDeepBoundQueryProgram,
  reducedOpenings,
  reducedOpeningsBigInt,
  rollInSchedule,
  rootDeepTermCount,
  twoAdicGeneratorBigInt,
  witnessDeepBatches,
  witnessDeepShape,
} from '../src/DeepQuotient.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const eqv = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);
const B = (s: string) => BigInt(s);
const md = (x: bigint) => ((x % P) + P) % P;

function probeDir(): string {
  const d =
    process.env.DREGG_PROBE_DIR ??
    resolve(process.cwd(), '../../circuit-prove/sketches/mina-pasta-hash-probe');
  if (!existsSync(resolve(d, 'Cargo.toml')))
    throw new Error(`the dregg-side hash probe is not at ${d} — set DREGG_PROBE_DIR`);
  return d;
}
function runDeep(dir: string, seed: number, index: number, lgmh: number, spec: string): any {
  const out = execFileSync(
    'cargo',
    ['run', '--offline', '--quiet', '--', 'p2deep', String(seed), String(index), String(lgmh), spec],
    { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 24 },
  );
  return JSON.parse(out);
}

/** The emitted batches, as the bigint twin consumes them. */
function toBigIntBatches(e: any): DeepMatBigInt[][] {
  return e.batches.map((batch: any[]) =>
    batch.map((m: any) => ({
      logHeight: m.logHeight,
      openedRow: m.openedRow.map(B),
      points: m.psAtZ.map((ps: string[][], p: number) => ({
        z: m.zs[p].map(B),
        psAtZ: ps.map((v: string[]) => v.map(B)),
      })),
    })),
  );
}

const dir = probeDir();

console.log('=== Rung 6: the DEEP QUOTIENT — the reduced opening, BOUND ===\n');

// ---------------------------------------------------------------------------
// [1] the query point.
// ---------------------------------------------------------------------------
console.log('[1] the DEEP query point == p3, and every wrong reading of it diverges');
let em0: any;
{
  // ⚑ A MULTI-HEIGHT SPEC ON A BIT-VARIED INDEX. Two matrices at the top height
  // in DIFFERENT batches, one below it. An index of 0 or of all-ones cannot see
  // conventions (2) or (3), so the fixed cases are the ones that CAN, plus a
  // fresh one.
  const SPEC = '22:2:3/22:1:2;18:2:2;12:1:4';
  const alternating = 0b0101010101010101010101;
  const fresh = Number(BigInt('0x' + randomBytes(3).toString('hex')) % (1n << 22n));
  const cases: [string, number][] = [
    ['all-zero index (every reading of x coincides at rev = 0)', 0],
    ['alternating bits', alternating],
    ['all-ones index', (1 << 22) - 1],
    [`a fresh index (${fresh})`, fresh],
  ];
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const divergences = [0, 0, 0, 0, 0];
  for (const [label, index] of cases) {
    const e = runDeep(dir, seed, index, 22, SPEC);
    if (!em0) em0 = e;
    if (B(e.generator) !== BB_GENERATOR)
      fail(`p3 says BabyBear::GENERATOR is ${e.generator}, this circuit uses ${BB_GENERATOR}`);
    for (const batch of e.batches)
      for (const m of batch) {
        const got = deepQueryPointBigInt(BigInt(index), m.logHeight, 22);
        if (got !== B(m.x))
          fail(`'${label}' h=${m.logHeight}: x is ${got}, p3 says ${m.x}`);

        // The four wrong readings, LIVE.
        const rev = (idx: bigint, n: number) => {
          let r = 0n;
          for (let i = 0; i < n; i++) if ((idx >> BigInt(i)) & 1n) r |= 1n << BigInt(n - 1 - i);
          return r;
        };
        const powg = (k: number, e2: bigint) => {
          let acc = 1n;
          let b = twoAdicGeneratorBigInt(k);
          let x = e2;
          while (x > 0n) {
            if (x & 1n) acc = md(acc * b);
            b = md(b * b);
            x >>= 1n;
          }
          return acc;
        };
        const L = m.logHeight;
        const shifted = BigInt(index) >> BigInt(22 - L);
        let lowBits = 0n;
        for (let i = 0; i < L; i++) if ((BigInt(index) >> BigInt(i)) & 1n) lowBits |= 1n << BigInt(i);
        const wrong = [
          powg(L, rev(shifted, L)), //                        (1) no GENERATOR
          md(BB_GENERATOR * powg(L + 1, rev(shifted, L))), //  (2) g_{L+1}, revLen L
          md(BB_GENERATOR * powg(L, rev(BigInt(index), L))), //(3) the UNSHIFTED index
          md(BB_GENERATOR * powg(L, shifted)), //              (4) no bit reversal
          md(BB_GENERATOR * powg(L, rev(lowBits, L))), //      (5) the LOW bits, not the high
        ];
        wrong.forEach((w, i) => {
          if (w !== got) divergences[i]++;
        });

        // ⚑ AND ONE READING THAT IS NOT A READING. `g_{L+1}^{rev(s, L+1)}` looks
        // like a sixth mistake and is ALGEBRAICALLY THE SAME FUNCTION: `s` has
        // `L` significant bits, so `rev(s, L+1) = 2 * rev(s, L)`, and
        // `g_{L+1}^2 = g_L`. A fault injection written against it could never
        // fire — the same shape as the challenger's `observe`-clears-output
        // twin, which stayed green and was deleted rather than kept. It is
        // ASSERTED as an identity here instead of counted as a divergence.
        if (md(BB_GENERATOR * powg(L + 1, rev(shifted, L + 1))) !== got)
          fail(
            `g_{L+1}^{rev(s, L+1)} != g_L^{rev(s, L)} at height ${L} — the identity this ` +
              'leg relies on to NOT count that reading has broken',
          );
      }
    ok(`${label} — x agrees with p3 at every height`);
  }
  divergences.forEach((n, i) => {
    if (n === 0)
      fail(
        `wrong reading #${i + 1} of the query point never diverged across ${cases.length} ` +
          'indices and 4 matrices: this leg cannot see the mistake it exists for',
      );
  });
  ok(
    `all five wrong readings of x diverge (no GENERATOR: ${divergences[0]}x, ` +
      `g_{L+1}: ${divergences[1]}x, unshifted index: ${divergences[2]}x, ` +
      `no bit-reversal: ${divergences[3]}x, low bits: ${divergences[4]}x)`,
  );
  ok(
    'and `g_{L+1}^{rev(s, L+1)}` is NOT a sixth reading — it is the same function ' +
      '(rev(s, L+1) = 2*rev(s, L) and g_{L+1}^2 = g_L), so a fault written against it ' +
      'could never fire. Asserted as an identity, not counted as a divergence.',
  );
  ok(`emitter: ${em0.emitter}`);
}

// ---------------------------------------------------------------------------
// [2] the reduced openings.
// ---------------------------------------------------------------------------
console.log('\n[2] the REDUCED OPENINGS == p3 — across batches, heights, points and columns');
{
  const SPEC = '22:2:3/22:1:2;18:2:2;12:1:4';
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const index = Number(BigInt('0x' + randomBytes(3).toString('hex')) % (1n << 22n));
  const e = runDeep(dir, seed, index, 22, SPEC);
  const batches = toBigIntBatches(e);
  const alpha = e.alpha.map(B);

  const got = reducedOpeningsBigInt({ index: BigInt(index), logGlobalMaxHeight: 22, alpha, batches });
  if (got.length !== e.reducedOpenings.length)
    fail(`${got.length} reduced openings, p3 emitted ${e.reducedOpenings.length}`);
  got.forEach((g, i) => {
    const want = e.reducedOpenings[i];
    if (g.logHeight !== want.logHeight)
      fail(`opening ${i} is at height ${g.logHeight}, p3 says ${want.logHeight}`);
    if (!eqv(g.ro, want.ro.map(B)))
      fail(`the reduced opening at height ${g.logHeight} is ${g.ro}, p3 says ${want.ro}`);
  });
  ok(
    `${got.length} reduced openings at heights [${got.map((g) => g.logHeight).join(', ')}], ` +
      'descending, all agree with p3',
  );

  // The per-point quotients, so a divergence localises to a point.
  for (const batch of e.batches)
    for (const m of batch)
      m.quotients.forEach((q: string[], p: number) => {
        const x = B(m.x);
        const mine = extInvBigInt(extSubBigInt(m.zs[p].map(B), [x, 0n, 0n, 0n]));
        if (!eqv(mine, q.map(B)))
          fail(`(z - x)^-1 at height ${m.logHeight} point ${p} is ${mine}, p3 says ${q}`);
      });
  ok('every (z - x)^-1 agrees with p3\'s own BinomialExtensionField inverse');

  // ⚑ THE ALPHA-POWER TWINS, LIVE. Both are the same value on a one-matrix,
  // one-height fixture and wrong on this one.
  const perMatrix = altOpenings(batches, alpha, 'per-matrix', BigInt(index));
  const global = altOpenings(batches, alpha, 'global', BigInt(index));
  const same = (a: { logHeight: number; ro: bigint[] }[]) =>
    a.length === got.length && a.every((s, i) => s.logHeight === got[i].logHeight && eqv(s.ro, got[i].ro));
  if (same(perMatrix)) fail('resetting alpha_pow per MATRIX gave the same openings — the fixture is blind');
  if (same(global)) fail('threading alpha_pow GLOBALLY gave the same openings — the fixture is blind');
  ok('resetting alpha_pow per matrix, and threading it globally, BOTH diverge (the key is HEIGHT)');

  // Sensitivity: every opened row entry and every claimed evaluation moves it.
  let moved = 0;
  for (let b = 0; b < batches.length; b++)
    for (let m = 0; m < batches[b].length; m++)
      for (let c = 0; c < batches[b][m].openedRow.length; c++) {
        const perturbed = structuredClone(batches);
        perturbed[b][m].openedRow[c] = md(perturbed[b][m].openedRow[c] + 1n);
        const r = reducedOpeningsBigInt({ index: BigInt(index), logGlobalMaxHeight: 22, alpha, batches: perturbed });
        if (!same(r)) moved++;
      }
  const cols = batches.flat().reduce((a, m) => a + m.openedRow.length, 0);
  if (moved !== cols) fail(`only ${moved} of ${cols} opened columns move the reduced openings`);
  ok(`all ${cols} opened columns move the reduced openings (the binding is not partial)`);
}

/** The two alpha-power readings this rung must not have. Kept LIVE rather than
 *  described, so [2]'s discrimination has something to discriminate against. */
function altOpenings(
  batches: DeepMatBigInt[][],
  alpha: bigint[],
  mode: 'per-matrix' | 'global',
  index: bigint,
): { logHeight: number; ro: bigint[] }[] {
  const slots: { logHeight: number; ro: bigint[] }[] = [];
  let globalPow = [1n, 0n, 0n, 0n];
  for (const batch of batches)
    for (const m of batch) {
      // ⚑ THE SAME `x` AS THE REAL COMPUTATION. The twin varies ONE thing — how
      // `alpha_pow` is keyed — so a divergence is attributable to that and not
      // to a query point that happened to differ too.
      const x = deepQueryPointBigInt(index, m.logHeight, 22);
      let ap = mode === 'global' ? globalPow : [1n, 0n, 0n, 0n];
      let acc = [0n, 0n, 0n, 0n];
      for (const pt of m.points) {
        const q = extInvBigInt(extSubBigInt(pt.z, [x, 0n, 0n, 0n]));
        for (let c = 0; c < pt.psAtZ.length; c++) {
          const d = extSubBigInt(pt.psAtZ[c], [m.openedRow[c], 0n, 0n, 0n]);
          acc = extAddBigInt(acc, extMulBigInt(extMulBigInt(ap, d), q));
          ap = extMulBigInt(ap, alpha);
        }
      }
      if (mode === 'global') globalPow = ap;
      const s = slots.find((y) => y.logHeight === m.logHeight);
      if (s) s.ro = extAddBigInt(s.ro, acc);
      else slots.push({ logHeight: m.logHeight, ro: acc });
    }
  slots.sort((a, b) => b.logHeight - a.logHeight);
  return slots;
}

// ---------------------------------------------------------------------------
// [3] the same thing IN CIRCUIT.
// ---------------------------------------------------------------------------
console.log('\n[3] the reduced openings IN CIRCUIT, against p3');
{
  const SPEC = '22:2:3/22:1:2;18:2:2;12:1:4';
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const index = 0b0101010101010101010101;
  const e = runDeep(dir, seed, index, 22, SPEC);
  const indexBits = Array.from({ length: 22 }, (_, i) => ((index >> i) & 1) === 1);
  const alpha = e.alpha.map(B);

  for (const perColumn of [false, true]) {
    const t0 = Date.now();
    await Provable.runAndCheck(() => {
      const bits = indexBits.map((b) => Provable.witness(Bool, () => Bool(b)));
      const a = Provable.witness(BbExt, () => BbExt.from(alpha));
      const mats: DeepMatrix[][] = e.batches.map((batch: any[]) =>
        batch.map((m: any) => ({
          logHeight: m.logHeight,
          openedRow: m.openedRow.map((v: string) => Provable.witness(Field, () => Field(B(v)))),
          points: m.psAtZ.map((ps: string[][], p: number) => ({
            z: Provable.witness(BbExt, () => BbExt.from(m.zs[p].map(B))),
            psAtZ: ps.map((v: string[]) => Provable.witness(BbExt, () => BbExt.from(v.map(B)))),
          })),
        })),
      );
      const ro = reducedOpenings({
        indexBits: bits,
        logGlobalMaxHeight: 22,
        alpha: a,
        batches: mats,
        perColumn,
      });
      Provable.asProver(() => {
        ro.forEach((g, i) => {
          const want = e.reducedOpenings[i];
          if (g.logHeight !== want.logHeight)
            fail(`in-circuit opening ${i} at height ${g.logHeight}, p3 says ${want.logHeight}`);
          if (!eqv(g.ro.toBigInts(), want.ro.map(B)))
            fail(
              `in-circuit opening at height ${g.logHeight} is ${g.ro.toBigInts()}, ` +
                `p3 says ${want.ro}`,
            );
        });
      });
    });
    ok(
      `the CIRCUIT computes p3's reduced openings ` +
        `(${perColumn ? "p3's literal per-column loop" : 'the factored Horner form'}) ` +
        `[${((Date.now() - t0) / 1000).toFixed(1)}s]`,
    );
  }

  // The roll-in schedule is DERIVED from the heights, not supplied.
  const ro = reducedOpeningsBigInt({
    index: BigInt(index),
    logGlobalMaxHeight: 22,
    alpha,
    batches: toBigIntBatches(e),
  });
  const sched = rollInSchedule(ro, 22, 16);
  const wantRounds = ro.slice(1).map((o) => 22 - 1 - o.logHeight);
  if (sched.rounds.join(',') !== wantRounds.join(','))
    fail(`the roll-in schedule is ${sched.rounds}, expected ${wantRounds}`);
  ok(
    `the roll-in schedule [${sched.rounds.join(', ')}] is DERIVED from the matrix heights ` +
      `[${ro.map((o) => o.logHeight).join(', ')}] — §3.14 listed it as uncounted; it is a function`,
  );

  // and a first opening below the global max is REFUSED, as verify_query does.
  let held = false;
  try {
    rollInSchedule([{ logHeight: 21, ro: null }], 22, 16);
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a chain accepted a first reduced opening below the global max height');
  ok('a first reduced opening below the global max height is REFUSED (verify_query:388-393)');
}

// ---------------------------------------------------------------------------
// [4] the extension inverse.
// ---------------------------------------------------------------------------
console.log('\n[4] the EXTENSION INVERSE, and what it refuses');
{
  const rnd = () => BigInt('0x' + randomBytes(4).toString('hex')) % P;
  const a = [rnd(), rnd(), rnd(), rnd()];
  const inv = extInvBigInt(a);
  if (!eqv(extMulBigInt(a, inv), [1n, 0n, 0n, 0n]))
    fail('the bigint extension inverse does not invert');
  ok('the bigint extension inverse inverts (a * a^-1 == 1 over X^4 - 11)');

  await Provable.runAndCheck(() => {
    const wa = Provable.witness(BbExt, () => BbExt.from(a));
    const wi = extInverse(wa);
    Provable.asProver(() => {
      if (!eqv(wi.toBigInts(), inv)) fail('the in-circuit inverse disagrees with the twin');
    });
  });
  ok('the in-circuit extension inverse agrees with the twin');

  // ⚑ THE BOUND IS ARITHMETIC, NOT A LOOKUP. `Provable.runAndCheck` does NOT
  // evaluate lookup constraints, so a check resting on a range lookup alone is
  // sound in a proof and undemonstrable outside one — a gate can never watch it
  // refuse. This one rests on a canonical EQUALITY (`a * inv == 1`, lane by
  // lane), which every instrument can see. And `assertExtInverse` takes both
  // sides as ARGUMENTS precisely so a lying witness can be handed to it.
  for (const [label, lie] of [
    ['one off the true inverse', extAddBigInt(inv, [1n, 0n, 0n, 0n])],
    ['with two lanes swapped', [inv[1], inv[0], inv[2], inv[3]]],
    ['whose lane 3 is zeroed', [inv[0], inv[1], inv[2], 0n]],
  ] as [string, bigint[]][]) {
    if (eqv(lie, inv)) fail(`the '${label}' lie is not actually a lie`);
    let held = false;
    try {
      await Provable.runAndCheck(() => {
        const wa = Provable.witness(BbExt, () => BbExt.from(a));
        const wl = Provable.witness(BbExt, () => BbExt.from(lie));
        assertExtInverse(wa, wl);
      });
      held = true;
    } catch {
      /* expected */
    }
    if (held) fail(`the circuit accepted an inverse ${label}`);
    ok(`the circuit REFUSES an inverse ${label}`);
  }

  // A zero denominator (`z == x`) is UNSATISFIABLE — the constraint-system
  // analogue of the `.inverse()` panic p3 would take, and the right behaviour.
  // Checked at the CONSTRAINT, not merely by the twin throwing.
  let held = false;
  try {
    await Provable.runAndCheck(() => {
      const zero = Provable.witness(BbExt, () => BbExt.zero());
      const any = Provable.witness(BbExt, () => BbExt.from(a));
      assertExtInverse(zero, any);
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the circuit produced an inverse for the extension ZERO');
  ok('a zero denominator (z == x) is REFUSED rather than answered');
}

// ---------------------------------------------------------------------------
// [5] THE DEEP-BOUND QUERY — and the proof the OLD statement admits.
// ---------------------------------------------------------------------------
console.log('\n[5] THE DEEP-BOUND QUERY — nothing the chain consumes is witnessed');
let deepSeamRows = 0;
let bindingDelta = 0;
{
  const LOG_D0 = 6;
  const LAYERS = 2;
  const POW = 8; //  a LABELLED reduction; the deployed 16 is exercised in leg 6.
  const PRE = 9;
  const knobs: FriKnobs = {
    ...DEPLOYED_KNOBS,
    layers: LAYERS,
    numQueries: 1,
    logGlobalMaxHeight: LOG_D0,
    indexBits: LOG_D0,
    queryPowBits: POW,
  };
  // ⚑ THE SHAPE IS DELIBERATELY NON-DEGENERATE. Two batches at the TOP height
  // (so the height-keyed alpha power has to thread across commitments), one
  // below it (so the index shift and the roll-in schedule are both live).
  const specs = [
    [{ logHeight: LOG_D0, numPoints: 2, numCols: 3 }],
    [{ logHeight: LOG_D0, numPoints: 1, numCols: 2 }],
    [{ logHeight: LOG_D0 - 2, numPoints: 2, numCols: 2 }],
  ];
  const widths = specs.map((s) => s[0].numCols);
  const nPts = specs.map((s) => s[0].numPoints);
  const rnd = () => BigInt('0x' + randomBytes(4).toString('hex')) % P;
  const ext = () => [rnd(), rnd(), rnd(), rnd()];

  const prefix = Array.from({ length: PRE }, rnd);
  const rows = specs.map((s) => Array.from({ length: s[0].numCols }, rnd));
  const zs = specs.flatMap((s) => Array.from({ length: s[0].numPoints }, ext));
  const evals = specs.flatMap((s) =>
    Array.from({ length: s[0].numPoints * s[0].numCols }, ext),
  );
  const inputCommits = rows.map((r) => spongeBigInt(r));
  const preamble = deepPreambleBigInt(prefix, zs, evals);

  // alpha is sampled BEFORE any commit-phase commitment is observed, so it is a
  // function of the preamble alone — which is exactly why f(z) has to be in it.
  const alphaOf = (pre: bigint[]) => {
    const c = new ChallengerBigInt();
    c.observeSlice(pre);
    return c.sampleExt();
  };

  const batchesFor = (rws: bigint[][], zz: bigint[][], ev: bigint[][]): DeepMatBigInt[][] => {
    let zo = 0;
    let eo = 0;
    return specs.map((s, b) => {
      const pts = [];
      for (let p = 0; p < nPts[b]; p++) {
        pts.push({ z: zz[zo + p], psAtZ: ev.slice(eo, eo + widths[b]) });
        eo += widths[b];
      }
      zo += nPts[b];
      return [{ logHeight: s[0].logHeight, openedRow: rws[b], points: pts }];
    });
  };

  /** Build the chain from a starting value, returning the commits it induces,
   *  the betas, the final polynomial and the derived index. */
  function chainFrom(initial: bigint[], rollIns: { afterRound: number; value: bigint[] }[], bits: boolean[]) {
    const c = new ChallengerBigInt();
    c.observeSlice(preamble);
    c.sampleExt(); //                                   alpha
    const betas: bigint[][] = [];
    const commits: bigint[][] = [];
    const siblings: bigint[][] = [];
    let running = initial;
    // The FOLD chain's coset point — g_{L+1}, no generator. NOT the DEEP x.
    let x = 1n;
    {
      const L = LOG_D0 - 1;
      let rev = 0n;
      for (let i = 1; i < LOG_D0; i++) if (bits[i]) rev |= 1n << BigInt(L - 1 - (i - 1));
      let b = twoAdicGeneratorBigInt(L + 1);
      let e2 = rev;
      while (e2 > 0n) {
        if (e2 & 1n) x = md(x * b);
        b = md(b * b);
        e2 >>= 1n;
      }
    }
    for (let r = 0; r < LAYERS; r++) {
      const sib = ext();
      siblings.push(sib);
      const even = bits[r] ? sib : running;
      const odd = bits[r] ? running : sib;
      commits.push(spongeBigInt([...even, ...odd]));
      c.observeSlice(commits[r]);
      const beta = c.sampleExt();
      betas.push(beta);
      running = foldRowArity2BigInt(x, beta, even, odd);
      const sq = md(x * x);
      x = r + 1 < LOG_D0 && bits[r + 1] ? md(P - sq) : sq;
      for (const ri of rollIns)
        if (ri.afterRound === r)
          running = extAddBigInt(running, extMulBigInt(extMulBigInt(beta, beta), ri.value));
    }
    const finalPoly = [running];
    for (const e2 of finalPoly) c.observeSlice(e2);
    for (let r = 0; r < LAYERS; r++) c.observe(BigInt(knobs.maxLogArity));
    const w = c.grind(POW);
    if (!c.checkWitness(POW, w)) fail('the ground witness did not pass');
    const derived = c.sampleBits(LOG_D0);
    return { betas, commits, siblings, finalPoly, witness: w, derived };
  }

  /** Search for the index that its own chain derives. `free` replaces the DEEP
   *  starting value with an arbitrary one — the pre-rung-6 prover's freedom. */
  function search(free: bigint[] | null) {
    for (let attempt = 0; attempt < 8; attempt++) {
      for (let cand = 0; cand < 1 << LOG_D0; cand++) {
        const bits = Array.from({ length: LOG_D0 }, (_, i) => ((cand >> i) & 1) === 1);
        const ro = reducedOpeningsBigInt({
          index: BigInt(cand),
          logGlobalMaxHeight: LOG_D0,
          alpha: alphaOf(preamble),
          batches: batchesFor(rows, zs, evals),
        });
        const sched = rollInSchedule(ro, LOG_D0, LAYERS);
        const initial = free ?? ro[0].ro;
        const rollIns = sched.rounds.map((r, i) => ({ afterRound: r, value: ro[i + 1].ro }));
        const out = chainFrom(initial, rollIns, bits);
        if (out.derived === cand) return { cand, bits, ro, sched, initial, rollIns, ...out };
      }
    }
    return null;
  }

  const t0 = Date.now();
  const honest = search(null);
  if (!honest) fail('no fixed point found for the DEEP-bound query');
  ok(
    `an honest witness exists: index ${honest.cand} is the one its own chain derives, ` +
      `and its starting value is the DEEP quotient of the opened rows ` +
      `[${((Date.now() - t0) / 1000).toFixed(1)}s]`,
  );

  const { prog, DeepQueryClaim } = makeDeepBoundQueryProgram({
    knobs,
    prefixLen: PRE,
    batches: specs,
    inputPathDepths: specs.map(() => 0),
    pathDepths: Array(LAYERS).fill(0),
  });
  const analysis = await prog.analyzeMethods();
  console.log(
    `    proveDeepQuery      : ${analysis.proveDeepQuery.rows.toLocaleString()} rows\n` +
      `    proveWitnessedInitial (the PRE-rung-6 statement): ` +
      `${analysis.proveWitnessedInitial.rows.toLocaleString()} rows  ` +
      `(+${(analysis.proveDeepQuery.rows - analysis.proveWitnessedInitial.rows).toLocaleString()} ` +
      `is what the binding costs at this shape)`,
  );
  const t1 = Date.now();
  await prog.compile();
  ok(`compiled both methods in ${((Date.now() - t1) / 1000).toFixed(1)}s`);

  const claim = new DeepQueryClaim({
    inputCommits: inputCommits.map((c) => BbDigest.from(c)),
    commits: honest.commits.map((c) => BbDigest.from(c)),
    finalPoly: honest.finalPoly.map((c) => BbExt.from(c)),
  });
  const priv = (
    r = rows,
    z = zs,
    ev = evals,
    pre = prefix,
    wit = honest.witness,
    sib = honest.siblings,
  ) =>
    [
      pre.map((v) => Field(v)),
      z.map((v) => BbExt.from(v)),
      ev.map((v) => BbExt.from(v)),
      r.flat().map((v) => Field(v)),
      specs.map(() => [BbDigest.zero()]),
      Field(wit),
      sib.map((v) => BbExt.from(v)),
      Array.from({ length: LAYERS }, () => [BbDigest.zero()]),
    ] as const;

  const t2 = Date.now();
  const { proof } = await prog.proveDeepQuery(claim, ...priv());
  if (!(await prog.verify(proof))) fail('the DEEP-bound proof failed to verify');
  ok(`the DEEP-BOUND QUERY PROVES and VERIFIES in ${((Date.now() - t2) / 1000).toFixed(1)}s`);
  if (proof.publicOutput.toBigInt() !== BigInt(honest.cand))
    fail(`the proof reports index ${proof.publicOutput.toBigInt()}, not ${honest.cand}`);
  ok(`the PROVEN index ${honest.cand} is derived, and the chain it walked started at the DEEP value`);

  // ⚑ THE GAP, EXHIBITED. A witness whose starting value is NOT the DEEP
  // quotient: the pre-rung-6 statement PROVES it, and rung 6 refuses the same
  // public claim. Without this pair, "the reduced opening is now bound" is a
  // sentence rather than a measurement.
  const freeInitial = extAddBigInt(honest.ro[0].ro, [1n, 0n, 0n, 0n]);
  const forged = search(freeInitial);
  if (!forged) fail('no fixed point found for the free-initial witness');
  const forgedClaim = new DeepQueryClaim({
    inputCommits: inputCommits.map((c) => BbDigest.from(c)),
    commits: forged.commits.map((c) => BbDigest.from(c)),
    finalPoly: forged.finalPoly.map((c) => BbExt.from(c)),
  });
  const forgedRollIns = forged.rollIns.map((r) => BbExt.from(r.value));
  const { proof: oldProof } = await prog.proveWitnessedInitial(
    forgedClaim,
    prefix.map((v) => Field(v)),
    zs.map((v) => BbExt.from(v)),
    evals.map((v) => BbExt.from(v)),
    rows.flat().map((v) => Field(v)),
    specs.map(() => [BbDigest.zero()]),
    Field(forged.witness),
    BbExt.from(freeInitial),
    forgedRollIns.length ? forgedRollIns : [BbExt.zero()],
    forged.siblings.map((v) => BbExt.from(v)),
    Array.from({ length: LAYERS }, () => [BbDigest.zero()]),
  );
  if (!(await prog.verify(oldProof))) fail('the pre-rung-6 forgery did not verify');
  ok(
    'the PRE-RUNG-6 statement PROVES a query whose starting value is NOT the DEEP quotient ' +
      '(this is the hole, and it is a real proof object)',
  );

  let held = false;
  try {
    await prog.proveDeepQuery(
      forgedClaim,
      prefix.map((v) => Field(v)),
      zs.map((v) => BbExt.from(v)),
      evals.map((v) => BbExt.from(v)),
      rows.flat().map((v) => Field(v)),
      specs.map(() => [BbDigest.zero()]),
      Field(forged.witness),
      forged.siblings.map((v) => BbExt.from(v)),
      Array.from({ length: LAYERS }, () => [BbDigest.zero()]),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('RUNG 6 ADMITTED THE SAME FORGERY — the binding is decorative');
  ok('RUNG 6 REFUSES that same public claim — the starting value is no longer the prover\'s');

  // REJECT: one opened-row entry moved. The row is NOT absorbed, so the
  // transcript is untouched: this is purely the DEEP binding refusing.
  held = false;
  try {
    const bad = rows.map((r) => r.slice());
    bad[2][1] = md(bad[2][1] + 1n);
    await prog.proveDeepQuery(claim, ...priv(bad));
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a doctored opened row still produced the same reduced opening');
  ok('NO proof exists for an opened row one element off (and the row is NOT in the transcript)');

  // REJECT: one claimed evaluation f(z) moved. This moves the transcript AND the
  // reduced opening — both halves of the binding at once.
  held = false;
  try {
    const bad = evals.map((v) => v.slice());
    bad[4][0] = md(bad[4][0] + 1n);
    await prog.proveDeepQuery(claim, ...priv(rows, zs, bad));
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a doctored claimed evaluation proved anyway');
  ok('NO proof exists for a claimed evaluation f(z) one element off');

  // REJECT: an opening point z moved.
  held = false;
  try {
    const bad = zs.map((v) => v.slice());
    bad[1][2] = md(bad[1][2] + 1n);
    await prog.proveDeepQuery(claim, ...priv(rows, bad));
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a doctored opening point proved anyway');
  ok('NO proof exists for an opening point z one element off');

  // REJECT: the PoW is still live here.
  held = false;
  try {
    await prog.proveDeepQuery(claim, ...priv(rows, zs, evals, prefix, md(honest.witness + 1n)));
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the DEEP-bound query proved with a PoW witness that does not grind');
  ok('the query PoW is still enforced inside the DEEP-bound query');

  deepSeamRows = analysis.proveDeepQuery.rows;
  bindingDelta = analysis.proveDeepQuery.rows - analysis.proveWitnessedInitial.rows;

  // ⚑ AND HERE IS WHAT NO INSTRUMENT IN THIS HARNESS CAN SEE, SAID OUT LOUD.
  // A fault injection was written for "the DEEP-bound query goes back to a
  // WITNESSED initial value" — `initial: Provable.witness(BbExt, () => ro[0].ro)`
  // — and it STAYED GREEN. Every check above runs the honest prover, whose
  // witness callback recomputes the same value from the same inputs, so a
  // derived variable and a witness carrying that variable's value are
  // indistinguishable to `runAndCheck`, to `prove`, and to `getRows()`. That
  // injection was deleted rather than kept as a falsifier that cannot fire —
  // the same call the challenger leg made about `observe` clearing the output
  // buffer.
  //
  // What CAN see the realistic form of the regression (witness it AND delete the
  // now-dead computation) is the ROW DELTA between the two compiled methods. It
  // is ratcheted below. If it ever collapses, the binding has stopped costing
  // anything, which is what a decorative binding looks like from the outside.
  if (bindingDelta <= 0)
    fail(
      `the DEEP-bound method costs ${bindingDelta} rows more than the witnessed-initial one: ` +
        'the binding is not in the circuit at all',
    );
}

// ---------------------------------------------------------------------------
// [6] getRows() — the DEPLOYED root's DEEP quotient.
// ---------------------------------------------------------------------------
console.log('\n[6] getRows() — the DEEP quotient at the ROOT\'s real table set');
let deepFactored = 0;
let deepPerColumn = 0;
let deepPerTerm = 0;
{
  const census = rootDeepTermCount();
  console.log(
    `    the root's opened-column census (§1.3, 7 tables):\n` +
      `      main       ${String(census.main).padStart(5)}  (940 cols x 2 points)\n` +
      `      prepro     ${String(census.prep).padStart(5)}  (175 cols x 2 points)\n` +
      `      quotient   ${String(census.quotient).padStart(5)}  (7 instances x 2 chunks x D=4)\n` +
      `      TOTAL      ${String(census.total).padStart(5)}  DEEP terms per query`,
  );

  const measure = async (perColumn: boolean, specs: ReturnType<typeof deployedDeepShape>) => {
    const cs = await Provable.constraintSystem(() => {
      const w = witnessDeepShape(DEPLOYED_KNOBS.logGlobalMaxHeight, specs);
      const ro = reducedOpenings({
        indexBits: w.indexBits,
        logGlobalMaxHeight: DEPLOYED_KNOBS.logGlobalMaxHeight,
        alpha: w.alpha,
        batches: w.batches,
        perColumn,
      });
      for (const o of ro) o.ro.limbs.forEach((x) => x.seal());
    });
    return cs.rows;
  };

  const shape = deployedDeepShape();
  const t0 = Date.now();
  deepFactored = await measure(false, shape);
  console.log(
    `    the whole DEEP quotient, ONE query, factored Horner : ` +
      `${deepFactored.toLocaleString()} rows   [${((Date.now() - t0) / 1000).toFixed(1)}s]`,
  );
  const t1 = Date.now();
  deepPerColumn = await measure(true, shape);
  console.log(
    `    the same, p3's literal per-column loop              : ` +
      `${deepPerColumn.toLocaleString()} rows   [${((Date.now() - t1) / 1000).toFixed(1)}s]` +
      `   (${(deepPerColumn / deepFactored).toFixed(2)}x)`,
  );
  deepPerTerm = deepFactored / census.total;
  console.log(
    `    per DEEP term: ${deepPerTerm.toFixed(1)} rows factored / ` +
      `${(deepPerColumn / census.total).toFixed(1)} literal`,
  );
  console.log(
    `    x 19 queries  : ${(deepFactored * 19).toLocaleString()} rows ` +
      `= ${((deepFactored * 19) / 1e6).toFixed(2)}e6`,
  );
  console.log(
    '    ⚑ §3.14 priced the DEEP+AIR residual at ~1.0e6 rows from "~2.4e4 ext ops".\n' +
      `      The DEEP quotient ALONE, at the root's own column census, is ` +
      `${((deepFactored * 19) / 1e6).toFixed(2)}e6.`,
  );

  if (deepFactored <= 0) fail('the deployed DEEP shape measured zero rows');
  if (deepPerColumn <= deepFactored)
    fail("p3's literal loop measured no more than the factored form — one of them is not building");
}

// ---------------------------------------------------------------------------
// [7] the DEPLOYED-scale seam: transcript + DEEP + one commit phase, jointly.
// ---------------------------------------------------------------------------
console.log('\n[7] the seam: transcript + DEEP quotient + the commit phase, JOINTLY');
let jointCapped = 0;
{
  // ⚑ MEASURED AT THE CAPPED CHAIN, AND THE DEPLOYED FIGURE IS A SUM — SAID SO.
  // `Provable.constraintSystem` serialises the whole gate vector through the
  // Kimchi wasm, and that allocator dies somewhere past ~8e5 rows: the joint
  // circuit at deployed Merkle depths is ~8.4e5 and OOMs the wasm heap, not
  // node. So the JOIN is measured on the capped chain — where it is the same
  // object, minus 216 Merkle levels that compose additively and were measured
  // standalone in §3.13 — and the deployed figure below is that measurement
  // plus the §3.13 delta, labelled as a composition rather than a measurement.
  const LOG_D0 = DEPLOYED_KNOBS.logGlobalMaxHeight;
  const LAYERS = DEPLOYED_KNOBS.layers;
  // The SAME stand-in preamble length §3.12 measured 62,637 at, so the three
  // standalone figures below are directly comparable and the join is a real
  // delta rather than an artefact of a longer absorb. (§3.16 measures what the
  // preamble actually costs: 2.97e6 rows, not 13 lanes.)
  const PRE = 13;
  const t0 = Date.now();
  const cs = await Provable.constraintSystem(() => {
    const t = witnessTranscriptShape(DEPLOYED_KNOBS, PRE);
    const ch = deriveFriChallenges(t, DEPLOYED_KNOBS);
    // ⚑ ONLY the matrices are witnessed here. The index bits and `alpha` come out
    // of the transcript, so re-witnessing them would put dead constraints inside
    // the very number the join is read from.
    const ro = reducedOpenings({
      indexBits: ch.queryIndexBits[0],
      logGlobalMaxHeight: LOG_D0,
      alpha: ch.alpha,
      batches: witnessDeepBatches(deployedDeepShape()),
    });
    verifyCommitPhase({
      indexBits: ch.queryIndexBits[0],
      initial: ro[0].ro,
      rounds: Array.from({ length: LAYERS }, (_, r) => ({
        sibling: Provable.witness(BbExt, () => BbExt.zero()),
        path: [] as BbDigest[],
        beta: ch.betas[r],
        commit: t.commits[r],
      })),
      rollIns: [],
      finalPoly: t.finalPoly,
      logGlobalMaxHeight: LOG_D0,
    });
  });
  jointCapped = cs.rows;

  // ⚑ AND THE JOIN IS ATTRIBUTED, NOT LEFT AS A MYSTERY. §3.13b measured the
  // transcript-plus-chain join at 58 rows; this one is three orders larger, so
  // the same circuit is measured WITHOUT the DEEP quotient to say how much of
  // the difference is the DEEP seam and how much is the pair that was already
  // measured.
  const noDeep = await Provable.constraintSystem(() => {
    const t = witnessTranscriptShape(DEPLOYED_KNOBS, PRE);
    const ch = deriveFriChallenges(t, DEPLOYED_KNOBS);
    verifyCommitPhase({
      indexBits: ch.queryIndexBits[0],
      initial: Provable.witness(BbExt, () => BbExt.zero()),
      rounds: Array.from({ length: LAYERS }, (_, r) => ({
        sibling: Provable.witness(BbExt, () => BbExt.zero()),
        path: [] as BbDigest[],
        beta: ch.betas[r],
        commit: t.commits[r],
      })),
      rollIns: [],
      finalPoly: t.finalPoly,
      logGlobalMaxHeight: LOG_D0,
    });
  });

  // The three standalone figures this is being joined from, all §3.12/§3.13/[6].
  const TRANSCRIPT = 62_637;
  const CAPPED_CHAIN = 45_186;
  const DEPLOYED_CHAIN = 623_310;
  const parts = TRANSCRIPT + CAPPED_CHAIN + deepFactored;
  console.log(
    `    transcript + DEEP + CAPPED commit phase (MEASURED)  : ` +
      `${jointCapped.toLocaleString()} rows   [${((Date.now() - t0) / 1000).toFixed(1)}s]`,
  );
  console.log(
    `    the three parts standalone                          : ${parts.toLocaleString()} rows ` +
      `(${TRANSCRIPT.toLocaleString()} + ${CAPPED_CHAIN.toLocaleString()} + ` +
      `${deepFactored.toLocaleString()})`,
  );
  console.log(
    `    the SAME circuit without the DEEP quotient (MEASURED): ` +
      `${noDeep.rows.toLocaleString()} rows`,
  );
  console.log(
    `    ... vs transcript + capped chain standalone         : ` +
      `${(TRANSCRIPT + CAPPED_CHAIN).toLocaleString()} rows ` +
      `(join ${(noDeep.rows - TRANSCRIPT - CAPPED_CHAIN).toLocaleString()}; §3.13b measured 58)`,
  );
  console.log(
    `    so the DEEP quotient's own seam costs               : ` +
      `${(jointCapped - noDeep.rows - deepFactored).toLocaleString()} rows on top of ` +
      `its ${deepFactored.toLocaleString()}`,
  );
  console.log(
    `    the JOIN, over all three standalone figures         : ` +
      `${(jointCapped - parts).toLocaleString()} rows`,
  );
  const deployedJoint = jointCapped + (DEPLOYED_CHAIN - CAPPED_CHAIN);
  console.log(
    `    at DEPLOYED Merkle depths (COMPOSED, not measured)   : ` +
      `${deployedJoint.toLocaleString()} rows`,
  );
  const USABLE_LOW = 48000;
  const USABLE_HIGH = 55000;
  console.log(
    `    = ${Math.ceil(deployedJoint / USABLE_HIGH)}-${Math.ceil(deployedJoint / USABLE_LOW)} ` +
      `Pickles steps for ONE query; 19 of them = ` +
      `${Math.ceil((deployedJoint * 19) / USABLE_HIGH)}-${Math.ceil((deployedJoint * 19) / USABLE_LOW)}`,
  );
  console.log(
    '    ⚑ Still missing from this statement: the input-phase MMCS openings\n' +
      '      (§3.14, ~6.3e5 rows/query) and the AIR constraint evaluation at zeta.',
  );
  // A join that costs nothing means the two halves are not actually joined.
  if (Math.abs(jointCapped - parts) < 1)
    fail('the join cost exactly zero rows — the DEEP output is not feeding the chain');
}

// ---------------------------------------------------------------------------
// §3.15, all MEASURED 2026-07-28 on o1js 2.15.0.
const RECORDED_DEEP_FACTORED = 154_523;
const RECORDED_DEEP_PERCOLUMN = 287_123;
const RECORDED_JOINT = 280_513;
const RECORDED_SEAM = 50_409;
const RECORDED_BINDING_DELTA = 1_754;
const RATCHET: [string, number, number][] = [
  ['the deployed DEEP quotient (factored)', deepFactored, RECORDED_DEEP_FACTORED],
  ["the deployed DEEP quotient (p3's per-column loop)", deepPerColumn, RECORDED_DEEP_PERCOLUMN],
  ['transcript + DEEP + the capped commit phase', jointCapped, RECORDED_JOINT],
  ['the proved DEEP-bound seam', deepSeamRows, RECORDED_SEAM],
  // ⚑ The ONE figure here that is a soundness ratchet rather than a size one.
  ['the BINDING DELTA (DEEP-bound minus witnessed-initial)', bindingDelta, RECORDED_BINDING_DELTA],
];
for (const [what, got, want] of RATCHET) {
  if (want === 0) fail(`${what} has no recorded figure — an unratcheted number is not measured`);
  const drift = Math.abs(got - want) / want;
  if (drift > 0.02)
    fail(
      `rows for ${what} moved to ${got} from the recorded ${want} (${(drift * 100).toFixed(1)}%): ` +
        'docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.15 is stale',
    );
}
console.log(
  `\n    ratchet: ${deepFactored.toLocaleString()} DEEP / ${jointCapped.toLocaleString()} joint rows ` +
    'are both within 2% of the recorded figures',
);

console.log('\n=== FRI DEEP PASS ===\n');

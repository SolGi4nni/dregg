// RUNG 7 — THE AIR CONSTRAINT EVALUATION AT ZETA, started and honestly priced.
//
//   npm run air-eval
//
// Rungs 1-5 authenticate a value; rung 6 ties it to the CLAIMED out-of-domain
// evaluations. Nothing yet says those evaluations satisfy dregg's constraint
// system, so a verifier stopping at rung 6 certifies that some low-degree
// function takes some values at zeta — true of an arbitrary polynomial, and a
// statement about nothing dregg does.
//
// The closing object is `VerifierData::verify_constraints_with_lookups`:
//
//     accumulator = fold_i alpha (C_i(...))
//     accumulator * inv_vanishing(zeta) == quotient(zeta)
//
// with `quotient(zeta)` recomposed from the opened chunks by Lagrange over the
// chunk domains. THIS LEG BUILDS EVERYTHING EXCEPT `C_i`, KAT'd against p3's own
// `TwoAdicMultiplicativeCoset` algebra, and prices the whole against the ROOT's
// real table set.
//
// ⚑ AND IT SAYS PLAINLY WHAT IS STILL UNCOUNTED. The number of constraints per
// AIR is the one quantity nobody has measured, so the AIR price is reported as
// `A + N*h` with `A` and `h` MEASURED and `N` named — not as a number with an
// invented `N` folded inside it. §2.4 already made that mistake once at a 7x
// error on the Horner unit alone.
//
// ⚑ THE TABLE SET IS THE ROOT'S SEVEN, NOT THE SHRINK'S FIVE. `degree_bits =
// [9,9,15,14,15]` is the BN254 shrink proof (§1.2). Using it here would
// under-count the AIR side by more than an order of magnitude, and that
// mis-attribution has already been made once in this tree.

import { Field, Provable } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { P } from '../src/Poseidon2BabyBearW16.js';
import { BbExt, extMulBigInt, extAddBigInt, extSubBigInt } from '../src/FriQueryStep.js';
import { extInvBigInt, rootDeepTermCount } from '../src/DeepQuotient.js';
import {
  ROOT_LOG_TRACE_HEIGHT,
  ROOT_N_CHUNKS,
  assertQuotientConsistency,
  foldConstraints,
  fromExtBasisCoefficients,
  recomposeQuotient,
  rootColumnCensus,
  selectorsAtPoint,
  vanishingAtPoint,
  witnessInstanceShape,
} from '../src/AirEval.js';

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
function runAir(dir: string, seed: number, degreeBits: number, logChunks: number, nC: number): any {
  const out = execFileSync(
    'cargo',
    [
      'run',
      '--offline',
      '--quiet',
      '--',
      'p2air',
      String(seed),
      String(degreeBits),
      String(logChunks),
      String(nC),
    ],
    { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 24 },
  );
  return JSON.parse(out);
}

const dir = probeDir();
const EXT_ONE = [1n, 0n, 0n, 0n];

console.log('=== Rung 7: the AIR CONSTRAINT EVALUATION at zeta ===\n');

// ---------------------------------------------------------------------------
console.log('[1] the LAGRANGE SELECTORS at zeta == p3');
let em: any;
{
  // ⚑ SEVERAL DEGREE BITS, NOT ONE. `Z_H(X) = (g^-1 X)^{2^k} - 1` is a chain of
  // `k` squarings; a fixture at one `k` cannot see an off-by-one in it, exactly
  // as one FRI round could not see the coset-descent sign.
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  for (const degreeBits of [4, 9, 15, 16]) {
    const e = runAir(dir, seed, degreeBits, 1, 5);
    if (!em) em = e;
    const zeta = e.zeta.map(B);
    const shiftInv = 1n; //   the trace domain's shift is ONE (`traceShift` below)
    if (B(e.traceShift) !== 1n)
      fail(`the trace domain's shift is ${e.traceShift}, not 1 — the circuit assumes 1`);

    // Z_H(zeta), out of circuit.
    let pow = zeta;
    for (let i = 0; i < degreeBits; i++) pow = extMulBigInt(pow, pow);
    const zH = extSubBigInt(pow, EXT_ONE);
    if (!eqv(zH, e.vanishingAtZeta.map(B)))
      fail(`k=${degreeBits}: Z_H(zeta) is ${zH}, p3 says ${e.vanishingAtZeta}`);

    const gInv = B(e.subgroupGeneratorInv);
    const isTransition = extSubBigInt(zeta, [gInv, 0n, 0n, 0n]);
    const isFirst = extMulBigInt(zH, extInvBigInt(extSubBigInt(zeta, EXT_ONE)));
    const isLast = extMulBigInt(zH, extInvBigInt(isTransition));
    const invVan = extInvBigInt(zH);
    for (const [what, got, want] of [
      ['is_first_row', isFirst, e.isFirstRow],
      ['is_last_row', isLast, e.isLastRow],
      ['is_transition', isTransition, e.isTransition],
      ['inv_vanishing', invVan, e.invVanishing],
    ] as [string, bigint[], string[]][])
      if (!eqv(got, want.map(B))) fail(`k=${degreeBits}: ${what} is ${got}, p3 says ${want}`);

    // ⚑ THE OFF-BY-ONE TWIN, LIVE: `k-1` squarings instead of `k`.
    let short = zeta;
    for (let i = 0; i < degreeBits - 1; i++) short = extMulBigInt(short, short);
    if (eqv(extSubBigInt(short, EXT_ONE), zH))
      fail(`k=${degreeBits}: one squaring fewer gave the same Z_H — the check is blind`);
    void shiftInv;
    ok(`degree_bits = ${degreeBits} — all four selectors and Z_H(zeta) agree with p3`);
  }
  ok(`emitter: ${em.emitter}`);
}

// ---------------------------------------------------------------------------
console.log('\n[2] the CONSTRAINT FOLD and the QUOTIENT RECOMPOSITION == p3');
{
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const e = runAir(dir, seed, ROOT_LOG_TRACE_HEIGHT, 1, 9);
  const alpha = e.alpha.map(B);
  const cs = e.constraints.map((c: string[]) => c.map(B));

  // p3 folds from ZERO: `acc *= alpha; acc += C`. Starting at `C_0` and doing
  // `acc*alpha + C_i` is the same value with one fewer degenerate multiply.
  let acc = cs[0];
  for (let i = 1; i < cs.length; i++) acc = extAddBigInt(extMulBigInt(acc, alpha), cs[i]);
  if (!eqv(acc, e.accumulator.map(B)))
    fail(`the constraint fold is ${acc}, p3 says ${e.accumulator}`);
  ok(`the alpha-folded accumulator over ${cs.length} constraints agrees with p3`);

  // Discriminating: the ORDER is load-bearing.
  const rev = cs.slice().reverse();
  let racc = rev[0];
  for (let i = 1; i < rev.length; i++) racc = extAddBigInt(extMulBigInt(racc, alpha), rev[i]);
  if (eqv(racc, acc)) fail('reversing the constraint order gave the same accumulator');
  ok('reversing the constraint order gives a DIFFERENT accumulator (the fold is ordered)');

  // The quotient recomposition, out of circuit, against p3's zps.
  const chunkShifts = e.chunkShifts.map(B);
  const lag = e.lagrangeConsts.map((r: string[]) => r.map(B));
  const zeta = e.zeta.map(B);
  const zAt = chunkShifts.map((s: bigint) => {
    const si = extInvBigInt([s, 0n, 0n, 0n]);
    let u = extMulBigInt(zeta, si);
    for (let i = 0; i < e.chunkLogSize; i++) u = extMulBigInt(u, u);
    return extSubBigInt(u, EXT_ONE);
  });
  const zps: bigint[][] = [];
  for (let i = 0; i < ROOT_N_CHUNKS; i++) {
    let zp = EXT_ONE;
    for (let j = 0; j < ROOT_N_CHUNKS; j++) {
      if (j === i) continue;
      zp = extMulBigInt(zp, zAt[j].map((v: bigint) => md(v * lag[i][j])));
    }
    zps.push(zp);
  }
  zps.forEach((z, i) => {
    if (!eqv(z, e.zps[i].map(B))) fail(`zps[${i}] is ${z}, p3 says ${e.zps[i]}`);
  });
  ok(`the ${ROOT_N_CHUNKS} Lagrange chunk weights agree with p3 (shift ${chunkShifts.join(', ')})`);

  // ⚑ THE SHIFT TWIN. `create_disjoint_domain` multiplies by GENERATOR and
  // `split_domains` by h^i. Dropping the chunk shift (i.e. reading shift = 1)
  // must move the weights, or the whole recomposition is unpinned.
  const zAtNoShift = chunkShifts.map(() => {
    let u = zeta;
    for (let i = 0; i < e.chunkLogSize; i++) u = extMulBigInt(u, u);
    return extSubBigInt(u, EXT_ONE);
  });
  let zpNo = EXT_ONE;
  for (let j = 1; j < ROOT_N_CHUNKS; j++)
    zpNo = extMulBigInt(zpNo, zAtNoShift[j].map((v: bigint) => md(v * lag[0][j])));
  if (eqv(zpNo, zps[0]))
    fail('dropping the chunk-domain shift left the Lagrange weights unchanged');
  ok('dropping the chunk-domain shift MOVES the weights (GENERATOR and h^i are load-bearing)');

  // and the full recomposition, in circuit.
  await Provable.runAndCheck(() => {
    const wz = Provable.witness(BbExt, () => BbExt.from(zeta));
    const chunks = e.chunks.map((c: string[][]) =>
      c.map((v: string[]) => Provable.witness(BbExt, () => BbExt.from(v.map(B)))),
    );
    const q = recomposeQuotient({
      zeta: wz,
      chunks,
      logChunkSize: e.chunkLogSize,
      chunkShiftInvs: chunkShifts.map((s: bigint) => extInvBigInt([s, 0n, 0n, 0n])[0]),
      lagrangeConsts: lag,
    });
    Provable.asProver(() => {
      if (!eqv(q.toBigInts(), e.quotient.map(B)))
        fail(`the in-circuit quotient is ${q.toBigInts()}, p3 says ${e.quotient}`);
    });
  });
  ok("the CIRCUIT recomposes p3's quotient(zeta) from the opened chunks");

  // the selectors and the fold, in circuit, and the closing equality.
  await Provable.runAndCheck(() => {
    const wz = Provable.witness(BbExt, () => BbExt.from(zeta));
    const s = selectorsAtPoint(wz, ROOT_LOG_TRACE_HEIGHT, 1n, B(e.subgroupGeneratorInv));
    const wa = Provable.witness(BbExt, () => BbExt.from(alpha));
    const wc = cs.map((c: bigint[]) => Provable.witness(BbExt, () => BbExt.from(c)));
    const f = foldConstraints(wa, wc);
    Provable.asProver(() => {
      if (!eqv(s.isFirstRow.toBigInts(), e.isFirstRow.map(B)))
        fail('the in-circuit is_first_row diverges');
      if (!eqv(s.invVanishing.toBigInts(), e.invVanishing.map(B)))
        fail('the in-circuit inv_vanishing diverges');
      if (!eqv(f.toBigInts(), e.accumulator.map(B)))
        fail('the in-circuit constraint fold diverges');
    });
    const lhs = e.foldedTimesInvVanishing.map(B);
    Provable.asProver(() => {
      if (!eqv(extMulBigInt(e.accumulator.map(B), e.invVanishing.map(B)), lhs))
        fail('p3\'s own accumulator * inv_vanishing does not match its emitted product');
    });
  });
  ok('the CIRCUIT computes p3\'s selectors and p3\'s folded accumulator');

  // `from_ext_basis_coefficients` is a lane shift with a W-fold, not four
  // extension multiplies. Checked against the emitted chunk values.
  await Provable.runAndCheck(() => {
    const ch = e.chunks[0].map((v: string[]) =>
      Provable.witness(BbExt, () => BbExt.from(v.map(B))),
    );
    const v = fromExtBasisCoefficients(ch);
    Provable.asProver(() => {
      // `zps[0] * from_ext(chunk0) + zps[1] * from_ext(chunk1) == quotient`.
      const other = fromExtBasisCoefficientsBigInt(e.chunks[1].map((x: string[]) => x.map(B)));
      const q = extAddBigInt(
        extMulBigInt(e.zps[0].map(B), v.toBigInts()),
        extMulBigInt(e.zps[1].map(B), other),
      );
      if (!eqv(q, e.quotient.map(B)))
        fail('from_ext_basis_coefficients does not reproduce p3\'s quotient');
    });
  });
  ok('`from_ext_basis_coefficients` is the lane shift with the W-fold, and it reproduces p3');
}

/** `sum_k ch[k] * X^k` over the extension basis, out of circuit. */
function fromExtBasisCoefficientsBigInt(ch: bigint[][]): bigint[] {
  const W = 11n;
  const out = [0n, 0n, 0n, 0n];
  for (let k = 0; k < ch.length; k++)
    for (let i = 0; i < 4; i++) {
      const d = k + i;
      const slot = d < 4 ? d : d - 4;
      const scale = d < 4 ? 1n : W;
      out[slot] = md(out[slot] + scale * ch[k][i]);
    }
  return out;
}

// ---------------------------------------------------------------------------
console.log('\n[3] the closing equality REFUSES a quotient the constraints do not fold to');
{
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const e = runAir(dir, seed, ROOT_LOG_TRACE_HEIGHT, 1, 7);
  const zeta = e.zeta.map(B);
  const alpha = e.alpha.map(B);
  const cs = e.constraints.map((c: string[]) => c.map(B));
  const lag = e.lagrangeConsts.map((r: string[]) => r.map(B));
  const shiftInvs = e.chunkShifts.map((s: string) => extInvBigInt([B(s), 0n, 0n, 0n])[0]);

  // The honest witness: chunks whose recomposition IS `accumulator/Z_H`. p3's
  // emitted chunks are random, so they will NOT satisfy it — which is the point:
  // the honest instance has to be CONSTRUCTED, and that construction is the
  // statement. Solve for chunk 1 given chunk 0.
  const target = extMulBigInt(e.accumulator.map(B), e.invVanishing.map(B));
  const ch0 = e.chunks[0].map((v: string[]) => v.map(B));
  const v0 = fromExtBasisCoefficientsBigInt(ch0);
  const rest = extSubBigInt(target, extMulBigInt(e.zps[0].map(B), v0));
  const need = extMulBigInt(rest, extInvBigInt(e.zps[1].map(B)));
  // `from_ext_basis_coefficients` is the identity on the basis when each ch[k]
  // is the BASE embedding of the k-th coefficient, so a chunk of base lanes
  // reproduces `need` exactly.
  const ch1 = need.map((c) => [c, 0n, 0n, 0n]);
  if (!eqv(fromExtBasisCoefficientsBigInt(ch1), need))
    fail('the constructed chunk does not reassemble to the value it was solved for');

  const run = async (chunks: bigint[][][]) =>
    Provable.runAndCheck(() => {
      const wz = Provable.witness(BbExt, () => BbExt.from(zeta));
      const wa = Provable.witness(BbExt, () => BbExt.from(alpha));
      const wc = cs.map((c: bigint[]) => Provable.witness(BbExt, () => BbExt.from(c)));
      const wch = chunks.map((c) =>
        c.map((v) => Provable.witness(BbExt, () => BbExt.from(v))),
      );
      assertQuotientConsistency({
        zeta: wz,
        alpha: wa,
        constraints: wc,
        logSize: ROOT_LOG_TRACE_HEIGHT,
        shiftInv: 1n,
        subgroupGenInv: B(e.subgroupGeneratorInv),
        chunks: wch,
        logChunkSize: e.chunkLogSize,
        chunkShiftInvs: shiftInvs,
        lagrangeConsts: lag,
      });
    });

  await run([ch0, ch1]);
  ok('the closing equality ACCEPTS a quotient the constraints DO fold to');

  for (const [label, mutate] of [
    ['a quotient chunk one lane off', () => [ch0, ch1.map((c, i) => (i === 0 ? [md(c[0] + 1n), c[1], c[2], c[3]] : c))]],
    ['the two chunks swapped', () => [ch1, ch0]],
  ] as [string, () => bigint[][][]][]) {
    let held = false;
    try {
      await run(mutate());
      held = true;
    } catch {
      /* expected */
    }
    if (held) fail(`the closing equality accepted ${label}`);
    ok(`the closing equality REFUSES ${label}`);
  }

  // and a constraint one off — which is the whole point of the rung.
  let held = false;
  try {
    const bad = cs.map((c: bigint[], i: number) => (i === 3 ? [md(c[0] + 1n), c[1], c[2], c[3]] : c));
    await Provable.runAndCheck(() => {
      const wz = Provable.witness(BbExt, () => BbExt.from(zeta));
      const wa = Provable.witness(BbExt, () => BbExt.from(alpha));
      const wc = bad.map((c: bigint[]) => Provable.witness(BbExt, () => BbExt.from(c)));
      const wch = ([ch0, ch1] as bigint[][][]).map((c) =>
        c.map((v: bigint[]) => Provable.witness(BbExt, () => BbExt.from(v))),
      );
      assertQuotientConsistency({
        zeta: wz,
        alpha: wa,
        constraints: wc,
        logSize: ROOT_LOG_TRACE_HEIGHT,
        shiftInv: 1n,
        subgroupGenInv: B(e.subgroupGeneratorInv),
        chunks: wch,
        logChunkSize: e.chunkLogSize,
        chunkShiftInvs: shiftInvs,
        lagrangeConsts: lag,
      });
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a constraint one off still satisfied the closing equality');
  ok('a CONSTRAINT one off breaks the closing equality (the AIR is what is being checked)');
}

// ---------------------------------------------------------------------------
console.log('\n[4] getRows() — the AIR side at the ROOT\'s 7 tables');
let perInstanceFixed = 0;
let perConstraint = 0;
{
  const measure = async (numConstraints: number) => {
    const cs = await Provable.constraintSystem(() => {
      const w = witnessInstanceShape(numConstraints);
      assertQuotientConsistency({
        zeta: w.zeta,
        alpha: w.alpha,
        constraints: w.constraints,
        logSize: ROOT_LOG_TRACE_HEIGHT,
        shiftInv: 1n,
        subgroupGenInv: 3n,
        chunks: w.chunks,
        logChunkSize: ROOT_LOG_TRACE_HEIGHT,
        chunkShiftInvs: [1n, 5n],
        lagrangeConsts: [
          [1n, 7n],
          [11n, 1n],
        ],
      });
    });
    return cs.rows;
  };
  const at0 = await measure(1);
  const at101 = await measure(101);
  perConstraint = (at101 - at0) / 100;
  perInstanceFixed = at0 - perConstraint;
  console.log(
    `    per-instance FIXED cost (selectors at k=${ROOT_LOG_TRACE_HEIGHT}, chunk recomposition,\n` +
      `      the closing equality)                       : ${perInstanceFixed.toFixed(0)} rows`,
  );
  console.log(
    `    per CONSTRAINT (the alpha fold only, NOT C_i)  : ${perConstraint.toFixed(0)} rows`,
  );
  if (perConstraint <= 0) fail('a constraint measured no rows — the fold is being optimised away');

  const census = rootColumnCensus();
  const deep = rootDeepTermCount();
  const fixedAll = perInstanceFixed * census.tables;
  console.log(
    `\n    the ROOT: ${census.tables} tables, ${census.main} main + ${census.prep} preprocessed ` +
      `= ${census.total} columns; ${deep.total} DEEP terms/query`,
  );
  console.log(
    `    the AIR side is  A + N*h  with  A = ${fixedAll.toLocaleString()} rows ` +
      `(${census.tables} x ${perInstanceFixed.toFixed(0)}) and h = ${perConstraint.toFixed(0)} rows,\n` +
      `    N = the TOTAL number of AIR constraints across the 7 tables.`,
  );
  console.log('\n    ⚑ N IS UNCOUNTED. What it implies, if it were known:');
  console.log('      N (constraints)   |  fold rows   |  + A       |  and this is STILL not C_i');
  console.log('      ------------------+--------------+------------+---------------------------');
  for (const ratio of [0.5, 1, 2, 3]) {
    const N = Math.round(census.total * ratio);
    const foldRows = N * perConstraint;
    console.log(
      `      ${String(N).padStart(5)} (${ratio}x cols) | ` +
        `${String(Math.round(foldRows).toLocaleString()).padStart(12)} | ` +
        `${String(Math.round(foldRows + fixedAll).toLocaleString()).padStart(10)} |`,
    );
  }
  console.log(
    '\n    ⚑ AND `C_i` ITSELF IS NOT IN ANY OF THOSE NUMBERS. A degree-3 constraint\n' +
      '      over extension values costs at least two extension multiplies (~62 rows)\n' +
      "      on top of its fold, so the table above is a FLOOR on the AIR side, not an\n" +
      '      estimate of it. Naming that is the point: §2.4 put a guessed unit inside a\n' +
      '      guessed count and was 7x out on the unit alone.',
  );
  console.log(
    `\n    ⚑ ONE THING THE AIR SIDE DOES MAKE EXACT. Every one of the ${deep.total} opened\n` +
      `      values is OBSERVED into the challenger before alpha is sampled\n` +
      `      (two_adic_pcs.rs:780-788) — ${deep.total * 4} lanes = ` +
      `${Math.ceil((deep.total * 4) / 8)} permutations at 2,600.5 rows\n` +
      `      = ${Math.round((Math.ceil((deep.total * 4) / 8) * 2600.5) / 1e6 * 100) / 100}e6 rows. ` +
      `§3.12 stood that whole preamble in with 32 lanes.`,
  );
}

// ---------------------------------------------------------------------------
// §3.16, MEASURED 2026-07-28 on o1js 2.15.0.
const RECORDED_PER_INSTANCE = 2025;
const RECORDED_PER_CONSTRAINT = 48;
for (const [what, got, want] of [
  ['the per-instance AIR fixed cost', perInstanceFixed, RECORDED_PER_INSTANCE],
  ['the per-constraint fold', perConstraint, RECORDED_PER_CONSTRAINT],
] as [string, number, number][]) {
  if (want === 0) fail(`${what} has no recorded figure — an unratcheted number is not measured`);
  const drift = Math.abs(got - want) / want;
  if (drift > 0.02)
    fail(
      `${what} moved to ${got} from the recorded ${want} (${(drift * 100).toFixed(1)}%): ` +
        'docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.16 is stale',
    );
}
console.log(
  `\n    ratchet: ${perInstanceFixed} per-instance / ${perConstraint} per-constraint rows ` +
    'are both within 2% of the recorded figures',
);

console.log('\n=== AIR EVAL PASS ===\n');
void Field;

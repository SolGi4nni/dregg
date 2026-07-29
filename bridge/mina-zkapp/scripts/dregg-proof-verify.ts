// THE ASSEMBLY — one ZkProgram that takes a dregg FRI-STARK proof and DECIDES.
//
//   npm run dregg-verify
//
// Rungs 1-7 built and measured every piece of a Mina-side dregg verifier and
// assembled none of them. Each is fed by a fixture the MEASUREMENT synthesised:
// an opened row no prover produced, a fold chain over a value nobody committed
// to, a transcript whose preamble is a stand-in. "Mina verifies dregg" is not a
// statement about a set of components.
//
// This leg is the assembly. `circuit/src/bin/mina_stark_fixture.rs` mints a REAL
// proof with `p3_uni_stark::prove` under `DreggStarkConfig` — the same
// Poseidon2-w16 permutation, the same `PaddingFreeSponge`/`TruncatedPermutation`
// MMCS, the same `DuplexChallenger`, the same degree-4 extension, the same
// `TwoAdicFriPcs` the deployed root runs, with the six FRI knobs turned down —
// verifies it with dregg's OWN verifier before emitting anything, and
// `DreggProofVerify` consumes it: transcript, AIR closing equality, DEEP
// quotient, MMCS openings and fold chain, all in one Pickles step.
//
// ⚑ WHAT IT DOES AND DOES NOT SAY. The FRI/PCS/transcript machinery is dregg's
// at reduced knobs. The AIR is a 3-column degree-3 fixture AIR, NOT one of
// dregg's seven root tables — because `C_i` for those is not built and `N` is
// not counted (§3.14). At the fixture AIR this program is CLOSED: it evaluates
// the constraints itself, and [6] shows the closing equality REFUSING a bent
// one, so it is not decoration. At the root's AIRs it would be the same program
// with a different evaluator and a row count [8] measures.
//
// ⚑ EVERY REFUSAL BELOW IS A REAL `prove` REFUSAL, NOT `runAndCheck`. §3.15e:
// `Provable.runAndCheck` does not evaluate lookup constraints, and a derived
// variable is indistinguishable from a witness carrying its value to
// `runAndCheck`, to `prove` AND to `getRows()`. Where a check is only a
// constraint-satisfaction check it says so in the line it prints.
//
// Needs cargo (the emitter) and a 16 GB node heap (the deployed-geometry
// measurement in [8]). ~6 min warm.

import { Provable } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { P } from '../src/Poseidon2BabyBearW16.js';
import { ChallengerBigInt, FriKnobs } from '../src/FriChallenger.js';
import { twoAdicGenerator } from '../src/FriQueryStep.js';
import {
  ConstraintEvaluator,
  DreggProofShape,
  claimOf,
  makeDreggProofVerifyProgram,
  minaFixtureConstraints,
  minaFixtureConstraintsBentDegree,
  minaFixtureConstraintsNoSelector,
  minaFixtureConstraintsPermuted,
  shapeOf,
  witnessOf,
} from '../src/DreggProofVerify.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const secs = (t: number) => ((Date.now() - t) / 1000).toFixed(1) + 's';
const B = (v: number | string) => BigInt(v);
const md = (x: bigint) => ((x % P) + P) % P;
const eqv = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);

// ---------------------------------------------------------------------------
// The dregg-side emitter.
// ---------------------------------------------------------------------------

function repoRoot(): string {
  const d = process.env.DREGG_REPO_ROOT ?? resolve(process.cwd(), '../..');
  if (!existsSync(resolve(d, 'circuit/src/bin/mina_stark_fixture.rs')))
    throw new Error(`the dregg-side proof emitter is not under ${d} — set DREGG_REPO_ROOT`);
  return d;
}
const ROOT = repoRoot();
let emitterBuilt = false;
function mint(
  degreeBits: number,
  logBlowup: number,
  numQueries: number,
  queryPowBits: number,
  seed: number,
  tamper = 'none',
): any {
  if (!emitterBuilt) {
    const t = Date.now();
    // ⚑ `--bin`, not `--example`: an example compiles DEV-dependencies, which
    // reach `dregg-lean-ffi`, whose build script fails closed while the Lean
    // tree is mid-edit. This leg is about Mina and must not go red for that.
    execFileSync('cargo', ['build', '-p', 'dregg-circuit', '--release', '--bin', 'mina_stark_fixture'], {
      cwd: ROOT,
      stdio: ['ignore', 'ignore', 'inherit'],
    });
    console.log(`    emitter built in ${secs(t)}`);
    emitterBuilt = true;
  }
  const out = execFileSync(
    resolve(ROOT, 'target/release/mina_stark_fixture'),
    [degreeBits, logBlowup, numQueries, queryPowBits, seed].map(String).concat([tamper]),
    { encoding: 'utf8', maxBuffer: 1 << 26 },
  );
  return JSON.parse(out);
}

/** Constraint-satisfaction only — sound for a REFUSAL (an unsatisfied
 *  constraint is unsatisfied), never quoted as an accept. */
async function satisfies(fx: any, cons: ConstraintEvaluator | undefined): Promise<boolean> {
  const sh = shapeOf(fx, { constraints: cons });
  const { prog, DreggProofClaim } = makeDreggProofVerifyProgram(sh);
  const claim = claimOf(fx, DreggProofClaim);
  const w = witnessOf(fx, sh);
  const types = (prog as any).privateInputTypes.verifyDreggProof;
  try {
    await Provable.runAndCheck(async () => {
      const c = Provable.witness(DreggProofClaim, () => claim);
      const pw = w.map((v: any, i: number) => Provable.witness(types[i], () => v));
      await (prog as any).rawMethods.verifyDreggProof(c, ...pw);
    });
    return true;
  } catch {
    return false;
  }
}

async function rowsOf(sh: DreggProofShape): Promise<number> {
  const { prog } = makeDreggProofVerifyProgram(sh);
  const a = await prog.analyzeMethods();
  return (a as any).verifyDreggProof.rows;
}

// ===========================================================================

console.log('=== the ASSEMBLY: one ZkProgram that decides a dregg proof ===\n');

// The geometry that fits in ONE Pickles step. Chosen by measurement in [8], not
// by taste: 73,259 rows (degree_bits 2) is REFUSED by the compiler.
const DB = 1;
const LB = 1;
const NQ = 1;
const QPOW = 16;

// ---------------------------------------------------------------------------
console.log('[1] the fixture is a proof DREGG MADE, and dregg accepts it first');
let fx: any;
{
  const t = Date.now();
  // A fresh seed every run: a fixture that could have been precomputed proves
  // nothing about a verifier.
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  fx = mint(DB, LB, NQ, QPOW, seed);
  if (fx.kind !== 'dregg-uni-stark-fixture') fail(`the emitter returned ${fx.kind}`);
  ok(
    `minted + self-verified by dregg's own p3_uni_stark::verify (seed ${seed}, ${secs(t)}) — ` +
      `degree_bits ${fx.shape.degreeBits}, log_blowup ${fx.knobs.logBlowup}, ` +
      `${fx.knobs.numQueries} quer${fx.knobs.numQueries === 1 ? 'y' : 'ies'}, ` +
      `${fx.shape.layers} fold layer(s), |D^0| = 2^${fx.shape.logGlobalMaxHeight}`,
  );
  // The shape is READ OFF the proof, not assumed. `log_global_max_height` is
  // `sum(log_arities) + log_blowup + log_final_poly_len` (`verifier.rs:201-203`).
  const lgmh = fx.shape.layers * fx.knobs.maxLogArity + fx.knobs.logBlowup + fx.knobs.logFinalPolyLen;
  if (lgmh !== fx.shape.logGlobalMaxHeight)
    fail(`the emitted log_global_max_height ${fx.shape.logGlobalMaxHeight} != the derived ${lgmh}`);
  ok('log_global_max_height is DERIVED from the proof\'s arity schedule and agrees');
  if (fx.shape.numQuotientChunks < 2)
    fail(
      `${fx.shape.numQuotientChunks} quotient chunk(s): the Lagrange recomposition degenerates ` +
        'and [6] would be measuring nothing',
    );
  ok(`${fx.shape.numQuotientChunks} quotient chunks — the Lagrange recomposition is a real product`);
  if (!fx.shape.hasTraceNext) fail('the fixture AIR has no next-row column: only one opening point');
  ok('the trace opens at TWO points (zeta, g*zeta) — the DEEP quotient runs multi-point');
}

// ---------------------------------------------------------------------------
console.log('\n[2] the o1js challenger reproduces p3\'s transcript, absorption for absorption');
{
  // ⚑ NOT A SELF-CHECK. `absorbed` is the exact base-field sequence p3's OWN
  // `DuplexChallenger` took in, recorded by the emitter; the schedule below is
  // the o1js twin's. Both alpha, zeta, the FRI alpha, every beta and every query
  // index have to come out the same, or the transcript the circuit derives is
  // not the transcript the prover ground against.
  const replay = (absorb: bigint[], knobs: FriKnobs, shape: any) => {
    const c = new ChallengerBigInt();
    let p = 0;
    const take = (n: number) => absorb.slice(p, (p += n));
    c.observeSlice(take(3)); //                          degree bits x2, preprocessed width
    c.observeSlice(take(8)); //                          commitments.trace
    c.observeSlice(take(shape.numPublicValues));
    const alphaStark = c.sampleExt();
    c.observeSlice(take(8)); //                          commitments.quotient_chunks
    const zeta = c.sampleExt();
    const nOpened =
      (shape.hasTraceNext ? 2 : 1) * shape.airWidth * 4 + shape.numQuotientChunks * 4 * 4;
    c.observeSlice(take(nOpened));
    const friAlpha = c.sampleExt();
    const betas: bigint[][] = [];
    for (let r = 0; r < knobs.layers; r++) {
      c.observeSlice(take(8));
      if (!c.checkWitness(knobs.commitPowBits, 0n)) throw new Error('commit PoW');
      betas.push(c.sampleExt());
    }
    c.observeSlice(take(4 * knobs.finalPolyLen)); //     final_poly
    c.observeSlice(take(knobs.layers)); //               the arity schedule
    const w = take(1)[0];
    const powOk = c.checkWitness(knobs.queryPowBits, w);
    if (p !== absorb.length)
      throw new Error(`the replay consumed ${p} of ${absorb.length} absorbed elements`);
    const indices = Array.from({ length: knobs.numQueries }, () => c.sampleBits(knobs.indexBits));
    return { alphaStark, zeta, friAlpha, betas, indices, powOk, perms: c.perms };
  };

  const sh = shapeOf(fx, {});
  const got = replay(fx.challenges.absorbed.map(B), sh.knobs, fx.shape);
  if (!got.powOk) fail('the o1js twin says the query PoW does not grind — p3 says it does');
  if (!eqv(got.alphaStark, fx.challenges.alphaStark.map(B)))
    fail(`alpha_stark: o1js ${got.alphaStark}, p3 ${fx.challenges.alphaStark}`);
  if (!eqv(got.zeta, fx.challenges.zeta.map(B)))
    fail(`zeta: o1js ${got.zeta}, p3 ${fx.challenges.zeta}`);
  if (!eqv(got.friAlpha, fx.challenges.friAlpha.map(B)))
    fail(`FRI alpha: o1js ${got.friAlpha}, p3 ${fx.challenges.friAlpha}`);
  got.betas.forEach((b, r) => {
    if (!eqv(b, fx.challenges.betas[r].map(B))) fail(`beta[${r}] diverges from p3`);
  });
  if (String(got.indices) !== String(fx.challenges.queryIndices))
    fail(`query indices: o1js ${got.indices}, p3 ${fx.challenges.queryIndices}`);
  ok(
    `alpha, zeta, the FRI alpha, ${got.betas.length} beta(s), the 16-bit grind and ` +
      `${got.indices.length} query index/indices all agree with p3 (${got.perms} permutations)`,
  );

  // ⚑ THE DISCRIMINATING POLARITY, AND IT HAD TO BE REPAIRED TO BE ONE.
  // A transcript twin that agrees no matter what it is fed is not a twin, so one
  // element of each REGION is bent and every derived value must move. The first
  // version of this compared only {zeta, friAlpha, indices} — which cannot see a
  // bend in the LAST absorbed element, the query PoW witness, because zeta and
  // the FRI alpha are sampled before it and the index is only `indexBits` wide
  // (2 here). It passed 3 of 4 and was a coin flip on the fourth. The grind's
  // own verdict is part of the comparison now.
  const nPre = 3 + 8 + fx.shape.numPublicValues; //          shape + trace commit + PIs
  const regions: [string, number][] = [
    ['the degree-bits prefix', 0],
    ['the trace commitment', 4],
    ['a public value', nPre - 1],
    ['the quotient commitment', nPre + 4],
    ['a claimed opened evaluation', nPre + 8 + 3],
    ['a final-polynomial coefficient', fx.challenges.absorbed.length - 2 - sh.knobs.layers],
    ['an arity-schedule tag', fx.challenges.absorbed.length - 2],
    ['the query PoW witness', fx.challenges.absorbed.length - 1],
  ];
  const same = (g: any) =>
    g.powOk === got.powOk &&
    eqv(g.zeta, got.zeta) &&
    eqv(g.friAlpha, got.friAlpha) &&
    eqv(g.alphaStark, got.alphaStark) &&
    g.betas.every((b: bigint[], i: number) => eqv(b, got.betas[i])) &&
    String(g.indices) === String(got.indices);
  for (const [label, pos] of regions) {
    if (pos < 0 || pos >= fx.challenges.absorbed.length)
      fail(`the polarity for ${label} indexes ${pos}, outside the ${fx.challenges.absorbed.length} absorbed`);
    const bent = fx.challenges.absorbed.map(B);
    bent[pos] = md(bent[pos] + 1n);
    let moved: boolean;
    try {
      moved = !same(replay(bent, sh.knobs, fx.shape));
    } catch {
      moved = true;
    }
    if (!moved) fail(`bending ${label} (position ${pos}) left every challenge unchanged`);
  }
  ok(`bending any of ${regions.length} transcript regions moves a challenge — the twin is not a constant`);
}

// ---------------------------------------------------------------------------
console.log('\n[3] the two-adic generator the circuit folds in is p3\'s');
{
  const g = twoAdicGenerator(fx.domain.traceLogSize);
  if (md(g * B(fx.domain.subgroupGenInv)) !== 1n)
    fail(
      `g_${fx.domain.traceLogSize} = ${g} is not the inverse of the generator p3's domain algebra ` +
        `emitted (${fx.domain.subgroupGenInv}) — zeta_next and every selector would be wrong`,
    );
  ok(`g_${fx.domain.traceLogSize} * (p3's subgroup_generator^{-1}) == 1`);
  const lag = fx.domain.lagrangeConstInvs;
  if (lag.length !== fx.shape.numQuotientChunks) fail('the Lagrange constant table is the wrong size');
  let offDiagNonTrivial = 0;
  lag.forEach((row: any[], i: number) =>
    row.forEach((v: any, j: number) => {
      if (i !== j && B(v) !== 1n) offDiagNonTrivial++;
    }),
  );
  if (offDiagNonTrivial === 0)
    fail('every off-diagonal Lagrange constant is 1 — the recomposition is a sum, not a Lagrange');
  ok(`${offDiagNonTrivial} non-trivial off-diagonal Lagrange constants from p3's chunk domains`);
}

// ---------------------------------------------------------------------------
console.log('\n[4] the program: rows, and the ceiling that fixed the geometry');
const SHAPE = shapeOf(fx, { constraints: minaFixtureConstraints });
let provedRows = 0;
{
  const t = Date.now();
  provedRows = await rowsOf(SHAPE);
  console.log(`    the assembled verifier: ${provedRows.toLocaleString()} rows  [${secs(t)}]`);
  const KIMCHI_ROWS = 65536;
  if (provedRows >= KIMCHI_ROWS)
    fail(`${provedRows} rows is past the 2^16 Pickles step domain — this geometry cannot prove`);
  ok(
    `${provedRows.toLocaleString()} rows = ${((provedRows / KIMCHI_ROWS) * 100).toFixed(1)}% of the ` +
      `2^16 step domain`,
  );
}

// ---------------------------------------------------------------------------
console.log('\n[5] COMPILE, PROVE, VERIFY — a real Pickles proof of a real dregg proof');
let prog: any;
let Claim: any;
{
  const built = makeDreggProofVerifyProgram(SHAPE);
  prog = built.prog;
  Claim = built.DreggProofClaim;
  let t = Date.now();
  const { verificationKey } = await prog.compile();
  ok(`compiled in ${secs(t)} (vk hash ${verificationKey.hash.toString().slice(0, 16)}…)`);

  t = Date.now();
  const { proof } = await prog.verifyDreggProof(claimOf(fx, Claim), ...witnessOf(fx, SHAPE));
  const proveTime = secs(t);
  t = Date.now();
  if (!(await prog.verify(proof))) fail('the produced proof does not verify');
  ok(`PROVED in ${proveTime} and VERIFIED in ${secs(t)} — a dregg proof, decided on Mina's field`);

  // ⚑ THE SEAM, VISIBLE. The public output is the query index the CIRCUIT
  // derived from the transcript. It has to be the one p3's own challenger drew,
  // or the walk happened somewhere the prover was never bound to.
  const derived = proof.publicOutput.map((f: any) => Number(f.toBigInt()));
  if (String(derived) !== String(fx.challenges.queryIndices))
    fail(`the circuit walked ${derived}; p3's challenger drew ${fx.challenges.queryIndices}`);
  ok(`the PROVEN public output — query index ${derived} — is the one p3's challenger drew`);
}

// ---------------------------------------------------------------------------
console.log('\n[6] it DISCRIMINATES: seven bends, each refused by a real prove()');
{
  // Every bend is applied to the SAME proof structure the honest fixture came
  // from, and `mina_stark_fixture.rs` REQUIRES dregg's own verifier to refuse it
  // before emitting — a fault injection that no longer reaches its target
  // silently becomes a passing test.
  const BENDS = [
    ['opened', 'a claimed out-of-domain evaluation'],
    ['quotient', 'a quotient chunk'],
    ['finalpoly', 'the final polynomial'],
    ['sibling', 'a commit-phase sibling'],
    ['inputrow', 'an input-phase opened row element'],
    ['inputpath', 'an input-phase Merkle sibling'],
    ['querypow', 'the query PoW witness'],
  ] as const;
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  for (const [mode, what] of BENDS) {
    const bent = mint(DB, LB, NQ, QPOW, seed, mode);
    if (bent.tamper !== mode) fail(`the emitter returned tamper '${bent.tamper}' for '${mode}'`);
    let refused = false;
    try {
      await prog.verifyDreggProof(claimOf(bent, Claim), ...witnessOf(bent, SHAPE));
    } catch {
      refused = true;
    }
    if (!refused) fail(`the assembled verifier ACCEPTED a proof with ${what} bent`);
    ok(`prove() REFUSES ${what}`);
  }
}

// ---------------------------------------------------------------------------
console.log('\n[7] the AIR closing equality is load-bearing, shown REFUSING');
{
  // Rung 7 built the arithmetic around `C_i` and could not show it biting,
  // because nothing fed it a proof. Here the proof, the transcript, the openings
  // and the whole fold chain are IDENTICAL and only the constraint evaluator
  // moves — so a refusal is attributable to the AIR check and to nothing else.
  const t = Date.now();
  const bentAir = makeDreggProofVerifyProgram(
    shapeOf(fx, { constraints: minaFixtureConstraintsBentDegree }),
  );
  await bentAir.prog.compile();
  let refused = false;
  try {
    await (bentAir.prog as any).verifyDreggProof(
      claimOf(fx, bentAir.DreggProofClaim),
      ...witnessOf(fx, shapeOf(fx, { constraints: minaFixtureConstraintsBentDegree })),
    );
  } catch {
    refused = true;
  }
  if (!refused)
    fail(
      'an AIR reading `a^2` where dregg proved `a^3` still accepted the proof — the closing ' +
        'equality is decoration',
    );
  ok(`prove() REFUSES an AIR that reads a^2 where dregg proved a^3 (compile + attempt, ${secs(t)})`);

  // ⚑ AND THE CONTROL THAT MAKES THAT MEAN SOMETHING. Without the AIR check the
  // SAME proof is accepted — so [7] is measuring the constraint evaluation and
  // not some unrelated wiring difference.
  if (!(await satisfies(fx, undefined)))
    fail('the PCS-only statement refuses the honest proof — the control is broken');
  ok('the PCS-only statement (no AIR check) ACCEPTS the same proof — the control holds');
}

// ---------------------------------------------------------------------------
console.log('\n[8] the falsifiers that a SINGLE geometry cannot see');
{
  // ⚑ THE COSET-DESCENT LESSON, APPLIED TO THE AIR SIDE. Two of the four
  // constraints are boundary constraints, and on a TWO-ROW trace they collapse
  // into the same polynomial: with `|H| = 2`, `is_first_row = X+1` and
  // `is_last_row = X-1`, so both `C_1` and `C_3` are a multiple of `X^2-1` and
  // for this AIR they are the SAME multiple. A permuted fold order is therefore
  // INVISIBLE at the geometry that fits in a Pickles step. That is not a reason
  // to drop the falsifier; it is a reason to run it where it can fire.
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  const fx2 = mint(2, LB, NQ, QPOW, seed);

  const cases: [string, ConstraintEvaluator][] = [
    ['a^2 where dregg proved a^3', minaFixtureConstraintsBentDegree],
    ['the fold order permuted (C1 <-> C3)', minaFixtureConstraintsPermuted],
    ['is_transition dropped from C2', minaFixtureConstraintsNoSelector],
  ];
  for (const [label, cons] of cases) {
    const at1 = await satisfies(fx, cons);
    const at2 = await satisfies(fx2, cons);
    if (at2) fail(`'${label}' is accepted at degree_bits 2 — the falsifier does not fire anywhere`);
    ok(
      `'${label}' refuses at degree_bits 2` +
        (at1 ? ' — and is BLIND at degree_bits 1 (see below)' : ' and at degree_bits 1'),
    );
  }

  // The blindness is a PROVED identity, not an unexplained green: evaluate the
  // two boundary constraints at the emitted zeta from the emitted openings and
  // require them EQUAL at 2 rows and DIFFERENT at 4.
  const boundaryPair = (f: any) => {
    const md4 = (v: bigint[]) => v.map(md);
    const mul = (a: bigint[], b: bigint[]) => {
      const r = Array(7).fill(0n);
      for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) r[i + j] = md(r[i + j] + a[i] * b[j]);
      const o = r.slice(0, 4);
      for (let i = 4; i < 7; i++) o[i - 4] = md(o[i - 4] + 11n * r[i]);
      return md4(o);
    };
    const sub = (a: bigint[], b: bigint[]) => a.map((x, i) => md(x - b[i]));
    const one = [1n, 0n, 0n, 0n];
    const inv = (a: bigint[]) => {
      let r = one.slice();
      let b = a.slice();
      let e = P ** 4n - 2n;
      while (e > 0n) {
        if (e & 1n) r = mul(r, b);
        b = mul(b, b);
        e >>= 1n;
      }
      return r;
    };
    const z = f.challenges.zeta.map(B);
    const k = f.domain.traceLogSize;
    let zh = z.slice();
    for (let i = 0; i < k; i++) zh = mul(zh, zh);
    zh = sub(zh, one);
    const isFirst = mul(zh, inv(sub(z, one)));
    const isLast = mul(zh, inv(sub(z, [B(f.domain.subgroupGenInv), 0n, 0n, 0n])));
    const c = f.openedValues.traceLocal[2].map(B);
    const c1 = mul(isFirst, sub(c, [B(f.publicValues[0]), 0n, 0n, 0n]));
    const c3 = mul(isLast, sub(c, [B(f.publicValues[1]), 0n, 0n, 0n]));
    return [c1, c3];
  };
  const [a1, a3] = boundaryPair(fx);
  const [b1, b3] = boundaryPair(fx2);
  if (!eqv(a1, a3))
    fail(
      'C_1 and C_3 differ at degree_bits 1, so the permuted-order falsifier SHOULD have fired ' +
        'there and did not — the check above is not measuring what it says',
    );
  if (eqv(b1, b3))
    fail('C_1 and C_3 coincide at degree_bits 2 as well — the falsifier can never fire');
  ok(
    'C_1 == C_3 identically at 2 rows (both are the same multiple of X^2-1) and differ at 4 — ' +
      'the blindness is an identity, not a hole',
  );
}

// ---------------------------------------------------------------------------
console.log('\n[9] the challenges are DERIVED, and the row delta is the evidence');
{
  // §3.15e: a derived variable is indistinguishable from a witness carrying its
  // value to `runAndCheck`, to `prove` AND to `getRows()`. Only the DELTA
  // against a twin that witnesses them says the derivation is in the circuit.
  const witnessed = await rowsOf(
    shapeOf(fx, { constraints: minaFixtureConstraints, deriveChallenges: false }),
  );
  const delta = provedRows - witnessed;
  if (delta <= 0)
    fail(
      `witnessing every challenge costs ${witnessed} rows against ${provedRows} derived — the ` +
        'transcript is not in the circuit',
    );
  ok(
    `deriving the transcript costs ${delta.toLocaleString()} rows ` +
      `(${witnessed.toLocaleString()} witnessed vs ${provedRows.toLocaleString()} derived, ` +
      `${((delta / provedRows) * 100).toFixed(0)}% of the program)`,
  );
  // And the twin must ACCEPT the honest proof, or the delta is measuring a break
  // rather than a derivation.
  if (!(await satisfies(fx, minaFixtureConstraints)))
    fail('the honest fixture stopped satisfying — [9] is measuring a broken circuit');
}

// ---------------------------------------------------------------------------
console.log('\n[10] the distance to deployed geometry, measured rather than guessed');
let deployedOneQuery = 0;
{
  const marginal = async (label: string, sh: DreggProofShape) => {
    const t = Date.now();
    const r = await rowsOf(sh);
    console.log(`    ${label.padEnd(54)}: ${r.toLocaleString().padStart(10)} rows  [${secs(t)}]`);
    return r;
  };

  // -- the three marginals, at the geometry that proves. -------------------
  const fxq2 = mint(DB, LB, 2, QPOW, 4242);
  const perQuery =
    (await marginal('degree_bits 1, TWO queries', shapeOf(fxq2, { constraints: minaFixtureConstraints }))) -
    provedRows;
  const fxdb2 = mint(2, LB, NQ, QPOW, 4242);
  const perLayer =
    (await marginal('degree_bits 2 (one more fold layer + Merkle level)', shapeOf(fxdb2, { constraints: minaFixtureConstraints }))) -
    provedRows;

  // Per OPENED TRACE COLUMN. Widening the trace is a shape change, not a proof
  // change, so this is measured with the AIR check OFF — the column cost is the
  // PCS half (one absorbed evaluation per point, one lane in the MMCS leaf, one
  // DEEP term per point) and `N`, the constraint count, stays the named residual
  // it has been since §3.14.
  const widen = (base: DreggProofShape, w: number): DreggProofShape => ({
    ...base,
    constraints: undefined,
    air: { ...base.air, width: w },
    batches: base.batches.map((b, i) =>
      i === 0 ? { ...b, matrices: b.matrices.map((m) => ({ ...m, numCols: w })) } : b,
    ),
  });
  const narrowPcs = await marginal('degree_bits 1, PCS-only, 3 trace columns', widen(SHAPE, 3));
  const widePcs = await marginal('degree_bits 1, PCS-only, 35 trace columns', widen(SHAPE, 35));
  const perColumn = (widePcs - narrowPcs) / 32;
  ok(
    `per additional query ${perQuery.toLocaleString()} rows; per additional fold layer + Merkle ` +
      `level ${perLayer.toLocaleString()} rows; per additional opened trace column ` +
      `${perColumn.toFixed(0)} rows (at 2 opening points)`,
  );

  // Split the column cost into its ONCE-ONLY and PER-QUERY halves: an opened
  // evaluation is absorbed once (2 points x 4 limbs = 8 lanes = exactly one
  // permutation) but pays a DEEP term and an MMCS leaf lane in EVERY query.
  const narrowPcs2 = await marginal('degree_bits 1, PCS-only, 3 columns, TWO queries', {
    ...widen(shapeOf(fxq2, {}), 3),
  });
  const widePcs2 = await marginal('degree_bits 1, PCS-only, 35 columns, TWO queries', {
    ...widen(shapeOf(fxq2, {}), 35),
  });
  const perColumn2 = (widePcs2 - narrowPcs2) / 32;
  const perColPerQuery = perColumn2 - perColumn;
  const perColOnce = perColumn - perColPerQuery;
  if (perColPerQuery <= 0 || perColOnce <= 0)
    fail(
      `the column cost did not split (once-only ${perColOnce.toFixed(0)}, per-query ` +
        `${perColPerQuery.toFixed(0)}) — the projection below would be a guess`,
    );
  ok(
    `an opened column costs ${perColOnce.toFixed(0)} rows once (its absorption) + ` +
      `${perColPerQuery.toFixed(0)} rows PER QUERY (its DEEP term and MMCS lane)`,
  );

  // -- the DEPLOYED FRI geometry. -------------------------------------------
  // `|D^0| = 2^22`, 16 arity-2 layers, log_blowup 6, cap_height 0 — carrying the
  // FIXTURE's AIR widths, so this is the FRI half of the ladder and says nothing
  // about the root's 940+175 columns. Those ride on the column marginals above.
  //
  // ⚑ TWO QUERIES AT THIS GEOMETRY DOES NOT BUILD. `analyzeMethods` on a
  // ~1.7M-row circuit aborts inside kimchi's wasm allocator (32-bit address
  // space), not the node heap, so the per-query/fixed split is taken from a
  // WITNESSED-challenge, AIR-free twin at one query instead: that twin is the
  // per-query walk and nothing else, up to the range checks on the witnessed
  // challenges. Both halves are measured; neither is subtracted from a guess.
  const deployedAt = (q: number, opts: { air: boolean; derive: boolean }): DreggProofShape => ({
    ...SHAPE,
    constraints: opts.air ? minaFixtureConstraints : undefined,
    deriveChallenges: opts.derive,
    knobs: { ...SHAPE.knobs, layers: 16, logGlobalMaxHeight: 22, indexBits: 22, logBlowup: 6, numQueries: q },
    logGlobalMaxHeight: 22,
    commitPathDepths: Array.from({ length: 16 }, (_, i) => 21 - i),
    batches: SHAPE.batches.map((b) => ({
      matrices: b.matrices.map((m) => ({ ...m, logHeight: 22 })),
      pathDepth: 22,
    })),
  });
  deployedOneQuery = await marginal(
    'ONE query at the DEPLOYED FRI geometry (fixture AIR)',
    deployedAt(1, { air: true, derive: true }),
  );
  const depWalkOnly = await marginal(
    '  the same, challenges WITNESSED and no AIR check',
    deployedAt(1, { air: false, derive: false }),
  );
  const depFixed = deployedOneQuery - depWalkOnly;
  if (depFixed <= 0) fail('the deployed transcript + AIR came out non-positive');
  ok(
    `at the deployed FRI geometry: ${depFixed.toLocaleString()} rows of transcript + AIR, ` +
      `${depWalkOnly.toLocaleString()} rows per query walk`,
  );

  // -- the projection to the root. ------------------------------------------
  const KIMCHI = 65536;
  const USABLE_LOW = 48000;
  const USABLE_HIGH = 55000;
  const NQ_DEPLOYED = 19;
  const fri19 = depFixed + NQ_DEPLOYED * depWalkOnly;
  // §1.3: 940 main + 175 preprocessed columns, each opened at TWO points. The
  // fixture opens `SHAPE.air.width` the same way, so the gap is the difference.
  const rootCols = 940 + 175;
  const extraCols = rootCols - SHAPE.air.width;
  const columnGap = extraCols * (perColOnce + NQ_DEPLOYED * perColPerQuery);
  const total = fri19 + columnGap;
  console.log(
    `    the deployed root, projected from the marginals above:\n` +
      `      transcript + AIR arithmetic            ${depFixed.toLocaleString().padStart(12)} rows\n` +
      `      + 19 query walks                       ${(NQ_DEPLOYED * depWalkOnly).toLocaleString().padStart(12)} rows\n` +
      `      + ${extraCols.toLocaleString()} more opened columns              ` +
      `${Math.round(columnGap).toLocaleString().padStart(12)} rows\n` +
      `      = ${Math.round(total).toLocaleString()} rows  ` +
      `(${Math.ceil(total / USABLE_HIGH)}-${Math.ceil(total / USABLE_LOW)} Pickles steps)`,
  );
  if (total < 1e7 || total > 1e8)
    fail(`the projected ladder is ${Math.round(total)} rows, outside any band this repo has recorded`);
  ok(
    `one deployed-geometry query is ${(deployedOneQuery / KIMCHI).toFixed(1)}x a 2^16 step; the ` +
      `whole root projects to ${(total / 1e7).toFixed(2)}e7 rows / ` +
      `${Math.ceil(total / USABLE_HIGH)}-${Math.ceil(total / USABLE_LOW)} steps — ` +
      'and the per-instance constraint count N is STILL uncounted, so the AIR term in this ' +
      'total is the fixture\'s four constraints, not the root\'s.',
  );
}

console.log('\n[11] the ratchet');
{
  const RECORDED_PROVED_ROWS = 56_927; //          §3.16, measured 2026-07-29
  const RECORDED_DEPLOYED_QUERY = 827_887; //      §3.16, measured 2026-07-29
  const RECORDED: [string, number, number][] = [
    ['the assembled verifier at degree_bits 1', provedRows, RECORDED_PROVED_ROWS],
    ['ONE query at the deployed FRI geometry', deployedOneQuery, RECORDED_DEPLOYED_QUERY],
  ];
  for (const [what, got, want] of RECORDED) {
    if (got !== want)
      fail(
        `rows for ${what} moved to ${got.toLocaleString()} from the recorded ${want.toLocaleString()} — ` +
          'update the figure and whatever quotes it, in the same commit',
      );
  }
  ok(
    `ratchet: ${provedRows.toLocaleString()} rows proved / ` +
      `${deployedOneQuery.toLocaleString()} rows for one deployed-geometry query, both as recorded`,
  );
}

console.log('\n=== DREGG-PROOF-VERIFY PASS ===');

// RUNG 4 — the COMMIT PHASE as ONE object: all 16 fold layers, chained.
//
//   npm run fri-chain
//
// Rung 2 proved a single commit-phase round at path depth 2. A chain of rounds
// is NOT sixteen copies of one round, and the difference is where the bugs are:
//
//   * the index is ONE object, shifted once per round, and the same bits do
//     three different jobs at three different offsets (slot selector, path
//     directions, coset descent sign);
//   * the coset point descends sixteen times by `(-1)^b x^2`;
//   * the landing value is compared to the final polynomial at the point the
//     LEFTOVER index bits name;
//   * reduced openings roll in partway down, scaled by `beta^arity`.
//
// ⚑ AND THAT IS NOT HYPOTHETICAL. Built against `p2chain` — p3's OWN sixteen-
// round chain, not sixteen calls to a one-round emitter — this leg immediately
// showed the descent taking `indexBits[r]` where `verify_query` takes
// `indexBits[r+1]`. It is right whenever two consecutive index bits agree, so it
// is right on about half of every chain's rounds and on ALL of a chain whose
// index is zero — which is exactly the witness `getRows()` supplies. The
// previous lane had already made the single-round descent check deterministic
// and both-polarity; that check stayed green, because one round never consumes
// two bits. Composition needed its own referent.

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
  makeDerivedQueryProgram,
  witnessTranscriptShape,
} from '../src/FriChallenger.js';
import {
  BbExt,
  evalFinalPolyBigInt,
  foldRowArity2BigInt,
  makeCommitPhaseProgram,
  verifyCommitPhase,
  verifyCommitPhaseBigInt,
  witnessCommitPhaseShape,
} from '../src/FriQueryStep.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const eqv = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);
const eq2 = (a: bigint[][], b: bigint[][]) => a.length === b.length && a.every((r, i) => eqv(r, b[i]));
const B = (s: string) => BigInt(s);

function probeDir(): string {
  const d =
    process.env.DREGG_PROBE_DIR ??
    resolve(process.cwd(), '../../circuit-prove/sketches/mina-pasta-hash-probe');
  if (!existsSync(resolve(d, 'Cargo.toml')))
    throw new Error(`the dregg-side hash probe is not at ${d} — set DREGG_PROBE_DIR`);
  return d;
}
function runChain(
  dir: string,
  seed: number,
  index: number,
  logD0: number,
  layers: number,
  finalPolyLen: number,
  rollIns: number[],
): any {
  const out = execFileSync(
    'cargo',
    [
      'run',
      '--offline',
      '--quiet',
      '--',
      'p2chain',
      String(seed),
      String(index),
      String(logD0),
      String(layers),
      String(finalPolyLen),
      rollIns.length ? rollIns.join(',') : '-',
    ],
    { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 24 },
  );
  return JSON.parse(out);
}

import * as fri from '../src/FriQueryStep.js';

const dir = probeDir();
const LOG_D0 = 22;
const LAYERS = 16;

console.log('=== Rung 4: the COMMIT PHASE, all 16 layers as one chain ===\n');

// ---------------------------------------------------------------------------
console.log('[1] the 16-layer chain == p3 — every coset point and every fold');
let em: any;
{
  // ⚑ DELIBERATELY NOT A RANDOM INDEX ALONE. The descent bug above is invisible
  // on an index whose consecutive bits agree, so the chain is run on THREE
  // fixed indices with known bit patterns plus one fresh one. `0` and
  // `2^22 - 1` are the two constant-bit extremes (where the buggy and the
  // correct reading COINCIDE — they must still pass), and the alternating
  // pattern is where they differ at EVERY round.
  const alternating = 0b0101010101010101010101; //  no two consecutive bits agree
  const fresh = Number(BigInt('0x' + randomBytes(3).toString('hex')) % (1n << 22n));
  const cases: [string, number][] = [
    ['all-zero index (the two readings coincide)', 0],
    ['all-ones index (the two readings coincide)', (1 << 22) - 1],
    ['alternating bits (they differ at EVERY round)', alternating],
    [`a fresh index (${fresh})`, fresh],
  ];
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  let sawDivergence = false;
  for (const [label, index] of cases) {
    const e = runChain(dir, seed, index, LOG_D0, LAYERS, 1, []);
    if (!em) em = e;
    const indexBits = Array.from({ length: LOG_D0 }, (_, i) => ((index >> i) & 1) === 1);
    const got = verifyCommitPhaseBigInt({
      indexBits,
      initial: e.initial.map(B),
      betas: e.betas.map((b: string[]) => b.map(B)),
      siblings: e.siblings.map((b: string[]) => b.map(B)),
      rollIns: [],
    });
    // `xs[0]` is the coset point round 0 folds at; p3 emits the same list.
    if (!eqv(got.xs.slice(0, LAYERS), e.cosetPoints.map(B)))
      fail(
        `'${label}': the coset chain diverges — got ${got.xs.slice(0, LAYERS)}, ` +
          `p3 says ${e.cosetPoints}`,
      );
    if (!eqv(got.folded, e.folded.map(B)))
      fail(`'${label}': the chain lands on ${got.folded}, p3 says ${e.folded}`);
    // The DISCRIMINATING half: the wrong-bit reading must give a different
    // chain on the alternating index, or this whole leg would be free.
    const wrong = verifyCommitPhaseBigIntWrongBit({
      indexBits,
      initial: e.initial.map(B),
      betas: e.betas.map((b: string[]) => b.map(B)),
      siblings: e.siblings.map((b: string[]) => b.map(B)),
    });
    const differs = !eqv(wrong, e.folded.map(B));
    if (index === alternating && !differs)
      fail('the slot-bit reading agrees on the alternating index — the check is blind');
    if (differs) sawDivergence = true;
    ok(`${label} — all ${LAYERS} coset points and the landing value`);
  }
  if (!sawDivergence)
    fail('the wrong-bit reading never diverged on any case: this leg cannot see the bug it exists for');
  ok('the SLOT-bit reading of the descent diverges on a bit-alternating index (the check discriminates)');
  ok(`emitter: ${em.emitter}`);
}

/**
 * The reading `commitPhaseRound` had before this leg existed: descend on the bit
 * that chose the SLOT rather than the next one. Kept as a LIVE twin, not a
 * comment, so the check above has something to be discriminating against — a
 * "we fixed it" with no standing counter-example is how the single-round check
 * stayed green through the bug.
 */
function verifyCommitPhaseBigIntWrongBit(w: {
  indexBits: boolean[];
  initial: bigint[];
  betas: bigint[][];
  siblings: bigint[][];
}): bigint[] {
  const md = (x: bigint) => ((x % P) + P) % P;
  const real = verifyCommitPhaseBigInt({ ...w, rollIns: [] });
  let folded = w.initial;
  let x = real.xs[0];
  for (let r = 0; r < w.betas.length; r++) {
    const even = w.indexBits[r] ? w.siblings[r] : folded;
    const odd = w.indexBits[r] ? folded : w.siblings[r];
    folded = foldRowArity2BigInt(x, w.betas[r], even, odd);
    const sq = md(x * x);
    x = w.indexBits[r] ? md(P - sq) : sq; //   ⚑ the WRONG bit: r, not r+1
  }
  return folded;
}

// ---------------------------------------------------------------------------
console.log('\n[2] the ROLL-INS and the FINAL-POLY comparison == p3');
{
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const index = Number(BigInt('0x' + randomBytes(3).toString('hex')) % (1n << 22n));
  const rollIns = [2, 5, 11];
  const e = runChain(dir, seed, index, LOG_D0, LAYERS, 1, rollIns);
  const indexBits = Array.from({ length: LOG_D0 }, (_, i) => ((index >> i) & 1) === 1);
  const got = verifyCommitPhaseBigInt({
    indexBits,
    initial: e.initial.map(B),
    betas: e.betas.map((b: string[]) => b.map(B)),
    siblings: e.siblings.map((b: string[]) => b.map(B)),
    rollIns: rollIns.map((r, i) => ({ afterRound: r, value: e.rollInValues[i].map(B) })),
  });
  if (!eqv(got.folded, e.folded.map(B)))
    fail(`a chain with roll-ins at ${rollIns} diverges: ${got.folded} vs ${e.folded}`);
  ok(`roll-ins at rounds ${rollIns} — scaled by beta^arity, at the FOLDED height`);

  // Discriminating: dropping the beta^2 factor must change the answer.
  const noScale = verifyCommitPhaseBigInt({
    indexBits,
    initial: e.initial.map(B),
    betas: e.betas.map((b: string[]) => b.map(B)),
    siblings: e.siblings.map((b: string[]) => b.map(B)),
    rollIns: [],
  });
  if (eqv(noScale.folded, e.folded.map(B)))
    fail('the roll-ins changed nothing — the chain is ignoring them');
  ok('a chain WITHOUT the roll-ins lands somewhere else (they are load-bearing)');

  // The final polynomial's point and evaluation.
  const finalPoly = e.finalPoly.map((c: string[]) => c.map(B));
  const wantEval = evalFinalPolyBigInt(finalPoly, B(e.finalX));
  if (!eqv(wantEval, e.finalPolyEval.map(B)))
    fail(`the Horner evaluation diverges: ${wantEval} vs ${e.finalPolyEval}`);
  ok(`the final polynomial's Horner evaluation at x = ${e.finalX} agrees with p3`);
  if (e.finalDomainIndex !== index >> LAYERS)
    fail(`p3's leftover domain index ${e.finalDomainIndex} != index >> ${LAYERS}`);
  ok(`the leftover domain index after ${LAYERS} folds is index >> ${LAYERS} = ${e.finalDomainIndex}`);
  if (e.logFinalHeight !== LOG_D0 - LAYERS)
    fail(`the chain landed at log height ${e.logFinalHeight}, expected ${LOG_D0 - LAYERS}`);
  ok(`the chain lands at log height ${e.logFinalHeight} — the deployed log_final_height`);
}

// ---------------------------------------------------------------------------
console.log('\n[3] the 16-layer chain, IN CIRCUIT, against p3');
{
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const index = 0b0101010101010101010101; //  the case that separates the readings
  const rollIns = [4, 9];
  const e = runChain(dir, seed, index, LOG_D0, LAYERS, 1, rollIns);
  const indexBits = Array.from({ length: LOG_D0 }, (_, i) => ((index >> i) & 1) === 1);
  const t0 = Date.now();
  await Provable.runAndCheck(() => {
    const bits = indexBits.map((b) => Provable.witness(Bool, () => Bool(b)));
    const initial = Provable.witness(BbExt, () => BbExt.from(e.initial.map(B)));
    const rounds = Array.from({ length: LAYERS }, (_, r) => ({
      sibling: Provable.witness(BbExt, () => BbExt.from(e.siblings[r].map(B))),
      path: [] as BbDigest[],
      beta: Provable.witness(BbExt, () => BbExt.from(e.betas[r].map(B))),
      commit: Provable.witness(BbDigest, () => BbDigest.zero()),
    }));
    // path depth 0 => the leaf digest IS the commitment; supply it honestly.
    for (let r = 0; r < LAYERS; r++) {
      const even = indexBits[r] ? e.siblings[r].map(B) : chainEven(e, r);
      const odd = indexBits[r] ? chainEven(e, r) : e.siblings[r].map(B);
      const leaf = spongeBigInt([...even, ...odd]);
      rounds[r].commit = Provable.witness(BbDigest, () => BbDigest.from(leaf));
    }
    const out = verifyCommitPhase({
      indexBits: bits,
      initial,
      rounds,
      rollIns: rollIns.map((r, i) => ({
        afterRound: r,
        value: Provable.witness(BbExt, () => BbExt.from(e.rollInValues[i].map(B))),
      })),
      logGlobalMaxHeight: LOG_D0,
    });
    Provable.asProver(() => {
      if (!eqv(out.folded.toBigInts(), e.folded.map(B)))
        fail(`the in-CIRCUIT chain lands on ${out.folded.toBigInts()}, p3 says ${e.folded}`);
    });
  });
  ok(
    `the CIRCUIT walks all ${LAYERS} layers to p3's landing value, roll-ins included ` +
      `[${((Date.now() - t0) / 1000).toFixed(1)}s]`,
  );
}

/** The value that enters round `r`'s row from the chain: `initial` at round 0,
 *  otherwise the previous round's fold. */
function chainEven(e: any, r: number): bigint[] {
  return r === 0 ? e.initial.map(B) : e.foldedAfterRound[r - 1].map(B);
}

// ---------------------------------------------------------------------------
console.log('\n[4] the whole chain is a real PROVABLE object');
{
  // The deployed chain's Merkle paths (depths 21..6, 216 levels) are two orders
  // of magnitude past one Kimchi domain — that is §3.10's measurement, not a
  // defect. At path depth 0 each round's leaf digest IS its commitment, the
  // `cap_height = log_folded_height` corner of the same MMCS, and everything a
  // single round could not show survives.
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const index = 0b0101010101010101010101;
  const rollIns = [4, 9];
  const e = runChain(dir, seed, index, LOG_D0, LAYERS, 1, rollIns);
  const indexBits = Array.from({ length: LOG_D0 }, (_, i) => ((index >> i) & 1) === 1);

  const { prog, CommitPhaseClaim } = makeCommitPhaseProgram({
    logD0: LOG_D0,
    layers: LAYERS,
    pathDepths: Array(LAYERS).fill(0),
    rollInRounds: rollIns,
    finalPolyLen: 1,
  });
  const analysis = await prog.analyzeMethods();
  console.log(`    the proved instance: ${analysis.proveChain.rows.toLocaleString()} rows`);
  const t0 = Date.now();
  await prog.compile();
  ok(`compiled in ${((Date.now() - t0) / 1000).toFixed(1)}s`);

  // The honest witness: commitments derived from the rows, and a final
  // polynomial whose evaluation IS the landing value (log_final_poly_len = 0,
  // so the coefficient is the value).
  const commits = Array.from({ length: LAYERS }, (_, r) => {
    const even = indexBits[r] ? e.siblings[r].map(B) : chainEven(e, r);
    const odd = indexBits[r] ? chainEven(e, r) : e.siblings[r].map(B);
    return BbDigest.from(spongeBigInt([...even, ...odd]));
  });
  const claim = new CommitPhaseClaim({
    commits,
    finalPoly: [BbExt.from(e.folded.map(B))],
  });
  const priv = () =>
    [
      indexBits.map((b) => Bool(b)),
      BbExt.from(e.initial.map(B)),
      Array.from({ length: LAYERS }, (_, r) => BbExt.from(e.siblings[r].map(B))),
      Array.from({ length: LAYERS }, (_, r) => BbExt.from(e.betas[r].map(B))),
      rollIns.map((_, i) => BbExt.from(e.rollInValues[i].map(B))),
      Array.from({ length: LAYERS }, () => [BbDigest.zero()]),
    ] as const;

  const t1 = Date.now();
  const { proof } = await prog.proveChain(claim, ...priv());
  if (!(await prog.verify(proof))) fail('the chain proof failed to verify');
  ok(`the whole ${LAYERS}-layer chain PROVES and VERIFIES in ${((Date.now() - t1) / 1000).toFixed(1)}s`);
  if (proof.publicOutput.toBigInt() !== BigInt(index))
    fail(`the proof reports index ${proof.publicOutput.toBigInt()}, not ${index}`);
  ok(`the PROVEN public output names the query index the chain walked (${index})`);

  // REJECT: a final polynomial the chain does not land on.
  let held = false;
  try {
    const bad = new CommitPhaseClaim({
      commits,
      finalPoly: [BbExt.from(e.folded.map((v: string, i: number) => (i === 0 ? (B(v) + 1n) % P : B(v))))],
    });
    await prog.proveChain(bad, ...priv());
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a chain proved against a final polynomial it does not land on');
  ok('NO proof exists for a final polynomial the chain does not land on');

  // REJECT: a commitment the row does not open under, mid-chain.
  held = false;
  try {
    const badCommits = commits.slice();
    badCommits[9] = BbDigest.from(
      commits[9].limbs.map((x, i) => (i === 0 ? (x.toBigInt() + 1n) % P : x.toBigInt())),
    );
    await prog.proveChain(
      new CommitPhaseClaim({ commits: badCommits, finalPoly: [BbExt.from(e.folded.map(B))] }),
      ...priv(),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a chain proved against a layer-9 commitment its row does not open under');
  ok('NO proof exists for a mid-chain commitment the row does not open under');

  // REJECT: a DIFFERENT index against the same commitments. The chain's whole
  // claim is that ONE index threads all 16 layers.
  held = false;
  try {
    const flipped = indexBits.slice();
    flipped[3] = !flipped[3];
    await prog.proveChain(
      claim,
      flipped.map((b) => Bool(b)),
      BbExt.from(e.initial.map(B)),
      Array.from({ length: LAYERS }, (_, r) => BbExt.from(e.siblings[r].map(B))),
      Array.from({ length: LAYERS }, (_, r) => BbExt.from(e.betas[r].map(B))),
      rollIns.map((_, i) => BbExt.from(e.rollInValues[i].map(B))),
      Array.from({ length: LAYERS }, () => [BbDigest.zero()]),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the same commitments admitted a chain at a different index');
  ok('NO proof exists at a different query index against the same commitments');
}

// ---------------------------------------------------------------------------
console.log('\n[4b] THE SEAM — the chain driven by DERIVED challenges, not witnessed ones');
let seamDeployed = 0;
{
  // ⚑ THIS IS THE POINT OF ORDER. Rung 4 above walks a chain at an index the
  // WITNESS supplies; rung 3 derives an index from a transcript. Each alone is
  // satisfiable by a prover that answers at its own index while deriving a
  // different one. They are a FRI verifier only when the SAME index does both
  // jobs — an identity that exists nowhere except inside a program that does
  // both. This is that program.
  //
  // ⚑ AND FINDING AN HONEST WITNESS FOR IT IS ITSELF THE ARGUMENT. The
  // commitments the challenger absorbs are the commitments the rows must open
  // under, so the derived index depends on the very rows it selects. A real
  // prover escapes the circularity by committing to a whole CODEWORD first and
  // opening afterwards; a test that carries one row per layer cannot, and must
  // SEARCH for a fixed point. That the search is needed is the property: the
  // prover does not get to pick the index.
  const SEAM_LOG_D0 = 6;
  const SEAM_LAYERS = 2;
  const SEAM_INDEX_BITS = SEAM_LOG_D0;
  // ⚑ A LABELLED REDUCTION. The seam's PROVED instance grinds 8 PoW bits, not
  // the deployed 16, because the fixed-point search re-grinds per candidate.
  // The deployed 16 is exercised at full width by the challenger leg (twin,
  // circuit and proof, both polarities) and by the refusal below.
  const SEAM_POW_BITS = 8;
  const PRE = 13;
  const knobs: FriKnobs = {
    ...DEPLOYED_KNOBS,
    layers: SEAM_LAYERS,
    numQueries: 1,
    logGlobalMaxHeight: SEAM_LOG_D0,
    indexBits: SEAM_INDEX_BITS,
    queryPowBits: SEAM_POW_BITS,
  };
  const rnd = () => BigInt('0x' + randomBytes(4).toString('hex')) % P;
  const ext = () => [rnd(), rnd(), rnd(), rnd()];

  // Derive a transcript from a candidate's own commitments, grinding the PoW.
  function transcriptFor(preamble: bigint[], commits: bigint[][], finalPoly: bigint[][]) {
    const c = new ChallengerBigInt();
    c.observeSlice(preamble);
    c.sampleExt(); //                       alpha
    const betas: bigint[][] = [];
    for (let r = 0; r < SEAM_LAYERS; r++) {
      c.observeSlice(commits[r]);
      betas.push(c.sampleExt());
    }
    for (const e of finalPoly) c.observeSlice(e);
    for (let r = 0; r < SEAM_LAYERS; r++) c.observe(BigInt(knobs.maxLogArity));
    const w = c.grind(SEAM_POW_BITS);
    if (!c.checkWitness(SEAM_POW_BITS, w)) fail('the ground witness did not pass');
    const v = c.sampleBits(SEAM_INDEX_BITS);
    return { betas, witness: w, index: v };
  }

  // Search for a fixed point: an index whose own chain's commitments derive it.
  let found: any = null;
  let attempts = 0;
  const t0 = Date.now();
  outer: for (let attempt = 0; attempt < 40 && !found; attempt++) {
    const preamble = Array.from({ length: PRE }, rnd);
    const initial = ext();
    const siblings = Array.from({ length: SEAM_LAYERS }, ext);
    for (let cand = 0; cand < 1 << SEAM_INDEX_BITS; cand++) {
      attempts++;
      const bits = Array.from({ length: SEAM_INDEX_BITS }, (_, i) => ((cand >> i) & 1) === 1);
      // Betas depend on the commitments, which depend on the rows, which depend
      // on the betas. Break it the way the protocol does: layer 0's row is free,
      // and each later row is the fold under the beta the PREVIOUS commitment
      // induced. That is a well-founded order, not a fixed point — the fixed
      // point is only over the INDEX.
      const c = new ChallengerBigInt();
      c.observeSlice(preamble);
      c.sampleExt();
      const betas: bigint[][] = [];
      const commits: bigint[][] = [];
      let running = initial;
      let x = verifyCommitPhaseBigInt({
        indexBits: bits,
        initial,
        betas: [],
        siblings: [],
        rollIns: [],
      }).xs[0];
      for (let r = 0; r < SEAM_LAYERS; r++) {
        const even = bits[r] ? siblings[r] : running;
        const odd = bits[r] ? running : siblings[r];
        commits.push(spongeBigInt([...even, ...odd]));
        c.observeSlice(commits[r]);
        const beta = c.sampleExt();
        betas.push(beta);
        running = foldRowArity2BigInt(x, beta, even, odd);
        const sq = (x * x) % P;
        x = bits[r + 1] ? (P - sq) % P : sq;
      }
      const finalPoly = [running];
      const t = transcriptFor(preamble, commits, finalPoly);
      if (!eq2(t.betas, betas)) fail('the transcript replay disagreed with the incremental build');
      if (t.index === cand) {
        found = { preamble, initial, siblings, commits, finalPoly, betas, witness: t.witness, index: cand };
        break outer;
      }
    }
  }
  if (!found) fail('no fixed point found in 40 x 64 candidates — the search is broken');
  ok(
    `an honest witness exists: index ${found.index} is the one its OWN commitments derive ` +
      `(found after ${attempts} candidates, ${((Date.now() - t0) / 1000).toFixed(1)}s)`,
  );

  const { prog, DerivedQueryClaim } = makeDerivedQueryProgram({
    knobs,
    preambleLen: PRE,
    pathDepths: Array(SEAM_LAYERS).fill(0),
  });
  const analysis = await prog.analyzeMethods();
  console.log(`    the seam program: ${analysis.proveDerivedQuery.rows.toLocaleString()} rows`);
  const t1 = Date.now();
  await prog.compile();
  ok(`compiled in ${((Date.now() - t1) / 1000).toFixed(1)}s`);

  const claim = new DerivedQueryClaim({
    commits: found.commits.map((c: bigint[]) => BbDigest.from(c)),
    finalPoly: found.finalPoly.map((c: bigint[]) => BbExt.from(c)),
  });
  const priv = () =>
    [
      found.preamble.map((v: bigint) => Field(v)),
      Field(found.witness),
      BbExt.from(found.initial),
      found.siblings.map((s: bigint[]) => BbExt.from(s)),
      Array.from({ length: SEAM_LAYERS }, () => [BbDigest.zero()]),
    ] as const;
  const t2 = Date.now();
  const { proof } = await prog.proveDerivedQuery(claim, ...priv());
  if (!(await prog.verify(proof))) fail('the seam proof failed to verify');
  ok(`the SEAM PROVES and VERIFIES in ${((Date.now() - t2) / 1000).toFixed(1)}s`);
  if (proof.publicOutput.toBigInt() !== BigInt(found.index))
    fail(`the seam reports index ${proof.publicOutput.toBigInt()}, not ${found.index}`);
  ok(`the PROVEN index ${found.index} is DERIVED from the transcript, not witnessed`);

  // REJECT: the same rows against a transcript whose commitments were shifted.
  // The chain still folds identically — only the derivation moved — so this is
  // precisely the "prover answers at its own index" attack, refused.
  let held = false;
  try {
    const badCommits = found.commits.map((c: bigint[]) => c.slice());
    badCommits[0][0] = (badCommits[0][0] + 1n) % P;
    await prog.proveDerivedQuery(
      new DerivedQueryClaim({
        commits: badCommits.map((c: bigint[]) => BbDigest.from(c)),
        finalPoly: found.finalPoly.map((c: bigint[]) => BbExt.from(c)),
      }),
      ...priv(),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held)
    fail('the seam admitted rows opened under one commitment while deriving from another');
  ok('NO proof exists when the ABSORBED commitment and the OPENED-UNDER one differ');

  // REJECT: a preamble one element off. Nothing about the chain changed, but the
  // whole derivation did — which is what "the index is unchooseable" means.
  held = false;
  try {
    const badPre = found.preamble.slice();
    badPre[4] = (badPre[4] + 1n) % P;
    await prog.proveDerivedQuery(
      claim,
      badPre.map((v: bigint) => Field(v)),
      Field(found.witness),
      BbExt.from(found.initial),
      found.siblings.map((s: bigint[]) => BbExt.from(s)),
      Array.from({ length: SEAM_LAYERS }, () => [BbDigest.zero()]),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the seam accepted a perturbed preamble — the transcript is not binding');
  ok('NO proof exists for a preamble one element off (the derivation is REACTIVE)');

  // REJECT: the PoW is live inside the seam.
  held = false;
  try {
    await prog.proveDerivedQuery(
      claim,
      found.preamble.map((v: bigint) => Field(v)),
      Field((found.witness + 1n) % P),
      BbExt.from(found.initial),
      found.siblings.map((s: bigint[]) => BbExt.from(s)),
      Array.from({ length: SEAM_LAYERS }, () => [BbDigest.zero()]),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the seam proved with a PoW witness that does not grind');
  ok('the query PoW is still enforced inside the seam');

  // And the DEPLOYED-scale seam, measured.
  const depthsHere = Array.from({ length: LAYERS }, (_, i) => LOG_D0 - 1 - i);
  const cs = await Provable.constraintSystem(() => {
    const w = witnessTranscriptShape(DEPLOYED_KNOBS, PRE);
    const ch = deriveFriChallenges(w, DEPLOYED_KNOBS);
    verifyCommitPhase({
      indexBits: ch.queryIndexBits[0],
      initial: Provable.witness(BbExt, () => BbExt.zero()),
      rounds: Array.from({ length: LAYERS }, (_, r) => ({
        sibling: Provable.witness(BbExt, () => BbExt.zero()),
        path: Array.from({ length: depthsHere[r] }, () =>
          Provable.witness(BbDigest, () => BbDigest.zero()),
        ),
        beta: ch.betas[r],
        commit: w.commits[r],
      })),
      rollIns: [],
      finalPoly: w.finalPoly,
      logGlobalMaxHeight: LOG_D0,
    });
  });
  seamDeployed = cs.rows;
  console.log(
    `    the DEPLOYED seam (whole transcript + ONE commit phase at real depths): ` +
      `${seamDeployed.toLocaleString()} rows`,
  );
}

// ---------------------------------------------------------------------------
console.log('\n[5] getRows() — the chain at the DEPLOYED path depths');
const depths = Array.from({ length: LAYERS }, (_, i) => LOG_D0 - 1 - i);
let capped = 0;
let deployed = 0;
let perRollIn = 0;
{
  const measure = async (
    pathDepths: number[],
    rollInRounds: number[],
    finalPolyLen: number,
  ) => {
    const cs = await Provable.constraintSystem(() => {
      verifyCommitPhase(
        witnessCommitPhaseShape(LOG_D0, LAYERS, pathDepths, rollInRounds, finalPolyLen),
      );
    });
    return cs.rows;
  };
  capped = await measure(Array(LAYERS).fill(0), [], 1);
  console.log(
    `    path depth 0 (fully capped), final-poly check : ${capped.toLocaleString()} rows` +
      `   — the PROVABLE shape`,
  );
  const withRoll = await measure(Array(LAYERS).fill(0), [2, 5, 8, 11], 1);
  perRollIn = (withRoll - capped) / 4;
  console.log(`    + 4 roll-ins                                  : ${withRoll.toLocaleString()} rows  (${perRollIn.toFixed(0)}/roll-in)`);
  const t0 = Date.now();
  deployed = await measure(depths, [], 1);
  console.log(
    `    DEPLOYED depths ${depths[0]}..${depths[LAYERS - 1]} (${depths.reduce((a, b) => a + b, 0)} Merkle levels): ` +
      `${deployed.toLocaleString()} rows   [built in ${((Date.now() - t0) / 1000).toFixed(1)}s]`,
  );
  const levels = depths.reduce((a, b) => a + b, 0);
  console.log(
    `    implied rows per Merkle level: ${((deployed - capped) / levels).toFixed(0)} ` +
      `(Rung 1 measured 2,677 standalone)`,
  );
  const USABLE_LOW = 48000;
  const USABLE_HIGH = 55000;
  console.log(
    `    ONE query's commit phase = ${Math.ceil(deployed / USABLE_HIGH)}–${Math.ceil(deployed / USABLE_LOW)} Pickles steps; ` +
      `19 of them = ${Math.ceil((deployed * 19) / USABLE_HIGH)}–${Math.ceil((deployed * 19) / USABLE_LOW)}`,
  );
  console.log(
    '    ⚑ Commit phase only. The input-phase openings, the DEEP quotient and the\n' +
      '      AIR evaluation are separate and none is priced here.',
  );
}

// ---------------------------------------------------------------------------
console.log('\n[6] the EXTENSION-ARITHMETIC primitives, so what is left can be PRICED');
{
  // §2.4 priced the DEEP quotient and the AIR evaluation from a rows-per-Horner
  // GUESS ("~7 rows"). These are the actual units. They do not measure those
  // terms — the term is a count of Horner steps nobody has counted — but they
  // replace the price with a measured one, so §3.14's arithmetic is a
  // multiplication of a measured unit by a stated count rather than a product
  // of two estimates.
  const unit = async (label: string, f: () => void) => {
    const cs = await Provable.constraintSystem(f);
    console.log(`    ${label.padEnd(46)}: ${String(cs.rows).padStart(5)} rows`);
    return cs.rows;
  };
  const w = () => Provable.witness(BbExt, () => BbExt.zero());
  const wf = () => Provable.witness(Field, () => Field(1));
  const extMulRows = await unit('extension multiply (X^4 - 11)', () => {
    fri.extMul(w(), w()).limbs.forEach((x) => x.seal());
  });
  const extAddRows = await unit('extension add', () => {
    fri.extAdd(w(), w()).limbs.forEach((x) => x.seal());
  });
  await unit('extension subtract', () => {
    fri.extSub(w(), w()).limbs.forEach((x) => x.seal());
  });
  const extScaleRows = await unit('extension scale by a base element', () => {
    fri.extScale(w(), wf()).limbs.forEach((x) => x.seal());
  });
  const invRows = await unit('base-field inverse (witness + check)', () => {
    fri.baseInverse(wf()).seal();
  });
  const foldRows = await unit('one arity-2 fold_row', () => {
    fri.foldRowArity2(wf(), w(), w(), w()).limbs.forEach((x) => x.seal());
  });
  // A DEEP-quotient Horner step over the extension: acc <- acc*alpha + v.
  const hornerRows = await unit('one Horner step acc <- acc*alpha + v', () => {
    fri.extAdd(fri.extMul(w(), w()), w()).limbs.forEach((x) => x.seal());
  });
  console.log(
    `    ⚑ §2.4 priced a Horner step at ~7 rows. It is ${hornerRows} — ` +
      `${(hornerRows / 7).toFixed(0)}x, and the DEEP/AIR residual scales with it.`,
  );
  if (extMulRows <= 0 || extAddRows <= 0 || extScaleRows <= 0 || invRows <= 0 || foldRows <= 0)
    fail('an extension primitive measured zero rows — the probe is not building a circuit');
  // Ratcheted like every other figure: §3.14 multiplies this unit by a stated
  // count, so a drift in the unit silently re-prices the whole residual.
  const RECORDED_HORNER_ROWS = 49; //   §3.14, measured 2026-07-28
  const RECORDED_FOLD_ROWS = 150; //    §3.14, measured 2026-07-28
  for (const [what, got, want] of [
    ['the extension Horner step', hornerRows, RECORDED_HORNER_ROWS],
    ['one arity-2 fold_row', foldRows, RECORDED_FOLD_ROWS],
  ] as [string, number, number][])
    if (Math.abs(got - want) / want > 0.02)
      fail(`${what} moved to ${got} from the recorded ${want}: §3.14's pricing is stale`);
}

// ---------------------------------------------------------------------------
const RECORDED_CAPPED_ROWS = 45_186; //   §3.13, measured 2026-07-28
const RECORDED_DEPLOYED_ROWS = 623_310; // §3.13, measured 2026-07-28
for (const [what, got, want] of [
  ['the capped 16-layer chain', capped, RECORDED_CAPPED_ROWS],
  ['the deployed-depth 16-layer chain', deployed, RECORDED_DEPLOYED_ROWS],
] as [string, number, number][]) {
  const drift = Math.abs(got - want) / want;
  if (drift > 0.02)
    fail(
      `rows for ${what} moved to ${got} from the recorded ${want} ` +
        `(${(drift * 100).toFixed(1)}%): docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.13 is stale`,
    );
}
console.log(
  `\n    ratchet: ${capped.toLocaleString()} capped / ${deployed.toLocaleString()} deployed rows ` +
    'are both within 2% of the recorded figures',
);

console.log('\n=== FRI CHAIN PASS ===\n');

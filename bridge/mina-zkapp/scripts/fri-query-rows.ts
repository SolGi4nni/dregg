// RUNG 2 — MEASURE one FRI QUERY at the deployed root's geometry, and KAT its
// arithmetic against p3.
//
//   npm run fri-query
//
// Rung 1 measured a Merkle opening. A FRI query is an opening PLUS the fold
// chain: 16 arity-2 rounds, each reconstructing a two-evaluation row, opening
// it under that round's commitment, and interpolating at `beta`. This script
// builds that object at the deployed knobs (`|D^0| = 2^22`, 16 layers, depths
// 21..6, `cap_height = 0`) and reads `getRows()` off it.
//
// The extension arithmetic is pinned to the DEPLOYED field, not to a
// transcription: `mina-pasta-hash-probe p2fold` computes the fold with the same
// `BinomialExtensionField<BabyBear, 4>` semantics p3 uses (`ext_mul` is checked
// against p3's own multiplication in that crate's tests), and this script must
// reproduce its output — in the bigint twin AND inside `Provable.runAndCheck`.
//
// ⚑ WHAT IS NOT MEASURED HERE, said once and plainly: the DEEP quotient
// (reduced openings, alpha powers), the AIR constraint evaluation, the
// Fiat-Shamir challenger that produces `beta` and the query index, and the
// proof-of-work grind. A query costs at least what this measures, not at most.

import { Bool, Field, Provable } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { P } from '../src/Poseidon2BabyBearW16.js';
import { BbDigest, DEPLOYED_COMMIT_LAYERS, DEPLOYED_INPUT_PHASE_DEPTH } from '../src/Poseidon2Merkle.js';
import {
  BbExt,
  EXT_W,
  cosetPointFromBits,
  deployedQueryShape,
  extMul,
  extMulBigInt,
  foldRowArity2,
  foldRowArity2BigInt,
  makeCommitRoundProgram,
  nextCosetPoint,
  twoAdicGenerator,
  verifyQuery,
  witnessQueryShape,
} from '../src/FriQueryStep.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const eqv = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);

type FoldEmission = {
  emitter: string;
  index: number;
  logHeight: number;
  extW: number;
  x: string;
  beta: string[];
  eEven: string[];
  eOdd: string[];
  mulBetaEven: string[];
  folded: string[];
};

function probeDir(): string {
  const d =
    process.env.DREGG_PROBE_DIR ??
    resolve(process.cwd(), '../../circuit-prove/sketches/mina-pasta-hash-probe');
  if (!existsSync(resolve(d, 'Cargo.toml')))
    throw new Error(`the dregg-side hash probe is not at ${d} — set DREGG_PROBE_DIR`);
  return d;
}

function runP2Fold(dir: string, index: number, logHeight: number, vals: bigint[]): FoldEmission {
  const out = execFileSync(
    'cargo',
    [
      'run',
      '--offline',
      '--quiet',
      '--',
      'p2fold',
      String(index),
      String(logHeight),
      ...vals.map((v) => v.toString()),
    ],
    { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 22 },
  );
  return JSON.parse(out) as FoldEmission;
}

// ===========================================================================
console.log('=== Rung 2: one FRI QUERY at the deployed root geometry ===\n');

const dir = probeDir();

// ---------------------------------------------------------------------------
console.log('[1] the fold arithmetic == p3, on values the emitter cannot have precomputed');
{
  // 12 fresh extension limbs: beta, eEven, eOdd.
  const fresh = Array.from(randomBytes(24 * 4)).reduce<bigint[]>((acc, b, i) => {
    if (i % 4 === 0) acc.push(0n);
    acc[acc.length - 1] = (acc[acc.length - 1] * 256n + BigInt(b)) % P;
    return acc;
  }, []);
  const vals = fresh.slice(0, 12);
  const index = Number(BigInt('0x' + randomBytes(2).toString('hex')) % 2048n);
  const logHeight = 21;
  const em = runP2Fold(dir, index, logHeight, vals);
  ok(`p3 emitter: ${em.emitter}`);
  if (BigInt(em.extW) !== EXT_W) fail(`the deployed extension is X^4 - ${em.extW}, not ${EXT_W}`);
  ok(`the extension modulus X^4 - ${em.extW} matches`);

  const beta = em.beta.map(BigInt);
  const eEven = em.eEven.map(BigInt);
  const eOdd = em.eOdd.map(BigInt);
  const x = BigInt(em.x);
  const folded = em.folded.map(BigInt);

  if (!eqv(extMulBigInt(beta, eEven), em.mulBetaEven.map(BigInt)))
    fail('the o1js extension multiplication twin diverges from p3');
  ok('extension multiplication agrees with p3');

  if (!eqv(foldRowArity2BigInt(x, beta, eEven, eOdd), folded))
    fail('the o1js fold twin diverges from p3 fold_row');
  ok('fold_row (arity 2, two-point Lagrange) agrees with p3');

  // The coset point the circuit DERIVES from the index bits must be the one p3
  // computed from the index — this is what binds the domain to the query.
  const bits = Array.from({ length: logHeight }, (_, i) => ((index >> i) & 1) === 1);
  await Provable.runAndCheck(() => {
    const bb = bits.map((b) => Provable.witness(Bool, () => Bool(b)));
    const got = cosetPointFromBits(bb, logHeight);
    Provable.asProver(() => {
      if (got.toBigInt() % P !== x)
        fail(`the derived coset point ${got.toBigInt() % P} != p3's ${x}`);
    });
  });
  ok(`the coset point is DERIVED from the ${logHeight} index bits and equals p3's`);
  if (twoAdicGenerator(logHeight + 1) === 0n) fail('the two-adic generator is degenerate');

  // The whole fold, in circuit.
  await Provable.runAndCheck(() => {
    const b = Provable.witness(BbExt, () => BbExt.from(beta));
    const e0 = Provable.witness(BbExt, () => BbExt.from(eEven));
    const e1 = Provable.witness(BbExt, () => BbExt.from(eOdd));
    const xf = Provable.witness(Field, () => Field(x));
    const got = foldRowArity2(xf, b, e0, e1);
    Provable.asProver(() => {
      if (!eqv(got.toBigInts(), folded)) fail(`in-circuit fold ${got.toBigInts()} != p3 ${folded}`);
    });
    const m = extMul(b, e0);
    Provable.asProver(() => {
      if (!eqv(m.toBigInts(), em.mulBetaEven.map(BigInt))) fail('in-circuit ext-mul != p3');
    });
  });
  ok('the CIRCUIT reproduces p3 fold_row and p3 extension multiplication');

  // The `(-1)^b x^2` descent, against p3's own next coset point.
  const nextIdx = index >> 1;
  const emNext = runP2Fold(dir, nextIdx, logHeight - 1, vals);
  await Provable.runAndCheck(() => {
    const xf = Provable.witness(Field, () => Field(x));
    const bit = Provable.witness(Bool, () => Bool((index & 1) === 1));
    const got = nextCosetPoint(xf, bit);
    Provable.asProver(() => {
      if (got.toBigInt() % P !== BigInt(emNext.x))
        fail(`the coset descent gave ${got.toBigInt() % P}, p3 says ${emNext.x}`);
      // and the naive squaring is wrong exactly when the bit is set
      const naive = (x * x) % P;
      if ((naive === BigInt(emNext.x)) !== ((index & 1) === 0))
        fail('the sign correction in the coset descent is not load-bearing');
    });
  });
  ok('the coset descent (-1)^b x^2 matches p3 at the next layer, sign included');

  // REJECT polarity.
  const badFold = foldRowArity2BigInt((x + 1n) % P, beta, eEven, eOdd);
  if (eqv(badFold, folded)) fail('the fold ignored the coset point');
  ok('a wrong coset point does NOT reproduce the fold (the check is discriminating)');
}

// ---------------------------------------------------------------------------
console.log('\n[2] one commit-phase round is a real provable object');
{
  const D = 2;
  const prog = makeCommitRoundProgram(D);
  const analysis = await prog.analyzeMethods();
  console.log(`    commit round at path depth ${D}: ${analysis.proveRound.rows.toLocaleString()} rows`);
  const t0 = Date.now();
  await prog.compile();
  ok(`compiled in ${((Date.now() - t0) / 1000).toFixed(1)}s`);

  // Build an honest witness: pick the row, hash it, walk it to a root we then
  // use as the public commitment. The commitment is DERIVED from the row, so
  // the opening is real rather than asserted.
  const { spongeBigInt, foldPathBigInt } = await import('../src/Poseidon2Merkle.js');
  const rnd = () => BigInt('0x' + randomBytes(4).toString('hex')) % P;
  const folded = [rnd(), rnd(), rnd(), rnd()];
  const sibling = [rnd(), rnd(), rnd(), rnd()];
  const beta = [rnd(), rnd(), rnd(), rnd()];
  const slotBit = false; //   folded sits in the even slot
  const pathBits = [true, false];
  const path = [
    [rnd(), rnd(), rnd(), rnd(), rnd(), rnd(), rnd(), rnd()],
    [rnd(), rnd(), rnd(), rnd(), rnd(), rnd(), rnd(), rnd()],
  ];
  const leaf = spongeBigInt([...folded, ...sibling]);
  const nodes = foldPathBigInt(leaf, path, pathBits);
  const commit = nodes[nodes.length - 1];
  const x = BigInt(runP2Fold(dir, 5, 20, [...beta, ...folded, ...sibling]).x);

  const { proof } = await prog.proveRound(
    BbDigest.from(commit),
    BbExt.from(folded),
    Field(x),
    Bool(slotBit),
    pathBits.map((b) => Bool(b)),
    BbExt.from(sibling),
    path.map((d) => BbDigest.from(d)),
    BbExt.from(beta),
  );
  if (!(await prog.verify(proof))) fail('the commit-round proof failed to verify');
  ok('a commit-phase round PROVES and VERIFIES');
  const want = foldRowArity2BigInt(x, beta, folded, sibling);
  if (!eqv(proof.publicOutput.toBigInts(), want))
    fail(`the PROVEN fold ${proof.publicOutput.toBigInts()} != the p3-shaped fold ${want}`);
  ok('the PROVEN public output == the fold p3 computes');

  let held = false;
  try {
    const badCommit = commit.slice();
    badCommit[0] = (badCommit[0] + 1n) % P;
    await prog.proveRound(
      BbDigest.from(badCommit),
      BbExt.from(folded),
      Field(x),
      Bool(slotBit),
      pathBits.map((b) => Bool(b)),
      BbExt.from(sibling),
      path.map((d) => BbDigest.from(d)),
      BbExt.from(beta),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a round proved against a commitment the row does not open under');
  ok('NO proof exists for a commitment the row does not open under');
}

// ---------------------------------------------------------------------------
console.log('\n[3] getRows() — one whole query at the DEPLOYED geometry');
const INPUT_ROW_WIDTH = 8; // one sponge block; the real width is a §1.3 residual
const shape = deployedQueryShape(INPUT_ROW_WIDTH);

async function queryRows(logD0: number, layers: number, w: number): Promise<number> {
  const cs = await Provable.constraintSystem(() => {
    const wit = witnessQueryShape(logD0, layers, w);
    verifyQuery(wit).limbs.forEach((x) => x.seal());
  });
  return cs.rows;
}

// A small shape first, so the composition is attributable rather than one
// opaque number, then the deployed one.
const small = await queryRows(6, 2, INPUT_ROW_WIDTH);
console.log(`    |D^0| = 2^6, 2 layers  : ${small.toLocaleString()} rows`);
const t0 = Date.now();
const full = await queryRows(shape.logD0, shape.layers, INPUT_ROW_WIDTH);
console.log(
  `    |D^0| = 2^${shape.logD0}, ${shape.layers} layers (DEPLOYED): ` +
    `${full.toLocaleString()} rows   [built in ${((Date.now() - t0) / 1000).toFixed(1)}s]`,
);

const merkleLevels =
  shape.logD0 + shape.commitDepths.reduce((a, b) => a + b, 0);
console.log(
  `    Merkle levels in that query: ${shape.logD0} (input) + ` +
    `${shape.commitDepths.reduce((a, b) => a + b, 0)} (${shape.layers} commit layers, ` +
    `depths ${shape.commitDepths[0]}..${shape.commitDepths[shape.commitDepths.length - 1]}) = ${merkleLevels}`,
);
console.log(`    rows per Merkle level, implied: ${(full / merkleLevels).toFixed(0)}`);

const KIMCHI_ROWS = 65536;
const USABLE_LOW = 48000;
const USABLE_HIGH = 55000;
const NUM_QUERIES = 19;
console.log('');
console.log(
  `    ONE query   : ${full.toExponential(3)} rows = ` +
    `${Math.ceil(full / USABLE_HIGH)}–${Math.ceil(full / USABLE_LOW)} Pickles steps ` +
    `(${(full / KIMCHI_ROWS).toFixed(1)}x the 2^16 domain)`,
);
const allQ = full * NUM_QUERIES;
console.log(
  `    ${NUM_QUERIES} queries : ${allQ.toExponential(3)} rows = ` +
    `${Math.ceil(allQ / USABLE_HIGH)}–${Math.ceil(allQ / USABLE_LOW)} Pickles steps`,
);
console.log(
  '    ⚑ FRI query walk only. No DEEP quotient, no AIR evaluation, no challenger,\n' +
    '      no PoW. The full verify is strictly larger.',
);

// ---------------------------------------------------------------------------
// Ratchet.
// ---------------------------------------------------------------------------
const RECORDED_QUERY_ROWS = 684_726; //  docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.10, measured 2026-07-28
const drift = Math.abs(full - RECORDED_QUERY_ROWS) / RECORDED_QUERY_ROWS;
if (drift > 0.02)
  fail(
    `rows for one deployed-geometry FRI query moved to ${full} from the recorded ` +
      `${RECORDED_QUERY_ROWS} (${(drift * 100).toFixed(1)}%): ` +
      'docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.10 is stale',
  );
console.log(`\n    ratchet: ${full.toLocaleString()} rows/query is within 2% of the recorded figure`);

console.log('\n=== FRI QUERY PASS ===\n');

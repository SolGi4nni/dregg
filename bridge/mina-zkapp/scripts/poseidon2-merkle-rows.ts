// RUNG 1 — MEASURE the Poseidon2-w16-BabyBear MERKLE PATH in o1js, and KAT it
// against the DEPLOYED Rust MMCS.
//
//   npm run poseidon2-merkle
//
// `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` establishes that the dominant cost of
// a Mina-side FRI-STARK verifier is Merkle openings, and measures the ONE
// permutation they are built from (2,600.5 rows). It does not measure an
// OPENING. The difference is not bookkeeping: a chain pays, per node, eight
// witnessed-lane range checks and eight lane reductions that a single
// permutation never pays, and if it did NOT pay the range checks the bound
// tracking the 2,600.5 rests on would be a claim about unconstrained witnesses.
//
// This script measures the opening, and refuses to report a number for the
// wrong object: every value is cross-checked against
// `circuit-prove/sketches/mina-pasta-hash-probe p2merkle`, which calls
// `p3_baby_bear::default_babybear_poseidon2_16` +
// `p3_symmetric::TruncatedPermutation<.,2,8,16>` +
// `p3_symmetric::PaddingFreeSponge<.,16,8,8>` at the workspace's pinned p3 rev —
// on leaves carrying a timestamp and a 128-bit nonce, so nothing here can be
// replaying a constant it produced itself.

import { Bool, Field, Provable } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { P } from '../src/Poseidon2BabyBearW16.js';
import {
  BbDigest,
  DEPLOYED_COMMIT_LAYERS,
  DEPLOYED_INPUT_PHASE_DEPTH,
  compressBigInt,
  foldOpening,
  makePoseidon2LeafOpeningProgram,
  makePoseidon2MerkleProgram,
  sparsePathBigInt,
  spongeBB,
  spongeBigInt,
  zeroAtBigInt,
} from '../src/Poseidon2Merkle.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const eqv = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);
const eqm = (a: bigint[][], b: bigint[][]) => a.length === b.length && a.every((r, i) => eqv(r, b[i]));

// ---------------------------------------------------------------------------
// The dregg-side emitter.
// ---------------------------------------------------------------------------

type P2Emission = {
  emitter: string;
  depth: number;
  leafIndex: number;
  rowWidth: number;
  nRows: number;
  rows: string[][];
  leafDigests: string[][];
  leaf: string[];
  siblings: string[][];
  isRight: boolean[];
  nodes: string[][];
  zeroAt: string[][];
  root: string[];
};

function probeDir(): string {
  const d =
    process.env.DREGG_PROBE_DIR ??
    resolve(process.cwd(), '../../circuit-prove/sketches/mina-pasta-hash-probe');
  if (!existsSync(resolve(d, 'Cargo.toml')))
    throw new Error(`the dregg-side hash probe is not at ${d} — set DREGG_PROBE_DIR`);
  return d;
}

const big = (m: string[][]) => m.map((r) => r.map(BigInt));

/** Rows the Rust side cannot have precomputed: a domain tag, this tree's HEAD
 *  (as BabyBear-sized chunks), a millisecond timestamp and a 128-bit nonce. */
function freshRows(dir: string, nRows: number, rowWidth: number): bigint[] {
  const gitCommit = execFileSync('git', ['rev-parse', 'HEAD'], {
    cwd: process.env.DREGG_ATTEST_GIT_DIR ?? dir,
    encoding: 'utf8',
  }).trim();
  const seed: bigint[] = [];
  const tag = Buffer.from('dregg/mina-p2merkle/v1', 'ascii');
  for (const b of tag) seed.push(BigInt(b));
  for (let i = 0; i + 8 <= gitCommit.length; i += 8) seed.push(BigInt('0x' + gitCommit.slice(i, i + 8)) % P);
  seed.push(BigInt(Date.now()) % P);
  for (const b of randomBytes(16)) seed.push(BigInt(b) * 7919n + 13n);
  const out: bigint[] = [];
  for (let i = 0; i < nRows * rowWidth; i++) out.push(seed[i % seed.length] % P);
  return out;
}

function runP2Merkle(
  dir: string,
  depth: number,
  leafIndex: number,
  rowWidth: number,
  vals: bigint[],
): P2Emission {
  const out = execFileSync(
    'cargo',
    [
      'run',
      '--offline',
      '--quiet',
      '--',
      'p2merkle',
      String(depth),
      String(leafIndex),
      String(rowWidth),
      ...vals.map((v) => v.toString()),
    ],
    { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 26 },
  );
  return JSON.parse(out) as P2Emission;
}

// ===========================================================================
console.log('=== Rung 1: the Poseidon2-w16-BabyBear MERKLE PATH in o1js ===\n');

const DEPTH = DEPLOYED_INPUT_PHASE_DEPTH; //          22, the deployed |D^0| = 2^22
const ROW_WIDTH = 13; //                              partial trailing block: 2 sponge perms
const N_ROWS = 6;
const LEAF_INDEX = 3;

// ---------------------------------------------------------------------------
console.log('[1] the DEPLOYED Rust MMCS emits; the o1js twins must reproduce it');
const dir = probeDir();
const vals = freshRows(dir, N_ROWS, ROW_WIDTH);
const t0 = Date.now();
const em = runP2Merkle(dir, DEPTH, LEAF_INDEX, ROW_WIDTH, vals);
ok(`p3 emitter ran in ${((Date.now() - t0) / 1000).toFixed(1)}s: ${em.emitter}`);
if (em.depth !== DEPTH || em.nRows !== N_ROWS || em.rowWidth !== ROW_WIDTH)
  fail('the emitter did not run the shape it was asked for');

const emRows = big(em.rows);
const emLeafDigests = big(em.leafDigests);
const emSiblings = big(em.siblings);
const emNodes = big(em.nodes);
const emZeroAt = big(em.zeroAt);
const emRoot = em.root.map(BigInt);

// The leaf sponge.
{
  const got = emRows.map((r) => spongeBigInt(r));
  if (!eqm(got, emLeafDigests)) fail('the o1js PaddingFreeSponge twin diverges from p3');
  ok(`leaf sponge: ${N_ROWS} rows of width ${ROW_WIDTH} agree elementwise (${Math.ceil(ROW_WIDTH / 8)} perms/row)`);
  // The partial-block rule is load-bearing and easy to get wrong the other way.
  const w8 = emRows[0].slice(0, 8);
  const w9 = emRows[0].slice(0, 9);
  if (eqv(spongeBigInt(w8), spongeBigInt(w9))) fail('the sponge collided on widths 8 and 9');
  ok('the sponge separates width 8 from width 9 (no phantom pad block)');
}

// The zero-subtree ladder, the sparse path, and the root.
{
  const z = zeroAtBigInt(DEPTH);
  if (!eqm(z, emZeroAt)) fail('the zero-subtree ladder diverges from p3');
  ok(`zero-subtree ladder: ${DEPTH + 1} levels agree elementwise`);

  const sp = sparsePathBigInt(emLeafDigests, LEAF_INDEX, DEPTH);
  if (!eqm(sp.siblings, emSiblings)) fail('the sparse-path siblings diverge from p3');
  if (sp.isRight.length !== em.isRight.length || sp.isRight.some((b, i) => b !== em.isRight[i]))
    fail('the isRight bits diverge from p3');
  if (!eqm(sp.nodes, emNodes)) fail('the intermediate path nodes diverge from p3');
  if (!eqv(sp.root, emRoot)) fail('the root diverges from p3');
  ok(`sparse path: all ${DEPTH} siblings, all ${DEPTH} isRight bits, all ${DEPTH} nodes and the root agree`);

  // REJECT polarity: an agreement check that cannot disagree proves nothing.
  const bad = emSiblings.map((s) => s.slice());
  bad[0][0] = (bad[0][0] + 1n) % P;
  const tampered = sparsePathBigInt(emLeafDigests, LEAF_INDEX, DEPTH);
  let cur = emLeafDigests[LEAF_INDEX];
  for (let h = 0; h < DEPTH; h++)
    cur = em.isRight[h] ? compressBigInt(bad[h], cur) : compressBigInt(cur, bad[h]);
  if (eqv(cur, emRoot)) fail('a tampered sibling still reached the root');
  ok('a tampered sibling does NOT reach the root');
  if (!eqv(tampered.root, emRoot)) fail('the twin is not deterministic');
}

// ---------------------------------------------------------------------------
console.log('\n[2] the CIRCUIT computes the same opening, with real witnesses');
{
  await Provable.runAndCheck(() => {
    const leaf = Provable.witness(BbDigest, () => BbDigest.from(emLeafDigests[LEAF_INDEX]));
    const sibs = emSiblings.map((s) => Provable.witness(BbDigest, () => BbDigest.from(s)));
    const bits = em.isRight.map((b) => Provable.witness(Bool, () => Bool(b)));
    const root = foldOpening(leaf, sibs, bits);
    Provable.asProver(() => {
      const got = root.limbs.map((f) => f.toBigInt());
      if (!eqv(got, emRoot)) fail(`in-circuit root ${got} != p3 root ${emRoot}`);
      // The circuit's output is CANONICAL (< p), not merely congruent.
      if (got.some((x) => x >= P)) fail('the in-circuit root is not canonical');
    });
  });
  ok(`depth-${DEPTH} opening: the CIRCUIT's root == the p3 root, canonical`);

  // The leaf sponge, in circuit.
  await Provable.runAndCheck(() => {
    const row = emRows[0].map((v) => Provable.witness(Field, () => Field(v)));
    const d = spongeBB(row);
    Provable.asProver(() => {
      const got = d.limbs.map((f) => f.toBigInt() % P);
      if (!eqv(got, emLeafDigests[0])) fail(`in-circuit sponge ${got} != p3 ${emLeafDigests[0]}`);
    });
  });
  ok(`leaf sponge in circuit: width-${ROW_WIDTH} row == the p3 leaf digest`);

  // The constraints must BITE.
  for (const [what, mutate] of [
    ['a tampered sibling', (s: bigint[][]) => { s[0] = s[0].slice(); s[0][0] = (s[0][0] + 1n) % P; }],
    ['a tampered isRight bit', () => {}],
  ] as [string, (s: bigint[][]) => void][]) {
    const sibs = emSiblings.map((s) => s.slice());
    mutate(sibs);
    const bits = em.isRight.slice();
    if (what.includes('isRight')) bits[0] = !bits[0];
    let held = false;
    try {
      await Provable.runAndCheck(() => {
        const leaf = Provable.witness(BbDigest, () => BbDigest.from(emLeafDigests[LEAF_INDEX]));
        const ss = sibs.map((s) => Provable.witness(BbDigest, () => BbDigest.from(s)));
        const bb = bits.map((b) => Provable.witness(Bool, () => Bool(b)));
        const root = foldOpening(leaf, ss, bb);
        for (let j = 0; j < 8; j++) root.limbs[j].assertEquals(Field(emRoot[j]));
      });
      held = true;
    } catch {
      /* expected */
    }
    if (held) fail(`the circuit accepted ${what}`);
    ok(`the circuit REFUSES ${what}`);
  }

  // ⚑ The range checks are load-bearing, and this is what says so: an
  // out-of-range sibling lane must be REFUSED, not silently folded. Without
  // this the bound tracking in Poseidon2BabyBearW16.ts is about nothing.
  //
  // ⚑ AND THE FAULT VALUE USED TO BE `s[0] + p`, WHICH IS NOT ALWAYS OUT OF
  // RANGE. `assertLt2p31` bounds a lane by `2^31`, not by `p`, and
  // `s[0] + p >= 2^31` only when `s[0] >= 2^31 - p = 134,217,727` — about
  // 93.3% of canonical lanes. On the other **6.7%** `s[0] + p` is a perfectly
  // legitimate non-canonical representative under `2^31`, the circuit is RIGHT
  // to accept it, and this check failed a green tree. Since the emitted leaves
  // carry a fresh 128-bit nonce every run, that was a one-in-fifteen spurious
  // red — measured, on a run that hit it. The offset is now `2^31`, which is
  // out of range unconditionally, and the premise is ASSERTED rather than
  // assumed: a negative check whose fault value might not be a fault is a check
  // that reports on the weather.
  const badLane = emSiblings[0][0] + (1n << 31n);
  if (badLane < 1n << 31n)
    fail(`the fault lane ${badLane} is under 2^31 — this check would be testing nothing`);
  let held = false;
  try {
    await Provable.runAndCheck(() => {
      const leaf = Provable.witness(BbDigest, () => BbDigest.from(emLeafDigests[LEAF_INDEX]));
      const ss = emSiblings.map((s, i) =>
        Provable.witness(BbDigest, () =>
          BbDigest.from(i === 0 ? [badLane, ...s.slice(1)] : s),
        ),
      );
      const bb = em.isRight.map((b) => Provable.witness(Bool, () => Bool(b)));
      foldOpening(leaf, ss, bb);
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the circuit accepted a sibling lane >= 2^31 (the bound tracking is vacuous)');
  ok('the circuit REFUSES an out-of-range sibling lane (the bound tracking is enforced)');
}

// ---------------------------------------------------------------------------
console.log('\n[3] getRows() — the measurement');

async function openingRows(depth: number): Promise<number> {
  const cs = await Provable.constraintSystem(() => {
    const leaf = Provable.witness(BbDigest, () => BbDigest.zero());
    const sibs = Array.from({ length: depth }, () =>
      Provable.witness(BbDigest, () => BbDigest.zero()),
    );
    const bits = Array.from({ length: depth }, () => Provable.witness(Bool, () => Bool(false)));
    foldOpening(leaf, sibs, bits).limbs.forEach((x) => x.seal());
  });
  return cs.rows;
}

const rowsAt: Record<number, number> = {};
for (const d of [1, 2, 4, 8, 16, DEPTH]) rowsAt[d] = await openingRows(d);
const marginalLevel = (rowsAt[16] - rowsAt[8]) / 8;
for (const d of [1, 2, 4, 8, 16, DEPTH])
  console.log(`    depth ${String(d).padStart(2)} opening: ${rowsAt[d].toLocaleString().padStart(9)} rows`);
console.log(`    MARGINAL rows per Merkle level: ${marginalLevel.toLocaleString()}`);

// The sponge, separately: a FRI input-phase leaf is a ROW, not a digest.
async function spongeRows(w: number): Promise<number> {
  const cs = await Provable.constraintSystem(() => {
    const row = Array.from({ length: w }, () => Provable.witness(Field, () => Field(1)));
    spongeBB(row).limbs.forEach((x) => x.seal());
  });
  return cs.rows;
}
const sponge8 = await spongeRows(8);
const sponge16 = await spongeRows(16);
console.log(`    leaf sponge, width  8 (1 perm): ${sponge8.toLocaleString()} rows`);
console.log(`    leaf sponge, width 16 (2 perms): ${sponge16.toLocaleString()} rows`);
console.log(`    MARGINAL rows per sponge block: ${(sponge16 - sponge8).toLocaleString()}`);

const KIMCHI_ROWS = 65536; //   2^16, the Pickles step domain
const USABLE_LOW = 48000; //    MINA-VERIFIES-DREGG-FRI-SIZE §4.1
const USABLE_HIGH = 55000;
console.log('');
console.log(
  `    a depth-${DEPTH} opening is ${rowsAt[DEPTH].toLocaleString()} rows = ` +
    `${(rowsAt[DEPTH] / KIMCHI_ROWS).toFixed(2)}x the 2^16 step DOMAIN, ` +
    `${(rowsAt[DEPTH] / USABLE_HIGH).toFixed(2)}–${(rowsAt[DEPTH] / USABLE_LOW).toFixed(2)}x the USABLE rows`,
);
console.log(
  `    => ONE input-phase opening does NOT fit in one Pickles step ` +
    `(it needs ${Math.ceil(rowsAt[DEPTH] / USABLE_LOW)} at the pessimistic end)`,
);

// ---------------------------------------------------------------------------
console.log('\n[4] the circuit is really Pickles-provable, and proves the p3 object');
// Proved at a SMALL depth so the gate stays fast; the rows above are the
// deployed depth. Saying which is which beats quoting a compile of the wrong
// shape as if it were the measured one.
const PROVE_DEPTH = 3;
{
  const emS = runP2Merkle(dir, PROVE_DEPTH, LEAF_INDEX, ROW_WIDTH, vals);
  const prog = makePoseidon2MerkleProgram(PROVE_DEPTH);
  const t1 = Date.now();
  const { verificationKey } = await prog.compile();
  ok(`compiled the depth-${PROVE_DEPTH} opening program in ${((Date.now() - t1) / 1000).toFixed(1)}s`);
  const t2 = Date.now();
  const { proof } = await prog.proveOpening(
    BbDigest.from(emS.root.map(BigInt)),
    BbDigest.from(emS.leaf.map(BigInt)),
    big(emS.siblings).map((s) => BbDigest.from(s)),
    emS.isRight.map((b) => Bool(b)),
  );
  ok(`proved it in ${((Date.now() - t2) / 1000).toFixed(1)}s (vk hash ${verificationKey.hash.toString().slice(0, 12)}…)`);
  if (!(await prog.verify(proof))) fail('the Merkle opening proof failed to verify');
  ok('the proof VERIFIES');
  const outLeaf = proof.publicOutput.limbs.map((f) => f.toBigInt());
  if (!eqv(outLeaf, emS.leaf.map(BigInt)))
    fail(`the PROVEN leaf ${outLeaf} is not the p3-emitted leaf ${emS.leaf}`);
  ok('the PROVEN public output == the leaf digest the DEPLOYED p3 MMCS emitted');

  // A proof cannot be produced for a root the path does not reach.
  let held = false;
  try {
    const wrong = emS.root.map(BigInt);
    wrong[0] = (wrong[0] + 1n) % P;
    await prog.proveOpening(
      BbDigest.from(wrong),
      BbDigest.from(emS.leaf.map(BigInt)),
      big(emS.siblings).map((s) => BbDigest.from(s)),
      emS.isRight.map((b) => Bool(b)),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a proof was produced for a root the path does not reach');
  ok('NO proof exists for a root the path does not reach');
}

// The row-opening shape (sponge + fold), compiled once so the FRI input-phase
// shape is a thing that exists rather than a composition on paper.
{
  const rowProgDepth = 2;
  const prog = makePoseidon2LeafOpeningProgram(rowProgDepth, ROW_WIDTH);
  const analysis = await prog.analyzeMethods();
  console.log(
    `    row-opening ZkProgram (sponge width ${ROW_WIDTH} + depth ${rowProgDepth}): ` +
      `${analysis.proveRowOpening.rows.toLocaleString()} rows`,
  );
  const emS = runP2Merkle(dir, rowProgDepth, LEAF_INDEX, ROW_WIDTH, vals);
  await prog.compile();
  const { proof } = await prog.proveRowOpening(
    BbDigest.from(emS.root.map(BigInt)),
    emRows[LEAF_INDEX].map((v) => Field(v)),
    big(emS.siblings).map((s) => BbDigest.from(s)),
    emS.isRight.map((b) => Bool(b)),
  );
  if (!(await prog.verify(proof))) fail('the row-opening proof failed to verify');
  const got = proof.publicOutput.limbs.map((f) => f.toBigInt());
  if (!eqv(got, emS.leaf.map(BigInt))) fail('the row-opening proof hashed the row to the wrong digest');
  ok('a ROW opening (p3 sponge in circuit + fold) proves and verifies against the p3 root');
}

// ---------------------------------------------------------------------------
// [5] Ratchet. A measurement nobody re-runs is a number.
// ---------------------------------------------------------------------------
const RECORDED_ROWS_PER_LEVEL = 2677; //   docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.9, measured 2026-07-28
const RECORDED_DEPTH22_ROWS = 58971; //    §3.9
const RECORDED_SPONGE_BLOCK_ROWS = 2632; // §3.9
for (const [what, got, want] of [
  ['rows per Merkle level', marginalLevel, RECORDED_ROWS_PER_LEVEL],
  [`rows for a depth-${DEPTH} opening`, rowsAt[DEPTH], RECORDED_DEPTH22_ROWS],
  ['rows per sponge block', sponge16 - sponge8, RECORDED_SPONGE_BLOCK_ROWS],
] as [string, number, number][]) {
  const drift = Math.abs(got - want) / want;
  if (drift > 0.02)
    fail(
      `${what} moved to ${got} from the recorded ${want} (${(drift * 100).toFixed(1)}%): ` +
        'docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.9 is now stale — update it, or the ' +
        'document is quoting a number nothing produces',
    );
}
console.log(
  `\n    ratchet: ${marginalLevel} rows/level and ${rowsAt[DEPTH].toLocaleString()} rows/opening ` +
    'are within 2% of the recorded figures',
);

// ---------------------------------------------------------------------------
// [6] What this prices, at the deployed FRI geometry.
// ---------------------------------------------------------------------------
console.log('\n[5] the deployed root, priced from the MEASURED opening');
// One query = the input-phase opening at depth 22, plus one commit-phase
// opening per layer at depths 21..6 (16 layers, arity 2, cap_height 0).
const commitDepths = Array.from({ length: DEPLOYED_COMMIT_LAYERS }, (_, i) => DEPTH - 1 - i);
const levelsPerQuery = DEPTH + commitDepths.reduce((a, b) => a + b, 0);
console.log(
  `    per query: 1 input-phase opening (depth ${DEPTH}) + ${DEPLOYED_COMMIT_LAYERS} ` +
    `commit-phase openings (depths ${commitDepths[0]}..${commitDepths[commitDepths.length - 1]})` +
    ` = ${levelsPerQuery} Merkle levels`,
);
const NUM_QUERIES = 19; //  plonky3_recursion_impl.rs:121
const merkleRowsPerQuery = levelsPerQuery * marginalLevel;
const merkleRowsAllQueries = merkleRowsPerQuery * NUM_QUERIES;
console.log(
  `    Merkle rows/query   : ${merkleRowsPerQuery.toExponential(3)} ` +
    `(${Math.ceil(merkleRowsPerQuery / USABLE_HIGH)}–${Math.ceil(merkleRowsPerQuery / USABLE_LOW)} Pickles steps)`,
);
console.log(
  `    Merkle rows, ${NUM_QUERIES} queries: ${merkleRowsAllQueries.toExponential(3)} ` +
    `(${Math.ceil(merkleRowsAllQueries / USABLE_HIGH)}–${Math.ceil(merkleRowsAllQueries / USABLE_LOW)} Pickles steps)`,
);
console.log(
  '    ⚑ Merkle openings ALONE, before the sponges, the folds, the AIR evaluation,\n' +
    '      the DEEP quotient, the challenger, or the recursion glue.',
);

console.log('\n=== MERKLE PASS ===\n');

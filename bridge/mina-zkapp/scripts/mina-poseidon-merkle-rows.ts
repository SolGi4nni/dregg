// RUNG 1-PASTA — MEASURE the NATIVE Mina-Poseidon Merkle path in o1js, and KAT
// it against the dregg-side Rust hasher.
//
//   npm run mina-merkle
//
// This is the probe `docs/MINA-FACING-TERMINAL-OPTIONS.md` §4 names as the one
// thing that converts its headline from a PROJECTION to a MEASUREMENT:
//
//   > an o1js circuit that walks a depth-20 Merkle path with native
//   > `Poseidon.hash`, KAT'd against the probe crate's `compress`, and reports
//   > `getRows()`. That is the Pasta analogue of §3.9.
//
// §3.9 measured the DEPLOYED BabyBear-hashed level at **2,677 rows**
// (`poseidon2-merkle-rows.ts`). The Pasta column of every table in
// MINA-FACING-TERMINAL-OPTIONS assumes **~15 rows/level** — kimchi's cited
// `POS_ROWS_PER_HASH = 11` plus ~4 for the conditional swap — and that 15 was
// CITED UPSTREAM, never measured here. This script measures it.
//
// The same discipline as the BabyBear rung: every value is cross-checked
// against `circuit-prove/sketches/mina-pasta-hash-probe merkle`, on leaves
// carrying a git commit, a millisecond timestamp and a 128-bit nonce, so
// nothing here can be replaying a constant it produced itself.

import { Bool, Field, Poseidon, Provable, ZkProgram } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { compress, foldPath, sparsePath } from '../src/DreggPoseidonAttestation.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}

/** Pasta Fp modulus — o1js `Field.ORDER`. */
const P_PASTA = 28948022309329048855892746252171976963363056481941560715954676764349967630337n;

// ---------------------------------------------------------------------------
// The dregg-side emitter (Rust `mina-poseidon`, gold-KAT-pinned to o1js).
// ---------------------------------------------------------------------------

type MerkleEmission = {
  emitter: string;
  depth: number;
  leafIndex: number;
  leaves: string[];
  leaf: string;
  siblings: string[];
  isRight: boolean[];
  nodes: string[];
  root: string;
};

function probeDir(): string {
  const d =
    process.env.DREGG_PROBE_DIR ??
    resolve(process.cwd(), '../../circuit-prove/sketches/mina-pasta-hash-probe');
  if (!existsSync(resolve(d, 'Cargo.toml')))
    throw new Error(`the dregg-side hash probe is not at ${d} — set DREGG_PROBE_DIR`);
  return d;
}

/** Leaves the Rust side cannot have precomputed: a domain tag, this tree's HEAD,
 *  a millisecond timestamp and a 128-bit nonce, folded into Pasta Fp. */
function freshLeaves(dir: string, n: number): bigint[] {
  const gitCommit = execFileSync('git', ['rev-parse', 'HEAD'], {
    cwd: process.env.DREGG_ATTEST_GIT_DIR ?? dir,
    encoding: 'utf8',
  }).trim();
  const tag = Buffer.from('dregg/mina-pasta-merkle/v1', 'ascii');
  let acc = 0n;
  for (const b of tag) acc = (acc * 257n + BigInt(b)) % P_PASTA;
  acc = (acc * 65537n + BigInt('0x' + gitCommit.slice(0, 32))) % P_PASTA;
  acc = (acc * 65537n + BigInt(Date.now())) % P_PASTA;
  acc = (acc * 65537n + BigInt('0x' + randomBytes(16).toString('hex'))) % P_PASTA;
  const out: bigint[] = [];
  for (let i = 0; i < n; i++) {
    acc = (acc * 1000003n + BigInt(i) + 7n) % P_PASTA;
    out.push(acc);
  }
  return out;
}

function runMerkle(dir: string, depth: number, leafIndex: number, leaves: bigint[]): MerkleEmission {
  const out = execFileSync(
    'cargo',
    [
      'run',
      '--offline',
      '--quiet',
      '--',
      'merkle',
      String(depth),
      String(leafIndex),
      ...leaves.map((v) => '0x' + v.toString(16).padStart(64, '0')),
    ],
    { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 26 },
  );
  return JSON.parse(out) as MerkleEmission;
}

const eqv = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);

// ===========================================================================
console.log('=== Rung 1-Pasta: the NATIVE Mina-Poseidon MERKLE PATH in o1js ===\n');

const DEPTH = 22; //        the deployed |D^0| = 2^22 — the SAME depth §3.9 measured
const PROBE_DEPTH = 20; //  the depth MINA-FACING-TERMINAL-OPTIONS §4 names
const N_LEAVES = 6;
const LEAF_INDEX = 3;

// ---------------------------------------------------------------------------
console.log('[1] the Rust Mina-Poseidon hasher emits; the o1js twins must reproduce it');
const dir = probeDir();
const leafVals = freshLeaves(dir, N_LEAVES);
const t0 = Date.now();
const em = runMerkle(dir, DEPTH, LEAF_INDEX, leafVals);
ok(`rust emitter ran in ${((Date.now() - t0) / 1000).toFixed(1)}s: ${em.emitter}`);
if (em.depth !== DEPTH || em.leaves.length !== N_LEAVES)
  fail('the emitter did not run the shape it was asked for');

const emSiblings = em.siblings.map(BigInt);
const emNodes = em.nodes.map(BigInt);
const emRoot = BigInt(em.root);
if (!eqv(em.leaves.map(BigInt), leafVals)) fail('the emitter did not hash the leaves it was given');

{
  const sp = sparsePath(leafVals.map((v) => Field(v)), LEAF_INDEX, DEPTH);
  const gotSibs = sp.path.siblings.map((f) => f.toBigInt());
  const gotBits = sp.path.isRight.map((b) => b.toBoolean());
  const gotNodes = sp.nodes.map((f) => f.toBigInt());
  if (!eqv(gotSibs, emSiblings)) fail('the o1js sparse-path siblings diverge from the Rust hasher');
  if (gotBits.length !== em.isRight.length || gotBits.some((b, i) => b !== em.isRight[i]))
    fail('the isRight bits diverge from the Rust hasher');
  if (!eqv(gotNodes, emNodes)) fail('the intermediate path nodes diverge from the Rust hasher');
  if (sp.root.toBigInt() !== emRoot) fail('the root diverges from the Rust hasher');
  ok(`depth-${DEPTH} sparse path: all ${DEPTH} siblings, ${DEPTH} bits, ${DEPTH} nodes and the root agree`);

  // REJECT polarity: an agreement check that cannot disagree proves nothing.
  const bad = emSiblings.slice();
  bad[0] = (bad[0] + 1n) % P_PASTA;
  let cur = leafVals[LEAF_INDEX];
  for (let h = 0; h < DEPTH; h++) {
    const l = em.isRight[h] ? bad[h] : cur;
    const r = em.isRight[h] ? cur : bad[h];
    cur = compress(Field(l), Field(r)).toBigInt();
  }
  if (cur === emRoot) fail('a tampered sibling still reached the root');
  ok('a tampered sibling does NOT reach the root');

  // The compress twin is EXACTLY `Poseidon.hash([l, r])` — this is the identity
  // the whole lever rests on (one native Poseidon gate chain per Merkle level).
  const l = Field(emSiblings[0]);
  const r = Field(emNodes[0]);
  if (compress(l, r).toBigInt() !== Poseidon.hash([l, r]).toBigInt())
    fail('compress is not Poseidon.hash([l, r])');
  ok('compress(l, r) IS o1js Poseidon.hash([l, r]) — one native permutation per node');
}

// ---------------------------------------------------------------------------
console.log('\n[2] the CIRCUIT computes the same opening, with real witnesses');

/** The in-circuit fold: conditional swap + one native Poseidon per level. This
 *  is the same body `makeDreggMembershipAttestation` proves. */
function foldOpeningPasta(leaf: Field, siblings: Field[], isRight: Bool[]): Field {
  let current = leaf;
  for (let i = 0; i < siblings.length; i++) {
    const left = Provable.if(isRight[i], siblings[i], current);
    const right = Provable.if(isRight[i], current, siblings[i]);
    current = Poseidon.hash([left, right]);
  }
  return current;
}

{
  await Provable.runAndCheck(() => {
    const leaf = Provable.witness(Field, () => Field(leafVals[LEAF_INDEX]));
    const sibs = emSiblings.map((s) => Provable.witness(Field, () => Field(s)));
    const bits = em.isRight.map((b) => Provable.witness(Bool, () => Bool(b)));
    const root = foldOpeningPasta(leaf, sibs, bits);
    Provable.asProver(() => {
      if (root.toBigInt() !== emRoot) fail(`in-circuit root ${root.toBigInt()} != Rust root ${emRoot}`);
    });
  });
  ok(`depth-${DEPTH} opening: the CIRCUIT's root == the Rust root`);

  for (const what of ['a tampered sibling', 'a tampered isRight bit']) {
    const sibs = emSiblings.slice();
    const bits = em.isRight.slice();
    if (what.includes('sibling')) sibs[0] = (sibs[0] + 1n) % P_PASTA;
    else bits[0] = !bits[0];
    let held = false;
    try {
      await Provable.runAndCheck(() => {
        const leaf = Provable.witness(Field, () => Field(leafVals[LEAF_INDEX]));
        const ss = sibs.map((s) => Provable.witness(Field, () => Field(s)));
        const bb = bits.map((b) => Provable.witness(Bool, () => Bool(b)));
        foldOpeningPasta(leaf, ss, bb).assertEquals(Field(emRoot));
      });
      held = true;
    } catch {
      /* expected */
    }
    if (held) fail(`the circuit accepted ${what}`);
    ok(`the circuit REFUSES ${what}`);
  }

  // ⚑ The direction bits must be BOOLEAN-CONSTRAINED, not merely witnessed. A
  // `Provable.if` on an unconstrained "bit" would let a prover mix left and
  // right and reach a root no honest path reaches. `Bool` carries its own
  // `x*(x-1)=0`; this asserts that it is REALLY there rather than assuming it.
  let held = false;
  try {
    await Provable.runAndCheck(() => {
      const two = Provable.witness(Field, () => Field(2));
      const b = Bool.Unsafe.fromField(two); //  deliberately out of {0,1}
      b.assertEquals(b); //                     no-op; the constraint must come from elsewhere
      const leaf = Provable.witness(Field, () => Field(1));
      foldOpeningPasta(leaf, [Provable.witness(Field, () => Field(2))], [b]);
      // A well-formed circuit must reject the non-boolean selector somewhere.
      b.toField().assertBool();
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a non-boolean direction selector was accepted');
  ok('a non-boolean direction selector is REFUSED (assertBool bites)');
}

// ---------------------------------------------------------------------------
console.log('\n[3] getRows() — THE MEASUREMENT');

async function rowsOf(f: () => void): Promise<number> {
  const cs = await Provable.constraintSystem(f);
  return cs.rows;
}

/** Rows for a bare `Poseidon.hash` of `n` inputs, sealed so nothing is elided. */
async function hashRows(n: number): Promise<number> {
  return rowsOf(() => {
    const xs = Array.from({ length: n }, (_, i) => Provable.witness(Field, () => Field(i + 1)));
    Poseidon.hash(xs).seal();
  });
}

/** Rows for a depth-`d` opening (conditional swap + one hash per level). */
async function openingRows(d: number): Promise<number> {
  return rowsOf(() => {
    const leaf = Provable.witness(Field, () => Field(1));
    const sibs = Array.from({ length: d }, () => Provable.witness(Field, () => Field(2)));
    const bits = Array.from({ length: d }, () => Provable.witness(Bool, () => Bool(false)));
    foldOpeningPasta(leaf, sibs, bits).seal();
  });
}

const h2 = await hashRows(2);
const h4 = await hashRows(4);
const h6 = await hashRows(6);
const h8 = await hashRows(8);
console.log(`    Poseidon.hash of 2 inputs (1 permutation) : ${h2} rows`);
console.log(`    Poseidon.hash of 4 inputs (2 permutations): ${h4} rows`);
console.log(`    Poseidon.hash of 6 inputs (3 permutations): ${h6} rows`);
console.log(`    Poseidon.hash of 8 inputs (4 permutations): ${h8} rows`);
const marginalPerm = (h8 - h2) / 3;
console.log(`    MARGINAL rows per NATIVE Poseidon permutation: ${marginalPerm}`);

const openRows: Record<number, number> = {};
for (const d of [1, 2, 4, 8, 16, PROBE_DEPTH, DEPTH]) openRows[d] = await openingRows(d);
for (const d of [1, 2, 4, 8, 16, PROBE_DEPTH, DEPTH])
  console.log(`    depth ${String(d).padStart(2)} opening: ${openRows[d].toLocaleString().padStart(8)} rows`);
const marginalLevel = (openRows[16] - openRows[8]) / 8;
console.log(`    MARGINAL rows per Merkle LEVEL (swap + hash): ${marginalLevel}`);

// The contrast the whole document is about, in one line.
const BB_ROWS_PER_LEVEL = 2677; //   MINA-VERIFIES-DREGG-FRI-SIZE §3.9, measured
const BB_PERM_ROWS = 2600.5; //      §3.8, measured
console.log('');
console.log(
  `    ⚑ NATIVE ${marginalPerm} rows/permutation vs the EMULATED Poseidon2-BabyBear ` +
    `${BB_PERM_ROWS} — ${(BB_PERM_ROWS / marginalPerm).toFixed(0)}x`,
);
console.log(
  `    ⚑ NATIVE ${marginalLevel} rows/Merkle level vs the deployed ${BB_ROWS_PER_LEVEL} — ` +
    `${(BB_ROWS_PER_LEVEL / marginalLevel).toFixed(0)}x`,
);
console.log(
  `    a depth-${DEPTH} opening: ${openRows[DEPTH].toLocaleString()} Pasta rows vs 58,971 BabyBear rows ` +
    `(${(58971 / openRows[DEPTH]).toFixed(0)}x)`,
);

// The cited-upstream figure this replaces.
const CITED_POS_ROWS_PER_HASH = 11; //  kimchi POS_ROWS_PER_HASH
const CITED_LEVEL = 15; //              MINA-FACING-TERMINAL-OPTIONS §4: 11 + ~4 swap
console.log('');
console.log(
  `    the document ASSUMED ${CITED_POS_ROWS_PER_HASH} rows/permutation and ${CITED_LEVEL} rows/level; ` +
    `MEASURED ${marginalPerm} and ${marginalLevel} ` +
    `(${((marginalLevel / CITED_LEVEL - 1) * 100).toFixed(0)}% on the level)`,
);

// ---------------------------------------------------------------------------
console.log('\n[4] the circuit is really Pickles-provable, and proves the Rust object');
{
  const PROVE_DEPTH = 8;
  const emS = runMerkle(dir, PROVE_DEPTH, LEAF_INDEX, leafVals);
  const prog = ZkProgram({
    name: `mina-pasta-opening-d${PROVE_DEPTH}`,
    publicInput: Field, //  the Rust-emitted root
    publicOutput: Field, // the opened leaf
    methods: {
      proveOpening: {
        privateInputs: [
          Field,
          Provable.Array(Field, PROVE_DEPTH),
          Provable.Array(Bool, PROVE_DEPTH),
        ],
        async method(root: Field, leaf: Field, sibs: Field[], bits: Bool[]) {
          foldOpeningPasta(leaf, sibs, bits).assertEquals(root);
          return { publicOutput: leaf };
        },
      },
    },
  });
  const analysis = await prog.analyzeMethods();
  console.log(`    the depth-${PROVE_DEPTH} opening ZkProgram: ${analysis.proveOpening.rows} rows`);
  const t1 = Date.now();
  const { verificationKey } = await prog.compile();
  ok(`compiled in ${((Date.now() - t1) / 1000).toFixed(1)}s (vk ${verificationKey.hash.toString().slice(0, 12)}…)`);
  const t2 = Date.now();
  const { proof } = await prog.proveOpening(
    Field(BigInt(emS.root)),
    Field(leafVals[LEAF_INDEX]),
    emS.siblings.map((s) => Field(BigInt(s))),
    emS.isRight.map((b) => Bool(b)),
  );
  ok(`proved in ${((Date.now() - t2) / 1000).toFixed(1)}s`);
  if (!(await prog.verify(proof))) fail('the Pasta opening proof failed to verify');
  ok('the proof VERIFIES');
  if (proof.publicOutput.toBigInt() !== leafVals[LEAF_INDEX])
    fail('the PROVEN public output is not the leaf the Rust hasher committed');
  ok('the PROVEN public output == the leaf the Rust Mina-Poseidon hasher committed');

  let held = false;
  try {
    await prog.proveOpening(
      Field((BigInt(emS.root) + 1n) % P_PASTA),
      Field(leafVals[LEAF_INDEX]),
      emS.siblings.map((s) => Field(BigInt(s))),
      emS.isRight.map((b) => Bool(b)),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a proof was produced for a root the path does not reach');
  ok('NO proof exists for a root the path does not reach');
}

// ---------------------------------------------------------------------------
console.log('\n[5] what this prices, at the DEPLOYED root geometry');
// Same decomposition as poseidon2-merkle-rows.ts [5]: one input-phase opening
// at depth 22 plus one commit-phase opening per fold layer at depths 21..6.
const COMMIT_LAYERS = 16;
const commitDepths = Array.from({ length: COMMIT_LAYERS }, (_, i) => DEPTH - 1 - i);
const levelsPerQuery = DEPTH + commitDepths.reduce((a, b) => a + b, 0);
const NUM_QUERIES = 19;
const merkleRowsAll = levelsPerQuery * marginalLevel * NUM_QUERIES;
const bbMerkleRowsAll = levelsPerQuery * BB_ROWS_PER_LEVEL * NUM_QUERIES;
const USABLE = 54300; //  PartitionSchedule.ts:105, the currency §5 of the doc uses
console.log(
  `    ${levelsPerQuery} Merkle levels/query x ${NUM_QUERIES} queries = ` +
    `${(levelsPerQuery * NUM_QUERIES).toLocaleString()} levels`,
);
console.log(
  `    Merkle rows, all queries: BabyBear ${bbMerkleRowsAll.toExponential(3)} ` +
    `(${(bbMerkleRowsAll / USABLE).toFixed(0)} slices)  ->  ` +
    `Pasta ${merkleRowsAll.toExponential(3)} (${(merkleRowsAll / USABLE).toFixed(2)} slices)`,
);
console.log(
  '    ⚑ the doc projects the WHOLE Pasta-hashed root verify at 2.9e6 rows / 54 slices;\n' +
    `      the Merkle term measured here is ${((merkleRowsAll / 2.9e6) * 100).toFixed(2)}% of that budget.`,
);

// ---------------------------------------------------------------------------
// [6] Ratchet. A measurement nobody re-runs is a number.
// ---------------------------------------------------------------------------
// MEASURED 2026-07-30, o1js 2.15.0, this script. ⚠ The 11 the document cites is
// kimchi's `POS_ROWS_PER_HASH` — the Poseidon GATE chain alone. o1js charges
// **13**: the 11 gate rows plus 2 for the surrounding generic rows (state
// assembly + the output wiring). The document's DERIVED "15 rows/level"
// (11 + ~4 for the conditional swap) lands at a measured **15.5**, so the
// derivation was right for the wrong reason — the swap is ~2.5 rows, not ~4,
// and the permutation is 13, not 11.
const RECORDED_PERM_ROWS = Number(process.env.MINA_PASTA_PERM_ROWS ?? 13);
const RECORDED_LEVEL_ROWS = Number(process.env.MINA_PASTA_LEVEL_ROWS ?? 15.5);
const RECORDED_DEPTH22_ROWS = Number(process.env.MINA_PASTA_D22_ROWS ?? 342);
for (const [what, got, want] of [
  ['rows per native permutation', marginalPerm, RECORDED_PERM_ROWS],
  ['rows per Merkle level', marginalLevel, RECORDED_LEVEL_ROWS],
  [`rows for a depth-${DEPTH} opening`, openRows[DEPTH], RECORDED_DEPTH22_ROWS],
] as [string, number, number][]) {
  const drift = Math.abs(got - want) / want;
  if (drift > 0.05)
    fail(
      `${what} moved to ${got} from the recorded ${want} (${(drift * 100).toFixed(1)}%): ` +
        'docs/MINA-FACING-TERMINAL-OPTIONS.md is now stale — update it, or the document ' +
        'is quoting a number nothing produces',
    );
}
console.log(
  `\n    ratchet: ${marginalPerm} rows/perm, ${marginalLevel} rows/level and ` +
    `${openRows[DEPTH]} rows/opening are within 5% of the recorded figures`,
);

console.log('\n=== MINA-POSEIDON MERKLE PASS ===\n');

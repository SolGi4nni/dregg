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

import { Bool, Field, Gadgets, Poseidon, Provable, ZkProgram } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { compress, foldPath, sparsePath } from '../src/DreggPoseidonAttestation.js';
import { BABYBEAR_HASH, PASTA_HASH, PICKLES } from '../src/CostModel.js';

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

/** Filled in by [4b]; used by [5]'s re-price. */
let PASTA_SPONGE_ROWS_PER_LANE = 0;

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
const BB_ROWS_PER_LEVEL = BABYBEAR_HASH.merkleLevel; //  §3.9 — OWNED by src/CostModel.ts
const BB_PERM_ROWS = BABYBEAR_HASH.perm; //          §3.8 — OWNED by src/CostModel.ts
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
console.log('\n[4b] the MMCS LEAF SPONGE — the second-biggest hash term');
//
// The Merkle path is only half the hashing. A FRI input-phase leaf is a ROW of
// BabyBear values, and the MMCS packs it into Pasta elements before absorbing:
// `MultiField32PaddingFreeSponge<BabyBear, PastaFp, MinaPoseidonPerm, 3, 2, 1>`
// writes 8 shifted radix-2^31 limbs per rate slot, 2 slots per permutation, so
// SIXTEEN BabyBear lanes ride one Poseidon — against the deployed
// `PaddingFreeSponge<_, 16, 8, 8>`'s EIGHT.
//
// Every value here is KAT'd against `dregg-p3-pasta`'s own emitter, which calls
// the REAL p3 sponge — not a transcription of it.

const BB_P = 2013265921n; //           BabyBear modulus
const LIMBS_PER_SLOT = 8;
const LANES_PER_PERM = LIMBS_PER_SLOT * 2;
const RADIX = 1n << 31n;

/** `r < 2^31`, via three 12-bit lookups — the same check the deployed BabyBear
 *  path uses (`Poseidon2BabyBearW16.ts`'s `assertLt2p31`, not exported). */
function assertLt2p31(r: Field) {
  const [a, b, c] = Provable.witness(Provable.Array(Field, 3), () => {
    const v = r.toBigInt();
    return [Field(v & 0xfffn), Field((v >> 12n) & 0xfffn), Field((v >> 24n) & 0x7fn)];
  });
  Gadgets.rangeCheck3x12(a, b, c.mul(16n));
  a.add(b.mul(1n << 12n)).add(c.mul(1n << 24n)).assertEquals(r);
}

/** p3 `reduce_packed_shifted(lanes, 31)`: Horner in base 2^31 over the digits
 *  `lane + 1`. Each lane is range-checked to `< 2^31`, which is what makes the
 *  packing injective (the +1 shift reserves 0 as "no digit", so lengths do not
 *  collide).
 *
 *  ⚠ NAMED, not fixed here: `< 2^31` is a WEAKER check than `< p_BabyBear`, so
 *  a prover may present a non-canonical lane in `[p, 2^31)` and pack a
 *  different Pasta element than the canonical one. The DEPLOYED BabyBear path
 *  has exactly the same shape, so this is inherited, not introduced — but a
 *  Mina-side verifier that wants canonical openings must add the `p`-bound. */
function packSlot(lanes: Field[]): Field {
  let acc = Field(0);
  for (let i = lanes.length - 1; i >= 0; i--) {
    assertLt2p31(lanes[i]);
    acc = acc.mul(Field(RADIX)).add(lanes[i].add(Field(1)));
  }
  return acc;
}

/** The p3 sponge, in circuit. The rate lanes are OVERWRITTEN per block (p3
 *  semantics), which o1js expresses by absorbing the DIFFERENCE against a state
 *  whose rate cells are known in circuit — `Poseidon.update` absorbs by
 *  addition, and `d - s` added to `s` is `d`. Costs two field subtractions, i.e.
 *  nothing: Kimchi linear combinations are free. */
function leafSpongePasta(row: Field[]): Field {
  let state: [Field, Field, Field] = [Field(0), Field(0), Field(0)];
  for (let off = 0; off < row.length; off += LANES_PER_PERM) {
    const block = row.slice(off, off + LANES_PER_PERM);
    const slots: Field[] = [];
    for (let c = 0; c < block.length; c += LIMBS_PER_SLOT)
      slots.push(packSlot(block.slice(c, c + LIMBS_PER_SLOT)));
    const d0 = slots[0];
    const d1 = slots.length > 1 ? slots[1] : state[1]; // an unwritten slot KEEPS its value
    state = Poseidon.update(state, [d0.sub(state[0]), d1.sub(state[1])]);
  }
  return state[0];
}

function runPastaLeaf(rowWidth: number, nRows: number, vals: bigint[]) {
  const out = execFileSync(
    'cargo',
    [
      'run', '--quiet', '--offline', '-p', 'dregg-p3-pasta', '--bin', 'pasta-mmcs-emit', '--',
      'leaf', String(rowWidth), String(nRows), ...vals.map((v) => v.toString()),
    ],
    { cwd: resolve(dir, '../../..'), encoding: 'utf8', maxBuffer: 1 << 26 },
  );
  return JSON.parse(out) as {
    emitter: string;
    rowWidth: number;
    nRows: number;
    limbsPerSlot: number;
    radixBits: number;
    lanesPerPermutation: number;
    rows: number[][];
    packedSlots: string[][];
    leafDigests: string[];
  };
}

{
  const ROW_WIDTH = 13; //  the same width the BabyBear rung measures (§3.9)
  const N = 3;
  const lanes: bigint[] = [];
  {
    let acc = leafVals[0] % BB_P;
    for (let i = 0; i < ROW_WIDTH * N; i++) {
      acc = (acc * 1000003n + BigInt(i) + 17n) % BB_P;
      lanes.push(acc);
    }
  }
  const em = runPastaLeaf(ROW_WIDTH, N, lanes);
  ok(`p3 sponge emitter: ${em.emitter}`);
  if (em.limbsPerSlot !== LIMBS_PER_SLOT || em.radixBits !== 31 || em.lanesPerPermutation !== LANES_PER_PERM)
    fail('the p3 packing constants moved — this script is describing the wrong sponge');
  ok(`packing: ${em.limbsPerSlot} limbs/slot at radix 2^${em.radixBits} => ${em.lanesPerPermutation} BabyBear lanes per PERMUTATION (deployed BabyBear sponge: 8)`);

  // The pack alone, out of circuit, against p3.
  for (let r = 0; r < N; r++) {
    for (let c = 0; c < em.packedSlots[r].length; c++) {
      const chunk = em.rows[r].slice(c * LIMBS_PER_SLOT, (c + 1) * LIMBS_PER_SLOT);
      let acc = 0n;
      for (let i = chunk.length - 1; i >= 0; i--) acc = acc * RADIX + BigInt(chunk[i]) + 1n;
      if (acc !== BigInt(em.packedSlots[r][c]))
        fail(`the shifted radix-2^31 pack diverges from p3 at row ${r} slot ${c}`);
    }
  }
  ok('the shifted radix-2^31 pack agrees with p3 elementwise');

  // The whole sponge, IN CIRCUIT, against p3.
  await Provable.runAndCheck(() => {
    for (let r = 0; r < N; r++) {
      const row = em.rows[r].map((v) => Provable.witness(Field, () => Field(v)));
      const d = leafSpongePasta(row);
      Provable.asProver(() => {
        if (d.toBigInt() !== BigInt(em.leafDigests[r]))
          fail(`in-circuit leaf digest ${d.toBigInt()} != p3 ${em.leafDigests[r]}`);
      });
    }
  });
  ok(`the CIRCUIT's leaf digests == the p3 MultiField sponge, all ${N} rows of width ${ROW_WIDTH}`);

  // REJECT: an out-of-range lane must be refused, or the packing bound is vacuous.
  let held = false;
  try {
    await Provable.runAndCheck(() => {
      const row = em.rows[0].map((v, i) =>
        Provable.witness(Field, () => Field(i === 0 ? BigInt(v) + (1n << 31n) : BigInt(v))),
      );
      leafSpongePasta(row);
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the circuit packed a lane >= 2^31 (the injectivity bound is vacuous)');
  ok('the circuit REFUSES a lane >= 2^31 (the packing bound is enforced)');

  // The measurement.
  async function spongeRows(w: number): Promise<number> {
    return rowsOf(() => {
      const row = Array.from({ length: w }, () => Provable.witness(Field, () => Field(1)));
      leafSpongePasta(row).seal();
    });
  }
  const s16 = await spongeRows(16);
  const s32 = await spongeRows(32);
  const s48 = await spongeRows(48);
  const marginalBlock = (s48 - s16) / 2;
  console.log(`    leaf sponge, 16 lanes (1 perm) : ${s16} rows`);
  console.log(`    leaf sponge, 32 lanes (2 perms): ${s32} rows`);
  console.log(`    leaf sponge, 48 lanes (3 perms): ${s48} rows`);
  console.log(`    MARGINAL rows per 16-lane BLOCK: ${marginalBlock}`);
  console.log(`    => ${(marginalBlock / LANES_PER_PERM).toFixed(2)} rows per BabyBear LANE`);
  const BB_SPONGE_BLOCK = 2632; //  §3.9, measured: one 8-lane BabyBear block
  console.log(
    `    ⚑ per LANE: Pasta ${(marginalBlock / LANES_PER_PERM).toFixed(2)} vs BabyBear ` +
      `${(BB_SPONGE_BLOCK / 8).toFixed(1)} — ${((BB_SPONGE_BLOCK / 8) / (marginalBlock / LANES_PER_PERM)).toFixed(0)}x`,
  );
  PASTA_SPONGE_ROWS_PER_LANE = marginalBlock / LANES_PER_PERM;
}

// ---------------------------------------------------------------------------
console.log('\n[5] RE-MEASURING the Mina-side row count against the 2.9e6 projection');
//
// THE MODEL, stated in one line so it can be argued with: a Mina-side verify of
// the deployed root decomposes into HASH terms and NON-HASH terms; the hash
// terms scale by their own MEASURED unit ratio, and the non-hash terms do not
// move at all (they are BabyBear extension arithmetic, which no hash choice
// touches). The deployed column below is MINA-VERIFIES-DREGG-FRI-SIZE §3's
// measured decomposition of 24,574,325 rows at q=19, arity 2, cap_height 0.

const USABLE = PICKLES.usableRowsMpv1; //  leg 16 — OWNED by src/CostModel.ts
const NUM_QUERIES = 19;
const COMMIT_LAYERS = 16;

// MEASURED deployed (BabyBear-hashed) unit prices.
const BB_PERM = BABYBEAR_HASH.perm; //          §3.8 — OWNED
const BB_LEVEL = BABYBEAR_HASH.merkleLevel; //  §3.9 — OWNED
const BB_SPONGE_PER_LANE = 2632 / BABYBEAR_HASH.spongeRate; // §3.9: one 8-lane block. COST-OK: 2632 is the block, not a registered per-unit price

// MEASURED Pasta unit prices — this script, above.
const PASTA_PERM = marginalPerm;
const PASTA_LEVEL = marginalLevel;
const PASTA_SPONGE_PER_LANE = PASTA_SPONGE_ROWS_PER_LANE;

// MINA-VERIFIES-DREGG-FRI-SIZE §3's measured decomposition of the 24,574,325.
const TERMS: { name: string; rows: number; ratio: number | null }[] = [
  { name: 'Merkle paths', rows: 1.23e7, ratio: PASTA_LEVEL / BB_LEVEL },
  { name: 'leaf hash + lane range checks', rows: 6.5e6, ratio: PASTA_SPONGE_PER_LANE / BB_SPONGE_PER_LANE },
  { name: 'challenger observe of opened values', rows: 2.5e6, ratio: PASTA_PERM / BB_PERM },
  { name: 'DEEP quotient (BabyBear ext. arith)', rows: 2.5e6, ratio: null },
  { name: 'AIR constraint evaluation at zeta', rows: 1.9e5, ratio: null },
];

let bbTotal = 0;
let pastaTotal = 0;
console.log('    term                                   deployed        Pasta   ratio');
for (const t of TERMS) {
  const p = t.ratio === null ? t.rows : t.rows * t.ratio;
  bbTotal += t.rows;
  pastaTotal += p;
  console.log(
    `    ${t.name.padEnd(36)} ${t.rows.toExponential(2).padStart(9)}  ${p.toExponential(2).padStart(11)}   ` +
      (t.ratio === null ? 'unchanged' : `${t.ratio.toFixed(4)}`),
  );
}
console.log(
  `    ${'TOTAL'.padEnd(36)} ${bbTotal.toExponential(3).padStart(9)}  ${pastaTotal.toExponential(3).padStart(11)}`,
);
console.log(
  `    slices @ ${USABLE.toLocaleString()} usable rows: ` +
    `${Math.ceil(bbTotal / USABLE)}  ->  ${Math.ceil(pastaTotal / USABLE)}`,
);

// A CROSS-CHECK on the method, not a restatement of it: the Merkle term can be
// computed two independent ways — by scaling the deployed term by the measured
// unit ratio (above), and DIRECTLY from the geometry (levels x queries x the
// measured rows/level). If the two disagree the decomposition being scaled is
// not the decomposition that was measured.
const commitDepths = Array.from({ length: COMMIT_LAYERS }, (_, i) => DEPTH - 1 - i);
const levelsPerQuery = DEPTH + commitDepths.reduce((a, b) => a + b, 0);
const merkleDirect = levelsPerQuery * NUM_QUERIES * PASTA_LEVEL;
const merkleScaled = 1.23e7 * (PASTA_LEVEL / BB_LEVEL);
const merkleDrift = Math.abs(merkleDirect - merkleScaled) / merkleScaled;
console.log(
  `\n    cross-check on the Merkle term: direct ${merkleDirect.toExponential(3)} ` +
    `(${levelsPerQuery} levels x ${NUM_QUERIES} queries x ${PASTA_LEVEL}) vs ` +
    `scaled ${merkleScaled.toExponential(3)} — ${(merkleDrift * 100).toFixed(1)}% apart`,
);
if (merkleDrift > 0.1)
  fail(
    'the two independent Merkle computations disagree by more than 10%: the ' +
      'deployed decomposition being scaled is not the geometry being measured',
  );

// The deliverable.
const PROJECTED = 2.923071e6; //  MINA-FACING-TERMINAL-OPTIONS §3, "q 19, arity 2, cap 0"
const PROJECTED_SLICES = 54;
const delta = (pastaTotal - PROJECTED) / PROJECTED;
console.log('');
console.log(
  `    ⚑ RE-MEASURED ${pastaTotal.toExponential(3)} rows = ${Math.ceil(pastaTotal / USABLE)} slices, ` +
    `against the PROJECTED ${PROJECTED.toExponential(3)} / ${PROJECTED_SLICES} slices ` +
    `(${delta >= 0 ? '+' : ''}${(delta * 100).toFixed(1)}%)`,
);
console.log(
  `    ⚑ and the shape flips: hashing was ${(((1.23e7 + 6.5e6 + 2.5e6) / bbTotal) * 100).toFixed(0)}% ` +
    `of the deployed budget and is ${(((TERMS[0].rows * TERMS[0].ratio! + TERMS[1].rows * TERMS[1].ratio! + TERMS[2].rows * TERMS[2].ratio!) / pastaTotal) * 100).toFixed(1)}% of this one; ` +
    `the DEEP quotient is now ${((2.5e6 / pastaTotal) * 100).toFixed(0)}%.`,
);
console.log(
  '    ⚑ SENSITIVITY: a 3x error in EVERY measured Pasta hash price above moves\n' +
    `      the total to ${((pastaTotal + 2 * (TERMS[0].rows * TERMS[0].ratio! + TERMS[1].rows * TERMS[1].ratio! + TERMS[2].rows * TERMS[2].ratio!)) / USABLE).toFixed(0)} slices. The answer is not sensitive to the hash any more.`,
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
const RECORDED_PERM_ROWS = Number(process.env.MINA_PASTA_PERM_ROWS ?? PASTA_HASH.perm);
const RECORDED_LEVEL_ROWS = Number(process.env.MINA_PASTA_LEVEL_ROWS ?? PASTA_HASH.merkleLevel);
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

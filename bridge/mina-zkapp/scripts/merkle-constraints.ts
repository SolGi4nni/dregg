// GO/NO-GO Part B: o1js/Kimchi constraint count for native-Poseidon Merkle
// openings at the REAL apex-shrink FRI shape (chain/gnark/fixtures/
// apex_shrink_fri_real.json: log_global_max_height=18, 15 commit rounds,
// 38 queries) — the load-bearing sizing measurement for a Pickles-recursive
// FRI verifier over a Pasta-instantiated DreggOuterConfig.
//
// Run: node scripts/merkle-constraints.mjs
import { Field, Bool, Poseidon, Provable, ZkProgram, Struct } from 'o1js';

const DEPTH = 18; // real tree height: degree_bits max 15 + log_blowup 3

// ---------------------------------------------------------------------------
// Micro-measurements: rows per primitive
// ---------------------------------------------------------------------------

async function rowsOf(name: string, f: () => void) {
  const cs = await Provable.constraintSystem(f);
  console.log(`${name}: ${cs.rows} rows`);
  return cs.rows;
}

const rowsHash2 = await rowsOf('Poseidon.hash([l,r]) (1 permutation)', () => {
  const l = Provable.witness(Field, () => Field(1));
  const r = Provable.witness(Field, () => Field(2));
  Poseidon.hash([l, r]);
});

const rowsHash16 = await rowsOf('Poseidon.hash(16 fields) (8 permutations)', () => {
  const xs = Array.from({ length: 16 }, (_, i) =>
    Provable.witness(Field, () => Field(i))
  );
  Poseidon.hash(xs);
});

const rowsSwapHash = await rowsOf('cond-swap + Poseidon.hash (1 Merkle level)', () => {
  const cur = Provable.witness(Field, () => Field(1));
  const sib = Provable.witness(Field, () => Field(2));
  const bit = Provable.witness(Bool, () => Bool(false));
  const l = Provable.if(bit, sib, cur);
  const r = Provable.if(bit, cur, sib);
  Poseidon.hash([l, r]);
});

// ---------------------------------------------------------------------------
// The ZkProgram: N depth-18 Merkle openings (the FRI query walk shape)
// ---------------------------------------------------------------------------

function verifyOpening(root: Field, leaf: Field, siblings: Field[], bits: Bool[]) {
  let cur = leaf;
  for (let i = 0; i < DEPTH; i++) {
    const l = Provable.if(bits[i], siblings[i], cur);
    const r = Provable.if(bits[i], cur, siblings[i]);
    cur = Poseidon.hash([l, r]);
  }
  cur.assertEquals(root);
}

class Opening extends Struct({
  leaf: Field,
  siblings: Provable.Array(Field, DEPTH),
  bits: Provable.Array(Bool, DEPTH),
}) {}

const MerkleProbe = ZkProgram({
  name: 'mina-pasta-merkle-probe',
  publicInput: Field, // the MMCS root

  methods: {
    verify1: {
      privateInputs: [Opening],
      async method(root, o) {
        verifyOpening(root, o.leaf, o.siblings, o.bits);
      },
    },
    verify4: {
      // one FRI query's INPUT-opening shape: 4 batch openings at depth 18
      privateInputs: [Opening, Opening, Opening, Opening],
      async method(root, a, b, c, d) {
        for (const o of [a, b, c, d]) {
          verifyOpening(root, o.leaf, o.siblings, o.bits);
        }
      },
    },
  },
});

const analysis = await MerkleProbe.analyzeMethods();
const rows1 = analysis.verify1.rows;
const rows4 = analysis.verify4.rows;
console.log(`\nZkProgram verify1 (1 depth-${DEPTH} opening): ${rows1} rows`);
console.log(`ZkProgram verify4 (4 depth-${DEPTH} openings): ${rows4} rows`);
console.log(`marginal rows/opening: ${(rows4 - rows1) / 3}`);

// ---------------------------------------------------------------------------
// Extrapolation to the full FRI verify at the real fixture shape
// ---------------------------------------------------------------------------
// Permutation counts derived from apex_shrink_fri_real.json (exact geometry,
// p3 verify_batch semantics — sibling compresses + injection compresses +
// row sponges, computed per input round from the fixture's matrix dims):
//   per query: 4 input openings (72 sibling compresses + injection compresses
//   + row-sponge perms over 967 opened BabyBear columns packed 8x31-bit limbs
//   per Fp, rate 2) + 15 commit-phase paths (depths 17..3 = 150 compresses +
//   15 pair-leaf perms).
const PERMS_PER_QUERY = 316; // exact count from the fixture geometry
const QUERIES = 38;
const rowsPerPerm = rowsSwapHash; // conservative: every hash behind a swap
const hashRowsFull = PERMS_PER_QUERY * QUERIES * rowsPerPerm;
const KIMCHI_CEILING = 2 ** 16;
console.log(`\n--- extrapolation (real fixture shape) ---`);
console.log(`perms/query=${PERMS_PER_QUERY}, queries=${QUERIES}, rows/perm<=${rowsPerPerm}`);
console.log(`hashing rows, full FRI verify: ~${hashRowsFull.toLocaleString()}`);
console.log(
  `Pickles steps for hashing alone (2^16 ceiling): ${(hashRowsFull / KIMCHI_CEILING).toFixed(1)}`
);

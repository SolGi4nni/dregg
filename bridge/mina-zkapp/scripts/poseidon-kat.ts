// Gold-KAT generator/checker: o1js `Poseidon.hash` (Mina-Poseidon / kimchi
// params over Pasta Fp) for the fixed inputs the Rust probe at
// `circuit-prove/sketches/mina-pasta-hash-probe` asserts bit-exact.
//
// It PRINTS the vectors (so they can be re-pasted into the Rust probe and into
// `src/rust-gold-vectors.ts`) and CHECKS them against the pinned table, so a
// drift on either side is visible here too. The attestation gate runs the same
// comparison; this script exists for regeneration.
//
//   npm run kat

import { Field, Poseidon, MerkleTree } from 'o1js';
import {
  PASTA_FP_MODULUS_HEX,
  RUST_GOLD_HASHES,
  RUST_MERKLE_ROOT_1234,
  RUST_MERKLE_LEAVES_1234,
  goldInputs,
  fpHex,
} from '../src/rust-gold-vectors.js';

let bad = 0;

const modulusHex = '0x' + Field.ORDER.toString(16).padStart(64, '0');
console.log('# o1js Field.ORDER =', modulusHex);
if (modulusHex !== PASTA_FP_MODULUS_HEX) {
  console.error(`  ✗ modulus differs from the pinned Rust value ${PASTA_FP_MODULUS_HEX}`);
  bad++;
}

for (const c of RUST_GOLD_HASHES) {
  const got = fpHex(Poseidon.hash(goldInputs(c)));
  const mark = got === c.digest ? ' ' : '✗';
  console.log(`${mark} ${c.name.padEnd(16)} = ${got}`);
  if (got !== c.digest) {
    console.error(`    pinned: ${c.digest}`);
    bad++;
  }
}

// MMCS-shape cross-check: o1js `MerkleTree` (nodes = `Poseidon.hash([l, r])`),
// depth-2 root over leaves [1,2,3,4] — matched by the Rust probe's `compress`.
const tree = new MerkleTree(3);
RUST_MERKLE_LEAVES_1234.forEach((x, i) => tree.setLeaf(BigInt(i), Field(x)));
const root = tree.getRoot();
const rootOk = root.toBigInt() === RUST_MERKLE_ROOT_1234;
console.log(`${rootOk ? ' ' : '✗'} merkle_root_1234 = ${fpHex(root)}`);
if (!rootOk) {
  console.error(
    `    pinned: 0x${RUST_MERKLE_ROOT_1234.toString(16).padStart(64, '0')}`,
  );
  bad++;
}

if (bad > 0) {
  console.error(`\n=== FAILED === (${bad} vector(s) diverged from the Rust pin)\n`);
  process.exit(1);
}
console.log('\n=== PASS === (all vectors agree with the Rust probe pin)\n');

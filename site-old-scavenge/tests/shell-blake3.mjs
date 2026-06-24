// The shell's BLAKE3 (cell-id derivation) against the official BLAKE3 test
// vectors (tests/mocks/blake3-test-vectors.json = BLAKE3-team/BLAKE3
// test_vectors/test_vectors.json): hash + derive_key modes, every published
// input length, first 32 output bytes (the shell only emits 32-byte ids).
//
// Also pins the derive_raw composition shape: deriveCellIdHex(pubkey) must be
// derive_key("dregg-cell-id-v1", pubkey ‖ blake3("default")).
//
// Run: node site/tests/shell-blake3.mjs

import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const SHELL = path.join(SITE, 'src', '_includes', 'studio', 'shell');

const { blake3Hash, blake3DeriveKey, deriveCellIdHex, bytesToHex, hexToBytes } =
  await import(path.join(SHELL, 'blake3.js'));

const vectors = JSON.parse(
  fs.readFileSync(path.join(SITE, 'tests', 'mocks', 'blake3-test-vectors.json'), 'utf-8'),
);

let failures = 0;
let passes = 0;
function check(cond, what) {
  if (!cond) { console.error(`FAIL: ${what}`); failures++; }
  else passes++;
}

function inputOfLen(n) {
  const buf = new Uint8Array(n);
  for (let i = 0; i < n; i += 1) buf[i] = i % 251;
  return buf;
}

for (const c of vectors.cases) {
  const input = inputOfLen(c.input_len);
  check(
    bytesToHex(blake3Hash(input)) === c.hash.slice(0, 64),
    `hash(len=${c.input_len})`,
  );
  check(
    bytesToHex(blake3DeriveKey(vectors.context_string, input)) === c.derive_key.slice(0, 64),
    `derive_key(len=${c.input_len})`,
  );
}

// derive_raw composition: cell id = derive_key("dregg-cell-id-v1", pk ‖ H("default")).
{
  const pk = inputOfLen(32);
  const tokenId = blake3Hash('default');
  const material = new Uint8Array(64);
  material.set(pk, 0);
  material.set(tokenId, 32);
  const expected = bytesToHex(blake3DeriveKey('dregg-cell-id-v1', material));
  check(deriveCellIdHex(pk) === expected, 'deriveCellIdHex composition');
  check(deriveCellIdHex(pk).length === 64, 'cell id is 64 hex chars');
  check(bytesToHex(hexToBytes(expected)) === expected, 'hex round-trip');
}

console.log(`${passes} checks passed, ${failures} failed`);
if (failures) process.exit(1);

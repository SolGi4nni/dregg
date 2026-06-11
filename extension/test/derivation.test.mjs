// Golden key-derivation vector — the extension's third pin.
//
// The dregg identity derivation is:
//
//   blake3::derive_key("dregg/0", seed64) -> 32-byte Ed25519 seed -> pubkey
//
// implemented in Rust in sdk/src/mnemonic.rs (`AgentCipherclerk::from_seed`),
// replicated in cli/src/commands/id.rs, and performed for the extension by
// the wasm crate (wasm/src/lib.rs `derive_keypair_from_mnemonic`, the
// `blake3::derive_key("dregg/0", &seed)` step). All three Rust sites pin the
// SAME golden vector (seed = 00..3f); this test pins it in JS with an
// independent BLAKE3 implementation + node:crypto Ed25519, so if ANY
// implementation drifts, its golden test fails alongside these.
//
// Golden vector (sdk/src/profiles.rs + cli/src/commands/id.rs):
//   seed   = 000102...3f (64 bytes)
//   pubkey = 335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createPrivateKey, createPublicKey } from 'node:crypto';

// ---------------------------------------------------------------------------
// Minimal BLAKE3 (single-chunk inputs <= 1024 bytes — ample for key
// derivation contexts and 64-byte seeds). Independent of the Rust/wasm code.
// ---------------------------------------------------------------------------

const IV = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];
const MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];
const CHUNK_START = 1 << 0;
const CHUNK_END = 1 << 1;
const ROOT = 1 << 3;
const DERIVE_KEY_CONTEXT = 1 << 5;
const DERIVE_KEY_MATERIAL = 1 << 6;

const rotr = (x, n) => ((x >>> n) | (x << (32 - n))) >>> 0;

function g(s, a, b, c, d, mx, my) {
  s[a] = (s[a] + s[b] + mx) >>> 0;
  s[d] = rotr(s[d] ^ s[a], 16);
  s[c] = (s[c] + s[d]) >>> 0;
  s[b] = rotr(s[b] ^ s[c], 12);
  s[a] = (s[a] + s[b] + my) >>> 0;
  s[d] = rotr(s[d] ^ s[a], 8);
  s[c] = (s[c] + s[d]) >>> 0;
  s[b] = rotr(s[b] ^ s[c], 7);
}

function roundFn(s, m) {
  g(s, 0, 4, 8, 12, m[0], m[1]);
  g(s, 1, 5, 9, 13, m[2], m[3]);
  g(s, 2, 6, 10, 14, m[4], m[5]);
  g(s, 3, 7, 11, 15, m[6], m[7]);
  g(s, 0, 5, 10, 15, m[8], m[9]);
  g(s, 1, 6, 11, 12, m[10], m[11]);
  g(s, 2, 7, 8, 13, m[12], m[13]);
  g(s, 3, 4, 9, 14, m[14], m[15]);
}

function compress(cv, blockWords, counter, blockLen, flags) {
  const s = [
    cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
    IV[0], IV[1], IV[2], IV[3],
    counter >>> 0, Math.floor(counter / 2 ** 32) >>> 0, blockLen >>> 0, flags >>> 0,
  ];
  let m = blockWords.slice();
  for (let r = 0; r < 7; r++) {
    roundFn(s, m);
    if (r < 6) m = MSG_PERMUTATION.map((i) => m[i]);
  }
  const out = new Array(16);
  for (let i = 0; i < 8; i++) {
    out[i] = (s[i] ^ s[i + 8]) >>> 0;
    out[i + 8] = (s[i + 8] ^ cv[i]) >>> 0;
  }
  return out;
}

const readLE32 = (bytes, off) =>
  (bytes[off] | (bytes[off + 1] << 8) | (bytes[off + 2] << 16) | (bytes[off + 3] << 24)) >>> 0;

function wordsToBytes(words) {
  const out = new Uint8Array(words.length * 4);
  words.forEach((w, i) => {
    out[i * 4] = w & 0xff;
    out[i * 4 + 1] = (w >>> 8) & 0xff;
    out[i * 4 + 2] = (w >>> 16) & 0xff;
    out[i * 4 + 3] = (w >>> 24) & 0xff;
  });
  return out;
}

const bytesToWords = (bytes) =>
  Array.from({ length: bytes.length / 4 }, (_, i) => readLE32(bytes, i * 4));

/** BLAKE3 of a single-chunk input (<= 1024 bytes), 32-byte output. */
function blake3SingleChunk(input, keyWords, flags) {
  if (input.length > 1024) throw new Error('single-chunk implementation only');
  let cv = keyWords.slice();
  const blocks = [];
  if (input.length === 0) {
    blocks.push(new Uint8Array(0));
  } else {
    for (let i = 0; i < input.length; i += 64) blocks.push(input.slice(i, i + 64));
  }
  for (let i = 0; i < blocks.length; i++) {
    let blockFlags = flags;
    if (i === 0) blockFlags |= CHUNK_START;
    const last = i === blocks.length - 1;
    if (last) blockFlags |= CHUNK_END | ROOT;
    const padded = new Uint8Array(64);
    padded.set(blocks[i]);
    const out = compress(cv, bytesToWords(padded), 0, blocks[i].length, blockFlags);
    if (last) return wordsToBytes(out.slice(0, 8));
    cv = out.slice(0, 8);
  }
}

const blake3 = (input) => blake3SingleChunk(input, IV, 0);

/** blake3::derive_key(context, keyMaterial) — 32-byte output. */
function blake3DeriveKey(context, keyMaterial) {
  const contextKey = blake3SingleChunk(new TextEncoder().encode(context), IV, DERIVE_KEY_CONTEXT);
  return blake3SingleChunk(keyMaterial, bytesToWords(contextKey), DERIVE_KEY_MATERIAL);
}

const hex = (bytes) => Buffer.from(bytes).toString('hex');

/** Ed25519 public key from a 32-byte seed via node:crypto (PKCS8 DER). */
function ed25519PublicKey(seed32) {
  const pkcs8Prefix = Buffer.from('302e020100300506032b657004220420', 'hex');
  const priv = createPrivateKey({
    key: Buffer.concat([pkcs8Prefix, Buffer.from(seed32)]),
    format: 'der',
    type: 'pkcs8',
  });
  const spki = createPublicKey(priv).export({ format: 'der', type: 'spki' });
  return new Uint8Array(spki.subarray(spki.length - 32));
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

test('BLAKE3 implementation matches official test vectors', () => {
  // From the BLAKE3 reference test vectors (input length 0 and 1024).
  assert.equal(
    hex(blake3(new Uint8Array(0))),
    'af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262',
  );
  // Repeating 0..250 pattern, length 63 (sub-block) and 127 (multi-block).
  const pattern = (len) => Uint8Array.from({ length: len }, (_, i) => i % 251);
  assert.equal(
    hex(blake3(pattern(63))),
    'e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b',
  );
  assert.equal(
    hex(blake3(pattern(127))),
    'd81293fda863f008c09e92fc382a81f5a0b4a1251cba1634016a0f86a6bd640d',
  );
  // The derive_key mode (DERIVE_KEY_CONTEXT/MATERIAL flags) is validated
  // against the Rust `blake3::derive_key` by the golden-vector test below:
  // it only passes if both keying stages match the reference byte-for-byte.
});

test('golden vector: blake3 derive_key("dregg/0", 00..3f) -> Ed25519 pubkey 335840a9..8b9a', () => {
  const seed = Uint8Array.from({ length: 64 }, (_, i) => i);
  const ed25519Seed = blake3DeriveKey('dregg/0', seed);
  const pubkey = ed25519PublicKey(ed25519Seed);
  assert.equal(
    hex(pubkey),
    '335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a',
    'extension-side key derivation diverged from the SDK/CLI profile stores ' +
    '(sdk/src/profiles.rs + cli/src/commands/id.rs pin this same vector)',
  );
});

test('derivation is deterministic and seed-sensitive', () => {
  const seed = Uint8Array.from({ length: 64 }, (_, i) => i);
  const a = blake3DeriveKey('dregg/0', seed);
  const b = blake3DeriveKey('dregg/0', seed);
  assert.equal(hex(a), hex(b));
  const tweaked = seed.slice();
  tweaked[0] ^= 1;
  assert.notEqual(hex(blake3DeriveKey('dregg/0', tweaked)), hex(a));
  // Context separation: a different path yields a different key.
  assert.notEqual(hex(blake3DeriveKey('dregg/1', seed)), hex(a));
});

// Minimal pure-JS BLAKE3 for SINGLE-CHUNK inputs (<= 1024 bytes) — enough to
// reconstruct `TurnExecutor::compute_signing_message` (a ~123-byte input) in
// the federation-domain verification tests WITHOUT trusting the code under
// test. Grounded at runtime against the wasm `blake3_hash` export across
// block boundaries before any verification uses it (see run.mjs).
const IV = new Uint32Array([
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
]);
const PERM = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];
const CHUNK_START = 1, CHUNK_END = 2, ROOT = 8;
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

function compress(cv, block, blockLen, flags) {
  const s = new Uint32Array(16);
  s.set(cv.subarray(0, 8), 0);
  s.set(IV.subarray(0, 4), 8);
  s[12] = 0; // chunk counter low (single chunk 0)
  s[13] = 0; // chunk counter high
  s[14] = blockLen;
  s[15] = flags;
  let m = Array.from(block);
  for (let r = 0; r < 7; r++) {
    g(s, 0, 4, 8, 12, m[0], m[1]);
    g(s, 1, 5, 9, 13, m[2], m[3]);
    g(s, 2, 6, 10, 14, m[4], m[5]);
    g(s, 3, 7, 11, 15, m[6], m[7]);
    g(s, 0, 5, 10, 15, m[8], m[9]);
    g(s, 1, 6, 11, 12, m[10], m[11]);
    g(s, 2, 7, 8, 13, m[12], m[13]);
    g(s, 3, 4, 9, 14, m[14], m[15]);
    if (r < 6) m = PERM.map((i) => m[i]);
  }
  const out = new Uint32Array(8);
  for (let i = 0; i < 8; i++) out[i] = (s[i] ^ s[i + 8]) >>> 0;
  return out;
}

/** BLAKE3 hash (32 bytes) of a single-chunk input. */
export function blake3(input) {
  if (input.length > 1024) throw new Error("single-chunk blake3 only (<= 1024 bytes)");
  let cv = new Uint32Array(IV);
  const nBlocks = Math.max(1, Math.ceil(input.length / 64));
  for (let b = 0; b < nBlocks; b++) {
    const slice = input.subarray(b * 64, Math.min((b + 1) * 64, input.length));
    const padded = new Uint8Array(64);
    padded.set(slice);
    const words = new Uint32Array(16);
    const dv = new DataView(padded.buffer);
    for (let i = 0; i < 16; i++) words[i] = dv.getUint32(i * 4, true);
    let flags = 0;
    if (b === 0) flags |= CHUNK_START;
    if (b === nBlocks - 1) flags |= CHUNK_END | ROOT;
    cv = compress(cv, words, slice.length, flags);
  }
  const out = new Uint8Array(32);
  const dv = new DataView(out.buffer);
  for (let i = 0; i < 8; i++) dv.setUint32(i * 4, cv[i], true);
  return out;
}

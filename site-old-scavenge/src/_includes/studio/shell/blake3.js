/**
 * blake3.js — compact BLAKE3 (hash + derive_key), pure ES module.
 *
 * The shell derives a profile's hosted cell id exactly the way the node does
 * (`types/src/lib.rs CellId::derive_raw`):
 *
 *     cell_id = blake3::derive_key("dregg-cell-id-v1", public_key ‖ token_id)
 *     token_id (default domain) = blake3::hash("default")
 *
 * The shipped wasm pkg exposes only string-input plain `blake3_hash`, which can
 * neither take raw bytes nor run the derive_key mode — so the derivation lives
 * here. Verified against the official BLAKE3 test vectors (hash + derive_key
 * across all published input lengths) by site/tests/shell-blake3.mjs.
 *
 * 32-byte outputs only (all dregg ids are 32 bytes); no XOF beyond one block.
 */

const IV = new Uint32Array([
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
]);

const MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

const CHUNK_LEN = 1024;
const BLOCK_LEN = 64;

const CHUNK_START = 1 << 0;
const CHUNK_END = 1 << 1;
const PARENT = 1 << 2;
const ROOT = 1 << 3;
const DERIVE_KEY_CONTEXT = 1 << 5;
const DERIVE_KEY_MATERIAL = 1 << 6;

function rotr(x, n) {
  return ((x >>> n) | (x << (32 - n))) >>> 0;
}

function g(state, a, b, c, d, mx, my) {
  state[a] = (state[a] + state[b] + mx) >>> 0;
  state[d] = rotr(state[d] ^ state[a], 16);
  state[c] = (state[c] + state[d]) >>> 0;
  state[b] = rotr(state[b] ^ state[c], 12);
  state[a] = (state[a] + state[b] + my) >>> 0;
  state[d] = rotr(state[d] ^ state[a], 8);
  state[c] = (state[c] + state[d]) >>> 0;
  state[b] = rotr(state[b] ^ state[c], 7);
}

function roundFn(state, m) {
  g(state, 0, 4, 8, 12, m[0], m[1]);
  g(state, 1, 5, 9, 13, m[2], m[3]);
  g(state, 2, 6, 10, 14, m[4], m[5]);
  g(state, 3, 7, 11, 15, m[6], m[7]);
  g(state, 0, 5, 10, 15, m[8], m[9]);
  g(state, 1, 6, 11, 12, m[10], m[11]);
  g(state, 2, 7, 8, 13, m[12], m[13]);
  g(state, 3, 4, 9, 14, m[14], m[15]);
}

/** Core compression. Returns the full 16-word output state. */
function compress(cv, blockWords, counter, blockLen, flags) {
  const state = new Uint32Array(16);
  state.set(cv.subarray(0, 8), 0);
  state.set(IV.subarray(0, 4), 8);
  state[12] = counter >>> 0;
  // Chunk counters stay far below 2^32 for any input this module accepts.
  state[13] = Math.floor(counter / 0x100000000) >>> 0;
  state[14] = blockLen;
  state[15] = flags;

  let m = Uint32Array.from(blockWords);
  for (let r = 0; r < 7; r += 1) {
    roundFn(state, m);
    if (r < 6) {
      const next = new Uint32Array(16);
      for (let i = 0; i < 16; i += 1) next[i] = m[MSG_PERMUTATION[i]];
      m = next;
    }
  }
  for (let i = 0; i < 8; i += 1) {
    state[i] = (state[i] ^ state[i + 8]) >>> 0;
    state[i + 8] = (state[i + 8] ^ cv[i]) >>> 0;
  }
  return state;
}

function wordsFromBlock(bytes, offset, len) {
  const words = new Uint32Array(16);
  // Partial final blocks are zero-padded (the spec's pad-with-zeros rule).
  for (let i = 0; i < len; i += 1) {
    words[i >> 2] |= bytes[offset + i] << ((i & 3) * 8);
  }
  for (let i = 0; i < 16; i += 1) words[i] = words[i] >>> 0;
  return words;
}

/**
 * Hash one chunk to a chaining value, or — when it is the only node — to the
 * root output state. Returns { cv, lastBlockWords, lastBlockLen, lastFlags }.
 */
function chunkState(keyWords, input, chunkStart, chunkLen, chunkCounter, baseFlags) {
  let cv = Uint32Array.from(keyWords);
  const blockCount = Math.max(1, Math.ceil(chunkLen / BLOCK_LEN));
  let last = null;
  for (let b = 0; b < blockCount; b += 1) {
    const off = chunkStart + b * BLOCK_LEN;
    const len = Math.min(BLOCK_LEN, chunkLen - b * BLOCK_LEN);
    let flags = baseFlags;
    if (b === 0) flags |= CHUNK_START;
    if (b === blockCount - 1) {
      flags |= CHUNK_END;
      last = { cv: Uint32Array.from(cv), words: wordsFromBlock(input, off, len), len, flags };
      break; // the caller decides whether the last block is ROOT
    }
    const out = compress(cv, wordsFromBlock(input, off, len), chunkCounter, len, flags);
    cv = out.subarray(0, 8);
  }
  return last;
}

function rootBytes(cv, blockWords, blockLen, flags, counterForRoot) {
  const out = compress(cv, blockWords, counterForRoot, blockLen, flags | ROOT);
  const bytes = new Uint8Array(32);
  for (let i = 0; i < 8; i += 1) {
    bytes[i * 4] = out[i] & 0xff;
    bytes[i * 4 + 1] = (out[i] >>> 8) & 0xff;
    bytes[i * 4 + 2] = (out[i] >>> 16) & 0xff;
    bytes[i * 4 + 3] = (out[i] >>> 24) & 0xff;
  }
  return bytes;
}

/** Hash `input` with the given 8-word key and base flags → 32 bytes. */
function blake3Internal(keyWords, input, baseFlags) {
  const totalLen = input.length;
  const chunkCount = Math.max(1, Math.ceil(totalLen / CHUNK_LEN));

  if (chunkCount === 1) {
    const last = chunkState(keyWords, input, 0, totalLen, 0, baseFlags);
    return rootBytes(last.cv, last.words, last.len, last.flags, 0);
  }

  // Multi-chunk: compute chunk CVs, then fold the canonical left-full tree.
  const cvs = [];
  for (let c = 0; c < chunkCount; c += 1) {
    const start = c * CHUNK_LEN;
    const len = Math.min(CHUNK_LEN, totalLen - start);
    const last = chunkState(keyWords, input, start, len, c, baseFlags);
    const out = compress(last.cv, last.words, c, last.len, last.flags);
    cvs.push(out.subarray(0, 8));
  }

  function parentBlock(left, right) {
    const words = new Uint32Array(16);
    words.set(left, 0);
    words.set(right, 8);
    return words;
  }

  // Reduce: each merge joins a left subtree holding the largest power-of-two
  // number of chunks. Recursive form mirrors the reference implementation.
  function merge(list) {
    if (list.length === 1) return { cv: list[0], words: null };
    let split = 1;
    while (split * 2 < list.length) split *= 2;
    const left = merge(list.slice(0, split));
    const right = merge(list.slice(split));
    const leftCv = finishSubtree(left);
    const rightCv = finishSubtree(right);
    return { cv: null, words: parentBlock(leftCv, rightCv) };
  }
  function finishSubtree(node) {
    if (node.cv) return node.cv;
    const out = compress(keyWords, node.words, 0, BLOCK_LEN, baseFlags | PARENT);
    return out.subarray(0, 8);
  }

  const rootNode = merge(cvs);
  return rootBytes(keyWords, rootNode.words, BLOCK_LEN, baseFlags | PARENT, 0);
}

function toBytes(input) {
  if (input instanceof Uint8Array) return input;
  if (typeof input === 'string') return new TextEncoder().encode(input);
  return new Uint8Array(input);
}

function keyWordsFromBytes(bytes) {
  const words = new Uint32Array(8);
  for (let i = 0; i < 8; i += 1) {
    words[i] = (bytes[i * 4] | (bytes[i * 4 + 1] << 8) | (bytes[i * 4 + 2] << 16) | (bytes[i * 4 + 3] << 24)) >>> 0;
  }
  return words;
}

/** blake3::hash — 32 bytes. */
export function blake3Hash(input) {
  return blake3Internal(IV, toBytes(input), 0);
}

/** blake3::derive_key(context, material) — 32 bytes. */
export function blake3DeriveKey(context, material) {
  const contextKey = blake3Internal(IV, toBytes(context), DERIVE_KEY_CONTEXT);
  return blake3Internal(keyWordsFromBytes(contextKey), toBytes(material), DERIVE_KEY_MATERIAL);
}

export function bytesToHex(bytes) {
  return Array.from(bytes, (b) => b.toString(16).padStart(2, '0')).join('');
}

export function hexToBytes(hex) {
  const clean = String(hex).replace(/^0x/, '');
  const out = new Uint8Array(clean.length >> 1);
  for (let i = 0; i < out.length; i += 1) out[i] = parseInt(clean.substr(i * 2, 2), 16);
  return out;
}

/**
 * The node's cell-id derivation (`CellId::derive_raw`) for the default token
 * domain: derive_key("dregg-cell-id-v1", pubkey(32) ‖ blake3("default")(32)).
 * Returns 64-char hex.
 */
export function deriveCellIdHex(publicKeyBytes) {
  const pk = toBytes(publicKeyBytes);
  if (pk.length !== 32) throw new Error('public key must be 32 bytes');
  const tokenId = blake3Hash('default');
  const buf = new Uint8Array(64);
  buf.set(pk, 0);
  buf.set(tokenId, 32);
  return bytesToHex(blake3DeriveKey('dregg-cell-id-v1', buf));
}

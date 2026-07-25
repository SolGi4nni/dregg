/**
 * BLAKE3 — portable JS (hash + derive_key modes), for IN-BROWSER verification.
 *
 * This is a direct port of `sdk-ts/src/internal/blake3.ts` (same algorithm, same
 * constants, `.ts` types stripped). That module is itself pinned by the repo's
 * golden derivation vector and differentially tested against the `dregg-wasm`
 * build, so this file inherits a checked lineage rather than being a fresh
 * hand-roll.
 *
 * WHY IT IS HERE: the explorer's proof check must run in the READER's browser.
 * If the server recomputed the ledger root, the reader would just be trusting a
 * second server. The point of `GET /api/cell/{id}/proof` is that the fold is
 * reproducible by anyone holding the leaves — so the fold happens here, on the
 * reader's machine, over bytes the reader can see in the raw JSON.
 *
 * Full tree hashing is implemented (inputs > 1024 bytes split per the BLAKE3
 * spec), so this agrees with the Rust `blake3` crate at any length. The ledger
 * root folds 8 + 64*N bytes, which is many chunks on a real ledger — the tree
 * layer is load-bearing, not decoration.
 */

const IV = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

const MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

const CHUNK_LEN = 1024;
const BLOCK_LEN = 64;

const CHUNK_START = 1 << 0;
const CHUNK_END = 1 << 1;
const PARENT = 1 << 2;
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

function compress(cv, blockWords, counterLo, counterHi, blockLen, flags) {
  const s = [
    cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
    IV[0], IV[1], IV[2], IV[3],
    counterLo >>> 0, counterHi >>> 0, blockLen >>> 0, flags >>> 0,
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

function bytesToWords(bytes) {
  const out = new Array(bytes.length / 4);
  for (let i = 0; i < out.length; i++) out[i] = readLE32(bytes, i * 4);
  return out;
}

function chunkOutput(input, counter, keyWords, flags, isRoot) {
  const counterLo = counter >>> 0;
  const counterHi = Math.floor(counter / 2 ** 32) >>> 0;
  let cv = keyWords.slice();
  const blockCount = input.length === 0 ? 1 : Math.ceil(input.length / BLOCK_LEN);
  let last = [];
  for (let i = 0; i < blockCount; i++) {
    const block = input.subarray(i * BLOCK_LEN, Math.min((i + 1) * BLOCK_LEN, input.length));
    let blockFlags = flags;
    if (i === 0) blockFlags |= CHUNK_START;
    if (i === blockCount - 1) {
      blockFlags |= CHUNK_END;
      if (isRoot) blockFlags |= ROOT;
    }
    const padded = new Uint8Array(BLOCK_LEN);
    padded.set(block);
    last = compress(cv, bytesToWords(padded), counterLo, counterHi, block.length, blockFlags);
    cv = last.slice(0, 8);
  }
  return last;
}

/** Largest power-of-two multiple of CHUNK_LEN strictly less than `len`. */
function leftLen(len) {
  const full = Math.floor((len - 1) / CHUNK_LEN);
  let p = 1;
  while (p * 2 <= full) p *= 2;
  return p * CHUNK_LEN;
}

function subtreeCv(input, counter, keyWords, flags) {
  if (input.length <= CHUNK_LEN) {
    return chunkOutput(input, counter, keyWords, flags, false).slice(0, 8);
  }
  const split = leftLen(input.length);
  const left = subtreeCv(input.subarray(0, split), counter, keyWords, flags);
  const right = subtreeCv(input.subarray(split), counter + split / CHUNK_LEN, keyWords, flags);
  return compress(keyWords, left.concat(right), 0, 0, BLOCK_LEN, flags | PARENT).slice(0, 8);
}

function blake3Internal(input, keyWords, flags) {
  if (input.length <= CHUNK_LEN) {
    return wordsToBytes(chunkOutput(input, 0, keyWords, flags, true).slice(0, 8));
  }
  const split = leftLen(input.length);
  const left = subtreeCv(input.subarray(0, split), 0, keyWords, flags);
  const right = subtreeCv(input.subarray(split), split / CHUNK_LEN, keyWords, flags);
  const out = compress(keyWords, left.concat(right), 0, 0, BLOCK_LEN, flags | PARENT | ROOT);
  return wordsToBytes(out.slice(0, 8));
}

/** `blake3::hash(input)` — 32-byte digest. */
export function blake3(input) {
  const bytes = typeof input === "string" ? new TextEncoder().encode(input) : input;
  return blake3Internal(bytes, IV.slice(), 0);
}

/** `blake3::derive_key(context, keyMaterial)` — 32-byte output. */
export function blake3DeriveKey(context, keyMaterial) {
  const contextKey = blake3Internal(
    new TextEncoder().encode(context),
    IV.slice(),
    DERIVE_KEY_CONTEXT,
  );
  return blake3Internal(keyMaterial, bytesToWords(contextKey), DERIVE_KEY_MATERIAL);
}

export function hexToBytes(hex) {
  const clean = String(hex || "").trim().toLowerCase();
  if (clean.length % 2 !== 0 || /[^0-9a-f]/.test(clean)) return null;
  const out = new Uint8Array(clean.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(clean.slice(i * 2, i * 2 + 2), 16);
  return out;
}

export function bytesToHex(bytes) {
  return Array.from(bytes).map((b) => b.toString(16).padStart(2, "0")).join("");
}

/**
 * The CURRENT ledger-root domain, from `persist/src/lib.rs`.
 *
 * Domain separation is versioned: `canonical_ledger_root_uses_v3_domain` in
 * `persist/src/tests.rs` asserts the v3 fold and asserts it DIFFERS from v2.
 * A node built before the v3 epoch folds under v2 and its root will not match
 * this one — which is a real, observable difference, not a rounding error.
 */
export const LEDGER_ROOT_CONTEXT = "dregg-ledger-root-v3";

/**
 * Domains this checker knows how to recognise, newest first. Used ONLY to
 * explain a mismatch: if the leaves fold to the served root under an older
 * domain, the honest report is "this node predates the v3 epoch", not a bare
 * red X that leaves the reader guessing whether the node lied.
 */
export const KNOWN_LEDGER_ROOT_CONTEXTS = [
  "dregg-ledger-root-v3",
  "dregg-ledger-root-v2",
  "dregg-ledger-root-v1",
];

/**
 * Canonicalise a wire leaf set (`[[cell_id_hex, leaf_hash_hex], ...]`) into the
 * exact byte string the Rust hasher is fed.
 *
 * The Rust fold (persist/src/lib.rs `canonical_ledger_root_from_leaves`) is:
 *
 *   let mut h = blake3::Hasher::new_derive_key("dregg-ledger-root-v3");
 *   h.update(&(entries.len() as u64).to_le_bytes());
 *   for (id, leaf_hash) in entries { h.update(id); h.update(leaf_hash); }
 *   h.finalize()
 *
 * `entries` arrives sorted by cell id, and the Rust comment calls that order
 * "fixed and load-bearing" — so we re-sort here rather than trusting the order
 * the JSON happened to arrive in. That makes the check independent of the
 * server's serialization choices.
 */
function ledgerRootMaterial(leaves) {
  if (!Array.isArray(leaves)) return { ok: false, error: "leaves is not an array" };
  const parsed = [];
  for (let i = 0; i < leaves.length; i++) {
    const pair = leaves[i];
    if (!Array.isArray(pair) || pair.length !== 2) {
      return { ok: false, error: `leaf ${i} is not a [id, hash] pair` };
    }
    const id = hexToBytes(pair[0]);
    const h = hexToBytes(pair[1]);
    if (!id || id.length !== 32) return { ok: false, error: `leaf ${i}: cell id is not 32 hex bytes` };
    if (!h || h.length !== 32) return { ok: false, error: `leaf ${i}: leaf hash is not 32 hex bytes` };
    parsed.push([id, h]);
  }
  parsed.sort((a, b) => {
    for (let i = 0; i < 32; i++) {
      if (a[0][i] !== b[0][i]) return a[0][i] - b[0][i];
    }
    return 0;
  });

  const material = new Uint8Array(8 + parsed.length * 64);
  // len as u64 little-endian, via DataView so a count above 2^32 stays correct
  // rather than silently wrapping.
  new DataView(material.buffer).setBigUint64(0, BigInt(parsed.length), true);
  let off = 8;
  for (const [id, h] of parsed) {
    material.set(id, off); off += 32;
    material.set(h, off); off += 32;
  }
  return { ok: true, material, count: parsed.length };
}

/** Fold a leaf set under an explicit domain. Returns { ok, root, error }. */
export function canonicalLedgerRootWithContext(leaves, context) {
  const m = ledgerRootMaterial(leaves);
  if (!m.ok) return m;
  return { ok: true, root: bytesToHex(blake3DeriveKey(context, m.material)) };
}

/** Fold a leaf set under the CURRENT domain. Returns { ok, root, error }. */
export function canonicalLedgerRoot(leaves) {
  return canonicalLedgerRootWithContext(leaves, LEDGER_ROOT_CONTEXT);
}

/**
 * Fold under the current domain and, ONLY if that misses the served root, look
 * for an older domain that hits it.
 *
 * Returns { ok, root, matched, matchedContext, staleDomain, error } where
 * `matchedContext` names whichever domain reproduced `servedRoot` (null if
 * none did). `staleDomain` is true when an OLDER domain matched — the node is
 * real and self-consistent but built before the current epoch. That is a very
 * different fact from "the node served a root its own leaves do not fold to",
 * and the explorer must not blur them.
 */
export function verifyLedgerRoot(leaves, servedRoot) {
  const m = ledgerRootMaterial(leaves);
  if (!m.ok) return { ok: false, error: m.error };
  const want = String(servedRoot || "").trim().toLowerCase();
  const roots = {};
  for (const ctx of KNOWN_LEDGER_ROOT_CONTEXTS) {
    roots[ctx] = bytesToHex(blake3DeriveKey(ctx, m.material));
  }
  const current = roots[LEDGER_ROOT_CONTEXT];
  let matchedContext = null;
  for (const ctx of KNOWN_LEDGER_ROOT_CONTEXTS) {
    if (roots[ctx] === want) { matchedContext = ctx; break; }
  }
  return {
    ok: true,
    root: current,
    roots,
    matched: matchedContext === LEDGER_ROOT_CONTEXT,
    matchedContext,
    staleDomain: matchedContext !== null && matchedContext !== LEDGER_ROOT_CONTEXT,
    count: m.count,
  };
}

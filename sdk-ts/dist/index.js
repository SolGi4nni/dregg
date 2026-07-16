"use strict";
var __create = Object.create;
var __defProp = Object.defineProperty;
var __getOwnPropDesc = Object.getOwnPropertyDescriptor;
var __getOwnPropNames = Object.getOwnPropertyNames;
var __getProtoOf = Object.getPrototypeOf;
var __hasOwnProp = Object.prototype.hasOwnProperty;
var __export = (target, all) => {
  for (var name in all)
    __defProp(target, name, { get: all[name], enumerable: true });
};
var __copyProps = (to, from, except, desc) => {
  if (from && typeof from === "object" || typeof from === "function") {
    for (let key of __getOwnPropNames(from))
      if (!__hasOwnProp.call(to, key) && key !== except)
        __defProp(to, key, { get: () => from[key], enumerable: !(desc = __getOwnPropDesc(from, key)) || desc.enumerable });
  }
  return to;
};
var __toESM = (mod, isNodeMode, target) => (target = mod != null ? __create(__getProtoOf(mod)) : {}, __copyProps(
  // If the importer is in node compatibility mode or this is not an ESM
  // file that has been converted to a CommonJS file using a Babel-
  // compatible transform (i.e. "__esModule" has not been set), then set
  // "default" to the CommonJS "module.exports" for node compatibility.
  isNodeMode || !mod || !mod.__esModule ? __defProp(target, "default", { value: mod, enumerable: true }) : target,
  mod
));
var __toCommonJS = (mod) => __copyProps(__defProp({}, "__esModule", { value: true }), mod);

// src/index.ts
var index_exports = {};
__export(index_exports, {
  AgentRuntime: () => AgentRuntime,
  AttestedQuery: () => AttestedQuery,
  AuthorizedTurn: () => AuthorizedTurn,
  ChannelsClient: () => ChannelsClient,
  DEFAULT_DOMAINS: () => DEFAULT_DOMAINS,
  DEFAULT_LEASE_METHOD: () => DEFAULT_LEASE_METHOD,
  DREGG_ENDPOINTS: () => DREGG_ENDPOINTS,
  DeployChecker: () => DeployChecker,
  DreggPgError: () => DreggPgError,
  EmptyTurnError: () => EmptyTurnError,
  Identity: () => Identity,
  KERNEL_ROLE: () => KERNEL_ROLE,
  LEASE_STEP_SLOT: () => LEASE_STEP_SLOT,
  Lease: () => Lease,
  MAIN_IDENTITY_PATH: () => MAIN_IDENTITY_PATH,
  MailboxClient: () => MailboxClient,
  NodeClient: () => NodeClient,
  NodeError: () => NodeError,
  NodeEvents: () => NodeEvents,
  PAY_METHOD: () => PAY_METHOD,
  PROFILE_ENV: () => PROFILE_ENV,
  Pg: () => Pg,
  ProfileError: () => ProfileError,
  READER_ROLE: () => READER_ROLE,
  Receipt: () => Receipt,
  ReceiptFilter: () => ReceiptFilter,
  ReceiptStream: () => ReceiptStream,
  RelayError: () => RelayError,
  ServiceEconomy: () => ServiceEconomy,
  TOKEN_GUC: () => TOKEN_GUC,
  TrustlineClient: () => TrustlineClient,
  TurnBuilder: () => TurnBuilder,
  TurnProof: () => TurnProof,
  WrongTurnProofError: () => WrongTurnProofError,
  apiUrl: () => apiUrl,
  base64Decode: () => base64Decode,
  base64Encode: () => base64Encode,
  createSseParser: () => createSseParser,
  devnetUrl: () => devnetUrl,
  devnetWssUrl: () => devnetWssUrl,
  explainAction: () => explainAction,
  explainEffect: () => explainEffect,
  explainTurn: () => explainTurn,
  fieldFromU64: () => fieldFromU64,
  gatewayUrl: () => gatewayUrl,
  hexDecode: () => hexDecode,
  hexEncode: () => hexEncode,
  leaseProgramConstraints: () => leaseProgramConstraints,
  portalUrl: () => portalUrl,
  profiles: () => profiles_exports,
  program: () => program_exports,
  renderTurn: () => renderTurn,
  resolveDomains: () => resolveDomains,
  symbol: () => symbol
});
module.exports = __toCommonJS(index_exports);

// src/internal/blake3.ts
var IV = [
  1779033703,
  3144134277,
  1013904242,
  2773480762,
  1359893119,
  2600822924,
  528734635,
  1541459225
];
var MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];
var CHUNK_LEN = 1024;
var BLOCK_LEN = 64;
var CHUNK_START = 1 << 0;
var CHUNK_END = 1 << 1;
var PARENT = 1 << 2;
var ROOT = 1 << 3;
var DERIVE_KEY_CONTEXT = 1 << 5;
var DERIVE_KEY_MATERIAL = 1 << 6;
var rotr = (x, n) => (x >>> n | x << 32 - n) >>> 0;
function g(s, a, b, c, d, mx, my) {
  s[a] = s[a] + s[b] + mx >>> 0;
  s[d] = rotr(s[d] ^ s[a], 16);
  s[c] = s[c] + s[d] >>> 0;
  s[b] = rotr(s[b] ^ s[c], 12);
  s[a] = s[a] + s[b] + my >>> 0;
  s[d] = rotr(s[d] ^ s[a], 8);
  s[c] = s[c] + s[d] >>> 0;
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
    cv[0],
    cv[1],
    cv[2],
    cv[3],
    cv[4],
    cv[5],
    cv[6],
    cv[7],
    IV[0],
    IV[1],
    IV[2],
    IV[3],
    counterLo >>> 0,
    counterHi >>> 0,
    blockLen >>> 0,
    flags >>> 0
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
var readLE32 = (bytes, off) => (bytes[off] | bytes[off + 1] << 8 | bytes[off + 2] << 16 | bytes[off + 3] << 24) >>> 0;
function wordsToBytes(words) {
  const out = new Uint8Array(words.length * 4);
  words.forEach((w, i) => {
    out[i * 4] = w & 255;
    out[i * 4 + 1] = w >>> 8 & 255;
    out[i * 4 + 2] = w >>> 16 & 255;
    out[i * 4 + 3] = w >>> 24 & 255;
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
function leftLen(len) {
  let full = Math.floor((len - 1) / CHUNK_LEN);
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
function blake3(input) {
  const bytes = typeof input === "string" ? new TextEncoder().encode(input) : input;
  return blake3Internal(bytes, IV.slice(), 0);
}
function blake3DeriveKey(context, keyMaterial) {
  const contextKey = blake3Internal(
    new TextEncoder().encode(context),
    IV.slice(),
    DERIVE_KEY_CONTEXT
  );
  return blake3Internal(keyMaterial, bytesToWords(contextKey), DERIVE_KEY_MATERIAL);
}
var Blake3Hasher = class _Blake3Hasher {
  constructor(context = null) {
    this.parts = [];
    this.context = context;
  }
  static new() {
    return new _Blake3Hasher(null);
  }
  /** `blake3::Hasher::new_derive_key(context)`. */
  static newDeriveKey(context) {
    return new _Blake3Hasher(context);
  }
  update(bytes) {
    this.parts.push(typeof bytes === "string" ? new TextEncoder().encode(bytes) : bytes);
    return this;
  }
  finalize() {
    let total = 0;
    for (const p of this.parts) total += p.length;
    const all = new Uint8Array(total);
    let off = 0;
    for (const p of this.parts) {
      all.set(p, off);
      off += p.length;
    }
    return this.context === null ? blake3(all) : blake3DeriveKey(this.context, all);
  }
};

// src/internal/ed25519.ts
var ed = __toESM(require("@noble/ed25519"));
var import_sha512 = require("@noble/hashes/sha512");
if (!ed.etc.sha512Sync) {
  ed.etc.sha512Sync = (...messages) => (0, import_sha512.sha512)(ed.etc.concatBytes(...messages));
}
function ed25519PublicKey(seed32) {
  if (seed32.length !== 32) throw new Error("ed25519 seed must be 32 bytes");
  return ed.getPublicKey(seed32);
}
function ed25519Sign(seed32, message) {
  if (seed32.length !== 32) throw new Error("ed25519 seed must be 32 bytes");
  return ed.sign(message, seed32);
}

// src/internal/bytes.ts
function hexEncode(bytes) {
  let out = "";
  for (const b of bytes) out += b.toString(16).padStart(2, "0");
  return out;
}
function hexDecode(hex) {
  const clean = hex.startsWith("0x") ? hex.slice(2) : hex;
  if (clean.length % 2 !== 0 || /[^0-9a-fA-F]/.test(clean)) {
    throw new Error(`invalid hex string (len ${clean.length})`);
  }
  const out = new Uint8Array(clean.length / 2);
  for (let i = 0; i < out.length; i++) {
    out[i] = parseInt(clean.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}
function hexDecodeExact(hex, len) {
  const b = hexDecode(hex);
  if (b.length !== len) throw new Error(`expected ${len} bytes, got ${b.length}`);
  return b;
}
function concatBytes(...parts) {
  let total = 0;
  for (const p of parts) total += p.length;
  const out = new Uint8Array(total);
  let off = 0;
  for (const p of parts) {
    out.set(p, off);
    off += p.length;
  }
  return out;
}
function u64le(v) {
  const out = new Uint8Array(8);
  let n = BigInt(v);
  if (n < 0n) throw new Error("u64le: negative");
  for (let i = 0; i < 8; i++) {
    out[i] = Number(n & 0xffn);
    n >>= 8n;
  }
  return out;
}
function i64le(v) {
  let n = BigInt(v);
  if (n < 0n) n += 1n << 64n;
  return u64le(n);
}
function u32le(v) {
  const out = new Uint8Array(4);
  out[0] = v & 255;
  out[1] = v >>> 8 & 255;
  out[2] = v >>> 16 & 255;
  out[3] = v >>> 24 & 255;
  return out;
}
function bytesEqual(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}
function exactBytes(v, len, what) {
  if (!(v instanceof Uint8Array) || v.length !== len) {
    throw new Error(`${what} must be exactly ${len} bytes`);
  }
  return Uint8Array.from(v);
}
var utf8 = {
  encode: (s) => new TextEncoder().encode(s)
};

// src/internal/wire.ts
function symbol(name) {
  return blake3(utf8.encode(name));
}
function defaultTokenId() {
  return blake3(utf8.encode("default"));
}
function deriveCellId(publicKey, tokenId = defaultTokenId()) {
  return blake3DeriveKey(
    "dregg-cell-id-v1",
    concatBytes(exactBytes(publicKey, 32, "publicKey"), exactBytes(tokenId, 32, "tokenId"))
  );
}
function fieldFromU64(v) {
  const out = new Uint8Array(32);
  let n = BigInt(v);
  if (n < 0n || n >= 1n << 64n) throw new Error("fieldFromU64: out of u64 range");
  for (let i = 31; i >= 24; i--) {
    out[i] = Number(n & 0xffn);
    n >>= 8n;
  }
  return out;
}
function unsignedAction(target, method, effects) {
  return {
    target: exactBytes(target, 32, "target"),
    method: exactBytes(method, 32, "method"),
    args: [],
    authorization: { kind: "unchecked" },
    effects
  };
}
function unsignedActionNamed(target, method, effects) {
  return unsignedAction(target, symbol(method), effects);
}
var Writer = class {
  constructor() {
    this.parts = [];
  }
  u8(v) {
    this.parts.push(v & 255);
    return this;
  }
  bytes(b) {
    for (const x of b) this.parts.push(x);
    return this;
  }
  /** Unsigned LEB128 varint (postcard's u16/u32/u64/usize encoding). */
  varint(v) {
    let n = BigInt(v);
    if (n < 0n) throw new Error("varint: negative");
    do {
      let byte = Number(n & 0x7fn);
      n >>= 7n;
      if (n !== 0n) byte |= 128;
      this.parts.push(byte);
    } while (n !== 0n);
    return this;
  }
  /** Zigzag varint (postcard's i64 encoding). */
  ivarint(v) {
    const n = BigInt(v);
    return this.varint(n >= 0n ? n << 1n : (-n << 1n) - 1n);
  }
  /** Option discriminant + value. */
  option(v, write) {
    if (v === void 0 || v === null) {
      this.u8(0);
    } else {
      this.u8(1);
      write(v);
    }
    return this;
  }
  /** Length-prefixed sequence. */
  seq(items, write) {
    this.varint(items.length);
    for (const it of items) write(it);
    return this;
  }
  /** Length-prefixed byte string (postcard `Vec<u8>` / serde_bytes). */
  byteSeq(b) {
    this.varint(b.length);
    return this.bytes(b);
  }
  out() {
    return Uint8Array.from(this.parts);
  }
};
function writeAuthRequired(w, a) {
  switch (a.kind) {
    case "none":
      w.varint(0);
      break;
    case "signature":
      w.varint(1);
      break;
    case "proof":
      w.varint(2);
      break;
    case "either":
      w.varint(3);
      break;
    case "impossible":
      w.varint(4);
      break;
    case "custom":
      w.varint(5).bytes(exactBytes(a.vkHash, 32, "vkHash"));
      break;
  }
}
function writeCapabilityRef(w, cap) {
  w.bytes(exactBytes(cap.target, 32, "cap.target"));
  w.varint(cap.slot);
  writeAuthRequired(w, cap.permissions);
  w.option(cap.breadstuff, (b) => w.bytes(exactBytes(b, 32, "cap.breadstuff")));
  w.option(cap.expiresAt, (e) => w.varint(e));
  w.u8(0);
  w.option(cap.storedEpoch, (e) => w.varint(e));
  w.bytes(exactBytes(cap.provenance ?? new Uint8Array(32), 32, "cap.provenance"));
}
function writeEffect(w, e) {
  switch (e.kind) {
    case "setField":
      w.varint(0).bytes(exactBytes(e.cell, 32, "cell")).varint(e.index).bytes(exactBytes(e.value, 32, "value"));
      break;
    case "transfer":
      w.varint(1).bytes(exactBytes(e.from, 32, "from")).bytes(exactBytes(e.to, 32, "to")).varint(e.amount);
      break;
    case "grantCapability":
      w.varint(2).bytes(exactBytes(e.from, 32, "from")).bytes(exactBytes(e.to, 32, "to"));
      writeCapabilityRef(w, e.cap);
      break;
    case "revokeCapability":
      w.varint(3).bytes(exactBytes(e.cell, 32, "cell")).varint(e.slot);
      break;
    case "emitEvent":
      w.varint(4).bytes(exactBytes(e.cell, 32, "cell")).bytes(exactBytes(e.topic, 32, "topic"));
      w.seq(e.data, (d) => w.bytes(exactBytes(d, 32, "event data word")));
      break;
    case "incrementNonce":
      w.varint(5).bytes(exactBytes(e.cell, 32, "cell"));
      break;
    case "createCell":
      w.varint(6).bytes(exactBytes(e.publicKey, 32, "publicKey")).bytes(exactBytes(e.tokenId, 32, "tokenId")).varint(e.balance);
      break;
  }
}
function writeAuthorization(w, a) {
  switch (a.kind) {
    case "signature":
      w.varint(0).bytes(exactBytes(a.r, 32, "sig r")).bytes(exactBytes(a.s, 32, "sig s"));
      break;
    case "unchecked":
      w.varint(4);
      break;
  }
}
var PRECONDITIONS_DEFAULT = Uint8Array.from([0, 0, 0, 0]);
function writeAction(w, a) {
  w.bytes(exactBytes(a.target, 32, "target"));
  w.bytes(exactBytes(a.method, 32, "method"));
  w.seq(a.args, (arg) => w.bytes(exactBytes(arg, 32, "arg")));
  writeAuthorization(w, a.authorization);
  w.bytes(PRECONDITIONS_DEFAULT);
  w.seq(a.effects, (e) => writeEffect(w, e));
  w.varint(0);
  w.varint(0);
  w.option(a.balanceChange, (d) => w.ivarint(d));
  w.varint(0);
}
function writeCallTree(w, t) {
  writeAction(w, t.action);
  w.seq(t.children, (c) => writeCallTree(w, c));
  w.bytes(new Uint8Array(32));
}
function encodeTurn(t) {
  const w = new Writer();
  w.bytes(exactBytes(t.agent, 32, "agent"));
  w.varint(t.nonce);
  w.seq(t.roots, (r) => writeCallTree(w, r));
  w.bytes(new Uint8Array(32));
  w.varint(t.fee);
  w.option(t.memo, (m) => w.byteSeq(utf8.encode(m)));
  w.option(t.validUntil, (v) => w.ivarint(v));
  w.option(t.previousReceiptHash, (h) => w.bytes(exactBytes(h, 32, "previousReceiptHash")));
  w.seq(t.dependsOn ?? [], (d) => w.bytes(exactBytes(d, 32, "dependsOn")));
  w.u8(0);
  w.varint(0);
  w.u8(0);
  w.u8(0);
  w.u8(0);
  w.u8(0);
  w.varint(0);
  w.varint(0);
  w.varint(0);
  return w.out();
}
function encodeSignedTurn(turn, signature, signer) {
  const w = new Writer();
  w.bytes(encodeTurn(turn));
  w.byteSeq(exactBytes(signature, 64, "signature"));
  w.byteSeq(exactBytes(signer, 32, "signer"));
  return w.out();
}
function effectHash(e) {
  const h = Blake3Hasher.new();
  switch (e.kind) {
    case "setField":
      h.update(Uint8Array.from([0])).update(e.cell).update(u64le(e.index)).update(e.value);
      break;
    case "transfer":
      h.update(Uint8Array.from([1])).update(e.from).update(e.to).update(u64le(e.amount));
      break;
    case "grantCapability":
      h.update(Uint8Array.from([2])).update(e.from).update(e.to).update(e.cap.target).update(u32le(e.cap.slot));
      break;
    case "revokeCapability":
      h.update(Uint8Array.from([3])).update(e.cell).update(u32le(e.slot));
      break;
    case "emitEvent":
      h.update(Uint8Array.from([4])).update(e.cell).update(e.topic);
      for (const d of e.data) h.update(d);
      break;
    case "incrementNonce":
      h.update(Uint8Array.from([5])).update(e.cell);
      break;
    case "createCell":
      h.update(Uint8Array.from([6])).update(e.publicKey).update(e.tokenId).update(u64le(e.balance));
      break;
  }
  return h.finalize();
}
function authHashUpdate(h, a) {
  switch (a.kind) {
    case "signature":
      h.update(Uint8Array.from([0])).update(a.r).update(a.s);
      break;
    case "unchecked":
      h.update(Uint8Array.from([3]));
      break;
  }
}
function actionHash(a) {
  const h = Blake3Hasher.new();
  h.update(utf8.encode("dregg-action-v2:"));
  h.update(a.target);
  h.update(a.method);
  for (const arg of a.args) h.update(arg);
  authHashUpdate(h, a.authorization);
  h.update(Uint8Array.from([0]));
  h.update(Uint8Array.from([0]));
  if (a.balanceChange !== void 0) {
    h.update(Uint8Array.from([1])).update(i64le(a.balanceChange));
  } else {
    h.update(Uint8Array.from([0]));
  }
  for (const e of a.effects) h.update(effectHash(e));
  h.update(PRECONDITIONS_DEFAULT);
  h.update(u64le(0));
  return h.finalize();
}
function actionSigningMessage(a, federationId) {
  const h = Blake3Hasher.new();
  h.update(utf8.encode("dregg-action-sig-v2:"));
  h.update(exactBytes(federationId, 32, "federationId"));
  h.update(a.target);
  h.update(a.method);
  for (const arg of a.args) h.update(arg);
  for (const e of a.effects) h.update(effectHash(e));
  h.update(Uint8Array.from([0]));
  h.update(Uint8Array.from([0]));
  if (a.balanceChange !== void 0) {
    h.update(Uint8Array.from([1])).update(i64le(a.balanceChange));
  } else {
    h.update(Uint8Array.from([0]));
  }
  h.update(PRECONDITIONS_DEFAULT);
  return h.finalize();
}
function treeHash(t) {
  const a = actionHash(t.action);
  let children;
  if (t.children.length === 0) {
    children = new Uint8Array(32);
  } else {
    const h = Blake3Hasher.new();
    for (const c of t.children) h.update(treeHash(c));
    children = h.finalize();
  }
  return Blake3Hasher.new().update(a).update(children).finalize();
}
function forestHash(roots) {
  if (roots.length === 0) return new Uint8Array(32);
  const h = Blake3Hasher.new();
  for (const r of roots) h.update(treeHash(r));
  return h.finalize();
}
function turnHash(t) {
  const h = Blake3Hasher.new();
  h.update(utf8.encode("dregg-turn-v3:"));
  h.update(t.agent);
  h.update(u64le(t.nonce));
  h.update(forestHash(t.roots));
  h.update(u64le(t.fee));
  if (t.memo !== void 0) {
    const m = utf8.encode(t.memo);
    h.update(Uint8Array.from([1])).update(u64le(m.length)).update(m);
  } else {
    h.update(Uint8Array.from([0]));
  }
  if (t.validUntil !== void 0) {
    h.update(Uint8Array.from([1])).update(i64le(t.validUntil));
  } else {
    h.update(Uint8Array.from([0]));
  }
  const deps = t.dependsOn ?? [];
  h.update(u64le(deps.length));
  for (const d of deps) h.update(d);
  if (t.previousReceiptHash !== void 0) {
    h.update(Uint8Array.from([1])).update(t.previousReceiptHash);
  } else {
    h.update(Uint8Array.from([0]));
  }
  h.update(Uint8Array.from([0]));
  h.update(Uint8Array.from([0]));
  h.update(Uint8Array.from([0]));
  h.update(u64le(0));
  h.update(Uint8Array.from([0]));
  return h.finalize();
}

// src/identity.ts
var MAIN_IDENTITY_PATH = "dregg/0";
var Identity = class _Identity {
  constructor(seed32) {
    this.seed = exactBytes(seed32, 32, "ed25519 seed");
    this.publicKey = ed25519PublicKey(this.seed);
  }
  /**
   * Derive the main identity from a 64-byte master seed at path `dregg/0`
   * (the profile-store derivation — mirrors `AgentCipherclerk::from_seed`).
   */
  static fromSeed(seed64, path = MAIN_IDENTITY_PATH) {
    exactBytes(seed64, 64, "master seed");
    return new _Identity(blake3DeriveKey(path, seed64));
  }
  /** Wrap a raw 32-byte Ed25519 seed directly (no path derivation). */
  static fromKeyBytes(seed32) {
    return new _Identity(seed32);
  }
  /** A fresh random identity (OS randomness). */
  static generate() {
    const seed = new Uint8Array(64);
    globalThis.crypto.getRandomValues(seed);
    return _Identity.fromSeed(seed);
  }
  /** Hex Ed25519 public key (the profile store's `public_key_hex`). */
  get publicKeyHex() {
    return hexEncode(this.publicKey);
  }
  /**
   * This identity's default agent cell:
   * `CellId::derive_raw(publicKey, blake3("default"))` — the cell the node
   * requires as `turn.agent` for envelope-signed submissions.
   */
  cellId() {
    return deriveCellId(this.publicKey);
  }
  /** Hex form of [`cellId`]. */
  cellIdHex() {
    return hexEncode(this.cellId());
  }
  /** Sign arbitrary bytes (Ed25519, deterministic). */
  signBytes(message) {
    return ed25519Sign(this.seed, message);
  }
  /**
   * Sign an action over the canonical federation-bound signing message
   * (`dregg-action-sig-v2`), replacing its authorization with a real
   * `Signature` — the ONLY way an action leaves the authorized flow.
   */
  signAction(action, federationId) {
    const message = actionSigningMessage(action, federationId);
    const sig = this.signBytes(message);
    return {
      ...action,
      authorization: { kind: "signature", r: sig.slice(0, 32), s: sig.slice(32, 64) }
    };
  }
  /**
   * Sign a turn's canonical `Turn::hash` (v3) and wrap it in the postcard
   * `SignedTurn` envelope the node's `/api/turns/submit-signed` ingress
   * verifies (signature over the hash; `turn.agent` must be this identity's
   * default cell).
   */
  signTurnEnvelope(turn) {
    const hash = turnHash(turn);
    const sig = this.signBytes(hash);
    return encodeSignedTurn(turn, sig, this.publicKey);
  }
};

// src/profiles.ts
var profiles_exports = {};
__export(profiles_exports, {
  PROFILE_ENV: () => PROFILE_ENV,
  ProfileError: () => ProfileError,
  activeName: () => activeName,
  create: () => create,
  list: () => list,
  load: () => load,
  loadActive: () => loadActive,
  profilesDir: () => profilesDir,
  setActive: () => setActive
});
var import_node_fs = require("fs");
var import_node_crypto = require("crypto");
var import_node_path = require("path");
var PROFILE_ENV = "DREGG_PROFILE";
var ProfileError = class extends Error {
  constructor(code, message) {
    super(message);
    this.name = "ProfileError";
    this.code = code;
  }
};
function profilesDir() {
  const home = process.env.DREGG_HOME;
  if (home) return (0, import_node_path.join)(home, "profiles");
  const base = process.env.HOME ?? ".";
  return (0, import_node_path.join)(base, ".dregg", "profiles");
}
function validName(name) {
  return /^[a-z0-9_-]{1,64}$/.test(name);
}
function profilePath(name) {
  return (0, import_node_path.join)(profilesDir(), `${name}.json`);
}
function activePath() {
  return (0, import_node_path.join)(profilesDir(), "ACTIVE");
}
function writePrivate(path, contents) {
  (0, import_node_fs.mkdirSync)(profilesDir(), { recursive: true });
  (0, import_node_fs.writeFileSync)(path, contents, { mode: 384 });
  (0, import_node_fs.chmodSync)(path, 384);
}
function readProfile(name) {
  const path = profilePath(name);
  if (!(0, import_node_fs.existsSync)(path)) {
    throw new ProfileError("not_found", `profile ${JSON.stringify(name)} not found`);
  }
  let parsed;
  try {
    parsed = JSON.parse((0, import_node_fs.readFileSync)(path, "utf8"));
  } catch (e) {
    throw new ProfileError("malformed", `profile file for ${JSON.stringify(name)} is malformed: ${e.message}`);
  }
  const p = parsed;
  if (typeof p !== "object" || p === null || p.version !== 1 || typeof p.name !== "string" || typeof p.seed_hex !== "string" || typeof p.public_key_hex !== "string") {
    throw new ProfileError("malformed", `profile file for ${JSON.stringify(name)} is malformed: missing/invalid fields`);
  }
  return {
    version: 1,
    name: p.name,
    seed_hex: p.seed_hex,
    public_key_hex: p.public_key_hex,
    created_at: typeof p.created_at === "number" ? p.created_at : 0
  };
}
function create(name) {
  if (!validName(name)) {
    throw new ProfileError("invalid_name", `invalid profile name ${JSON.stringify(name)}: use 1-64 chars of [a-z0-9-_]`);
  }
  const path = profilePath(name);
  if ((0, import_node_fs.existsSync)(path)) {
    throw new ProfileError("already_exists", `profile ${JSON.stringify(name)} already exists`);
  }
  const seed = new Uint8Array((0, import_node_crypto.randomBytes)(64));
  const identity = Identity.fromSeed(seed);
  const createdAt = Math.floor(Date.now() / 1e3);
  const record = {
    version: 1,
    name,
    seed_hex: hexEncode(seed),
    public_key_hex: identity.publicKeyHex,
    created_at: createdAt
  };
  writePrivate(path, JSON.stringify(record, null, 2));
  return {
    name,
    publicKeyHex: identity.publicKeyHex,
    createdAt,
    active: activeName() === name
  };
}
function list() {
  const dir = profilesDir();
  const active = activeName();
  let entries;
  try {
    entries = (0, import_node_fs.readdirSync)(dir);
  } catch (e) {
    if (e.code === "ENOENT") return [];
    throw new ProfileError("io", `profile store io error: ${e.message}`);
  }
  const out = [];
  for (const entry of entries) {
    if (!entry.endsWith(".json")) continue;
    const name = entry.slice(0, -".json".length);
    try {
      const p = readProfile(name);
      out.push({
        name: p.name,
        publicKeyHex: p.public_key_hex,
        createdAt: p.created_at,
        active: active === name
      });
    } catch (e) {
      if (e instanceof ProfileError && e.code === "malformed") {
        out.push({ name, publicKeyHex: `<malformed: ${e.message}>`, createdAt: 0, active: false });
        continue;
      }
      throw e;
    }
  }
  out.sort((a, b) => a.name < b.name ? -1 : a.name > b.name ? 1 : 0);
  return out;
}
function setActive(name) {
  if (!validName(name)) {
    throw new ProfileError("invalid_name", `invalid profile name ${JSON.stringify(name)}: use 1-64 chars of [a-z0-9-_]`);
  }
  if (!(0, import_node_fs.existsSync)(profilePath(name))) {
    throw new ProfileError("not_found", `profile ${JSON.stringify(name)} not found`);
  }
  writePrivate(activePath(), name);
}
function activeName() {
  const env = process.env[PROFILE_ENV]?.trim();
  if (env) return env;
  try {
    const contents = (0, import_node_fs.readFileSync)(activePath(), "utf8").trim();
    return contents.length > 0 ? contents : void 0;
  } catch {
    return void 0;
  }
}
function load(name) {
  const record = readProfile(name);
  let seed;
  try {
    seed = hexDecodeExact(record.seed_hex, 64);
  } catch (e) {
    throw new ProfileError("malformed", `profile file for ${JSON.stringify(name)} is malformed: seed_hex: ${e.message}`);
  }
  return Identity.fromSeed(seed);
}
function loadActive() {
  const name = activeName();
  return name === void 0 ? void 0 : load(name);
}

// src/endpoints.ts
var DEFAULT_DOMAINS = Object.freeze({
  api: "dregg.fg-goose.online",
  devnet: "devnet.dregg.fg-goose.online",
  auth: "auth.dregg.fg-goose.online",
  gateway: "gateway.dregg.fg-goose.online",
  hosting: "dregg.works",
  portal: "portal.dregg.studio"
});
var ENV_VARS = {
  api: "DREGG_API_DOMAIN",
  devnet: "DREGG_DEVNET_DOMAIN",
  auth: "DREGG_AUTH_DOMAIN",
  gateway: "DREGG_GATEWAY_DOMAIN",
  hosting: "DREGG_HOSTING_DOMAIN",
  portal: "DREGG_PORTAL_DOMAIN"
};
function envOverride(field) {
  const env = globalThis.process?.env;
  const v = env?.[ENV_VARS[field]];
  return v && v.trim() ? v.trim() : void 0;
}
function browserOverride(field) {
  const o = globalThis.__DREGG_ENDPOINTS__;
  const v = o?.[field];
  return v && v.trim() ? v.trim() : void 0;
}
function resolveDomains() {
  const out = {};
  for (const key of Object.keys(DEFAULT_DOMAINS)) {
    out[key] = browserOverride(key) ?? envOverride(key) ?? DEFAULT_DOMAINS[key];
  }
  return out;
}
function devnetUrl(domains = resolveDomains()) {
  return `https://${domains.devnet}`;
}
function devnetWssUrl(domains = resolveDomains()) {
  return `wss://${domains.devnet}/ws`;
}
function apiUrl(domains = resolveDomains()) {
  return `https://${domains.api}`;
}
function gatewayUrl(domains = resolveDomains()) {
  return `https://${domains.gateway}`;
}
function portalUrl(domains = resolveDomains()) {
  return `https://${domains.portal}`;
}
var DREGG_ENDPOINTS = Object.freeze({
  /** Default node URL (e.g. `https://devnet.dregg.fg-goose.online`). */
  defaultNodeUrl: devnetUrl(),
  /** Default node WSS URL (e.g. `wss://devnet.dregg.fg-goose.online/ws`). */
  defaultNodeWssUrl: devnetWssUrl()
});

// src/receipt.ts
var TurnProof = class {
  constructor(turnHash2, bytes) {
    if (turnHash2.length !== 32) throw new Error("TurnProof: turnHash must be 32 bytes");
    this.turnHash = Uint8Array.from(turnHash2);
    this.bytes = bytes;
  }
  get turnHashHex() {
    return hexEncode(this.turnHash);
  }
};
var WrongTurnProofError = class extends Error {
  constructor(expectedHex, gotHex) {
    super(`proof is bound to turn ${gotHex}, receipt is turn ${expectedHex}`);
    this.name = "WrongTurnProofError";
  }
};
var num32ToHex = (a) => Array.isArray(a) ? hexEncode(Uint8Array.from(a)) : void 0;
var Receipt = class _Receipt {
  constructor(fields) {
    this.turnHash = fields.turnHash.toLowerCase();
    this.receiptHash = fields.receiptHash?.toLowerCase();
    this.agent = fields.agent?.toLowerCase();
    this.preStateHash = fields.preStateHash;
    this.postStateHash = fields.postStateHash;
    this.timestamp = fields.timestamp;
    this.computronsUsed = fields.computronsUsed;
    this.actionCount = fields.actionCount;
    this.previousReceiptHash = fields.previousReceiptHash;
    this.finality = fields.finality;
    this.wasEncrypted = fields.wasEncrypted;
    this.wasBurn = fields.wasBurn;
    this.chainIndex = fields.chainIndex;
    this.hasProofHint = fields.hasProofHint;
    this.raw = fields.raw;
  }
  /** Build from the canonical wire receipt (the SSE `receipt` field). */
  static fromTurnReceipt(r, extra) {
    return new _Receipt({
      turnHash: num32ToHex(r.turn_hash) ?? "",
      agent: num32ToHex(r.agent),
      preStateHash: num32ToHex(r.pre_state_hash),
      postStateHash: num32ToHex(r.post_state_hash),
      timestamp: r.timestamp,
      computronsUsed: r.computrons_used,
      actionCount: r.action_count,
      previousReceiptHash: num32ToHex(r.previous_receipt_hash) ?? void 0,
      finality: typeof r.finality === "string" ? r.finality.toLowerCase() : void 0,
      wasEncrypted: r.was_encrypted,
      wasBurn: r.was_burn,
      raw: r,
      ...extra
    });
  }
  /** The attached proof, if one has been attached (receipts are born proofless). */
  proof() {
    return this.attached;
  }
  /** Whether a proof has been attached. */
  hasProof() {
    return this.attached !== void 0;
  }
  /**
   * Attach the composed turn proof. Idempotent-at-first-writer: returns
   * `false` if one was already attached (a receipt never silently swaps
   * attestations) and throws [`WrongTurnProofError`] if the proof names a
   * different turn (a mis-bound attachment is refused, not stored).
   */
  attachProof(proof) {
    const expected = hexDecodeExact(this.turnHash, 32);
    if (!bytesEqual(proof.turnHash, expected)) {
      throw new WrongTurnProofError(this.turnHash, proof.turnHashHex);
    }
    if (this.attached !== void 0) return false;
    this.attached = proof;
    return true;
  }
  /**
   * Lazily attach: return the attached proof, producing it with `f` if none
   * is attached yet (mirrors `Receipt::proof_or_attach`). A produced proof
   * bound to the wrong turn is refused, never stored.
   */
  async proofOrAttach(f) {
    if (this.attached === void 0) {
      const produced = await f();
      this.attachProof(produced);
    }
    const got = this.attached;
    if (got === void 0) throw new Error("unreachable: attached above");
    return got;
  }
};

// src/events.ts
var ReceiptFilter = class {
  /**
   * Only receipts touching `cell` (the agent cell, an event-emitting cell,
   * or the commit record's cell).
   */
  cell(cell) {
    this.cellHexValue = hexEncode(cell);
    return this;
  }
  /** [`cell`] with a raw hex id (e.g. straight from an explorer URL). */
  cellHex(cell) {
    this.cellHexValue = cell;
    return this;
  }
  /**
   * Only receipts whose commit record names this effect kind
   * (e.g. `set_field`, `transfer`, `turn_committed`).
   */
  kind(kind) {
    this.kindValue = kind;
    return this;
  }
  query() {
    const q = new URLSearchParams();
    if (this.cellHexValue) q.set("cell", this.cellHexValue);
    if (this.kindValue) q.set("kind", this.kindValue);
    const s = q.toString();
    return s.length > 0 ? `?${s}` : "";
  }
};
function createSseParser() {
  let buffer = "";
  let eventType = "";
  let dataLines = [];
  let id = null;
  function dispatch(out) {
    if (dataLines.length === 0) {
      eventType = "";
      return;
    }
    out.push({ event: eventType || "message", data: dataLines.join("\n"), id });
    eventType = "";
    dataLines = [];
  }
  function processLine(line, out) {
    if (line === "") {
      dispatch(out);
      return;
    }
    if (line.startsWith(":")) return;
    const colon = line.indexOf(":");
    const field = colon === -1 ? line : line.slice(0, colon);
    let value = colon === -1 ? "" : line.slice(colon + 1);
    if (value.startsWith(" ")) value = value.slice(1);
    switch (field) {
      case "event":
        eventType = value;
        break;
      case "data":
        dataLines.push(value);
        break;
      case "id":
        if (!value.includes("\0")) id = value;
        break;
      default:
        break;
    }
  }
  return {
    feed(chunk) {
      buffer += chunk;
      const out = [];
      let start = 0;
      for (let i = 0; i < buffer.length; i++) {
        const c = buffer[i];
        if (c === "\n" || c === "\r") {
          processLine(buffer.slice(start, i), out);
          if (c === "\r" && buffer[i + 1] === "\n") i++;
          start = i + 1;
        }
      }
      buffer = buffer.slice(start);
      return out;
    }
  };
}
var ReceiptStream = class {
  constructor(url, headers, initialBackoffMs) {
    this.url = url;
    this.headers = headers;
    this.queue = [];
    this.closed = false;
    this.abort = new AbortController();
    void this.run(initialBackoffMs);
  }
  push(r) {
    const w = this.waiter;
    if (w) {
      this.waiter = void 0;
      w(r);
    } else {
      this.queue.push(r);
    }
  }
  async run(initialBackoffMs) {
    let lastEventId = null;
    let backoff = initialBackoffMs;
    const decoder = new TextDecoder();
    while (!this.closed) {
      try {
        const headers = {
          accept: "text/event-stream",
          ...this.headers
        };
        if (lastEventId !== null) headers["last-event-id"] = lastEventId;
        const resp = await fetch(this.url, { headers, signal: this.abort.signal });
        if (resp.ok && resp.body) {
          const parser = createSseParser();
          const reader = resp.body.getReader();
          for (; ; ) {
            const { done, value } = await reader.read();
            if (done || this.closed) break;
            for (const event of parser.feed(decoder.decode(value, { stream: true }))) {
              if (event.id !== null) lastEventId = event.id;
              if (event.event !== "receipt") continue;
              let wire;
              try {
                wire = JSON.parse(event.data);
              } catch {
                continue;
              }
              this.push(
                Receipt.fromTurnReceipt(wire.receipt, {
                  turnHash: wire.turn_hash,
                  receiptHash: wire.receipt_hash,
                  chainIndex: wire.chain_index,
                  hasProofHint: wire.has_proof,
                  finality: wire.finality
                })
              );
              backoff = initialBackoffMs;
            }
          }
        }
      } catch {
      }
      if (this.closed) break;
      await new Promise((r) => setTimeout(r, backoff));
      backoff = Math.min(backoff * 2, 15e3);
    }
    const w = this.waiter;
    if (w) {
      this.waiter = void 0;
      w(null);
    }
  }
  /** The next committed receipt (`null` only after [`close`]). */
  next() {
    const head = this.queue.shift();
    if (head !== void 0) return Promise.resolve(head);
    if (this.closed) return Promise.resolve(null);
    return new Promise((resolve) => {
      this.waiter = resolve;
    });
  }
  /** End the subscription. */
  close() {
    this.closed = true;
    this.abort.abort();
    const w = this.waiter;
    if (w) {
      this.waiter = void 0;
      w(null);
    }
  }
  async *[Symbol.asyncIterator]() {
    try {
      for (; ; ) {
        const r = await this.next();
        if (r === null) return;
        yield r;
      }
    } finally {
      this.close();
    }
  }
};
var NodeEvents = class {
  /** Point at a node's base URL (e.g. `https://devnet.dregg.fg-goose.online`). */
  constructor(baseUrl, opts = {}) {
    this.baseUrl = baseUrl.replace(/\/+$/, "");
    this.opts = opts;
  }
  /**
   * Subscribe to the node's committed receipts. Reconnects with exponential
   * backoff and `Last-Event-ID` resume; the stream ends only when closed.
   */
  subscribe(filter = new ReceiptFilter()) {
    const headers = {};
    if (this.opts.devnetKey) headers["X-Devnet-Key"] = this.opts.devnetKey;
    return new ReceiptStream(
      `${this.baseUrl}/api/events/stream${filter.query()}`,
      headers,
      this.opts.initialBackoffMs ?? 500
    );
  }
};

// src/explain.ts
var hx32 = (b) => hexEncode(b);
function semTag(hash) {
  return `[sem ${hx32(hash)}]`;
}
function effectBody(effect) {
  switch (effect.kind) {
    case "setField":
      return `set state field #${effect.index} of cell ${hx32(effect.cell)} to 0x${hx32(effect.value)}`;
    case "transfer":
      return `transfer ${effect.amount} computrons from cell ${hx32(effect.from)} to cell ${hx32(effect.to)}`;
    case "grantCapability":
      return `grant capability (target ${hx32(effect.cap.target)} slot ${effect.cap.slot}) from cell ${hx32(effect.from)} to cell ${hx32(effect.to)}`;
    case "revokeCapability":
      return `revoke capability in slot ${effect.slot} of cell ${hx32(effect.cell)}`;
    case "emitEvent":
      return `emit event (topic 0x${hx32(effect.topic)}, ${effect.data.length} data field(s)) from cell ${hx32(effect.cell)}`;
    case "incrementNonce":
      return `increment the nonce of cell ${hx32(effect.cell)}`;
    case "createCell":
      return `create a new cell (owner 0x${hx32(effect.publicKey)}, token 0x${hx32(effect.tokenId)}) with balance ${effect.balance}`;
    default: {
      const unreachable = effect;
      return unreachable;
    }
  }
}
function explainEffect(effect) {
  return `${effectBody(effect)} ${semTag(effectHash(effect))}`;
}
function authMode(auth) {
  switch (auth.kind) {
    case "signature":
      return "an Ed25519 signature";
    case "unchecked":
      return "NO authorization (unchecked \u2014 only valid if the cell permits)";
    default: {
      const unreachable = auth;
      return unreachable;
    }
  }
}
function explainAction(action) {
  let out = `Action on cell ${hx32(action.target)}, authorized by ${authMode(action.authorization)}`;
  if (action.balanceChange !== void 0) {
    out += `, balance change ${action.balanceChange}`;
  }
  out += `:
  ${action.effects.length} effect(s):
`;
  action.effects.forEach((effect, i) => {
    out += `    ${i + 1}. ${explainEffect(effect)}
`;
  });
  out += `  ${semTag(actionHash(action))}`;
  return out;
}
function explainTurn(turn) {
  let out = `Turn by agent ${hx32(turn.agent)} (nonce ${turn.nonce}, fee ${turn.fee})`;
  if (turn.memo !== void 0) {
    out += ` memo ${JSON.stringify(turn.memo)}`;
  }
  out += "\n";
  const actions = [];
  const walk = (trees) => {
    for (const t of trees) {
      actions.push(t.action);
      walk(t.children);
    }
  };
  walk(turn.roots);
  out += `${actions.length} action(s) in the call forest:
`;
  actions.forEach((a, i) => {
    out += `[${i}] ${explainAction(a)}
`;
  });
  return out;
}
var renderTurn = explainTurn;

// src/turns.ts
var PAY_METHOD = "pay";
var DEFAULT_FEE = 10000n;
var VALIDITY_HORIZON_SECS = 3600n;
var EmptyTurnError = class extends Error {
  constructor() {
    super("refusing to sign an empty turn (no effects staged)");
    this.name = "EmptyTurnError";
  }
};
var TurnBuilder = class {
  constructor(runtime) {
    this.methodName = "execute";
    this.effectList = [];
    this.argList = [];
    this.runtime = runtime;
  }
  /** The cell whose authority this turn exercises. */
  actingCell() {
    return this.actingOn ?? this.runtime.identity.cellId();
  }
  /**
   * Target another cell the identity administers (the action targets
   * `target`; this agent signs and pays). The node verifies the signature
   * against `target`'s `owner_pubkey` and requires the agent's c-list
   * capability on it.
   */
  on(target) {
    this.actingOn = target;
    return this;
  }
  /** Set the action's method verb (default `"execute"`). */
  method(name) {
    this.methodName = name;
    return this;
  }
  /** Set the turn fee (computron budget). Defaults to 10 000. */
  fee(fee) {
    this.feeValue = BigInt(fee);
    return this;
  }
  // ─── typed verbs ───
  /** Transfer `amount` computrons from the acting cell to `to`. */
  transfer(to, amount) {
    this.effectList.push({ kind: "transfer", from: this.actingCell(), to, amount });
    return this;
  }
  /**
   * Transfer with an explicit source cell (must still be within this
   * identity's authority — the executor checks, not the builder).
   */
  transferFrom(from, to, amount) {
    this.effectList.push({ kind: "transfer", from, to, amount });
    return this;
  }
  /**
   * Write state slot `index` of the acting cell (admitted only where the
   * cell's installed program allows).
   */
  write(index, value) {
    this.effectList.push({ kind: "setField", cell: this.actingCell(), index, value });
    return this;
  }
  /** [`write`] with a numeric value (encoded like `field_from_u64`). */
  writeU64(index, value) {
    return this.write(index, fieldFromU64(value));
  }
  /**
   * Grant a capability from the acting cell to `to` (non-amplifying: the
   * executor admits only grants within held authority).
   */
  grant(to, cap) {
    this.effectList.push({ kind: "grantCapability", from: this.actingCell(), to, cap });
    return this;
  }
  /** Bump the acting cell's nonce (a deliberate no-op state advance). */
  incrementNonce() {
    this.effectList.push({ kind: "incrementNonce", cell: this.actingCell() });
    return this;
  }
  /** Append one prebuilt effect (escape hatch; the executor's gates apply identically). */
  effect(effect) {
    this.effectList.push(effect);
    return this;
  }
  /** Append a prebuilt effect list (the splice point for plan builders). */
  effects(effects) {
    for (const e of effects) this.effectList.push(e);
    return this;
  }
  /**
   * Set the action's argument vector (the typed witness the method carries;
   * the routing/auth gate on the method symbol, these are the receipt-bound
   * record). Each entry is a 32-byte field element. Replaces any prior args.
   */
  args(args) {
    this.argList = args.slice();
    return this;
  }
  /**
   * **`pay`** — move `amount` of `asset` from the acting cell to `to` through
   * the canonical `Payable` `pay` desugar. The byte-identical twin of
   * `dregg_payable::resolve_pay` / the Rust SDK's `AgentRuntime::pay`: the
   * action's `method` is `pay`, its `args` are `[asset, field_from_u64(amount),
   * to]` (the `pay_args` witness), and it carries EXACTLY ONE conserving
   * `Effect::Transfer` (per-asset Σδ=0). The same value rail the app
   * framework's `Payable::pay` and the metered tool-gateway charge ride — not a
   * hand-rolled effect.
   *
   * `asset` is the asset to pay in (the payer's `token_id`; a bridged `$DREGG`
   * mirror asset is an ordinary 32-byte id, routed identically).
   */
  pay(to, amount, asset) {
    this.methodName = PAY_METHOD;
    this.argList = [asset, fieldFromU64(amount), to];
    this.effectList.push({ kind: "transfer", from: this.actingCell(), to, amount });
    return this;
  }
  // ─── terminal ───
  /**
   * Sign the built action with this identity's key over the canonical
   * federation-bound signing message, yielding an [`AuthorizedTurn`] ready
   * to [`submit`](AuthorizedTurn.submit).
   *
   * After this point the act is credentialed; there is no way back to an
   * unauthorized shape. (Async because the federation binding is discovered
   * from the node on first use.)
   */
  async sign() {
    if (this.effectList.length === 0) {
      throw new EmptyTurnError();
    }
    const target = this.actingCell();
    const federationId = await this.runtime.node.federationId();
    const unsigned = unsignedActionNamed(target, this.methodName, this.effectList);
    unsigned.args = this.argList;
    const action = this.runtime.identity.signAction(unsigned, federationId);
    return new AuthorizedTurn(this.runtime, action, this.feeValue ?? DEFAULT_FEE);
  }
};
var AuthorizedTurn = class {
  constructor(runtime, action, fee) {
    this.submitted = false;
    this.runtime = runtime;
    this.signedAction = action;
    this.fee = fee;
  }
  /**
   * The clerk's faithful, total explanation of exactly what was signed —
   * the anti-blind-signing reading (see `explain.ts`).
   */
  explain() {
    return explainAction(this.signedAction);
  }
  /** The signed action (inspection only — `submit` consumes the turn). */
  action() {
    return this.signedAction;
  }
  /**
   * Execute the turn on the node and return the [`Receipt`] noun.
   *
   * The agent cell pays; the turn rides the cell's live nonce, the node's
   * receipt-chain head (`previous_receipt_hash` causal binding), and a
   * one-hour validity horizon; the envelope signature binds the canonical
   * `Turn::hash` (v3). A chain-head race (another commit landing between
   * read and submit) is retried once with fresh bindings — the per-action
   * signature stays valid; only the envelope is re-signed. One-shot: a
   * second call is refused (the consumed turn would replay-fail anyway).
   */
  async submit() {
    if (this.submitted) {
      throw new Error("AuthorizedTurn already submitted (one-shot, like the Rust consume-on-submit)");
    }
    this.submitted = true;
    let lastError;
    for (let attempt = 0; attempt < 2; attempt++) {
      const nonce = await this.runtime.currentNonce();
      const previousReceiptHash = await this.runtime.node.receiptChainHead();
      const turn = {
        agent: this.runtime.identity.cellId(),
        nonce,
        roots: [{ action: this.signedAction, children: [] }],
        fee: this.fee,
        validUntil: BigInt(Math.floor(Date.now() / 1e3)) + VALIDITY_HORIZON_SECS,
        previousReceiptHash
      };
      try {
        return await this.runtime.submitTurn(turn);
      } catch (e) {
        lastError = e;
        const msg = e instanceof Error ? e.message : String(e);
        if (attempt === 0 && /receipt chain mismatch|nonce/i.test(msg)) {
          continue;
        }
        throw e;
      }
    }
    throw lastError;
  }
};

// src/trustline.ts
function asHex(cell) {
  return typeof cell === "string" ? cell : hexEncode(cell);
}
var TrustlineClient = class {
  constructor(node) {
    this.node = node;
  }
  /**
   * Open a directional line `operator → holder` of `line`, escrowed in full
   * (fullReserve). The node births the per-line cell, funds it, grants the
   * holder + operator their capabilities, and opens it — four turns.
   *
   * `salt` disambiguates multiple lines to the same holder.
   */
  open(holder, line, salt) {
    const body = { holder: asHex(holder), line: Number(line) };
    if (salt !== void 0) body.salt = salt;
    return this.node.postJson("/trustline/open", body);
  }
  /**
   * Draw `amount` against the line (debits the shared counter). Supply a
   * `digest` (hex) for client-side replay protection across retries; the
   * node derives one otherwise. Draws are one-shot per digest.
   */
  draw(trustline, amount, digest) {
    const body = { trustline: asHex(trustline), amount: Number(amount) };
    if (digest !== void 0) body.digest = digest;
    return this.node.postJson("/trustline/draw", body);
  }
  /** Repay `amount`, restoring the line (never resurrects a burned digest). */
  repay(trustline, amount) {
    return this.node.postJson("/trustline/repay", {
      trustline: asHex(trustline),
      amount: Number(amount)
    });
  }
  /** Settle outstanding draws as ledger moves to the holders (epoch sweep). */
  settle(trustline) {
    return this.node.postJson("/trustline/settle", { trustline: asHex(trustline) });
  }
  /** Close the line: settle outstanding to the holder, residual to the issuer. */
  close(trustline) {
    return this.node.postJson("/trustline/close", { trustline: asHex(trustline) });
  }
  /** Live position: line / drawn / remaining / escrow / coordinator state. */
  status(trustline) {
    return this.node.getJson(`/trustline/status/${asHex(trustline)}`);
  }
};

// src/channels.ts
function asHex2(cell) {
  return typeof cell === "string" ? cell : hexEncode(cell);
}
function memberJson(m) {
  return { cell: asHex2(m.cell), seal_pk: typeof m.sealPk === "string" ? m.sealPk : hexEncode(m.sealPk) };
}
var ChannelsClient = class {
  constructor(node) {
    this.node = node;
  }
  /**
   * Birth the group at epoch 1 with `members` as founders. `tag` (u64) names
   * the group among the operator's groups. Returns the first fan-out.
   */
  create(tag, members) {
    return this.node.postJson("/channels/create", {
      tag: Number(tag),
      members: members.map(memberJson)
    });
  }
  /** Add a member — one unified epoch step; returns the fresh fan-out. */
  join(channel, member) {
    return this.node.postJson("/channels/join", {
      channel: asHex2(channel),
      member: memberJson(member)
    });
  }
  /**
   * Remove a member — one unified epoch step that darkens BOTH their
   * forward-read ability and their group-held capabilities. The removed
   * member is simply absent from the returned fan-out.
   */
  remove(channel, member) {
    return this.node.postJson("/channels/remove", {
      channel: asHex2(channel),
      member: asHex2(member)
    });
  }
  /** Advance the epoch without a membership change (a fresh key fan-out). */
  rekey(channel) {
    return this.node.postJson("/channels/rekey", { channel: asHex2(channel) });
  }
  /**
   * Post a message body. Encrypt client-side under the CURRENT epoch key,
   * then POST only `nonce` + `ciphertext` (hex). The body never touches the
   * chain — only this transport relay does.
   */
  post(channel, epoch, nonce, ciphertext) {
    return this.node.postJson("/channels/post", {
      channel: asHex2(channel),
      epoch: Number(epoch),
      nonce: typeof nonce === "string" ? nonce : hexEncode(nonce),
      ciphertext: typeof ciphertext === "string" ? ciphertext : hexEncode(ciphertext)
    });
  }
  /** Live group state: epoch, roster commitment, the `epochs_unified` tooth. */
  status(channel) {
    return this.node.getJson(`/channels/status/${asHex2(channel)}`);
  }
  /**
   * Subscribe to the group's message stream (`GET /channels/messages/{cell}`,
   * SSE) as an async iterable of ciphertext envelopes. Open each body with
   * the epoch key you hold from the fan-out.
   */
  async *messages(channel) {
    yield* this.node.sseStream(`/channels/messages/${asHex2(channel)}`);
  }
};

// src/service-economy.ts
var LEASE_STEP_SLOT = 4;
var DEFAULT_LEASE_METHOD = "run";
function leaseProgramConstraints(maxSteps) {
  const ceiling = maxSteps < 0 ? 0 : maxSteps;
  return [
    { kind: "fieldLte", index: LEASE_STEP_SLOT, value: fieldFromU64(ceiling) },
    { kind: "monotonic", index: LEASE_STEP_SLOT }
  ];
}
var Lease = class {
  constructor(runtime, terms) {
    this.runtime = runtime;
    this.stepIndex = 0;
    this.maxSteps = terms.maxSteps;
    this.leaseCell = terms.leaseCell;
    this.asset = terms.asset;
    this.method = terms.method ?? DEFAULT_LEASE_METHOD;
  }
  /** The durable checkpoint index so far. */
  step() {
    return this.stepIndex;
  }
  /** The runs remaining on the lease (`maxSteps - step`). */
  remaining() {
    return this.maxSteps - this.stepIndex;
  }
  /**
   * The unsigned-then-signable builder for the next `run`: a
   * `Monotonic`/`FieldLte`-gated `SetField` on {@link LEASE_STEP_SLOT}
   * (`step → step+1`) followed by `work`, on the lease's run verb. Does NOT
   * advance the local counter (inspect / sign without committing).
   */
  runTurn(work = []) {
    const next = this.stepIndex + 1;
    return this.runtime.turn().on(this.leaseCell).method(this.method).writeU64(LEASE_STEP_SLOT, next).effects(work);
  }
  /**
   * Advance the durable checkpoint and meter `work` on one turn. Submits the
   * {@link runTurn} and, on commit, advances the local step counter.
   */
  async run(work = []) {
    const receipt = await (await this.runTurn(work).sign()).submit();
    this.stepIndex += 1;
    return { receipt, step: this.stepIndex, remaining: this.remaining() };
  }
  /** The signable builder for a funding transfer: one conserving
   * `Effect::Transfer` of `amount` from `funder` into the lease cell. */
  fundTurn(funder, amount) {
    return this.runtime.turn().transferFrom(funder, this.leaseCell, amount);
  }
  /** Move `amount` from `funder` into the lease cell with a conserving
   * `Effect::Transfer`. The runtime signs; the executor checks authority over
   * `funder`. */
  async fund(funder, amount) {
    return (await this.fundTurn(funder, amount).sign()).submit();
  }
};
var ServiceEconomy = class {
  constructor(runtime) {
    this.runtime = runtime;
  }
  /** The signable builder for {@link pay} (inspect / sign without submitting). */
  payTurn(to, amount, asset) {
    return this.runtime.turn().pay(to, amount, asset);
  }
  /**
   * **`pay`** — move `amount` of `asset` from this runtime's cell to `to`
   * through the canonical `Payable` `pay` desugar (one conserving
   * `Effect::Transfer`, per-asset Σδ=0). Byte-identical to the Rust
   * `AgentRuntime::pay`.
   */
  async pay(to, amount, asset) {
    return (await this.payTurn(to, amount, asset).sign()).submit();
  }
  /**
   * The signable builder for {@link invoke}: an action targeting `cell`'s
   * `method` with `args`, optionally PREPENDING the canonical pay `Transfer`
   * (caller → provider) ahead of `work`. The DFA route + fail-closed
   * unknown-method/under-authority refusals are the node executor's job over
   * the wire.
   */
  invokeTurn(cell, method, args = [], opts) {
    const builder = this.runtime.turn().on(cell).method(method).args(args);
    if (opts?.pay) {
      builder.transferFrom(this.runtime.identity.cellId(), opts.pay.provider, opts.pay.amount);
    }
    if (opts?.work) builder.effects(opts.work);
    return builder;
  }
  /**
   * **`invoke`** — call `method` on the `cell` service, optionally paying
   * through `Payable` in the same turn, and submit. The committed turn carries
   * the routed method + (optionally pay-prepended) effects, mirroring the Rust
   * `AgentRuntime::invoke_service`.
   */
  async invoke(cell, method, args = [], opts) {
    return (await this.invokeTurn(cell, method, args, opts).sign()).submit();
  }
  /**
   * **`lease`** — bind to a provisioned lease cell and drive its durable,
   * metered `run` / `fund` turns. See {@link Lease} and
   * {@link leaseProgramConstraints} for the meter program installed at
   * provisioning.
   */
  lease(terms) {
    return new Lease(this.runtime, terms);
  }
};

// src/client.ts
var NodeError = class extends Error {
  constructor(message, status) {
    super(message);
    this.name = "NodeError";
    this.status = status;
  }
};
var NodeClient = class {
  constructor(baseUrl, opts = {}) {
    this.baseUrl = baseUrl.replace(/\/+$/, "");
    this.opts = opts;
    if (opts.federationId !== void 0) {
      this.cachedFederationId = typeof opts.federationId === "string" ? hexDecodeExact(opts.federationId, 32) : Uint8Array.from(opts.federationId);
    }
  }
  headers(extra = {}) {
    const h = { ...extra };
    if (this.opts.devnetKey) {
      h["X-Devnet-Key"] = this.opts.devnetKey;
      h["Authorization"] = `Bearer ${this.opts.devnetKey}`;
    }
    return h;
  }
  async request(path, init = {}) {
    const url = this.baseUrl + path;
    const resp = await fetch(url, {
      signal: AbortSignal.timeout(this.opts.timeoutMs ?? 15e3),
      ...init,
      headers: this.headers(init.headers ?? {})
    });
    if (!resp.ok) {
      const body = await resp.text().catch(() => "");
      throw new NodeError(`HTTP ${resp.status} from ${path}: ${body.slice(0, 300)}`, resp.status);
    }
    return await resp.json();
  }
  /**
   * `GET {path}` → parsed JSON. The generic read used by the organ clients
   * (trustline / channels / attested-query); carries the devnet headers and
   * timeout. Throws [`NodeError`] on a non-2xx.
   */
  getJson(path) {
    return this.request(path);
  }
  /**
   * `POST {path}` with a JSON body → parsed JSON. The generic write used by
   * the organ clients. Throws [`NodeError`] on a non-2xx.
   */
  postJson(path, body) {
    return this.request(path, {
      method: "POST",
      body: JSON.stringify(body),
      headers: { "Content-Type": "application/json" }
    });
  }
  /**
   * Subscribe to a node SSE route as a one-shot async iterable of parsed
   * `data:` JSON payloads (no reconnect — that lives in [`NodeEvents`] for
   * the receipt stream). Used by the channels message stream.
   */
  async *sseStream(path) {
    const resp = await fetch(this.baseUrl + path, {
      headers: this.headers({ Accept: "text/event-stream" })
    });
    if (!resp.ok || !resp.body) {
      const txt = resp.body ? await resp.text().catch(() => "") : "";
      throw new NodeError(`HTTP ${resp.status} from ${path}: ${txt.slice(0, 300)}`, resp.status);
    }
    const reader = resp.body.getReader();
    const decoder = new TextDecoder();
    const parser = createSseParser();
    for (; ; ) {
      const { value, done } = await reader.read();
      if (done) break;
      for (const evt of parser.feed(decoder.decode(value, { stream: true }))) {
        if (evt.data) yield JSON.parse(evt.data);
      }
    }
  }
  /** `GET /api/node/identity` — the node operator's identity. */
  nodeIdentity() {
    return this.request("/api/node/identity");
  }
  /** The node operator's Ed25519 public key (hex). Falls back from
   * `/api/node/identity` to `/status` for older node builds. */
  async operatorPublicKeyHex() {
    try {
      return (await this.nodeIdentity()).public_key;
    } catch (e) {
      if (e instanceof NodeError && e.status === 404) {
        const status = await this.request("/status");
        return status.public_key;
      }
      throw e;
    }
  }
  /** `GET /api/cell/{id}` — live cell state (balance, nonce, slots). */
  cell(cellId) {
    const hex = typeof cellId === "string" ? cellId : hexEncode(cellId);
    return this.request(`/api/cell/${hex}`);
  }
  /** `GET /api/receipts` — the node's recent committed receipts. */
  receipts() {
    return this.request("/api/receipts");
  }
  /**
   * The node's receipt-chain head hash (32 bytes), or undefined on an empty
   * chain. Submitted turns bind to this via `previous_receipt_hash` (causal
   * ordering; the node verifies the claim against its live head).
   */
  async receiptChainHead() {
    const infos = await this.receipts();
    if (infos.length === 0) return void 0;
    const head = infos.find((r) => r.chain_head) ?? infos.reduce((a, b) => a.chain_index >= b.chain_index ? a : b);
    return hexDecodeExact(head.receipt_hash, 32);
  }
  /**
   * The federation id the node's EXECUTOR verifies action signatures
   * against. Explicit option wins; else discovered (see
   * [`NodeClientOptions.federationId`]) and cached.
   */
  async federationId() {
    if (this.cachedFederationId) return this.cachedFederationId;
    try {
      const feds = await this.request(
        "/api/federations"
      );
      const local = feds.find((f) => f.is_local && f.member_count > 0 && f.committee_epoch > 0);
      if (local) {
        this.cachedFederationId = hexDecodeExact(local.federation_id, 32);
        return this.cachedFederationId;
      }
    } catch {
    }
    const operatorPk = await this.operatorPublicKeyHex();
    this.cachedFederationId = blake3(hexDecodeExact(operatorPk, 32));
    return this.cachedFederationId;
  }
  /**
   * `POST /api/faucet` — devnet: materialize a hosted cell (`amount: 0`)
   * and/or claim computrons (max 10000 per request). Passing `publicKey`
   * lets the node install a canonical hosted cell with a real owner key —
   * REQUIRED before that cell can pass Ed25519 turn authorization.
   */
  async faucet(recipient, amount, publicKey) {
    const body = {
      recipient: typeof recipient === "string" ? recipient : hexEncode(recipient),
      amount
    };
    if (publicKey !== void 0) {
      body.public_key = typeof publicKey === "string" ? publicKey : hexEncode(publicKey);
    }
    return this.request("/api/faucet", {
      method: "POST",
      body: JSON.stringify(body),
      headers: { "Content-Type": "application/json" }
    });
  }
  /** Submit a postcard `SignedTurn` envelope (the signed-byte ingress). */
  submitSignedEnvelope(envelope) {
    return this.request("/api/turns/submit-signed", {
      method: "POST",
      body: envelope,
      headers: { "Content-Type": "application/octet-stream" }
    });
  }
  /**
   * Find the committed receipt for `turnHashHex`, polling briefly — commits
   * land synchronously but the receipt listing is a separate read.
   */
  async receiptForTurn(turnHashHex, attempts = 10, delayMs = 300) {
    const want = turnHashHex.toLowerCase();
    for (let i = 0; i < attempts; i++) {
      const infos = await this.receipts();
      const hit = infos.find((r) => r.turn_hash.toLowerCase() === want);
      if (hit) {
        return new Receipt({
          turnHash: hit.turn_hash,
          receiptHash: hit.receipt_hash,
          agent: hit.agent,
          preStateHash: hit.pre_state,
          postStateHash: hit.post_state,
          timestamp: hit.timestamp,
          computronsUsed: hit.computrons_used,
          actionCount: hit.action_count,
          previousReceiptHash: hit.previous_receipt_hash ?? void 0,
          finality: hit.finality,
          wasEncrypted: hit.was_encrypted,
          wasBurn: hit.was_burn,
          chainIndex: hit.chain_index,
          hasProofHint: hit.has_proof
        });
      }
      await new Promise((r) => setTimeout(r, delayMs));
    }
    return new Receipt({ turnHash: want });
  }
  /**
   * Fetch the persisted full-turn STARK for a committed turn
   * (`GET /api/turn/{hash}/proof`) — proofs land asynchronously from the
   * node's prove pool; `undefined` until then.
   */
  async turnProof(turnHashHex) {
    try {
      const res = await this.request(
        `/api/turn/${turnHashHex}/proof`
      );
      const bytes = new Uint8Array(res.proof_hex.length / 2);
      for (let i = 0; i < bytes.length; i++) {
        bytes[i] = parseInt(res.proof_hex.slice(i * 2, i * 2 + 2), 16);
      }
      return new TurnProof(hexDecodeExact(res.turn_hash, 32), bytes);
    } catch (e) {
      if (e instanceof NodeError && e.status === 404) return void 0;
      throw e;
    }
  }
  /** The node's committed-receipt event stream (SSE). */
  events() {
    return new NodeEvents(this.baseUrl, { devnetKey: this.opts.devnetKey });
  }
  /**
   * The **trustline** organ (`docs/ORGANS.md` §1) over this node's
   * operator-local trustline service. Operator-gated — pass a `devnetKey`.
   */
  trustline() {
    return new TrustlineClient(this);
  }
  /**
   * The **channels** organ (`docs/ORGANS.md` §4) over this node's channels
   * service. Operator-gated — pass a `devnetKey`.
   */
  channels() {
    return new ChannelsClient(this);
  }
};
var AgentRuntime = class {
  constructor(identity, node, opts = {}) {
    this.identity = identity;
    this.node = typeof node === "string" ? new NodeClient(node, opts) : node;
  }
  /** This identity's default agent cell (hex). */
  cellIdHex() {
    return this.identity.cellIdHex();
  }
  /**
   * Open the typed turn builder — the SDK's one public turn shape:
   * `runtime.turn().transfer(..).write(..).sign()` → `submit()` → `Receipt`.
   */
  turn() {
    return new TurnBuilder(this);
  }
  /**
   * Devnet bootstrap: materialize this identity's agent cell with its real
   * owner key and claim `amount` computrons.
   */
  async faucet(amount) {
    const res = await this.node.faucet(this.identity.cellId(), amount, this.identity.publicKey);
    if (!res.success) {
      throw new NodeError(`faucet refused: ${res.error ?? "unknown"}`);
    }
  }
  /** The **trustline** organ on this runtime's node ([`NodeClient.trustline`]). */
  trustline() {
    return this.node.trustline();
  }
  /** The **channels** organ on this runtime's node ([`NodeClient.channels`]). */
  channels() {
    return this.node.channels();
  }
  /**
   * The **service-economy** surface (`docs/guide/SERVICE-ECONOMY-SDK.md`) — the
   * TS twin of the Rust SDK facade. `runtime.services.invoke(...)`,
   * `runtime.execution.lease(...)`, `runtime.pay(...)`.
   */
  econ() {
    return this.serviceEconomy ?? (this.serviceEconomy = new ServiceEconomy(this));
  }
  /** Find + call a service (`econ.invoke`); `runtime.services.invoke(...)`. */
  get services() {
    return this.econ();
  }
  /** Open a durable, metered execution lease (`econ.lease`);
   * `runtime.execution.lease(...)`. */
  get execution() {
    return this.econ();
  }
  /**
   * **`pay`** — move `amount` of `asset` from this runtime's cell to `to`
   * through the canonical `Payable` `pay` desugar (one conserving
   * `Effect::Transfer`). The few-lines front door; mirrors Rust
   * `AgentRuntime::pay`.
   */
  pay(to, amount, asset) {
    return this.econ().pay(to, amount, asset);
  }
  /** The agent cell's current nonce (0 for a never-seen cell). */
  async currentNonce() {
    try {
      const cell = await this.node.cell(this.identity.cellId());
      return cell.found ? BigInt(cell.nonce) : 0n;
    } catch (e) {
      if (e instanceof NodeError && e.status === 404) return 0n;
      throw e;
    }
  }
  /**
   * Envelope-sign and submit a finished turn; resolve the committed
   * [`Receipt`]. Used by `AuthorizedTurn.submit()`.
   */
  async submitTurn(turn) {
    const envelope = this.identity.signTurnEnvelope(turn);
    const res = await this.node.submitSignedEnvelope(envelope);
    const hashHex = res.turn_hash ?? hexEncode(turnHash(turn));
    if (!res.accepted) {
      throw new NodeError(`turn rejected: ${res.error ?? "unknown"} (turn ${hashHex})`);
    }
    return this.node.receiptForTurn(hashHex);
  }
};

// src/mailbox.ts
var SUBSCRIBE_DOMAIN = new TextEncoder().encode("dregg-relay-subscribe-v1");
var UNSUBSCRIBE_DOMAIN = new TextEncoder().encode("dregg-relay-unsubscribe-v1");
var DRAIN_DOMAIN = new TextEncoder().encode("dregg-relay-drain-v1");
function base64Encode(bytes) {
  if (typeof Buffer !== "undefined") return Buffer.from(bytes).toString("base64");
  let bin = "";
  for (const b of bytes) bin += String.fromCharCode(b);
  return btoa(bin);
}
function base64Decode(s) {
  if (typeof Buffer !== "undefined") return Uint8Array.from(Buffer.from(s, "base64"));
  const bin = atob(s);
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}
function concat(...parts) {
  const total = parts.reduce((n, p) => n + p.length, 0);
  const out = new Uint8Array(total);
  let off = 0;
  for (const p of parts) {
    out.set(p, off);
    off += p.length;
  }
  return out;
}
function freshNonce() {
  const n = new Uint8Array(8);
  globalThis.crypto.getRandomValues(n);
  return n;
}
var RelayError = class extends Error {
  constructor(message, status) {
    super(message);
    this.name = "RelayError";
    this.status = status;
  }
};
var MailboxClient = class {
  constructor(relayBaseUrl, identity, opts = {}) {
    this.baseUrl = relayBaseUrl.replace(/\/+$/, "");
    this.identity = identity;
    this.opts = opts;
  }
  /** The owner public key (hex) — the inbox id. */
  get ownerHex() {
    return this.identity.publicKeyHex;
  }
  async request(path, init = {}) {
    const resp = await fetch(this.baseUrl + path, {
      signal: AbortSignal.timeout(this.opts.timeoutMs ?? 15e3),
      ...init
    });
    if (!resp.ok) {
      const body = await resp.text().catch(() => "");
      throw new RelayError(`HTTP ${resp.status} from ${path}: ${body.slice(0, 300)}`, resp.status);
    }
    return await resp.json();
  }
  /** `GET /relay/status` — the relay operator's identity + bond. */
  status() {
    return this.request("/relay/status");
  }
  /**
   * `POST /relay/subscribe` — create this owner's hosted inbox. Signs
   * `owner || nonce` under `dregg-relay-subscribe-v1`.
   */
  subscribe(capacity, minDeposit) {
    const owner = this.identity.publicKey;
    const nonce = freshNonce();
    const sig = this.identity.signBytes(concat(SUBSCRIBE_DOMAIN, owner, nonce));
    const body = {
      owner: this.ownerHex,
      nonce: hexEncode(nonce),
      signature: hexEncode(sig)
    };
    if (capacity !== void 0) body.capacity = capacity;
    if (minDeposit !== void 0) body.min_deposit = minDeposit;
    return this.request("/relay/subscribe", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body)
    });
  }
  /**
   * `DELETE /relay/unsubscribe` — remove this owner's inbox. Signs
   * `owner || nonce` under `dregg-relay-unsubscribe-v1`.
   */
  unsubscribe() {
    const owner = this.identity.publicKey;
    const nonce = freshNonce();
    const sig = this.identity.signBytes(concat(UNSUBSCRIBE_DOMAIN, owner, nonce));
    return this.request("/relay/unsubscribe", {
      method: "DELETE",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ owner: this.ownerHex, nonce: hexEncode(nonce), signature: hexEncode(sig) })
    });
  }
  /**
   * `POST /relay/send/{dest}` — enqueue an ALREADY-SEALED `ciphertext` to
   * `dest`'s inbox, paying `deposit`. Unauthenticated (the sender identity
   * here only labels the message). Seal the body yourself first.
   */
  send(dest, ciphertext, deposit) {
    const destHex = typeof dest === "string" ? dest : hexEncode(dest);
    return this.request(`/relay/send/${destHex}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        sender: this.ownerHex,
        payload: base64Encode(ciphertext),
        deposit
      })
    });
  }
  /**
   * `GET /relay/drain` — drain up to `max` messages (default 100), each with
   * its full dequeue proof. Signs `owner || nonce || max_le(u64)` under
   * `dregg-relay-drain-v1`. Recompute each body's `content_hash` before
   * trusting it.
   */
  drain(max = 100) {
    const owner = this.identity.publicKey;
    const nonce = freshNonce();
    const sig = this.identity.signBytes(concat(DRAIN_DOMAIN, owner, nonce, u64le(max)));
    const params = new URLSearchParams({
      owner: this.ownerHex,
      nonce: hexEncode(nonce),
      max: String(max),
      signature: hexEncode(sig)
    });
    return this.request(`/relay/drain?${params.toString()}`);
  }
  /** `GET /relay/inbox/{id}/status` — this inbox's queue depth + root. */
  inboxStatus() {
    return this.request(`/relay/inbox/${this.ownerHex}/status`);
  }
};

// src/attested.ts
var AttestedQuery = class {
  constructor(node, opts = {}) {
    this.node = typeof node === "string" ? new NodeClient(node, opts) : node;
  }
  /** `GET /federation/roots` — the federation-attested state roots. */
  attestedRoots() {
    return this.node.getJson("/federation/roots");
  }
  /** `GET /checkpoint/latest` — the latest finalized checkpoint. */
  checkpoint() {
    return this.node.getJson("/checkpoint/latest");
  }
  /** `GET /checkpoint/{height}` — the finalized checkpoint at `height`. */
  checkpointAt(height) {
    return this.node.getJson(`/checkpoint/${height}`);
  }
  /**
   * The full-turn STARK for a committed turn (`GET /api/turn/{hash}/proof`),
   * or `undefined` while the node's prove pool is still producing it. The
   * proof is BYTES — verify it with the wasm/Rust `verify_full_turn`, not
   * here.
   */
  turnProof(turnHashHex) {
    return this.node.turnProof(turnHashHex);
  }
};

// src/program.ts
var program_exports = {};
__export(program_exports, {
  CellProgramBuilder: () => CellProgramBuilder,
  anyOf: () => anyOf,
  balanceGte: () => balanceGte,
  balanceLte: () => balanceLte,
  canonicalProgramVk: () => canonicalProgramVk,
  encodeConstraints: () => encodeConstraints,
  fieldEquals: () => fieldEquals,
  fieldFromU64: () => fieldFromU642,
  immutable: () => immutable,
  implies: () => implies,
  monotonic: () => monotonic,
  preimageGate: () => preimageGate,
  programmedCellDescriptor: () => programmedCellDescriptor,
  senderInSlot: () => senderInSlot,
  senderIs: () => senderIs,
  simple: () => simple,
  writeOnce: () => writeOnce
});
function fieldFromU642(v) {
  const out = new Uint8Array(32);
  let n = BigInt(v);
  if (n < 0n || n >= 1n << 64n) throw new Error("fieldFromU64: out of u64 range");
  for (let i = 31; i >= 24; i--) {
    out[i] = Number(n & 0xffn);
    n >>= 8n;
  }
  return out;
}
function senderIs(pk) {
  return { kind: "senderIs", pk: exactBytes(pk, 32, "senderIs pk") };
}
function senderInSlot(index) {
  return { kind: "senderInSlot", index };
}
function balanceGte(min) {
  return { kind: "balanceGte", min: BigInt(min) };
}
function balanceLte(max) {
  return { kind: "balanceLte", max: BigInt(max) };
}
function preimageGate(commitmentIndex, hashKind = "blake3") {
  return { kind: "preimageGate", commitmentIndex, hashKind };
}
function immutable(index) {
  return { kind: "immutable", index };
}
function writeOnce(index) {
  return { kind: "writeOnce", index };
}
function monotonic(index) {
  return { kind: "monotonic", index };
}
function fieldEquals(index, value) {
  return { kind: "fieldEquals", index, value: exactBytes(value, 32, "fieldEquals value") };
}
function anyOf(variants) {
  return { kind: "anyOf", variants };
}
var simple = {
  fieldEquals: (index, value) => ({
    kind: "fieldEquals",
    index,
    value: exactBytes(value, 32, "fieldEquals value")
  }),
  writeOnce: (index) => ({ kind: "writeOnce", index }),
  immutable: (index) => ({ kind: "immutable", index }),
  senderIs: (pk) => ({
    kind: "senderIs",
    pk: exactBytes(pk, 32, "senderIs pk")
  }),
  senderInSlot: (index) => ({ kind: "senderInSlot", index }),
  balanceGte: (min) => ({ kind: "balanceGte", min: BigInt(min) }),
  balanceLte: (max) => ({ kind: "balanceLte", max: BigInt(max) }),
  preimageGate: (commitmentIndex, hashKind = "blake3") => ({
    kind: "preimageGate",
    commitmentIndex,
    hashKind
  }),
  /**
   * Negation — accept iff the inner constraint rejects. Fail-closed: an
   * unevaluable inner stays unevaluable, never vacuously satisfied.
   * Double-negation is unrepresentable (mirrors the Rust type shape).
   */
  not: (inner) => {
    if (inner.kind === "not") {
      throw new Error("Not(Not(..)) is not representable; use the inner constraint directly");
    }
    return { kind: "not", inner };
  }
};
function implies(antecedent, consequent) {
  return anyOf([simple.not(antecedent), consequent]);
}
var W = class {
  constructor() {
    this.parts = [];
  }
  u8(v) {
    this.parts.push(v & 255);
    return this;
  }
  varint(v) {
    let n = BigInt(v);
    if (n < 0n) throw new Error("varint: negative");
    do {
      let b = Number(n & 0x7fn);
      n >>= 7n;
      if (n !== 0n) b |= 128;
      this.parts.push(b);
    } while (n !== 0n);
    return this;
  }
  bytes(b) {
    for (const x of b) this.parts.push(x);
    return this;
  }
  out() {
    return Uint8Array.from(this.parts);
  }
};
var hashKindIndex = (k) => k === "blake3" ? 0 : 1;
function writeSimple(w, c) {
  switch (c.kind) {
    case "fieldEquals":
      w.varint(0).u8(c.index).bytes(c.value);
      break;
    case "fieldGte":
      w.varint(1).u8(c.index).bytes(c.value);
      break;
    case "fieldLte":
      w.varint(2).u8(c.index).bytes(c.value);
      break;
    case "writeOnce":
      w.varint(3).u8(c.index);
      break;
    case "immutable":
      w.varint(4).u8(c.index);
      break;
    case "monotonic":
      w.varint(5).u8(c.index);
      break;
    case "strictMonotonic":
      w.varint(6).u8(c.index);
      break;
    case "boundedBy":
      w.varint(7).u8(c.index).u8(c.witnessIndex);
      break;
    case "not":
      w.varint(11);
      writeSimple(w, c.inner);
      break;
    case "senderIs":
      w.varint(12).bytes(c.pk);
      break;
    case "senderInSlot":
      w.varint(13).u8(c.index);
      break;
    case "balanceGte":
      w.varint(14).varint(c.min);
      break;
    case "balanceLte":
      w.varint(15).varint(c.max);
      break;
    case "preimageGate":
      w.varint(16).u8(c.commitmentIndex).varint(hashKindIndex(c.hashKind));
      break;
  }
}
function writeConstraint(w, c) {
  switch (c.kind) {
    case "fieldEquals":
      w.varint(0).u8(c.index).bytes(c.value);
      break;
    case "fieldGte":
      w.varint(1).u8(c.index).bytes(c.value);
      break;
    case "fieldLte":
      w.varint(2).u8(c.index).bytes(c.value);
      break;
    case "writeOnce":
      w.varint(6).u8(c.index);
      break;
    case "immutable":
      w.varint(7).u8(c.index);
      break;
    case "monotonic":
      w.varint(8).u8(c.index);
      break;
    case "preimageGate":
      w.varint(21).u8(c.commitmentIndex).varint(hashKindIndex(c.hashKind));
      break;
    case "anyOf":
      w.varint(26).varint(c.variants.length);
      for (const v of c.variants) writeSimple(w, v);
      break;
    case "senderIs":
      w.varint(38).bytes(c.pk);
      break;
    case "senderInSlot":
      w.varint(39).u8(c.index);
      break;
    case "balanceGte":
      w.varint(40).varint(c.min);
      break;
    case "balanceLte":
      w.varint(41).varint(c.max);
      break;
  }
}
function encodeConstraints(constraints) {
  const w = new W();
  w.varint(constraints.length);
  for (const c of constraints) writeConstraint(w, c);
  return w.out();
}
function canonicalProgramVk(constraints) {
  const w = new W();
  w.varint(1);
  w.bytes(encodeConstraints(constraints));
  const serialized = w.out();
  return Blake3Hasher.newDeriveKey("dregg-cellprogram-vk-v1").update(u64le(serialized.length)).update(serialized).finalize();
}
function programmedCellDescriptor(constraints) {
  const encoded = encodeConstraints(constraints);
  const factoryVk = Blake3Hasher.newDeriveKey("dregg-sdk:programmed-cell-factory v1").update(u64le(encoded.length)).update(encoded).finalize();
  const childVk = canonicalProgramVk(constraints);
  return {
    factoryVk,
    factoryVkHex: hexEncode(factoryVk),
    childProgramVk: childVk,
    childProgramVkHex: hexEncode(childVk),
    stateConstraints: constraints,
    defaultMode: "hosted",
    creationBudget: 1
  };
}
var CellProgramBuilder = class {
  constructor() {
    this.staged = [];
  }
  /** Add one constraint atom. */
  require(constraint) {
    this.staged.push(constraint);
    return this;
  }
  /** Add a whole constraint list (e.g. a blueprint's published set). */
  program(constraints) {
    for (const c of constraints) this.staged.push(c);
    return this;
  }
  /** The staged constraint set. */
  constraints() {
    return this.staged;
  }
  /** Publish as a content-addressed descriptor. */
  descriptor() {
    return programmedCellDescriptor(this.staged);
  }
};

// src/pg.ts
var TOKEN_GUC = "dregg.token";
var READER_ROLE = "dregg_reader";
var KERNEL_ROLE = "dregg_kernel";
var DreggPgError = class extends Error {
  constructor(message) {
    super(message);
    this.name = "DreggPgError";
  }
};
function toBytea(value, what = "identifier") {
  if (value instanceof Uint8Array) return value;
  if (typeof value === "string") {
    const s = value.startsWith("\\x") || value.startsWith("0x") ? value.slice(2) : value;
    try {
      return hexDecode(s);
    } catch {
      throw new DreggPgError(`${what} hex is not valid: ${value}`);
    }
  }
  throw new DreggPgError(`${what} must be 64-char hex or 32 bytes`);
}
function bytea(value) {
  const B = globalThis.Buffer;
  return B ? B.from(value) : value;
}
var ROLE_RE = /^[A-Za-z_][A-Za-z0-9_]{0,62}$/;
function validateIdent(ident) {
  if (!ROLE_RE.test(ident)) throw new DreggPgError(`invalid role identifier: ${ident}`);
  return ident;
}
function asBigInt(v) {
  if (typeof v === "bigint") return v;
  if (typeof v === "number") return BigInt(v);
  if (typeof v === "string") return BigInt(v);
  throw new DreggPgError(`expected an integer, got ${typeof v}`);
}
function asBigIntOrNull(v) {
  return v === null || v === void 0 ? null : asBigInt(v);
}
function asDateOrNull(v) {
  if (v === null || v === void 0) return null;
  return v instanceof Date ? v : new Date(String(v));
}
function asStringOrNull(v) {
  return v === null || v === void 0 ? null : String(v);
}
function wrapPgError(err, what) {
  const msg = String(err?.message ?? err).trim();
  const lower = msg.toLowerCase();
  if (lower.includes("row-level security")) {
    return new DreggPgError(
      `${what}: refused by Row-Level Security \u2014 your presented capability does not authorize it (the submit_gate / read policy denied it). Present a token that admits it, and assume the dregg_reader role. [${msg}]`
    );
  }
  if (lower.includes("does not exist") && (lower.includes("function") || lower.includes("dregg"))) {
    return new DreggPgError(
      `${what}: the pg-dregg surface is not installed in this database (CREATE EXTENSION pg_dregg; SELECT dregg_install_schema();). [${msg}]`
    );
  }
  return new DreggPgError(`${what}: ${msg}`);
}
var Pg = class _Pg {
  constructor(client) {
    this.client = client;
    this.outboxRelCache = null;
  }
  /**
   * Wrap an already-connected client and (optionally) present a token + assume a
   * role. Mirrors `dregg.pg.connect`. The client must already be connected (this
   * does not open the socket — inject a `pg.Client`/`pg.Pool` you connected).
   */
  static async connect(client, opts = {}) {
    const pg = new _Pg(client);
    const role = opts.role === void 0 ? READER_ROLE : opts.role;
    if (role !== null) await pg.setRole(role);
    if (opts.token !== void 0) await pg.presentToken(opts.token);
    return pg;
  }
  /** The underlying client (escape hatch for raw SQL). */
  get connection() {
    return this.client;
  }
  /** Release the client if it exposes `end()` (a `pg.Client`/`pg.Pool`). */
  async close() {
    if (typeof this.client.end === "function") await this.client.end();
  }
  // ── small query helpers ──
  async rows(text, params = []) {
    const res = await this.client.query(text, params);
    return res.rows;
  }
  async scalar(text, params = []) {
    const rows = await this.rows(text, params);
    if (rows.length === 0) return null;
    const row = rows[0];
    const keys = Object.keys(row);
    return keys.length ? row[keys[0]] : null;
  }
  // ── presenting authority (the capability the rows are gated by) ──
  /**
   * Present a `dga1_…` capability token for the session by setting the
   * `dregg.token` GUC (`set_config('dregg.token', token, local)`). The
   * `dregg_admits` RLS policies read it. With `local=true` it is
   * transaction-local. A superuser BYPASSes RLS; assume `dregg_reader` (the
   * default in {@link Pg.connect}) so the policy fires.
   */
  async presentToken(token, local = false) {
    await this.scalar("SELECT set_config($1, $2, $3)", [TOKEN_GUC, token, local]);
  }
  /** Clear the presented token (present the empty string ⇒ deny-by-default). */
  async clearToken(local = false) {
    await this.scalar("SELECT set_config($1, $2, $3)", [TOKEN_GUC, "", local]);
  }
  /** The token currently presented, or `null` if none. */
  async currentToken() {
    const tok = await this.scalar("SELECT current_setting($1, true)", [TOKEN_GUC]);
    return tok ? tok : null;
  }
  /** `SET ROLE` — assume `role` so RLS is enforced as it (`dregg_reader` for apps). */
  async setRole(role) {
    await this.scalar("SELECT set_config('role', $1, false)", [validateIdent(role)]);
  }
  /** `RESET ROLE`. */
  async resetRole() {
    await this.scalar("RESET ROLE");
  }
  // ── free-SQL reads (typed projections of the shipped views) ──
  /**
   * `dregg.cell_balances` — the ledger, hex-keyed and balance-first. Only the
   * cells the presented token admits `read` on are returned (read-side RLS).
   */
  async cellBalances(opts = {}) {
    const orderByBalance = opts.orderByBalance ?? true;
    let sql = "SELECT cell, balance, nonce, lifecycle, last_ordinal FROM dregg.cell_balances";
    if (orderByBalance) sql += " ORDER BY balance DESC";
    const params = [];
    if (opts.limit !== void 0) {
      sql += " LIMIT $1";
      params.push(opts.limit);
    }
    const rows = await this.rows(sql, params);
    return rows.map(rowToCellBalance);
  }
  /** One cell's row by id, or `null` if absent / not admitted. */
  async cellBalance(cell) {
    const cellHex = hexEncode(toBytea(cell, "cell id"));
    const rows = await this.rows(
      "SELECT cell, balance, nonce, lifecycle, last_ordinal FROM dregg.cell_balances WHERE cell = $1",
      [cellHex]
    );
    return rows.length ? rowToCellBalance(rows[0]) : null;
  }
  /**
   * `dregg.receipt_chain` — the turn hash chain in ordinal order. Walk it to
   * verify non-omission: each row's `prevRoot` is the prior row's `ledgerRoot`.
   */
  async receiptChain(opts = {}) {
    let sql = "SELECT ordinal, height, creator, prev_root, ledger_root, committed_at FROM dregg.receipt_chain ORDER BY ordinal";
    const params = [];
    if (opts.limit !== void 0) {
      sql += " LIMIT $1";
      params.push(opts.limit);
    }
    const rows = await this.rows(sql, params);
    return rows.map(rowToReceipt);
  }
  /** The latest turn in `dregg.receipt_chain` (the chain head), or `null`. */
  async chainHead() {
    const rows = await this.rows(
      "SELECT ordinal, height, creator, prev_root, ledger_root, committed_at FROM dregg.receipt_chain ORDER BY ordinal DESC LIMIT 1"
    );
    return rows.length ? rowToReceipt(rows[0]) : null;
  }
  /** `dregg.cap_edges` — the delegation graph; with `src`, only edges out of it. */
  async capEdges(opts = {}) {
    let rows;
    if (opts.src !== void 0) {
      const srcHex = hexEncode(toBytea(opts.src, "src cell"));
      rows = await this.rows(
        "SELECT src, dst, slot, permissions, expires_at FROM dregg.cap_edges WHERE src = $1",
        [srcHex]
      );
    } else {
      rows = await this.rows(
        "SELECT src, dst, slot, permissions, expires_at FROM dregg.cap_edges"
      );
    }
    return rows.map(rowToCapEdge);
  }
  /** `SELECT sum(balance) FROM dregg.cells` — value conserved across the ledger. */
  async conservationTotal() {
    const total = await this.scalar("SELECT coalesce(sum(balance), 0) FROM dregg.cells");
    return asBigInt(total);
  }
  // ── the write path: submit a verified turn (the node drains it) ──
  /**
   * Submit a SIGNED turn FROM postgres via `dregg_submit_turn(signed_turn,
   * agent)` (`docs/PG-DREGG.md` §11). `signedTurn` is the postcard `SignedTurn`
   * bytes; `agent` is the turn's agent cell id.
   *
   * Enqueues into `dregg.submit_queue` and returns the submission `uuid`. The
   * enqueue is RLS-gated by `dregg_admits('submit', encode(agent,'hex'))` — a
   * role submits only the turns its capability authorizes; otherwise RLS refuses
   * the INSERT (throws {@link DreggPgError}). **Postgres never executes** — the
   * node's §11.4 drainer applies the turn; poll {@link Pg.outbox} /
   * {@link Pg.submission} for the outcome (`status` walks `pending → executed |
   * refused`). `dregg_submit_turn` is NOT `SECURITY DEFINER` — present a `submit`
   * token and assume `dregg_reader` first.
   */
  async submitTurn(signedTurn, agent) {
    if (!(signedTurn instanceof Uint8Array)) {
      throw new DreggPgError("signedTurn must be the postcard SignedTurn bytes (Uint8Array)");
    }
    const agentB = toBytea(agent, "agent cell");
    try {
      const id = await this.scalar("SELECT dregg_submit_turn($1, $2)", [
        bytea(signedTurn),
        bytea(agentB)
      ]);
      return String(id);
    } catch (err) {
      throw wrapPgError(err, "dregg_submit_turn (enqueue)");
    }
  }
  /**
   * Enqueue a signed turn by a direct `INSERT INTO dregg.submit_queue` (the
   * explicit form `dregg_submit_turn` wraps). Same RLS gate (`submit_gate`).
   */
  async enqueueTurn(signedTurn, agent) {
    if (!(signedTurn instanceof Uint8Array)) {
      throw new DreggPgError("signedTurn must be the postcard SignedTurn bytes (Uint8Array)");
    }
    const agentB = toBytea(agent, "agent cell");
    try {
      const id = await this.scalar(
        "INSERT INTO dregg.submit_queue (agent, signed_turn) VALUES ($1, $2) RETURNING id",
        [bytea(agentB), bytea(signedTurn)]
      );
      return String(id);
    } catch (err) {
      throw wrapPgError(err, "submit_queue INSERT");
    }
  }
  // ── the outbox tail (view preferred, base table fallback) ──
  /**
   * Tail the submit-queue audit surface — every submission you may see and its
   * outcome, ordered by `id` (= arrival order on pg18, where the key is a
   * `uuidv7`). RLS-gated by the same `submit` admission. Prefers
   * `dregg.submit_queue_audit` (the pg18 view); falls back to the base
   * `dregg.submit_queue` table where the view is absent (older / pg17 installs).
   */
  async outbox(opts = {}) {
    const { relation, cols } = await this.outboxRelation();
    let sql = `SELECT ${cols} FROM ${relation} ORDER BY id`;
    const params = [];
    if (opts.limit !== void 0) {
      sql += " LIMIT $1";
      params.push(opts.limit);
    }
    const rows = await this.rows(sql, params);
    return rows.map(rowToSubmission);
  }
  /** One submission by id from the audit surface (poll after {@link Pg.submitTurn}). */
  async submission(id) {
    const { relation, cols } = await this.outboxRelation();
    const rows = await this.rows(`SELECT ${cols} FROM ${relation} WHERE id = $1`, [
      id
    ]);
    return rows.length ? rowToSubmission(rows[0]) : null;
  }
  async outboxRelation() {
    if (this.outboxRelCache) return this.outboxRelCache;
    const base = "id, agent, submitter, status, receipt_hash, error, submitted_at, resolved_at";
    const viewPresent = await this.scalar(
      "SELECT to_regclass('dregg.submit_queue_audit') IS NOT NULL"
    );
    let result;
    if (viewPresent) {
      result = { relation: "dregg.submit_queue_audit", cols: base };
    } else {
      result = {
        relation: "dregg.submit_queue",
        cols: "id, encode(agent,'hex') AS agent, submitter, status, encode(receipt_hash,'hex') AS receipt_hash, error, submitted_at, resolved_at"
      };
    }
    this.outboxRelCache = result;
    return result;
  }
  // ── federation health ──
  /**
   * `dregg_federation_health()` — the subscriber-side federation health check
   * (`docs/PG-DREGG.md` §15): the pg18 apply-conflict counters DRIVE the chain
   * re-validation. Returns the one-line verdict (`'ok: …'` / `'ALARM …'` /
   * `'CRITICAL …'`).
   */
  async federationHealth() {
    return String(await this.scalar("SELECT dregg_federation_health()"));
  }
  /** `true` iff {@link Pg.federationHealth} reports the healthy verdict. */
  async federationHealthOk() {
    return (await this.federationHealth()).startsWith("ok:");
  }
  /**
   * `dregg_revalidate_replicated_chain()` — the subscriber re-validation sweep
   * over the replicated `dregg.turns` (the anti-substitution tooth, run locally).
   */
  async revalidateReplicatedChain() {
    return String(await this.scalar("SELECT dregg_revalidate_replicated_chain()"));
  }
  // ── issuer status + dev mint ──
  /**
   * `dregg_issuer_status()` — the database's dregg key configuration in one line,
   * so the silent fail-closed mode ("no issuer key ⇒ everything denies") is
   * discoverable. Run it first when "all my rows vanished". The private key is
   * never reported.
   */
  async issuerStatus() {
    return String(await this.scalar("SELECT dregg_issuer_status()"));
  }
  /**
   * `dregg_dev_mint(subject, actions[], resource_prefix, ttl interval)` — **DEV
   * ONLY.** Compose the common capability shape (`action ∈ actions` confined to
   * `resourcePrefix`, expiring `ttl` from now, naming `subject`) and mint a
   * `dga1_…` token, so a newcomer never hand-writes `Pred` JSON. Issuer-key
   * discipline is intact: it routes through the same mint path as `dregg_mint`
   * and RAISES (no silent token) if `dregg.issuer_privkey` is not configured.
   * `ttl` is a postgres interval literal (e.g. `"1 hour"`).
   */
  async devMint(subject, actions, resourcePrefix, ttl) {
    try {
      const tok = await this.scalar("SELECT dregg_dev_mint($1, $2, $3, $4::interval)", [
        subject,
        actions,
        resourcePrefix,
        ttl
      ]);
      return String(tok);
    } catch (err) {
      throw wrapPgError(err, "dregg_dev_mint");
    }
  }
  // ── direct capability decisions (the M1 functions, offline-verified) ──
  /** `dregg_cap_admits(token, action, resource, now)` — TRUE iff admitted (fail-closed). */
  async capAdmits(token, action, resource, now) {
    const at = now ?? Number(await this.scalar("SELECT extract(epoch from now())::bigint"));
    const v = await this.scalar("SELECT dregg_cap_admits($1, $2, $3, $4)", [
      token,
      action,
      resource,
      at
    ]);
    return Boolean(v);
  }
  /** `dregg_cap_explain(...)` — the human-readable decision reason. */
  async capExplain(token, action, resource, now) {
    const at = now ?? Number(await this.scalar("SELECT extract(epoch from now())::bigint"));
    return asStringOrNull(
      await this.scalar("SELECT dregg_cap_explain($1, $2, $3, $4)", [token, action, resource, at])
    );
  }
  /** `dregg_cap_subject(token)` — the confined subject the token names, or `null`. */
  async capSubject(token) {
    return asStringOrNull(await this.scalar("SELECT dregg_cap_subject($1)", [token]));
  }
  /** `dregg_revoke(token)` — revoke the credential; returns the revoked id or `null`. */
  async revoke(token) {
    try {
      return asStringOrNull(await this.scalar("SELECT dregg_revoke($1)", [token]));
    } catch (err) {
      throw wrapPgError(err, "dregg_revoke");
    }
  }
  // ── one-call schema install (the dregg-developer entry points) ──
  /** `dregg_install_schema()` — install the Tier-B store. Idempotent (DBA role). */
  async installSchema() {
    try {
      return String(await this.scalar("SELECT dregg_install_schema()"));
    } catch (err) {
      throw wrapPgError(err, "dregg_install_schema");
    }
  }
  /** `dregg_install_write_outbox()` — install the write-path outbox. Idempotent. */
  async installWriteOutbox() {
    try {
      return String(await this.scalar("SELECT dregg_install_write_outbox()"));
    } catch (err) {
      throw wrapPgError(err, "dregg_install_write_outbox");
    }
  }
};
function rowToCellBalance(r) {
  return {
    cell: String(r.cell),
    balance: asBigInt(r.balance),
    nonce: asBigInt(r.nonce),
    lifecycle: String(r.lifecycle),
    lastOrdinal: asBigInt(r.last_ordinal)
  };
}
function rowToReceipt(r) {
  return {
    ordinal: asBigInt(r.ordinal),
    height: asBigInt(r.height),
    creator: String(r.creator),
    prevRoot: String(r.prev_root),
    ledgerRoot: String(r.ledger_root),
    committedAt: asDateOrNull(r.committed_at)
  };
}
function rowToCapEdge(r) {
  return {
    src: String(r.src),
    dst: String(r.dst),
    slot: Number(r.slot),
    permissions: r.permissions ?? null,
    expiresAt: asBigIntOrNull(r.expires_at)
  };
}
function rowToSubmission(r) {
  return {
    id: String(r.id),
    agent: String(r.agent),
    submitter: String(r.submitter),
    status: String(r.status),
    receiptHash: asStringOrNull(r.receipt_hash),
    error: asStringOrNull(r.error),
    submittedAt: asDateOrNull(r.submitted_at),
    resolvedAt: asDateOrNull(r.resolved_at)
  };
}

// src/deploy.ts
var DeployChecker = class {
  constructor(wasm) {
    this.wasm = wasm;
  }
  /**
   * Parse DreggDL → lower to the real `CallForest` → run the static assurance
   * over the whole declared authority layout → return the {@link DeployVerdict}.
   *
   * This is exactly what `dregg-deploy check <file>` runs (the same lowering +
   * the same `dregg_userspace_verify::analyze`).
   *
   * @param text DreggDL surface text — TOML, or JSON when it starts with `{`.
   * @param ring When `true`, also run the ring-balance check (a settlement
   *   ring declared as bare funding transfers must net to zero).
   * @throws Error naming the offending row on a parse / lowering error.
   */
  check(text, ring = false) {
    const json = this.wasm.deploy_check(text, ring);
    return JSON.parse(json);
  }
  /**
   * Run only the real `Lowered::from_deployment` lowering (no check) and return
   * the resolved artifact: the ordered births → funds → grants `CallForest` the
   * checker consumes, the resolved federation id, and the resolved
   * factory / cell content-addresses. This is `dregg-deploy lower <file>`.
   *
   * @throws Error naming the offending row on a parse / lowering error.
   */
  lower(text) {
    const json = this.wasm.deploy_lower(text);
    return JSON.parse(json);
  }
};
// Annotate the CommonJS export names for ESM import in node:
0 && (module.exports = {
  AgentRuntime,
  AttestedQuery,
  AuthorizedTurn,
  ChannelsClient,
  DEFAULT_DOMAINS,
  DEFAULT_LEASE_METHOD,
  DREGG_ENDPOINTS,
  DeployChecker,
  DreggPgError,
  EmptyTurnError,
  Identity,
  KERNEL_ROLE,
  LEASE_STEP_SLOT,
  Lease,
  MAIN_IDENTITY_PATH,
  MailboxClient,
  NodeClient,
  NodeError,
  NodeEvents,
  PAY_METHOD,
  PROFILE_ENV,
  Pg,
  ProfileError,
  READER_ROLE,
  Receipt,
  ReceiptFilter,
  ReceiptStream,
  RelayError,
  ServiceEconomy,
  TOKEN_GUC,
  TrustlineClient,
  TurnBuilder,
  TurnProof,
  WrongTurnProofError,
  apiUrl,
  base64Decode,
  base64Encode,
  createSseParser,
  devnetUrl,
  devnetWssUrl,
  explainAction,
  explainEffect,
  explainTurn,
  fieldFromU64,
  gatewayUrl,
  hexDecode,
  hexEncode,
  leaseProgramConstraints,
  portalUrl,
  profiles,
  program,
  renderTurn,
  resolveDomains,
  symbol
});

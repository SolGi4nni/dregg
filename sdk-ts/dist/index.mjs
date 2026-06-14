import {
  AgentRuntime,
  AuthorizedTurn,
  ChannelsClient,
  EmptyTurnError,
  Identity,
  MAIN_IDENTITY_PATH,
  NodeClient,
  NodeError,
  NodeEvents,
  Receipt,
  ReceiptFilter,
  ReceiptStream,
  TrustlineClient,
  TurnBuilder,
  TurnProof,
  WrongTurnProofError,
  createSseParser,
  explainAction,
  explainEffect,
  explainTurn,
  renderTurn
} from "./chunk-Q4UVKDBW.mjs";
import {
  Blake3Hasher,
  exactBytes,
  fieldFromU64,
  hexDecode,
  hexDecodeExact,
  hexEncode,
  symbol,
  u64le
} from "./chunk-4HL4X43K.mjs";
import {
  __export
} from "./chunk-7P6ASYW6.mjs";

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
import { chmodSync, existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "fs";
import { randomBytes } from "crypto";
import { join } from "path";
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
  if (home) return join(home, "profiles");
  const base = process.env.HOME ?? ".";
  return join(base, ".dregg", "profiles");
}
function validName(name) {
  return /^[a-z0-9_-]{1,64}$/.test(name);
}
function profilePath(name) {
  return join(profilesDir(), `${name}.json`);
}
function activePath() {
  return join(profilesDir(), "ACTIVE");
}
function writePrivate(path, contents) {
  mkdirSync(profilesDir(), { recursive: true });
  writeFileSync(path, contents, { mode: 384 });
  chmodSync(path, 384);
}
function readProfile(name) {
  const path = profilePath(name);
  if (!existsSync(path)) {
    throw new ProfileError("not_found", `profile ${JSON.stringify(name)} not found`);
  }
  let parsed;
  try {
    parsed = JSON.parse(readFileSync(path, "utf8"));
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
  if (existsSync(path)) {
    throw new ProfileError("already_exists", `profile ${JSON.stringify(name)} already exists`);
  }
  const seed = new Uint8Array(randomBytes(64));
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
    entries = readdirSync(dir);
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
  if (!existsSync(profilePath(name))) {
    throw new ProfileError("not_found", `profile ${JSON.stringify(name)} not found`);
  }
  writePrivate(activePath(), name);
}
function activeName() {
  const env = process.env[PROFILE_ENV]?.trim();
  if (env) return env;
  try {
    const contents = readFileSync(activePath(), "utf8").trim();
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
export {
  AgentRuntime,
  AttestedQuery,
  AuthorizedTurn,
  ChannelsClient,
  DeployChecker,
  EmptyTurnError,
  Identity,
  MAIN_IDENTITY_PATH,
  MailboxClient,
  NodeClient,
  NodeError,
  NodeEvents,
  PROFILE_ENV,
  ProfileError,
  Receipt,
  ReceiptFilter,
  ReceiptStream,
  RelayError,
  TrustlineClient,
  TurnBuilder,
  TurnProof,
  WrongTurnProofError,
  base64Decode,
  base64Encode,
  createSseParser,
  explainAction,
  explainEffect,
  explainTurn,
  fieldFromU64,
  hexDecode,
  hexEncode,
  profiles_exports as profiles,
  program_exports as program,
  renderTurn,
  symbol
};

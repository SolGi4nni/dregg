import {
  ChannelsClient,
  TrustlineClient
} from "./chunk-NXSLBHQJ.mjs";
import {
  Blake3Hasher,
  actionHash,
  actionSigningMessage,
  blake3,
  blake3DeriveKey,
  deriveCellId,
  ed25519PublicKey,
  ed25519Sign,
  effectHash,
  encodeSignedTurn,
  fieldFromU64,
  symbol,
  turnHash,
  unsignedActionNamed
} from "./chunk-JGRCUNFP.mjs";
import {
  bytesEqual,
  exactBytes,
  hexDecode,
  hexDecodeExact,
  hexEncode,
  u64le
} from "./chunk-O4UULVUH.mjs";
import {
  __export
} from "./chunk-7P6ASYW6.mjs";

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
export {
  AgentRuntime,
  AttestedQuery,
  AuthorizedTurn,
  ChannelsClient,
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

/**
 * The raw turn-construction vocabulary: wire types, postcard encoding, and
 * the canonical BLAKE3 hash/signing preimages — byte-compatible with the
 * Rust `dregg-turn` / `dregg-sdk` crates.
 *
 * Sources of truth mirrored here (drift in any of them must fail the
 * differential test in `test/wire.test.mjs`, which checks byte equality
 * against the repo's own `dregg-wasm` build):
 *
 *   - `turn/src/action.rs`   — `Effect`, `Authorization`, `Action::hash` (v2)
 *   - `turn/src/forest.rs`   — `CallForest::compute_hash`
 *   - `turn/src/turn.rs`     — `Turn`, `Turn::hash` (v3)
 *   - `turn/src/executor/authorize.rs` — `compute_signing_message`
 *     (`dregg-action-sig-v2`, federation-bound)
 *   - `types/src/lib.rs`     — `CellId::derive_raw` (`dregg-cell-id-v1`)
 *   - `sdk/src/cipherclerk.rs` — `SignedTurn` envelope (postcard)
 *
 * Effects modeled: the typed-verb subset the authorized builder needs
 * (SetField / Transfer / GrantCapability / RevokeCapability / EmitEvent /
 * IncrementNonce / CreateCell). The full Rust enum has ~27 variants; the
 * postcard variant indexes here are the Rust declaration indexes, which are
 * append-only by contract.
 */

import {
  concatBytes,
  exactBytes,
  hexEncode,
  i64le,
  u32le,
  u64le,
  utf8,
} from "./bytes";
import { Blake3Hasher, blake3, blake3DeriveKey } from "./blake3";

// ─────────────────────────────────────────────────────────────────────────────
// Core identifiers
// ─────────────────────────────────────────────────────────────────────────────

/** A 32-byte cell identity (`dregg_types::CellId`). */
export type CellId = Uint8Array;

/** A 32-byte field element / symbol / hash. */
export type Bytes32 = Uint8Array;

/** `symbol(name)` — the BLAKE3-hashed method/topic name actions carry. */
export function symbol(name: string): Bytes32 {
  return blake3(utf8.encode(name));
}

/** The default token domain: `blake3("default")` (agent default cells). */
export function defaultTokenId(): Bytes32 {
  return blake3(utf8.encode("default"));
}

/**
 * `CellId::derive_raw(public_key, token_id)` — domain-separated BLAKE3
 * (`dregg-cell-id-v1`) over `public_key || token_id`.
 */
export function deriveCellId(publicKey: Uint8Array, tokenId: Uint8Array = defaultTokenId()): CellId {
  return blake3DeriveKey(
    "dregg-cell-id-v1",
    concatBytes(exactBytes(publicKey, 32, "publicKey"), exactBytes(tokenId, 32, "tokenId")),
  );
}

/** Encode a u64 as a `FieldElement` the way `dregg_cell::field_from_u64` does:
 * big-endian u64 in the LAST 8 bytes of a 32-byte word. */
export function fieldFromU64(v: number | bigint): Bytes32 {
  const out = new Uint8Array(32);
  let n = BigInt(v);
  if (n < 0n || n >= 1n << 64n) throw new Error("fieldFromU64: out of u64 range");
  for (let i = 31; i >= 24; i--) {
    out[i] = Number(n & 0xffn);
    n >>= 8n;
  }
  return out;
}

// ─────────────────────────────────────────────────────────────────────────────
// Wire types (TS projections of the Rust enums/structs)
// ─────────────────────────────────────────────────────────────────────────────

/** `dregg_cell::AuthRequired`. */
export type AuthRequired =
  | { kind: "none" }
  | { kind: "signature" }
  | { kind: "proof" }
  | { kind: "either" }
  | { kind: "impossible" }
  | { kind: "custom"; vkHash: Bytes32 };

/** `dregg_cell::CapabilityRef` (the c-list entry a grant installs). */
export interface CapabilityRef {
  target: CellId;
  slot: number;
  permissions: AuthRequired;
  breadstuff?: Bytes32;
  expiresAt?: number | bigint;
  /**
   * NOTE: `allowed_effects` is intentionally not modeled on this surface.
   * The Rust field carries `#[serde(default)]` ONLY (NOT
   * `skip_serializing_if`, see cell/src/capability.rs) — a skipped field
   * cannot round-trip the non-self-describing `postcard` codec, so its
   * `None` discriminant IS emitted into the stream. The encoder writes a
   * literal `None` for it (parity with the Rust serializer keeps the
   * differential green).
   */
  storedEpoch?: number | bigint;
  /**
   * The capability-instance PROVENANCE hash (`cell/src/capability.rs`,
   * `CapabilityRef::provenance`). Same serde rule as `allowed_effects`:
   * `#[serde(default)]` ONLY, NO `skip_serializing_if`, so postcard EMITS
   * its 32 bytes positionally after `stored_epoch`. It is a bare `[u8; 32]`
   * (NOT an `Option`) — there is no discriminant, just the 32 raw bytes.
   * `[0u8; 32]` is the legacy/unprovenanced sentinel (the correct default
   * for a direct grant), so an omitted `provenance` encodes as 32 zeros.
   */
  provenance?: Bytes32;
}

/** The typed-verb `Effect` subset (Rust declaration indexes in comments). */
export type Effect =
  | { kind: "setField"; cell: CellId; index: number; value: Bytes32 } // 0
  | { kind: "transfer"; from: CellId; to: CellId; amount: number | bigint } // 1
  | { kind: "grantCapability"; from: CellId; to: CellId; cap: CapabilityRef } // 2
  | { kind: "revokeCapability"; cell: CellId; slot: number } // 3
  | { kind: "emitEvent"; cell: CellId; topic: Bytes32; data: Bytes32[] } // 4
  | { kind: "incrementNonce"; cell: CellId } // 5
  | { kind: "createCell"; publicKey: Bytes32; tokenId: Bytes32; balance: number | bigint }; // 6

/** `dregg_turn::Authorization` (the variants the authorized flow emits). */
export type Authorization =
  /** Classical ed25519 only — the LEGACY shape (`sign_action_classical`). */
  | { kind: "signature"; r: Bytes32; s: Bytes32 } // postcard variant 0
  /**
   * HYBRID (ed25519 + ML-DSA-65) — the DEFAULT, matching Rust's
   * `AgentCipherclerk::sign_action`. Both halves cover the SAME canonical
   * signing message; the ML-DSA half is bound into `Action::hash` under
   * discriminant 10 so an outer signed-turn envelope covers it (anti-strip).
   */
  | {
      kind: "hybridSignature"; // postcard variant 10
      /** The ed25519 signature over the canonical signing message (64 bytes). */
      ed25519: Uint8Array;
      /** The ML-DSA-65 signature (3309 bytes). Empty ⇒ PQ half absent. */
      mlDsa: Uint8Array;
      /** The signer's serialized ML-DSA-65 public key (1952 bytes). */
      mlDsaPk: Uint8Array;
    }
  | { kind: "unchecked" }; // postcard variant 4

/** `dregg_turn::Action` with every optional field at its default. */
export interface Action {
  target: CellId;
  method: Bytes32;
  args: Bytes32[];
  authorization: Authorization;
  // preconditions: always default (cell_state/network/valid_while None, witnessed []).
  effects: Effect[];
  // may_delegate: DelegationMode::None; commitment_mode: CommitmentMode::Full.
  balanceChange?: bigint;
  // witness_blobs: always empty on this surface.
}

/** One call-forest node (children supported structurally; the builder emits roots). */
export interface CallTree {
  action: Action;
  children: CallTree[];
}

/** `dregg_turn::Turn` with the exotic proof-bundle fields at their defaults. */
export interface Turn {
  agent: CellId;
  nonce: bigint;
  roots: CallTree[];
  fee: bigint;
  memo?: string;
  validUntil?: bigint;
  previousReceiptHash?: Bytes32;
  dependsOn?: Bytes32[];
}

// ─────────────────────────────────────────────────────────────────────────────
// UNAUTHORIZED construction — the single place `unchecked` is spelled
// ─────────────────────────────────────────────────────────────────────────────

/**
 * Build the UNAUTHORIZED action scaffold (`Authorization::Unchecked`, every
 * optional field defaulted) — mirror of `sdk/src/raw.rs::unsigned_action`.
 *
 * Sanctioned uses: (1) as the zero-authorization input to the canonical
 * signing message — the signing flow immediately replaces the field with a
 * real signature; (2) genesis / test fixtures. An action submitted as-is
 * presents NO credential.
 */
export function unsignedAction(target: CellId, method: Bytes32, effects: Effect[]): Action {
  return {
    target: exactBytes(target, 32, "target"),
    method: exactBytes(method, 32, "method"),
    args: [],
    authorization: { kind: "unchecked" },
    effects,
  };
}

/** [`unsignedAction`] with a string method name (hashed via [`symbol`]). */
export function unsignedActionNamed(target: CellId, method: string, effects: Effect[]): Action {
  return unsignedAction(target, symbol(method), effects);
}

// ─────────────────────────────────────────────────────────────────────────────
// Postcard encoding
// ─────────────────────────────────────────────────────────────────────────────

class Writer {
  private parts: number[] = [];

  u8(v: number): this {
    this.parts.push(v & 0xff);
    return this;
  }

  bytes(b: Uint8Array): this {
    for (const x of b) this.parts.push(x);
    return this;
  }

  /** Unsigned LEB128 varint (postcard's u16/u32/u64/usize encoding). */
  varint(v: number | bigint): this {
    let n = BigInt(v);
    if (n < 0n) throw new Error("varint: negative");
    do {
      let byte = Number(n & 0x7fn);
      n >>= 7n;
      if (n !== 0n) byte |= 0x80;
      this.parts.push(byte);
    } while (n !== 0n);
    return this;
  }

  /** Zigzag varint (postcard's i64 encoding). */
  ivarint(v: number | bigint): this {
    const n = BigInt(v);
    return this.varint(n >= 0n ? n << 1n : ((-n) << 1n) - 1n);
  }

  /** Option discriminant + value. */
  option<T>(v: T | undefined | null, write: (v: T) => void): this {
    if (v === undefined || v === null) {
      this.u8(0);
    } else {
      this.u8(1);
      write(v);
    }
    return this;
  }

  /** Length-prefixed sequence. */
  seq<T>(items: readonly T[], write: (v: T) => void): this {
    this.varint(items.length);
    for (const it of items) write(it);
    return this;
  }

  /** Length-prefixed byte string (postcard `Vec<u8>` / serde_bytes). */
  byteSeq(b: Uint8Array): this {
    this.varint(b.length);
    return this.bytes(b);
  }

  out(): Uint8Array {
    return Uint8Array.from(this.parts);
  }
}

function writeAuthRequired(w: Writer, a: AuthRequired): void {
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

function writeCapabilityRef(w: Writer, cap: CapabilityRef): void {
  w.bytes(exactBytes(cap.target, 32, "cap.target"));
  w.varint(cap.slot);
  writeAuthRequired(w, cap.permissions);
  w.option(cap.breadstuff, (b) => w.bytes(exactBytes(b, 32, "cap.breadstuff")));
  w.option(cap.expiresAt, (e) => w.varint(e));
  // allowed_effects: not modeled on this surface, but the Rust field is
  // `#[serde(default)]` ONLY (NOT skip_serializing_if — cell/src/capability.rs)
  // so its `None` discriminant IS emitted into the non-self-describing postcard
  // stream (a skipped field cannot round-trip the durable codec). Emit it as a
  // literal `None` to stay byte-identical to the Rust serializer.
  w.u8(0);
  w.option(cap.storedEpoch, (e) => w.varint(e));
  // provenance: `[u8; 32]` carrying `#[serde(default)]` ONLY (NOT
  // skip_serializing_if — cell/src/capability.rs:133) — the IDENTICAL rule the
  // allowed_effects note above quotes — so postcard emits its 32 bytes
  // positionally, as a bare fixed array (no Option discriminant). Missing this
  // was the M30 drift: the node reads the 32 bytes following the cap as
  // provenance and desyncs. `[0u8;32]` is the unprovenanced sentinel.
  w.bytes(exactBytes(cap.provenance ?? new Uint8Array(32), 32, "cap.provenance"));
}

function writeEffect(w: Writer, e: Effect): void {
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
      w.varint(6)
        .bytes(exactBytes(e.publicKey, 32, "publicKey"))
        .bytes(exactBytes(e.tokenId, 32, "tokenId"))
        .varint(e.balance);
      break;
  }
}

function writeAuthorization(w: Writer, a: Authorization): void {
  switch (a.kind) {
    case "signature":
      // `Signature([u8; 32], [u8; 32])` — fixed-size arrays: NO length prefix.
      w.varint(0).bytes(exactBytes(a.r, 32, "sig r")).bytes(exactBytes(a.s, 32, "sig s"));
      break;
    case "hybridSignature":
      // `HybridSignature { ed25519, ml_dsa, ml_dsa_pk }`. All three are
      // LENGTH-PREFIXED seqs: `ed25519` is `[u8; 64]` but rides
      // `#[serde(with = "serde_sig64")]`, which serializes it as a *slice*
      // (`bytes.as_slice().serialize(ser)`) — so postcard emits varint(64)
      // first, exactly like the `Vec<u8>` halves. This is why it is `byteSeq`
      // and not `bytes` (which the fixed-array `Signature` case above uses).
      w.varint(10)
        .byteSeq(exactBytes(a.ed25519, 64, "hybrid ed25519"))
        .byteSeq(a.mlDsa)
        .byteSeq(a.mlDsaPk);
      break;
    case "unchecked":
      w.varint(4);
      break;
  }
}

/** Postcard bytes of the default `Preconditions` (all None / empty). */
const PRECONDITIONS_DEFAULT = Uint8Array.from([0, 0, 0, 0]);

function writeAction(w: Writer, a: Action): void {
  w.bytes(exactBytes(a.target, 32, "target"));
  w.bytes(exactBytes(a.method, 32, "method"));
  w.seq(a.args, (arg) => w.bytes(exactBytes(arg, 32, "arg")));
  writeAuthorization(w, a.authorization);
  w.bytes(PRECONDITIONS_DEFAULT);
  w.seq(a.effects, (e) => writeEffect(w, e));
  w.varint(0); // may_delegate: DelegationMode::None
  w.varint(0); // commitment_mode: CommitmentMode::Full
  w.option(a.balanceChange, (d) => w.ivarint(d));
  w.varint(0); // witness_blobs: empty
}

function writeCallTree(w: Writer, t: CallTree): void {
  writeAction(w, t.action);
  w.seq(t.children, (c) => writeCallTree(w, c));
  w.bytes(new Uint8Array(32)); // cached hash: zeros (recomputed by readers)
}

/** Postcard-encode a [`Turn`] (the `dregg_turn::Turn` wire shape). */
export function encodeTurn(t: Turn): Uint8Array {
  const w = new Writer();
  w.bytes(exactBytes(t.agent, 32, "agent"));
  w.varint(t.nonce);
  w.seq(t.roots, (r) => writeCallTree(w, r)); // call_forest.roots
  w.bytes(new Uint8Array(32)); // call_forest.forest_hash: zeros
  w.varint(t.fee);
  w.option(t.memo, (m) => w.byteSeq(utf8.encode(m)));
  w.option(t.validUntil, (v) => w.ivarint(v));
  w.option(t.previousReceiptHash, (h) => w.bytes(exactBytes(h, 32, "previousReceiptHash")));
  w.seq(t.dependsOn ?? [], (d) => w.bytes(exactBytes(d, 32, "dependsOn")));
  w.u8(0); // conservation_proof: None
  w.varint(0); // sovereign_witnesses: empty map
  w.u8(0); // execution_proof: None
  w.u8(0); // execution_proof_cell: None
  w.u8(0); // execution_proof_new_commitment: None
  w.u8(0); // custom_program_proofs: None
  w.varint(0); // effect_binding_proofs: []
  w.varint(0); // cross_effect_dependencies: []
  w.varint(0); // effect_witness_index_map: []
  return w.out();
}

/**
 * Postcard-encode the `SignedTurn` envelope the node's
 * `/api/turns/submit-signed` ingress expects:
 * `turn ++ varint(64) ++ signature ++ varint(32) ++ signer`.
 */
export function encodeSignedTurn(turn: Turn, signature: Uint8Array, signer: Uint8Array): Uint8Array {
  const w = new Writer();
  w.bytes(encodeTurn(turn));
  w.byteSeq(exactBytes(signature, 64, "signature"));
  w.byteSeq(exactBytes(signer, 32, "signer"));
  return w.out();
}

// ─────────────────────────────────────────────────────────────────────────────
// Canonical hashes (BLAKE3 preimages — byte-identical to the Rust impls)
// ─────────────────────────────────────────────────────────────────────────────

/** `Effect::hash` (turn/src/action.rs). */
export function effectHash(e: Effect): Bytes32 {
  const h = Blake3Hasher.new();
  switch (e.kind) {
    case "setField":
      h.update(Uint8Array.from([0])).update(e.cell).update(u64le(e.index)).update(e.value);
      break;
    case "transfer":
      h.update(Uint8Array.from([1])).update(e.from).update(e.to).update(u64le(e.amount));
      break;
    case "grantCapability":
      h.update(Uint8Array.from([2]))
        .update(e.from)
        .update(e.to)
        .update(e.cap.target)
        .update(u32le(e.cap.slot));
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

function authHashUpdate(h: Blake3Hasher, a: Authorization): void {
  switch (a.kind) {
    case "signature":
      h.update(Uint8Array.from([0])).update(a.r).update(a.s);
      break;
    case "hybridSignature":
      // Discriminant 10 — distinct from `Signature` (0), so a classical and a
      // hybrid authorization over the same action never collide in the action
      // hash. Binding the PQ material (signature + public key) here is what
      // makes the OUTER turn envelope's signature cover it: a tampering
      // executor cannot swap or strip the PQ half under a signed envelope.
      // NB the length prefixes here are u64-LE (`(len as u64).to_le_bytes()`),
      // NOT the postcard varints the wire encoding uses.
      h.update(Uint8Array.from([10]))
        .update(a.ed25519)
        .update(u64le(a.mlDsa.length))
        .update(a.mlDsa)
        .update(u64le(a.mlDsaPk.length))
        .update(a.mlDsaPk);
      break;
    case "unchecked":
      h.update(Uint8Array.from([3]));
      break;
  }
}

/** `Action::hash` (v2 domain, turn/src/action.rs). */
export function actionHash(a: Action): Bytes32 {
  const h = Blake3Hasher.new();
  h.update(utf8.encode("dregg-action-v2:"));
  h.update(a.target);
  h.update(a.method);
  for (const arg of a.args) h.update(arg);
  authHashUpdate(h, a.authorization);
  h.update(Uint8Array.from([0])); // may_delegate: None
  h.update(Uint8Array.from([0])); // commitment_mode: Full
  if (a.balanceChange !== undefined) {
    h.update(Uint8Array.from([1])).update(i64le(a.balanceChange));
  } else {
    h.update(Uint8Array.from([0]));
  }
  for (const e of a.effects) h.update(effectHash(e));
  h.update(PRECONDITIONS_DEFAULT);
  h.update(u64le(0)); // witness_blobs: empty (length prefix only)
  return h.finalize();
}

/**
 * `TurnExecutor::compute_signing_message` — the canonical action signing
 * preimage (`dregg-action-sig-v3`). Computed over the action with the
 * authorization field IGNORED (the Rust path zeroes it first; this preimage
 * never reads it).
 *
 * ## v3 binds the SUBMITTING turn's nonce
 *
 * v2 added the federation binding; **v3 added `turn_nonce`** (the Full-
 * commitment replay closure). `turnNonce` MUST be the nonce of the turn this
 * action will ride — the executor recomputes this preimage over
 * `turn.nonce` and rejects the signature otherwise. It is a REQUIRED
 * parameter, not a defaulted one, precisely because a silently-wrong nonce
 * produces a signature that verifies nowhere.
 */
export function actionSigningMessage(
  a: Action,
  federationId: Uint8Array,
  turnNonce: bigint | number,
): Bytes32 {
  const h = Blake3Hasher.new();
  h.update(utf8.encode("dregg-action-sig-v3:"));
  h.update(exactBytes(federationId, 32, "federationId"));
  h.update(u64le(turnNonce));
  h.update(a.target);
  h.update(a.method);
  for (const arg of a.args) h.update(arg);
  for (const e of a.effects) h.update(effectHash(e));
  h.update(Uint8Array.from([0])); // may_delegate: None
  h.update(Uint8Array.from([0])); // commitment_mode: Full
  if (a.balanceChange !== undefined) {
    h.update(Uint8Array.from([1])).update(i64le(a.balanceChange));
  } else {
    h.update(Uint8Array.from([0]));
  }
  h.update(PRECONDITIONS_DEFAULT);
  return h.finalize();
}

function treeHash(t: CallTree): Bytes32 {
  const a = actionHash(t.action);
  let children: Bytes32;
  if (t.children.length === 0) {
    children = new Uint8Array(32);
  } else {
    const h = Blake3Hasher.new();
    for (const c of t.children) h.update(treeHash(c));
    children = h.finalize();
  }
  return Blake3Hasher.new().update(a).update(children).finalize();
}

/** `CallForest::compute_hash` (turn/src/forest.rs). */
export function forestHash(roots: CallTree[]): Bytes32 {
  if (roots.length === 0) return new Uint8Array(32);
  const h = Blake3Hasher.new();
  for (const r of roots) h.update(treeHash(r));
  return h.finalize();
}

/** `Turn::hash` (v3 domain, turn/src/turn.rs) for default-bundle turns. */
export function turnHash(t: Turn): Bytes32 {
  const h = Blake3Hasher.new();
  h.update(utf8.encode("dregg-turn-v3:"));
  h.update(t.agent);
  h.update(u64le(t.nonce));
  h.update(forestHash(t.roots));
  h.update(u64le(t.fee));
  if (t.memo !== undefined) {
    const m = utf8.encode(t.memo);
    h.update(Uint8Array.from([1])).update(u64le(m.length)).update(m);
  } else {
    h.update(Uint8Array.from([0]));
  }
  if (t.validUntil !== undefined) {
    h.update(Uint8Array.from([1])).update(i64le(t.validUntil));
  } else {
    h.update(Uint8Array.from([0]));
  }
  const deps = t.dependsOn ?? [];
  h.update(u64le(deps.length));
  for (const d of deps) h.update(d);
  if (t.previousReceiptHash !== undefined) {
    h.update(Uint8Array.from([1])).update(t.previousReceiptHash);
  } else {
    h.update(Uint8Array.from([0]));
  }
  // v3 proof-bundle fields, all at their defaults:
  h.update(Uint8Array.from([0])); // execution_proof: None
  h.update(Uint8Array.from([0])); // execution_proof_cell: None
  h.update(Uint8Array.from([0])); // execution_proof_new_commitment: None
  h.update(u64le(0)); // sovereign_witnesses: empty
  h.update(Uint8Array.from([0])); // custom_program_proofs: None
  // binding extensions all empty → no presence byte (byte-identity rule).
  return h.finalize();
}

/** Hex of a turn hash (the `turn_id` the node logs / indexes by). */
export function turnHashHex(t: Turn): string {
  return hexEncode(turnHash(t));
}

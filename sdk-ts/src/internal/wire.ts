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
 * Effects modeled: ALL 34 variants of the Rust `Effect` enum
 * (`turn/src/action.rs`, declaration indexes 0..=33 — count verified against
 * the enum body, NOT a comment). The postcard variant indexes here are the
 * Rust declaration indexes, which are append-only by contract (`Mint` and
 * later variants carry explicit APPENDED-LAST notes in action.rs).
 *
 * KEEPING THE COUNT IN SYNC: the per-variant differential in
 * `test/wire-effects.test.mjs` drives every kind below through the wasm
 * oracle (`sign_turn_v3` re-encodes with the REAL Rust postcard and the REAL
 * `Turn::hash`), so a new Rust variant shows up as a missing kind here the
 * moment someone models it — and the `EFFECT_KIND_COUNT` export is asserted
 * against the modeled union so this header cannot silently understate again.
 *
 * Named sub-gaps (modeled shallowly, REFUSED loudly rather than encoded
 * wrongly — see `UnmodeledWireError`):
 *   - `SetProgram` accepts `CellProgram::{None, Predicate, Circuit}`;
 *     `Cases` (TransitionCase guards) is not modeled.
 *   - `React`'s `ConditionProof::Receipt` (a full `TurnReceipt`) is not
 *     modeled; `Preimage` and `StarkProof` are.
 *   - Nested `wake` turns (`Promise`/`Notify`/`React`) are the same
 *     default-proof-bundle `Turn` shape `encodeTurn` supports.
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
import type { StateConstraint as ProgramStateConstraint } from "../program";
import { encodeConstraints } from "../program";

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

/** Refusal to encode a shape this surface does not model (never wrong bytes). */
export class UnmodeledWireError extends Error {
  constructor(what: string) {
    super(`unmodeled wire shape: ${what} — refuse to guess the postcard bytes`);
    this.name = "UnmodeledWireError";
  }
}

/** `dregg_cell::Permissions` — 8 `AuthRequired` fields, declaration order. */
export interface Permissions {
  send: AuthRequired;
  receive: AuthRequired;
  setState: AuthRequired;
  setPermissions: AuthRequired;
  setVerificationKey: AuthRequired;
  incrementNonce: AuthRequired;
  delegate: AuthRequired;
  access: AuthRequired;
}

/** `dregg_cell::VerificationKey` (`hash` + opaque `data`). */
export interface VerificationKey {
  hash: Bytes32;
  data: Uint8Array;
}

/**
 * `dregg_cell::CellProgram` (postcard: None=0, Predicate=1, Cases=2,
 * Circuit=3). `Cases` is NOT modeled (TransitionCase guards); `predicate`
 * carries the `StateConstraint` subset `../program` models, encoded by its
 * `encodeConstraints` (the same bytes `canonical_program_vk` addresses).
 */
export type CellProgram =
  | { kind: "none" }
  | { kind: "predicate"; constraints: ProgramStateConstraint[] }
  | { kind: "circuit"; circuitHash: Bytes32 };

/** `dregg_turn::eventual::EventualRef`. `federation_id` is ALWAYS serialized
 * (the Rust field is `#[serde(default)]` only — the Option discriminant is
 * emitted into the positional postcard stream). */
export interface EventualRef {
  sourceTurn: Bytes32;
  outputSlot: number;
  federationId?: Bytes32;
}

/** `dregg_turn::action::RefusalReason` (postcard: 0..=3). */
export type RefusalReason =
  | { kind: "declined" }
  | { kind: "noAuthority" }
  | { kind: "windowExpired" }
  | { kind: "custom"; reasonHash: Bytes32 };

/** `dregg_cell::lifecycle::DeathReason` (postcard: 0..=3). */
export type DeathReason =
  | { kind: "voluntary" }
  | { kind: "forced" }
  | { kind: "migrated" }
  | { kind: "custom"; reasonHash: Bytes32 };

/** `dregg_cell::lifecycle::DeathCertificate`. */
export interface DeathCertificate {
  cellId: CellId;
  lastReceiptHash: Bytes32;
  finalStateCommitment: Bytes32;
  destroyedAtHeight: number | bigint;
  reason: DeathReason;
}

/** `dregg_cell::lifecycle::ArchivalAttestation`. */
export interface ArchivalAttestation {
  cellId: CellId;
  archiveStartHeight: number | bigint;
  archiveEndHeight: number | bigint;
  archiveBlobHash: Bytes32;
  archiveTerminalCommitment: Bytes32;
  archiveTerminalReceiptHash: Bytes32;
}

/** `dregg_cell::factory::CapTarget` (postcard: SelfCell=0, Specific=1, Any=2). */
export type CapTarget =
  | { kind: "selfCell" }
  | { kind: "specific"; cell: CellId }
  | { kind: "any" };

/** `dregg_cell::factory::CapGrant`. */
export interface CapGrant {
  target: CapTarget;
  maxPermissions: AuthRequired;
  attenuatable: boolean;
}

/** `dregg_cell::CellMode` (postcard: Hosted=0, Sovereign=1). */
export type CellMode = "hosted" | "sovereign";

/** `dregg_cell::factory::FactoryCreationParams`. */
export interface FactoryCreationParams {
  mode: CellMode;
  programVk?: Bytes32;
  /** `(field_index, value)` pairs. */
  initialFields: Array<[number, number | bigint]>;
  initialCaps: CapGrant[];
  ownerPubkey: Bytes32;
}

/** `dregg_types::HybridQuorumSig` (pubkey/signature ride `serde_32`/`serde_64`
 * = SLICES, so postcard length-prefixes them — unlike bare `[u8; N]`). */
export interface HybridQuorumSig {
  pubkey: Bytes32;
  signature: Uint8Array; // 64 bytes
  mlDsaPubkey: Uint8Array;
  pqSignature: Uint8Array;
}

/** `dregg_types::AttestedRoot` — full declaration-order mirror. The
 * `#[serde(default)]` Options in the middle still EMIT their discriminant in
 * postcard (positional codec); `federation_id` is a bare `[u8; 32]` newtype
 * (no length prefix), while `PublicKey`/`Signature` are serde_32/serde_64
 * slices (length-prefixed). */
export interface AttestedRoot {
  merkleRoot: Bytes32;
  noteTreeRoot?: Bytes32;
  nullifierSetRoot?: Bytes32;
  height: number | bigint;
  timestamp: number | bigint; // i64 (zigzag varint on the wire)
  blocklaceBlockId?: Bytes32;
  finalityRound?: number | bigint;
  /** `(PublicKey, Signature)` pairs. */
  quorumSignatures: Array<[Bytes32, Uint8Array]>;
  thresholdQc?: Uint8Array; // ThresholdQC(Vec<u8>)
  threshold: number;
  federationId: Bytes32;
  receiptStreamRoot?: Bytes32;
  hybridQuorum: HybridQuorumSig[];
}

/** `dregg_cell_crypto::note_bridge::PortableNoteProof`. */
export interface PortableNoteProof {
  nullifier: Bytes32;
  destinationFederation: Bytes32;
  sourceRoot: AttestedRoot;
  spendingProof: Uint8Array;
  destinationCommitment: Bytes32;
  value: number | bigint;
  assetType: number | bigint;
}

/** `dregg_turn::pending::ResolutionCondition` (postcard: 0..=2). */
export type ResolutionCondition =
  | { kind: "awaitReceipt"; turnHash: Bytes32; federationId?: Bytes32 }
  | { kind: "awaitCondition"; condition: ProofCondition }
  | { kind: "awaitHeight"; height: number | bigint };

/** `dregg_turn::conditional::ProofCondition` (postcard: 0..=3). */
export type ProofCondition =
  | { kind: "hashPreimage"; hash: Bytes32 }
  | { kind: "remoteProof"; federationRoot: Bytes32; expectedAir: string; expectedConclusion: number }
  | { kind: "localProof"; expectedAir: string; expectedPublicInputs: number[] }
  | { kind: "turnExecuted"; turnHash: Bytes32 };

/** `dregg_turn::conditional::ConditionProof` (postcard: Preimage=0,
 * StarkProof=1, Receipt=2). `Receipt` (a full `TurnReceipt`) is NOT modeled. */
export type ConditionProof =
  | { kind: "preimage"; preimage: Bytes32 }
  | {
      kind: "starkProof";
      proofBytes: Uint8Array;
      federationRoot: Bytes32;
      publicOutputs: number[];
      airName: string;
    };

/** `dregg_turn::action::ShieldedLeg`. */
export interface ShieldedLeg {
  assetType: number | bigint;
  commitmentBytes: Bytes32;
}

/** `dregg_turn::action::ShieldedInputPayload` (u32 felts + proof blob). */
export interface ShieldedInputPayload {
  nullifier: number;
  valueBinding: number;
  proof: Uint8Array;
}

/** `dregg_cell_crypto::ConservationProof` (3 × 32 bytes). */
export interface ConservationProof {
  excessCommitment: Bytes32;
  nonceCommitment: Bytes32;
  response: Bytes32;
}

/** `dregg_turn::action::ShieldedTransferPayload`. */
export interface ShieldedTransferPayload {
  merkleRoot: number;
  inputs: ShieldedInputPayload[];
  inputLegs: ShieldedLeg[];
  outputLegs: ShieldedLeg[];
  outputRangeProofs: Uint8Array[];
  conservation: ConservationProof;
}

/**
 * ALL 34 `Effect` variants (Rust declaration indexes in comments — these are
 * the postcard variant indexes; field order matches the Rust declaration
 * exactly, camel-cased per this file's convention).
 */
export type Effect =
  | { kind: "setField"; cell: CellId; index: number; value: Bytes32 } // 0
  | { kind: "transfer"; from: CellId; to: CellId; amount: number | bigint } // 1
  | { kind: "grantCapability"; from: CellId; to: CellId; cap: CapabilityRef } // 2
  | { kind: "revokeCapability"; cell: CellId; slot: number } // 3
  | { kind: "emitEvent"; cell: CellId; topic: Bytes32; data: Bytes32[] } // 4
  | { kind: "incrementNonce"; cell: CellId } // 5
  | { kind: "createCell"; publicKey: Bytes32; tokenId: Bytes32; balance: number | bigint } // 6
  | { kind: "setPermissions"; cell: CellId; newPermissions: Permissions } // 7
  | { kind: "setVerificationKey"; cell: CellId; newVk?: VerificationKey } // 8
  | { kind: "setProgram"; cell: CellId; program: CellProgram } // 9
  | {
      kind: "noteSpend"; // 10
      nullifier: Bytes32;
      noteTreeRoot: Bytes32;
      value: number | bigint;
      assetType: number | bigint;
      spendingProof: Uint8Array;
      valueCommitment?: Bytes32;
    }
  | {
      kind: "noteCreate"; // 11
      commitment: Bytes32;
      value: number | bigint;
      assetType: number | bigint;
      encryptedNote: Uint8Array;
      valueCommitment?: Bytes32;
      rangeProof?: Uint8Array;
    }
  | {
      kind: "spawnWithDelegation"; // 12
      childPublicKey: Bytes32;
      childTokenId: Bytes32;
      maxStaleness: number | bigint;
    }
  | { kind: "refreshDelegation"; child: CellId; snapshot: Bytes32 } // 13
  | { kind: "revokeDelegation"; child: CellId } // 14
  | { kind: "bridgeMint"; portableProof: PortableNoteProof } // 15
  | {
      kind: "introduce"; // 16
      introducer: CellId;
      recipient: CellId;
      target: CellId;
      permissions: AuthRequired;
    }
  | { kind: "pipelinedSend"; target: EventualRef; action: Action } // 17
  | { kind: "exerciseViaCapability"; capSlot: number; innerEffects: Effect[] } // 18
  | { kind: "makeSovereign"; cell: CellId } // 19
  | {
      kind: "createCellFromFactory"; // 20
      factoryVk: Bytes32;
      ownerPubkey: Bytes32;
      tokenId: Bytes32;
      params: FactoryCreationParams;
    }
  | {
      kind: "refusal"; // 21
      cell: CellId;
      offeredActionCommitment: Bytes32;
      refusalReason: RefusalReason;
      proofWitnessIndex: number;
    }
  | { kind: "cellSeal"; target: CellId; reason: Bytes32 } // 22
  | { kind: "cellUnseal"; target: CellId } // 23
  | { kind: "cellDestroy"; target: CellId; certificate: DeathCertificate } // 24
  | { kind: "burn"; target: CellId; slot: number; amount: number | bigint } // 25
  | {
      kind: "attenuateCapability"; // 26
      cell: CellId;
      slot: number;
      narrowerPermissions: AuthRequired;
      narrowerEffects?: number; // EffectMask = u32
      narrowerExpiry?: number | bigint;
    }
  | {
      kind: "receiptArchive"; // 27
      prefixEndHeight: number | bigint;
      checkpoint: ArchivalAttestation;
    }
  | {
      kind: "promise"; // 28
      cell: CellId;
      resolutionCondition: ResolutionCondition;
      wake: Turn;
      timeoutHeight: number | bigint;
    }
  | {
      kind: "notify"; // 29
      from: CellId;
      to: CellId;
      wake: Turn;
      resolutionCondition: ResolutionCondition;
      timeoutHeight: number | bigint;
    }
  | {
      kind: "react"; // 30
      pendingId: Bytes32;
      condition: ProofCondition;
      resolutionProof: ConditionProof;
      wake: Turn;
    }
  | { kind: "mint"; target: CellId; slot: number; amount: number | bigint } // 31
  | { kind: "shieldedTransfer"; payload: ShieldedTransferPayload } // 32
  | { kind: "custom"; cell: CellId; programVkHash: Bytes32; proofCommitment: Bytes32 }; // 33

/** The modeled Effect-kind count, asserted by the wire tests against the Rust
 * enum's variant count (34) so the header can never silently understate. */
export const EFFECT_KIND_COUNT = 34;

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

function writePermissions(w: Writer, p: Permissions): void {
  // dregg_cell::Permissions — 8 AuthRequired fields in declaration order.
  writeAuthRequired(w, p.send);
  writeAuthRequired(w, p.receive);
  writeAuthRequired(w, p.setState);
  writeAuthRequired(w, p.setPermissions);
  writeAuthRequired(w, p.setVerificationKey);
  writeAuthRequired(w, p.incrementNonce);
  writeAuthRequired(w, p.delegate);
  writeAuthRequired(w, p.access);
}

function writeCellProgram(w: Writer, p: CellProgram): void {
  switch (p.kind) {
    case "none":
      w.varint(0);
      break;
    case "predicate":
      // Predicate(Vec<StateConstraint>) — the Vec bytes are exactly
      // `encodeConstraints` (varint len + constraints), the same postcard
      // `canonical_program_vk` addresses.
      w.varint(1).bytes(encodeConstraints(p.constraints));
      break;
    case "circuit":
      // Cases = 2 is unmodeled; Circuit is declaration index 3.
      w.varint(3).bytes(exactBytes(p.circuitHash, 32, "circuitHash"));
      break;
    default:
      // JS callers can bypass the type system; never emit guessed bytes.
      throw new UnmodeledWireError(`CellProgram kind ${String((p as { kind?: string }).kind)}`);
  }
}

function writeEventualRef(w: Writer, r: EventualRef): void {
  w.bytes(exactBytes(r.sourceTurn, 32, "sourceTurn")).varint(r.outputSlot);
  // federation_id: #[serde(default)] ONLY — the Option discriminant IS emitted.
  w.option(r.federationId, (f) => w.bytes(exactBytes(f, 32, "eventual federationId")));
}

function writeRefusalReason(w: Writer, r: RefusalReason): void {
  switch (r.kind) {
    case "declined":
      w.varint(0);
      break;
    case "noAuthority":
      w.varint(1);
      break;
    case "windowExpired":
      w.varint(2);
      break;
    case "custom":
      w.varint(3).bytes(exactBytes(r.reasonHash, 32, "refusal reasonHash"));
      break;
  }
}

function writeDeathReason(w: Writer, r: DeathReason): void {
  switch (r.kind) {
    case "voluntary":
      w.varint(0);
      break;
    case "forced":
      w.varint(1);
      break;
    case "migrated":
      w.varint(2);
      break;
    case "custom":
      w.varint(3).bytes(exactBytes(r.reasonHash, 32, "death reasonHash"));
      break;
  }
}

function writeDeathCertificate(w: Writer, c: DeathCertificate): void {
  w.bytes(exactBytes(c.cellId, 32, "cert cellId"))
    .bytes(exactBytes(c.lastReceiptHash, 32, "lastReceiptHash"))
    .bytes(exactBytes(c.finalStateCommitment, 32, "finalStateCommitment"))
    .varint(c.destroyedAtHeight);
  writeDeathReason(w, c.reason);
}

function writeArchivalAttestation(w: Writer, a: ArchivalAttestation): void {
  w.bytes(exactBytes(a.cellId, 32, "attestation cellId"))
    .varint(a.archiveStartHeight)
    .varint(a.archiveEndHeight)
    .bytes(exactBytes(a.archiveBlobHash, 32, "archiveBlobHash"))
    .bytes(exactBytes(a.archiveTerminalCommitment, 32, "archiveTerminalCommitment"))
    .bytes(exactBytes(a.archiveTerminalReceiptHash, 32, "archiveTerminalReceiptHash"));
}

function writeCapGrant(w: Writer, g: CapGrant): void {
  switch (g.target.kind) {
    case "selfCell":
      w.varint(0);
      break;
    case "specific":
      w.varint(1).bytes(exactBytes(g.target.cell, 32, "capTarget cell"));
      break;
    case "any":
      w.varint(2);
      break;
  }
  writeAuthRequired(w, g.maxPermissions);
  w.u8(g.attenuatable ? 1 : 0);
}

function writeFactoryCreationParams(w: Writer, p: FactoryCreationParams): void {
  w.varint(p.mode === "hosted" ? 0 : 1);
  w.option(p.programVk, (vk) => w.bytes(exactBytes(vk, 32, "programVk")));
  w.seq(p.initialFields, ([idx, val]) => w.varint(idx).varint(val));
  w.seq(p.initialCaps, (g) => writeCapGrant(w, g));
  w.bytes(exactBytes(p.ownerPubkey, 32, "params ownerPubkey"));
}

function writeAttestedRoot(w: Writer, r: AttestedRoot): void {
  w.bytes(exactBytes(r.merkleRoot, 32, "merkleRoot"));
  w.option(r.noteTreeRoot, (x) => w.bytes(exactBytes(x, 32, "noteTreeRoot")));
  w.option(r.nullifierSetRoot, (x) => w.bytes(exactBytes(x, 32, "nullifierSetRoot")));
  w.varint(r.height);
  w.ivarint(r.timestamp); // i64 → zigzag
  w.option(r.blocklaceBlockId, (x) => w.bytes(exactBytes(x, 32, "blocklaceBlockId")));
  w.option(r.finalityRound, (x) => w.varint(x));
  // Vec<(PublicKey, Signature)> — both ride serde_32/serde_64 (SLICES), so
  // each is length-prefixed, unlike a bare [u8; N].
  w.seq(r.quorumSignatures, ([pk, sig]) => {
    w.byteSeq(exactBytes(pk, 32, "quorum pubkey"));
    w.byteSeq(exactBytes(sig, 64, "quorum signature"));
  });
  w.option(r.thresholdQc, (qc) => w.byteSeq(qc)); // ThresholdQC(Vec<u8>)
  w.varint(r.threshold); // usize
  w.bytes(exactBytes(r.federationId, 32, "federationId")); // bare [u8;32] newtype
  w.option(r.receiptStreamRoot, (x) => w.bytes(exactBytes(x, 32, "receiptStreamRoot")));
  w.seq(r.hybridQuorum, (h) => {
    w.byteSeq(exactBytes(h.pubkey, 32, "hybrid pubkey"));
    w.byteSeq(exactBytes(h.signature, 64, "hybrid signature"));
    w.byteSeq(h.mlDsaPubkey);
    w.byteSeq(h.pqSignature);
  });
}

function writePortableNoteProof(w: Writer, p: PortableNoteProof): void {
  w.bytes(exactBytes(p.nullifier, 32, "portable nullifier"));
  w.bytes(exactBytes(p.destinationFederation, 32, "destinationFederation"));
  writeAttestedRoot(w, p.sourceRoot);
  w.byteSeq(p.spendingProof);
  w.bytes(exactBytes(p.destinationCommitment, 32, "destinationCommitment"));
  w.varint(p.value).varint(p.assetType);
}

function writeProofCondition(w: Writer, c: ProofCondition): void {
  switch (c.kind) {
    case "hashPreimage":
      w.varint(0).bytes(exactBytes(c.hash, 32, "preimage hash"));
      break;
    case "remoteProof":
      w.varint(1)
        .bytes(exactBytes(c.federationRoot, 32, "federationRoot"))
        .byteSeq(utf8.encode(c.expectedAir))
        .varint(c.expectedConclusion);
      break;
    case "localProof":
      w.varint(2).byteSeq(utf8.encode(c.expectedAir));
      w.seq(c.expectedPublicInputs, (pi) => w.varint(pi));
      break;
    case "turnExecuted":
      w.varint(3).bytes(exactBytes(c.turnHash, 32, "turnHash"));
      break;
  }
}

function writeResolutionCondition(w: Writer, c: ResolutionCondition): void {
  switch (c.kind) {
    case "awaitReceipt":
      w.varint(0).bytes(exactBytes(c.turnHash, 32, "await turnHash"));
      w.option(c.federationId, (f) => w.bytes(exactBytes(f, 32, "await federationId")));
      break;
    case "awaitCondition":
      w.varint(1);
      writeProofCondition(w, c.condition);
      break;
    case "awaitHeight":
      w.varint(2).varint(c.height);
      break;
  }
}

function writeConditionProof(w: Writer, p: ConditionProof): void {
  switch (p.kind) {
    case "preimage":
      // Preimage([u8; 32]) — newtype of a fixed array: NO length prefix.
      w.varint(0).bytes(exactBytes(p.preimage, 32, "preimage"));
      break;
    case "starkProof":
      w.varint(1).byteSeq(p.proofBytes).bytes(exactBytes(p.federationRoot, 32, "stark federationRoot"));
      w.seq(p.publicOutputs, (o) => w.varint(o));
      w.byteSeq(utf8.encode(p.airName));
      break;
    default:
      // ConditionProof::Receipt (postcard 2) is unmodeled — refuse, never guess.
      throw new UnmodeledWireError(`ConditionProof kind ${String((p as { kind?: string }).kind)}`);
  }
}

function writeShieldedPayload(w: Writer, p: ShieldedTransferPayload): void {
  w.varint(p.merkleRoot);
  w.seq(p.inputs, (i) => {
    w.varint(i.nullifier).varint(i.valueBinding).byteSeq(i.proof);
  });
  w.seq(p.inputLegs, (l) => {
    w.varint(l.assetType).bytes(exactBytes(l.commitmentBytes, 32, "input leg commitment"));
  });
  w.seq(p.outputLegs, (l) => {
    w.varint(l.assetType).bytes(exactBytes(l.commitmentBytes, 32, "output leg commitment"));
  });
  w.seq(p.outputRangeProofs, (rp) => w.byteSeq(rp));
  w.bytes(exactBytes(p.conservation.excessCommitment, 32, "excessCommitment"));
  w.bytes(exactBytes(p.conservation.nonceCommitment, 32, "nonceCommitment"));
  w.bytes(exactBytes(p.conservation.response, 32, "conservation response"));
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
    case "setPermissions":
      w.varint(7).bytes(exactBytes(e.cell, 32, "cell"));
      writePermissions(w, e.newPermissions);
      break;
    case "setVerificationKey":
      w.varint(8).bytes(exactBytes(e.cell, 32, "cell"));
      w.option(e.newVk, (vk) => {
        w.bytes(exactBytes(vk.hash, 32, "vk hash")).byteSeq(vk.data);
      });
      break;
    case "setProgram":
      w.varint(9).bytes(exactBytes(e.cell, 32, "cell"));
      writeCellProgram(w, e.program);
      break;
    case "noteSpend":
      w.varint(10)
        .bytes(exactBytes(e.nullifier, 32, "nullifier"))
        .bytes(exactBytes(e.noteTreeRoot, 32, "noteTreeRoot"))
        .varint(e.value)
        .varint(e.assetType)
        .byteSeq(e.spendingProof);
      w.option(e.valueCommitment, (vc) => w.bytes(exactBytes(vc, 32, "valueCommitment")));
      break;
    case "noteCreate":
      w.varint(11)
        .bytes(exactBytes(e.commitment, 32, "commitment"))
        .varint(e.value)
        .varint(e.assetType)
        .byteSeq(e.encryptedNote);
      w.option(e.valueCommitment, (vc) => w.bytes(exactBytes(vc, 32, "valueCommitment")));
      w.option(e.rangeProof, (rp) => w.byteSeq(rp));
      break;
    case "spawnWithDelegation":
      w.varint(12)
        .bytes(exactBytes(e.childPublicKey, 32, "childPublicKey"))
        .bytes(exactBytes(e.childTokenId, 32, "childTokenId"))
        .varint(e.maxStaleness);
      break;
    case "refreshDelegation":
      w.varint(13).bytes(exactBytes(e.child, 32, "child")).bytes(exactBytes(e.snapshot, 32, "snapshot"));
      break;
    case "revokeDelegation":
      w.varint(14).bytes(exactBytes(e.child, 32, "child"));
      break;
    case "bridgeMint":
      w.varint(15);
      writePortableNoteProof(w, e.portableProof);
      break;
    case "introduce":
      w.varint(16)
        .bytes(exactBytes(e.introducer, 32, "introducer"))
        .bytes(exactBytes(e.recipient, 32, "recipient"))
        .bytes(exactBytes(e.target, 32, "target"));
      writeAuthRequired(w, e.permissions);
      break;
    case "pipelinedSend":
      w.varint(17);
      writeEventualRef(w, e.target);
      writeAction(w, e.action); // Box<Action> — postcard boxes are transparent
      break;
    case "exerciseViaCapability":
      w.varint(18).varint(e.capSlot);
      w.seq(e.innerEffects, (inner) => writeEffect(w, inner));
      break;
    case "makeSovereign":
      w.varint(19).bytes(exactBytes(e.cell, 32, "cell"));
      break;
    case "createCellFromFactory":
      w.varint(20)
        .bytes(exactBytes(e.factoryVk, 32, "factoryVk"))
        .bytes(exactBytes(e.ownerPubkey, 32, "ownerPubkey"))
        .bytes(exactBytes(e.tokenId, 32, "tokenId"));
      writeFactoryCreationParams(w, e.params);
      break;
    case "refusal":
      w.varint(21)
        .bytes(exactBytes(e.cell, 32, "cell"))
        .bytes(exactBytes(e.offeredActionCommitment, 32, "offeredActionCommitment"));
      writeRefusalReason(w, e.refusalReason);
      w.varint(e.proofWitnessIndex);
      break;
    case "cellSeal":
      w.varint(22).bytes(exactBytes(e.target, 32, "target")).bytes(exactBytes(e.reason, 32, "reason"));
      break;
    case "cellUnseal":
      w.varint(23).bytes(exactBytes(e.target, 32, "target"));
      break;
    case "cellDestroy":
      w.varint(24).bytes(exactBytes(e.target, 32, "target"));
      writeDeathCertificate(w, e.certificate);
      break;
    case "burn":
      w.varint(25).bytes(exactBytes(e.target, 32, "target")).varint(e.slot).varint(e.amount);
      break;
    case "attenuateCapability":
      w.varint(26).bytes(exactBytes(e.cell, 32, "cell")).varint(e.slot);
      writeAuthRequired(w, e.narrowerPermissions);
      w.option(e.narrowerEffects, (m) => w.varint(m));
      w.option(e.narrowerExpiry, (x) => w.varint(x));
      break;
    case "receiptArchive":
      w.varint(27).varint(e.prefixEndHeight);
      writeArchivalAttestation(w, e.checkpoint);
      break;
    case "promise":
      w.varint(28).bytes(exactBytes(e.cell, 32, "cell"));
      writeResolutionCondition(w, e.resolutionCondition);
      w.bytes(encodeTurn(e.wake)); // Box<Turn> — nested struct = same bytes inline
      w.varint(e.timeoutHeight);
      break;
    case "notify":
      w.varint(29).bytes(exactBytes(e.from, 32, "from")).bytes(exactBytes(e.to, 32, "to"));
      w.bytes(encodeTurn(e.wake));
      writeResolutionCondition(w, e.resolutionCondition);
      w.varint(e.timeoutHeight);
      break;
    case "react":
      w.varint(30).bytes(exactBytes(e.pendingId, 32, "pendingId"));
      writeProofCondition(w, e.condition);
      writeConditionProof(w, e.resolutionProof);
      w.bytes(encodeTurn(e.wake));
      break;
    case "mint":
      w.varint(31).bytes(exactBytes(e.target, 32, "target")).varint(e.slot).varint(e.amount);
      break;
    case "shieldedTransfer":
      w.varint(32);
      writeShieldedPayload(w, e.payload);
      break;
    case "custom":
      w.varint(33)
        .bytes(exactBytes(e.cell, 32, "cell"))
        .bytes(exactBytes(e.programVkHash, 32, "programVkHash"))
        .bytes(exactBytes(e.proofCommitment, 32, "proofCommitment"));
      break;
    default:
      throw new UnmodeledWireError(`Effect kind ${String((e as { kind?: string }).kind)}`);
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

/** `hash_auth_required` (turn/src/action.rs) — discriminant byte, plus the
 * vk_hash bytes for `Custom`. */
function authRequiredHashUpdate(h: Blake3Hasher, a: AuthRequired): void {
  switch (a.kind) {
    case "none":
      h.update(Uint8Array.from([0]));
      break;
    case "signature":
      h.update(Uint8Array.from([1]));
      break;
    case "proof":
      h.update(Uint8Array.from([2]));
      break;
    case "either":
      h.update(Uint8Array.from([3]));
      break;
    case "impossible":
      h.update(Uint8Array.from([4]));
      break;
    case "custom":
      h.update(Uint8Array.from([5])).update(exactBytes(a.vkHash, 32, "vkHash"));
      break;
  }
}

/** Postcard bytes of a sub-structure, via the same writers the wire uses. */
function postcardOf(write: (w: Writer) => void): Uint8Array {
  const w = new Writer();
  write(w);
  return w.out();
}

/** `DeathCertificate::certificate_hash` (cell/src/lifecycle.rs). */
export function deathCertificateHash(c: DeathCertificate): Bytes32 {
  const parts: Uint8Array[] = [
    exactBytes(c.cellId, 32, "cert cellId"),
    exactBytes(c.lastReceiptHash, 32, "lastReceiptHash"),
    exactBytes(c.finalStateCommitment, 32, "finalStateCommitment"),
    u64le(c.destroyedAtHeight),
  ];
  switch (c.reason.kind) {
    case "voluntary":
      parts.push(Uint8Array.from([0]));
      break;
    case "forced":
      parts.push(Uint8Array.from([1]));
      break;
    case "migrated":
      parts.push(Uint8Array.from([2]));
      break;
    case "custom":
      parts.push(Uint8Array.from([3]), exactBytes(c.reason.reasonHash, 32, "reasonHash"));
      break;
  }
  return blake3DeriveKey("dregg-cell:death-certificate v1", concatBytes(...parts));
}

/** `ArchivalAttestation::checkpoint_hash` (cell/src/lifecycle.rs). */
export function archivalCheckpointHash(a: ArchivalAttestation): Bytes32 {
  return blake3DeriveKey(
    "dregg-cell:archival-attestation v1",
    concatBytes(
      exactBytes(a.cellId, 32, "attestation cellId"),
      u64le(a.archiveStartHeight),
      u64le(a.archiveEndHeight),
      exactBytes(a.archiveBlobHash, 32, "archiveBlobHash"),
      exactBytes(a.archiveTerminalCommitment, 32, "archiveTerminalCommitment"),
      exactBytes(a.archiveTerminalReceiptHash, 32, "archiveTerminalReceiptHash"),
    ),
  );
}

/**
 * `Effect::hash` (turn/src/action.rs). The domain-tag bytes mirror the Rust
 * match EXACTLY — they are hand-assigned there and NOT the postcard variant
 * indexes (e.g. SetProgram=54, MakeSovereign=35). NOTE (faithful mirror of a
 * Rust smell, reported in TESTQALOG 2026-07-17): `Mint` and `ShieldedTransfer`
 * BOTH use tag 63 in the Rust source; we mirror, not fix — the preimage
 * shapes differ in length so no practical collision exists today.
 */
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
    case "setPermissions": {
      h.update(Uint8Array.from([7])).update(e.cell);
      const p = e.newPermissions;
      for (const a of [
        p.send,
        p.receive,
        p.setState,
        p.setPermissions,
        p.setVerificationKey,
        p.incrementNonce,
        p.delegate,
        p.access,
      ]) {
        authRequiredHashUpdate(h, a);
      }
      break;
    }
    case "setVerificationKey":
      h.update(Uint8Array.from([8])).update(e.cell);
      if (e.newVk !== undefined) {
        h.update(Uint8Array.from([1])).update(e.newVk.data);
      } else {
        h.update(Uint8Array.from([0]));
      }
      break;
    case "setProgram":
      // [54] + cell + canonical postcard bytes of the program (no length prefix).
      h.update(Uint8Array.from([54])).update(e.cell);
      h.update(postcardOf((w) => writeCellProgram(w, e.program)));
      break;
    case "noteSpend":
      h.update(Uint8Array.from([9]))
        .update(e.nullifier)
        .update(e.noteTreeRoot)
        .update(u64le(e.value))
        .update(u64le(e.assetType))
        .update(e.spendingProof);
      if (e.valueCommitment !== undefined) {
        h.update(Uint8Array.from([1])).update(e.valueCommitment);
      } else {
        h.update(Uint8Array.from([0]));
      }
      break;
    case "noteCreate":
      h.update(Uint8Array.from([10]))
        .update(e.commitment)
        .update(u64le(e.value))
        .update(u64le(e.assetType))
        .update(u64le(e.encryptedNote.length))
        .update(e.encryptedNote);
      if (e.valueCommitment !== undefined) {
        h.update(Uint8Array.from([1])).update(e.valueCommitment);
      } else {
        h.update(Uint8Array.from([0]));
      }
      if (e.rangeProof !== undefined) {
        h.update(Uint8Array.from([1])).update(u64le(e.rangeProof.length)).update(e.rangeProof);
      } else {
        h.update(Uint8Array.from([0]));
      }
      break;
    case "bridgeMint":
      // NB the Rust hash folds only these six fields (not the federation id,
      // spending proof, or the rest of the attested root).
      h.update(Uint8Array.from([21]))
        .update(e.portableProof.nullifier)
        .update(e.portableProof.destinationCommitment)
        .update(u64le(e.portableProof.value))
        .update(u64le(e.portableProof.assetType))
        .update(e.portableProof.sourceRoot.merkleRoot)
        .update(u64le(e.portableProof.sourceRoot.height));
      break;
    case "introduce":
      h.update(Uint8Array.from([17])).update(e.introducer).update(e.recipient).update(e.target);
      authRequiredHashUpdate(h, e.permissions);
      break;
    case "pipelinedSend":
      h.update(Uint8Array.from([16]))
        .update(e.target.sourceTurn)
        .update(u32le(e.target.outputSlot))
        .update(actionHash(e.action));
      break;
    case "spawnWithDelegation":
      h.update(Uint8Array.from([18]))
        .update(e.childPublicKey)
        .update(e.childTokenId)
        .update(u64le(e.maxStaleness));
      break;
    case "refreshDelegation":
      h.update(Uint8Array.from([19])).update(e.child).update(e.snapshot);
      break;
    case "revokeDelegation":
      h.update(Uint8Array.from([20])).update(e.child);
      break;
    case "exerciseViaCapability":
      h.update(Uint8Array.from([25])).update(u32le(e.capSlot));
      for (const inner of e.innerEffects) h.update(effectHash(inner));
      break;
    case "makeSovereign":
      h.update(Uint8Array.from([35])).update(e.cell);
      break;
    case "createCellFromFactory": {
      h.update(Uint8Array.from([36])).update(e.factoryVk).update(e.ownerPubkey).update(e.tokenId);
      h.update(Uint8Array.from([e.params.mode === "hosted" ? 0 : 1]));
      if (e.params.programVk !== undefined) {
        h.update(Uint8Array.from([1])).update(e.params.programVk);
      } else {
        h.update(Uint8Array.from([0]));
      }
      h.update(u64le(e.params.initialFields.length));
      for (const [idx, val] of e.params.initialFields) {
        h.update(u32le(idx)).update(u64le(val));
      }
      h.update(u64le(e.params.initialCaps.length));
      for (const cap of e.params.initialCaps) {
        switch (cap.target.kind) {
          case "selfCell":
            h.update(Uint8Array.from([0]));
            break;
          case "specific":
            h.update(Uint8Array.from([1])).update(cap.target.cell);
            break;
          case "any":
            h.update(Uint8Array.from([2]));
            break;
        }
        authRequiredHashUpdate(h, cap.maxPermissions);
        h.update(Uint8Array.from([cap.attenuatable ? 1 : 0]));
      }
      h.update(e.params.ownerPubkey);
      break;
    }
    case "cellSeal":
      h.update(Uint8Array.from([48])).update(e.target).update(e.reason);
      break;
    case "cellUnseal":
      h.update(Uint8Array.from([49])).update(e.target);
      break;
    case "cellDestroy":
      h.update(Uint8Array.from([50])).update(e.target).update(deathCertificateHash(e.certificate));
      break;
    case "burn":
      h.update(Uint8Array.from([51])).update(e.target).update(u32le(e.slot)).update(u64le(e.amount));
      break;
    case "mint":
      // Tag 63 in Rust (collides with ShieldedTransfer's tag — mirrored, see above).
      h.update(Uint8Array.from([63])).update(e.target).update(u32le(e.slot)).update(u64le(e.amount));
      break;
    case "attenuateCapability":
      h.update(Uint8Array.from([52])).update(e.cell).update(u32le(e.slot));
      authRequiredHashUpdate(h, e.narrowerPermissions);
      if (e.narrowerEffects !== undefined) {
        h.update(Uint8Array.from([1])).update(u32le(e.narrowerEffects));
      } else {
        h.update(Uint8Array.from([0]));
      }
      if (e.narrowerExpiry !== undefined) {
        h.update(Uint8Array.from([1])).update(u64le(e.narrowerExpiry));
      } else {
        h.update(Uint8Array.from([0]));
      }
      break;
    case "receiptArchive":
      h.update(Uint8Array.from([53]))
        .update(u64le(e.prefixEndHeight))
        .update(archivalCheckpointHash(e.checkpoint));
      break;
    case "refusal":
      h.update(Uint8Array.from([47])).update(e.cell).update(e.offeredActionCommitment);
      switch (e.refusalReason.kind) {
        case "declined":
          h.update(Uint8Array.from([0]));
          break;
        case "noAuthority":
          h.update(Uint8Array.from([1]));
          break;
        case "windowExpired":
          h.update(Uint8Array.from([2]));
          break;
        case "custom":
          h.update(Uint8Array.from([3])).update(e.refusalReason.reasonHash);
          break;
      }
      h.update(u32le(e.proofWitnessIndex));
      break;
    case "promise": {
      h.update(Uint8Array.from([60])).update(e.cell);
      const rc = postcardOf((w) => writeResolutionCondition(w, e.resolutionCondition));
      h.update(u64le(rc.length)).update(rc);
      h.update(turnHash(e.wake)).update(u64le(e.timeoutHeight));
      break;
    }
    case "notify": {
      h.update(Uint8Array.from([61])).update(e.from).update(e.to).update(turnHash(e.wake));
      const rc = postcardOf((w) => writeResolutionCondition(w, e.resolutionCondition));
      h.update(u64le(rc.length)).update(rc);
      h.update(u64le(e.timeoutHeight));
      break;
    }
    case "react": {
      h.update(Uint8Array.from([62])).update(e.pendingId);
      const c = postcardOf((w) => writeProofCondition(w, e.condition));
      h.update(u64le(c.length)).update(c);
      const p = postcardOf((w) => writeConditionProof(w, e.resolutionProof));
      h.update(u64le(p.length)).update(p);
      h.update(turnHash(e.wake));
      break;
    }
    case "shieldedTransfer": {
      // Tag 63 in Rust (same byte as Mint — mirrored, see above).
      const pl = e.payload;
      h.update(Uint8Array.from([63])).update(u32le(pl.merkleRoot));
      h.update(u64le(pl.inputs.length));
      for (const input of pl.inputs) {
        h.update(u32le(input.nullifier)).update(u32le(input.valueBinding));
        h.update(u64le(input.proof.length)).update(input.proof);
      }
      const legPairs: Array<[number, ShieldedLeg[]]> = [
        [0, pl.inputLegs],
        [1, pl.outputLegs],
      ];
      for (const [tag, legs] of legPairs) {
        h.update(Uint8Array.from([tag])).update(u64le(legs.length));
        for (const leg of legs) {
          h.update(u64le(leg.assetType)).update(leg.commitmentBytes);
        }
      }
      h.update(u64le(pl.outputRangeProofs.length));
      for (const rp of pl.outputRangeProofs) {
        h.update(u64le(rp.length)).update(rp);
      }
      const cons = postcardOf((w) => {
        w.bytes(exactBytes(pl.conservation.excessCommitment, 32, "excessCommitment"))
          .bytes(exactBytes(pl.conservation.nonceCommitment, 32, "nonceCommitment"))
          .bytes(exactBytes(pl.conservation.response, 32, "response"));
      });
      h.update(u64le(cons.length)).update(cons);
      break;
    }
    case "custom":
      h.update(Uint8Array.from([64])).update(e.cell).update(e.programVkHash).update(e.proofCommitment);
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

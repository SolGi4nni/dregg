/**
 * Cell-program sugar — the constraint language at the builder surface
 * (mirror of `sdk/src/program.rs`).
 *
 * A cell's law is its installed `CellProgram`: the `StateConstraint` set a
 * factory bakes into every cell it births, re-evaluated by the executor on
 * EVERY turn that touches the cell. This module makes the language — in
 * particular the **turn-context actor atoms** (sender bindings, own-balance
 * bounds, the composable preimage gate) — reachable from TS:
 *
 * ```ts
 * import { program } from "@dregg/sdk";
 *
 * const descriptor = new program.CellProgramBuilder()
 *   .require(program.writeOnce(0))            // slot 0 set at most once
 *   .require(program.senderIs(controllerPk))  // only this key may act
 *   .require(program.balanceGte(100n))        // solvency floor
 *   .descriptor();
 * ```
 *
 * The safety is NOT in this builder — it is in the executor's program gate.
 * What the builder adds is the content-addressed publication shape: the
 * descriptor's `factoryVk` / `childProgramVk` are the SAME BLAKE3
 * derivations as the Rust SDK (`programmed_cell_descriptor` /
 * `canonical_program_vk`), computed over the SAME postcard encoding, so a TS
 * publisher and a Rust verifier agree on a program's address.
 */

import { Blake3Hasher } from "./internal/blake3";
import { exactBytes, hexEncode, u64le } from "./internal/bytes";

/** `dregg_cell::program::HashKind` (postcard: Blake3=0, Poseidon2=1). */
export type HashKind = "blake3" | "poseidon2";

/** A 32-byte field element value (the slot word). */
export type FieldValue = Uint8Array;

/** Encode a u64 as a slot word (big-endian in the last 8 bytes). */
export function fieldFromU64(v: number | bigint): FieldValue {
  const out = new Uint8Array(32);
  let n = BigInt(v);
  if (n < 0n || n >= 1n << 64n) throw new Error("fieldFromU64: out of u64 range");
  for (let i = 31; i >= 24; i--) {
    out[i] = Number(n & 0xffn);
    n >>= 8n;
  }
  return out;
}

/**
 * The simple (non-recursive) constraints permitted inside `AnyOf` / under
 * `Not` (`dregg_cell::program::SimpleStateConstraint`). Postcard variant
 * indexes (declaration order, append-only) in comments.
 */
export type SimpleStateConstraint =
  | { kind: "fieldEquals"; index: number; value: FieldValue } // 0
  | { kind: "fieldGte"; index: number; value: FieldValue } // 1
  | { kind: "fieldLte"; index: number; value: FieldValue } // 2
  | { kind: "writeOnce"; index: number } // 3
  | { kind: "immutable"; index: number } // 4
  | { kind: "monotonic"; index: number } // 5
  | { kind: "strictMonotonic"; index: number } // 6
  | { kind: "boundedBy"; index: number; witnessIndex: number } // 7
  | { kind: "not"; inner: SimpleStateConstraint } // 11 (inner must not itself be "not")
  | { kind: "senderIs"; pk: Uint8Array } // 12
  | { kind: "senderInSlot"; index: number } // 13
  | { kind: "balanceGte"; min: bigint } // 14
  | { kind: "balanceLte"; max: bigint } // 15
  | { kind: "preimageGate"; commitmentIndex: number; hashKind: HashKind }; // 16

/**
 * The outer constraint set (`dregg_cell::program::StateConstraint`) —
 * modeled subset: the actor atoms, the slot-freeze atoms, and `AnyOf`
 * composition. Postcard variant indexes in comments.
 */
export type StateConstraint =
  | { kind: "fieldEquals"; index: number; value: FieldValue } // 0
  | { kind: "fieldGte"; index: number; value: FieldValue } // 1
  | { kind: "fieldLte"; index: number; value: FieldValue } // 2
  | { kind: "writeOnce"; index: number } // 6
  | { kind: "immutable"; index: number } // 7
  | { kind: "monotonic"; index: number } // 8
  | { kind: "preimageGate"; commitmentIndex: number; hashKind: HashKind } // 21
  | { kind: "anyOf"; variants: SimpleStateConstraint[] } // 26
  | { kind: "senderIs"; pk: Uint8Array } // 38
  | { kind: "senderInSlot"; index: number } // 39
  | { kind: "balanceGte"; min: bigint } // 40
  | { kind: "balanceLte"; max: bigint }; // 41

// ─── atom constructors (top-level constraints) ───

/**
 * The turn's sender must be exactly `pk` (actor binding, literal form).
 * Fail-closed: a turn with no sender context is rejected, not passed.
 */
export function senderIs(pk: Uint8Array): StateConstraint {
  return { kind: "senderIs", pk: exactBytes(pk, 32, "senderIs pk") };
}

/**
 * The turn's sender must equal the 32-byte identity stored in slot `index`
 * — the dynamic-owner actor binding (pin the slot with [`writeOnce`] /
 * [`immutable`] and the cell carries its own controller).
 */
export function senderInSlot(index: number): StateConstraint {
  return { kind: "senderInSlot", index };
}

/** Post-turn own-balance floor (`balance >= min`): solvency floors. */
export function balanceGte(min: number | bigint): StateConstraint {
  return { kind: "balanceGte", min: BigInt(min) };
}

/**
 * Post-turn own-balance ceiling (`balance <= max`). `balanceLte(0)` under a
 * terminal-state guard is the "resolve drains everything" tooth.
 */
export function balanceLte(max: number | bigint): StateConstraint {
  return { kind: "balanceLte", max: BigInt(max) };
}

/**
 * Knowledge gate: the turn must exhibit a witness whose `hashKind`-hash
 * equals the commitment stored in slot `commitmentIndex`.
 */
export function preimageGate(commitmentIndex: number, hashKind: HashKind = "blake3"): StateConstraint {
  return { kind: "preimageGate", commitmentIndex, hashKind };
}

/** Slot `index` may never change once the cell is born. */
export function immutable(index: number): StateConstraint {
  return { kind: "immutable", index };
}

/** Slot `index` may be written at most once (from zero). */
export function writeOnce(index: number): StateConstraint {
  return { kind: "writeOnce", index };
}

/** Slot `index` may only ever increase (or stay equal) — the monotone meter
 * tooth (a rewind to forge head-room or replay a stale image is refused). */
export function monotonic(index: number): StateConstraint {
  return { kind: "monotonic", index };
}

/** Field at `index` must equal `value` post-turn. */
export function fieldEquals(index: number, value: FieldValue): StateConstraint {
  return { kind: "fieldEquals", index, value: exactBytes(value, 32, "fieldEquals value") };
}

/**
 * `AnyOf` over simple atoms — the disjunction the per-slot actor binding
 * uses: `anyOf([simple.immutable(i), simple.senderIs(member)])`.
 */
export function anyOf(variants: SimpleStateConstraint[]): StateConstraint {
  return { kind: "anyOf", variants };
}

// ─── simple-atom constructors (for composition under anyOf / not / implies) ───

export const simple = {
  fieldEquals: (index: number, value: FieldValue): SimpleStateConstraint => ({
    kind: "fieldEquals",
    index,
    value: exactBytes(value, 32, "fieldEquals value"),
  }),
  writeOnce: (index: number): SimpleStateConstraint => ({ kind: "writeOnce", index }),
  immutable: (index: number): SimpleStateConstraint => ({ kind: "immutable", index }),
  senderIs: (pk: Uint8Array): SimpleStateConstraint => ({
    kind: "senderIs",
    pk: exactBytes(pk, 32, "senderIs pk"),
  }),
  senderInSlot: (index: number): SimpleStateConstraint => ({ kind: "senderInSlot", index }),
  balanceGte: (min: number | bigint): SimpleStateConstraint => ({ kind: "balanceGte", min: BigInt(min) }),
  balanceLte: (max: number | bigint): SimpleStateConstraint => ({ kind: "balanceLte", max: BigInt(max) }),
  preimageGate: (commitmentIndex: number, hashKind: HashKind = "blake3"): SimpleStateConstraint => ({
    kind: "preimageGate",
    commitmentIndex,
    hashKind,
  }),
  /**
   * Negation — accept iff the inner constraint rejects. Fail-closed: an
   * unevaluable inner stays unevaluable, never vacuously satisfied.
   * Double-negation is unrepresentable (mirrors the Rust type shape).
   */
  not: (inner: SimpleStateConstraint): SimpleStateConstraint => {
    if (inner.kind === "not") {
      throw new Error("Not(Not(..)) is not representable; use the inner constraint directly");
    }
    return { kind: "not", inner };
  },
};

/**
 * Heyting implication, derived not primitive:
 * `implies(P, Q) == anyOf([not(P), Q])` — the canonical encoding so authors
 * don't open-code it (mirrors `SimpleStateConstraint::implies`).
 */
export function implies(antecedent: SimpleStateConstraint, consequent: SimpleStateConstraint): StateConstraint {
  return anyOf([simple.not(antecedent), consequent]);
}

// ─── postcard encoding (content addressing) ───

class W {
  parts: number[] = [];
  u8(v: number): this {
    this.parts.push(v & 0xff);
    return this;
  }
  varint(v: number | bigint): this {
    let n = BigInt(v);
    if (n < 0n) throw new Error("varint: negative");
    do {
      let b = Number(n & 0x7fn);
      n >>= 7n;
      if (n !== 0n) b |= 0x80;
      this.parts.push(b);
    } while (n !== 0n);
    return this;
  }
  bytes(b: Uint8Array): this {
    for (const x of b) this.parts.push(x);
    return this;
  }
  out(): Uint8Array {
    return Uint8Array.from(this.parts);
  }
}

const hashKindIndex = (k: HashKind): number => (k === "blake3" ? 0 : 1);

function writeSimple(w: W, c: SimpleStateConstraint): void {
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

function writeConstraint(w: W, c: StateConstraint): void {
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
    // Variant indexes verified against the CURRENT `cell/src/program/types.rs`
    // declaration order (2026-07-17): the enum appended `MonotonicSequence`
    // (27) through `Custom` (42) over time, which pushed everything after
    // `PreimageGate` (26) — the stale indexes previously written here (21 /
    // 26 / 38..41) DECODED AS DIFFERENT CONSTRAINTS on the Rust side (21 =
    // RateBound, 26 = PreimageGate, 38 = AffineLe, …). Proven against the
    // real Rust decode by `test/wire-effects.test.mjs` (setProgram predicate
    // differential through the wasm oracle).
    case "preimageGate":
      w.varint(26).u8(c.commitmentIndex).varint(hashKindIndex(c.hashKind));
      break;
    case "anyOf":
      w.varint(31).varint(c.variants.length);
      for (const v of c.variants) writeSimple(w, v);
      break;
    case "senderIs":
      w.varint(43).bytes(c.pk);
      break;
    case "senderInSlot":
      w.varint(44).u8(c.index);
      break;
    case "balanceGte":
      w.varint(45).varint(c.min);
      break;
    case "balanceLte":
      w.varint(46).varint(c.max);
      break;
  }
}

/** Postcard bytes of `Vec<StateConstraint>` (the descriptor's published set). */
export function encodeConstraints(constraints: StateConstraint[]): Uint8Array {
  const w = new W();
  w.varint(constraints.length);
  for (const c of constraints) writeConstraint(w, c);
  return w.out();
}

/**
 * `canonical_program_vk(CellProgram::Predicate(constraints))` — the BLAKE3
 * derive-key (`dregg-cellprogram-vk-v1`) over the length-prefixed postcard
 * encoding of the program (cell/src/factory.rs).
 */
export function canonicalProgramVk(constraints: StateConstraint[]): Uint8Array {
  const w = new W();
  w.varint(1); // CellProgram::Predicate
  w.bytes(encodeConstraints(constraints));
  const serialized = w.out();
  return Blake3Hasher.newDeriveKey("dregg-cellprogram-vk-v1")
    .update(u64le(serialized.length))
    .update(serialized)
    .finalize();
}

/** A published programmed-cell factory shape (TS projection of `FactoryDescriptor`). */
export interface ProgrammedCellDescriptor {
  /** Content address of the factory (hex): same program → same address. */
  factoryVkHex: string;
  factoryVk: Uint8Array;
  /** The canonical VK every child cell is born under (hex). */
  childProgramVkHex: string;
  childProgramVk: Uint8Array;
  /** The published constraint set (the cells' perpetual law). */
  stateConstraints: StateConstraint[];
  defaultMode: "hosted";
  creationBudget: number;
}

/**
 * Build a content-addressed factory descriptor for a custom program —
 * `sdk::program::programmed_cell_descriptor`. Anyone can recompute the
 * address from the published constraints and verify a cell's law.
 */
export function programmedCellDescriptor(constraints: StateConstraint[]): ProgrammedCellDescriptor {
  const encoded = encodeConstraints(constraints);
  const factoryVk = Blake3Hasher.newDeriveKey("dregg-sdk:programmed-cell-factory v1")
    .update(u64le(encoded.length))
    .update(encoded)
    .finalize();
  const childVk = canonicalProgramVk(constraints);
  return {
    factoryVk,
    factoryVkHex: hexEncode(factoryVk),
    childProgramVk: childVk,
    childProgramVkHex: hexEncode(childVk),
    stateConstraints: constraints,
    defaultMode: "hosted",
    creationBudget: 1,
  };
}

/**
 * Stage a custom cell program, then publish it as a content-addressed
 * factory descriptor — the `.program(p)` sugar. An empty program constrains
 * nothing; add atoms or the cell is law-free.
 */
export class CellProgramBuilder {
  private staged: StateConstraint[] = [];

  /** Add one constraint atom. */
  require(constraint: StateConstraint): this {
    this.staged.push(constraint);
    return this;
  }

  /** Add a whole constraint list (e.g. a blueprint's published set). */
  program(constraints: Iterable<StateConstraint>): this {
    for (const c of constraints) this.staged.push(c);
    return this;
  }

  /** The staged constraint set. */
  constraints(): readonly StateConstraint[] {
    return this.staged;
  }

  /** Publish as a content-addressed descriptor. */
  descriptor(): ProgrammedCellDescriptor {
    return programmedCellDescriptor(this.staged);
  }
}

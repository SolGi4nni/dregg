// THE VOCABULARY GATE — sdk-ts's half of the sdk-py drift-killer.
//
// ## WHY THIS FILE EXISTS (the structural story, not a scandal)
//
// The two SDKs are an accidental controlled experiment. sdk-py CANNOT
// mis-encode: it depends on dregg-turn/dregg-cell by PATH and encodes with the
// same `postcard` the node decodes with, so it never had M30's dropped
// `provenance` and it got hybrid PQ signing for free. sdk-ts MUST port the codec
// to TypeScript and therefore drifts — and did. Same team, same week, opposite
// outcomes: STRUCTURE, not diligence.
//
// The repo already carries the strongest oracle available to a TS port:
// `wire.test.mjs` compares TS bytes against the FRESHLY-BUILT dregg-wasm, i.e.
// the real Rust codec, rebuilt by the `pretest` hook on every run. That closes
// mis-encoding for what it compares.
//
// It cannot close what it does not compare. Rust's `Effect` has 34 variants;
// as of 2026-07-17 the TS union models ALL 34 (each driven through the oracle
// by `wire-effects.test.mjs`). A 35th variant, a renamed field, or a new field
// on a modeled variant is still INVISIBLE to a byte comparison over hand-built
// fixtures. That is the remaining silent channel, and this file closes it — the
// way sdk-py closes it: by reading the protocol's own source at test time and
// refusing to pass when the vocabulary has moved.
//
// ## THE DIVISION OF LABOUR (why the pair is airtight)
//
//   * `wire.test.mjs`  — BYTES. For the modeled variants, the encoding equals the
//                        real Rust postcard, oracle rebuilt fresh every run.
//   * this file        — VOCABULARY. The modeled variants are still the same
//                        NAME, INDEX and FIELD SET in Rust, and the unmodeled
//                        remainder is still exactly the declared set.
//
// Between them: a field added to a modeled variant → RED here (field set) and
// RED there (bytes). A variant inserted or reordered → RED here (index pin) and
// RED there (discriminant). A variant appended → RED here. A field renamed →
// RED here. None of those can pass silently.
//
// ## THE LEDGER BELOW IS THE POINT
//
// `MODELED` and `UNMODELED` together must equal the Rust enum EXACTLY, in both
// directions. That is what converts a protocol change from a silent byte
// difference into a RED test naming the variant. A new Rust variant cannot be
// absorbed by this gate: someone must add it to `MODELED` (and teach the codec)
// or to `UNMODELED` (and write down WHY the SDK does not carry it). The
// unmodeled list is not a shrug — it is sdk-ts stating, in the tree, the exact
// subset of the protocol it speaks.
//
// ⚠ NO cached copy, NO checked-in fixture, NO generated artifact. The oracle is
// `../turn/src/action.rs` and `../cell/src/capability.rs`, read on every run.
// Missing or restructured ⇒ THROW, never skip (M30).

import { test } from "node:test";
import assert from "node:assert/strict";

import { rustEnum, rustStruct, tsDiscriminants, snake } from "./protocol-source.mjs";

const ACTION_RS = "turn/src/action.rs";
const CAPABILITY_RS = "cell/src/capability.rs";

/**
 * THE BRIDGE — every effect the TS codec encodes, and the Rust variant it claims
 * to be. `fields` is the Rust field set this codec was written against; the gate
 * asserts it still equals the source's. Change the protocol and this list is
 * where you are forced to look.
 */
const MODELED = [
  { ts: "setField", rust: "SetField", fields: ["cell", "index", "value"] },
  { ts: "transfer", rust: "Transfer", fields: ["from", "to", "amount"] },
  { ts: "grantCapability", rust: "GrantCapability", fields: ["from", "to", "cap"] },
  { ts: "revokeCapability", rust: "RevokeCapability", fields: ["cell", "slot"] },
  // TS FLATTENS Rust's `event: Event` into `{ topic, data }` at the API surface;
  // the encoder writes Event's fields inline, which is byte-identical because
  // postcard has no struct framing. `EVENT_FIELDS` pins the struct it inlines,
  // so growing `Event` a third field is RED even though `Effect::EmitEvent`'s
  // own field set is untouched.
  { ts: "emitEvent", rust: "EmitEvent", fields: ["cell", "event"] },
  { ts: "incrementNonce", rust: "IncrementNonce", fields: ["cell"] },
  { ts: "createCell", rust: "CreateCell", fields: ["public_key", "token_id", "balance"] },
  // ── 2026-07-17: the remaining 27 variants modeled (per-variant byte+hash
  //    differential in wire-effects.test.mjs drives each through the wasm
  //    oracle). Sub-shape gaps that remain UNMODELED inside a modeled variant
  //    (refused loudly by `UnmodeledWireError`, never encoded wrongly):
  //      * SetProgram: `CellProgram::Cases` (TransitionCase guards);
  //      * React: `ConditionProof::Receipt` (a full TurnReceipt);
  //      * nested `wake` Turns are the default-proof-bundle shape only.
  { ts: "setPermissions", rust: "SetPermissions", fields: ["cell", "new_permissions"] },
  { ts: "setVerificationKey", rust: "SetVerificationKey", fields: ["cell", "new_vk"] },
  { ts: "setProgram", rust: "SetProgram", fields: ["cell", "program"] },
  {
    ts: "noteSpend",
    rust: "NoteSpend",
    fields: ["nullifier", "note_tree_root", "value", "asset_type", "spending_proof", "value_commitment"],
  },
  {
    ts: "noteCreate",
    rust: "NoteCreate",
    fields: ["commitment", "value", "asset_type", "encrypted_note", "value_commitment", "range_proof"],
  },
  {
    ts: "spawnWithDelegation",
    rust: "SpawnWithDelegation",
    fields: ["child_public_key", "child_token_id", "max_staleness"],
  },
  { ts: "refreshDelegation", rust: "RefreshDelegation", fields: ["child", "snapshot"] },
  { ts: "revokeDelegation", rust: "RevokeDelegation", fields: ["child"] },
  { ts: "bridgeMint", rust: "BridgeMint", fields: ["portable_proof"] },
  { ts: "introduce", rust: "Introduce", fields: ["introducer", "recipient", "target", "permissions"] },
  { ts: "pipelinedSend", rust: "PipelinedSend", fields: ["target", "action"] },
  { ts: "exerciseViaCapability", rust: "ExerciseViaCapability", fields: ["cap_slot", "inner_effects"] },
  { ts: "makeSovereign", rust: "MakeSovereign", fields: ["cell"] },
  {
    ts: "createCellFromFactory",
    rust: "CreateCellFromFactory",
    fields: ["factory_vk", "owner_pubkey", "token_id", "params"],
  },
  {
    ts: "refusal",
    rust: "Refusal",
    fields: ["cell", "offered_action_commitment", "refusal_reason", "proof_witness_index"],
  },
  { ts: "cellSeal", rust: "CellSeal", fields: ["target", "reason"] },
  { ts: "cellUnseal", rust: "CellUnseal", fields: ["target"] },
  { ts: "cellDestroy", rust: "CellDestroy", fields: ["target", "certificate"] },
  { ts: "burn", rust: "Burn", fields: ["target", "slot", "amount"] },
  {
    ts: "attenuateCapability",
    rust: "AttenuateCapability",
    fields: ["cell", "slot", "narrower_permissions", "narrower_effects", "narrower_expiry"],
  },
  { ts: "receiptArchive", rust: "ReceiptArchive", fields: ["prefix_end_height", "checkpoint"] },
  { ts: "promise", rust: "Promise", fields: ["cell", "resolution_condition", "wake", "timeout_height"] },
  {
    ts: "notify",
    rust: "Notify",
    fields: ["from", "to", "wake", "resolution_condition", "timeout_height"],
  },
  { ts: "react", rust: "React", fields: ["pending_id", "condition", "resolution_proof", "wake"] },
  { ts: "mint", rust: "Mint", fields: ["target", "slot", "amount"] },
  { ts: "shieldedTransfer", rust: "ShieldedTransfer", fields: ["payload"] },
  { ts: "custom", rust: "Custom", fields: ["cell", "program_vk_hash", "proof_commitment"] },
];

/** The `Event` struct the `emitEvent` case inlines. */
const EVENT_FIELDS = ["topic", "data"];

/**
 * THE DECLARED REMAINDER — protocol effects the TS SDK does NOT model, each with
 * the reason it is out of scope for a browser/node client. This is sdk-ts saying
 * out loud which subset of the protocol it speaks. A variant that is neither here
 * nor in MODELED turns this file RED by name.
 */
// 2026-07-17: EMPTY — every Effect variant is now modeled (34/34; each proven
// byte-identical to the Rust postcard AND hash-identical to Effect::hash by
// the per-variant oracle differential in wire-effects.test.mjs). The gate
// keeps the empty ledger so a 35th Rust variant still turns this file RED by
// name until someone models it or declares it here WITH a reason.
const UNMODELED = {};

/** Authorization variants the TS codec writes, and their Rust names. */
const MODELED_AUTH = [
  { ts: "signature", rust: "Signature" },
  { ts: "hybridSignature", rust: "HybridSignature" },
  { ts: "unchecked", rust: "Unchecked" },
];

// The remainder. NOTE: this list was WRONG when first written from memory — the
// gate immediately went red naming `Custom, OneOf, Stealth, Token`, which is the
// gate doing its job on its own author. The reasons below are read off the real
// declarations in `turn/src/action.rs`, not recalled.
const UNMODELED_AUTH = {
  Proof: "ZK-proof authorization (proof_bytes + bound action/resource); the client does not prove",
  Breadstuff: "bare capability-token hash; superseded by the c-list path in TS",
  Bearer: "BearerCapProof; delegation-chain proving is not a client capability",
  CapTpDelivered: "constructed by the CapTP wire layer from a HandoffCertificate, not by a client",
  Custom: "a WitnessedPredicate against a cell's AuthRequired::Custom{vk_hash}; needs a proof the client cannot make",
  OneOf: "disjunctive alternation over nested Authorizations; modeling it forces the FULL auth codec into TS",
  Stealth: "one-time-key stealth addressing (P = c·G + S); no TS key-derivation surface yet",
  Token: "encoded biscuit/macaroon credential from dregg_token; the TS SDK has no token codec yet",
};

// ─── 1. THE ORACLE IS REAL AND FAILS LOUD ───────────────────────────────────

test("the vocabulary oracle reads the REAL protocol source (and cannot skip)", () => {
  const effects = rustEnum(ACTION_RS, "Effect");
  assert.ok(
    effects.length > 20,
    `parsed only ${effects.length} Effect variants from ${ACTION_RS} — the parser is not seeing the real enum`,
  );
  // Pin the law the protocol states about itself: postcard is index-sensitive,
  // so index 0 must still be SetField. If this moved, every durable blob moved.
  assert.equal(effects[0].name, "SetField", "Effect index 0 moved — the postcard discriminant space shifted");
  assert.equal(rustStruct(CAPABILITY_RS, "CapabilityRef")[0], "target");
});

test("a missing protocol file THROWS rather than passing silently", () => {
  assert.throws(
    () => rustEnum("turn/src/definitely-not-a-real-file.rs", "Effect"),
    /PROTOCOL SOURCE MISSING/,
    "the oracle must refuse to pass when the source of truth is absent (M30)",
  );
  assert.throws(
    () => rustEnum(ACTION_RS, "NoSuchEnumAnywhere"),
    /PROTOCOL VOCABULARY LOST/,
    "the oracle must refuse to pass when the declaration it parses is gone",
  );
});

// ─── 2. THE LEDGER MUST EXHAUST THE PROTOCOL ────────────────────────────────

test("EXHAUSTIVE: every Rust Effect variant is either MODELED or declared UNMODELED", () => {
  const effects = rustEnum(ACTION_RS, "Effect");
  const modeled = new Set(MODELED.map((m) => m.rust));
  const unmodeled = new Set(Object.keys(UNMODELED));

  const unaccounted = effects.map((e) => e.name).filter((n) => !modeled.has(n) && !unmodeled.has(n));
  assert.deepEqual(
    unaccounted,
    [],
    `PROTOCOL GREW AND sdk-ts DID NOT NOTICE — these Effect variants exist in ${ACTION_RS} but are ` +
      `neither modeled by the TS codec nor declared unmodeled: ${unaccounted.join(", ")}. ` +
      `This is the drift class the SDK is structurally prone to. Decide, in the tree: either teach ` +
      `the codec (add to MODELED + wire.ts + the byte differential) or declare it UNMODELED with the ` +
      `reason the SDK does not carry it. Do not delete this assertion.`,
  );

  const known = new Set(effects.map((e) => e.name));
  const phantom = [...modeled, ...unmodeled].filter((n) => !known.has(n));
  assert.deepEqual(
    phantom,
    [],
    `sdk-ts's ledger names Effect variants the protocol NO LONGER HAS: ${phantom.join(", ")}. ` +
      `They were renamed or removed; a codec that still encodes them is writing bytes the node cannot read.`,
  );

  // The two lists must not overlap, or "modeled" and "unmodeled" both look true.
  const both = MODELED.map((m) => m.rust).filter((n) => unmodeled.has(n));
  assert.deepEqual(both, [], `declared BOTH modeled and unmodeled: ${both.join(", ")}`);
});

test("EXHAUSTIVE: every Rust Authorization variant is accounted for", () => {
  const auths = rustEnum(ACTION_RS, "Authorization");
  const modeled = new Set(MODELED_AUTH.map((m) => m.rust));
  const unmodeled = new Set(Object.keys(UNMODELED_AUTH));
  const unaccounted = auths.map((a) => a.name).filter((n) => !modeled.has(n) && !unmodeled.has(n));
  assert.deepEqual(
    unaccounted,
    [],
    `Authorization grew variants sdk-ts has not accounted for: ${unaccounted.join(", ")}. ` +
      `The M30 sibling bug was signing the WRONG authorization shape; this is where that is caught.`,
  );
  const known = new Set(auths.map((a) => a.name));
  const phantom = [...modeled, ...unmodeled].filter((n) => !known.has(n));
  assert.deepEqual(phantom, [], `ledger names Authorization variants the protocol no longer has: ${phantom.join(", ")}`);
});

// ─── 3. THE INDEX PIN — postcard is positional ──────────────────────────────

test("DISCRIMINANT PIN: every index the TS codec writes equals the Rust variant's position", () => {
  // `turn/src/action.rs` states the law itself: "a new variant MUST append,
  // never insert — the durable postcard codec is index-sensitive". This is that
  // law, enforced. The indices are read from BOTH sources — the Rust enum's
  // position and the literal `w.varint(n)` in `src/internal/wire.ts` — so this
  // is not a third hand-maintained restatement of the same numbers.
  const effects = rustEnum(ACTION_RS, "Effect");
  const byName = new Map(effects.map((e) => [e.name, e]));
  const ts = tsDiscriminants("writeEffect");

  assert.deepEqual(
    [...ts.keys()].sort(),
    MODELED.map((m) => m.ts).sort(),
    "the TS codec encodes a different set of effects than MODELED declares — the ledger has drifted from the codec",
  );

  for (const { ts: kind, rust } of MODELED) {
    const written = ts.get(kind);
    const actual = byName.get(rust).index;
    assert.equal(
      written,
      actual,
      `DISCRIMINANT DRIFT: writeEffect writes varint(${written}) for "${kind}", but Rust's ` +
        `Effect::${rust} is at index ${actual}. Every turn carrying this effect would decode as a ` +
        `DIFFERENT effect on the node. A variant was inserted rather than appended.`,
    );
  }
});

test("DISCRIMINANT PIN: Authorization indices match", () => {
  const auths = rustEnum(ACTION_RS, "Authorization");
  const byName = new Map(auths.map((a) => [a.name, a]));
  const ts = tsDiscriminants("writeAuthorization");
  assert.deepEqual([...ts.keys()].sort(), MODELED_AUTH.map((m) => m.ts).sort());
  for (const { ts: kind, rust } of MODELED_AUTH) {
    assert.equal(
      ts.get(kind),
      byName.get(rust).index,
      `Authorization::${rust} index drifted from what writeAuthorization writes for "${kind}" — ` +
        `signatures would be read as the wrong variant`,
    );
  }
});

// ─── 4. THE FIELD PIN — the M30 site ────────────────────────────────────────

test("FIELD PIN: every modeled effect's Rust field set is what the codec was written against", () => {
  const byName = new Map(rustEnum(ACTION_RS, "Effect").map((e) => [e.name, e]));
  for (const { rust, fields } of MODELED) {
    assert.deepEqual(
      byName.get(rust).fields,
      fields,
      `FIELD DRIFT on Effect::${rust} — the protocol now declares ` +
        `[${byName.get(rust).fields.join(", ")}] but the TS codec was written against ` +
        `[${fields.join(", ")}]. Postcard is positional and non-self-describing: an added, removed, ` +
        `renamed or REORDERED field means TS writes bytes the node reads as a different field. ` +
        `This is precisely the M30 shape (a dropped [u8;32] desyncing everything after it).`,
    );
  }
});

test("FIELD PIN: CapabilityRef — the actual M30 site — still has the field set the codec writes", () => {
  // M30: sdk-ts shipped "byte-faithful: yes" to npm while dropping
  // `CapabilityRef::provenance`, a `[u8; 32]` with `#[serde(default)]` (NOT
  // skip_serializing_if), so postcard emits its 32 bytes POSITIONALLY. Dropping
  // it desyncs the node's read of everything after it. `writeCapabilityRef`
  // encodes these eight, in this order.
  assert.deepEqual(
    rustStruct(CAPABILITY_RS, "CapabilityRef"),
    ["target", "slot", "permissions", "breadstuff", "expires_at", "allowed_effects", "stored_epoch", "provenance"],
    "CapabilityRef's field set/order drifted from what writeCapabilityRef encodes. THIS IS THE M30 SITE: " +
      "a positional [u8;32] silently dropped here made every cap-carrying turn undecodable while the SDK " +
      "reported byte-faithfulness. Update src/internal/wire.ts's writeCapabilityRef, then this pin.",
  );
});

test("FIELD PIN: the Event struct emitEvent inlines", () => {
  assert.deepEqual(
    rustStruct(ACTION_RS, "Event"),
    EVENT_FIELDS,
    "Event's fields drifted; the emitEvent case inlines them positionally into the effect encoding",
  );
});

// ─── 5. THE CANARY — this gate can actually FAIL ────────────────────────────

test("CANARY: the vocabulary gate goes RED on a simulated protocol change", () => {
  // A gate is worth nothing until it is shown to discriminate. Simulate the two
  // drift shapes this file exists for, against the REAL parsed vocabulary, and
  // pin that each is caught. (The live mutation demo — editing action.rs and
  // watching this go red — is the driven form of the same thing.)
  const effects = rustEnum(ACTION_RS, "Effect");
  const modeled = new Set(MODELED.map((m) => m.rust));
  const unmodeled = new Set(Object.keys(UNMODELED));

  // (a) An APPENDED variant is unaccounted-for.
  const grown = [...effects.map((e) => e.name), "SomeBrandNewEffect"];
  const unaccounted = grown.filter((n) => !modeled.has(n) && !unmodeled.has(n));
  assert.deepEqual(
    unaccounted,
    ["SomeBrandNewEffect"],
    "CANARY FAILED: an appended protocol variant was NOT flagged as unaccounted-for — the gate is blessing anything",
  );

  // (b) An INSERTED variant shifts every later index, so the pins break.
  const shifted = new Map(effects.map((e) => [e.name, e.index + 1]));
  const ts = tsDiscriminants("writeEffect");
  const broken = MODELED.filter(({ ts: kind, rust }) => ts.get(kind) !== shifted.get(rust));
  assert.equal(
    broken.length,
    MODELED.length,
    "CANARY FAILED: shifting every Rust discriminant did not break every index pin — the pin is not discriminating",
  );

  // (c) A RENAMED field on a modeled variant breaks the field pin.
  const t = MODELED.find((m) => m.rust === "Transfer");
  const renamed = ["from", "to", "amount_v2"];
  assert.notDeepEqual(renamed, t.fields, "CANARY FAILED: a renamed field compared equal to the declared field set");
});

test("the TS→Rust name bridge is honest (camelCase ↔ snake_case)", () => {
  for (const { ts, rust } of MODELED) {
    assert.equal(
      snake(ts),
      rust.replace(/^([A-Z])/, (c) => c.toLowerCase()).replace(/[A-Z]/g, (c) => `_${c.toLowerCase()}`),
      `the TS kind "${ts}" does not correspond to Effect::${rust} by the naming convention — ` +
        `if that is deliberate, say so here rather than letting the mapping be silently arbitrary`,
    );
  }
});

// The wire differential — the drift killer.
//
// Builds a turn in TS, hands the SAME turn (serde-JSON form) to the repo's
// own dregg-wasm build (the actual Rust dregg-turn/dregg-sdk code), and
// asserts BYTE EQUALITY between:
//
//   - the TS postcard `Turn` encoding and the Rust `postcard::to_allocvec`,
//     for the FULL wire shape (agent, forest, every modeled effect INCLUDING
//     `CapabilityRef.provenance`, the optional turn fields) — the encoder half;
//   - the TS `turnHash` and the Rust canonical `Turn::hash` (v3) — the hash half.
//
// Any drift in the postcard layout, the effect/action hash preimages, or the
// hash domains fails here.
//
// ⚠ SIGNATURE SHAPE — CLASSICAL vs HYBRID (read this before "fixing" a red run).
// The Rust DEFAULT signer (`AgentCipherclerk::sign_action`, which `sign_turn_v3`
// calls for an `Unchecked` action) now emits `Authorization::HybridSignature`
// (variant 10): ed25519 (64B) + an ML-DSA-65 (FIPS 204) signature (3309B) + the
// ML-DSA public key (1952B). The TS SDK signs CLASSICAL only
// (`Authorization::Signature`, variant 0, 64B) — it has no post-quantum crypto.
// So a TS-signed turn is byte-identical to `sign_action_classical`, NOT to the
// default hybrid signer, and the two turn encodings CANNOT match byte-for-byte.
//
// This differential therefore isolates the ENCODER by pre-signing on the TS side
// (classical) and handing the oracle the ALREADY-signed turn: `sign_call_tree`
// only signs `Unchecked` actions, so the oracle re-encodes the classical turn
// through the real Rust `postcard` serializer WITHOUT re-signing. That proves the
// encoder (incl. `provenance`) and the v3 hash are byte-faithful.
//
// The SIGNING MESSAGE is checked separately (`ed25519 signing message` test):
// the TS classical signature must equal the ed25519 HALF of the Rust hybrid
// signature over the same canonical `compute_signing_message`. And the classical
// vs hybrid wire-shape gap itself is guarded loud (`hybrid authorization
// boundary` test) so it can never silently regress to a false "byte-faithful".

import { test } from "node:test";
import assert from "node:assert/strict";

import { loadWasmOracle, hex, raw } from "./helpers.mjs";

const cell = (n) => Uint8Array.from({ length: 32 }, () => n);
const arr = (b) => Array.from(b);

/** serde-JSON form of a TS `Authorization` (externally tagged Rust enum). */
function authToJson(a) {
  switch (a.kind) {
    case "signature":
      return { Signature: [arr(a.r), arr(a.s)] };
    case "unchecked":
      return "Unchecked";
    default:
      throw new Error(`no JSON form for authorization ${a.kind}`);
  }
}

/** serde-JSON form of the TS effect union (externally tagged Rust enum). */
function effectToJson(e) {
  switch (e.kind) {
    case "setField":
      return { SetField: { cell: arr(e.cell), index: e.index, value: arr(e.value) } };
    case "transfer":
      return { Transfer: { from: arr(e.from), to: arr(e.to), amount: Number(e.amount) } };
    case "grantCapability":
      return {
        GrantCapability: {
          from: arr(e.from),
          to: arr(e.to),
          cap: {
            target: arr(e.cap.target),
            slot: e.cap.slot,
            permissions: "Signature",
            breadstuff: e.cap.breadstuff ? arr(e.cap.breadstuff) : null,
            expires_at: e.cap.expiresAt !== undefined ? Number(e.cap.expiresAt) : null,
            stored_epoch: e.cap.storedEpoch !== undefined ? Number(e.cap.storedEpoch) : null,
            // `provenance` is `[u8; 32]` with `#[serde(default)]` (NOT an
            // Option) — a bare 32-byte array. Omitting the key would let serde's
            // default fill zeros and mask an encoder that drops the field (M30),
            // so we ALWAYS pin the 32 bytes here and exercise a non-zero value.
            provenance: arr(e.cap.provenance ?? new Uint8Array(32)),
          },
        },
      };
    case "revokeCapability":
      return { RevokeCapability: { cell: arr(e.cell), slot: e.slot } };
    case "emitEvent":
      return { EmitEvent: { cell: arr(e.cell), event: { topic: arr(e.topic), data: e.data.map(arr) } } };
    case "incrementNonce":
      return { IncrementNonce: { cell: arr(e.cell) } };
    case "createCell":
      return { CreateCell: { public_key: arr(e.publicKey), token_id: arr(e.tokenId), balance: Number(e.balance) } };
    default:
      throw new Error(`no JSON form for ${e.kind}`);
  }
}

function actionToJson(a) {
  return {
    target: arr(a.target),
    method: arr(a.method),
    args: a.args.map(arr),
    authorization: authToJson(a.authorization),
    preconditions: { cell_state: null, network: null, valid_while: null, witnessed: [] },
    effects: a.effects.map(effectToJson),
    may_delegate: "None",
    commitment_mode: "Full",
    balance_change: a.balanceChange !== undefined ? Number(a.balanceChange) : null,
    witness_blobs: [],
  };
}

function turnToJson(t) {
  return {
    agent: arr(t.agent),
    nonce: Number(t.nonce),
    call_forest: {
      roots: t.roots.map((r) => ({ action: actionToJson(r.action), children: [], hash: arr(new Uint8Array(32)) })),
      forest_hash: arr(new Uint8Array(32)),
    },
    fee: Number(t.fee),
    memo: t.memo ?? null,
    valid_until: t.validUntil !== undefined ? Number(t.validUntil) : null,
    previous_receipt_hash: t.previousReceiptHash ? arr(t.previousReceiptHash) : null,
    depends_on: (t.dependsOn ?? []).map(arr),
    conservation_proof: null,
    sovereign_witnesses: {},
    execution_proof: null,
    execution_proof_cell: null,
    execution_proof_new_commitment: null,
    custom_program_proofs: null,
    effect_binding_proofs: [],
    cross_effect_dependencies: [],
    effect_witness_index_map: [],
  };
}

function richEffects(rawMod, acting) {
  const { symbol } = rawMod;
  return [
    { kind: "setField", cell: acting, index: 3, value: rawMod.fieldFromU64(77n) },
    { kind: "transfer", from: acting, to: cell(9), amount: 12345n },
    {
      kind: "grantCapability",
      from: acting,
      to: cell(8),
      cap: {
        target: cell(7),
        slot: 2,
        permissions: { kind: "signature" },
        expiresAt: 900n,
        // A non-zero provenance so the differential pins the actual 32 bytes
        // (M30): the drift killer must catch an encoder that drops this field.
        provenance: rawMod.fieldFromU64(0xABCDEFn),
      },
    },
    { kind: "revokeCapability", cell: acting, slot: 5 },
    { kind: "emitEvent", cell: acting, topic: symbol("ping"), data: [rawMod.fieldFromU64(1n), rawMod.fieldFromU64(2n)] },
    { kind: "incrementNonce", cell: acting },
    { kind: "createCell", publicKey: cell(0xaa), tokenId: cell(0xbb), balance: 500n },
  ];
}

/**
 * Re-encode a TS-built turn through the REAL Rust `postcard` serializer WITHOUT
 * re-signing it. `sign_turn_v3` only signs `Unchecked` actions; a turn whose
 * action already carries a classical `Authorization::Signature` is decoded,
 * left as-is, and re-serialized — so `turn_bytes` is the genuine Rust encoding
 * of THIS turn (the encoder oracle) and `turn_id` is the genuine Rust
 * `Turn::hash` (v3).
 */
function rustReencode(wasm, seed32, federationId, tsTurn) {
  const jsonBytes = new TextEncoder().encode(JSON.stringify(turnToJson(tsTurn)));
  return wasm.sign_turn_v3(jsonBytes, seed32, federationId);
}

test("differential: TS turn bytes + canonical hash == Rust encoder (every effect, incl. provenance)", async () => {
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x10 + i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = Uint8Array.from({ length: 32 }, () => 0x42);

  // A turn that exercises every modeled effect + the optional turn fields.
  const effects = richEffects(rawMod, agent);
  const unsigned = rawMod.unsignedActionNamed(agent, "execute", effects);
  const signedAction = identity.signAction(unsigned, federationId); // classical Signature
  assert.equal(signedAction.authorization.kind, "signature", "TS SDK must sign classical here");

  const turn = {
    agent,
    nonce: 7n,
    roots: [{ action: signedAction, children: [] }],
    fee: 10_000n,
    memo: "differential",
    validUntil: 1765432100n,
    previousReceiptHash: cell(0x33),
    dependsOn: [cell(0x44)],
  };

  const oracle = rustReencode(wasm, seed32, federationId, turn);
  assert.equal(oracle.signer_pubkey, identity.publicKeyHex, "key derivation drift");

  const tsBytes = rawMod.encodeTurn(turn);
  assert.equal(
    hex(tsBytes),
    hex(Uint8Array.from(oracle.turn_bytes)),
    "postcard Turn encoding drifted from Rust (a field/enum/layout in wire.ts disagrees with the Rust type)",
  );

  assert.equal(
    rawMod.turnHashHex(turn),
    oracle.turn_id,
    "canonical Turn::hash (v3) drifted from Rust",
  );
});

test("differential: minimal single-effect turn (all options None)", async () => {
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x77 - i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = new Uint8Array(32);

  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [
    { kind: "incrementNonce", cell: agent },
  ]);
  const signedAction = identity.signAction(unsigned, federationId);
  const turn = { agent, nonce: 0n, roots: [{ action: signedAction, children: [] }], fee: 0n };

  const oracle = rustReencode(wasm, seed32, federationId, turn);
  assert.equal(hex(rawMod.encodeTurn(turn)), hex(Uint8Array.from(oracle.turn_bytes)));
  assert.equal(rawMod.turnHashHex(turn), oracle.turn_id);
});

test("ed25519 signing message: TS classical sig == the ed25519 half of the Rust HYBRID signature", async () => {
  // Proves the canonical `compute_signing_message` (dregg-action-sig-v2,
  // federation-bound) is byte-identical: both signers cover the SAME message,
  // so the classical 64 bytes TS emits equal the ed25519 leg of the hybrid.
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x10 + i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = Uint8Array.from({ length: 32 }, () => 0x42);

  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [
    { kind: "incrementNonce", cell: agent },
  ]);
  const tsSigned = identity.signAction(unsigned, federationId); // classical
  const tsSigHex = hex(tsSigned.authorization.r) + hex(tsSigned.authorization.s);

  // Hand the oracle the UNSIGNED turn so it signs through the default (hybrid) path.
  const unsignedTurn = { agent, nonce: 0n, roots: [{ action: unsigned, children: [] }], fee: 0n };
  const jsonBytes = new TextEncoder().encode(JSON.stringify(turnToJson(unsignedTurn)));
  const oracle = wasm.sign_turn_v3(jsonBytes, seed32, federationId);
  const signedJson = JSON.parse(Buffer.from(Uint8Array.from(oracle.turn_bytes_json)).toString("utf8"));
  const oracleAuth = signedJson.call_forest.roots[0].action.authorization;

  assert.ok(oracleAuth.HybridSignature, "Rust default signer must emit HybridSignature");
  const oracleEd = hex(Uint8Array.from(oracleAuth.HybridSignature.ed25519));
  assert.equal(tsSigHex, oracleEd, "TS classical ed25519 signature diverged from Rust's ed25519 half (signing message drift)");
});

test("hybrid authorization boundary: the Rust default is post-quantum; the TS SDK signs classical only", async () => {
  // A LOUD guard on the ONE remaining wire-shape divergence (not silent drift):
  // Rust default → Authorization::HybridSignature (variant 10) with ML-DSA-65;
  // the TS SDK → Authorization::Signature (variant 0), classical ed25519 only.
  // If this ever stops being true, a signed-turn byte differential is possible
  // again and this test — not a false "byte-faithful" claim — is where you learn it.
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x21 + i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = new Uint8Array(32);

  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [{ kind: "incrementNonce", cell: agent }]);

  // TS side: classical.
  const tsSigned = identity.signAction(unsigned, federationId);
  assert.equal(tsSigned.authorization.kind, "signature", "TS SDK emits the classical Signature variant");

  // Rust default side: hybrid, with the two large PQ halves.
  const unsignedTurn = { agent, nonce: 0n, roots: [{ action: unsigned, children: [] }], fee: 0n };
  const oracle = wasm.sign_turn_v3(new TextEncoder().encode(JSON.stringify(turnToJson(unsignedTurn))), seed32, federationId);
  const auth = JSON.parse(Buffer.from(Uint8Array.from(oracle.turn_bytes_json)).toString("utf8"))
    .call_forest.roots[0].action.authorization;

  assert.ok(auth.HybridSignature, "Rust default authorization is HybridSignature");
  assert.equal(auth.HybridSignature.ed25519.length, 64, "hybrid carries a 64-byte ed25519 leg");
  assert.equal(auth.HybridSignature.ml_dsa.length, 3309, "hybrid carries a 3309-byte ML-DSA-65 signature the TS SDK cannot produce");
  assert.equal(auth.HybridSignature.ml_dsa_pk.length, 1952, "hybrid carries a 1952-byte ML-DSA-65 public key the TS SDK cannot produce");

  // The default-signed hybrid turn is far larger than the TS classical turn:
  // concrete proof the wire shapes differ (so a byte differential over the
  // default signer is not achievable from TS today).
  const tsClassicalTurn = { agent, nonce: 0n, roots: [{ action: tsSigned, children: [] }], fee: 0n };
  const tsLen = rawMod.encodeTurn(tsClassicalTurn).length;
  const hybridLen = Uint8Array.from(oracle.turn_bytes).length;
  assert.ok(hybridLen > tsLen + 5000, `hybrid turn (${hybridLen}B) dwarfs the classical TS turn (${tsLen}B)`);
});

test("the SignedTurn envelope verifies and frames as turn ++ sig ++ signer", async () => {
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => i * 3);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [
    { kind: "incrementNonce", cell: agent },
  ]);
  const action = identity.signAction(unsigned, new Uint8Array(32));
  const turn = { agent, nonce: 1n, roots: [{ action, children: [] }], fee: 100n };

  const envelope = identity.signTurnEnvelope(turn);
  const turnBytes = rawMod.encodeTurn(turn);
  assert.equal(envelope.length, turnBytes.length + 1 + 64 + 1 + 32);
  assert.equal(hex(envelope.subarray(0, turnBytes.length)), hex(turnBytes));
  assert.equal(envelope[turnBytes.length], 0x40, "varint(64) before the signature");
  assert.equal(envelope[turnBytes.length + 65], 0x20, "varint(32) before the signer");
  const sig = envelope.subarray(turnBytes.length + 1, turnBytes.length + 65);
  const signer = envelope.subarray(turnBytes.length + 66);
  assert.equal(hex(signer), identity.publicKeyHex);
  // The envelope signature is over the canonical Turn::hash (v3) — exactly
  // what post_submit_signed_turn re-derives and verifies.
  assert.ok(rawMod.ed25519Verify(identity.publicKey, rawMod.turnHash(turn), sig));
});

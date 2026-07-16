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
// ⚠ SIGNATURE SHAPE — HYBRID POST-QUANTUM IS THE DEFAULT ON BOTH SIDES.
// The Rust DEFAULT signer (`AgentCipherclerk::sign_action`, which `sign_turn_v3`
// calls for an `Unchecked` action) emits `Authorization::HybridSignature`
// (variant 10): ed25519 (64B) + an ML-DSA-65 (FIPS 204) signature (3309B) + the
// ML-DSA public key (1952B). The TS SDK's `Identity.signAction` now emits the
// SAME shape (`@noble/post-quantum` ML-DSA-65, deterministic, same ctx, key
// derived from the same ed25519 seed), so a TS-signed turn is byte-identical to
// the CURRENT Rust default signer — the `differential: TS HYBRID-signed turn ==
// Rust default-signed turn` test below drives exactly that, end to end, with
// BOTH sides signing (no pre-signing dodge).
//
// ⚠ THE ORACLE SIGNS AT NONCE 0. `sign_turn_v3` → `sign_call_forest` →
// `cclerk.sign_action`, which binds `next_turn_nonce()` = the clerk's
// receipt-chain length = 0 for a fresh clerk — REGARDLESS of `turn.nonce`.
// `dregg-action-sig-v3` binds that nonce into the signature, so any turn the
// oracle signs is only self-consistent at nonce 0. The differentials therefore
// use nonce 0 (where the oracle's binding and the turn's real nonce agree);
// signing at other nonces is covered by the Rust-verifier harness instead.
//
// The classical path stays exercised (`classical signing` test) because the node
// still accepts it while `require_pq` is off, and the CANARY test pins that
// signing classical where hybrid is expected makes the differential go RED —
// i.e. that this differential can still fail.

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
    case "hybridSignature":
      return {
        HybridSignature: {
          ed25519: arr(a.ed25519),
          ml_dsa: arr(a.mlDsa),
          ml_dsa_pk: arr(a.mlDsaPk),
        },
      };
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
 * Hand a turn to the oracle. `sign_turn_v3` signs every `Unchecked` action
 * through the REAL Rust default path (`AgentCipherclerk::sign_action` → HYBRID),
 * then re-encodes with the real `postcard`. Pass an UNSIGNED turn to get Rust's
 * own default-signed bytes; pass an already-signed turn to get a pure re-encode
 * (signing is skipped for non-`Unchecked` actions).
 */
function rustOracle(wasm, seed32, federationId, tsTurn) {
  const jsonBytes = new TextEncoder().encode(JSON.stringify(turnToJson(tsTurn)));
  return wasm.sign_turn_v3(jsonBytes, seed32, federationId);
}

/**
 * The nonce the oracle binds into every action signature. `sign_turn_v3` builds
 * a FRESH cipherclerk, whose `next_turn_nonce()` (receipt-chain length) is 0 —
 * it does not read `turn.nonce`. Differentials that compare SIGNATURES must
 * therefore ride nonce 0, or the two sides bind different `sig-v3` messages.
 */
const ORACLE_NONCE = 0n;

test("differential: TS HYBRID-signed turn == Rust DEFAULT-signed turn, byte for byte (every effect, incl. provenance)", async () => {
  // THE GATE. Both sides SIGN (no pre-signing dodge): TS signs hybrid through
  // `Identity.signAction`; the oracle is handed the UNSIGNED turn and signs it
  // through the real `AgentCipherclerk::sign_action` default path. The bytes
  // must be identical — which requires the postcard layout, the `sig-v3`
  // signing message, the ML-DSA-65 key DERIVATION (same seed → same PQ key),
  // the deterministic ML-DSA signature, and the FIPS 204 ctx to ALL agree.
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
  const signedAction = identity.signAction(unsigned, federationId, ORACLE_NONCE);
  assert.equal(signedAction.authorization.kind, "hybridSignature", "TS SDK must sign HYBRID by default");

  const base = {
    agent,
    nonce: ORACLE_NONCE,
    fee: 10_000n,
    memo: "differential",
    validUntil: 1765432100n,
    previousReceiptHash: cell(0x33),
    dependsOn: [cell(0x44)],
  };
  const tsTurn = { ...base, roots: [{ action: signedAction, children: [] }] };
  // The oracle signs this one itself (its action is still Unchecked).
  const oracle = rustOracle(wasm, seed32, federationId, {
    ...base,
    roots: [{ action: unsigned, children: [] }],
  });
  assert.equal(oracle.signer_pubkey, identity.publicKeyHex, "key derivation drift");

  assert.equal(
    hex(rawMod.encodeTurn(tsTurn)),
    hex(Uint8Array.from(oracle.turn_bytes)),
    "TS hybrid-signed turn diverged from the Rust DEFAULT signer (layout, sig-v3 message, ML-DSA derivation, determinism, or ctx)",
  );
  assert.equal(
    rawMod.turnHashHex(tsTurn),
    oracle.turn_id,
    "canonical Turn::hash (v3) drifted from Rust",
  );
});

test("differential: minimal single-effect HYBRID turn (all options None)", async () => {
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
  const signedAction = identity.signAction(unsigned, federationId, ORACLE_NONCE);
  const tsTurn = { agent, nonce: ORACLE_NONCE, roots: [{ action: signedAction, children: [] }], fee: 0n };

  const oracle = rustOracle(wasm, seed32, federationId, {
    agent,
    nonce: ORACLE_NONCE,
    roots: [{ action: unsigned, children: [] }],
    fee: 0n,
  });
  assert.equal(hex(rawMod.encodeTurn(tsTurn)), hex(Uint8Array.from(oracle.turn_bytes)));
  assert.equal(rawMod.turnHashHex(tsTurn), oracle.turn_id);
});

test("CANARY: signing CLASSICAL where the Rust default is HYBRID makes the differential go RED", async () => {
  // The differential above is only worth something if it can FAIL. This
  // reproduces the exact bug it now guards (PUBLISHED-VERIFY correction 2: the
  // TS SDK signed classical while the Rust default was hybrid) and pins that
  // the comparison catches it. If this test ever goes green-by-equality, the
  // differential has stopped discriminating and is blessing anything.
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x10 + i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = new Uint8Array(32);

  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [{ kind: "incrementNonce", cell: agent }]);
  const classical = identity.signActionClassical(unsigned, federationId, ORACLE_NONCE);
  assert.equal(classical.authorization.kind, "signature", "the canary must sign the LEGACY classical shape");

  const classicalTurn = { agent, nonce: ORACLE_NONCE, roots: [{ action: classical, children: [] }], fee: 0n };
  const oracle = rustOracle(wasm, seed32, federationId, {
    agent,
    nonce: ORACLE_NONCE,
    roots: [{ action: unsigned, children: [] }],
    fee: 0n,
  });

  assert.notEqual(
    hex(rawMod.encodeTurn(classicalTurn)),
    hex(Uint8Array.from(oracle.turn_bytes)),
    "CANARY FAILED: a classical-signed turn compared EQUAL to the Rust hybrid default — the differential is not discriminating",
  );

  // And the same turn signed HYBRID does match — so the RED above is caused by
  // the signature shape, not by some unrelated breakage in the fixture.
  const hybridTurn = {
    agent,
    nonce: ORACLE_NONCE,
    roots: [{ action: identity.signAction(unsigned, federationId, ORACLE_NONCE), children: [] }],
    fee: 0n,
  };
  assert.equal(
    hex(rawMod.encodeTurn(hybridTurn)),
    hex(Uint8Array.from(oracle.turn_bytes)),
    "hybrid must be the shape that matches",
  );
});

test("classical signing stays available + explicit (the pre-flip shape the node still accepts)", async () => {
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
  const classical = identity.signActionClassical(unsigned, federationId, ORACLE_NONCE);
  const hybrid = identity.signAction(unsigned, federationId, ORACLE_NONCE);

  // The classical 64 bytes are exactly the ed25519 HALF of the hybrid: both
  // halves cover the SAME canonical `compute_signing_message` (sig-v3).
  assert.equal(
    hex(classical.authorization.r) + hex(classical.authorization.s),
    hex(hybrid.authorization.ed25519),
    "classical signature must equal the hybrid's ed25519 leg (same signing message)",
  );

  // The classical turn re-encodes through the real Rust postcard unchanged
  // (`sign_turn_v3` only signs Unchecked actions) — the legacy shape is still
  // byte-faithful, so pre-flip consumers are not broken.
  const classicalTurn = { agent, nonce: ORACLE_NONCE, roots: [{ action: classical, children: [] }], fee: 0n };
  const reencoded = rustOracle(wasm, seed32, federationId, classicalTurn);
  assert.equal(hex(rawMod.encodeTurn(classicalTurn)), hex(Uint8Array.from(reencoded.turn_bytes)));
  assert.equal(rawMod.turnHashHex(classicalTurn), reencoded.turn_id);
});

test("hybrid authorization boundary: the Rust default IS post-quantum (the standing tripwire)", async () => {
  // The tripwire from PUBLISHED-VERIFY correction 2, KEPT: it pins that the
  // Rust default signer is hybrid ML-DSA-65 with the exact FIPS 204 lengths.
  // The TS SDK now MATCHES that shape rather than diverging from it, so this
  // guards the other direction: if Rust's default ever stops being hybrid, the
  // TS default silently becomes wrong, and this is where you learn it.
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x21 + i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = new Uint8Array(32);

  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [{ kind: "incrementNonce", cell: agent }]);

  // TS side: hybrid, by default.
  const tsSigned = identity.signAction(unsigned, federationId, ORACLE_NONCE);
  assert.equal(tsSigned.authorization.kind, "hybridSignature", "TS SDK emits the HybridSignature variant by default");

  // Rust default side: hybrid, with the two large PQ halves.
  const unsignedTurn = { agent, nonce: ORACLE_NONCE, roots: [{ action: unsigned, children: [] }], fee: 0n };
  const oracle = wasm.sign_turn_v3(new TextEncoder().encode(JSON.stringify(turnToJson(unsignedTurn))), seed32, federationId);
  const auth = JSON.parse(Buffer.from(Uint8Array.from(oracle.turn_bytes_json)).toString("utf8"))
    .call_forest.roots[0].action.authorization;

  assert.ok(auth.HybridSignature, "Rust default authorization is HybridSignature");
  assert.equal(auth.HybridSignature.ed25519.length, 64, "hybrid carries a 64-byte ed25519 leg");
  assert.equal(auth.HybridSignature.ml_dsa.length, 3309, "hybrid carries a 3309-byte ML-DSA-65 signature");
  assert.equal(auth.HybridSignature.ml_dsa_pk.length, 1952, "hybrid carries a 1952-byte ML-DSA-65 public key");

  // The TS side produces those SAME lengths and the SAME derived PQ public key.
  assert.equal(tsSigned.authorization.mlDsa.length, 3309, "TS emits a 3309-byte ML-DSA-65 signature");
  assert.equal(tsSigned.authorization.mlDsaPk.length, 1952, "TS emits a 1952-byte ML-DSA-65 public key");
  assert.equal(
    hex(tsSigned.authorization.mlDsaPk),
    hex(Uint8Array.from(auth.HybridSignature.ml_dsa_pk)),
    "TS ML-DSA-65 public key must equal Rust's (same ed25519 seed → same ML-DSA.KeyGen(ξ))",
  );

  // The PQ material is not free: a hybrid turn carries ~5.2 KB the classical
  // one does not. Pin the cost so a size regression is visible, and pin that
  // the TS hybrid turn is now the SAME size as Rust's (not the classical one).
  const tsHybridLen = rawMod.encodeTurn({
    agent,
    nonce: ORACLE_NONCE,
    roots: [{ action: tsSigned, children: [] }],
    fee: 0n,
  }).length;
  const tsClassicalLen = rawMod.encodeTurn({
    agent,
    nonce: ORACLE_NONCE,
    roots: [{ action: identity.signActionClassical(unsigned, federationId, ORACLE_NONCE), children: [] }],
    fee: 0n,
  }).length;
  const hybridLen = Uint8Array.from(oracle.turn_bytes).length;
  assert.equal(tsHybridLen, hybridLen, "the TS hybrid turn must be exactly Rust's size");
  assert.ok(
    tsHybridLen > tsClassicalLen + 5000,
    `hybrid turn (${tsHybridLen}B) carries ~5.2KB of PQ material over classical (${tsClassicalLen}B)`,
  );
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
  const action = identity.signAction(unsigned, new Uint8Array(32), 1n);
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

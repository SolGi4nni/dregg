// THE ACCEPTANCE GATE — the Rust VERIFIER, driven against TS-signed bytes.
//
// `wire.test.mjs` proves the TS SDK's bytes are byte-identical to Rust's. That
// compares an encoder against an encoder: necessary, but it cannot tell you the
// bytes are ACCEPTED. This test closes the loop at BOTH layers: Rust postcard
// decodes and verifies the complete hybrid SignedTurn perimeter against an
// independently enrolled key, then runs the real `TurnExecutor::execute` over
// the enclosed turn.
//
// The harness (`test/rust-verifier/`) is a standalone Rust bin over path deps on
// the real `dregg-turn`/`dregg-cell`/canonical signature types. It spells the
// five-field outer struct locally to avoid pulling the SDK prover graph into a
// wire test, validates the independently enrolled identity, then delegates the
// inner accept/reject verdict to `dregg-turn` itself.
//
// This is what makes the `require_pq` flip a NO-OP for TS callers: the same
// turn must be accepted in BOTH worlds.

import { test } from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { hex, raw } from "./helpers.mjs";

const here = dirname(fileURLToPath(import.meta.url));
const manifest = join(here, "rust-verifier", "Cargo.toml");
// Keep the standalone fixture isolated from the shared workspace target.
const targetDir = join(here, "rust-verifier", "target");

/**
 * Build (once) + run the Rust verifier over TS-produced turn bytes.
 * FAILS LOUD if the harness cannot build — never silently skips (M30: a gate
 * that quietly no-ops is not a gate).
 */
function rustVerify(request) {
  try {
    execFileSync("cargo", ["build", "--release", "--manifest-path", manifest], {
      env: { ...process.env, CARGO_TARGET_DIR: targetDir },
      stdio: "pipe",
    });
  } catch (e) {
    throw new Error(
      `the Rust verifier harness failed to BUILD — the acceptance gate cannot run:\n${e.stderr ?? e}`,
    );
  }
  const bin = join(targetDir, "release", "dregg-ts-sdk-verifier-harness");
  const out = execFileSync(bin, [], { input: JSON.stringify(request), stdio: "pipe" });
  return JSON.parse(out.toString("utf8"));
}

/** A TS-signed envelope + the independently provisioned Rust fixture state. */
async function tsSignedTurn({ classical = false, nonce = 0n } = {}) {
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x10 + i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = Uint8Array.from({ length: 32 }, () => 0x42);

  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [
    { kind: "setField", cell: agent, index: 3, value: rawMod.fieldFromU64(77n) },
  ]);
  const action = classical
    ? identity.signActionClassical(unsigned, federationId, nonce)
    : identity.signAction(unsigned, federationId, nonce);

  const turn = { agent, nonce, roots: [{ action, children: [] }], fee: 0n };
  const turnBytes = rawMod.encodeTurn(turn);
  const envelope = identity.signTurnEnvelope(turn);
  return {
    request: {
      signed_turn_bytes_hex: hex(envelope),
      federation_id_hex: hex(federationId),
      public_key_hex: identity.publicKeyHex,
      // Independently provision the Rust verifier's identity registry. The
      // verifier must never trust either public key carried by the envelope.
      pq_public_key_hex: hex(identity.mlDsaPublicKey()),
      token_id_hex: hex(rawMod.defaultTokenId()),
      balance: 1000000,
    },
    identity,
    turn,
    turnBytes,
    envelope,
    federationId,
  };
}

test("the Rust verifier ACCEPTS a TS HYBRID-signed turn — at require_pq OFF *and* ON", async () => {
  const fixture = await tsSignedTurn();
  const res = rustVerify(fixture.request);

  assert.ok(res.decoded, `Rust postcard could not decode the TS SignedTurn: ${res.decode_error}`);
  assert.ok(res.outer.accepted, `Rust rejected the outer hybrid envelope: ${res.outer.detail}`);
  assert.equal(res.outer_pq_signature_len, 3309, "Rust sees the full outer ML-DSA-65 signature");
  assert.equal(res.outer_pq_signer_len, 1952, "Rust sees the full outer ML-DSA-65 public key");
  assert.equal(res.roundtrip_hex, hex(fixture.envelope), "Rust postcard round-trip must preserve every envelope byte");
  // The Rust type system — not a TS claim — reports the shape it received.
  assert.equal(res.authorization, "HybridSignature", "Rust decoded a hybrid authorization");
  assert.equal(res.ml_dsa_len, 3309, "Rust sees a full ML-DSA-65 signature");
  assert.equal(res.ml_dsa_pk_len, 1952, "Rust sees a full ML-DSA-65 public key");

  // Today's node.
  assert.ok(
    res.require_pq_off.accepted,
    `the Rust executor REJECTED the TS hybrid turn at require_pq=off: ${res.require_pq_off.detail}`,
  );
  // THE CLIFF, crossed: the post-flip node accepts the same turn unchanged.
  assert.ok(
    res.require_pq_on.accepted,
    `the Rust executor REJECTED the TS hybrid turn at require_pq=ON — the flip would take TS agents offline: ${res.require_pq_on.detail}`,
  );
});

test("CANARY: the same turn signed CLASSICAL is accepted at require_pq=off but REJECTED at require_pq=on", async () => {
  // This is the cliff, reproduced. It proves (a) the acceptance gate above is
  // real — it can reject — and (b) exactly what shipping classical would cost
  // the day the node flips. A classical turn is fine today and dark tomorrow;
  // the hybrid turn above is fine in both worlds. That difference IS the point
  // of this work.
  const fixture = await tsSignedTurn({ classical: true });
  const res = rustVerify(fixture.request);

  assert.ok(res.decoded, `Rust could not decode the TS classical turn: ${res.decode_error}`);
  assert.ok(res.outer.accepted, "the outer envelope remains mandatory hybrid even for this inner-policy canary");
  assert.equal(res.authorization, "Signature", "the canary rides the legacy classical variant");
  assert.ok(
    res.require_pq_off.accepted,
    `classical must still be accepted pre-flip (do not break existing users): ${res.require_pq_off.detail}`,
  );
  assert.ok(
    !res.require_pq_on.accepted,
    "CANARY FAILED: a classical-only turn was accepted at require_pq=ON — the PQ requirement is not being enforced, so the hybrid gate above proves nothing",
  );
});

test("FALSIFIER: a hybrid signature bound to the WRONG turn nonce is REJECTED (sig-v3 nonce binding is load-bearing)", async () => {
  // Scope, honestly: the accept leg rides nonce 0, because the executor
  // requires `turn.nonce == cell.state.nonce()` and a freshly-inserted cell is
  // at 0 — a non-zero nonce would be rejected for a nonce MISMATCH, telling us
  // nothing about the signature. So the content of this test is the falsifier
  // below, not the nonce value.
  const fixture = await tsSignedTurn({ nonce: 0n });
  const res = rustVerify(fixture.request);
  assert.ok(res.require_pq_on.accepted, res.require_pq_on.detail);

  // Sign over nonce 5, ride the turn at nonce 0: if `dregg-action-sig-v3`'s
  // nonce binding were absent (the pre-fix `sig-v2` TS behaviour), this would
  // still verify. It must not.
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");
  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x10 + i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = Uint8Array.from({ length: 32 }, () => 0x42);
  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [
    { kind: "setField", cell: agent, index: 3, value: rawMod.fieldFromU64(77n) },
  ]);
  const mismatched = identity.signAction(unsigned, federationId, 5n);
  const badTurn = { agent, nonce: 0n, roots: [{ action: mismatched, children: [] }], fee: 0n };
  const bad = rustVerify({
    signed_turn_bytes_hex: hex(identity.signTurnEnvelope(badTurn)),
    federation_id_hex: hex(federationId),
    public_key_hex: identity.publicKeyHex,
    pq_public_key_hex: hex(identity.mlDsaPublicKey()),
    token_id_hex: hex(rawMod.defaultTokenId()),
    balance: 1000000,
  });
  assert.ok(
    !bad.require_pq_off.accepted,
    "a signature bound to the WRONG turn nonce must be rejected (sig-v3 nonce binding is load-bearing)",
  );
});

test("ABSENT outer PQ material cannot be emitted canonically and is rejected by Rust", async () => {
  const rawMod = await raw();
  const fixture = await tsSignedTurn();
  const turnHash = rawMod.turnHash(fixture.turn);
  const ed = fixture.identity.signBytes(turnHash);

  assert.throws(
    () => rawMod.encodeSignedTurn(
      fixture.turn,
      ed,
      fixture.identity.publicKey,
      new Uint8Array(),
      new Uint8Array(),
    ),
    /pqSignature must be exactly 3309 bytes/,
    "the TS encoder has no classical outer-envelope mode",
  );

  // Explicitly serialized empty trailing Vec fields: this is the only
  // decodable absent-PQ shape, and it must reach (then fail) the outer gate.
  const classicalPrefixLen = fixture.turnBytes.length + 1 + 64 + 1 + 32;
  const absent = Uint8Array.from([
    ...fixture.envelope.subarray(0, classicalPrefixLen),
    0x00, // pq_signature Vec length
    0x00, // pq_signer Vec length
  ]);
  const res = rustVerify({ ...fixture.request, signed_turn_bytes_hex: hex(absent) });
  assert.ok(res.decoded, `the historical prefix should reach the explicit absent-PQ check: ${res.decode_error}`);
  assert.ok(!res.outer.accepted, "Rust must reject an envelope with absent outer PQ material");
  assert.match(res.outer.detail, /missing outer ML-DSA/);
});

test("TRAILING bytes after an otherwise valid SignedTurn are rejected by Rust postcard", async () => {
  const fixture = await tsSignedTurn();
  const trailing = Uint8Array.from([...fixture.envelope, 0xa5]);
  const res = rustVerify({ ...fixture.request, signed_turn_bytes_hex: hex(trailing) });
  assert.ok(!res.decoded, "Rust must reject a valid envelope with unconsumed trailing bytes");
});

test("SUBSTITUTION: a valid attacker ML-DSA pair cannot replace the enrolled outer PQ identity", async () => {
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");
  const fixture = await tsSignedTurn();
  const turnHash = rawMod.turnHash(fixture.turn);
  const attacker = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0xd0 + i));
  const attackerKey = rawMod.mlDsaKeypairFromEd25519Seed(
    Uint8Array.from({ length: 32 }, (_, i) => 0xd0 + i),
  );
  const substituted = rawMod.encodeSignedTurn(
    fixture.turn,
    fixture.identity.signBytes(turnHash),
    fixture.identity.publicKey,
    rawMod.mlDsaSign(attackerKey.secretKey, turnHash),
    attacker.mlDsaPublicKey(),
  );
  const res = rustVerify({ ...fixture.request, signed_turn_bytes_hex: hex(substituted) });
  assert.ok(res.decoded, res.decode_error);
  assert.ok(!res.outer.accepted, "a self-consistent attacker PQ pair is not an authority");
  assert.match(res.outer.detail, /substituted outer ML-DSA public key/);
  assert.ok(!res.require_pq_on.accepted, "the rejected outer envelope never reaches execution");
});

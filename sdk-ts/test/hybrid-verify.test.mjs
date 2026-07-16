// THE ACCEPTANCE GATE — the Rust VERIFIER, driven against TS-signed bytes.
//
// `wire.test.mjs` proves the TS SDK's bytes are byte-identical to Rust's. That
// compares an encoder against an encoder: necessary, but it cannot tell you the
// bytes are ACCEPTED. This test closes the loop by running the real
// `TurnExecutor::execute` — the same public entry the node calls — over a turn
// TypeScript signed, at `require_pq` OFF (today's node) and ON (the post-flip
// node).
//
// The harness (`test/rust-verifier/`) is a standalone Rust bin over path deps on
// the real `dregg-turn`/`dregg-cell`. It re-implements nothing: postcard decodes
// with the real `Turn` type, and every accept/reject verdict is computed by
// `dregg-turn` itself, so it cannot bless a TS bug.
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
// The harness's DEFAULT target dir. The repo's root `.gitignore` carries a bare
// `target` pattern, which matches at any depth — so this stays untracked
// without touching a shared manifest or the root ignore file.
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

/** A TS-signed turn + the fixture the Rust side needs to rebuild the cell. */
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
  return {
    turn_bytes_hex: hex(rawMod.encodeTurn(turn)),
    federation_id_hex: hex(federationId),
    public_key_hex: identity.publicKeyHex,
    token_id_hex: hex(rawMod.defaultTokenId()),
    balance: 1000000,
  };
}

test("the Rust verifier ACCEPTS a TS HYBRID-signed turn — at require_pq OFF *and* ON", async () => {
  const res = rustVerify(await tsSignedTurn());

  assert.ok(res.decoded, `Rust postcard could not decode the TS turn: ${res.decode_error}`);
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
  const res = rustVerify(await tsSignedTurn({ classical: true }));

  assert.ok(res.decoded, `Rust could not decode the TS classical turn: ${res.decode_error}`);
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
  const res = rustVerify(await tsSignedTurn({ nonce: 0n }));
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
    turn_bytes_hex: hex(rawMod.encodeTurn(badTurn)),
    federation_id_hex: hex(federationId),
    public_key_hex: identity.publicKeyHex,
    token_id_hex: hex(rawMod.defaultTokenId()),
    balance: 1000000,
  });
  assert.ok(
    !bad.require_pq_off.accepted,
    "a signature bound to the WRONG turn nonce must be rejected (sig-v3 nonce binding is load-bearing)",
  );
});

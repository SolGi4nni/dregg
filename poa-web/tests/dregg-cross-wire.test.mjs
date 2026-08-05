import assert from "node:assert/strict";
import {
  createHash,
  createPrivateKey,
  createPublicKey,
  verify,
} from "node:crypto";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

import {
  normalizeHoldingCapability,
  normalizeHoldingChallenge,
  normalizeHoldingStatus,
} from "../src/dregg-admission-panel.js";
import {
  DREGG_MINT,
  DREGG_OWNER_BIND_DOMAIN,
  DREGG_TOKEN_PROGRAM,
  base58ToBytes,
  base64ToBytes,
  bytesToBase64,
} from "../src/dregg-wallet.js";

const VECTOR_SHA256 = "0cce843c20b8b12c13fc6095f7876bf89bd683b8bf6e9ece3d7fb44c3cd25993";
const MAINNET_GENESIS = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const CHALLENGE_DOMAIN = "path-of-angels/dregg-holding/challenge/v1";
const RECEIPT_DOMAIN = "path-of-angels/dregg-holding/receipt/v1";

function sha256(...parts) {
  return createHash("sha256").update(Buffer.concat(parts.map((part) => Buffer.from(part)))).digest();
}

function u32(value) {
  const bytes = Buffer.alloc(4);
  bytes.writeUInt32BE(value);
  return bytes;
}

function u64(value) {
  const bytes = Buffer.alloc(8);
  bytes.writeBigUInt64BE(BigInt(value));
  return bytes;
}

function put(bytes) {
  return Buffer.concat([u32(bytes.length), Buffer.from(bytes)]);
}

test("byte-pinned vector reproduces Rust challenge, signing, receipt, and JSON shapes", async () => {
  const raw = await readFile(new URL("./fixtures/dregg-holding-cross-wire-v1.json", import.meta.url));
  assert.equal(sha256(raw).toString("hex"), VECTOR_SHA256);
  const vector = JSON.parse(raw);
  const { challenge, capability, status, inputs } = vector;

  const seed = Buffer.from(inputs.wallet_seed_hex, "hex");
  const privateKey = createPrivateKey({
    key: Buffer.concat([Buffer.from("302e020100300506032b657004220420", "hex"), seed]),
    format: "der",
    type: "pkcs8",
  });
  const wallet = createPublicKey(privateKey).export({ format: "der", type: "spki" }).subarray(-32);
  assert.deepEqual(wallet, Buffer.from(base58ToBytes(challenge.wallet)));

  const issuedAt = challenge.issued_at;
  const transcript = Buffer.concat([
    Buffer.from(CHALLENGE_DOMAIN),
    Buffer.from(inputs.federation_id_hex, "hex"),
    Buffer.from("https://beta.pathofangels.network"),
    Buffer.from("pathofangels.network"),
    Buffer.from("solana:mainnet-beta"),
    Buffer.from(base58ToBytes(MAINNET_GENESIS)),
    Buffer.from(inputs.rpc_endpoint_id_hex, "hex"),
    Buffer.from(base58ToBytes(DREGG_MINT)),
    Buffer.from(base58ToBytes(DREGG_TOKEN_PROGRAM)),
    wallet,
    Buffer.from(inputs.nonce_hex, "hex"),
    u64(1),
    u64(challenge.min_context_slot),
    u64(300),
    u64(120),
    u64(issuedAt),
    u64(challenge.expires_at),
  ].map(put));
  const voter = sha256(transcript);
  assert.equal(voter.toString("hex"), inputs.voter_hex);
  const challengeId = sha256(Buffer.from(CHALLENGE_DOMAIN), transcript);
  assert.equal(challengeId.toString("base64url"), challenge.challenge_id);

  const signingMessage = Buffer.concat([Buffer.from(DREGG_OWNER_BIND_DOMAIN), wallet, voter]);
  assert.equal(signingMessage.toString("base64"), challenge.signing_message_base64);
  assert.equal(bytesToBase64(base64ToBytes(vector.signature_base64)), vector.signature_base64);
  assert.equal(verify(null, signingMessage, createPublicKey(privateKey), Buffer.from(vector.signature_base64, "base64")), true);

  const receiptId = sha256(
    Buffer.from(RECEIPT_DOMAIN),
    challengeId,
    Buffer.from(inputs.rpc_endpoint_id_hex, "hex"),
    wallet,
    Buffer.from(base58ToBytes(DREGG_MINT)),
    u64(1),
    u64(capability.snapshot_slot),
    Buffer.from(inputs.token_account_hex, "hex"),
    u64(capability.issued_at),
    u64(capability.expires_at),
  );
  assert.equal(receiptId.toString("base64url"), capability.receipt_id);

  const parsedChallenge = normalizeHoldingChallenge(
    challenge,
    { walletAddress: challenge.wallet },
    issuedAt * 1000,
  );
  const parsedCapability = normalizeHoldingCapability(
    capability,
    { walletAddress: challenge.wallet },
    capability.issued_at * 1000,
  );
  const parsedStatus = normalizeHoldingStatus(
    status,
    { receiptId: capability.receipt_id, walletAddress: challenge.wallet },
    capability.issued_at * 1000,
  );
  assert.deepEqual(Buffer.from(parsedChallenge.signingMessage), signingMessage);
  assert.equal(parsedCapability.receiptId, capability.receipt_id);
  assert.equal(parsedStatus.credential.receiptId, capability.receipt_id);
  assert.equal(challenge.expires_at - challenge.issued_at, 300);
  assert.equal(capability.expires_at - capability.issued_at, 120);
});

test("checked Rust sources retain the constants and response formats pinned by the vector", async () => {
  const [gate, api, binding] = await Promise.all([
    readFile(new URL("../../poa-solana-gate/src/lib.rs", import.meta.url), "utf8"),
    readFile(new URL("../../node/src/poa_holding_api.rs", import.meta.url), "utf8"),
    readFile(new URL("../../dregg-governance/src/holding_weight.rs", import.meta.url), "utf8"),
  ]);
  assert.match(gate, /CHALLENGE_DOMAIN:\s*&\[u8\]\s*=\s*b"path-of-angels\/dregg-holding\/challenge\/v1"/u);
  assert.match(gate, /RECEIPT_DOMAIN:\s*&\[u8\]\s*=\s*b"path-of-angels\/dregg-holding\/receipt\/v1"/u);
  assert.match(gate, /challenge_ttl_secs:\s*300/u);
  assert.match(gate, /capability_ttl_secs:\s*120/u);
  assert.match(binding, /BIND_DOMAIN:\s*&\[u8\]\s*=\s*b"dregg-holding-weight-bind-v1"/u);
  for (const format of [
    "poa-dregg-holding-challenge-v1",
    "poa-dregg-holding-capability-v1",
    "poa-dregg-holding-status-v1",
  ]) assert.match(api, new RegExp(format, "u"));
});

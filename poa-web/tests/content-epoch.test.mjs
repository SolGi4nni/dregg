import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { activationDigestBytes, authenticateContentEpoch, contentEpochSigningBytes } from "../src/content-epoch.js";

const encoder = new TextEncoder();

test("web signing bytes and Ed25519 verification match the curator shared vector", async () => {
  const vector = JSON.parse(await readFile(new URL("../../poa-curator/test-vectors/content-epoch-v1.json", import.meta.url), "utf8"));
  const manifestBytes = encoder.encode(vector.manifest_utf8);
  const envelope = {
    schema: "POA-CONTENT-EPOCH-SIGNATURE-V1",
    manifest_sha256: vector.manifest_sha256,
    curator_pubkey: vector.curator_pubkey,
    content_epoch: vector.content_epoch,
    counter: vector.counter,
    signature: vector.signature,
  };
  const key = { schema: "POA-CURATOR-KEY-V1", curator_pubkey: vector.curator_pubkey };
  const authenticated = await authenticateContentEpoch({
    manifestBytes,
    signatureBytes: encoder.encode(JSON.stringify(envelope)),
    keyBytes: encoder.encode(JSON.stringify(key)),
    expectedContentEpoch: 1,
    expectedCounter: 1,
  });
  assert.equal(authenticated.manifestDigest, vector.manifest_sha256);
  assert.equal(authenticated.activationDigest, vector.activation_digest);
  assert.equal(Buffer.from(contentEpochSigningBytes(authenticated, manifestBytes)).toString("hex"), vector.message_hex);
  assert.equal(Buffer.from(activationDigestBytes(authenticated)).toString("hex"), vector.activation_preimage_hex);
  assert.equal(Buffer.from("pathofangels.network/content-epoch/v1\0").toString("hex"), vector.domain_hex);
});

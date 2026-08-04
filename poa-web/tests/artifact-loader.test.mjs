import assert from "node:assert/strict";
import { test } from "node:test";
import { ArtifactRefusal, fnv1a64, loadPOAG1, sha256Hex, validateManifest } from "../src/poag1.js";
import { actualBundleFiles, actualFetch, fetchMap } from "./actual-bundle.mjs";

const encoder = new TextEncoder();

async function expectRefusal(promise, code) {
  await assert.rejects(promise, (error) => error instanceof ArtifactRefusal && error.code === code);
}

test("loads the actual curator-authenticated Lean-emitted POAG1 bundle", async () => {
  const bundle = await loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: 1,
    expectedCounter: 1,
    fetcher: await actualFetch(),
  });
  assert.equal(bundle.manifest.format, "POAG1");
  assert.equal(bundle.manifest.authority, "Dregg2.Games.PathOfAngels");
  assert.equal(bundle.contentEpoch.contentEpoch, 1);
  assert.match(bundle.manifestDigest, /^sha256:[0-9a-f]{64}$/);
  assert.deepEqual(Object.keys(bundle.payloads), [
    "schema.json",
    "catalog.json",
    "games/relay-repair.json",
    "games/salvage-lock.json",
    "games/signal-triangulation.json",
  ]);
});
test("refuses a missing artifact instead of falling back", async () => {
  const files = await actualBundleFiles();
  await expectRefusal(loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: 1,
    expectedCounter: 1,
    fetcher: fetchMap({
      "manifest.json": files.manifest,
      "manifest.sig.json": files.signature,
      "poa-curator-key.json": files.key,
      "schema.json": files.schema,
      "catalog.json": files.catalog,
    }),
  }), "fetch-status");
});

test("refuses a payload that differs from both signed SHA-256 and FNV pins", async () => {
  const files = await actualBundleFiles();
  const modified = new Uint8Array(files.signal.byteLength + 1);
  modified.set(files.signal);
  modified[modified.length - 1] = 0x20;
  await expectRefusal(loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: 1,
    expectedCounter: 1,
    fetcher: await actualFetch({ "games/signal-triangulation.json": modified }),
  }), "byte-length");
});

test("a self-consistent attacker manifest and payload cannot replace signed content", async () => {
  const files = await actualBundleFiles();
  const original = JSON.parse(new TextDecoder().decode(files.manifest));
  const modifiedPayload = new Uint8Array(files.signal.byteLength + 1);
  modifiedPayload.set(files.signal);
  modifiedPayload[modifiedPayload.length - 1] = 0x20;
  const entry = original.artifacts.find((pin) => pin.path === "games/signal-triangulation.json");
  entry.bytes = modifiedPayload.byteLength;
  entry.sha256 = `sha256:${await sha256Hex(modifiedPayload)}`;
  entry.fnv1a64 = fnv1a64(modifiedPayload);
  const repinnedManifest = encoder.encode(JSON.stringify(original));
  await expectRefusal(loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: 1,
    expectedCounter: 1,
    fetcher: await actualFetch({ "manifest.json": repinnedManifest, "games/signal-triangulation.json": modifiedPayload }),
  }), "manifest-digest");
});

test("a previously valid content epoch is rejected by the deployment rollback pin", async () => {
  await expectRefusal(loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: 2,
    expectedCounter: 1,
    fetcher: await actualFetch(),
  }), "epoch-rollback");
});

test("strict manifest parsing rejects field and artifact-order drift", async () => {
  const files = await actualBundleFiles();
  const manifest = JSON.parse(new TextDecoder().decode(files.manifest));
  assert.throws(() => validateManifest({ ...manifest, note: "accept me" }), { code: "unknown-field" });
  const reordered = structuredClone(manifest);
  [reordered.artifacts[0], reordered.artifacts[1]] = [reordered.artifacts[1], reordered.artifacts[0]];
  assert.throws(() => validateManifest(reordered), { code: "artifact-order" });
});

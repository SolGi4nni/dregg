import assert from "node:assert/strict";
import { test } from "node:test";
import { ArtifactRefusal, fnv1a64, loadPOAG1, sha256Hex, validateManifest } from "../src/poag1.js";
import { loadMissionCatalog } from "../src/mission-catalog.js";
import { POA_EXPECTED_CONTENT_EPOCH, POA_EXPECTED_CURATOR_COUNTER } from "../src/trust-config.js";
import { actualBundleFiles, actualFetch, fetchMap } from "./actual-bundle.mjs";

const encoder = new TextEncoder();

async function expectRefusal(promise, code) {
  await assert.rejects(promise, (error) => error instanceof ArtifactRefusal && error.code === code);
}

test("loads the actual curator-authenticated Lean-emitted POAG1 bundle", async () => {
  const bundle = await loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
    fetcher: await actualFetch(),
  });
  assert.equal(bundle.manifest.format, "POAG1");
  assert.equal(bundle.manifest.authority, "Dregg2.Games.PathOfAngels");
  assert.equal(bundle.contentEpoch.contentEpoch, 1);
  assert.match(bundle.manifestDigest, /^sha256:[0-9a-f]{64}$/);
  // ⚠ MANIFEST order, not lexicographic — `artificer-logic` is the FIRST game, ahead
  // of black-box. `GAME_SPECS` in mission-catalog.js is in MISSION order (1..7) instead.
  // Two lists that both read as "the games", keyed differently; the client refuses on order.
  assert.deepEqual(Object.keys(bundle.payloads), [
    "schema.json",
    "catalog.json",
    "games/artificer-logic.json",
    "games/black-box-reconstruction.json",
    "games/deck-descent.json",
    "games/relay-repair.json",
    "games/salvage-lock.json",
    "games/signal-triangulation.json",
    "games/vent-crawl.json",
  ]);
});

test("the client accepts the curator-signed counter-11 seven-game bundle end to end", async () => {
  const bundle = await loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
    fetcher: await actualFetch(),
  });
  assert.equal(bundle.contentEpoch.counter, 12);
  assert.equal(bundle.manifest.artifacts.length, 9);
  const missions = await loadMissionCatalog(bundle);
  // MISSION order (1..7) — deliberately NOT the manifest's path order above.
  assert.deepEqual(missions.map((mission) => mission.gameId), [
    "signal-triangulation",
    "relay-repair",
    "salvage-lock",
    "black-box-reconstruction",
    "deck-descent",
    "artificer-logic",
    "vent-crawl",
  ]);
  const blackBox = missions.find((mission) => mission.gameId === "black-box-reconstruction");
  assert.equal(blackBox.missionId, 4);
  assert.equal(blackBox.ruleset, "blackbox-v2");
  // 15 was the worst case of the DUMBEST strategy: the two-class minimax was ALSO 15
  // (Hall forces four eliminations to pin the first cell, and all four leave with it), so
  // any systematic scan won 100% and no budget could have separated good play from it.
  // A third answer class took the minimax to 11, so this is now the worst case of OPTIMAL play.
  assert.equal(blackBox.actionLimit, 11);
  assert.equal(blackBox.instanceDisclosure, "oracle-only");
});

test("the previous six-artifact shape is refused now that all seven games are enrolled", async () => {
  const files = await actualBundleFiles();
  const manifest = JSON.parse(new TextDecoder().decode(files.manifest));
  // Drop one enrolled descriptor and the count pin must REFUSE the short set rather
  // than warn. Kept keyed on a real game rather than a bare number so it fails for the
  // reason it names.
  manifest.artifacts = manifest.artifacts.filter((pin) => pin.path !== "games/vent-crawl.json");
  assert.equal(manifest.artifacts.length, 8);
  assert.throws(() => validateManifest(manifest), { code: "artifact-set" });
});

test("a curator counter below the deployment pin is refused as a rollback", async () => {
  await expectRefusal(loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER - 1,
    fetcher: await actualFetch(),
  }), "counter-rollback");
});
test("refuses a missing artifact instead of falling back", async () => {
  const files = await actualBundleFiles();
  await expectRefusal(loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
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
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
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
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
    fetcher: await actualFetch({ "manifest.json": repinnedManifest, "games/signal-triangulation.json": modifiedPayload }),
  }), "manifest-digest");
});

test("a previously valid content epoch is rejected by the deployment rollback pin", async () => {
  await expectRefusal(loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH + 1,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
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

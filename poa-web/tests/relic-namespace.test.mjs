import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { ArtifactRefusal, fnv1a64, sha256Hex, validateManifest } from "../src/poag1.js";
import { loadMissionCatalog } from "../src/mission-catalog.js";

const bundleRoot = new URL("../../poa/artifacts/poag1/", import.meta.url);
const decoder = new TextDecoder();

/**
 * The emitted bundle, byte-pinned against its own manifest, WITHOUT the curator
 * signature.
 *
 * ⚠ Signature-free on purpose, and it is not a shortcut: the relic renumbering
 * changed `catalog.json` and `schema.json`, so `manifest.json` changed and the
 * detached signature was deleted by `check-poag1-artifacts.sh --update` — the
 * bundle is UNSIGNED until the curator ceremony re-signs it. Everything the
 * loader does with bytes still happens here (length, SHA-256 and FNV pins per
 * artifact); the one thing skipped is the Ed25519 envelope, which is the
 * operator's act and is covered by `artifact-loader.test.mjs` once signed.
 *
 * ⚠ Deliberately not `canonical-descriptors.mjs`, which builds a similar envelope:
 * that one does not check the manifest byte pins and has no hook for mutating a
 * payload before the catalog is read, and both are the point here.
 */
async function emittedBundle(mutate) {
  const manifestBytes = new Uint8Array(await readFile(new URL("manifest.json", bundleRoot)));
  const manifest = validateManifest(JSON.parse(decoder.decode(manifestBytes)));
  const payloads = Object.create(null);
  for (const entry of manifest.artifacts) {
    const bytes = new Uint8Array(await readFile(new URL(entry.path, bundleRoot)));
    assert.equal(bytes.byteLength, entry.bytes, `${entry.path} byte length is not its manifest pin`);
    assert.equal(`sha256:${await sha256Hex(bytes)}`, entry.sha256, `${entry.path} is not its SHA-256 pin`);
    assert.equal(fnv1a64(bytes), entry.fnv1a64, `${entry.path} is not its FNV pin`);
    payloads[entry.path] = { bytes, json: JSON.parse(decoder.decode(bytes)), mediaType: entry.mediaType };
  }
  if (mutate) mutate(payloads);
  const manifestDigest = `sha256:${await sha256Hex(manifestBytes)}`;
  return {
    manifest,
    manifestDigest,
    contentEpoch: {
      schema: "POA-CONTENT-EPOCH-SIGNATURE-V1",
      manifestDigest,
      activationDigest: `sha256:${"11".repeat(32)}`,
      contentEpoch: 1,
      counter: 10,
    },
    payloads,
  };
}

const relicOwner = (relic) => Math.floor(relic / 16);

async function refusal(mutate, code, assertMutated) {
  const bundle = await emittedBundle(mutate);
  // ⚠ The mutation is asserted PRESENT before the verdict is read. A refusal test
  // whose mutation quietly stopped applying still passes, and then guards nothing.
  assertMutated(bundle.payloads["catalog.json"].json);
  await assert.rejects(loadMissionCatalog(bundle), (error) => {
    assert.ok(error instanceof ArtifactRefusal, `expected a refusal, got ${error}`);
    assert.equal(error.code, code, `refused as ${error.code}: ${error.message}`);
    return true;
  });
}

test("the seven-game catalog loads with every relic inside its own mission block", async () => {
  const missions = await loadMissionCatalog(await emittedBundle());
  assert.deepEqual(
    missions.map((mission) => [mission.missionId, [...mission.allowedRelics]]),
    [[1, [16]], [2, [32]], [3, [48]], [4, [64]], [5, [80, 81, 82, 83]], [6, [96]], [7, [112]]],
  );
  // Deck Descent is the multi-relic game the old one-relic rule could not express:
  // mouth, west and TWO east relics, all slots of block 5.
  const descent = missions.find((mission) => mission.gameId === "deck-descent");
  assert.equal(descent.allowedRelics.length, 4);
  assert.deepEqual([...descent.reward.relics], [82, 83]);

  for (const mission of missions) {
    for (const relic of mission.allowedRelics) {
      assert.equal(relicOwner(relic), mission.missionId, `relic ${relic} is not owned by mission ${mission.missionId}`);
    }
  }
  const claimed = missions.flatMap((mission) => [...mission.allowedRelics]);
  assert.equal(new Set(claimed).size, claimed.length, "two missions claim the same relic");
});

test("a catalog where two missions claim the same relic is refused by name", async () => {
  // Artificer Logic (mission 6) claims Deck Descent's first relic. Both missions
  // are otherwise well-formed; the only defect is that the namespace is shared.
  await refusal(
    (payloads) => { payloads["catalog.json"].json.missions[5].allowed_relics = [80]; },
    "catalog-relic-collision",
    (catalog) => {
      assert.deepEqual(catalog.missions[5].allowed_relics, [80]);
      assert.ok(catalog.missions[4].allowed_relics.includes(80), "the mutation must actually collide with mission 5");
    },
  );
});

test("a relic outside the declaring mission's block is refused by name", async () => {
  await refusal(
    (payloads) => { payloads["catalog.json"].json.missions[5].allowed_relics = [999]; },
    "catalog-relic-namespace",
    (catalog) => {
      assert.deepEqual(catalog.missions[5].allowed_relics, [999]);
      assert.notEqual(relicOwner(999), 6, "the mutation must actually leave mission 6's block");
    },
  );
});

test("the allowlists the counter-9 bundle shipped are refused, not reinterpreted", async () => {
  // ⚑ The exact shape of the defect: relic ids equal to mission ids, with Deck
  // Descent holding 5..8 and therefore Artificer's 6 and Vent Crawl's 7.
  await refusal(
    (payloads) => {
      const missions = payloads["catalog.json"].json.missions;
      const legacy = [[1], [2], [3], [4], [5, 6, 7, 8], [6], [7]];
      missions.forEach((mission, index) => { mission.allowed_relics = legacy[index]; });
    },
    "catalog-relic-namespace",
    (catalog) => {
      assert.deepEqual(catalog.missions[4].allowed_relics, [5, 6, 7, 8]);
      assert.deepEqual(catalog.missions[5].allowed_relics, [6]);
    },
  );
});

test("a bundle declaring a different relic namespace is refused rather than followed", async () => {
  const bundle = await emittedBundle((payloads) => {
    payloads["schema.json"].json.contract.relic_namespace.block_width = 8;
  });
  assert.equal(bundle.payloads["schema.json"].json.contract.relic_namespace.block_width, 8);
  await assert.rejects(loadMissionCatalog(bundle), (error) => {
    assert.ok(error instanceof ArtifactRefusal);
    assert.equal(error.code, "catalog-relic-namespace");
    return true;
  });
});

test("the signed schema publishes the rule the client pins", async () => {
  const bundle = await emittedBundle();
  assert.deepEqual(bundle.payloads["schema.json"].json.contract.relic_namespace, {
    scheme: "per-mission-block",
    block_width: 16,
    owner: "relic_id / block_width == mission_id",
    cross_mission: "disjoint-by-construction",
    authored_in: "Dregg2.Games.PathOfAngels.RelicNamespace",
    violation: "refuse",
  });
});

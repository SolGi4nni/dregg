import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { finiteTableAuthority } from "../src/mission-catalog.js";
import { loadMissionCatalog } from "../src/mission-catalog.js";
import { validateManifest } from "../src/poag1.js";
import { loadRelayRepairDescriptor } from "../src/relay-runtime.js";
import { loadSalvageLockDescriptor } from "../src/salvage-runtime.js";

const canonical = new URL("../../poa/artifacts/poag1/", import.meta.url);
const parse = async (path) => JSON.parse(await readFile(new URL(path, canonical), "utf8"));

async function canonicalUnsignedBundle() {
  const rawManifest = await parse("manifest.json");
  const manifest = validateManifest(rawManifest);
  const payloads = Object.create(null);
  for (const pin of manifest.artifacts) {
    const bytes = new Uint8Array(await readFile(new URL(pin.path, canonical)));
    payloads[pin.path] = { bytes, json: JSON.parse(new TextDecoder().decode(bytes)), mediaType: pin.mediaType };
  }
  const manifestDigest = `sha256:${"d".repeat(64)}`;
  return {
    manifest,
    manifestDigest,
    contentEpoch: {
      schema: "POA-CONTENT-EPOCH-SIGNATURE-V1",
      manifestDigest,
      activationDigest: `sha256:${"e".repeat(64)}`,
      contentEpoch: 1,
      counter: 1,
    },
    payloads,
  };
}

test("the exact unsigned candidate catalog is ready for three-game activation", async () => {
  const missions = await loadMissionCatalog(await canonicalUnsignedBundle());
  assert.deepEqual(missions.map((mission) => mission.gameId), ["signal-triangulation", "relay-repair", "salvage-lock"]);
  assert.ok(missions.every((mission) => mission.rewardClass === "non-economic-demo" && mission.ballotRegime === "none"));
});

test("canonical Lean-emitted Relay and Salvage bytes match the strict web consumers", async () => {
  const [catalog, relayJson, salvageJson] = await Promise.all([
    parse("catalog.json"),
    parse("games/relay-repair.json"),
    parse("games/salvage-lock.json"),
  ]);
  const mission = (gameId, activationDigest) => {
    const raw = catalog.missions.find((candidate) => candidate.descriptor_path === `games/${gameId}.json`);
    return {
      missionId: raw.mission_id,
      activatedManifest: `sha256:${"a".repeat(64)}`,
      activationDigest,
      contentEpoch: raw.epoch,
      curatorCounter: 1,
      federationId: raw.federation_id,
      contentRoot: raw.content_root,
      contentSession: raw.content_session,
      runSeed: raw.run_seed,
      rewardClass: raw.reward_class,
    };
  };
  const relay = loadRelayRepairDescriptor(relayJson, finiteTableAuthority(mission("relay-repair", `sha256:${"b".repeat(64)}`)));
  const salvage = loadSalvageLockDescriptor(salvageJson, finiteTableAuthority(mission("salvage-lock", `sha256:${"c".repeat(64)}`)));
  assert.deepEqual([relay.states.length, relay.actions.length, relay.transitions.length], [15, 4, 60]);
  assert.deepEqual([salvage.states.length, salvage.actions.length, salvage.transitions.length], [164, 6, 984]);
  assert.equal(relay.initialState, "relay:0:4:0");
  assert.equal(salvage.initialState, "salvage:0:none:0");
});

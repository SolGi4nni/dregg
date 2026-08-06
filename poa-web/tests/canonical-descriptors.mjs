import { readFile } from "node:fs/promises";
import { finiteTableAuthority, loadMissionCatalog, missionByGameId } from "../src/mission-catalog.js";
import { validateManifest } from "../src/poag1.js";
import { loadRelayRepairDescriptor } from "../src/relay-runtime.js";
import { loadSalvageLockDescriptor } from "../src/salvage-runtime.js";

const canonical = new URL("../../poa/artifacts/poag1/", import.meta.url);

/**
 * The REAL Lean-emitted descriptors, loaded through the real loaders.
 *
 * Controller tests use these rather than a hand-written fixture on purpose: the
 * Salvage loader pins its emitted 632-state closure, and a fixture that could
 * satisfy that pin would be a second copy of the table maintained by hand — the
 * exact mirror this repo keeps paying for. Signature checking is out of scope
 * here (poag1.test covers it); the bytes are the committed ones.
 */
export async function canonicalDescriptors() {
  const manifest = validateManifest(JSON.parse(await readFile(new URL("manifest.json", canonical), "utf8")));
  const payloads = Object.create(null);
  for (const pin of manifest.artifacts) {
    const bytes = new Uint8Array(await readFile(new URL(pin.path, canonical)));
    payloads[pin.path] = { bytes, json: JSON.parse(new TextDecoder().decode(bytes)), mediaType: pin.mediaType };
  }
  const manifestDigest = `sha256:${"d".repeat(64)}`;
  const bundle = {
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
  const missions = await loadMissionCatalog(bundle);
  const load = (gameId, loader) => {
    const mission = missionByGameId(missions, gameId);
    return loader(bundle.payloads[mission.descriptorPath].json, finiteTableAuthority(mission));
  };
  return {
    bundle,
    missions,
    signalMission: missionByGameId(missions, "signal-triangulation"),
    signalJson: bundle.payloads["games/signal-triangulation.json"].json,
    relay: load("relay-repair", loadRelayRepairDescriptor),
    salvage: load("salvage-lock", loadSalvageLockDescriptor),
  };
}

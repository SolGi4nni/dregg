import { readFile } from "node:fs/promises";
import { finiteTableAuthority, loadMissionCatalog, missionByGameId } from "../src/mission-catalog.js";
import { validateManifest } from "../src/poag1.js";
import { loadArtificerLogicDescriptor } from "../src/artificer-runtime.js";
import { loadBlackBoxDescriptor } from "../src/blackbox-runtime.js";
import { loadDeckDescentDescriptor } from "../src/descent-runtime.js";
import { loadRelayRepairDescriptor } from "../src/relay-runtime.js";
import { loadSalvageLockDescriptor } from "../src/salvage-runtime.js";
import { loadVentCrawlDescriptor } from "../src/ventcrawl-runtime.js";

const canonical = new URL("../../poa/artifacts/poag1/", import.meta.url);

/**
 * The REAL Lean-emitted descriptors, loaded through the real loaders.
 *
 * Controller tests use these rather than a hand-written fixture on purpose: the
 * Salvage loader pins its emitted 632-state closure, and a fixture that could
 * satisfy that pin would be a second copy of the table maintained by hand — the
 * exact mirror this repo keeps paying for. Signature checking is out of scope
 * here (poag1.test covers it); the bytes are the committed ones.
 *
 * ⚑ THE PENDING FIXTURE FOLDED IN HERE, exactly as its own docblock said it
 * would. Until counter 10 three games were emitted but unsigned, so
 * `pending-descriptors.mjs` read them out of `poa/artifacts/poag1-pending/` and
 * assembled a SYNTHETIC catalog envelope — hand-written mission ids, disclosure,
 * reward class and content epoch — because no signed catalog named them. The
 * curator has now signed a counter enrolling all seven, so that envelope became a
 * hand-maintained second copy of something real, and the pending bytes predate
 * the draw repair (`symbol_draw`) so no loader accepts them any more.
 *
 * Every descriptor below is loaded against the authority the SIGNED catalog
 * declares. ⚠ `poa/artifacts/poag1-pending/` still exists on disk; it is dead
 * weight for the ceremony to remove, and nothing in this suite reads it.
 */
export async function canonicalDescriptors() {
  const manifest = validateManifest(JSON.parse(await readFile(new URL("manifest.json", canonical), "utf8")));
  const payloads = Object.create(null);
  for (const pin of manifest.artifacts) {
    const bytes = new Uint8Array(await readFile(new URL(pin.path, canonical)));
    payloads[pin.path] = { bytes, json: JSON.parse(new TextDecoder().decode(bytes)), mediaType: pin.mediaType };
  }
  const manifestDigest = `sha256:${"d".repeat(64)}`;
  const contentEpoch = {
    schema: "POA-CONTENT-EPOCH-SIGNATURE-V1",
    manifestDigest,
    activationDigest: `sha256:${"e".repeat(64)}`,
    contentEpoch: 1,
    counter: 1,
  };
  const bundle = { manifest, manifestDigest, contentEpoch, payloads };
  const missions = await loadMissionCatalog(bundle);
  const mission = (gameId) => missionByGameId(missions, gameId);
  const json = (gameId) => bundle.payloads[mission(gameId).descriptorPath].json;
  // Two envelope shapes, because two loaders want different things: the shared
  // finite-table engine takes `finiteTableAuthority(mission)`, Black Box and Vent
  // Crawl take the mission record itself. Neither is assembled by hand.
  const table = (gameId, loader) => loader(json(gameId), finiteTableAuthority(mission(gameId)));
  return {
    bundle,
    missions,
    signalMission: mission("signal-triangulation"),
    signalJson: json("signal-triangulation"),
    relay: table("relay-repair", loadRelayRepairDescriptor),
    salvage: table("salvage-lock", loadSalvageLockDescriptor),
    artificer: table("artificer-logic", loadArtificerLogicDescriptor),
    descent: table("deck-descent", loadDeckDescentDescriptor),
    blackbox: loadBlackBoxDescriptor(json("black-box-reconstruction"), mission("black-box-reconstruction")),
    ventcrawl: loadVentCrawlDescriptor(json("vent-crawl"), mission("vent-crawl"), contentEpoch),
  };
}

/**
 * The raw emitted bytes of one game, for tests that MUTATE a descriptor to
 * falsify a loader. It reads the signed bundle, so a mutation test and a load
 * test cannot drift onto two different copies of the same game.
 */
export async function canonicalPayload(gameId) {
  return JSON.parse(await readFile(new URL(`games/${gameId}.json`, canonical), "utf8"));
}

/** The signed catalog's own finite-table authority envelope for one game. */
export async function canonicalAuthority(gameId, missions) {
  return finiteTableAuthority(missionByGameId(missions ?? (await canonicalDescriptors()).missions, gameId));
}

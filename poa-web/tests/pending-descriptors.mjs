import { readFile } from "node:fs/promises";
import { loadArtificerLogicDescriptor } from "../src/artificer-runtime.js";
import { loadDeckDescentDescriptor } from "../src/descent-runtime.js";
import { loadVentCrawlDescriptor } from "../src/ventcrawl-runtime.js";

const pending = new URL("../../poa/artifacts/poag1-pending/", import.meta.url);

/**
 * The two games that are AUTHORED AND EMITTED but not yet in a curator-signed
 * bundle, loaded through their real loaders from their real Lean-emitted bytes.
 *
 * ⚠ WHY A SECOND FIXTURE MODULE EXISTS, AND WHEN IT SHOULD STOP.
 * `canonical-descriptors.mjs` reads `poa/artifacts/poag1/` — the bundle the
 * curator has signed, which at counter 8 carries four games. `Emit.lean` enrols
 * seven. The gap is one ceremony, not one design: `scripts/check-poag1-artifacts.sh
 * --update` re-emits every descriptor and DELETES the detached signature, and the
 * curator re-signs. On the far side of that, `poa/artifacts/poag1-pending/`
 * disappears and everything here moves to `canonicalDescriptors`.
 *
 * ⚠ The AUTHORITY is synthetic and the DESCRIPTOR BYTES ARE NOT. That is the whole
 * discipline of this file: the envelope a signed catalog would supply is assembled
 * here because no signed catalog names these missions yet, and every byte the
 * loaders actually parse comes from `ArtificerLogicEmitMain` / `VentCrawlEmitMain`.
 * A hand-written descriptor would be a second copy of the rules, which is the wound
 * the whole POAG1 split exists to close.
 *
 * The mission ids, disclosures and action limits below are the ones
 * `Emit.lean`'s `catalogJson` renders for these two missions. If they drift, these
 * loaders refuse — `loadFiniteTableDescriptor` compares the descriptor's
 * `action_limit` against the catalog's and `loadVentCrawlDescriptor` refuses any
 * catalog that does not declare it `oracle-only`.
 */

const DIGEST = (char) => `sha256:${char.repeat(64)}`;
const HEX32 = (char) => char.repeat(64);

/** The envelope `finiteTableAuthority(mission)` produces, for an unsigned mission. */
export function pendingAuthority(missionId) {
  return Object.freeze({
    missionId,
    manifestDigest: DIGEST("a"),
    activationDigest: DIGEST("b"),
    contentEpoch: 1,
    curatorCounter: 9,
    federationId: HEX32("c"),
    contentRoot: DIGEST("d"),
    contentSession: HEX32("e"),
    instanceDisclosure: "oracle-only",
    rewardClass: "non-economic-demo",
  });
}

/** The catalog mission record Vent Crawl's loader reads (it takes the mission, not the envelope). */
export function pendingMission(missionId, gameId) {
  return Object.freeze({
    ...pendingAuthority(missionId),
    gameId,
    epoch: 1,
    activation: Object.freeze({ state: "detached-signature-required", digestSource: "POA-CONTENT-EPOCH-SIGNATURE-V1" }),
  });
}

export const PENDING_CONTENT_EPOCH = Object.freeze({
  schema: "POA-CONTENT-EPOCH-SIGNATURE-V1",
  manifestDigest: DIGEST("a"),
  activationDigest: DIGEST("b"),
  contentEpoch: 1,
  counter: 9,
});

async function payload(path) {
  return JSON.parse(await readFile(new URL(path, pending), "utf8"));
}

/** The raw emitted bytes, for tests that MUTATE a descriptor to falsify a loader. */
export async function pendingPayload(gameId) {
  return payload(`games/${gameId}.json`);
}

/**
 * Deck Descent: mission 5, `descent-v1`, oracle-only, a parametric table.
 *
 * ⚑ Emitted by its OWN driver, `DeckDescentEmitMain`, into the same pending
 * directory — `Emit.lean` enrols it at mission 5 (`descentMission`) and
 * `EmitMain.lean` writes it into the bundle, so the ceremony's bytes and these
 * bytes are the same bytes.
 */
export async function pendingDescent() {
  return loadDeckDescentDescriptor(await payload("games/deck-descent.json"), pendingAuthority(5));
}

/** Artificer Logic: mission 6, `artificer-v1`, oracle-only, a parametric table. */
export async function pendingArtificer() {
  return loadArtificerLogicDescriptor(await payload("games/artificer-logic.json"), pendingAuthority(6));
}

/** Vent Crawl: mission 7, `push-your-luck-v1`, oracle-only, its own runtime. */
export async function pendingVentCrawl() {
  return loadVentCrawlDescriptor(
    await payload("games/vent-crawl.json"),
    pendingMission(7, "vent-crawl"),
    PENDING_CONTENT_EPOCH,
  );
}

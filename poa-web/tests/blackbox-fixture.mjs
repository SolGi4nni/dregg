/**
 * The Black Box descriptor, loaded from the bytes the Lean emitter actually
 * shipped in the curator-signed counter-8 bundle
 * (`poa/artifacts/poag1/games/black-box-reconstruction.json`, pinned by the
 * manifest and consumed by `validateBlackBoxDescriptor`).
 *
 * This USED to be a hand-built MIRROR: a second Lehmer enumeration of the 120
 * permutations of five fragments, kept in step with `orderRow` in `Emit.lean` by
 * eye. That was the exact duplication this repo keeps paying for, tolerated only
 * while the real descriptor was unemitted. The real bytes have now landed and
 * were byte-identical to the mirror, so the mirror is gone: every test mutates a
 * clone of the SHIPPED descriptor, which is the only thing a green Black Box test
 * should be allowed to mean.
 *
 * `blackBoxMission` and `blackBoxOpening` are NOT bundle artifacts. They are the
 * catalog-derived mission authority and a slot opening, synthesized here as
 * runtime inputs for the controller and runtime unit tests.
 */

import { readFileSync } from "node:fs";

const EMITTED_BLACK_BOX = JSON.parse(
  readFileSync(new URL("../../poa/artifacts/poag1/games/black-box-reconstruction.json", import.meta.url), "utf8"),
);

/** A fresh deep clone of the emitted descriptor, so hostile mutations are local. */
export function blackBoxFixture(overrides = {}) {
  return { ...structuredClone(EMITTED_BLACK_BOX), ...overrides };
}

export function blackBoxMission() {
  return {
    missionId: 4,
    gameId: "black-box-reconstruction",
    title: "Black Box Reconstruction",
    actionLimit: 11,
    instanceDisclosure: "oracle-only",
    federationId: "7".repeat(64),
    contentSession: "8".repeat(64),
    contentRoot: `sha256:${"9".repeat(64)}`,
    contentEpoch: 1,
    curatorCounter: 8,
    activationDigest: `sha256:${"e".repeat(64)}`,
    rewardClass: "non-economic-demo",
  };
}

export function blackBoxOpening(missionId = 4) {
  return {
    slot: 5,
    mission_id: missionId,
    commitment: "a".repeat(64),
    curator_pubkey: "b".repeat(64),
    signature: "c".repeat(128),
  };
}

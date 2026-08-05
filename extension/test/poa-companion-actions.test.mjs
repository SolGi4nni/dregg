import test from "node:test";
import assert from "node:assert/strict";

import {
  POA_RECEIPT_CORE_PROTOCOL,
  PoAEngine,
  parsePoAReceiptCoreObservation,
  poaManifestSigningBytes,
  validatePoAManifest,
} from "./.build/poa.mjs";

const NOW = 1_800_000_000;
const VIDEO = "AbCdEfGhI01";
const SIGNER = "11".repeat(32);
const SIGNATURE = "22".repeat(64);
const RECEIPT = "33".repeat(32);
const MANIFEST_DIGEST = "44".repeat(32);
const FEDERATION = "55".repeat(32);
const TURN = "66".repeat(32);
const BLOCK = "77".repeat(32);
const AGENT = "88".repeat(32);

function manifestV2(overrides = {}) {
  const base = {
    schema: "poa-companion/v2",
    contentEpoch: 2,
    counter: 7,
    context: { platform: "youtube", videoId: VIDEO, channelId: "UC_PathOfAngels" },
    experience: {
      id: "episode-2-debrief",
      title: "Crown wreckage debrief",
      episode: "Episode 2",
      dispatch: "The Crown returned three public bearings.",
      betaUrl: "https://beta.pathofangels.network/?episode=2",
      actions: {
        mission: { label: "Enter the deck survey", betaUrl: "https://beta.pathofangels.network/?view=missions&episode=2" },
        evidence: { label: "Inspect the Crown bearings", betaUrl: "https://beta.pathofangels.network/?view=records&episode=2" },
        debrief: { label: "Read the crew debrief", betaUrl: "https://beta.pathofangels.network/?view=watch&episode=2" },
      },
      fieldRecord: { finalizedReceiptCoreId: RECEIPT, federationId: FEDERATION, turnHash: TURN },
    },
    issuedAt: NOW - 60,
    expiresAt: NOW + 3600,
  };
  return {
    ...base,
    ...overrides,
    context: { ...base.context, ...(overrides.context || {}) },
    experience: { ...base.experience, ...(overrides.experience || {}) },
  };
}

function engineFor(envelope) {
  return new PoAEngine({
    manifestSource: "persisted_legacy_migration",
    resolveSignedManifest: async () => envelope,
    isVideoAllowlisted: async () => false,
    trustedCuratorKeys: async () => new Set([SIGNER]),
    acceptManifestVersion: async () => true,
    verifyEd25519: async () => true,
    nowSeconds: () => NOW,
  });
}

test("v2 signs episode actions and the exact finalized-receipt coordinate", () => {
  const parsed = validatePoAManifest(manifestV2(), NOW);
  assert.ok(parsed);
  const signed = new TextDecoder().decode(poaManifestSigningBytes(parsed));
  assert.match(signed, /^poa-companion\/v2\n/);
  assert.match(signed, /"actions":\{"mission":\{"label":"Enter the deck survey"/);
  assert.match(signed, /"evidence":\{"label":"Inspect the Crown bearings"/);
  assert.match(signed, /"debrief":\{"label":"Read the crew debrief"/);
  assert.match(signed, new RegExp(`"fieldRecord":\\{"finalizedReceiptCoreId":"${RECEIPT}","federationId":"${FEDERATION}","turnHash":"${TURN}"\\}`));
});

test("v2 routing is exact, episode-bound, beta-origin-only, and credential-free", () => {
  const noEpisode = manifestV2({ experience: { episode: undefined } });
  assert.equal(validatePoAManifest(noEpisode, NOW), null, "actions cannot float free of an episode");

  const v1Smuggle = manifestV2({ schema: "poa-companion/v1" });
  assert.equal(validatePoAManifest(v1Smuggle, NOW), null, "new route fields cannot ride unsigned under v1 projection");

  const credentials = manifestV2({ experience: {
    actions: { evidence: { label: "unsafe", betaUrl: "https://eden:secret@beta.pathofangels.network/records" } },
  } });
  assert.equal(validatePoAManifest(credentials, NOW), null, "Basic Auth credentials never enter signed content");
  assert.equal(validatePoAManifest(manifestV2({ experience: {
    betaUrl: "https://eden:secret@beta.pathofangels.network/",
  } }), NOW), null, "the general beta route cannot smuggle credentials either");

  const foreign = manifestV2({ experience: {
    actions: { evidence: { label: "unsafe", betaUrl: "https://evil.example/records" } },
  } });
  assert.equal(validatePoAManifest(foreign, NOW), null);

  const unknownAction = manifestV2({ experience: {
    actions: { lore: { label: "unsigned semantics", betaUrl: "https://beta.pathofangels.network/" } },
  } });
  assert.equal(validatePoAManifest(unknownAction, NOW), null);

  const unknownTop = { ...manifestV2(), hostDomTimestamp: 231 };
  assert.equal(validatePoAManifest(unknownTop, NOW), null, "v2 has an exact interpreted envelope");
  assert.equal(validatePoAManifest(manifestV2({ experience: {
    fieldRecord: { finalizedReceiptCoreId: "0".repeat(64), federationId: FEDERATION, turnHash: TURN },
  } }), NOW), null, "FRC1 reserves the zero core id and the manifest cannot name it");
});

test("only a verified manifest can deliver actions and a field-record pointer to the view", async () => {
  const value = manifestV2();
  const accepted = await engineFor({ manifest: value, signer: SIGNER, signature: SIGNATURE }).handle({
    op: "openContext",
    context: { href: `https://www.youtube.com/watch?v=${VIDEO}` },
  });
  assert.equal(accepted.ok, true);
  assert.equal(accepted.verified, true);
  assert.equal(accepted.model.actions.evidence.label, "Inspect the Crown bearings");
  assert.equal(accepted.model.fieldRecord.finalizedReceiptCoreId, RECEIPT);

  const wrongContext = await engineFor({ manifest: value, signer: SIGNER, signature: SIGNATURE }).handle({
    op: "openContext",
    context: { href: "https://www.youtube.com/watch?v=ZyXwVuTsR02" },
  });
  assert.equal(wrongContext.ok, false);

  const xValue = manifestV2();
  xValue.context = { platform: "x", postId: "1891234567890123456" };
  xValue.experience.id = "x-episode-2-debrief";
  const xAccepted = await engineFor({ manifest: xValue, signer: SIGNER, signature: SIGNATURE }).handle({
    op: "openContext",
    context: { href: "https://x.com/sentyr/status/1891234567890123456" },
  });
  assert.equal(xAccepted.ok, true);
  assert.equal(xAccepted.model.platform, "x");
  assert.equal(xAccepted.model.actions.debrief.label, "Read the crew debrief");
});

function canonicalFrc1({ turnHash = TURN, federationId = FEDERATION } = {}) {
  const bytes = new Uint8Array(592);
  const view = new DataView(bytes.buffer);
  const text = new TextEncoder();
  const putHex = (offset, hex) => {
    for (let index = 0; index < hex.length / 2; index += 1) {
      bytes[offset + index] = Number.parseInt(hex.slice(index * 2, index * 2 + 2), 16);
    }
  };
  bytes.set(text.encode("FRC1"), 0);
  view.setUint16(4, 1, true);
  bytes.set(text.encode("FEC1"), 8);
  view.setUint16(12, 1, true);
  putHex(16, BLOCK);
  view.setBigUint64(48, 19n, true);
  view.setBigInt64(56, 1_700_000_019n, true);
  view.setBigUint64(64, 3n, true);
  putHex(72, turnHash);
  // Five receipt commitment hashes occupy 72..232; the remaining four stay zero.
  // Cost/count, genesis predecessor, and disclosure commitments are canonically zero.
  putHex(321, AGENT);
  putHex(353, federationId);
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join("");
}

function frc1Response(overrides = {}) {
  return {
    protocol: POA_RECEIPT_CORE_PROTOCOL,
    receipt_index: 12,
    core_id: RECEIPT,
    canonical_core: canonicalFrc1(),
    block_id: BLOCK,
    tau_round: 19,
    consensus_unix_seconds: 1_700_000_019,
    committee_epoch: 3,
    predecessor: { kind: "genesis" },
    turn_hash: TURN,
    agent: AGENT,
    federation_id: FEDERATION,
    ...overrides,
  };
}

test("FRC1 parser yields only a self-consistent node observation, never verified finality", () => {
  const binding = {
    platform: "youtube",
    contextId: VIDEO,
    experienceId: "episode-2-debrief",
    manifestDigest: MANIFEST_DIGEST,
    finalizedReceiptCoreId: RECEIPT,
    federationId: FEDERATION,
    turnHash: TURN,
  };
  const value = frc1Response();
  const accepted = parsePoAReceiptCoreObservation(value, binding);
  assert.equal(accepted.grade, "node_transport_observation");
  assert.equal(accepted.quorumFinality, "not_verified_by_extension");
  assert.equal(accepted.coreIdHash, "not_verified_by_extension");
  assert.equal(accepted.canonicalProjection, "self_consistent_frc1");
  assert.equal(accepted.tauRound, 19);
  assert.equal(accepted.finalizedReceiptCoreId, RECEIPT);
  assert.equal(Object.isFrozen(accepted), true);
  assert.equal("finality" in accepted, false);

  assert.equal(parsePoAReceiptCoreObservation({ ...value, finality: "finalized" }, binding), null,
    "an operator-supplied finality label is not part of FRC1 and cannot be laundered");
  assert.equal(parsePoAReceiptCoreObservation({ ...value, core_id: "99".repeat(32) }, binding), null);
  assert.equal(parsePoAReceiptCoreObservation({ ...value, federation_id: "99".repeat(32) }, binding), null);
  assert.equal(parsePoAReceiptCoreObservation({ ...value, turn_hash: "99".repeat(32) }, binding), null);
  assert.equal(parsePoAReceiptCoreObservation({ ...value, canonical_core: canonicalFrc1({ turnHash: "99".repeat(32) }) }, binding), null,
    "projected JSON must agree with the canonical FRC1 bytes");
  assert.equal(parsePoAReceiptCoreObservation({ ...value, host_dom_claim: true }, binding), null);
});

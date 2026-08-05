import test from "node:test";
import assert from "node:assert/strict";

import {
  POA_BETA_URL,
  PoAEngine,
  poaManifestSigningBytes,
  validatePoAManifest,
} from "./.build/poa.mjs";

const NOW = 1_800_000_000;
// Test-only placeholders. The production companion tree stays empty until the
// real episode ids are supplied by the author.
const EPISODE_ONE = "AbCdEfGhI01";
const EPISODE_TWO = "ZyXwVuTsR02";
const SIGNER = "11".repeat(32);
const OTHER_SIGNER = "22".repeat(32);
// ⚠ RE-POINTED 2026-08-05 with the Rust mirror in poa-curator/src/companion.rs. These four
// are the SHARED PAYLOAD of a two-implementation gate: neither side derives them here, and
// what the two tests actually compare is that the JS and Rust canonical serializers produce
// identical bytes from identical records. Moving them in ONE file only would turn that into
// two serializers agreeing about nothing.
// ⚑ On the RUST side `contentPackDigest` and the catalog `bytes`/`sha256` are DERIVED from
// poa/artifacts/poag1/manifest.json, so a POAG1 re-emit turns that test red and forces this
// file to follow. Here they are typed, so this file cannot notice on its own.
const FEDERATION = "70b7fa4cfbc3921bef2e1ddb1a42869c8dcef27539179c9cbdf6a6e6b1d07c1b";
const DEPLOYMENT = "4db835cc36cd0d3b722e742334dc1dde9557601fe1334c7499ab023de4d6d45d";
const PACK = "sha256:3cff74449b87d468aec9bd95c04e7fc3bb6d193e23f5b00076691c23abdcd1df";

function manifest(videoId = EPISODE_ONE, overrides = {}) {
  const base = {
    schema: "poa-companion/v3",
    contentEpoch: 1,
    contentCounter: 4,
    sequence: 7,
    poaOrigin: "https://beta.pathofangels.network",
    federationId: FEDERATION,
    deploymentId: DEPLOYMENT,
    contentPackDigest: PACK,
    context: { platform: "youtube", videoId, channelId: "UC_PathOfAngels" },
    experience: {
      id: `episode-${videoId === EPISODE_ONE ? "1" : "2"}`,
      title: "Path of Angels field dispatch",
      episode: videoId === EPISODE_ONE ? "Episode 1" : "Episode 2",
      dispatch: "A signed field route is available.",
      betaUrl: `${POA_BETA_URL}?episode=${videoId === EPISODE_ONE ? "1" : "2"}`,
      game: { kind: "descent", src: "dregg://descent/b3_de5ce0" },
      contentAssets: [{
        path: "catalog.json",
        url: `${POA_BETA_URL}artifacts/poag1/catalog.json`,
        mediaType: "application/json",
        bytes: 5508,
        sha256: "2e85db1fbe2b670d2bbc210790e0b04be521a6cddfa65b9724c49aa2558b39f8",
      }],
      actions: {
        mission: { label: "Open field terminal", betaUrl: `${POA_BETA_URL}?station=field` },
      },
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

function engineFor(envelope, expectedManifest = envelope?.manifest, trusted = new Set([SIGNER])) {
  const expected = expectedManifest ? poaManifestSigningBytes(expectedManifest) : null;
  return new PoAEngine({
    manifestSource: "public_network_v3",
    resolveSignedManifest: async () => envelope,
    isVideoAllowlisted: async () => false,
    trustedCuratorKeys: async () => trusted,
    acceptManifestVersion: async () => true,
    verifyEd25519: async (_key, bytes) => expected !== null && Buffer.from(bytes).equals(Buffer.from(expected)),
    nowSeconds: () => NOW,
  });
}

async function open(engine, videoId = EPISODE_ONE) {
  return engine.handle({
    op: "openContext",
    context: { href: `https://www.youtube.com/watch?v=${videoId}` },
  });
}

test("v3 binds an exact episode to PoA origin, deployment, content pack, assets and actions", async () => {
  for (const videoId of [EPISODE_ONE, EPISODE_TWO]) {
    const value = manifest(videoId);
    assert.ok(validatePoAManifest(value, NOW));
    const response = await open(engineFor({ manifest: value, signer: SIGNER, signature: "33".repeat(64) }), videoId);
    assert.equal(response.ok, true);
    assert.equal(response.model.counter, 7);
    assert.deepEqual(response.model.contentScope, {
      poaOrigin: "https://beta.pathofangels.network",
      federationId: FEDERATION,
      deploymentId: DEPLOYMENT,
      contentCounter: 4,
      contentPackDigest: PACK,
      contentAssets: value.experience.contentAssets,
    });
    assert.equal(response.model.actions.mission.label, "Open field terminal");
  }
});

test("v3 signing bytes are byte-identical to the curator's canonical projection", () => {
  const bytes = Buffer.from(poaManifestSigningBytes(manifest())).toString("utf8");
  assert.equal(bytes, [
    "poa-companion/v3\n",
    '{"schema":"poa-companion/v3","contentEpoch":1,"contentCounter":4,"sequence":7,',
    '"poaOrigin":"https://beta.pathofangels.network",',
    `"federationId":"${FEDERATION}",`,
    `"deploymentId":"${DEPLOYMENT}",`,
    `"contentPackDigest":"${PACK}",`,
    `"context":{"platform":"youtube","videoId":"${EPISODE_ONE}","channelId":"UC_PathOfAngels"},`,
    '"experience":{"id":"episode-1","title":"Path of Angels field dispatch","episode":"Episode 1",',
    '"dispatch":"A signed field route is available.","betaUrl":"https://beta.pathofangels.network/?episode=1",',
    '"game":{"kind":"descent","src":"dregg://descent/b3_de5ce0"},',
    '"contentAssets":[{"path":"catalog.json","url":"https://beta.pathofangels.network/artifacts/poag1/catalog.json",',
    '"mediaType":"application/json","bytes":5508,"sha256":"2e85db1fbe2b670d2bbc210790e0b04be521a6cddfa65b9724c49aa2558b39f8"}],',
    '"actions":{"mission":{"label":"Open field terminal","betaUrl":"https://beta.pathofangels.network/?station=field"}}},',
    '"issuedAt":1799999940,"expiresAt":1800003600}',
  ].join(""));
});

test("v3 refuses malformed, cross-origin, substituted deployment/pack/assets and expiry", () => {
  const cases = [
    manifest(EPISODE_ONE, { poaOrigin: "https://evil.example" }),
    manifest(EPISODE_ONE, { federationId: "0".repeat(64) }),
    manifest(EPISODE_ONE, { contentPackDigest: `sha256:${"AA".repeat(32)}` }),
    manifest(EPISODE_ONE, { expiresAt: NOW }),
    manifest(EPISODE_ONE, { issuedAt: NOW, expiresAt: NOW + 7 * 86400 + 1 }),
    manifest(EPISODE_ONE, { experience: { title: "control\u0000byte" } }),
    manifest(EPISODE_ONE, { experience: { dispatch: "delete\u007fbyte" } }),
    manifest(EPISODE_ONE, { experience: { contentAssets: [] } }),
    manifest(EPISODE_ONE, { experience: { contentAssets: [{
      ...manifest().experience.contentAssets[0],
      url: "https://evil.example/catalog.json",
    }] } }),
    manifest(EPISODE_ONE, { experience: { contentAssets: [{
      ...manifest().experience.contentAssets[0],
      sha256: "ff".repeat(32),
    }, manifest().experience.contentAssets[0]] } }),
    manifest(EPISODE_ONE, { experience: { actions: {
      mission: { label: "cross origin", betaUrl: "https://evil.example/mission" },
    } } }),
  ];
  for (const value of cases) assert.equal(validatePoAManifest(value, NOW), null);
});

test("signature covers every v3 scope/content/action byte and wrong signer is refused", async () => {
  const original = manifest();
  const envelope = { manifest: original, signer: SIGNER, signature: "33".repeat(64) };
  assert.equal((await open(engineFor(envelope))).ok, true);

  for (const changed of [
    manifest(EPISODE_TWO),
    manifest(EPISODE_ONE, { deploymentId: "aa".repeat(32) }),
    manifest(EPISODE_ONE, { contentPackDigest: `sha256:${"bb".repeat(32)}` }),
    manifest(EPISODE_ONE, { experience: { actions: {
      mission: { label: "substituted", betaUrl: `${POA_BETA_URL}?station=field` },
    } } }),
    manifest(EPISODE_ONE, { experience: { contentAssets: [{
      ...manifest().experience.contentAssets[0], sha256: "ff".repeat(32),
    }] } }),
  ]) {
    const changedEnvelope = { manifest: changed, signer: SIGNER, signature: envelope.signature };
    assert.equal((await open(engineFor(changedEnvelope, original), changed.context.videoId)).ok, false);
  }

  assert.equal((await open(engineFor(
    { manifest: original, signer: OTHER_SIGNER, signature: envelope.signature },
    original,
  ))).ok, false, "a non-pinned signer is rejected before signature verification");
});

test("unknown exact context returns no route and receives no unsigned X fallback", async () => {
  const known = manifest(EPISODE_ONE);
  const engine = engineFor({ manifest: known, signer: SIGNER, signature: "33".repeat(64) });
  assert.equal((await open(engine, EPISODE_TWO)).ok, false);
  const x = await engine.handle({
    op: "openContext",
    context: { href: "https://x.com/sentyr/status/1891234567890123456" },
  });
  assert.equal(x.ok, false);
});

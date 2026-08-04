import test from 'node:test';
import assert from 'node:assert/strict';

import {
  POA_BETA_URL,
  PoAEngine,
  parsePoAYouTubeUrl,
  poaManifestSigningBytes,
  validatePoAManifest,
} from './.build/poa.mjs';

const NOW = 1_800_000_000;
const VIDEO = 'AbCdEfGhI01';
const OTHER = 'ZyXwVuTsR02';
const SIGNER = '11'.repeat(32);
const SIGNATURE = '22'.repeat(64);

function manifest(overrides = {}) {
  const base = {
    schema: 'poa-companion/v1',
    context: { platform: 'youtube', videoId: VIDEO, channelId: 'UC_PathOfAngels' },
    experience: {
      id: 'episode-1',
      title: 'Path of Angels field dispatch',
      episode: 'Episode 1',
      dispatch: 'Survey ping returned.',
      betaUrl: `${POA_BETA_URL}?episode=1`,
      game: { kind: 'descent', src: 'dregg://descent/b3_de5ce0' },
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

function engineFor(envelope, allowlisted = new Set()) {
  return new PoAEngine({
    resolveSignedManifest: async () => envelope,
    isVideoAllowlisted: async (videoId) => allowlisted.has(videoId),
    trustedCuratorKeys: async () => new Set([SIGNER]),
    verifyEd25519: async () => true,
    nowSeconds: () => NOW,
  });
}

test('YouTube recognition accepts exact watch/shorts/live routes only', () => {
  assert.equal(parsePoAYouTubeUrl(`https://www.youtube.com/watch?v=${VIDEO}`).videoId, VIDEO);
  assert.equal(parsePoAYouTubeUrl(`https://m.youtube.com/shorts/${VIDEO}`).videoId, VIDEO);
  assert.equal(parsePoAYouTubeUrl(`https://youtube.com/live/${VIDEO}?feature=share`).videoId, VIDEO);
  assert.equal(parsePoAYouTubeUrl(`http://www.youtube.com/watch?v=${VIDEO}`), null, 'HTTP refused');
  assert.equal(parsePoAYouTubeUrl(`https://evil.example/watch?v=${VIDEO}`), null, 'lookalike host refused');
  assert.equal(parsePoAYouTubeUrl('https://www.youtube.com/'), null, 'channel/home page is not a video');
  assert.equal(parsePoAYouTubeUrl('https://www.youtube.com/watch?v=short'), null, 'malformed id refused');
});

test('canonical signing bytes are stable and omit no interpreted optional field', () => {
  const bytes = new TextDecoder().decode(poaManifestSigningBytes(manifest()));
  assert.match(bytes, /^poa-companion\/v1\n\{/);
  assert.match(bytes, /"videoId":"AbCdEfGhI01"/);
  assert.match(bytes, /"game":\{"kind":"descent","src":"dregg:\/\/descent\/b3_de5ce0"\}/);
  assert.match(bytes, /"expiresAt":1800003600\}$/);
});

test('manifest validator rejects stale, overlong, foreign-beta, and unknown game routes', () => {
  assert.ok(validatePoAManifest(manifest(), NOW));
  assert.equal(validatePoAManifest(manifest({ expiresAt: NOW }), NOW), null);
  assert.equal(validatePoAManifest(manifest({ issuedAt: NOW - 1, expiresAt: NOW + 367 * 86400 }), NOW), null);
  assert.equal(validatePoAManifest(manifest({ experience: { betaUrl: 'https://evil.example/' } }), NOW), null);
  assert.equal(validatePoAManifest(manifest({ experience: { game: { kind: 'poll', src: 'dregg://poll/b3_a1a1a1' } } }), NOW), null);
  assert.equal(validatePoAManifest(manifest({ experience: { game: { kind: 'descent', src: 'dregg://descent/notahash' } } }), NOW), null);
});

test('signed manifest is bound to the URL-derived video id', async () => {
  const envelope = { manifest: manifest(), signer: SIGNER, signature: SIGNATURE };
  const accepted = await engineFor(envelope).handle({
    op: 'openContext',
    context: { href: `https://www.youtube.com/watch?v=${VIDEO}` },
  });
  assert.equal(accepted.ok, true);
  assert.equal(accepted.verified, true);
  assert.equal(accepted.tier, 'extension');
  assert.equal(accepted.model.trust, 'signed_manifest');
  assert.equal(accepted.model.game.kind, 'descent');

  const wrongVideo = await engineFor(envelope).handle({
    op: 'openContext',
    context: { href: `https://www.youtube.com/watch?v=${OTHER}` },
  });
  assert.equal(wrongVideo.ok, false, 'a valid signature for another episode is refused');
});

test('exact local video allowlist produces a game-free shell', async () => {
  const response = await engineFor(null, new Set([VIDEO])).handle({
    op: 'openContext',
    context: {
      href: `https://www.youtube.com/watch?v=${VIDEO}`,
      channelHint: 'UC_PageControlledHint',
    },
  });
  assert.equal(response.ok, true);
  assert.equal(response.recognized, true);
  assert.equal(response.verified, false, 'allowlisting recognizes; it does not verify');
  assert.equal(response.tier, 'none');
  assert.equal(response.model.trust, 'local_allowlist');
  assert.equal(response.model.game, undefined, 'allowlist cannot introduce a game route');

  const channelOnly = await engineFor(null, new Set(['UC_PageControlledHint'])).handle({
    op: 'openContext',
    context: {
      href: `https://www.youtube.com/watch?v=${VIDEO}`,
      channelHint: 'UC_PageControlledHint',
    },
  });
  assert.equal(channelOnly.ok, false, 'page-scraped channel hints never establish local recognition');
});

test('node failure can only fall back to an exact local, game-free recognition', async () => {
  const offline = (allowlisted) => new PoAEngine({
    resolveSignedManifest: async () => { throw new Error('offline'); },
    isVideoAllowlisted: async (videoId) => allowlisted && videoId === VIDEO,
    trustedCuratorKeys: async () => new Set([SIGNER]),
    nowSeconds: () => NOW,
  });
  const context = { op: 'openContext', context: { href: `https://www.youtube.com/watch?v=${VIDEO}` } };
  const local = await offline(true).handle(context);
  assert.equal(local.ok, true);
  assert.equal(local.recognized, true);
  assert.equal(local.verified, false);
  assert.equal(local.model.trust, 'local_allowlist');
  assert.equal(local.model.game, undefined);
  assert.match(local.model.betaUrl, /^https:\/\/beta\.pathofangels\.network\//);

  const unknown = await offline(false).handle(context);
  assert.equal(unknown.ok, false, 'offline + no exact allowlist refuses instead of inventing a shell');
});

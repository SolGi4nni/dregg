import test from 'node:test';
import assert from 'node:assert/strict';

import {
  POA_BETA_URL,
  PoAEngine,
  acceptStoredPoAManifestVersion,
  createStoredPoAEngine,
  parsePoAContextUrl,
  parsePoAYouTubeUrl,
  poaManifestSigningBytes,
  validatePoAManifest,
} from './.build/poa.mjs';

const NOW = 1_800_000_000;
const VIDEO = 'AbCdEfGhI01';
const OTHER = 'ZyXwVuTsR02';
const X_POST = '1891234567890123456';
const OTHER_X_POST = '1891234567890123457';
const SIGNER = '11'.repeat(32);
const OTHER_SIGNER = '33'.repeat(32);
const SIGNATURE = '22'.repeat(64);

function memoryStorage(initial = {}) {
  const data = structuredClone(initial);
  return {
    data,
    async get(keys) {
      const names = Array.isArray(keys) ? keys : [keys];
      return Object.fromEntries(names.filter((key) => key in data).map((key) => [key, structuredClone(data[key])]));
    },
    async set(values) {
      Object.assign(data, structuredClone(values));
    },
  };
}

function manifest(overrides = {}) {
  const base = {
    schema: 'poa-companion/v1',
    contentEpoch: 1,
    counter: 1,
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

function xManifest(postId = X_POST, overrides = {}) {
  const value = manifest({
    ...overrides,
    experience: {
      id: 'x-field-dispatch',
      title: 'Path of Angels X field dispatch',
      betaUrl: `${POA_BETA_URL}?x=${postId}`,
      ...(overrides.experience || {}),
    },
  });
  value.context = { platform: 'x', postId, ...(overrides.context || {}) };
  return value;
}

function engineFor(envelope, allowlisted = new Set()) {
  return new PoAEngine({
    manifestSource: 'persisted_legacy_migration',
    resolveSignedManifest: async () => envelope,
    isVideoAllowlisted: async (videoId) => allowlisted.has(videoId),
    trustedCuratorKeys: async () => new Set([SIGNER]),
    acceptManifestVersion: async () => true,
    verifyEd25519: async () => true,
    nowSeconds: () => NOW,
  });
}

function bytesToHex(bytes) {
  return Array.from(new Uint8Array(bytes), (byte) => byte.toString(16).padStart(2, '0')).join('');
}

async function cryptographicallySignedEnvelope(value, pair, signer) {
  const signature = await crypto.subtle.sign(
    { name: 'Ed25519' },
    pair.privateKey,
    poaManifestSigningBytes(value),
  );
  return { manifest: value, signer, signature: bytesToHex(signature) };
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

test('X recognition accepts exact browser-authenticated status routes only', () => {
  assert.deepEqual(parsePoAContextUrl(`https://x.com/sentyr/status/${X_POST}`), { platform: 'x', postId: X_POST });
  assert.deepEqual(parsePoAContextUrl(`https://twitter.com/sentyr/status/${X_POST}/photo/1`), { platform: 'x', postId: X_POST });
  assert.equal(parsePoAContextUrl(`https://x.com/home?status=${X_POST}`), null, 'feed DOM/query hints are not authoritative');
  assert.equal(parsePoAContextUrl(`https://x.com/sentyr/status/0`), null, 'zero is not a snowflake');
  assert.equal(parsePoAContextUrl(`http://x.com/sentyr/status/${X_POST}`), null, 'HTTP refused');
  assert.equal(parsePoAContextUrl(`https://x.com/sentyr/status/${X_POST}999`), null, 'overlong post id refused');
});

test('canonical signing bytes are stable and omit no interpreted optional field', () => {
  const bytes = new TextDecoder().decode(poaManifestSigningBytes(manifest()));
  assert.match(bytes, /^poa-companion\/v1\n\{/);
  assert.match(bytes, /"contentEpoch":1,"counter":1/);
  assert.match(bytes, /"videoId":"AbCdEfGhI01"/);
  assert.match(bytes, /"game":\{"kind":"descent","src":"dregg:\/\/descent\/b3_de5ce0"\}/);
  assert.match(bytes, /"expiresAt":1800003600\}$/);

  const xBytes = new TextDecoder().decode(poaManifestSigningBytes(xManifest()));
  assert.match(xBytes, new RegExp(`"context":\\{"platform":"x","postId":"${X_POST}"\\}`));
  assert.doesNotMatch(xBytes, /videoId|channelId/, 'X signs only its discriminated stable identity');
});

test('manifest validator rejects stale, overlong, foreign-beta, and unknown game routes', () => {
  assert.ok(validatePoAManifest(manifest(), NOW));
  assert.equal(validatePoAManifest(manifest({ expiresAt: NOW }), NOW), null);
  assert.ok(validatePoAManifest(manifest({ issuedAt: NOW, expiresAt: NOW + 7 * 86400 }), NOW), 'seven-day TTL accepted');
  assert.equal(validatePoAManifest(manifest({ issuedAt: NOW, expiresAt: NOW + 7 * 86400 + 1 }), NOW), null);
  assert.equal(validatePoAManifest(manifest({ contentEpoch: -1 }), NOW), null);
  assert.equal(validatePoAManifest(manifest({ counter: 1.5 }), NOW), null);
  const missingEpoch = manifest(); delete missingEpoch.contentEpoch;
  assert.equal(validatePoAManifest(missingEpoch, NOW), null);
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
  assert.equal(accepted.model.contentEpoch, 1);
  assert.equal(accepted.model.counter, 1);
  assert.match(accepted.model.manifestDigest, /^[0-9a-f]{64}$/);
  assert.equal(accepted.model.issuedAt, NOW - 60);
  assert.equal(accepted.model.expiresAt, NOW + 3600);
  assert.equal(accepted.model.game.kind, 'descent');

  const wrongVideo = await engineFor(envelope).handle({
    op: 'openContext',
    context: { href: `https://www.youtube.com/watch?v=${OTHER}` },
  });
  assert.equal(wrongVideo.ok, false, 'a valid signature for another episode is refused');
});

test('signed X manifest is bound to platform plus stable post id', async () => {
  const envelope = { manifest: xManifest(), signer: SIGNER, signature: SIGNATURE };
  const accepted = await engineFor(envelope).handle({
    op: 'openContext',
    context: { href: `https://x.com/sentyr/status/${X_POST}` },
  });
  assert.equal(accepted.ok, true);
  assert.equal(accepted.verified, true);
  assert.equal(accepted.model.platform, 'x');
  assert.equal(accepted.model.contextId, X_POST);
  assert.equal(accepted.model.postId, X_POST);
  assert.equal(accepted.model.videoId, undefined);

  const wrongPost = await engineFor(envelope).handle({
    op: 'openContext',
    context: { href: `https://x.com/sentyr/status/${OTHER_X_POST}` },
  });
  assert.equal(wrongPost.ok, false, 'signature for another X post is refused');

  const wrongPlatform = await engineFor({ manifest: manifest(), signer: SIGNER, signature: SIGNATURE }).handle({
    op: 'openContext',
    context: { href: `https://x.com/sentyr/status/${X_POST}` },
  });
  assert.equal(wrongPlatform.ok, false, 'same-looking id on another platform cannot establish context');
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
    manifestSource: 'public_network_v3',
    resolveSignedManifest: async () => { throw new Error('offline'); },
    isVideoAllowlisted: async (videoId) => allowlisted && videoId === VIDEO,
    trustedCuratorKeys: async () => new Set([SIGNER]),
    acceptManifestVersion: async () => true,
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

test('persisted epoch+counter rejects stale and equal-conflicting signed routes', async () => {
  const storage = memoryStorage();
  let envelope = null;
  const makeEngine = () => new PoAEngine({
    manifestSource: 'persisted_legacy_migration',
    resolveSignedManifest: async () => envelope,
    isVideoAllowlisted: async () => false,
    trustedCuratorKeys: async () => new Set([SIGNER, OTHER_SIGNER]),
    verifyEd25519: async () => true,
    acceptManifestVersion: (version) => acceptStoredPoAManifestVersion(storage, version),
    nowSeconds: () => NOW,
  });
  const open = (engine) => engine.handle({
    op: 'openContext',
    context: { href: `https://www.youtube.com/watch?v=${VIDEO}` },
  });
  const serve = (m, signer = SIGNER) => {
    envelope = { manifest: m, signer, signature: SIGNATURE };
  };

  const engine = makeEngine();
  const revision10 = manifest({ contentEpoch: 4, counter: 10 });
  serve(revision10);
  assert.equal((await open(engine)).ok, true, 'first signed revision accepted');
  assert.equal((await open(engine)).ok, true, 'byte-identical replay is idempotent');

  serve(manifest({ contentEpoch: 4, counter: 9, experience: { game: { kind: 'descent', src: 'dregg://descent/b3_bad009' } } }));
  assert.equal((await open(engine)).ok, false, 'lower counter rejected');

  serve(manifest({ contentEpoch: 4, counter: 10, experience: { game: { kind: 'descent', src: 'dregg://descent/b3_c0ffee' } } }));
  assert.equal((await open(engine)).ok, false, 'equal counter with a different canonical digest rejected');

  const revision11 = manifest({ contentEpoch: 4, counter: 11, experience: { game: { kind: 'descent', src: 'dregg://descent/b3_c0ffee' } } });
  serve(revision11);
  assert.equal((await open(engine)).ok, true, 'higher counter accepted');

  // The persisted high-water mark survives a new background engine instance.
  serve(revision10);
  assert.equal((await open(makeEngine())).ok, false, 'old route rejected after worker/engine restart');

  serve(manifest({ contentEpoch: 5, counter: 0, experience: { game: { kind: 'descent', src: 'dregg://descent/b3_e50000' } } }));
  assert.equal((await open(makeEngine())).ok, true, 'higher content epoch may restart the counter');
  serve(manifest({ contentEpoch: 5, counter: 1, experience: { game: undefined } }));
  const revoked = await open(makeEngine());
  assert.equal(revoked.ok, true, 'higher signed revision can revoke the game route');
  assert.equal(revoked.model.game, undefined);
  serve(manifest({ contentEpoch: 5, counter: 0, experience: { game: { kind: 'descent', src: 'dregg://descent/b3_e50000' } } }));
  assert.equal((await open(makeEngine())).ok, false, 'revoked route cannot replay after the route-free revision');
  serve(manifest({ contentEpoch: 4, counter: 999, experience: { game: { kind: 'descent', src: 'dregg://descent/b3_bad999' } } }));
  assert.equal((await open(makeEngine())).ok, false, 'older content epoch cannot win with a larger counter');

  // High-water marks are scoped to exact video+curator, so curator rotation is
  // explicit rather than silently inheriting another key's counter.
  serve(manifest({ contentEpoch: 1, counter: 0 }), OTHER_SIGNER);
  assert.equal((await open(makeEngine())).ok, true, 'separately trusted curator has an independent high-water mark');
});

test('rollback ratchets namespace X and YouTube identities independently', async () => {
  const storage = memoryStorage();
  const ambiguousId = '12345678901';
  const base = {
    signer: SIGNER,
    contextId: ambiguousId,
    contentEpoch: 1,
    counter: 1,
  };
  assert.equal(await acceptStoredPoAManifestVersion(storage, {
    ...base,
    platform: 'youtube',
    digest: 'aa'.repeat(32),
  }), true);
  assert.equal(await acceptStoredPoAManifestVersion(storage, {
    ...base,
    platform: 'x',
    digest: 'bb'.repeat(32),
  }), true, 'same textual id on X does not collide with the YouTube ratchet');
  assert.equal(await acceptStoredPoAManifestVersion(storage, {
    ...base,
    platform: 'x',
    counter: 0,
    digest: 'cc'.repeat(32),
  }), false, 'X route rollback is refused by the shared persistent gate');
});

test('401 protected endpoint embeds no credential and yields local-only recognition', async () => {
  const storage = memoryStorage({
    dregg_poa_youtube_videos: { [VIDEO]: true },
  });
  let request = null;
  const engine = createStoredPoAEngine(storage, async (url, init) => {
    request = { url, init };
    return new Response('', { status: 401 });
  });
  const response = await engine.handle({
    op: 'openContext',
    context: { href: `https://www.youtube.com/watch?v=${VIDEO}` },
  });
  assert.equal(response.ok, true);
  assert.equal(response.recognized, true);
  assert.equal(response.verified, false);
  assert.equal(response.model.trust, 'local_allowlist');
  assert.equal(response.model.game, undefined);
  assert.equal(request.url, 'https://companion.pathofangels.network/v1/youtube/AbCdEfGhI01.json');
  assert.deepEqual(request.init.headers, { Accept: 'application/json' }, 'no Authorization header or embedded beta password');
  assert.equal(request.init.cache, 'no-store');
  assert.equal(request.init.method, undefined, 'fetch defaults to GET; the client never mutates the discovery origin');

  const denied = await createStoredPoAEngine(memoryStorage(), async () => new Response('', { status: 401 })).handle({
    op: 'openContext',
    context: { href: `https://www.youtube.com/watch?v=${VIDEO}` },
  });
  assert.equal(denied.ok, false, '401 with no exact local allowlist stays default-deny');
});

test('X transport uses its exact post endpoint and never embeds beta credentials', async () => {
  let request = null;
  const engine = createStoredPoAEngine(memoryStorage(), async (url, init) => {
    request = { url, init };
    return new Response('', { status: 401 });
  });
  const response = await engine.handle({
    op: 'openContext',
    context: { href: `https://x.com/sentyr/status/${X_POST}` },
  });
  assert.equal(response.ok, false, 'X has no unsigned/local authority fallback');
  assert.equal(request.url, `https://companion.pathofangels.network/v1/x/${X_POST}.json`);
  assert.deepEqual(request.init.headers, { Accept: 'application/json' });
  assert.equal('Authorization' in request.init.headers, false);
});

test('fresh public transport refuses valid trusted legacy v1/v2 for both YouTube and X', async () => {
  const pair = await crypto.subtle.generateKey({ name: 'Ed25519' }, true, ['sign', 'verify']);
  const signer = bytesToHex(await crypto.subtle.exportKey('raw', pair.publicKey));

  for (const schema of ['poa-companion/v1', 'poa-companion/v2']) {
    for (const platform of ['youtube', 'x']) {
      const value = platform === 'youtube' ? manifest({ schema }) : xManifest(X_POST, { schema });
      const envelope = await cryptographicallySignedEnvelope(value, pair, signer);
      assert.equal(await crypto.subtle.verify(
        { name: 'Ed25519' },
        pair.publicKey,
        Buffer.from(envelope.signature, 'hex'),
        poaManifestSigningBytes(value),
      ), true, `${schema}/${platform} fixture really is signature-valid`);

      const publicStorage = memoryStorage({
        dregg_poa_trusted_curators: { [signer]: true },
      });
      const publicEngine = createStoredPoAEngine(publicStorage, async () => new Response(
        JSON.stringify(envelope),
        { status: 200, headers: { 'Content-Type': 'application/json' } },
      ));
      const request = platform === 'youtube'
        ? { op: 'openContext', context: { href: `https://www.youtube.com/watch?v=${VIDEO}` } }
        : { op: 'openContext', context: { href: `https://x.com/sentyr/status/${X_POST}` } };
      assert.equal((await publicEngine.handle(request)).ok, false, `${schema}/${platform} is unreachable from fresh public fetch`);

      // Legacy compatibility is an explicitly named persisted-envelope
      // migration mode, never the shipping public-network factory.
      const legacyKey = 'dregg_poa_legacy_manifest_migration';
      const persistedStorage = memoryStorage({ [legacyKey]: envelope });
      const migrationEngine = new PoAEngine({
        manifestSource: 'persisted_legacy_migration',
        resolveSignedManifest: async () => (await persistedStorage.get(legacyKey))[legacyKey] ?? null,
        isVideoAllowlisted: async () => false,
        trustedCuratorKeys: async () => new Set([signer]),
        acceptManifestVersion: async () => true,
        nowSeconds: () => NOW,
      });
      assert.equal((await migrationEngine.handle(request)).ok, true, `${schema}/${platform} remains readable only for explicit persisted migration`);
    }
  }
});

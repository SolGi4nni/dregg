/** Real PoA detector + element + signature engine, with only transport and the
 * nested Descent engine stood in. */
import {
  PoAEngine,
  POA_BETA_URL,
  acceptStoredPoAManifestVersion,
  poaManifestSigningBytes,
  type PoAManifestV1,
  type SignedPoAManifestV1,
  type PoACompanionPort,
} from "../../src/poa";
import { findPoAXPostTarget, startPoACompanionDetector, type DetectedPoAContext } from "../../src/poa-detect";
import { setPoAPortFactory } from "../../src/elements/dregg-poa";
import { registerDescentElement, setDescentPortFactory } from "../../src/elements/dregg-descent";

declare const window: any;

const VIDEO_A = "AbCdEfGhI01";
const VIDEO_B = "ZyXwVuTsR02";
const VIDEO_MISMATCH = "LmNoPqRsT03";
const VIDEO_LOCAL = "AllowVid004";
const X_POST = "1891234567890123456";
const NOW = 1_800_000_000;

function memoryStorage() {
  const data: Record<string, unknown> = {};
  return {
    async get(keys: string | string[]) {
      const names = Array.isArray(keys) ? keys : [keys];
      return Object.fromEntries(names.filter((key) => key in data).map((key) => [key, structuredClone(data[key])]));
    },
    async set(values: Record<string, unknown>) {
      Object.assign(data, structuredClone(values));
    },
  };
}

function bytesToHex(bytes: ArrayBuffer | Uint8Array): string {
  const view = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
  return Array.from(view, (b) => b.toString(16).padStart(2, "0")).join("");
}

function manifest(videoId: string, suffix: string, withGame: boolean): PoAManifestV1 {
  return {
    schema: "poa-companion/v1",
    contentEpoch: 1,
    counter: Number(suffix),
    context: { platform: "youtube", videoId, channelId: "UC_PathOfAngels_Test_Channel" },
    experience: {
      id: `episode-${suffix}`,
      title: `Path of Angels — Field Dispatch ${suffix}`,
      episode: `Episode ${suffix}`,
      dispatch: `Deck ${400 + Number(suffix)} has answered the survey ping.`,
      betaUrl: `${POA_BETA_URL}?episode=${suffix}`,
      ...(withGame ? { game: { kind: "descent" as const, src: "dregg://descent/b3_de5ce0" } } : {}),
    },
    issuedAt: NOW - 60,
    expiresAt: NOW + 3600,
  };
}

function xManifest(postId: string): PoAManifestV1 {
  return {
    schema: "poa-companion/v1",
    contentEpoch: 1,
    counter: 1,
    context: { platform: "x", postId },
    experience: {
      id: "x-field-dispatch",
      title: "Path of Angels — X Field Dispatch",
      episode: "Signal intercept",
      dispatch: '<img src=x onerror="globalThis.__POA_X_XSS=1"> Exact post route acquired.',
      betaUrl: `${POA_BETA_URL}?x=${postId}`,
      game: { kind: "descent", src: "dregg://descent/b3_de5ce0" },
    },
    issuedAt: NOW - 60,
    expiresAt: NOW + 3600,
  };
}

async function signManifest(value: PoAManifestV1, pair: CryptoKeyPair, signer: string): Promise<SignedPoAManifestV1> {
  const signature = await crypto.subtle.sign({ name: "Ed25519" }, pair.privateKey, poaManifestSigningBytes(value));
  return { manifest: value, signer, signature: bytesToHex(signature) };
}

const state = {
  room: "gate",
  hp: 50,
  wardenHp: 45,
  depth: 0,
  gold: 0,
  downed: 0,
  alive: true,
  dead: false,
  won: false,
  ended: false,
  turns: 1,
  commitment: "de5ce0",
};

(async () => {
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;
  const pair = await crypto.subtle.generateKey({ name: "Ed25519" }, true, ["sign", "verify"]);
  const signer = bytesToHex(await crypto.subtle.exportKey("raw", pair.publicKey));
  const signedA = await signManifest(manifest(VIDEO_A, "1", true), pair, signer);
  const revocationManifest = manifest(VIDEO_A, "1", false);
  revocationManifest.counter = 2;
  revocationManifest.experience.dispatch = '<img src=x onerror="globalThis.__POA_XSS=1"> Route withdrawn by field command.';
  const signedARevoked = await signManifest(revocationManifest, pair, signer);
  const signedB = await signManifest(manifest(VIDEO_B, "2", false), pair, signer);
  const signedX = await signManifest(xManifest(X_POST), pair, signer);
  const versionStorage = memoryStorage();
  let lookups = 0;
  let completedLookups = 0;
  let currentContext: DetectedPoAContext | null = {
    href: `https://www.youtube.com/watch?v=${VIDEO_A}`,
    platform: "youtube",
    videoId: VIDEO_A,
    channelHint: "UC_PathOfAngels_Test_Channel",
  };
  let contextFromHistory = false;
  let currentTime = NOW;
  let servedA: SignedPoAManifestV1 | null = signedA;
  let deferResponses = false;
  const deferredReleases: Array<() => void> = [];

  const engine = new PoAEngine({
    async resolveSignedManifest(context) {
      lookups += 1;
      if (context.platform === "x") return context.postId === X_POST ? signedX : null;
      if (context.videoId === VIDEO_A) return servedA;
      if (context.videoId === VIDEO_B) return signedB;
      // A valid signature for ANOTHER video must not recognize this context.
      if (context.videoId === VIDEO_MISMATCH) return signedA;
      return null;
    },
    async isVideoAllowlisted(videoId) {
      return videoId === VIDEO_LOCAL;
    },
    async trustedCuratorKeys() {
      return new Set([signer]);
    },
    acceptManifestVersion: (version) => acceptStoredPoAManifestVersion(versionStorage, version),
    nowSeconds: () => currentTime,
  });
  const port: PoACompanionPort = {
    async request(req) {
      const response = await engine.handle(req);
      completedLookups += 1;
      if (deferResponses) {
        await new Promise<void>((resolve) => deferredReleases.push(resolve));
      }
      return response;
    },
  };
  setPoAPortFactory(() => port);

  // The companion routes to the real `<dregg-descent>` thin view. Its background
  // transport is stood in here; no game rules are copied into the PoA companion.
  setDescentPortFactory(() => ({
    async request(req) {
      if (req.op === "openDescent") {
        return {
          ok: true,
          verified: true,
          tier: "extension",
          object: { kind: "descent", addr: "b3_de5ce0", title: "Deck 401 survey", seedHex: "0123456789abcdef" },
          state,
          commitment: state.commitment,
          canSettle: false,
        };
      }
      if (req.op === "renderDescent") {
        return {
          ok: true,
          tier: "extension",
          room: "gate",
          prose: "An unlit maintenance span falls away beneath the expedition.",
          moves: [{ index: 0, text: "Lower the survey drone", available: true }],
          state,
        };
      }
      if (req.op === "verifyDescent") return { ok: true, tier: "extension", verified: true, state, commitment: state.commitment };
      return { ok: true, tier: "extension", refused: true, reason: "fixture does not advance" };
    },
  }));
  registerDescentElement();

  const getContext = (): DetectedPoAContext | null => {
    if (!contextFromHistory) return currentContext;
    const match = location.pathname.match(/^\/__poa_x\/status\/([1-9][0-9]{0,19})$/);
    if (!match) return null;
    return {
      href: `https://x.com/sentyr/status/${match[1]}`,
      platform: "x",
      postId: match[1],
    };
  };
  const getTarget = (context: DetectedPoAContext) => context.platform === "x"
    ? findPoAXPostTarget(context.postId)
    : document.querySelector("[data-dregg-poa-anchor]");

  // Prove the default-deny gate before enabling the fixture's explicit opt-in.
  await startPoACompanionDetector({ isOriginAllowed: async () => false, getContext, getTarget, port, debounceMs: 0 });
  window.__POA_DENIED_COUNT = document.querySelectorAll("dregg-poa").length;

  const stop = await startPoACompanionDetector({
    isOriginAllowed: async () => true,
    getContext,
    getTarget,
    port,
    debounceMs: 0,
    refreshMs: 5 * 60 * 1000,
    nowSeconds: () => currentTime,
  });

  window.__poaSetVideo = (videoId: string) => {
    contextFromHistory = false;
    currentContext = {
      href: `https://www.youtube.com/watch?v=${videoId}`,
      platform: "youtube",
      videoId,
      channelHint: "UC_PathOfAngels_Test_Channel",
    };
    window.dispatchEvent(new Event("yt-navigate-finish"));
  };
  window.__poaSetXPost = (postId: string) => {
    contextFromHistory = false;
    currentContext = { href: `https://x.com/sentyr/status/${postId}`, platform: "x", postId };
    window.dispatchEvent(new PopStateEvent("popstate"));
  };
  window.__poaSetXPostHeld = (postId: string) => {
    contextFromHistory = false;
    deferResponses = true;
    currentContext = { href: `https://x.com/sentyr/status/${postId}`, platform: "x", postId };
    window.dispatchEvent(new PopStateEvent("popstate"));
  };
  window.__poaPushXPostHeld = (postId: string) => {
    deferResponses = true;
    contextFromHistory = true;
    history.pushState({}, "", `/__poa_x/status/${postId}`);
  };
  window.__poaPushXPost = (postId: string) => {
    contextFromHistory = true;
    history.pushState({}, "", `/__poa_x/status/${postId}`);
  };
  window.__poaClearContext = () => {
    currentContext = null;
    window.dispatchEvent(new PopStateEvent("popstate"));
  };
  window.__poaRemoveMounted = () => document.querySelector("dregg-poa")?.remove();
  window.__poaLookupCount = () => lookups;
  window.__poaCompletedLookupCount = () => completedLookups;
  window.__poaRevokeA = () => {
    servedA = signedARevoked;
    window.dispatchEvent(new Event("focus"));
  };
  window.__poaRollbackA = () => {
    servedA = signedA;
    window.dispatchEvent(new Event("focus"));
  };
  window.__poaExpireAOfflineHeld = () => {
    currentTime = NOW + 4000;
    servedA = null;
    deferResponses = true;
    window.dispatchEvent(new Event("focus"));
  };
  window.__poaRestoreRevokedA = () => {
    currentTime = NOW;
    servedA = signedARevoked;
    window.dispatchEvent(new Event("focus"));
  };
  window.__poaHoldValidA = () => {
    deferResponses = true;
    servedA = signedARevoked;
    window.dispatchEvent(new Event("focus"));
  };
  window.__poaAdvancePastAExpiry = () => {
    currentTime = NOW + 4000;
  };
  window.__poaDeferredCount = () => deferredReleases.length;
  window.__poaReleaseDeferredAndFlush = async () => {
    deferResponses = false;
    for (const release of deferredReleases.splice(0)) release();
    // Drain promise continuations without yielding to a zero-delay refresh
    // timer. This lets the test observe whether an expired response was ever
    // mounted on arrival, even for a single task.
    for (let i = 0; i < 12; i += 1) await Promise.resolve();
    return document.querySelectorAll("dregg-poa").length;
  };
  window.__poaReplaceNoContextAndRelease = async () => {
    history.replaceState({}, "", "/__poa_x/home");
    return window.__poaReleaseDeferredAndFlush();
  };
  window.__poaReplaceNoContext = () => {
    history.replaceState({}, "", "/__poa_x/home");
  };
  window.__poaResetClock = () => {
    currentTime = NOW;
  };
  window.__poaStop = stop;
  window.__POA_VIDEOS = { VIDEO_A, VIDEO_B, VIDEO_MISMATCH, VIDEO_LOCAL, X_POST };
  window.__DREGG_READY = true;
})().catch((error) => {
  window.__DREGG_ERROR = String(error?.stack || error?.message || error);
});

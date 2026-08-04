/** Real PoA detector + element + signature engine, with only transport and the
 * nested Descent engine stood in. */
import {
  PoAEngine,
  POA_BETA_URL,
  poaManifestSigningBytes,
  type PoAManifestV1,
  type SignedPoAManifestV1,
  type PoACompanionPort,
} from "../../src/poa";
import { startPoACompanionDetector, type DetectedPoAContext } from "../../src/poa-detect";
import { setPoAPortFactory } from "../../src/elements/dregg-poa";
import { registerDescentElement, setDescentPortFactory } from "../../src/elements/dregg-descent";

declare const window: any;

const VIDEO_A = "AbCdEfGhI01";
const VIDEO_B = "ZyXwVuTsR02";
const VIDEO_MISMATCH = "LmNoPqRsT03";
const VIDEO_LOCAL = "AllowVid004";
const NOW = 1_800_000_000;

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
  const signedB = await signManifest(manifest(VIDEO_B, "2", false), pair, signer);
  let lookups = 0;
  let currentVideo = VIDEO_A;

  const engine = new PoAEngine({
    async resolveSignedManifest(context) {
      lookups += 1;
      if (context.videoId === VIDEO_A) return signedA;
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
    acceptManifestVersion: async () => true,
    nowSeconds: () => NOW,
  });
  const port: PoACompanionPort = { request: (req) => engine.handle(req) };
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

  const getContext = (): DetectedPoAContext => ({
    href: `https://www.youtube.com/watch?v=${currentVideo}`,
    videoId: currentVideo,
    channelHint: "UC_PathOfAngels_Test_Channel",
  });
  const getTarget = () => document.querySelector("[data-dregg-poa-anchor]");

  // Prove the default-deny gate before enabling the fixture's explicit opt-in.
  await startPoACompanionDetector({ isOriginAllowed: async () => false, getContext, getTarget, port, debounceMs: 0 });
  window.__POA_DENIED_COUNT = document.querySelectorAll("dregg-poa").length;

  const stop = await startPoACompanionDetector({
    isOriginAllowed: async () => true,
    getContext,
    getTarget,
    port,
    debounceMs: 0,
  });

  window.__poaSetVideo = (videoId: string) => {
    currentVideo = videoId;
    window.dispatchEvent(new Event("yt-navigate-finish"));
  };
  window.__poaRemoveMounted = () => document.querySelector("dregg-poa")?.remove();
  window.__poaLookupCount = () => lookups;
  window.__poaStop = stop;
  window.__POA_VIDEOS = { VIDEO_A, VIDEO_B, VIDEO_MISMATCH, VIDEO_LOCAL };
  window.__DREGG_READY = true;
})().catch((error) => {
  window.__DREGG_ERROR = String(error?.stack || error?.message || error);
});

/**
 * Path of Angels companion context — the BACKGROUND side of `<dregg-poa>`.
 *
 * This module deliberately contains no game rules. It recognizes an exact
 * YouTube video context, verifies a curator-signed routing manifest (or an
 * explicit local video allowlist), and returns a small presentation model. A
 * routed game remains a normal `<dregg-descent>` whose rules and receipts are
 * owned by the existing background/wasm engine.
 *
 * Two trust paths exist, both default-deny:
 *
 *  - `signed_manifest`: the manifest's Ed25519 key is in the extension-local
 *    curator trust set and its signature verifies over the canonical v1 bytes;
 *  - `local_allowlist`: the exact YouTube VIDEO id is extension-locally
 *    allowlisted. This path intentionally cannot attach a game; it renders only
 *    the safe Path of Angels shell + beta fallback.
 *
 * Channel ids scraped from YouTube's DOM are hints only. They never establish
 * recognition. The shipping background supplies the browser-authenticated
 * `sender.tab.url`, so a page cannot ask the worker to bless another video.
 */

export const POA_BETA_URL = "https://beta.pathofangels.network/";
export const POA_NODE_URL = "https://node.pathofangels.network";
export const POA_NODE_URL_KEY = "dregg_poa_node_url";
export const POA_VIDEO_ALLOWLIST_KEY = "dregg_poa_youtube_videos";
export const POA_CURATOR_KEYS_KEY = "dregg_poa_trusted_curators";

const YOUTUBE_VIDEO_RE = /^[A-Za-z0-9_-]{11}$/;
const YOUTUBE_CHANNEL_RE = /^[A-Za-z0-9_-]{3,128}$/;
const EXPERIENCE_ID_RE = /^[a-z0-9][a-z0-9_-]{0,63}$/;
const DESCENT_URI_RE = /^dregg:\/\/descent\/b3_[0-9a-f]{6,}$/i;
const HEX_KEY_RE = /^[0-9a-f]{64}$/i;
const HEX_SIG_RE = /^[0-9a-f]{128}$/i;

export interface PoAContextHint {
  href: string;
  channelHint?: string;
}

export interface PoAYouTubeContext {
  platform: "youtube";
  videoId: string;
  channelHint?: string;
}

export interface PoAGameRoute {
  kind: "descent";
  src: string;
}

export interface PoAManifestV1 {
  schema: "poa-companion/v1";
  context: {
    platform: "youtube";
    videoId: string;
    channelId: string;
  };
  experience: {
    id: string;
    title: string;
    episode?: string;
    dispatch?: string;
    betaUrl: string;
    game?: PoAGameRoute;
  };
  issuedAt: number;
  expiresAt: number;
}

export interface SignedPoAManifestV1 {
  manifest: PoAManifestV1;
  signer: string;
  signature: string;
}

interface PoACompanionModelBase {
  videoId: string;
  experienceId: string;
  title: string;
  episode?: string;
  dispatch?: string;
  betaUrl: string;
}

export interface PoASignedCompanionModel extends PoACompanionModelBase {
  trust: "signed_manifest";
  channelId: string;
  game?: PoAGameRoute;
  signer: string;
}

export interface PoALocalCompanionModel extends PoACompanionModelBase {
  trust: "local_allowlist";
  // These `never` fields make it impossible to accidentally bless a locally
  // recognized shell with curator/game authority at the TypeScript boundary.
  channelId?: never;
  game?: never;
  signer?: never;
}

export type PoACompanionModel = PoASignedCompanionModel | PoALocalCompanionModel;

export type PoACompanionResponse =
  | { ok: true; recognized: true; verified: true; tier: "extension"; model: PoASignedCompanionModel }
  | { ok: true; recognized: true; verified: false; tier: "none"; model: PoALocalCompanionModel }
  | { ok: false; recognized: false; verified: false; tier: "none"; error: string };

export type PoACompanionRequest = { op: "openContext"; context: PoAContextHint };

export interface PoACompanionPort {
  request(req: PoACompanionRequest): Promise<PoACompanionResponse>;
}

export interface PoAEngineDeps {
  resolveSignedManifest(context: PoAYouTubeContext): Promise<unknown | null>;
  isVideoAllowlisted(videoId: string): Promise<boolean>;
  trustedCuratorKeys(): Promise<ReadonlySet<string>>;
  verifyEd25519?(publicKeyHex: string, message: Uint8Array<ArrayBuffer>, signatureHex: string): Promise<boolean>;
  nowSeconds?: () => number;
}

/** Parse only actual YouTube watch routes. Titles, OpenGraph tags and channel
 * prose are never recognition inputs. */
export function parsePoAYouTubeUrl(href: string, channelHint?: string): PoAYouTubeContext | null {
  let url: URL;
  try {
    url = new URL(href);
  } catch {
    return null;
  }
  const host = url.hostname.toLowerCase();
  if (url.protocol !== "https:" || (host !== "www.youtube.com" && host !== "m.youtube.com" && host !== "youtube.com")) {
    return null;
  }

  let videoId = "";
  if (url.pathname === "/watch") videoId = url.searchParams.get("v") || "";
  else {
    const m = url.pathname.match(/^\/(?:shorts|live)\/([A-Za-z0-9_-]{11})(?:\/|$)/);
    videoId = m?.[1] || "";
  }
  if (!YOUTUBE_VIDEO_RE.test(videoId)) return null;
  const cleanChannel = channelHint && YOUTUBE_CHANNEL_RE.test(channelHint) ? channelHint : undefined;
  return { platform: "youtube", videoId, channelHint: cleanChannel };
}

/** Canonical signed bytes for `poa-companion/v1`. The fixed-field projection is
 * intentional: unknown JSON fields are neither silently signed nor interpreted. */
export function poaManifestSigningBytes(manifest: PoAManifestV1): Uint8Array<ArrayBuffer> {
  const canonical = {
    schema: manifest.schema,
    context: {
      platform: manifest.context.platform,
      videoId: manifest.context.videoId,
      channelId: manifest.context.channelId,
    },
    experience: {
      id: manifest.experience.id,
      title: manifest.experience.title,
      ...(manifest.experience.episode === undefined ? {} : { episode: manifest.experience.episode }),
      ...(manifest.experience.dispatch === undefined ? {} : { dispatch: manifest.experience.dispatch }),
      betaUrl: manifest.experience.betaUrl,
      ...(manifest.experience.game === undefined
        ? {}
        : { game: { kind: manifest.experience.game.kind, src: manifest.experience.game.src } }),
    },
    issuedAt: manifest.issuedAt,
    expiresAt: manifest.expiresAt,
  };
  const encoded = new TextEncoder().encode(`poa-companion/v1\n${JSON.stringify(canonical)}`);
  const out = new Uint8Array(new ArrayBuffer(encoded.length));
  out.set(encoded);
  return out;
}

function boundedString(value: unknown, max: number, allowEmpty = false): value is string {
  return typeof value === "string" && value.length <= max && (allowEmpty || value.length > 0);
}

function validBetaUrl(value: unknown): value is string {
  if (!boundedString(value, 512)) return false;
  try {
    const u = new URL(value);
    return u.protocol === "https:" && u.origin === "https://beta.pathofangels.network";
  } catch {
    return false;
  }
}

/** Validate the entire interpreted v1 surface, including freshness and the
 * only currently supported game route. */
export function validatePoAManifest(value: unknown, nowSeconds: number): PoAManifestV1 | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const m = value as Record<string, unknown>;
  const context = m.context as Record<string, unknown> | undefined;
  const experience = m.experience as Record<string, unknown> | undefined;
  if (m.schema !== "poa-companion/v1" || !context || !experience) return null;
  if (context.platform !== "youtube" || !boundedString(context.videoId, 11) || !YOUTUBE_VIDEO_RE.test(context.videoId)) return null;
  if (!boundedString(context.channelId, 128) || !YOUTUBE_CHANNEL_RE.test(context.channelId)) return null;
  if (!boundedString(experience.id, 64) || !EXPERIENCE_ID_RE.test(experience.id)) return null;
  if (!boundedString(experience.title, 160)) return null;
  if (experience.episode !== undefined && !boundedString(experience.episode, 96)) return null;
  if (experience.dispatch !== undefined && !boundedString(experience.dispatch, 1200, true)) return null;
  if (!validBetaUrl(experience.betaUrl)) return null;
  if (!Number.isSafeInteger(m.issuedAt) || !Number.isSafeInteger(m.expiresAt)) return null;
  const issuedAt = m.issuedAt as number;
  const expiresAt = m.expiresAt as number;
  if (issuedAt > nowSeconds + 300 || expiresAt <= nowSeconds || expiresAt <= issuedAt) return null;
  // Bound replayable lifetime. A season-long manifest is fine; an effectively
  // immortal routing signature is not.
  if (expiresAt - issuedAt > 366 * 24 * 60 * 60) return null;

  let game: PoAGameRoute | undefined;
  if (experience.game !== undefined) {
    if (!experience.game || typeof experience.game !== "object" || Array.isArray(experience.game)) return null;
    const g = experience.game as Record<string, unknown>;
    if (g.kind !== "descent" || !boundedString(g.src, 256) || !DESCENT_URI_RE.test(g.src)) return null;
    game = { kind: "descent", src: g.src };
  }

  return {
    schema: "poa-companion/v1",
    context: { platform: "youtube", videoId: context.videoId, channelId: context.channelId },
    experience: {
      id: experience.id,
      title: experience.title,
      ...(experience.episode === undefined ? {} : { episode: experience.episode as string }),
      ...(experience.dispatch === undefined ? {} : { dispatch: experience.dispatch as string }),
      betaUrl: experience.betaUrl,
      ...(game ? { game } : {}),
    },
    issuedAt,
    expiresAt,
  };
}

function hexToBytes(hex: string): Uint8Array<ArrayBuffer> {
  const out = new Uint8Array(new ArrayBuffer(hex.length / 2));
  for (let i = 0; i < out.length; i++) out[i] = Number.parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  return out;
}

export async function verifyPoAEd25519(publicKeyHex: string, message: Uint8Array<ArrayBuffer>, signatureHex: string): Promise<boolean> {
  if (!HEX_KEY_RE.test(publicKeyHex) || !HEX_SIG_RE.test(signatureHex)) return false;
  try {
    const key = await crypto.subtle.importKey("raw", hexToBytes(publicKeyHex), { name: "Ed25519" }, false, ["verify"]);
    return await crypto.subtle.verify({ name: "Ed25519" }, key, hexToBytes(signatureHex), message);
  } catch {
    return false;
  }
}

function refuse(error: string): PoACompanionResponse {
  return { ok: false, recognized: false, verified: false, tier: "none", error };
}

/** Recognition engine. It routes to existing game engines but owns no game
 * transition, contribution, canon-promotion or settlement semantics. */
export class PoAEngine {
  constructor(private readonly deps: PoAEngineDeps) {}

  async handle(req: PoACompanionRequest): Promise<PoACompanionResponse> {
    if (!req || req.op !== "openContext" || !req.context) return refuse("unsupported companion request");
    const context = parsePoAYouTubeUrl(req.context.href, req.context.channelHint);
    if (!context) return refuse("not a supported YouTube video context");

    let envelope: unknown | null = null;
    try {
      envelope = await this.deps.resolveSignedManifest(context);
    } catch {
      // Network failure is not recognition. The exact local allowlist may still
      // render its deliberately game-free shell below.
    }

    const signed = await this.acceptSigned(envelope, context);
    if (signed) {
      return {
        ok: true,
        recognized: true,
        verified: true,
        tier: "extension",
        model: {
          trust: "signed_manifest",
          videoId: signed.manifest.context.videoId,
          channelId: signed.manifest.context.channelId,
          experienceId: signed.manifest.experience.id,
          title: signed.manifest.experience.title,
          ...(signed.manifest.experience.episode === undefined ? {} : { episode: signed.manifest.experience.episode }),
          ...(signed.manifest.experience.dispatch === undefined ? {} : { dispatch: signed.manifest.experience.dispatch }),
          betaUrl: signed.manifest.experience.betaUrl,
          ...(signed.manifest.experience.game === undefined ? {} : { game: signed.manifest.experience.game }),
          signer: signed.signer.toLowerCase(),
        },
      };
    }

    if (await this.deps.isVideoAllowlisted(context.videoId)) {
      const beta = new URL(POA_BETA_URL);
      beta.searchParams.set("youtube", context.videoId);
      return {
        ok: true,
        recognized: true,
        verified: false,
        tier: "none",
        model: {
          trust: "local_allowlist",
          videoId: context.videoId,
          experienceId: `youtube-${context.videoId}`,
          title: "Path of Angels field terminal",
          dispatch: "This episode is recognized. No signed field mission is attached yet.",
          betaUrl: beta.toString(),
        },
      };
    }
    return refuse("this video is not in the Path of Angels trust set");
  }

  private async acceptSigned(
    value: unknown,
    context: PoAYouTubeContext,
  ): Promise<{ manifest: PoAManifestV1; signer: string } | null> {
    if (!value || typeof value !== "object" || Array.isArray(value)) return null;
    const envelope = value as Record<string, unknown>;
    if (!boundedString(envelope.signer, 64) || !HEX_KEY_RE.test(envelope.signer)) return null;
    if (!boundedString(envelope.signature, 128) || !HEX_SIG_RE.test(envelope.signature)) return null;
    const signer = envelope.signer.toLowerCase();
    const trusted = await this.deps.trustedCuratorKeys();
    if (!trusted.has(signer)) return null;
    const manifest = validatePoAManifest(envelope.manifest, (this.deps.nowSeconds ?? (() => Math.floor(Date.now() / 1000)))());
    if (!manifest || manifest.context.videoId !== context.videoId) return null;
    const verify = this.deps.verifyEd25519 ?? verifyPoAEd25519;
    if (!(await verify(signer, poaManifestSigningBytes(manifest), envelope.signature))) return null;
    return { manifest, signer };
  }
}

export interface PoAStorageLike {
  get(keys: string | string[]): Promise<Record<string, unknown>>;
}

export type PoAFetch = (input: string, init?: RequestInit) => Promise<Response>;

function exactTrueMap(value: unknown): Record<string, true> {
  if (!value || typeof value !== "object" || Array.isArray(value)) return {};
  const out: Record<string, true> = {};
  for (const [key, allowed] of Object.entries(value as Record<string, unknown>)) {
    if (allowed === true) out[key] = true;
  }
  return out;
}

function safePoANodeBase(value: unknown): string {
  if (typeof value !== "string" || !value.trim()) return POA_NODE_URL;
  try {
    const u = new URL(value);
    const local = u.hostname === "localhost" || u.hostname === "127.0.0.1";
    if (u.protocol !== "https:" && !(local && u.protocol === "http:")) return POA_NODE_URL;
    return u.origin;
  } catch {
    return POA_NODE_URL;
  }
}

/** Construct the shipping background engine over extension-private storage and
 * the dedicated PoA node endpoint. */
export function createStoredPoAEngine(storage: PoAStorageLike, fetcher: PoAFetch = fetch): PoAEngine {
  return new PoAEngine({
    async resolveSignedManifest(context) {
      const stored = await storage.get(POA_NODE_URL_KEY);
      const base = safePoANodeBase(stored[POA_NODE_URL_KEY]);
      const url = `${base}/api/poa/companion/youtube/${encodeURIComponent(context.videoId)}`;
      const response = await fetcher(url, {
        cache: "no-store",
        signal: AbortSignal.timeout(10_000),
        headers: { Accept: "application/json" },
      });
      if (response.status === 404) return null;
      if (!response.ok) throw new Error(`PoA companion HTTP ${response.status}`);
      return response.json();
    },
    async isVideoAllowlisted(videoId) {
      const stored = await storage.get(POA_VIDEO_ALLOWLIST_KEY);
      return exactTrueMap(stored[POA_VIDEO_ALLOWLIST_KEY])[videoId] === true;
    },
    async trustedCuratorKeys() {
      const stored = await storage.get(POA_CURATOR_KEYS_KEY);
      const values = Object.keys(exactTrueMap(stored[POA_CURATOR_KEYS_KEY]))
        .filter((key) => HEX_KEY_RE.test(key))
        .map((key) => key.toLowerCase());
      return new Set(values);
    },
  });
}

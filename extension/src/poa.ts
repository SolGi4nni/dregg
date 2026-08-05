/**
 * Path of Angels companion context — the BACKGROUND side of `<dregg-poa>`.
 *
 * This module deliberately contains no game rules. It recognizes an exact
 * browser-authenticated media context, verifies a curator-signed routing manifest (or an
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
/** Public, static, GET/HEAD-only discovery origin. It is deliberately not the
 * password-curtained beta or the mutable node API. */
export const POA_COMPANION_URL = "https://companion.pathofangels.network";
export const POA_COMPANION_URL_KEY = "dregg_poa_companion_url";
export const POA_VIDEO_ALLOWLIST_KEY = "dregg_poa_youtube_videos";
export const POA_CURATOR_KEYS_KEY = "dregg_poa_trusted_curators";
export const POA_MANIFEST_VERSIONS_KEY = "dregg_poa_manifest_versions";

const YOUTUBE_VIDEO_RE = /^[A-Za-z0-9_-]{11}$/;
const YOUTUBE_CHANNEL_RE = /^[A-Za-z0-9_-]{3,128}$/;
const X_POST_RE = /^[1-9][0-9]{0,19}$/;
const EXPERIENCE_ID_RE = /^[a-z0-9][a-z0-9_-]{0,63}$/;
const DESCENT_URI_RE = /^dregg:\/\/descent\/b3_[0-9a-f]{6,}$/i;
const HEX_KEY_RE = /^[0-9a-f]{64}$/i;
const HEX_SIG_RE = /^[0-9a-f]{128}$/i;
const DIGEST_RE = /^[0-9a-f]{64}$/i;
const LOWER_DIGEST_RE = /^[0-9a-f]{64}$/;
const TAGGED_SHA256_RE = /^sha256:[0-9a-f]{64}$/;
const MAX_MANIFEST_LIFETIME_SECONDS = 7 * 24 * 60 * 60;

export const POA_RECEIPT_CORE_PROTOCOL = "FRC1" as const;
const FINALIZED_RECEIPT_CORE_V1_BYTES = 592;

export interface PoAContextHint {
  href: string;
  channelHint?: string;
}

export interface PoAYouTubeContext {
  platform: "youtube";
  videoId: string;
  channelHint?: string;
}

export interface PoAXContext {
  platform: "x";
  postId: string;
}

export type PoAResolvedContext = PoAYouTubeContext | PoAXContext;
export type PoAManifestContext =
  | { platform: "youtube"; videoId: string; channelId: string }
  | { platform: "x"; postId: string };

export interface PoAGameRoute {
  kind: "descent";
  src: string;
}

export interface PoAEpisodeLink {
  label: string;
  betaUrl: string;
}

/** Curator-authenticated routes rendered beside one exact episode/post. */
export interface PoAEpisodeActions {
  mission?: PoAEpisodeLink;
  evidence?: PoAEpisodeLink;
  debrief?: PoAEpisodeLink;
}

/** A curator-signed coordinate in the node's finalized-receipt-core namespace.
 * Naming the coordinate does not prove the node's consensus claim. */
export interface PoAFieldRecordRef {
  finalizedReceiptCoreId: string;
  federationId: string;
  turnHash: string;
}

export interface PoAContentAsset {
  path: string;
  url: string;
  mediaType: string;
  bytes: number;
  sha256: string;
}

export interface PoAContentScope {
  poaOrigin: "https://beta.pathofangels.network";
  federationId: string;
  deploymentId: string;
  contentCounter: number;
  contentPackDigest: string;
  contentAssets: readonly PoAContentAsset[];
}

interface PoAExperienceBase {
  id: string;
  title: string;
  episode?: string;
  dispatch?: string;
  betaUrl: string;
  game?: PoAGameRoute;
}

export interface PoAManifestV1 {
  schema: "poa-companion/v1";
  /** Monotone season/content epoch. A larger epoch may restart `counter`. */
  contentEpoch: number;
  /** Monotone revision within `contentEpoch`. */
  counter: number;
  context: PoAManifestContext;
  experience: PoAExperienceBase & { actions?: never; fieldRecord?: never };
  issuedAt: number;
  expiresAt: number;
}

/** v2 adds only signed episode actions and a receipt-core observation seam.
 * The routes remain beta-origin links; the extension carries no Basic Auth
 * credential and the field-record pointer makes no claim until exact transport
 * returns a matching FRC1 projection. No finality grade is inferred. */
export interface PoAManifestV2 {
  schema: "poa-companion/v2";
  contentEpoch: number;
  counter: number;
  context: PoAManifestContext;
  experience: PoAExperienceBase & {
    actions?: PoAEpisodeActions;
    fieldRecord?: PoAFieldRecordRef;
  };
  issuedAt: number;
  expiresAt: number;
}

/** v3 is the public companion transport. Unlike the older protected-node
 * drafts it binds the exact PoA deployment and signed POAG1 pack, and every
 * content asset is itself hash/length/media-type pinned. `sequence` is the
 * independent per-context revocation ratchet; contentCounter is the curator's
 * already-verified POAG1 content envelope counter. */
export interface PoAManifestV3 {
  schema: "poa-companion/v3";
  contentEpoch: number;
  contentCounter: number;
  sequence: number;
  poaOrigin: "https://beta.pathofangels.network";
  federationId: string;
  deploymentId: string;
  contentPackDigest: string;
  context: PoAManifestContext;
  experience: PoAExperienceBase & {
    contentAssets: PoAContentAsset[];
    actions?: PoAEpisodeActions;
    fieldRecord?: PoAFieldRecordRef;
  };
  issuedAt: number;
  expiresAt: number;
}

export type PoAManifest = PoAManifestV1 | PoAManifestV2 | PoAManifestV3;

export interface SignedPoAManifestV1 {
  manifest: PoAManifestV1;
  signer: string;
  signature: string;
}

export interface SignedPoAManifestV2 {
  manifest: PoAManifestV2;
  signer: string;
  signature: string;
}

export interface SignedPoAManifestV3 {
  manifest: PoAManifestV3;
  signer: string;
  signature: string;
}

export type SignedPoAManifest = SignedPoAManifestV1 | SignedPoAManifestV2 | SignedPoAManifestV3;

interface PoACompanionModelBase {
  platform: "youtube" | "x";
  /** Stable identity within `platform`, used by the shared mount lifecycle. */
  contextId: string;
  experienceId: string;
  title: string;
  episode?: string;
  dispatch?: string;
  betaUrl: string;
}

interface PoASignedCompanionModelBase extends PoACompanionModelBase {
  trust: "signed_manifest";
  contentEpoch: number;
  counter: number;
  manifestDigest: string;
  issuedAt: number;
  expiresAt: number;
  game?: PoAGameRoute;
  actions?: PoAEpisodeActions;
  fieldRecord?: PoAFieldRecordRef;
  contentScope?: PoAContentScope;
  signer: string;
}

export interface PoAYouTubeSignedCompanionModel extends PoASignedCompanionModelBase {
  platform: "youtube";
  videoId: string;
  channelId: string;
  postId?: never;
}

export interface PoAXSignedCompanionModel extends PoASignedCompanionModelBase {
  platform: "x";
  postId: string;
  videoId?: never;
  channelId?: never;
}

export type PoASignedCompanionModel = PoAYouTubeSignedCompanionModel | PoAXSignedCompanionModel;

export interface PoALocalCompanionModel extends PoACompanionModelBase {
  trust: "local_allowlist";
  platform: "youtube";
  videoId: string;
  // These `never` fields make it impossible to accidentally bless a locally
  // recognized shell with curator/game authority at the TypeScript boundary.
  channelId?: never;
  postId?: never;
  contentEpoch?: never;
  counter?: never;
  manifestDigest?: never;
  issuedAt?: never;
  expiresAt?: never;
  game?: never;
  actions?: never;
  fieldRecord?: never;
  signer?: never;
  availability: "authenticated_route_unavailable";
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
  /** The trust boundary that supplied an envelope. Public network discovery is
   * v3-only. Legacy schemas are reachable solely through an explicit persisted
   * migration reader; the shipping network factory never enables that mode. */
  manifestSource: "public_network_v3" | "persisted_legacy_migration";
  resolveSignedManifest(context: PoAResolvedContext): Promise<unknown | null>;
  isVideoAllowlisted(videoId: string): Promise<boolean>;
  trustedCuratorKeys(): Promise<ReadonlySet<string>>;
  /** Persist/check the highest signed version for this exact video+curator. */
  acceptManifestVersion(version: PoAManifestVersion): Promise<boolean>;
  verifyEd25519?(publicKeyHex: string, message: Uint8Array<ArrayBuffer>, signatureHex: string): Promise<boolean>;
  nowSeconds?: () => number;
}

export interface PoAManifestVersion {
  signer: string;
  platform: "youtube" | "x";
  contextId: string;
  contentEpoch: number;
  counter: number;
  digest: string;
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

/** Parse only browser-authenticated, canonical media routes. X feed cards are
 * deliberately excluded: their post ids come from page-owned DOM, whereas an
 * exact `/status/<id>` tab URL is supplied authoritatively by the browser. */
export function parsePoAContextUrl(href: string, channelHint?: string): PoAResolvedContext | null {
  const youtube = parsePoAYouTubeUrl(href, channelHint);
  if (youtube) return youtube;
  let url: URL;
  try {
    url = new URL(href);
  } catch {
    return null;
  }
  const host = url.hostname.toLowerCase();
  if (url.protocol !== "https:" || (host !== "x.com" && host !== "www.x.com" && host !== "twitter.com" && host !== "www.twitter.com")) {
    return null;
  }
  const match = url.pathname.match(/^\/[A-Za-z0-9_]{1,15}\/status\/([0-9]{1,20})(?:\/|$)/);
  const postId = match?.[1] ?? "";
  if (!X_POST_RE.test(postId)) return null;
  return { platform: "x", postId };
}

export function poaContextId(context: PoAResolvedContext | PoAManifestContext): string {
  return context.platform === "youtube" ? context.videoId : context.postId;
}

function samePoAContext(manifest: PoAManifestContext, page: PoAResolvedContext): boolean {
  return manifest.platform === page.platform && poaContextId(manifest) === poaContextId(page);
}

function canonicalEpisodeLink(link: PoAEpisodeLink): PoAEpisodeLink {
  return { label: link.label, betaUrl: link.betaUrl };
}

function canonicalEpisodeActions(actions: PoAEpisodeActions): PoAEpisodeActions {
  return {
    ...(actions.mission ? { mission: canonicalEpisodeLink(actions.mission) } : {}),
    ...(actions.evidence ? { evidence: canonicalEpisodeLink(actions.evidence) } : {}),
    ...(actions.debrief ? { debrief: canonicalEpisodeLink(actions.debrief) } : {}),
  };
}

function canonicalContentAsset(asset: PoAContentAsset): PoAContentAsset {
  return {
    path: asset.path,
    url: asset.url,
    mediaType: asset.mediaType,
    bytes: asset.bytes,
    sha256: asset.sha256,
  };
}

/** Canonical signed bytes for the companion protocol. v1's projection and
 * domain remain byte-for-byte unchanged. Every v2 field interpreted by the
 * companion is included in a fixed order. */
export function poaManifestSigningBytes(manifest: PoAManifest): Uint8Array<ArrayBuffer> {
  const context = manifest.context.platform === "youtube"
    ? {
        platform: "youtube" as const,
        videoId: manifest.context.videoId,
        channelId: manifest.context.channelId,
      }
    : { platform: "x" as const, postId: manifest.context.postId };
  const canonicalExperience = {
      id: manifest.experience.id,
      title: manifest.experience.title,
      ...(manifest.experience.episode === undefined ? {} : { episode: manifest.experience.episode }),
      ...(manifest.experience.dispatch === undefined ? {} : { dispatch: manifest.experience.dispatch }),
      betaUrl: manifest.experience.betaUrl,
      ...(manifest.experience.game === undefined
        ? {}
        : { game: { kind: manifest.experience.game.kind, src: manifest.experience.game.src } }),
      ...(manifest.schema === "poa-companion/v3"
        ? { contentAssets: manifest.experience.contentAssets.map(canonicalContentAsset) }
        : {}),
      ...((manifest.schema === "poa-companion/v2" || manifest.schema === "poa-companion/v3") && manifest.experience.actions
        ? { actions: canonicalEpisodeActions(manifest.experience.actions) }
        : {}),
      ...((manifest.schema === "poa-companion/v2" || manifest.schema === "poa-companion/v3") && manifest.experience.fieldRecord
        ? { fieldRecord: {
            finalizedReceiptCoreId: manifest.experience.fieldRecord.finalizedReceiptCoreId,
            federationId: manifest.experience.fieldRecord.federationId,
            turnHash: manifest.experience.fieldRecord.turnHash,
          } }
        : {}),
  };
  const canonical = manifest.schema === "poa-companion/v3" ? {
    schema: manifest.schema,
    contentEpoch: manifest.contentEpoch,
    contentCounter: manifest.contentCounter,
    sequence: manifest.sequence,
    poaOrigin: manifest.poaOrigin,
    federationId: manifest.federationId,
    deploymentId: manifest.deploymentId,
    contentPackDigest: manifest.contentPackDigest,
    context,
    experience: canonicalExperience,
    issuedAt: manifest.issuedAt,
    expiresAt: manifest.expiresAt,
  } : {
    schema: manifest.schema,
    contentEpoch: manifest.contentEpoch,
    counter: manifest.counter,
    context,
    experience: canonicalExperience,
    issuedAt: manifest.issuedAt,
    expiresAt: manifest.expiresAt,
  };
  const encoded = new TextEncoder().encode(`${manifest.schema}\n${JSON.stringify(canonical)}`);
  const out = new Uint8Array(new ArrayBuffer(encoded.length));
  out.set(encoded);
  return out;
}

function boundedString(value: unknown, max: number, allowEmpty = false): value is string {
  return typeof value === "string"
    && value.length <= max
    && (allowEmpty || value.length > 0)
    && !/[\u0000-\u001f\u007f]/.test(value);
}

function validBetaUrl(value: unknown): value is string {
  if (!boundedString(value, 512)) return false;
  try {
    const u = new URL(value);
    return u.protocol === "https:" && u.origin === "https://beta.pathofangels.network" && !u.username && !u.password;
  } catch {
    return false;
  }
}

function exactObjectKeys(value: Record<string, unknown>, allowed: readonly string[]): boolean {
  const actual = Object.keys(value).sort();
  const expected = [...allowed].sort();
  return actual.length === expected.length && actual.every((key, index) => key === expected[index]);
}

function exactOptionalObjectKeys(value: Record<string, unknown>, allowed: readonly string[]): boolean {
  return Object.keys(value).every((key) => allowed.includes(key));
}

function parseEpisodeLink(value: unknown): PoAEpisodeLink | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const link = value as Record<string, unknown>;
  if (!exactObjectKeys(link, ["label", "betaUrl"])) return null;
  if (!boundedString(link.label, 80) || !validBetaUrl(link.betaUrl)) return null;
  return { label: link.label, betaUrl: link.betaUrl };
}

function parseEpisodeActions(value: unknown): PoAEpisodeActions | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const actions = value as Record<string, unknown>;
  if (!exactOptionalObjectKeys(actions, ["mission", "evidence", "debrief"]) || Object.keys(actions).length === 0) return null;
  const parsed: PoAEpisodeActions = {};
  for (const kind of ["mission", "evidence", "debrief"] as const) {
    if (actions[kind] === undefined) continue;
    const link = parseEpisodeLink(actions[kind]);
    if (!link) return null;
    parsed[kind] = link;
  }
  return parsed;
}

function parseContentAssets(value: unknown): PoAContentAsset[] | null {
  if (!Array.isArray(value) || value.length === 0 || value.length > 8) return null;
  const parsed: PoAContentAsset[] = [];
  let previous = "";
  for (const item of value) {
    if (!item || typeof item !== "object" || Array.isArray(item)) return null;
    const asset = item as Record<string, unknown>;
    if (!exactObjectKeys(asset, ["path", "url", "mediaType", "bytes", "sha256"])) return null;
    if (!boundedString(asset.path, 160) || asset.path.startsWith("/") || asset.path.includes("..") || asset.path.includes("\\")) return null;
    if (previous && previous >= asset.path) return null;
    previous = asset.path;
    if (!boundedString(asset.url, 512) || !boundedString(asset.mediaType, 96)) return null;
    if (!Number.isSafeInteger(asset.bytes) || (asset.bytes as number) <= 0 || (asset.bytes as number) > 16 * 1024 * 1024) return null;
    if (typeof asset.sha256 !== "string" || !LOWER_DIGEST_RE.test(asset.sha256)) return null;
    const expectedUrl = `${POA_BETA_URL}artifacts/poag1/${asset.path}`;
    if (asset.url !== expectedUrl) return null;
    parsed.push({
      path: asset.path,
      url: asset.url,
      mediaType: asset.mediaType,
      bytes: asset.bytes as number,
      sha256: asset.sha256,
    });
  }
  return parsed;
}

/** Validate the complete interpreted companion surface, including freshness,
 * v1 compatibility, and v2's exact authenticated action/receipt vocabulary. */
export function validatePoAManifest(value: unknown, nowSeconds: number): PoAManifest | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const m = value as Record<string, unknown>;
  const context = m.context as Record<string, unknown> | undefined;
  const experience = m.experience as Record<string, unknown> | undefined;
  if ((m.schema !== "poa-companion/v1" && m.schema !== "poa-companion/v2" && m.schema !== "poa-companion/v3") || !context || !experience) return null;
  const schema = m.schema;
  if (schema === "poa-companion/v3") {
    if (!exactObjectKeys(m, [
      "schema", "contentEpoch", "contentCounter", "sequence", "poaOrigin", "federationId",
      "deploymentId", "contentPackDigest", "context", "experience", "issuedAt", "expiresAt",
    ])) return null;
    const contextKeys = context.platform === "youtube"
      ? ["platform", "videoId", "channelId"]
      : ["platform", "postId"];
    if (!exactObjectKeys(context, contextKeys)) return null;
    if (!exactOptionalObjectKeys(experience, ["id", "title", "episode", "dispatch", "betaUrl", "game", "contentAssets", "actions", "fieldRecord"])) return null;
    if (m.poaOrigin !== "https://beta.pathofangels.network") return null;
    for (const digestField of ["federationId", "deploymentId"] as const) {
      if (typeof m[digestField] !== "string" || !LOWER_DIGEST_RE.test(m[digestField] as string)) return null;
    }
    if (typeof m.contentPackDigest !== "string" || !TAGGED_SHA256_RE.test(m.contentPackDigest)) return null;
    if ((m.federationId as string) === "0".repeat(64) || (m.deploymentId as string) === "0".repeat(64) || m.contentPackDigest === `sha256:${"0".repeat(64)}`) return null;
    if (!Number.isSafeInteger(m.contentCounter) || (m.contentCounter as number) < 0) return null;
    if (!Number.isSafeInteger(m.sequence) || (m.sequence as number) < 0) return null;
  } else if (schema === "poa-companion/v2") {
    if (!exactObjectKeys(m, ["schema", "contentEpoch", "counter", "context", "experience", "issuedAt", "expiresAt"])) return null;
    const contextKeys = context.platform === "youtube"
      ? ["platform", "videoId", "channelId"]
      : ["platform", "postId"];
    if (!exactObjectKeys(context, contextKeys)) return null;
    if (!exactOptionalObjectKeys(experience, ["id", "title", "episode", "dispatch", "betaUrl", "game", "actions", "fieldRecord"])) return null;
  } else if ("actions" in experience || "fieldRecord" in experience || "contentAssets" in experience) {
    // These fields have v2 semantics and must never be interpreted under v1's
    // older canonical projection.
    return null;
  }
  if (!Number.isSafeInteger(m.contentEpoch) || (m.contentEpoch as number) < 0) return null;
  if (schema !== "poa-companion/v3" && (!Number.isSafeInteger(m.counter) || (m.counter as number) < 0)) return null;
  let manifestContext: PoAManifestContext;
  if (context.platform === "youtube") {
    if (!boundedString(context.videoId, 11) || !YOUTUBE_VIDEO_RE.test(context.videoId)) return null;
    if (!boundedString(context.channelId, 128) || !YOUTUBE_CHANNEL_RE.test(context.channelId)) return null;
    manifestContext = { platform: "youtube", videoId: context.videoId, channelId: context.channelId };
  } else if (context.platform === "x") {
    if (!boundedString(context.postId, 20) || !X_POST_RE.test(context.postId)) return null;
    manifestContext = { platform: "x", postId: context.postId };
  } else {
    return null;
  }
  if (!boundedString(experience.id, 64) || !EXPERIENCE_ID_RE.test(experience.id)) return null;
  if (!boundedString(experience.title, 160)) return null;
  if (experience.episode !== undefined && !boundedString(experience.episode, 96)) return null;
  if (experience.dispatch !== undefined && !boundedString(experience.dispatch, 1200, true)) return null;
  if (!validBetaUrl(experience.betaUrl)) return null;
  if (!Number.isSafeInteger(m.issuedAt) || !Number.isSafeInteger(m.expiresAt)) return null;
  const issuedAt = m.issuedAt as number;
  const expiresAt = m.expiresAt as number;
  if (issuedAt > nowSeconds + 300 || expiresAt <= nowSeconds || expiresAt <= issuedAt) return null;
  // Anti-rollback state prevents a seen revision moving backward. This short
  // lifetime also bounds first-seen replay of an obsolete but never-before-seen
  // route; revocation never depends on a year-old signature expiring.
  if (expiresAt - issuedAt > MAX_MANIFEST_LIFETIME_SECONDS) return null;

  let game: PoAGameRoute | undefined;
  if (experience.game !== undefined) {
    if (!experience.game || typeof experience.game !== "object" || Array.isArray(experience.game)) return null;
    const g = experience.game as Record<string, unknown>;
    if (g.kind !== "descent" || !boundedString(g.src, 256) || !DESCENT_URI_RE.test(g.src)) return null;
    game = { kind: "descent", src: g.src };
  }

  let actions: PoAEpisodeActions | undefined;
  let fieldRecord: PoAFieldRecordRef | undefined;
  if (schema === "poa-companion/v2" || schema === "poa-companion/v3") {
    if ((experience.actions !== undefined || experience.fieldRecord !== undefined) && experience.episode === undefined) return null;
    if (experience.actions !== undefined) {
      actions = parseEpisodeActions(experience.actions) ?? undefined;
      if (!actions) return null;
    }
    if (experience.fieldRecord !== undefined) {
      if (!experience.fieldRecord || typeof experience.fieldRecord !== "object" || Array.isArray(experience.fieldRecord)) return null;
      const ref = experience.fieldRecord as Record<string, unknown>;
      if (!exactObjectKeys(ref, ["finalizedReceiptCoreId", "federationId", "turnHash"])) return null;
      if (typeof ref.finalizedReceiptCoreId !== "string" || !LOWER_DIGEST_RE.test(ref.finalizedReceiptCoreId) || ref.finalizedReceiptCoreId === "0".repeat(64)) return null;
      if (typeof ref.federationId !== "string" || !LOWER_DIGEST_RE.test(ref.federationId)) return null;
      if (typeof ref.turnHash !== "string" || !LOWER_DIGEST_RE.test(ref.turnHash)) return null;
      fieldRecord = {
        finalizedReceiptCoreId: ref.finalizedReceiptCoreId,
        federationId: ref.federationId,
        turnHash: ref.turnHash,
      };
    }
  }

  let contentAssets: PoAContentAsset[] | undefined;
  if (schema === "poa-companion/v3") {
    contentAssets = parseContentAssets(experience.contentAssets) ?? undefined;
    if (!contentAssets) return null;
    if (fieldRecord && fieldRecord.federationId !== m.federationId) return null;
  }

  const common = {
    contentEpoch: m.contentEpoch as number,
    counter: schema === "poa-companion/v3" ? m.sequence as number : m.counter as number,
    context: manifestContext,
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
  if (schema === "poa-companion/v1") return { schema, ...common };
  if (schema === "poa-companion/v3") return {
    schema,
    contentEpoch: common.contentEpoch,
    contentCounter: m.contentCounter as number,
    sequence: m.sequence as number,
    poaOrigin: m.poaOrigin as "https://beta.pathofangels.network",
    federationId: m.federationId as string,
    deploymentId: m.deploymentId as string,
    contentPackDigest: m.contentPackDigest as string,
    context: common.context,
    experience: {
      ...common.experience,
      contentAssets: contentAssets!,
      ...(actions ? { actions } : {}),
      ...(fieldRecord ? { fieldRecord } : {}),
    },
    issuedAt: common.issuedAt,
    expiresAt: common.expiresAt,
  };
  return {
    schema,
    ...common,
    experience: {
      ...common.experience,
      ...(actions ? { actions } : {}),
      ...(fieldRecord ? { fieldRecord } : {}),
    },
  };
}

export interface PoAFieldRecordBinding {
  readonly platform: "youtube" | "x";
  readonly contextId: string;
  readonly experienceId: string;
  readonly manifestDigest: string;
  readonly finalizedReceiptCoreId: string;
  readonly federationId: string;
  readonly turnHash: string;
}

export type PoAReceiptCorePredecessorObservation =
  | { kind: "genesis" }
  | { kind: "legacy_cutover"; legacyReceiptIndex: number; legacyReceiptHash: string }
  | { kind: "core"; coreId: string; legacyReceiptIndex: number; legacyReceiptHash: string };

/** A self-consistent response from one node's FRC1 HTTP endpoint. Neither the
 * FRC1 response nor its canonical core contains a quorum certificate. */
export interface PoAReceiptCoreObservationV1 {
  grade: "node_transport_observation";
  quorumFinality: "not_verified_by_extension";
  coreIdHash: "not_verified_by_extension";
  canonicalProjection: "self_consistent_frc1";
  protocol: typeof POA_RECEIPT_CORE_PROTOCOL;
  platform: "youtube" | "x";
  contextId: string;
  experienceId: string;
  manifestDigest: string;
  finalizedReceiptCoreId: string;
  receiptIndex: number;
  federationId: string;
  turnHash: string;
  blockId: string;
  tauRound: number;
  consensusUnixSeconds: number;
  committeeEpoch: number;
  agent: string;
  predecessor: PoAReceiptCorePredecessorObservation;
}

declare const POA_VERIFIED_FINALITY: unique symbol;

/** Nominal interface reserved for a future verifier that consumes actual
 * quorum evidence. Its unexported unique-symbol brand has no raw-JSON spelling,
 * and this module deliberately exports no constructor or parser for it. */
export interface PoAVerifiedFieldRecordFinality {
  readonly finalizedReceiptCoreId: string;
  readonly [POA_VERIFIED_FINALITY]: "quorum_evidence_verified";
}

interface DecodedFrc1Projection {
  blockId: string;
  tauRound: number;
  consensusUnixSeconds: number;
  committeeEpoch: number;
  turnHash: string;
  agent: string;
  federationId: string;
  predecessor: PoAReceiptCorePredecessorObservation;
}

function bytesHex(bytes: Uint8Array<ArrayBuffer>, start: number, end: number): string {
  return Array.from(bytes.subarray(start, end), (byte) => byte.toString(16).padStart(2, "0")).join("");
}

function safeWireInteger(view: DataView, offset: number, signed = false): number | null {
  const value = signed ? view.getBigInt64(offset, true) : view.getBigUint64(offset, true);
  if (value < BigInt(Number.MIN_SAFE_INTEGER) || value > BigInt(Number.MAX_SAFE_INTEGER)) return null;
  return Number(value);
}

function decodeFrc1Projection(canonicalCore: string): DecodedFrc1Projection | null {
  if (!new RegExp(`^[0-9a-f]{${FINALIZED_RECEIPT_CORE_V1_BYTES * 2}}$`).test(canonicalCore)) return null;
  const bytes = hexToBytes(canonicalCore);
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const hasPrefix = (offset: number, magic: readonly number[]): boolean =>
    magic.every((byte, index) => bytes[offset + index] === byte) &&
    bytes[offset + 4] === 1 && bytes[offset + 5] === 0 && bytes[offset + 6] === 0 && bytes[offset + 7] === 0;
  if (!hasPrefix(0, [0x46, 0x52, 0x43, 0x31]) || !hasPrefix(8, [0x46, 0x45, 0x43, 0x31])) return null;
  const tauRound = safeWireInteger(view, 48);
  const consensusUnixSeconds = safeWireInteger(view, 56, true);
  const committeeEpoch = safeWireInteger(view, 64);
  if (tauRound === null || consensusUnixSeconds === null || committeeEpoch === null) return null;

  const predecessorTag = bytes[248];
  const legacyReceiptIndex = safeWireInteger(view, 249);
  if (legacyReceiptIndex === null) return null;
  const legacyReceiptHash = bytesHex(bytes, 257, 289);
  const predecessorCoreId = bytesHex(bytes, 289, 321);
  const zero = "0".repeat(64);
  let predecessor: PoAReceiptCorePredecessorObservation;
  if (predecessorTag === 0 && legacyReceiptIndex === 0 && legacyReceiptHash === zero && predecessorCoreId === zero) {
    predecessor = { kind: "genesis" };
  } else if (predecessorTag === 1 && legacyReceiptHash !== zero && predecessorCoreId === zero) {
    predecessor = { kind: "legacy_cutover", legacyReceiptIndex, legacyReceiptHash };
  } else if (predecessorTag === 2 && legacyReceiptHash !== zero && predecessorCoreId !== zero) {
    predecessor = { kind: "core", coreId: predecessorCoreId, legacyReceiptIndex, legacyReceiptHash };
  } else {
    return null;
  }
  if ((bytes[585] & ~0b11) !== 0 || bytes.subarray(586, 592).some((byte) => byte !== 0)) return null;
  return {
    blockId: bytesHex(bytes, 16, 48),
    tauRound,
    consensusUnixSeconds,
    committeeEpoch,
    turnHash: bytesHex(bytes, 72, 104),
    agent: bytesHex(bytes, 321, 353),
    federationId: bytesHex(bytes, 353, 385),
    predecessor,
  };
}

function parseObservedPredecessor(value: unknown): PoAReceiptCorePredecessorObservation | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const predecessor = value as Record<string, unknown>;
  if (predecessor.kind === "genesis") return exactObjectKeys(predecessor, ["kind"]) ? { kind: "genesis" } : null;
  if (predecessor.kind === "legacy_cutover") {
    if (!exactObjectKeys(predecessor, ["kind", "legacy_receipt_index", "legacy_receipt_hash"])) return null;
    if (!Number.isSafeInteger(predecessor.legacy_receipt_index) || (predecessor.legacy_receipt_index as number) < 0) return null;
    if (typeof predecessor.legacy_receipt_hash !== "string" || !LOWER_DIGEST_RE.test(predecessor.legacy_receipt_hash)) return null;
    return { kind: "legacy_cutover", legacyReceiptIndex: predecessor.legacy_receipt_index as number, legacyReceiptHash: predecessor.legacy_receipt_hash };
  }
  if (predecessor.kind === "core") {
    if (!exactObjectKeys(predecessor, ["kind", "core_id", "legacy_receipt_index", "legacy_receipt_hash"])) return null;
    if (!Number.isSafeInteger(predecessor.legacy_receipt_index) || (predecessor.legacy_receipt_index as number) < 0) return null;
    if (typeof predecessor.legacy_receipt_hash !== "string" || !LOWER_DIGEST_RE.test(predecessor.legacy_receipt_hash)) return null;
    if (typeof predecessor.core_id !== "string" || !LOWER_DIGEST_RE.test(predecessor.core_id)) return null;
    return { kind: "core", coreId: predecessor.core_id, legacyReceiptIndex: predecessor.legacy_receipt_index as number, legacyReceiptHash: predecessor.legacy_receipt_hash };
  }
  return null;
}

function sameObservedPredecessor(left: PoAReceiptCorePredecessorObservation, right: PoAReceiptCorePredecessorObservation): boolean {
  if (left.kind !== right.kind) return false;
  if (left.kind === "genesis" || right.kind === "genesis") return true;
  if (left.legacyReceiptIndex !== right.legacyReceiptIndex || left.legacyReceiptHash !== right.legacyReceiptHash) return false;
  return left.kind !== "core" || (right.kind === "core" && left.coreId === right.coreId);
}

/** Parse the actual public `FinalizedReceiptCoreResponse` shape. This checks
 * exact signed coordinates and byte-level FRC1 projection consistency, but it
 * deliberately returns only a node transport observation: the endpoint carries
 * neither a quorum certificate nor a locally verifiable core-id hash primitive. */
export function parsePoAReceiptCoreObservation(
  value: unknown,
  binding: PoAFieldRecordBinding,
): PoAReceiptCoreObservationV1 | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const record = value as Record<string, unknown>;
  if (!exactObjectKeys(record, [
    "protocol", "receipt_index", "core_id", "canonical_core", "block_id", "tau_round",
    "consensus_unix_seconds", "committee_epoch", "predecessor", "turn_hash", "agent", "federation_id",
  ])) return null;
  if (record.protocol !== POA_RECEIPT_CORE_PROTOCOL || record.core_id !== binding.finalizedReceiptCoreId) return null;
  const validContext = binding.platform === "youtube" ? YOUTUBE_VIDEO_RE.test(binding.contextId) : X_POST_RE.test(binding.contextId);
  if (!validContext || !EXPERIENCE_ID_RE.test(binding.experienceId)) return null;
  if (![binding.manifestDigest, binding.finalizedReceiptCoreId, binding.federationId, binding.turnHash].every((digest) => LOWER_DIGEST_RE.test(digest))) return null;
  if (binding.finalizedReceiptCoreId === "0".repeat(64)) return null;
  if (!Number.isSafeInteger(record.receipt_index) || (record.receipt_index as number) < 0) return null;
  if (!Number.isSafeInteger(record.tau_round) || (record.tau_round as number) < 0) return null;
  if (!Number.isSafeInteger(record.consensus_unix_seconds)) return null;
  if (!Number.isSafeInteger(record.committee_epoch) || (record.committee_epoch as number) < 0) return null;
  for (const field of ["core_id", "block_id", "turn_hash", "agent", "federation_id"] as const) {
    if (typeof record[field] !== "string" || !LOWER_DIGEST_RE.test(record[field])) return null;
  }
  if (record.turn_hash !== binding.turnHash || record.federation_id !== binding.federationId) return null;
  if (typeof record.canonical_core !== "string") return null;
  const canonical = decodeFrc1Projection(record.canonical_core);
  const predecessor = parseObservedPredecessor(record.predecessor);
  if (!canonical || !predecessor || !sameObservedPredecessor(canonical.predecessor, predecessor)) return null;
  if (canonical.blockId !== record.block_id || canonical.tauRound !== record.tau_round ||
      canonical.consensusUnixSeconds !== record.consensus_unix_seconds || canonical.committeeEpoch !== record.committee_epoch ||
      canonical.turnHash !== record.turn_hash || canonical.agent !== record.agent || canonical.federationId !== record.federation_id) return null;
  return Object.freeze({
    grade: "node_transport_observation",
    quorumFinality: "not_verified_by_extension",
    coreIdHash: "not_verified_by_extension",
    canonicalProjection: "self_consistent_frc1",
    protocol: POA_RECEIPT_CORE_PROTOCOL,
    platform: binding.platform,
    contextId: binding.contextId,
    experienceId: binding.experienceId,
    manifestDigest: binding.manifestDigest,
    finalizedReceiptCoreId: binding.finalizedReceiptCoreId,
    receiptIndex: record.receipt_index as number,
    federationId: record.federation_id,
    turnHash: record.turn_hash,
    blockId: record.block_id,
    tauRound: record.tau_round as number,
    consensusUnixSeconds: record.consensus_unix_seconds as number,
    committeeEpoch: record.committee_epoch as number,
    agent: record.agent,
    predecessor,
  });
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

/** Digest of the exact canonical bytes the curator signed. Persisting this pin
 * makes an equal `(epoch,counter)` idempotent only for byte-identical content. */
export async function poaManifestDigest(manifest: PoAManifest): Promise<string> {
  const digest = await crypto.subtle.digest("SHA-256", poaManifestSigningBytes(manifest));
  return Array.from(new Uint8Array(digest), (b) => b.toString(16).padStart(2, "0")).join("");
}

function refuse(error: string): PoACompanionResponse {
  return { ok: false, recognized: false, verified: false, tier: "none", error };
}

/** Recognition engine. It routes to existing game engines but owns no game
 * transition, contribution, canon-promotion or settlement semantics. */
export class PoAEngine {
  // chrome.storage has no compare-and-swap. The background owns one engine, so
  // serialize read/compare/write acceptance to prevent two simultaneous fetches
  // from letting a lower revision overwrite a higher one.
  private versionLock: Promise<void> = Promise.resolve();

  constructor(private readonly deps: PoAEngineDeps) {}

  private acceptVersion(version: PoAManifestVersion): Promise<boolean> {
    const run = this.versionLock.then(async () => {
      try {
        return await this.deps.acceptManifestVersion(version);
      } catch {
        return false;
      }
    });
    this.versionLock = run.then(() => undefined, () => undefined);
    return run;
  }

  async handle(req: PoACompanionRequest): Promise<PoACompanionResponse> {
    if (!req || req.op !== "openContext" || !req.context) return refuse("unsupported companion request");
    const context = parsePoAContextUrl(req.context.href, req.context.channelHint);
    if (!context) return refuse("not a supported Path of Angels media context");

    let envelope: unknown | null = null;
    try {
      envelope = await this.deps.resolveSignedManifest(context);
    } catch {
      // Network failure is not recognition. The exact local allowlist may still
      // render its deliberately game-free shell below.
    }

    const signed = await this.acceptSigned(envelope, context);
    if (signed) {
      const manifestContext = signed.manifest.context;
      const common = {
        trust: "signed_manifest" as const,
        contextId: poaContextId(manifestContext),
        contentEpoch: signed.manifest.contentEpoch,
        counter: signed.manifest.schema === "poa-companion/v3" ? signed.manifest.sequence : signed.manifest.counter,
        manifestDigest: signed.digest,
        issuedAt: signed.manifest.issuedAt,
        expiresAt: signed.manifest.expiresAt,
        experienceId: signed.manifest.experience.id,
        title: signed.manifest.experience.title,
        ...(signed.manifest.experience.episode === undefined ? {} : { episode: signed.manifest.experience.episode }),
        ...(signed.manifest.experience.dispatch === undefined ? {} : { dispatch: signed.manifest.experience.dispatch }),
        betaUrl: signed.manifest.experience.betaUrl,
        ...(signed.manifest.experience.game === undefined ? {} : { game: signed.manifest.experience.game }),
        ...((signed.manifest.schema === "poa-companion/v2" || signed.manifest.schema === "poa-companion/v3") && signed.manifest.experience.actions
          ? { actions: signed.manifest.experience.actions }
          : {}),
        ...((signed.manifest.schema === "poa-companion/v2" || signed.manifest.schema === "poa-companion/v3") && signed.manifest.experience.fieldRecord
          ? { fieldRecord: signed.manifest.experience.fieldRecord }
          : {}),
        ...(signed.manifest.schema === "poa-companion/v3"
          ? { contentScope: {
              poaOrigin: signed.manifest.poaOrigin,
              federationId: signed.manifest.federationId,
              deploymentId: signed.manifest.deploymentId,
              contentCounter: signed.manifest.contentCounter,
              contentPackDigest: signed.manifest.contentPackDigest,
              contentAssets: signed.manifest.experience.contentAssets,
            } }
          : {}),
        signer: signed.signer.toLowerCase(),
      };
      const model: PoASignedCompanionModel = manifestContext.platform === "youtube"
        ? {
            ...common,
            platform: "youtube",
            videoId: manifestContext.videoId,
            channelId: manifestContext.channelId,
          }
        : {
            ...common,
            platform: "x",
            postId: manifestContext.postId,
          };
      return {
        ok: true,
        recognized: true,
        verified: true,
        tier: "extension",
        model,
      };
    }

    if (context.platform === "youtube" && await this.deps.isVideoAllowlisted(context.videoId)) {
      const beta = new URL(POA_BETA_URL);
      beta.searchParams.set("youtube", context.videoId);
      return {
        ok: true,
        recognized: true,
        verified: false,
        tier: "none",
        model: {
          trust: "local_allowlist",
          platform: "youtube",
          contextId: context.videoId,
          videoId: context.videoId,
          experienceId: `youtube-${context.videoId}`,
          title: "Path of Angels field terminal",
          dispatch: "This episode is recognized. No signed field mission is attached yet.",
          betaUrl: beta.toString(),
          availability: "authenticated_route_unavailable",
        },
      };
    }
    return refuse("this media context is not in the Path of Angels trust set");
  }

  private async acceptSigned(
    value: unknown,
    context: PoAResolvedContext,
  ): Promise<{ manifest: PoAManifest; signer: string; digest: string } | null> {
    if (!value || typeof value !== "object" || Array.isArray(value)) return null;
    const envelope = value as Record<string, unknown>;
    const rawManifest = envelope.manifest;
    if (!rawManifest || typeof rawManifest !== "object" || Array.isArray(rawManifest)) return null;
    const rawSchema = (rawManifest as Record<string, unknown>).schema;
    if (this.deps.manifestSource === "public_network_v3") {
      if (rawSchema !== "poa-companion/v3") return null;
    } else if (rawSchema !== "poa-companion/v1" && rawSchema !== "poa-companion/v2") {
      return null;
    }
    if (!boundedString(envelope.signer, 64) || !HEX_KEY_RE.test(envelope.signer)) return null;
    if (!boundedString(envelope.signature, 128) || !HEX_SIG_RE.test(envelope.signature)) return null;
    const signer = envelope.signer.toLowerCase();
    const trusted = await this.deps.trustedCuratorKeys();
    if (!trusted.has(signer)) return null;
    const manifest = validatePoAManifest(envelope.manifest, (this.deps.nowSeconds ?? (() => Math.floor(Date.now() / 1000)))());
    if (!manifest || !samePoAContext(manifest.context, context)) return null;
    const verify = this.deps.verifyEd25519 ?? verifyPoAEd25519;
    if (!(await verify(signer, poaManifestSigningBytes(manifest), envelope.signature))) return null;
    let digest: string;
    try {
      digest = await poaManifestDigest(manifest);
    } catch {
      return null;
    }
    if (!(await this.acceptVersion({
      signer,
      platform: manifest.context.platform,
      contextId: poaContextId(manifest.context),
      contentEpoch: manifest.contentEpoch,
      counter: manifest.schema === "poa-companion/v3" ? manifest.sequence : manifest.counter,
      digest,
    }))) return null;
    return { manifest, signer, digest };
  }
}

export interface PoAStorageLike {
  get(keys: string | string[]): Promise<Record<string, unknown>>;
  set(values: Record<string, unknown>): Promise<void>;
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

function safePoACompanionBase(value: unknown): string {
  if (typeof value !== "string" || !value.trim()) return POA_COMPANION_URL;
  try {
    const u = new URL(value);
    const local = u.hostname === "localhost" || u.hostname === "127.0.0.1";
    if (u.protocol !== "https:" && !(local && u.protocol === "http:")) return POA_COMPANION_URL;
    return u.origin;
  } catch {
    return POA_COMPANION_URL;
  }
}

interface StoredPoAManifestVersion {
  contentEpoch: number;
  counter: number;
  digest: string;
}

function parseStoredVersion(value: unknown): StoredPoAManifestVersion | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const v = value as Record<string, unknown>;
  if (!Number.isSafeInteger(v.contentEpoch) || (v.contentEpoch as number) < 0) return null;
  if (!Number.isSafeInteger(v.counter) || (v.counter as number) < 0) return null;
  if (typeof v.digest !== "string" || !DIGEST_RE.test(v.digest)) return null;
  return { contentEpoch: v.contentEpoch as number, counter: v.counter as number, digest: v.digest.toLowerCase() };
}

function versionStorageKey(version: Pick<PoAManifestVersion, "signer" | "platform" | "contextId">): string {
  // Preserve the already-shipped YouTube key shape; X is explicitly namespaced.
  return version.platform === "youtube"
    ? `v1:${version.signer.toLowerCase()}:${version.contextId}`
    : `v1:${version.signer.toLowerCase()}:x:${version.contextId}`;
}

/** Extension-persisted rollback gate. Comparison is lexicographic by
 * `(contentEpoch,counter)`. An equal version is accepted only when its canonical
 * manifest digest is identical; an equal counter with different content is a
 * conflict, never a replacement. */
export async function acceptStoredPoAManifestVersion(
  storage: PoAStorageLike,
  version: PoAManifestVersion,
): Promise<boolean> {
  const validContext = version.platform === "youtube"
    ? YOUTUBE_VIDEO_RE.test(version.contextId)
    : version.platform === "x" && X_POST_RE.test(version.contextId);
  if (!HEX_KEY_RE.test(version.signer) || !validContext) return false;
  const candidate = parseStoredVersion(version);
  if (!candidate) return false;
  const stored = await storage.get(POA_MANIFEST_VERSIONS_KEY);
  const rawMap = stored[POA_MANIFEST_VERSIONS_KEY];
  const map: Record<string, unknown> = rawMap && typeof rawMap === "object" && !Array.isArray(rawMap)
    ? { ...(rawMap as Record<string, unknown>) }
    : {};
  const key = versionStorageKey(version);
  const rawCurrent = map[key];
  if (rawCurrent !== undefined) {
    const current = parseStoredVersion(rawCurrent);
    // Corrupt persisted anti-rollback state fails closed. Treating it as absent
    // would silently reopen every old signed route.
    if (!current) return false;
    if (candidate.contentEpoch < current.contentEpoch) return false;
    if (candidate.contentEpoch === current.contentEpoch) {
      if (candidate.counter < current.counter) return false;
      if (candidate.counter === current.counter) return candidate.digest === current.digest;
    }
  }
  map[key] = candidate;
  await storage.set({ [POA_MANIFEST_VERSIONS_KEY]: map });
  return true;
}

/** Construct the shipping background engine over extension-private storage and
 * the dedicated public, static companion origin. Mutation and node diagnostics
 * remain on their separately protected origins. */
export function createStoredPoAEngine(storage: PoAStorageLike, fetcher: PoAFetch = fetch): PoAEngine {
  return new PoAEngine({
    manifestSource: "public_network_v3",
    async resolveSignedManifest(context) {
      const stored = await storage.get(POA_COMPANION_URL_KEY);
      const base = safePoACompanionBase(stored[POA_COMPANION_URL_KEY]);
      const url = context.platform === "youtube"
        ? `${base}/v1/youtube/${encodeURIComponent(context.videoId)}.json`
        : `${base}/v1/x/${encodeURIComponent(context.postId)}.json`;
      const response = await fetcher(url, {
        cache: "no-store",
        signal: AbortSignal.timeout(10_000),
        headers: { Accept: "application/json" },
      });
      if (response.status === 404 || response.status === 401 || response.status === 403) {
        // Unknown contexts and a misrouted protected origin are both absence,
        // never recognition. No beta credential is embedded or synthesized.
        return null;
      }
      if (!response.ok) throw new Error(`PoA companion HTTP ${response.status}`);
      const envelope: unknown = await response.json();
      // This is the public-network trust seam. Keep the legacy parser available
      // for explicit persisted-envelope migration, but never hand a fresh v1/v2
      // response to generic signature acceptance.
      if (!envelope || typeof envelope !== "object" || Array.isArray(envelope)) return null;
      const manifest = (envelope as Record<string, unknown>).manifest;
      if (!manifest || typeof manifest !== "object" || Array.isArray(manifest)) return null;
      if ((manifest as Record<string, unknown>).schema !== "poa-companion/v3") return null;
      return envelope;
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
    acceptManifestVersion: (version) => acceptStoredPoAManifestVersion(storage, version),
  });
}

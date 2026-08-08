/**
 * Exact browser consumer for the Lean-owned POAG1 v1 boundary in
 * Dregg2.Games.PathOfAngels.Emit. No web-owned manifest dialect is accepted.
 */

export const POAG1_FORMAT = "POAG1";
export const POAG1_SCHEMA_VERSION = 1;
export const POAG1_AUTHORITY = "Dregg2.Games.PathOfAngels";
/**
 * The exact artifact set, in the exact order `canonicalArtifacts` emits it —
 * path-ascending after the schema and catalog, so `black-box-reconstruction`
 * sorts before `relay-repair`.
 *
 * ⚠ SIX, and the count is refused, not warned about. Black Box's descriptor
 * landed in the curator-signed counter-8 bundle, so it is enrolled here against
 * the bytes that actually shipped. This list is the exact emitted set: widening
 * it beyond what the manifest carries would mean this client accepting a shape
 * nothing has produced.
 */
export const POAG1_EXPECTED_ARTIFACTS = Object.freeze([
  Object.freeze({ path: "schema.json", mediaType: "application/schema+json" }),
  Object.freeze({ path: "catalog.json", mediaType: "application/json" }),
  // ⚠ PATH-ascending, which puts artificer-logic FIRST among the games — ahead of
  // black-box. `GAME_SPECS` below is in MISSION order (1..7). Two lists that both read
  // as "the games", sorted by different keys; the client refuses on artifact ORDER.
  Object.freeze({ path: "games/artificer-logic.json", mediaType: "application/json" }),
  Object.freeze({ path: "games/black-box-reconstruction.json", mediaType: "application/json" }),
  Object.freeze({ path: "games/deck-descent.json", mediaType: "application/json" }),
  Object.freeze({ path: "games/relay-repair.json", mediaType: "application/json" }),
  Object.freeze({ path: "games/salvage-lock.json", mediaType: "application/json" }),
  Object.freeze({ path: "games/signal-triangulation.json", mediaType: "application/json" }),
  Object.freeze({ path: "games/vent-crawl.json", mediaType: "application/json" }),
]);

/**
 * ⚑ THE FLAG DAY, DECLARED RATHER THAN DISCOVERED.
 *
 * `Emit.lean` renders SEVEN game descriptors; the list above pins the four the
 * curator has signed. That gap is one ceremony, and it used to be held by nothing
 * at all — a game could join `canonicalArtifacts` and this client would simply
 * refuse the next bundle with `POAG1 artifact count does not match the Lean
 * bundle`, at load, in a browser, with no earlier warning anywhere.
 *
 * So the delta is NAMED here and CHECKED against the emitter by
 * `tests/bundle-enrolment.test.mjs`: pinned ∪ pending must equal
 * `Emit.POAG1_GAME_PATHS` exactly, every pending game must already have a
 * controller and a fully taught rack record, and every pending descriptor must be
 * emitted into `poa/artifacts/poag1-pending/` and absent from the signed bundle.
 *
 * ⚠ THE CEREMONY'S EDIT IS TO MOVE A LINE FROM HERE TO THE LIST ABOVE, in
 * path-ascending position, in the same commit as the re-emitted bundle. Nothing
 * else about this file changes. A path left here after its descriptor lands in
 * `poa/artifacts/poag1/` fails the test, and so does the reverse.
 *
 * ⚠ It is NOT a widening. `validateManifest` still refuses any count, order, path
 * or media type other than the pinned list; a pending path buys a game nothing at
 * load time. It is a statement about what the emitter will produce next.
 */
// Empty at counter 9: all seven games are in the signed bundle. A path lands here only
// while its descriptor is emitted and NOT yet signed into the manifest.
export const POAG1_PENDING_ARTIFACTS = Object.freeze([]);

const SHA256 = /^sha256:[0-9a-f]{64}$/;
const HEX_16 = /^[0-9a-f]{16}$/;

export class ArtifactRefusal extends Error {
  constructor(code, message, cause) {
    super(message, cause ? { cause } : undefined);
    this.name = "ArtifactRefusal";
    this.code = code;
  }
}

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function isPlainObject(value) {
  if (value === null || typeof value !== "object" || Array.isArray(value)) return false;
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

function exactKeys(object, expected, at) {
  const keys = Object.keys(object).sort();
  const wanted = [...expected].sort();
  refuse(
    keys.length === wanted.length && keys.every((key, i) => key === wanted[i]),
    "unknown-field",
    `${at} must contain exactly: ${wanted.join(", ")}`,
  );
}

function parseJson(bytes, at) {
  let text;
  try { text = new TextDecoder("utf-8", { fatal: true }).decode(bytes); }
  catch (cause) { throw new ArtifactRefusal("invalid-utf8", `${at} is not valid UTF-8`, cause); }
  try { return JSON.parse(text); }
  catch (cause) { throw new ArtifactRefusal("invalid-json", `${at} is not valid JSON`, cause); }
}

export function fnv1a64(bytes) {
  let hash = 0xcbf29ce484222325n;
  for (const byte of bytes) {
    hash ^= BigInt(byte);
    hash = BigInt.asUintN(64, hash * 0x100000001b3n);
  }
  return hash.toString(16).padStart(16, "0");
}

export async function sha256Hex(bytes) {
  const subtle = globalThis.crypto?.subtle;
  refuse(subtle, "crypto-unavailable", "Web Crypto SHA-256 is required to authenticate POAG1");
  const digest = await subtle.digest("SHA-256", bytes);
  return [...new Uint8Array(digest)].map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

/** Match Emit.Manifest and canonicalArtifacts order exactly. */
export function validateManifest(value, expected = POAG1_EXPECTED_ARTIFACTS) {
  refuse(isPlainObject(value), "manifest-shape", "POAG1 manifest must be an object");
  exactKeys(value, ["format", "schema_version", "source_digest", "authority", "artifacts"], "POAG1 manifest");
  refuse(value.format === POAG1_FORMAT, "format", `expected ${POAG1_FORMAT}`);
  refuse(value.schema_version === POAG1_SCHEMA_VERSION, "schema-version", "unsupported POAG1 schema version");
  refuse(typeof value.source_digest === "string" && SHA256.test(value.source_digest), "source-digest", "source_digest must be sha256: plus lowercase full-width hex");
  refuse(value.authority === POAG1_AUTHORITY, "authority", `authority must be ${POAG1_AUTHORITY}`);
  refuse(Array.isArray(value.artifacts), "artifact-list", "artifacts must be an array");
  refuse(value.artifacts.length === expected.length, "artifact-set", "POAG1 artifact count does not match the Lean bundle");

  const entries = value.artifacts.map((entry, index) => {
    refuse(isPlainObject(entry), "artifact-entry", `artifacts[${index}] must be an object`);
    exactKeys(entry, ["path", "media_type", "bytes", "sha256", "fnv1a64"], `artifacts[${index}]`);
    const wanted = expected[index];
    refuse(entry.path === wanted.path, "artifact-order", `artifacts[${index}].path must be ${wanted.path}`);
    refuse(entry.media_type === wanted.mediaType, "artifact-media-type", `${entry.path} media_type must be ${wanted.mediaType}`);
    refuse(Number.isSafeInteger(entry.bytes) && entry.bytes > 0, "artifact-bytes", `${entry.path} has an invalid byte length`);
    refuse(typeof entry.sha256 === "string" && SHA256.test(entry.sha256), "artifact-sha256", `${entry.path} has an invalid SHA-256 pin`);
    refuse(typeof entry.fnv1a64 === "string" && HEX_16.test(entry.fnv1a64), "artifact-pin", `${entry.path} has an invalid FNV-1a pin`);
    return Object.freeze({ path: entry.path, mediaType: entry.media_type, bytes: entry.bytes, sha256: entry.sha256, fnv1a64: entry.fnv1a64 });
  });
  return Object.freeze({
    format: value.format,
    schemaVersion: value.schema_version,
    sourceDigest: value.source_digest,
    authority: value.authority,
    artifacts: Object.freeze(entries),
  });
}

async function checkedFetch(fetcher, url, label) {
  let response;
  try { response = await fetcher(url, { cache: "no-store", credentials: "same-origin" }); }
  catch (cause) { throw new ArtifactRefusal("fetch-failed", `${label} could not be fetched`, cause); }
  refuse(response && response.ok === true, "fetch-status", `${label} returned HTTP ${response?.status ?? "unknown"}`);
  return new Uint8Array(await response.arrayBuffer());
}

/** Load, byte-pin, and parse the exact six-object POAG1 bundle. */
export async function loadPOAG1({
  baseUrl = new URL("../public/artifacts/poag1/", import.meta.url),
  fetcher = globalThis.fetch,
  curatorKeyUrl,
  expectedContentEpoch,
  expectedCounter,
} = {}) {
  refuse(typeof fetcher === "function", "fetch-unavailable", "fetch is required to load POAG1");
  const root = baseUrl instanceof URL ? baseUrl : new URL(String(baseUrl), globalThis.location?.href ?? import.meta.url);
  const manifestBytes = await checkedFetch(fetcher, new URL("manifest.json", root), "POAG1 manifest");
  const signatureBytes = await checkedFetch(fetcher, new URL("manifest.sig.json", root), "POAG1 content epoch signature");
  const keyUrl = curatorKeyUrl
    ? (curatorKeyUrl instanceof URL ? curatorKeyUrl : new URL(String(curatorKeyUrl), root))
    : new URL("/poa-curator-key.json", root);
  const keyBytes = await checkedFetch(fetcher, keyUrl, "PoA curator key pin");
  const { authenticateContentEpoch } = await import("./content-epoch.js");
  const contentEpoch = await authenticateContentEpoch({ manifestBytes, signatureBytes, keyBytes, expectedContentEpoch, expectedCounter });
  const manifest = validateManifest(parseJson(manifestBytes, "POAG1 manifest"));
  const payloads = Object.create(null);
  for (const entry of manifest.artifacts) {
    const bytes = await checkedFetch(fetcher, new URL(entry.path, root), `POAG1 artifact ${entry.path}`);
    refuse(bytes.byteLength === entry.bytes, "byte-length", `${entry.path} byte length does not match the manifest`);
    refuse(`sha256:${await sha256Hex(bytes)}` === entry.sha256, "sha256-mismatch", `${entry.path} does not match its SHA-256 manifest pin`);
    refuse(fnv1a64(bytes) === entry.fnv1a64, "pin-mismatch", `${entry.path} does not match its manifest pin`);
    payloads[entry.path] = Object.freeze({ bytes, json: parseJson(bytes, entry.path), mediaType: entry.mediaType });
  }
  return Object.freeze({
    manifest,
    manifestDigest: contentEpoch.manifestDigest,
    contentEpoch,
    payloads: Object.freeze(payloads),
  });
}

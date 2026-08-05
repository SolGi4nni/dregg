/**
 * Canonical Path of Angels Galley V1 browser transport.
 *
 * The node owns projection, actions, unsigned turn bytes, events, and receipts.
 * The browser validates and renders that authority; it does not carry a Galley
 * reducer or accept caller-authored player identity.
 */

export const POA_GALLEY_SESSION_FORMAT = "POA-GALLEY-SESSION-V1";
export const POA_GALLEY_STATUS_FORMAT = "POA-GALLEY-STATUS-V1";
export const POA_GALLEY_COMMAND_PREPARE_FORMAT = "POA-GALLEY-COMMAND-PREPARE-V1";
export const POA_GALLEY_UNSIGNED_TURN_FORMAT = "POA-GALLEY-UNSIGNED-TURN-V1";
export const POA_GALLEY_PENDING_JOURNAL_FORMAT = "POA-GALLEY-PENDING-INTENT-JOURNAL-V2";
export const POA_GALLEY_PENDING_STORAGE_KEY = "poa.galley.pending-intents.v2";
export const POA_GALLEY_ACTOR_HEADER = "X-Dregg-Actor";

/** Caddy adds `/node`; the authority itself serves `/api/poa/galley/v1`. */
export const DEFAULT_GALLEY_ENDPOINTS = Object.freeze({
  session: "/node/api/poa/galley/v1/session",
  command: "/node/api/poa/galley/v1/command",
  status: "/node/api/poa/galley/v1/status",
});

const HEX32 = /^[0-9a-f]{64}$/u;
const PROFILE_NAME = /^[a-z0-9_-]{1,64}$/u;
const OPAQUE_ID = /^[\x21-\x7e]{1,256}$/u;
const ACTION_TOKEN = HEX32;
const BASE64 = /^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$/u;
const CURRENT_KEYS = Object.freeze([
  "actions", "aggregate_id", "daily_id", "federation_id", "projection",
  "projection_digest", "replay", "schema_version", "semantic_head", "sequence",
]);
const SESSION_KEYS = Object.freeze([...CURRENT_KEYS, "format"]);
const STATUS_KEYS = Object.freeze([...CURRENT_KEYS, "events", "format"]);
const PROJECTION_KEYS = Object.freeze([
  "canon_revision", "canon_root", "local_service_total", "power_root",
  "public_play_count", "public_players", "sequence", "sponsorship_count",
  "sponsors", "spent_grant_nullifiers", "loot_root",
]);
const EVENT_PAYLOAD_KEYS = Object.freeze([
  "activity_id", "actor", "authority_commitment", "beneficiary",
  "grant_nullifier", "kind", "local_service",
]);
const MAX_OPAQUE_JSON_BYTES = 128 * 1024;
const MAX_OPAQUE_JSON_DEPTH = 16;
const MAX_EVENTS = 4096;
const MAX_POSTCARD_BYTES = 1024 * 1024;

export class GalleyApiRefusal extends Error {
  constructor(code, message, status = null) {
    super(message);
    this.name = "GalleyApiRefusal";
    this.code = code;
    this.status = status;
  }
}

function refuse(condition, code, message, status = null) {
  if (!condition) throw new GalleyApiRefusal(code, message, status);
}

function freeze(value) {
  if (value && typeof value === "object" && !Object.isFrozen(value)) {
    if (ArrayBuffer.isView(value)) return value;
    for (const child of Object.values(value)) freeze(child);
    Object.freeze(value);
  }
  return value;
}

function object(name, value) {
  refuse(value && typeof value === "object" && !Array.isArray(value) &&
    [Object.prototype, null].includes(Object.getPrototypeOf(value)), "galley-shape", `${name} must be a plain object`);
  return value;
}

function exact(name, value, keys) {
  const row = object(name, value);
  const actual = Object.keys(row).sort();
  const expected = [...keys].sort();
  refuse(actual.length === expected.length && actual.every((key, index) => key === expected[index]),
    "galley-shape", `${name} has unexpected or missing fields`);
  return row;
}

function natural(name, value) {
  refuse(Number.isSafeInteger(value) && value >= 0, "galley-integer", `${name} must be a non-negative safe integer`);
  return value;
}

function opaque(name, value) {
  refuse(typeof value === "string" && OPAQUE_ID.test(value), "galley-text", `${name} must be bounded opaque text`);
  return value;
}

function digest(name, value) {
  refuse(typeof value === "string" && HEX32.test(value), "galley-digest", `${name} must be a lowercase 32-byte digest`);
  return value;
}

function digestList(name, value) {
  refuse(Array.isArray(value) && value.length <= 64, "galley-projection", `${name} must be a bounded digest list`);
  const values = value.map((item, index) => digest(`${name}[${index}]`, item));
  refuse(new Set(values).size === values.length, "galley-projection", `${name} must not contain duplicates`);
  return Object.freeze(values);
}

/** Parse the permissioned page-provider result without granting it authority.
 * The public key is only a personalization claim for node preparation. */
export function normalizeGalleyActorIdentity(value) {
  const row = object("active Dregg identity", value);
  const keys = Object.keys(row).sort();
  refuse(keys.join(",") === "publicKeyHex" || keys.join(",") === "profileName,publicKeyHex",
    "galley-actor", "active Dregg identity has unexpected or missing fields");
  refuse(typeof row.publicKeyHex === "string" && HEX32.test(row.publicKeyHex),
    "galley-actor", "active Dregg public key must be 64 lowercase hexadecimal characters");
  refuse(row.profileName === undefined || (typeof row.profileName === "string" && PROFILE_NAME.test(row.profileName)),
    "galley-actor", "active Dregg profile name is not canonical");
  return freeze({
    publicKeyHex: row.publicKeyHex,
    ...(row.profileName === undefined ? {} : { profileName: row.profileName }),
  });
}

export function galleyActorHeaders(publicKeyHex) {
  refuse(typeof publicKeyHex === "string" && HEX32.test(publicKeyHex),
    "galley-actor", "Galley actor header must be a 64-character lowercase public key");
  return freeze({ [POA_GALLEY_ACTOR_HEADER]: publicKeyHex });
}

function hexBytes(value) {
  return Uint8Array.from(value.match(/.{2}/gu), (pair) => Number.parseInt(pair, 16));
}

function canonicalBase64(name, value, maxBytes) {
  refuse(typeof value === "string" && value.length > 0 && value.length <= Math.ceil(maxBytes / 3) * 4 && BASE64.test(value),
    "galley-base64", `${name} must be canonical bounded base64`);
  const padding = value.endsWith("==") ? 2 : value.endsWith("=") ? 1 : 0;
  refuse((value.length / 4) * 3 - padding <= maxBytes, "galley-base64", `${name} exceeds its byte bound`);
  return value;
}

function jsonValue(value, depth = 0) {
  if (depth > MAX_OPAQUE_JSON_DEPTH) return false;
  if (value === null || typeof value === "boolean" || typeof value === "string") return true;
  if (typeof value === "number") return Number.isFinite(value);
  if (Array.isArray(value)) return value.length <= 4096 && value.every((item) => jsonValue(item, depth + 1));
  if (!value || typeof value !== "object" || ![Object.prototype, null].includes(Object.getPrototypeOf(value)) ||
      Object.keys(value).length > 4096) return false;
  return Object.values(value).every((item) => jsonValue(item, depth + 1));
}

function boundedJson(name, value) {
  refuse(jsonValue(value), "galley-json", `${name} is not bounded JSON`);
  let bytes;
  try { bytes = new TextEncoder().encode(JSON.stringify(value)).byteLength; }
  catch { throw new GalleyApiRefusal("galley-json", `${name} cannot be serialized`); }
  refuse(bytes <= MAX_OPAQUE_JSON_BYTES, "galley-json", `${name} exceeds its byte bound`);
  return value;
}

function providerText(name, value, { optional = false } = {}) {
  if (optional && value === undefined) return null;
  refuse(typeof value === "string" && value.length > 0 && value.length <= 320 && !/[\u0000-\u001f\u007f]/u.test(value),
    "galley-sign-result", `${name} must be bounded printable text`);
  return value;
}

function providerTurnHash(name, value, { optional = false } = {}) {
  if (optional && value === undefined) return null;
  refuse(typeof value === "string" && HEX32.test(value),
    "galley-sign-result", `${name} must be a canonical lowercase turn hash`);
  return value;
}

/** Parse the signer's final post-authorization turn hash. The separate
 * preparation digest is checked against postcard bytes before this call. */
export function normalizeGalleySigningResult(value) {
  const row = object("Dregg signing result", value);
  const allowed = new Set(["error", "nodeResult", "outboxId", "queued", "receipt", "submitted", "turnId"]);
  refuse(Object.keys(row).every((key) => allowed.has(key)), "galley-sign-result",
    "Dregg signing result has an unexpected field");
  refuse(typeof row.submitted === "boolean", "galley-sign-result", "Dregg signing result must state whether it was submitted");
  refuse(row.queued === undefined || typeof row.queued === "boolean", "galley-sign-result", "queued must be boolean when present");
  const queued = row.queued === true;
  refuse(!(row.submitted && queued), "galley-sign-result", "a turn cannot be both submitted and queued");

  const turnHash = providerTurnHash("turnId", row.turnId, { optional: true });
  const error = providerText("signing error", row.error, { optional: true });
  const outboxId = providerText("outboxId", row.outboxId, { optional: true });
  refuse(!outboxId || queued, "galley-sign-result", "outboxId is only valid for a queued turn");

  if (row.receipt !== undefined) {
    refuse(row.submitted, "galley-sign-result", "receipt metadata is only valid after submission");
    const receipt = object("signing receipt", row.receipt);
    const receiptTurnHash = providerTurnHash("receipt.turnHash", receipt.turnHash, { optional: true });
    refuse(receiptTurnHash === null || receiptTurnHash === turnHash, "galley-sign-mismatch",
      "receipt.turnHash does not match the final signed turn");
  }
  if (row.nodeResult !== undefined) {
    refuse(row.submitted && boundedJson("nodeResult", row.nodeResult), "galley-sign-result",
      "nodeResult is only valid after submission");
    const nodeResult = object("nodeResult", row.nodeResult);
    const nodeTurnHash = providerTurnHash("nodeResult.turn_hash", nodeResult.turn_hash, { optional: true });
    refuse(nodeTurnHash === null || nodeTurnHash === turnHash, "galley-sign-mismatch",
      "nodeResult.turn_hash does not match the final signed turn");
  }

  if (row.submitted) {
    refuse(turnHash !== null && error === null, "galley-sign-result",
      "submitted turn must return its exact turnId without an error");
    return freeze({ state: "submitted", turnHash, outboxId: null, error: null });
  }
  if (queued) {
    refuse(turnHash !== null, "galley-sign-result", "queued signed turn must return its exact turnId");
    return freeze({ state: "queued", turnHash, outboxId, error });
  }
  const declined = typeof error === "string" && /\b(?:user\s+)?declin(?:e|ed)\b/iu.test(error);
  return freeze({ state: declined ? "declined" : "refused", turnHash, outboxId: null, error });
}

function galleySigningException(error) {
  const declined = error?.name === "DreggUserDeclined" || error?.code === "user-declined" ||
    /\b(?:user\s+)?declin(?:e|ed)\b/iu.test(error instanceof Error ? error.message : "");
  const message = error instanceof GalleyApiRefusal
    ? `${error.code}: ${error.message}`
    : error instanceof Error ? error.message : "Dregg signer returned an unknown error";
  return freeze({ state: declined ? "declined" : "error", turnHash: null, outboxId: null, error: message.slice(0, 320) });
}

function normalizeAction(value, at) {
  const row = exact(at, value, ["action_token", "expires_after_sequence", "kind"]);
  refuse(row.kind === "perform", "galley-action", `${at}.kind has no activated Galley writer`);
  digest(`${at}.action_token`, row.action_token);
  return freeze({
    kind: row.kind,
    actionToken: row.action_token,
    expiresAfterSequence: natural(`${at}.expires_after_sequence`, row.expires_after_sequence),
  });
}

/** Exact read schema emitted by the current Lean Galley runtime. This is a
 * presentation read-model only: no browser transition is derived from it. */
export function normalizeGalleyDailyProjection(value, expectedSequence) {
  const row = exact("projection", value, PROJECTION_KEYS);
  const publicPlayers = digestList("projection.public_players", row.public_players);
  const sponsors = digestList("projection.sponsors", row.sponsors);
  const spentGrantNullifiers = digestList("projection.spent_grant_nullifiers", row.spent_grant_nullifiers);
  const sequence = natural("projection.sequence", row.sequence);
  const publicPlayCount = natural("projection.public_play_count", row.public_play_count);
  const sponsorshipCount = natural("projection.sponsorship_count", row.sponsorship_count);
  refuse(sequence === expectedSequence, "galley-projection", "projection sequence does not bind the journal head");
  refuse(publicPlayCount === publicPlayers.length && sponsorshipCount === sponsors.length,
    "galley-projection", "projection participant counts are incoherent");
  return freeze({
    sequence,
    publicPlayers,
    sponsors,
    spentGrantNullifiers,
    publicPlayCount,
    sponsorshipCount,
    localServiceTotal: natural("projection.local_service_total", row.local_service_total),
    powerRoot: digest("projection.power_root", row.power_root),
    lootRoot: digest("projection.loot_root", row.loot_root),
    canonRoot: digest("projection.canon_root", row.canon_root),
    canonRevision: natural("projection.canon_revision", row.canon_revision),
  });
}

function normalizeReplay(value, sequence, semanticHead) {
  const row = exact("replay", value,
    ["audited", "event_count", "total_event_count", "from_sequence", "head_digest", "through_sequence"]);
  refuse(typeof row.audited === "boolean", "galley-replay", "replay.audited must be boolean");
  const replay = {
    audited: row.audited,
    eventCount: natural("replay.event_count", row.event_count),
    totalEventCount: natural("replay.total_event_count", row.total_event_count),
    fromSequence: natural("replay.from_sequence", row.from_sequence),
    throughSequence: natural("replay.through_sequence", row.through_sequence),
    headDigest: digest("replay.head_digest", row.head_digest),
  };
  refuse(replay.totalEventCount === sequence && replay.headDigest === semanticHead,
    "galley-replay", "replay total or head does not bind the current projection");
  if (replay.totalEventCount === 0) {
    refuse(replay.eventCount === 0 && replay.fromSequence === 0 && replay.throughSequence === 0,
      "galley-replay", "empty replay coordinates are incoherent");
  } else {
    refuse(replay.eventCount > 0 && replay.throughSequence === sequence && replay.fromSequence >= 1 &&
      replay.fromSequence + replay.eventCount - 1 === replay.throughSequence,
    "galley-replay", "replay window does not form the current journal suffix");
  }
  return freeze(replay);
}

function normalizeCurrent(row) {
  const actions = Array.isArray(row.actions) ? row.actions.map(normalizeAction) : null;
  refuse(actions && actions.length <= 128, "galley-actions", "actions must be a bounded array");
  refuse(new Set(actions.map(({ actionToken }) => actionToken)).size === actions.length,
    "galley-actions", "action tokens must be unique");
  return freeze({
    federationId: digest("federation_id", row.federation_id),
    dailyId: opaque("daily_id", row.daily_id),
    aggregateId: opaque("aggregate_id", row.aggregate_id),
    schemaVersion: natural("schema_version", row.schema_version),
    sequence: natural("sequence", row.sequence),
    semanticHead: digest("semantic_head", row.semantic_head),
    projectionDigest: digest("projection_digest", row.projection_digest),
    projection: normalizeGalleyDailyProjection(boundedJson("projection", row.projection), row.sequence),
    actions: Object.freeze(actions),
    replay: normalizeReplay(row.replay, row.sequence, row.semantic_head),
  });
}

export function normalizeGalleySession(value) {
  const row = exact("Galley session", value, SESSION_KEYS);
  refuse(row.format === POA_GALLEY_SESSION_FORMAT, "galley-format", "Galley session format is unsupported");
  return freeze({ format: POA_GALLEY_SESSION_FORMAT, ...normalizeCurrent(row), events: Object.freeze([]) });
}

function normalizeReceipt(value, at) {
  const row = exact(at, value, ["index", "postcard_base64", "sha256"]);
  return freeze({
    index: natural(`${at}.index`, row.index),
    postcardBase64: canonicalBase64(`${at}.postcard_base64`, row.postcard_base64, MAX_POSTCARD_BYTES),
    sha256: digest(`${at}.sha256`, row.sha256),
  });
}

function normalizeEvent(value, at) {
  const row = exact(at, value, ["event_digest", "payload", "payload_digest", "receipt", "receipt_hash", "sequence", "turn_hash"]);
  const payloadRow = exact(`${at}.payload`, boundedJson(`${at}.payload`, row.payload), EVENT_PAYLOAD_KEYS);
  refuse(payloadRow.kind === "public-play", "galley-event", `${at}.payload.kind has no activated Galley writer`);
  const actor = digest(`${at}.payload.actor`, payloadRow.actor);
  const beneficiary = digest(`${at}.payload.beneficiary`, payloadRow.beneficiary);
  refuse(actor === beneficiary, "galley-event", `${at}.payload beneficiary does not match its public actor`);
  return freeze({
    sequence: natural(`${at}.sequence`, row.sequence),
    turnHash: digest(`${at}.turn_hash`, row.turn_hash),
    receiptHash: digest(`${at}.receipt_hash`, row.receipt_hash),
    eventDigest: digest(`${at}.event_digest`, row.event_digest),
    payloadDigest: digest(`${at}.payload_digest`, row.payload_digest),
    payload: freeze({
      kind: payloadRow.kind,
      actor,
      beneficiary,
      activityId: digest(`${at}.payload.activity_id`, payloadRow.activity_id),
      grantNullifier: digest(`${at}.payload.grant_nullifier`, payloadRow.grant_nullifier),
      authorityCommitment: digest(`${at}.payload.authority_commitment`, payloadRow.authority_commitment),
      localService: natural(`${at}.payload.local_service`, payloadRow.local_service),
    }),
    receipt: normalizeReceipt(row.receipt, `${at}.receipt`),
  });
}

export function normalizeGalleyStatus(value) {
  const row = exact("Galley status", value, STATUS_KEYS);
  refuse(row.format === POA_GALLEY_STATUS_FORMAT, "galley-format", "Galley status format is unsupported");
  refuse(Array.isArray(row.events) && row.events.length <= MAX_EVENTS, "galley-events", "events must be a bounded array");
  const current = normalizeCurrent(row);
  const events = Object.freeze(row.events.map((event, index) => normalizeEvent(event, `events[${index}]`)));
  for (let index = 0; index < events.length; index += 1) {
    refuse(events[index].sequence <= current.sequence && (index === 0 || events[index - 1].sequence < events[index].sequence),
      "galley-events", "event sequences must be strictly increasing and within the current projection");
  }
  refuse(current.replay.eventCount === events.length, "galley-replay", "replay count does not match returned events");
  if (events.length > 0) {
    const first = events[0];
    const last = events.at(-1);
    refuse(first.sequence === current.replay.fromSequence && last.sequence === current.replay.throughSequence &&
      last.eventDigest === current.replay.headDigest && last.eventDigest === current.semanticHead,
    "galley-replay", "replay range or head does not bind the returned journal suffix");
  }
  return freeze({ format: POA_GALLEY_STATUS_FORMAT, ...current, events });
}

export function normalizeGalleyUnsignedTurn(value) {
  const row = exact("Galley unsigned turn", value,
    ["expires_after_sequence", "federation_id", "format", "intent_id", "preparation_digest", "turn_postcard_base64"]);
  refuse(row.format === POA_GALLEY_UNSIGNED_TURN_FORMAT, "galley-format", "Galley unsigned turn format is unsupported");
  return freeze({
    format: POA_GALLEY_UNSIGNED_TURN_FORMAT,
    intentId: opaque("intent_id", row.intent_id),
    federationId: digest("federation_id", row.federation_id),
    preparationDigest: digest("preparation_digest", row.preparation_digest),
    turnPostcardBase64: canonicalBase64("turn_postcard_base64", row.turn_postcard_base64, MAX_POSTCARD_BYTES),
    expiresAfterSequence: natural("expires_after_sequence", row.expires_after_sequence),
  });
}

export function galleyActionLabel(kind) {
  return Object.freeze({
    perform: "Take this watch",
  })[kind] ?? "Unknown action";
}

/** Player-facing read projection over exact node fields. It never judges a
 * command or advances state; actions still originate exclusively at the node. */
export function projectGalleyWatch(view, actorPublicKeyHex) {
  const actor = digest("Galley watch actor", actorPublicKeyHex);
  const audited = view.replay.audited;
  const participated = audited && view.projection.publicPlayers.includes(actor);
  const availableActions = audited ? view.actions.filter((action) =>
    action.kind === "perform" && galleyAvailableAtSequence(action.expiresAfterSequence, view.sequence))
    : [];
  refuse(!(participated && availableActions.length > 0), "galley-presentation",
    "a completed actor cannot also receive a public action at this daily head");
  const records = Object.freeze((audited ? view.events : []).map((event) => freeze({
    sequence: event.sequence,
    isPersonal: event.payload.actor === actor,
    actor: event.payload.actor,
    localService: event.payload.localService,
    turnHash: event.turnHash,
    receiptHash: event.receiptHash,
    eventDigest: event.eventDigest,
  })));
  const personalRecords = Object.freeze(records.filter(({ isPersonal }) => isPersonal));
  return freeze({
    state: !audited ? "unavailable" : participated ? "recorded" : availableActions.length > 0 ? "available" : "waiting",
    participated,
    availableActions: Object.freeze(availableActions),
    publicPlayCount: audited ? view.projection.publicPlayCount : null,
    localServiceTotal: audited ? view.projection.localServiceTotal : null,
    records,
    personalRecords,
    nextVisit: !audited
      ? "This watch is unavailable until the node returns an audited replay. No player record or action is claimed."
      : participated
      ? "Your signed shift is recorded for this daily. Return after the watch rotates."
      : availableActions.length > 0
        ? "One station is open at this journal head. Take the watch or return before it expires."
        : "No station is open at this journal head. Refresh after the watch changes.",
  });
}

export function galleyAvailableAtSequence(expiresAfterSequence, currentSequence) {
  return Number.isSafeInteger(expiresAfterSequence) && Number.isSafeInteger(currentSequence) &&
    expiresAfterSequence >= 0 && currentSequence >= 0 && currentSequence <= expiresAfterSequence;
}

export function decodeGalleyPostcard(base64) {
  canonicalBase64("postcard", base64, MAX_POSTCARD_BYTES);
  try {
    const binary = globalThis.atob
      ? globalThis.atob(base64)
      : Buffer.from(base64, "base64").toString("binary");
    return Uint8Array.from(binary, (character) => character.charCodeAt(0));
  } catch {
    throw new GalleyApiRefusal("galley-base64", "postcard could not be decoded");
  }
}

/** Adjacent transport checksum only; this is not canonical Dregg receipt verification. */
export async function checkGalleyReceiptPostcardSha256(event, cryptoImpl = globalThis.crypto) {
  const postcard = decodeGalleyPostcard(event.receipt.postcardBase64);
  refuse(cryptoImpl?.subtle?.digest, "galley-crypto", "SHA-256 is unavailable");
  const hash = new Uint8Array(await cryptoImpl.subtle.digest("SHA-256", postcard));
  const hex = [...hash].map((byte) => byte.toString(16).padStart(2, "0")).join("");
  return hex === event.receipt.sha256;
}

/** Bind the exact unsigned postcard bytes to the server's preparation
 * coordinate before any signer sees them. This is not a turn or receipt hash. */
export async function checkGalleyPreparationPostcardSha256(prepared, cryptoImpl = globalThis.crypto) {
  const postcard = decodeGalleyPostcard(prepared.turnPostcardBase64);
  refuse(cryptoImpl?.subtle?.digest, "galley-crypto", "SHA-256 is unavailable");
  const hash = new Uint8Array(await cryptoImpl.subtle.digest("SHA-256", postcard));
  const hex = [...hash].map((byte) => byte.toString(16).padStart(2, "0")).join("");
  return hex === prepared.preparationDigest;
}

function pendingKey(intent) {
  return JSON.stringify([
    intent.federationId, intent.dailyId, intent.aggregateId, intent.intentId, intent.preparationDigest,
  ]);
}

function normalizePendingIntent(value, at = "pending intent") {
  const row = exact(at, value, [
    "aggregate_id", "daily_id", "expires_after_sequence", "federation_id", "final_turn_hash",
    "intent_id", "preparation_digest", "prepared_at_sequence",
  ]);
  const intent = freeze({
    federationId: digest(`${at}.federation_id`, row.federation_id),
    dailyId: opaque(`${at}.daily_id`, row.daily_id),
    aggregateId: opaque(`${at}.aggregate_id`, row.aggregate_id),
    intentId: opaque(`${at}.intent_id`, row.intent_id),
    preparationDigest: digest(`${at}.preparation_digest`, row.preparation_digest),
    finalTurnHash: row.final_turn_hash === null ? null : digest(`${at}.final_turn_hash`, row.final_turn_hash),
    preparedAtSequence: natural(`${at}.prepared_at_sequence`, row.prepared_at_sequence),
    expiresAfterSequence: natural(`${at}.expires_after_sequence`, row.expires_after_sequence),
  });
  refuse(galleyAvailableAtSequence(intent.expiresAfterSequence, intent.preparedAtSequence),
    "galley-pending", `${at} expires before it was prepared`);
  return intent;
}

function pendingWire(intent) {
  return {
    federation_id: intent.federationId,
    daily_id: intent.dailyId,
    aggregate_id: intent.aggregateId,
    intent_id: intent.intentId,
    preparation_digest: intent.preparationDigest,
    final_turn_hash: intent.finalTurnHash,
    prepared_at_sequence: intent.preparedAtSequence,
    expires_after_sequence: intent.expiresAfterSequence,
  };
}

export function normalizeGalleyPendingJournal(value) {
  const row = exact("pending journal", value, ["entries", "format"]);
  refuse(row.format === POA_GALLEY_PENDING_JOURNAL_FORMAT && Array.isArray(row.entries) && row.entries.length <= 64,
    "galley-pending", "pending journal format or bound is invalid");
  const entries = Object.freeze(row.entries.map((entry, index) => normalizePendingIntent(entry, `entries[${index}]`)));
  refuse(new Set(entries.map(pendingKey)).size === entries.length, "galley-pending", "pending intent keys must be unique");
  return freeze({ format: POA_GALLEY_PENDING_JOURNAL_FORMAT, entries });
}

/** Durable local journal of intent coordinates only; never a Galley state twin. */
export function createGalleyPendingIntentJournal({
  storage,
  storageKey = POA_GALLEY_PENDING_STORAGE_KEY,
} = {}) {
  if (storage === undefined) {
    try { storage = globalThis.window?.localStorage ?? null; }
    catch { storage = null; }
  }
  const available = storage && typeof storage.getItem === "function" && typeof storage.setItem === "function";

  function read() {
    if (!available) return [];
    let serialized;
    try { serialized = storage.getItem(storageKey); }
    catch { return []; }
    if (serialized === null) return [];
    try { return [...normalizeGalleyPendingJournal(JSON.parse(serialized)).entries]; }
    catch {
      try { storage.removeItem?.(storageKey); } catch { /* corrupt journal stays unusable */ }
      return [];
    }
  }

  function write(entries) {
    refuse(available, "galley-pending-storage", "durable pending-intent storage is unavailable");
    const bounded = entries.slice(-64);
    const payload = { format: POA_GALLEY_PENDING_JOURNAL_FORMAT, entries: bounded.map(pendingWire) };
    normalizeGalleyPendingJournal(payload);
    try { storage.setItem(storageKey, JSON.stringify(payload)); }
    catch { throw new GalleyApiRefusal("galley-pending-storage", "durable pending-intent write failed"); }
  }

  function record(view, prepared) {
    refuse(prepared.federationId === view.federationId &&
      galleyAvailableAtSequence(prepared.expiresAfterSequence, view.sequence),
    "galley-pending", "prepared intent does not bind this world or sequence");
    const intent = normalizePendingIntent({
      federation_id: view.federationId,
      daily_id: view.dailyId,
      aggregate_id: view.aggregateId,
      intent_id: prepared.intentId,
      preparation_digest: prepared.preparationDigest,
      final_turn_hash: null,
      prepared_at_sequence: view.sequence,
      expires_after_sequence: prepared.expiresAfterSequence,
    });
    const entries = read().filter((candidate) => pendingKey(candidate) !== pendingKey(intent));
    entries.push(intent);
    write(entries);
    return intent;
  }

  function reconcile(status) {
    const entries = read();
    if (!status.replay.audited) {
      const replayRefused = entries.filter((intent) => intent.federationId === status.federationId &&
        intent.dailyId === status.dailyId && intent.aggregateId === status.aggregateId);
      return freeze({
        pending: Object.freeze(entries),
        settled: Object.freeze([]),
        expired: Object.freeze([]),
        replayRefused: Object.freeze(replayRefused),
      });
    }
    const pending = [];
    const settled = [];
    const expired = [];
    for (const intent of entries) {
      const sameWorld = intent.federationId === status.federationId && intent.dailyId === status.dailyId &&
        intent.aggregateId === status.aggregateId;
      if (!sameWorld) pending.push(intent);
      else if (status.replay.audited && intent.finalTurnHash &&
        status.events.some((event) => event.turnHash === intent.finalTurnHash)) settled.push(intent);
      else if (!galleyAvailableAtSequence(intent.expiresAfterSequence, status.sequence)) expired.push(intent);
      else pending.push(intent);
    }
    write(pending);
    return freeze({
      pending: Object.freeze(pending),
      settled: Object.freeze(settled),
      expired: Object.freeze(expired),
      replayRefused: Object.freeze([]),
    });
  }

  function discard(intent) {
    const entries = read().filter((candidate) => pendingKey(candidate) !== pendingKey(intent));
    write(entries);
  }

  function confirm(intent, finalTurnHash) {
    const finalHash = digest("final signed turn hash", finalTurnHash);
    const entries = read();
    const index = entries.findIndex((candidate) => pendingKey(candidate) === pendingKey(intent));
    refuse(index >= 0,
      "galley-pending", "signed intent is absent from the durable journal");
    const confirmed = freeze({ ...entries[index], finalTurnHash: finalHash });
    entries[index] = confirmed;
    write(entries);
    return confirmed;
  }

  function forView(view) {
    return Object.freeze(read().filter((intent) => intent.federationId === view.federationId &&
      intent.dailyId === view.dailyId && intent.aggregateId === view.aggregateId));
  }

  return freeze({ list: () => Object.freeze(read()), forView, record, confirm, discard, reconcile });
}

export function resolveSameOriginGalleyEndpoint(endpoint, origin) {
  const trustedOrigin = new URL(opaque("origin", origin)).origin;
  const resolved = new URL(opaque("endpoint", endpoint), `${trustedOrigin}/`);
  refuse(resolved.origin === trustedOrigin && !resolved.username && !resolved.password,
    "galley-origin", "Galley endpoints must be same-origin");
  return resolved.href;
}

async function jsonRequest(fetchImpl, url, actorPublicKeyHex, { method = "GET", body } = {}) {
  const actorHeaders = galleyActorHeaders(actorPublicKeyHex);
  const response = await fetchImpl(url, {
    method,
    credentials: "same-origin",
    cache: "no-store",
    redirect: "error",
    headers: Object.freeze({ Accept: "application/json", "Content-Type": "application/json", ...actorHeaders }),
    ...(body === undefined ? {} : { body: JSON.stringify(body) }),
  });
  const contentType = response.headers?.get?.("content-type") ?? "";
  if (!response.ok) throw new GalleyApiRefusal("galley-http", `Galley node refused request (${response.status})`, response.status);
  refuse(contentType.toLowerCase().includes("application/json"), "galley-content-type", "Galley node did not return JSON");
  return response.json();
}

/** Exact GET/prepare/sign/status transport shared conceptually with the extension. */
export function createGalleyTransport({
  origin = globalThis.location?.origin,
  endpoints = DEFAULT_GALLEY_ENDPOINTS,
  fetchImpl = globalThis.fetch,
  cryptoImpl = globalThis.crypto,
} = {}) {
  refuse(typeof fetchImpl === "function", "galley-fetch", "fetch implementation is required");
  const urls = freeze({
    session: resolveSameOriginGalleyEndpoint(endpoints.session, origin),
    command: resolveSameOriginGalleyEndpoint(endpoints.command, origin),
    status: resolveSameOriginGalleyEndpoint(endpoints.status, origin),
  });

  async function openSession(actorPublicKeyHex) {
    return normalizeGalleySession(await jsonRequest(fetchImpl, urls.session, actorPublicKeyHex));
  }

  async function openWatch(actorPublicKeyHex) {
    return normalizeGalleyStatus(await jsonRequest(fetchImpl, urls.status, actorPublicKeyHex));
  }

  async function requestCommand(view, actionToken, actorPublicKeyHex) {
    const action = view?.actions?.find((candidate) => candidate.actionToken === actionToken);
    refuse(action, "galley-action", "action token is absent from the current node session");
    refuse(view.replay.audited, "galley-replay", "node has not audited this Galley journal");
    refuse(galleyAvailableAtSequence(action.expiresAfterSequence, view.sequence),
      "galley-action-expired", "server-issued action token expired at this journal sequence");
    const prepared = normalizeGalleyUnsignedTurn(await jsonRequest(fetchImpl, urls.command, actorPublicKeyHex, {
      method: "POST",
      body: Object.freeze({ format: POA_GALLEY_COMMAND_PREPARE_FORMAT, action_token: action.actionToken }),
    }));
    refuse(prepared.federationId === view.federationId, "galley-federation", "prepared turn belongs to another federation");
    refuse(galleyAvailableAtSequence(prepared.expiresAfterSequence, view.sequence),
      "galley-turn-expired", "prepared turn expired at this journal sequence");
    return freeze({ kind: "signing", signingRequest: prepared, view });
  }

  async function sign(signingRequest, provider, currentSequence) {
    refuse(provider && typeof provider.signTurnV3 === "function", "galley-provider", "Dregg turn signer is unavailable");
    refuse(galleyAvailableAtSequence(signingRequest.expiresAfterSequence, currentSequence),
      "galley-turn-expired", "prepared turn expired before signing at this journal sequence");
    try {
      refuse(await checkGalleyPreparationPostcardSha256(signingRequest, cryptoImpl),
        "galley-preparation-digest", "server preparation digest does not match the exact postcard bytes");
      return normalizeGalleySigningResult(await provider.signTurnV3(
        decodeGalleyPostcard(signingRequest.turnPostcardBase64),
        hexBytes(signingRequest.federationId),
      ));
    } catch (error) {
      return galleySigningException(error);
    }
  }

  async function status(signingRequest, actorPublicKeyHex) {
    const view = normalizeGalleyStatus(await jsonRequest(fetchImpl, urls.status, actorPublicKeyHex));
    refuse(view.federationId === signingRequest.federationId &&
      (!signingRequest.dailyId || view.dailyId === signingRequest.dailyId) &&
      (!signingRequest.aggregateId || view.aggregateId === signingRequest.aggregateId),
    "galley-federation", "status belongs to another Galley world or aggregate");
    const expectedTurnHash = signingRequest.finalTurnHash;
    refuse(expectedTurnHash, "galley-final-turn-hash",
      "status reconciliation requires the signer's final turn hash");
    if (!view.replay.audited) {
      return freeze({ state: "replay-refused", event: null, receiptChecksumMatched: false, view });
    }
    const event = view.replay.audited
      ? view.events.find((candidate) => candidate.turnHash === expectedTurnHash) ?? null
      : null;
    if (!event) {
      const state = galleyAvailableAtSequence(signingRequest.expiresAfterSequence, view.sequence) ? "pending" : "expired";
      return freeze({ state, event: null, receiptChecksumMatched: false, view });
    }
    refuse(await checkGalleyReceiptPostcardSha256(event, cryptoImpl), "galley-receipt-checksum",
      "matching receipt postcard failed its adjacent SHA-256 checksum");
    return freeze({ state: "settled", event, receiptChecksumMatched: true, view });
  }

  return freeze({ openSession, openWatch, requestCommand, sign, status, endpoints: urls });
}

/**
 * Path of Angels Galley wire contract.
 *
 * This module is intentionally boring.  It validates the versioned node
 * projections and keeps their game payloads opaque.  The extension may render
 * a compact account of the journal and relay a server-issued action token; it
 * is not allowed to reproduce Galley rules, score an action, or infer a
 * receipt URL.
 */

export const POA_GALLEY_NODE_ORIGIN = "https://node.pathofangels.network";
export const POA_GALLEY_API_PATH = "/api/poa/galley/v1";
export const POA_GALLEY_SESSION_FORMAT = "POA-GALLEY-SESSION-V1";
export const POA_GALLEY_STATUS_FORMAT = "POA-GALLEY-STATUS-V1";
export const POA_GALLEY_COMMAND_PREPARE_FORMAT = "POA-GALLEY-COMMAND-PREPARE-V1";
export const POA_GALLEY_UNSIGNED_TURN_FORMAT = "POA-GALLEY-UNSIGNED-TURN-V1";
export const POA_GALLEY_PENDING_JOURNAL_FORMAT = "POA-GALLEY-PENDING-INTENT-JOURNAL-V1";
export const POA_GALLEY_ACTOR_HEADER = "X-Dregg-Actor";

const HEX32 = /^[0-9a-f]{64}$/;
const OPAQUE_ID = /^[\x21-\x7e]{1,256}$/;
const ACTION_TOKEN = /^[\x21-\x7e]{1,4096}$/;
const BASE64 = /^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$/;
const MAX_OPAQUE_JSON_BYTES = 128 * 1024;
const MAX_OPAQUE_JSON_DEPTH = 16;
const MAX_EVENTS = 4096;
const MAX_POSTCARD_BYTES = 1024 * 1024;

export type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };

export type PoAGalleyActionKind =
  | "public_vote"
  | "perform"
  | "visit_commons"
  | "holder_sponsorship";

export interface PoAGalleyAction {
  kind: PoAGalleyActionKind;
  action_token: string;
  expires_after_sequence: number;
}

export interface PoAGalleyReplaySummary {
  audited: boolean;
  event_count: number;
  total_event_count: number;
  from_sequence: number;
  through_sequence: number;
  head_digest: string;
}

export interface PoAGalleyCurrentView {
  federation_id: string;
  daily_id: string;
  aggregate_id: string;
  schema_version: number;
  sequence: number;
  semantic_head: string;
  projection_digest: string;
  projection: JsonValue;
  actions: readonly PoAGalleyAction[];
  replay: PoAGalleyReplaySummary;
}

export interface PoAGalleySession extends PoAGalleyCurrentView {
  format: typeof POA_GALLEY_SESSION_FORMAT;
}

export interface PoAGalleyReceipt {
  index: number;
  postcard_base64: string;
  sha256: string;
}

export interface PoAGalleyEvent {
  sequence: number;
  turn_hash: string;
  receipt_hash: string;
  event_digest: string;
  payload_digest: string;
  payload: JsonValue;
  receipt: PoAGalleyReceipt;
}

export interface PoAGalleyStatus extends PoAGalleyCurrentView {
  format: typeof POA_GALLEY_STATUS_FORMAT;
  events: readonly PoAGalleyEvent[];
}

export interface PoAGalleyUnsignedTurn {
  format: typeof POA_GALLEY_UNSIGNED_TURN_FORMAT;
  intent_id: string;
  federation_id: string;
  preparation_digest: string;
  turn_postcard_base64: string;
  expires_after_sequence: number;
}

export interface PoAGalleyPendingIntent {
  federation_id: string;
  daily_id: string;
  aggregate_id: string;
  intent_id: string;
  preparation_digest: string;
  turn_hash: string;
  prepared_at_sequence: number;
  expires_after_sequence: number;
}

export interface PoAGalleyPendingJournal {
  format: typeof POA_GALLEY_PENDING_JOURNAL_FORMAT;
  entries: readonly PoAGalleyPendingIntent[];
}

export interface PoAGalleyCommandPrepare {
  format: typeof POA_GALLEY_COMMAND_PREPARE_FORMAT;
  action_token: string;
  holding_receipt_id?: string;
}

export interface PoAGalleyBinding {
  platform: "youtube" | "x";
  contextId: string;
  experienceId: string;
  manifestDigest: string;
}

export type PoAGalleyPortRequest =
  | { op: "status"; binding: PoAGalleyBinding }
  | { op: "command"; binding: PoAGalleyBinding; actionToken: string };

export type PoAGalleyPortResponse =
  | { ok: true; op: "status"; status: PoAGalleyStatus }
  | {
      ok: true;
      op: "command";
      admission: "submitted" | "queued";
      observation: "receipt_observed" | "not_observed";
      turnHash: string;
      event?: PoAGalleyEvent;
      status?: PoAGalleyStatus;
      error?: string;
    }
  | { ok: false; op: "status" | "command"; error: string };

function object(value: unknown): Record<string, unknown> | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null ? value as Record<string, unknown> : null;
}

function exact(value: Record<string, unknown>, keys: readonly string[]): boolean {
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  return actual.length === expected.length && actual.every((key, index) => key === expected[index]);
}

function safeNatural(value: unknown): value is number {
  return Number.isSafeInteger(value) && (value as number) >= 0;
}

function opaqueId(value: unknown): value is string {
  return typeof value === "string" && OPAQUE_ID.test(value);
}

function hex32(value: unknown): value is string {
  return typeof value === "string" && HEX32.test(value);
}

export function parsePoAGalleyBinding(value: unknown): PoAGalleyBinding | null {
  const row = object(value);
  if (!row || !exact(row, ["platform", "contextId", "experienceId", "manifestDigest"])) return null;
  if ((row.platform !== "youtube" && row.platform !== "x") || !opaqueId(row.contextId) ||
      !opaqueId(row.experienceId) || !hex32(row.manifestDigest)) return null;
  return Object.freeze({
    platform: row.platform,
    contextId: row.contextId,
    experienceId: row.experienceId,
    manifestDigest: row.manifestDigest,
  });
}

export function poAGalleyAvailableAtSequence(expiresAfterSequence: number, currentSequence: number): boolean {
  return safeNatural(expiresAfterSequence) && safeNatural(currentSequence) && currentSequence <= expiresAfterSequence;
}

/** A public, non-authoritative personalization claim owned by the background.
 * Exact turn signatures and finalized receipts remain the authority. */
export function poAGalleyActorHeaders(publicKeyHex: unknown): Readonly<Record<typeof POA_GALLEY_ACTOR_HEADER, string>> | null {
  if (!hex32(publicKeyHex)) return null;
  return Object.freeze({ [POA_GALLEY_ACTOR_HEADER]: publicKeyHex });
}

function canonicalBase64(value: unknown, maxBytes: number): value is string {
  if (typeof value !== "string" || value.length === 0 || value.length > Math.ceil(maxBytes / 3) * 4 || !BASE64.test(value)) return false;
  const padding = value.endsWith("==") ? 2 : value.endsWith("=") ? 1 : 0;
  return (value.length / 4) * 3 - padding <= maxBytes;
}

function jsonValue(value: unknown, depth = 0): value is JsonValue {
  if (depth > MAX_OPAQUE_JSON_DEPTH) return false;
  if (value === null || typeof value === "boolean" || typeof value === "string") return true;
  if (typeof value === "number") return Number.isFinite(value);
  if (Array.isArray(value)) return value.length <= 4096 && value.every((item) => jsonValue(item, depth + 1));
  const record = object(value);
  if (!record || Object.keys(record).length > 4096) return false;
  return Object.values(record).every((item) => jsonValue(item, depth + 1));
}

function boundedJson(value: unknown): value is JsonValue {
  if (!jsonValue(value)) return false;
  try {
    return new TextEncoder().encode(JSON.stringify(value)).byteLength <= MAX_OPAQUE_JSON_BYTES;
  } catch {
    return false;
  }
}

function action(value: unknown): PoAGalleyAction | null {
  const row = object(value);
  if (!row || !exact(row, ["kind", "action_token", "expires_after_sequence"])) return null;
  if (row.kind !== "public_vote" && row.kind !== "perform" && row.kind !== "visit_commons" && row.kind !== "holder_sponsorship") return null;
  if (typeof row.action_token !== "string" || !ACTION_TOKEN.test(row.action_token) || !safeNatural(row.expires_after_sequence)) return null;
  return Object.freeze({ kind: row.kind, action_token: row.action_token, expires_after_sequence: row.expires_after_sequence });
}

function replay(value: unknown, sequence: number, semanticHead: string): PoAGalleyReplaySummary | null {
  const row = object(value);
  if (!row || !exact(row, ["audited", "event_count", "total_event_count", "from_sequence", "through_sequence", "head_digest"]) ||
      typeof row.audited !== "boolean" || !safeNatural(row.event_count) || !safeNatural(row.from_sequence) ||
      !safeNatural(row.total_event_count) || !safeNatural(row.through_sequence) || !hex32(row.head_digest) ||
      row.total_event_count !== sequence || row.head_digest !== semanticHead) return null;
  if (row.total_event_count === 0) {
    if (row.event_count !== 0 || row.from_sequence !== 0 || row.through_sequence !== 0) return null;
  } else if (row.event_count === 0 || row.through_sequence !== sequence || row.from_sequence < 1 ||
      row.from_sequence + row.event_count - 1 !== row.through_sequence) return null;
  return Object.freeze({
    audited: row.audited,
    event_count: row.event_count,
    total_event_count: row.total_event_count,
    from_sequence: row.from_sequence,
    through_sequence: row.through_sequence,
    head_digest: row.head_digest,
  });
}

function current(value: Record<string, unknown>): PoAGalleyCurrentView | null {
  if (!hex32(value.federation_id) || !opaqueId(value.daily_id) || !opaqueId(value.aggregate_id)) return null;
  if (!safeNatural(value.schema_version) || !safeNatural(value.sequence) || !hex32(value.semantic_head) || !hex32(value.projection_digest)) return null;
  if (!boundedJson(value.projection) || !Array.isArray(value.actions) || value.actions.length > 128) return null;
  const actions = value.actions.map(action);
  if (actions.some((item) => item === null)) return null;
  const tokens = new Set(actions.map((item) => item!.action_token));
  if (tokens.size !== actions.length) return null;
  const replayValue = replay(value.replay, value.sequence, value.semantic_head);
  if (!replayValue) return null;
  return Object.freeze({
    federation_id: value.federation_id,
    daily_id: value.daily_id,
    aggregate_id: value.aggregate_id,
    schema_version: value.schema_version,
    sequence: value.sequence,
    semantic_head: value.semantic_head,
    projection_digest: value.projection_digest,
    // Opaque by design. The browser renders no score or resource from it.
    projection: value.projection,
    actions: Object.freeze(actions as PoAGalleyAction[]),
    replay: replayValue,
  });
}

export function parsePoAGalleySession(value: unknown): PoAGalleySession | null {
  const row = object(value);
  if (!row || !exact(row, ["format", "federation_id", "daily_id", "aggregate_id", "schema_version", "sequence", "semantic_head", "projection_digest", "projection", "actions", "replay"])) return null;
  if (row.format !== POA_GALLEY_SESSION_FORMAT) return null;
  const view = current(row);
  return view ? Object.freeze({ format: POA_GALLEY_SESSION_FORMAT, ...view }) : null;
}

function receipt(value: unknown): PoAGalleyReceipt | null {
  const row = object(value);
  if (!row || !exact(row, ["index", "postcard_base64", "sha256"])) return null;
  if (!safeNatural(row.index) || !canonicalBase64(row.postcard_base64, MAX_POSTCARD_BYTES) || !hex32(row.sha256)) return null;
  return Object.freeze({ index: row.index, postcard_base64: row.postcard_base64, sha256: row.sha256 });
}

function event(value: unknown): PoAGalleyEvent | null {
  const row = object(value);
  if (!row || !exact(row, ["sequence", "turn_hash", "receipt_hash", "event_digest", "payload_digest", "payload", "receipt"])) return null;
  const receiptValue = receipt(row.receipt);
  if (!safeNatural(row.sequence) || !hex32(row.turn_hash) || !hex32(row.receipt_hash) || !hex32(row.event_digest) || !hex32(row.payload_digest) || !boundedJson(row.payload) || !receiptValue) return null;
  return Object.freeze({
    sequence: row.sequence,
    turn_hash: row.turn_hash,
    receipt_hash: row.receipt_hash,
    event_digest: row.event_digest,
    payload_digest: row.payload_digest,
    payload: row.payload,
    receipt: receiptValue,
  });
}

export function parsePoAGalleyStatus(value: unknown): PoAGalleyStatus | null {
  const row = object(value);
  if (!row || !exact(row, ["format", "federation_id", "daily_id", "aggregate_id", "schema_version", "sequence", "semantic_head", "projection_digest", "projection", "actions", "replay", "events"])) return null;
  if (row.format !== POA_GALLEY_STATUS_FORMAT || !Array.isArray(row.events) || row.events.length > MAX_EVENTS) return null;
  const view = current(row);
  const events = row.events.map(event);
  if (!view || events.some((item) => item === null)) return null;
  for (let index = 0; index < events.length; index += 1) {
    const item = events[index]!;
    if (item!.sequence > view.sequence || (index > 0 && events[index - 1]!.sequence >= item.sequence)) return null;
  }
  if (view.replay.event_count !== events.length) return null;
  if (events.length > 0 && (events[0]!.sequence !== view.replay.from_sequence ||
      events[events.length - 1]!.sequence !== view.replay.through_sequence ||
      events[events.length - 1]!.event_digest !== view.replay.head_digest ||
      events[events.length - 1]!.event_digest !== view.semantic_head)) return null;
  return Object.freeze({ format: POA_GALLEY_STATUS_FORMAT, ...view, events: Object.freeze(events as PoAGalleyEvent[]) });
}

export function parsePoAGalleyUnsignedTurn(value: unknown): PoAGalleyUnsignedTurn | null {
  const row = object(value);
  if (!row || !exact(row, ["format", "intent_id", "federation_id", "preparation_digest", "turn_postcard_base64", "expires_after_sequence"])) return null;
  if (row.format !== POA_GALLEY_UNSIGNED_TURN_FORMAT || !opaqueId(row.intent_id) || !hex32(row.federation_id) || !hex32(row.preparation_digest) || !canonicalBase64(row.turn_postcard_base64, MAX_POSTCARD_BYTES) || !safeNatural(row.expires_after_sequence)) return null;
  return Object.freeze({
    format: POA_GALLEY_UNSIGNED_TURN_FORMAT,
    intent_id: row.intent_id,
    federation_id: row.federation_id,
    preparation_digest: row.preparation_digest,
    turn_postcard_base64: row.turn_postcard_base64,
    expires_after_sequence: row.expires_after_sequence,
  });
}

export function makePoAGalleyPrepare(actionToken: string): PoAGalleyCommandPrepare | null {
  if (!ACTION_TOKEN.test(actionToken)) return null;
  // V1 holder receipts do not bind the active Dregg player identity and MUST
  // NOT be attached here.  Holder sponsorship remains visible but unavailable
  // until the V2 challenge/carrier binds that public key end to end.
  return Object.freeze({ format: POA_GALLEY_COMMAND_PREPARE_FORMAT, action_token: actionToken });
}

export function decodePoAGalleyPostcard(base64: string): Uint8Array<ArrayBuffer> | null {
  if (!canonicalBase64(base64, MAX_POSTCARD_BYTES)) return null;
  try {
    const binary = atob(base64);
    const bytes = new Uint8Array(new ArrayBuffer(binary.length));
    for (let index = 0; index < binary.length; index += 1) bytes[index] = binary.charCodeAt(index);
    return bytes;
  } catch {
    return null;
  }
}

/** Bind the exact unsigned postcard bytes to the preparation intent before
 * custody sees them. The final canonical Turn hash is minted only after the
 * signer replaces `Unchecked` authorization and is deliberately distinct. */
export async function checkPoAGalleyPreparationDigest(prepared: PoAGalleyUnsignedTurn): Promise<boolean> {
  const postcard = decodePoAGalleyPostcard(prepared.turn_postcard_base64);
  if (!postcard) return false;
  try {
    const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", postcard));
    const hex = Array.from(digest, (byte) => byte.toString(16).padStart(2, "0")).join("");
    return hex === prepared.preparation_digest;
  } catch {
    return false;
  }
}

/** Adjacent transport checksum only; this is not canonical Dregg receipt verification. */
export async function checkPoAGalleyReceiptPostcardSha256(event: PoAGalleyEvent): Promise<boolean> {
  const postcard = decodePoAGalleyPostcard(event.receipt.postcard_base64);
  if (!postcard) return false;
  try {
    const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", postcard));
    const hex = Array.from(digest, (byte) => byte.toString(16).padStart(2, "0")).join("");
    return hex === event.receipt.sha256;
  } catch {
    return false;
  }
}

function pendingIntent(value: unknown): PoAGalleyPendingIntent | null {
  const row = object(value);
  if (!row || !exact(row, ["federation_id", "daily_id", "aggregate_id", "intent_id", "preparation_digest", "turn_hash", "prepared_at_sequence", "expires_after_sequence"]) ||
      !hex32(row.federation_id) || !opaqueId(row.daily_id) || !opaqueId(row.aggregate_id) || !opaqueId(row.intent_id) ||
      !hex32(row.preparation_digest) || !hex32(row.turn_hash) || !safeNatural(row.prepared_at_sequence) || !safeNatural(row.expires_after_sequence) ||
      !poAGalleyAvailableAtSequence(row.expires_after_sequence, row.prepared_at_sequence)) return null;
  return Object.freeze({
    federation_id: row.federation_id,
    daily_id: row.daily_id,
    aggregate_id: row.aggregate_id,
    intent_id: row.intent_id,
    preparation_digest: row.preparation_digest,
    turn_hash: row.turn_hash,
    prepared_at_sequence: row.prepared_at_sequence,
    expires_after_sequence: row.expires_after_sequence,
  });
}

export function poAGalleyPendingIntentKey(intent: PoAGalleyPendingIntent): string {
  return JSON.stringify([
    intent.federation_id,
    intent.daily_id,
    intent.aggregate_id,
    intent.intent_id,
    intent.preparation_digest,
    intent.turn_hash,
  ]);
}

export function makePoAGalleyPendingIntent(
  session: PoAGalleyCurrentView,
  prepared: PoAGalleyUnsignedTurn,
  signedTurnHash: string,
): PoAGalleyPendingIntent | null {
  if (prepared.federation_id !== session.federation_id ||
      !hex32(signedTurnHash) ||
      !poAGalleyAvailableAtSequence(prepared.expires_after_sequence, session.sequence)) return null;
  return pendingIntent({
    federation_id: session.federation_id,
    daily_id: session.daily_id,
    aggregate_id: session.aggregate_id,
    intent_id: prepared.intent_id,
    preparation_digest: prepared.preparation_digest,
    turn_hash: signedTurnHash,
    prepared_at_sequence: session.sequence,
    expires_after_sequence: prepared.expires_after_sequence,
  });
}

export function parsePoAGalleyPendingJournal(value: unknown): PoAGalleyPendingJournal | null {
  const row = object(value);
  if (!row || !exact(row, ["format", "entries"]) || row.format !== POA_GALLEY_PENDING_JOURNAL_FORMAT ||
      !Array.isArray(row.entries) || row.entries.length > 64) return null;
  const entries = row.entries.map(pendingIntent);
  if (entries.some((entry) => entry === null)) return null;
  const keys = entries.map((entry) => poAGalleyPendingIntentKey(entry!));
  if (new Set(keys).size !== keys.length) return null;
  return Object.freeze({ format: POA_GALLEY_PENDING_JOURNAL_FORMAT, entries: Object.freeze(entries as PoAGalleyPendingIntent[]) });
}

export function reconcilePoAGalleyPendingIntents(entries: readonly PoAGalleyPendingIntent[], status: PoAGalleyStatus): {
  pending: readonly PoAGalleyPendingIntent[];
  observed: readonly PoAGalleyPendingIntent[];
  expired: readonly PoAGalleyPendingIntent[];
} {
  const pending: PoAGalleyPendingIntent[] = [];
  const observed: PoAGalleyPendingIntent[] = [];
  const expired: PoAGalleyPendingIntent[] = [];
  for (const intent of entries) {
    const sameWorld = intent.federation_id === status.federation_id && intent.daily_id === status.daily_id &&
      intent.aggregate_id === status.aggregate_id;
    if (!sameWorld) pending.push(intent);
    else if (status.events.some((event) => event.turn_hash === intent.turn_hash)) observed.push(intent);
    else if (!poAGalleyAvailableAtSequence(intent.expires_after_sequence, status.sequence)) expired.push(intent);
    else pending.push(intent);
  }
  return Object.freeze({ pending: Object.freeze(pending), observed: Object.freeze(observed), expired: Object.freeze(expired) });
}

export function findPoAGalleyAction(session: PoAGalleyCurrentView, token: string): PoAGalleyAction | null {
  return session.actions.find((item) => item.action_token === token) ?? null;
}

export function findPoAGalleyEvent(status: PoAGalleyStatus, turnHash: string): PoAGalleyEvent | null {
  if (!HEX32.test(turnHash)) return null;
  return status.events.find((item) => item.turn_hash === turnHash) ?? null;
}

export function poAGalleyActionLabel(kind: PoAGalleyActionKind): string {
  switch (kind) {
    case "public_vote": return "Cast public vote";
    case "perform": return "Perform shift action";
    case "visit_commons": return "Visit the Commons";
    case "holder_sponsorship": return "Sponsor as a holder";
  }
}

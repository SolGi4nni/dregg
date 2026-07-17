/**
 * OFFERING-TURN SIGNING — the extension side (rung 2) of the G1 signed-identity
 * ladder (`docs/EXCELLENCE-BACKLOG-2026-07-16.md` §G1).
 *
 * Rung 1 (server-side, `dreggnet-offerings/src/signed.rs`) is the VERIFYING
 * consumer: `OfferingHost::advance_signed` admits a `SignedAction` — an offering
 * move plus the actor's Ed25519 public key, a replay counter, and a signature
 * over the canonical `signing_message`. This module is the SIGNER side, living
 * where the user's secret lives: it builds the byte-identical canonical message
 * for `dregg.signOfferingTurn`, and validates the page-supplied parameters
 * before any confirmation surface or key material is touched.
 *
 * ## THE BYTE CONTRACT (must match `signed.rs::signing_message` exactly)
 *
 * ```text
 * "dregg-offering-turn-v1:" ‖ offering_key ‖ 0x00 ‖ session_id ‖ 0x00
 *   ‖ counter_le(8) ‖ 0x00 ‖ action.turn ‖ 0x00 ‖ action.arg_le(8) ‖ 0x00
 *   ‖ action.text-or-empty
 * ```
 *
 * - `counter` is a **u64**, little-endian, 8 bytes.
 * - `action.arg` is an **i64** (`dreggnet-offerings` `Action.arg`),
 *   two's-complement little-endian, 8 bytes.
 * - String fields are UTF-8. `text` absent encodes as empty (the Rust side is
 *   `action.text.as_deref().unwrap_or("")`).
 * - `label` and `enabled` are deliberately NOT signed (surface decorations the
 *   executor never reads) — same as the Rust builder.
 *
 * The pin test (`test/offering-sign.test.mjs`) carries the SAME hand-built
 * expected-bytes vector as the Rust pin test
 * (`signed.rs::the_canonical_signing_message_is_pinned_byte_for_byte`), so the
 * TS builder and the Rust builder can never drift silently — drift is a red
 * test on whichever side moved.
 *
 * ## Replay safety (who enforces what)
 *
 * Replay safety is enforced SERVER-SIDE by the strictly-increasing counter
 * ledger: the host tracks the last consumed counter per
 * `(offering, session, pubkey)` and refuses a stale one
 * (`SignedError::StaleCounter`). The page supplies the counter (it fetched the
 * next acceptable value from the server); the extension's job is HONEST DISPLAY
 * (the confirm surface shows the exact counter being signed) + CORRECT BYTES
 * (refusing non-integer / negative / >u64 values before anything is signed).
 *
 * ## NUL hardening
 *
 * The canonical message separates variable-length string fields with 0x00, so a
 * string field CONTAINING a NUL byte would make two different
 * `(offeringKey, sessionId, turn, text)` tuples encode to the same bytes — a
 * signature over one would verify as the other, and the confirm surface could
 * not honestly display which tuple is being authorized. The extension therefore
 * refuses NUL bytes in every string field. (Legitimate offering keys, session
 * ids, turn verbs, and text payloads never contain NUL.)
 */

/** The domain tag every offering-turn signature is bound under (ASCII). */
export const OFFERING_TURN_SIGNING_DOMAIN = "dregg-offering-turn-v1:";

export const U64_MAX = (1n << 64n) - 1n;
export const I64_MIN = -(1n << 63n);
export const I64_MAX = (1n << 63n) - 1n;

/**
 * The parameters a page hands `dregg.signOfferingTurn`. `counter` and `arg` may
 * be numbers (must be safe integers) or decimal strings (u64/i64-safe transport
 * for values beyond `Number.MAX_SAFE_INTEGER`); `bigint` is accepted for
 * in-process callers (it does not survive the page→background JSON channel).
 */
export interface OfferingTurnParams {
  /** The offering being moved (e.g. `"dungeon"`). */
  offeringKey: string;
  /** The session the move lands in. */
  sessionId: string;
  /** The replay counter (u64) — supplied by the page from the server's floor. */
  counter: number | string | bigint;
  /** The affordance verb (`Action.turn`, e.g. `"choose"`). */
  turn: string;
  /** The affordance argument (`Action.arg`, an i64). */
  arg: number | string | bigint;
  /** Optional free-text payload (`Action.text`); absent signs as empty. */
  text?: string | null;
}

/** The validated, canonical form every downstream step consumes. */
export interface ParsedOfferingTurn {
  offeringKey: string;
  sessionId: string;
  counter: bigint;
  turn: string;
  arg: bigint;
  /** `null` = no text payload (signs identically to `""`, per the Rust builder). */
  text: string | null;
}

export type ParseResult =
  | { ok: true; params: ParsedOfferingTurn }
  | { ok: false; error: string };

function fail(error: string): { ok: false; error: string } {
  return { ok: false, error };
}

function parseU64(value: unknown, field: string):
  | { ok: true; value: bigint }
  | { ok: false; error: string } {
  let v: bigint;
  if (typeof value === "number") {
    if (!Number.isSafeInteger(value)) {
      return fail(
        `${field} must be an integer within Number.MAX_SAFE_INTEGER — pass larger values as a decimal string`,
      );
    }
    v = BigInt(value);
  } else if (typeof value === "string") {
    if (!/^[0-9]+$/.test(value)) {
      return fail(`${field} string must be a non-negative decimal integer`);
    }
    v = BigInt(value);
  } else if (typeof value === "bigint") {
    v = value;
  } else {
    return fail(`${field} must be a number or a decimal string`);
  }
  if (v < 0n) return fail(`${field} must not be negative`);
  if (v > U64_MAX) return fail(`${field} exceeds u64::MAX`);
  return { ok: true, value: v };
}

function parseI64(value: unknown, field: string):
  | { ok: true; value: bigint }
  | { ok: false; error: string } {
  let v: bigint;
  if (typeof value === "number") {
    if (!Number.isSafeInteger(value)) {
      return fail(
        `${field} must be an integer within Number.MAX_SAFE_INTEGER — pass larger values as a decimal string`,
      );
    }
    v = BigInt(value);
  } else if (typeof value === "string") {
    if (!/^-?[0-9]+$/.test(value)) {
      return fail(`${field} string must be a decimal integer`);
    }
    v = BigInt(value);
  } else if (typeof value === "bigint") {
    v = value;
  } else {
    return fail(`${field} must be a number or a decimal string`);
  }
  if (v < I64_MIN || v > I64_MAX) return fail(`${field} is out of i64 range`);
  return { ok: true, value: v };
}

function parseStringField(
  value: unknown,
  field: string,
  opts: { allowEmpty: boolean },
): { ok: true; value: string } | { ok: false; error: string } {
  if (typeof value !== "string") return fail(`${field} must be a string`);
  if (!opts.allowEmpty && value.length === 0) return fail(`${field} must not be empty`);
  if (value.includes("\u0000")) {
    return fail(`${field} must not contain NUL bytes (0x00 is the canonical field separator)`);
  }
  return { ok: true, value };
}

/**
 * Validate raw `signOfferingTurn` parameters into the canonical parsed form.
 * Fail-closed: any missing/mistyped/out-of-range field is a named error and
 * NOTHING downstream (confirm surface, key material) is reached. Called on
 * BOTH sides of the page→background channel — the page for a fast typed
 * `TypeError`, the background independently (never trust page-side validation
 * alone).
 */
export function parseOfferingTurnParams(input: unknown): ParseResult {
  if (input === null || typeof input !== "object") {
    return fail("params must be an object");
  }
  const p = input as Record<string, unknown>;

  const offeringKey = parseStringField(p.offeringKey, "offeringKey", { allowEmpty: false });
  if (!offeringKey.ok) return offeringKey;
  const sessionId = parseStringField(p.sessionId, "sessionId", { allowEmpty: false });
  if (!sessionId.ok) return sessionId;
  const turn = parseStringField(p.turn, "turn", { allowEmpty: false });
  if (!turn.ok) return turn;
  const counter = parseU64(p.counter, "counter");
  if (!counter.ok) return counter;
  const arg = parseI64(p.arg, "arg");
  if (!arg.ok) return arg;

  let text: string | null = null;
  if (p.text !== undefined && p.text !== null) {
    const t = parseStringField(p.text, "text", { allowEmpty: true });
    if (!t.ok) return t;
    text = t.value;
  }

  return {
    ok: true,
    params: {
      offeringKey: offeringKey.value,
      sessionId: sessionId.value,
      counter: counter.value,
      turn: turn.value,
      arg: arg.value,
      text,
    },
  };
}

/** 8 little-endian bytes of a u64 (caller guarantees `0 <= v <= U64_MAX`). */
function u64Le(v: bigint): Uint8Array {
  const out = new Uint8Array(8);
  let x = v;
  for (let i = 0; i < 8; i++) {
    out[i] = Number(x & 0xffn);
    x >>= 8n;
  }
  return out;
}

/** 8 little-endian two's-complement bytes of an i64. */
function i64Le(v: bigint): Uint8Array {
  return u64Le(BigInt.asUintN(64, v));
}

/**
 * **The canonical signing message** — the exact bytes
 * `dreggnet-offerings/src/signed.rs::signing_message` builds and
 * `verify_signed` verifies. Validates its input (throws `TypeError` with the
 * same message `parseOfferingTurnParams` reports), then lays out:
 *
 * ```text
 * "dregg-offering-turn-v1:" ‖ offeringKey ‖ 0x00 ‖ sessionId ‖ 0x00
 *   ‖ counter_le(8) ‖ 0x00 ‖ turn ‖ 0x00 ‖ arg_le(8) ‖ 0x00 ‖ text-or-empty
 * ```
 *
 * A `ParsedOfferingTurn` is itself a valid `OfferingTurnParams` (bigint
 * counter/arg), so the background hands the already-validated form straight in.
 */
export function signingMessage(params: OfferingTurnParams): Uint8Array {
  const parsed = parseOfferingTurnParams(params);
  if (!parsed.ok) throw new TypeError(parsed.error);
  const p = parsed.params;

  const enc = new TextEncoder();
  const parts: Uint8Array[] = [
    enc.encode(OFFERING_TURN_SIGNING_DOMAIN),
    enc.encode(p.offeringKey),
    Uint8Array.of(0),
    enc.encode(p.sessionId),
    Uint8Array.of(0),
    u64Le(p.counter),
    Uint8Array.of(0),
    enc.encode(p.turn),
    Uint8Array.of(0),
    i64Le(p.arg),
    Uint8Array.of(0),
    enc.encode(p.text ?? ""),
  ];

  const total = parts.reduce((n, a) => n + a.length, 0);
  const out = new Uint8Array(total);
  let offset = 0;
  for (const part of parts) {
    out.set(part, offset);
    offset += part.length;
  }
  return out;
}

/** Lowercase hex of a byte array (the wire encoding for keys and signatures). */
export function bytesToHex(bytes: Uint8Array | number[]): string {
  const arr = bytes instanceof Uint8Array ? bytes : Uint8Array.from(bytes);
  let hex = "";
  for (let i = 0; i < arr.length; i++) {
    hex += arr[i].toString(16).padStart(2, "0");
  }
  return hex;
}

/**
 * The JSON-safe wire form of a validated counter: a plain number while it fits
 * a safe integer, else its decimal-string form (a raw JSON number above
 * 2^53 - 1 would silently lose precision in JS).
 */
export function counterWire(counter: bigint): number | string {
  return counter <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(counter) : counter.toString();
}

// ---------------------------------------------------------------------------
// The result wire (background → page).
// ---------------------------------------------------------------------------

/**
 * Why a `signOfferingTurn` request was REFUSED — typed so a page can
 * distinguish the user declining the confirm surface (`user-declined`) from a
 * parameter problem (`invalid-params`), locked custody (`custody-locked`), and
 * an actual signing failure (`sign-failed` / `wasm-unavailable`). The
 * origin-not-granted case never reaches this enum: it is the standard
 * restricted-method denial raised by the content script before dispatch.
 */
export type OfferingSignErrorCode =
  | "invalid-params"
  | "custody-locked"
  | "user-declined"
  | "sign-failed"
  | "wasm-unavailable";

/**
 * The signed result — the `SignedAction` wire, hex-encoded for JSON transport.
 * The webapp assembles the server payload for the (follow-up) `act-signed`
 * route from this plus the action fields it already holds; the server verifies
 * the signature over the SAME canonical message (`verify_signed`) and refuses
 * stale counters.
 */
export interface SignedOfferingTurnWire {
  ok: true;
  /** The signer's Ed25519 public key — lowercase hex, 64 chars (the verified `DreggIdentity`). */
  actorPubkeyHex: string;
  /** The counter that was signed (number while ≤ 2^53 - 1, else decimal string). */
  counter: number | string;
  /** The 64-byte Ed25519 signature over the canonical message — lowercase hex, 128 chars. */
  signatureHex: string;
}

export interface OfferingSignFailure {
  ok: false;
  code: OfferingSignErrorCode;
  error: string;
}

export type OfferingSignResult = SignedOfferingTurnWire | OfferingSignFailure;

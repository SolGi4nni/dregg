/**
 * JUDGED SIGNAL SESSION SIGNING — the scoped, schema-pinned player-key signer.
 *
 * The verifying half is `node/src/poa_signal_session.rs`: a judged Signal
 * session spends a per-player budget against a live slot secret, so `open` and
 * `guess` each carry an Ed25519 signature by the PLAYER key over a canonical
 * statement, on top of the node's bearer layer. This module is the signer half,
 * living where the player's secret lives.
 *
 * # ⚑ WHY THIS IS NOT `signMessage`
 *
 * The obvious way to unblock a browser that needs one Ed25519 signature is to
 * expose `signMessage(bytes)`. That is a **signing oracle**: a page that can ask
 * for a signature over caller-chosen bytes can ask for a signature over a
 * transfer, a capability grant, or anything else the identity key authorizes.
 *
 * So this path **takes no bytes at all**. It takes STRUCTURED FIELDS, and
 * re-derives the canonical statement here — the same rule the node applies to
 * itself (`verify_player_signature`: "the message is RE-DERIVED here from the
 * structured request fields; it is never accepted pre-encoded"). The signable
 * IMAGE of this method is therefore exactly the two templates below, over the
 * caller's choice of `(authorityId, slot, round, guess)` — and nothing else is
 * reachable, for any input, ever.
 *
 * # THE TWO STATEMENTS (pinned against `poa_signal_session.rs`)
 *
 * ```text
 * open:  {"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1","authority_id":"<hex32>","slot":<n>,"player_key":"<hex32>"}
 * guess: {"schema":"POA-SIGNAL-SESSION-GUESS-STATEMENT-1","authority_id":"<hex32>","slot":<n>,"player_key":"<hex32>","round":<n>,"guess":{"low":n,"mid":n,"high":n}}
 * ```
 *
 * Compact, key-ordered JSON in EXACTLY that order. Never `JSON.stringify` of
 * anything that arrived: re-serialising a received object signs whatever order
 * and whatever extra keys the sender chose. The Rust pin is
 * `the_signed_statements_are_the_documented_encodings`; the TS pin is
 * `test/signal-session.test.mjs`, carrying the same hand-built vector, so drift
 * is a red test on whichever side moved.
 *
 * # ⚑ THE PLAYER KEY IS NOT A PARAMETER
 *
 * `player_key` is inside both statements, and it is supplied by CUSTODY, never
 * by the page. A page-chosen player key would let a page ask for a statement
 * whose subject is someone else — useless (the signature would not verify under
 * that key) but a lie in the consent surface, which would display a subject the
 * signature does not have. Here the statement's subject is structurally the
 * signer: [`signalSessionStatement`] takes the key as a separate argument that
 * only the background can supply.
 *
 * # ⚑ DOMAIN SEPARATION — why a session signature cannot be anything else
 *
 * Three independent separations, in increasing strength:
 *
 * 1. **The image is two templates.** No input to this path produces bytes
 *    outside them; there is no byte parameter to smuggle a preimage through.
 * 2. **The prefix.** Every statement begins with the ASCII byte `{` followed by
 *    `"schema":"POA-SIGNAL-SESSION-`. Every other Ed25519 preimage in this
 *    system begins with an ASCII domain tag that is not `{`
 *    (`dregg-offering-turn-v1:`, `dregg-sovereign-witness-v1:` / `-v2:`), or
 *    with EIP-191's `0x19`.
 * 3. **The length.** ⚑ THE DECISIVE ONE. A v3 turn's action authorization is
 *    Ed25519 over a **32-byte** blake3 digest —
 *    `TurnExecutor::compute_signing_message` returns `[u8; 32]` and
 *    `authorize.rs` calls `verify_strict(&message, &signature)` on exactly those
 *    32 bytes. Ed25519 is PureEdDSA: it signs the WHOLE message, so a signature
 *    verifies against one byte string and no other. Every statement this module
 *    can build is at least [`MIN_STATEMENT_BYTES`] long — the two 64-character
 *    hex fields alone exceed 32 bytes — so **no output of this path is ever a
 *    valid action authorization for any turn, transfer or capability**, and no
 *    32-byte turn preimage is in the image of this path.
 *
 * `test/signal-session.test.mjs` asserts all three as poles, including a
 * transfer-shaped and an arbitrary-bytes request being REFUSED.
 */

/** Schema tag of the statement a player signs to open a session. */
export const SIGNAL_SESSION_OPEN_SCHEMA = "POA-SIGNAL-SESSION-OPEN-STATEMENT-1" as const;

/** Schema tag of the statement a player signs to spend one burst. */
export const SIGNAL_SESSION_GUESS_SCHEMA = "POA-SIGNAL-SESSION-GUESS-STATEMENT-1" as const;

/**
 * ⚑ THE ALLOWLIST, and it is the whole security surface of this module.
 *
 * A `kind` is a key of this map and nothing else; the schema tag is a FUNCTION
 * of the kind, so no page ever names a schema. Adding a kind here adds a
 * template to what this key will sign, which is exactly the review that should
 * be hard to do by accident.
 */
export const SIGNAL_SESSION_SCHEMAS = Object.freeze({
  open: SIGNAL_SESSION_OPEN_SCHEMA,
  guess: SIGNAL_SESSION_GUESS_SCHEMA,
} as const);

export type SignalSessionKind = keyof typeof SIGNAL_SESSION_SCHEMAS;

/** The kinds, as an array, in the order they occur in a run. */
export const SIGNAL_SESSION_KINDS: readonly SignalSessionKind[] = Object.freeze([
  "open",
  "guess",
] as const);

/** A band is `0..=5`; the node refuses a wrapped one rather than reducing it. */
export const SIGNAL_BAND_MAX = 5;

/** `round` rides in the statement as a `u32` (`PoaSignalSessionGuessRequestV1.round`). */
export const U32_MAX = 0xffff_ffff;

/** `slot` rides in the statement as a `u64` (`PoaInstalledSlotV1::slot`). */
export const U64_MAX = (1n << 64n) - 1n;

/**
 * The shortest statement this module can produce, in bytes.
 *
 * The `open` template with `slot: 0`. It is a LOWER BOUND on every output and
 * the reason no output can be a 32-byte action-authorization preimage; the test
 * computes it independently and pins it.
 */
export const MIN_STATEMENT_BYTES = (
  `{"schema":"${SIGNAL_SESSION_OPEN_SCHEMA}","authority_id":"${"0".repeat(64)}",` +
  `"slot":0,"player_key":"${"0".repeat(64)}"}`
).length;

const HEX_32 = /^[0-9a-f]{64}$/;

/** One three-band Signal code, as it appears in the guess statement. */
export interface SignalSessionGuessCode {
  low: number;
  mid: number;
  high: number;
}

/**
 * What a PAGE may ask for. Deliberately does NOT include `playerKey` (custody
 * supplies it) and deliberately does NOT include `schema` (the kind does).
 */
export interface SignalSessionRequest {
  kind: SignalSessionKind;
  /** The Signal authority, 64 lowercase hex. */
  authorityId: string;
  /** The installed slot this session is played against (u64). */
  slot: number | string | bigint;
  /** `guess` only: bursts ALREADY spent — the 0-based index of this guess (u32). */
  round?: number | string;
  /** `guess` only: the three-band code being spent. */
  guess?: SignalSessionGuessCode;
}

/** The validated canonical form. `round`/`guess` are present iff `kind` is `guess`. */
export interface ParsedSignalSessionRequest {
  kind: SignalSessionKind;
  authorityId: string;
  slot: bigint;
  round: number | null;
  guess: Readonly<SignalSessionGuessCode> | null;
}

export type SignalSessionParseResult =
  | { ok: true; request: ParsedSignalSessionRequest }
  | { ok: false; error: string };

function fail(error: string): { ok: false; error: string } {
  return { ok: false, error };
}

function plainObject(value: unknown): Record<string, unknown> | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null ? (value as Record<string, unknown>) : null;
}

/**
 * Exact key sets, not "at least these". This is what refuses a smuggled
 * `message` / `bytes` / `statement` / `turnBytes` field: an unknown key is a
 * named refusal rather than an ignored extra, so a caller can never believe it
 * handed this path a preimage and be quietly given a session statement instead.
 */
function exactKeys(row: Record<string, unknown>, expected: readonly string[], at: string):
  | { ok: true }
  | { ok: false; error: string } {
  const actual = Object.keys(row).sort();
  const wanted = [...expected].sort();
  if (actual.length !== wanted.length || actual.some((key, index) => key !== wanted[index])) {
    return fail(`${at} must contain exactly ${wanted.join(", ")} — got ${actual.join(", ") || "nothing"}`);
  }
  return { ok: true };
}

function parseU64(value: unknown, field: string): { ok: true; value: bigint } | { ok: false; error: string } {
  let v: bigint;
  if (typeof value === "number") {
    if (!Number.isSafeInteger(value)) {
      return fail(`${field} must be an integer within Number.MAX_SAFE_INTEGER — pass larger values as a decimal string`);
    }
    v = BigInt(value);
  } else if (typeof value === "string") {
    // No leading zeros, no sign, no whitespace: the statement writes this back
    // as a bare JSON number, so two spellings of one value would be two
    // different signed statements for the same slot.
    if (!/^(0|[1-9][0-9]*)$/.test(value)) {
      return fail(`${field} string must be a canonical non-negative decimal integer`);
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

function parseU32(value: unknown, field: string): { ok: true; value: number } | { ok: false; error: string } {
  let v: number;
  if (typeof value === "number") {
    v = value;
  } else if (typeof value === "string") {
    if (!/^(0|[1-9][0-9]*)$/.test(value)) {
      return fail(`${field} string must be a canonical non-negative decimal integer`);
    }
    v = Number(value);
  } else {
    return fail(`${field} must be a number or a decimal string`);
  }
  if (!Number.isSafeInteger(v) || v < 0 || v > U32_MAX) {
    return fail(`${field} must be an integer from 0 through ${U32_MAX}`);
  }
  return { ok: true, value: v };
}

function parseBand(value: unknown, field: string): { ok: true; value: number } | { ok: false; error: string } {
  if (!Number.isSafeInteger(value) || (value as number) < 0 || (value as number) > SIGNAL_BAND_MAX) {
    return fail(`${field} must be an integer band from 0 through ${SIGNAL_BAND_MAX}`);
  }
  return { ok: true, value: value as number };
}

/**
 * Validate a raw `signSignalSession` request into the canonical parsed form.
 *
 * Fail-closed: any unknown kind, unknown key, mistyped or out-of-range field is
 * a named error and NOTHING downstream (consent surface, key material) is
 * reached. Called on BOTH sides of the page→background channel — the page for a
 * fast typed `TypeError`, the background independently, because page-side
 * validation is never the check that matters.
 */
export function parseSignalSessionRequest(input: unknown): SignalSessionParseResult {
  const row = plainObject(input);
  if (!row) return fail("params must be an object");

  const kind = row.kind;
  if (typeof kind !== "string" || !Object.prototype.hasOwnProperty.call(SIGNAL_SESSION_SCHEMAS, kind)) {
    return fail(
      `kind must be one of ${SIGNAL_SESSION_KINDS.join(", ")} — this signer produces judged Signal session ` +
        "statements and nothing else, so an unlisted kind has no statement to build",
    );
  }
  const sessionKind = kind as SignalSessionKind;

  const shape = sessionKind === "open"
    ? ["kind", "authorityId", "slot"]
    : ["kind", "authorityId", "slot", "round", "guess"];
  const keys = exactKeys(row, shape, `a ${sessionKind} request`);
  if (!keys.ok) return keys;

  if (typeof row.authorityId !== "string" || !HEX_32.test(row.authorityId)) {
    return fail("authorityId must be exactly 64 lowercase hexadecimal digits");
  }
  const slot = parseU64(row.slot, "slot");
  if (!slot.ok) return slot;

  if (sessionKind === "open") {
    return {
      ok: true,
      request: Object.freeze({
        kind: sessionKind,
        authorityId: row.authorityId,
        slot: slot.value,
        round: null,
        guess: null,
      }),
    };
  }

  const round = parseU32(row.round, "round");
  if (!round.ok) return round;
  const guessRow = plainObject(row.guess);
  if (!guessRow) return fail("guess must be an object");
  const guessKeys = exactKeys(guessRow, ["low", "mid", "high"], "guess");
  if (!guessKeys.ok) return guessKeys;
  const low = parseBand(guessRow.low, "guess.low");
  if (!low.ok) return low;
  const mid = parseBand(guessRow.mid, "guess.mid");
  if (!mid.ok) return mid;
  const high = parseBand(guessRow.high, "guess.high");
  if (!high.ok) return high;

  return {
    ok: true,
    request: Object.freeze({
      kind: sessionKind,
      authorityId: row.authorityId,
      slot: slot.value,
      round: round.value,
      guess: Object.freeze({ low: low.value, mid: mid.value, high: high.value }),
    }),
  };
}

/** The statement, its schema tag, and its exact bytes. */
export interface SignalSessionStatement {
  kind: SignalSessionKind;
  schema: (typeof SIGNAL_SESSION_SCHEMAS)[SignalSessionKind];
  /** The exact statement text — what the consent surface shows and what is signed. */
  text: string;
  /** UTF-8 of `text`; the Ed25519 message. */
  bytes: Uint8Array;
}

/**
 * **The canonical statement** — the exact bytes `open_statement_message` /
 * `guess_statement_message` build in `node/src/poa_signal_session.rs` and
 * `verify_player_signature` re-derives before checking a signature.
 *
 * `playerKeyHex` comes from CUSTODY (the unlocked active identity), never from
 * the page — see the module header. A request that did not come out of
 * [`parseSignalSessionRequest`] is re-validated here, so this cannot be called
 * with an unvalidated shape by mistake.
 */
export function signalSessionStatement(
  request: SignalSessionRequest | ParsedSignalSessionRequest,
  playerKeyHex: string,
): SignalSessionStatement {
  const parsed = parseSignalSessionRequest(
    // A `ParsedSignalSessionRequest` carries `round: null, guess: null` on the
    // `open` shape; strip the nulls so the exact-key check sees the page shape.
    normalizeForReparse(request),
  );
  if (!parsed.ok) throw new TypeError(parsed.error);
  if (typeof playerKeyHex !== "string" || !HEX_32.test(playerKeyHex)) {
    throw new TypeError("playerKeyHex must be exactly 64 lowercase hexadecimal digits");
  }
  const r = parsed.request;
  const schema = SIGNAL_SESSION_SCHEMAS[r.kind];
  const head =
    `{"schema":"${schema}","authority_id":"${r.authorityId}",` +
    `"slot":${r.slot.toString()},"player_key":"${playerKeyHex}"`;
  const text = r.kind === "open"
    ? `${head}}`
    : `${head},"round":${r.round},"guess":{"low":${r.guess!.low},"mid":${r.guess!.mid},"high":${r.guess!.high}}}`;
  return Object.freeze({
    kind: r.kind,
    schema,
    text,
    bytes: new TextEncoder().encode(text),
  });
}

function normalizeForReparse(request: SignalSessionRequest | ParsedSignalSessionRequest): unknown {
  const row = plainObject(request);
  if (!row) return request;
  if (row.kind !== "open") return row;
  if (row.round === null && row.guess === null) {
    const { round: _round, guess: _guess, ...rest } = row;
    return rest;
  }
  return row;
}

// ---------------------------------------------------------------------------
// The result wire (background → page).
// ---------------------------------------------------------------------------

/**
 * Why a `signSignalSession` request was REFUSED — typed so a page can
 * distinguish the user declining the consent surface (`user-declined`) from a
 * parameter problem (`invalid-params`), locked custody (`custody-locked`), and
 * a signing failure (`sign-failed` / `wasm-unavailable`).
 */
export type SignalSessionSignErrorCode =
  | "invalid-params"
  | "custody-locked"
  | "user-declined"
  | "sign-failed"
  | "wasm-unavailable";

/**
 * The signed result. `statement` is returned so the page can compare it against
 * its OWN builder (`poa-web/src/judged-session.js::openStatementMessage`) before
 * POSTing — two independent derivations of the node's encoding, and a mismatch
 * is a refusal on the page rather than a 401 that reads like a node fault.
 */
export interface SignedSignalSessionWire {
  ok: true;
  kind: SignalSessionKind;
  schema: string;
  /** The signer's Ed25519 public key — the statement's `player_key`. */
  playerKeyHex: string;
  /** The exact statement that was signed. */
  statement: string;
  /** The 64-byte Ed25519 signature — lowercase hex, 128 chars, as the node parses it. */
  signatureHex: string;
}

export interface SignalSessionSignFailure {
  ok: false;
  code: SignalSessionSignErrorCode;
  error: string;
}

export type SignalSessionSignResult = SignedSignalSessionWire | SignalSessionSignFailure;

/** Lowercase hex of a byte array (the wire encoding the node's `parse_hex32` demands). */
export function bytesToHex(bytes: Uint8Array | number[]): string {
  const arr = bytes instanceof Uint8Array ? bytes : Uint8Array.from(bytes);
  let hex = "";
  for (let i = 0; i < arr.length; i++) hex += arr[i].toString(16).padStart(2, "0");
  return hex;
}

/** The JSON-safe wire form of a validated slot (decimal string past 2^53 - 1). */
export function slotWire(slot: bigint): number | string {
  return slot <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(slot) : slot.toString();
}

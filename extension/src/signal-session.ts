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

// ===========================================================================
// THE SESSION-SCOPED GRANT
// ===========================================================================

/**
 * ⚑ ONE CONSENT FOR ONE JUDGED RUN — and it widens NOTHING.
 *
 * # The failure it fixes
 *
 * A judged run is one `open` plus up to five `guess` signatures. Per-signature
 * consent means **six popups**, each one a modal window the player must find,
 * read and accept, between them and a game. That is not a security posture, it
 * is a reason nobody plays; and a surface that trains a player to click through
 * six identical dialogs has made the seventh — the one that matters — invisible.
 *
 * So the consent granularity moves to the thing the player actually decided:
 * *"play this judged run"*. Once. Never *"sign anything"*.
 *
 * # ⚑ WHAT A GRANT IS, AND — the load-bearing part — WHERE IT SITS
 *
 * A grant is **a decision to skip the popup**, and that is ALL it is. It is
 * consulted between "the request parsed" and "show the consent surface"; it is
 * never on the statement-building path. [`signalSessionStatement`] does not take
 * one, cannot see one, and behaves identically whether one exists or not.
 *
 * That placement is why the module's structural properties survive it, and each
 * survives for a reason you can point at rather than for lack of a counterexample.
 * `test/signal-session.test.mjs` asserts all five UNDER A LIVE GRANT:
 *
 * 1. **No bytes parameter.** A grant is checked against a
 *    [`ParsedSignalSessionRequest`] — the output of
 *    [`parseSignalSessionRequest`], which has already refused every unknown key.
 *    There is no `bytes`/`message`/`statement` input to the grant API either, so
 *    a grant cannot become the smuggling route the direct path refuses.
 * 2. **Exact key sets.** Unchanged, because the grant is downstream of them: a
 *    request that fails `parseSignalSessionRequest` never reaches a grant, and
 *    [`grantCovers`] re-derives from the parsed form rather than re-reading the
 *    page's object.
 * 3. **The frozen two-entry kind allowlist.** A grant's budget is a per-kind
 *    record over [`SIGNAL_SESSION_KINDS`] and is built from it, so it has an
 *    entry for `open` and one for `guess` and cannot acquire a third — there is
 *    no third kind to acquire, and a grant is not a place a schema can be named.
 * 4. **The player key comes from custody.** [`grantCovers`] takes `playerKeyHex`
 *    as a SEPARATE argument, exactly as `signalSessionStatement` does, and
 *    REFUSES if it differs from the key the grant was consented for. A grant
 *    therefore cannot be used to sign under a different identity — including
 *    after a lock/unlock into a different profile, which invalidates it
 *    structurally rather than by a cleanup step somebody has to remember.
 * 5. **The length floor.** [`MIN_STATEMENT_BYTES`] is 219 and a granted
 *    signature is produced by the same `signalSessionStatement`, so the image is
 *    byte-for-byte the image it always was. A 32-byte turn authorization stays
 *    unreachable. (⚠ 219, not the 148 that has been quoted around this: the two
 *    64-character hex fields and the schema tag alone put the `open` template
 *    well past it. The property is the same; the number was wrong.)
 *
 * # THE BOUND, and it is the run's own bound
 *
 * [`SIGNAL_SESSION_GRANT_BUDGET`] is `{ open: 1, guess: 5 }` — the node's
 * `POA_SIGNAL_SESSION_MAX_ROUNDS` is 5, so a grant can never authorize more
 * signatures than one complete judged run, and cannot be spent on a second run
 * even in the same slot. Plus an expiry, because a tab left open overnight is
 * not a player who is still deciding.
 *
 * # ⚠ WHAT A GRANT DOES COST, said plainly
 *
 * A hostile page holding a live grant can spend the run on guesses the player
 * did not choose. That is the real price of not asking six times, and it is
 * bounded exactly: **one judged run, in one slot, for one key.** Nothing on
 * chain moves (settling is a separate hybrid-signed turn, never reachable from
 * here), no other slot is touched, and the next slot opens a fresh budget. The
 * consent surface must therefore say what it is granting — five guesses and an
 * open, this slot, until this time — and not "allow this site to sign".
 *
 * # EXHAUSTION AND EXPIRY ARE FRESH CONSENT
 *
 * There is no renewal verb. [`spendSignalSessionGrant`] returns a NEW frozen
 * grant with one unit gone and, when the last unit goes, a grant that
 * [`grantCovers`] refuses as `grant-exhausted`. The only way to get another is
 * [`createSignalSessionGrant`], which only the consent path calls.
 */

/** ⚠ `POA_SIGNAL_SESSION_MAX_ROUNDS` in `persist/src/poa_signal_session.rs`. */
export const SIGNAL_SESSION_MAX_ROUNDS = 5;

/**
 * The most signatures one consent can ever authorize, per kind.
 *
 * Exactly one judged run: the `open` that starts it and the five bursts that are
 * its whole durable budget. Frozen, and keyed by the same two-entry allowlist as
 * the schemas — a kind with no budget entry is a kind a grant cannot cover.
 */
export const SIGNAL_SESSION_GRANT_BUDGET: Readonly<Record<SignalSessionKind, number>> = Object.freeze({
  open: 1,
  guess: SIGNAL_SESSION_MAX_ROUNDS,
} as const);

/** Fifteen minutes: long enough to think about five guesses, short enough that a
 * forgotten tab is not a standing authorization. */
export const SIGNAL_SESSION_GRANT_TTL_MS = 15 * 60 * 1000;

/** Why a grant did not cover a request. Every one is a NAMED refusal that sends
 * the request back to the consent surface — never a silent widening. */
export type SignalSessionGrantRefusal =
  | "grant-scope-authority"
  | "grant-scope-slot"
  | "grant-scope-player"
  | "grant-scope-origin"
  | "grant-expired"
  | "grant-exhausted";

/**
 * A live grant. Frozen, and every field is part of the scope — there is no
 * "options" bag and no wildcard: `authorityId`, `slot`, `playerKeyHex` and
 * `origin` are all compared for EQUALITY, never for prefix or membership.
 */
export interface SignalSessionGrant {
  /** The Signal authority this run is played on, 64 lowercase hex. */
  readonly authorityId: string;
  /** ⚑ The EXACT installed slot. A grant for slot N is useless at slot N+1. */
  readonly slot: bigint;
  /** The custody key the player consented AS. Compared against custody at spend time. */
  readonly playerKeyHex: string;
  /** The page that asked. A grant is not portable to another origin. */
  readonly origin: string;
  /** Signatures still authorized, per kind. Counts down; never back up. */
  readonly remaining: Readonly<Record<SignalSessionKind, number>>;
  /** `Date.now()` past which this grant covers nothing. */
  readonly expiresAtMs: number;
  /** When the player consented — for the popup that says "granted at …". */
  readonly grantedAtMs: number;
}

export type SignalSessionGrantCheck =
  | { ok: true }
  | { ok: false; code: SignalSessionGrantRefusal; error: string };

function grantFail(code: SignalSessionGrantRefusal, error: string): SignalSessionGrantCheck {
  return { ok: false, code, error };
}

function freezeRemaining(remaining: Record<SignalSessionKind, number>): Readonly<Record<SignalSessionKind, number>> {
  // Built by walking the FROZEN kind list, so the result has exactly the kinds
  // the allowlist has — no more, and never one carried in from a caller's object.
  const out = {} as Record<SignalSessionKind, number>;
  for (const kind of SIGNAL_SESSION_KINDS) out[kind] = remaining[kind];
  return Object.freeze(out);
}

/**
 * Mint a grant. ⚠ Called by the CONSENT PATH ONLY, after the user accepted a
 * surface that named this authority, this slot, this identity and this budget.
 *
 * `playerKeyHex` comes from custody, never from the page — the same rule
 * [`signalSessionStatement`] follows, and for the same reason: a page-chosen
 * subject would make the consent surface display a subject the grant does not
 * have.
 *
 * Throws `TypeError` on a malformed scope rather than minting a loose grant.
 */
export function createSignalSessionGrant(input: {
  authorityId: string;
  slot: number | string | bigint;
  playerKeyHex: string;
  origin: string;
  nowMs?: number;
  ttlMs?: number;
}): SignalSessionGrant {
  if (typeof input?.authorityId !== "string" || !HEX_32.test(input.authorityId)) {
    throw new TypeError("a grant's authorityId must be exactly 64 lowercase hexadecimal digits");
  }
  const slot = parseU64(input.slot, "slot");
  if (!slot.ok) throw new TypeError(slot.error);
  if (typeof input.playerKeyHex !== "string" || !HEX_32.test(input.playerKeyHex)) {
    throw new TypeError("a grant's playerKeyHex must be exactly 64 lowercase hexadecimal digits");
  }
  // An origin is compared for equality, so an empty or non-string one would be a
  // grant that matches an unknown caller. Refuse rather than normalise.
  if (typeof input.origin !== "string" || input.origin.length === 0) {
    throw new TypeError("a grant must name the origin it was consented to, exactly");
  }
  const nowMs = typeof input.nowMs === "number" && Number.isFinite(input.nowMs) ? input.nowMs : Date.now();
  const ttlMs =
    typeof input.ttlMs === "number" && Number.isFinite(input.ttlMs) && input.ttlMs > 0
      ? Math.min(input.ttlMs, SIGNAL_SESSION_GRANT_TTL_MS)
      : SIGNAL_SESSION_GRANT_TTL_MS;
  return Object.freeze({
    authorityId: input.authorityId,
    slot: slot.value,
    playerKeyHex: input.playerKeyHex,
    origin: input.origin,
    remaining: freezeRemaining({ ...SIGNAL_SESSION_GRANT_BUDGET }),
    expiresAtMs: nowMs + ttlMs,
    grantedAtMs: nowMs,
  });
}

/**
 * Does this grant cover this request, for this custody key, right now?
 *
 * ⚑ Pure and total: it reads, it never mutates, and it never throws. A `false`
 * here means "ask the user", which is always a safe answer — the failure
 * direction of this function is a popup, not a signature.
 *
 * `request` must already have passed [`parseSignalSessionRequest`]; pass the
 * parsed form. `playerKeyHex` is supplied by CUSTODY.
 */
export function grantCovers(
  grant: SignalSessionGrant | null | undefined,
  request: ParsedSignalSessionRequest,
  playerKeyHex: string,
  origin: string,
  nowMs: number = Date.now(),
): SignalSessionGrantCheck {
  if (!grant) return grantFail("grant-expired", "no grant is held for this run");
  // Scope, field by field, all equality. Ordered so the most specific mismatch a
  // player would actually hit — a new slot — is named as itself.
  if (grant.authorityId !== request.authorityId) {
    return grantFail(
      "grant-scope-authority",
      `this grant is for authority ${grant.authorityId}, not ${request.authorityId}`,
    );
  }
  if (grant.slot !== request.slot) {
    return grantFail(
      "grant-scope-slot",
      `this grant is for slot ${grant.slot.toString()}; slot ${request.slot.toString()} is a ` +
        "different judged run and needs its own consent",
    );
  }
  if (typeof playerKeyHex !== "string" || grant.playerKeyHex !== playerKeyHex) {
    return grantFail(
      "grant-scope-player",
      "this grant was consented to by a different identity than the one custody holds now",
    );
  }
  if (grant.origin !== origin) {
    return grantFail("grant-scope-origin", `this grant was consented to ${grant.origin}, not ${origin}`);
  }
  if (!(nowMs < grant.expiresAtMs)) {
    return grantFail("grant-expired", "this grant has expired; playing on needs fresh consent");
  }
  // The kind is a key of the FROZEN allowlist (parse guaranteed it), so this
  // lookup cannot reach a kind the budget does not name.
  const left = grant.remaining[request.kind];
  if (!(typeof left === "number" && left > 0)) {
    return grantFail(
      "grant-exhausted",
      `this grant's ${request.kind} allowance is spent; a further signature needs fresh consent`,
    );
  }
  return { ok: true };
}

export type SignalSessionGrantSpend =
  | { ok: true; grant: SignalSessionGrant }
  | { ok: false; code: SignalSessionGrantRefusal; error: string };

/**
 * Spend one unit and return the SUCCESSOR grant. Immutable: the grant handed in
 * is unchanged (it is frozen), so a caller that forgets to store the result
 * gets a repeated popup rather than an unbounded signer — the failure direction
 * is again toward asking.
 */
export function spendSignalSessionGrant(
  grant: SignalSessionGrant | null | undefined,
  request: ParsedSignalSessionRequest,
  playerKeyHex: string,
  origin: string,
  nowMs: number = Date.now(),
): SignalSessionGrantSpend {
  const covered = grantCovers(grant, request, playerKeyHex, origin, nowMs);
  if (!covered.ok) return covered;
  const live = grant as SignalSessionGrant;
  const next = {} as Record<SignalSessionKind, number>;
  for (const kind of SIGNAL_SESSION_KINDS) {
    next[kind] = kind === request.kind ? live.remaining[kind] - 1 : live.remaining[kind];
  }
  return {
    ok: true,
    grant: Object.freeze({
      authorityId: live.authorityId,
      slot: live.slot,
      playerKeyHex: live.playerKeyHex,
      origin: live.origin,
      remaining: freezeRemaining(next),
      expiresAtMs: live.expiresAtMs,
      grantedAtMs: live.grantedAtMs,
    }),
  };
}

/** Human-readable scope, for the consent surface and the audit log. What the
 * player is agreeing to, in the words of the thing they are agreeing to. */
export function describeSignalSessionGrant(grant: SignalSessionGrant): string {
  const guesses = grant.remaining.guess;
  const opens = grant.remaining.open;
  return (
    `judged Signal slot ${grant.slot.toString()} on authority ${grant.authorityId.slice(0, 16)}… — ` +
    `${opens} open + up to ${guesses} guess signature${guesses === 1 ? "" : "s"}, ` +
    `as ${grant.playerKeyHex.slice(0, 16)}…, for ${grant.origin}, ` +
    `until ${new Date(grant.expiresAtMs).toISOString()}`
  );
}

/**
 * The background's grant ledger: at most ONE live grant, replaced rather than
 * accumulated.
 *
 * ⚑ ONE, deliberately. A map of grants keyed by scope is a set of standing
 * authorizations a player cannot see the size of, and "revoke everything" stops
 * being a thing they can reason about. One judged run at a time is also just
 * true of the game: a player has one identity and a slot has one instance per
 * player.
 */
export class SignalSessionGrantBook {
  private grant: SignalSessionGrant | null = null;

  /** Install a freshly consented grant, dropping any predecessor. */
  remember(grant: SignalSessionGrant): void {
    this.grant = grant;
  }

  /** The live grant, or `null` — expiry is applied on READ so a stale one is
   * never handed out even if nothing has swept it. */
  peek(nowMs: number = Date.now()): SignalSessionGrant | null {
    if (this.grant && !(nowMs < this.grant.expiresAtMs)) this.grant = null;
    return this.grant;
  }

  /**
   * Try to cover this request without a popup. `{ ok: true }` means SKIP the
   * consent surface and sign; the unit is already spent, so a failure after this
   * point costs the grant a unit rather than leaving one recoverable — the safe
   * direction, because the alternative is a spend that can be retried silently.
   */
  consume(
    request: ParsedSignalSessionRequest,
    playerKeyHex: string,
    origin: string,
    nowMs: number = Date.now(),
  ): SignalSessionGrantCheck {
    const spent = spendSignalSessionGrant(this.peek(nowMs), request, playerKeyHex, origin, nowMs);
    if (!spent.ok) return spent;
    this.grant = spent.grant;
    return { ok: true };
  }

  /** Drop the grant. ⚠ Custody locking MUST call this; the player-key equality
   * check in [`grantCovers`] already makes a different identity structurally
   * unable to use it, so this is defence in depth rather than the mechanism. */
  clear(): void {
    this.grant = null;
  }
}

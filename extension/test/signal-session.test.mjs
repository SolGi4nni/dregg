// Judged Signal session signing — src/signal-session.ts.
//
// THE NON-NEGOTIABLES, in the order they matter:
//
// 1. THE WIRE PIN. The two canonical statements, byte for byte, built here BY
//    HAND from the same vector as the Rust pin test
//    (node/src/poa_signal_session.rs::the_signed_statements_are_the_documented_encodings)
//    — AND scraped out of that Rust file, so drift on either side is red here.
//    The node RE-DERIVES the statement before verifying, so a drifted builder
//    is not a wrong answer, it is every signature failing.
//
// 2. THE REFUSAL POLES. A page asking this method to sign a transfer-shaped or
//    arbitrary payload is REFUSED — and every pole asserts the mutation is
//    PRESENT before reading the verdict, because a refusal test whose input
//    stopped being hostile is a green light that checks nothing.
//
// 3. DOMAIN SEPARATION, exhibited rather than described: a v3 turn's action
//    authorization is Ed25519 over a 32-BYTE blake3 digest, and no statement
//    this path can build is anywhere near 32 bytes — so no signature obtained
//    here is ever a valid authorization for a transfer, and no turn preimage is
//    in the image of this path.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { createPrivateKey, createPublicKey, sign as edSign, verify as edVerify } from "node:crypto";
import {
  MIN_STATEMENT_BYTES,
  SIGNAL_BAND_MAX,
  SIGNAL_SESSION_GRANT_BUDGET,
  SIGNAL_SESSION_GRANT_TTL_MS,
  SIGNAL_SESSION_GUESS_SCHEMA,
  SIGNAL_SESSION_KINDS,
  SIGNAL_SESSION_MAX_ROUNDS,
  SIGNAL_SESSION_OPEN_SCHEMA,
  SIGNAL_SESSION_SCHEMAS,
  SignalSessionGrantBook,
  U32_MAX,
  U64_MAX,
  bytesToHex,
  createSignalSessionGrant,
  describeSignalSessionGrant,
  grantCovers,
  parseSignalSessionRequest,
  signalSessionStatement,
  slotWire,
  spendSignalSessionGrant,
} from "./.build/signal-session.mjs";

// The Rust pin's vector: AUTHORITY = [0x41; 32], PLAYER = [0x55; 32], slot 9.
const AUTHORITY = "41".repeat(32);
const PLAYER = "55".repeat(32);
// ⚠ `AUTHORITY` and `PLAYER` are all DIGITS, so `.toUpperCase()` on either is a
// NO-OP and a case-rejection pole built on them tests nothing. (It shipped that
// way for one run and this file caught it.) Case poles use these instead.
const MIXED_HEX = "ab".repeat(32);
const MIXED_HEX_UPPER = MIXED_HEX.toUpperCase();

const text = (request, playerKeyHex = PLAYER) => signalSessionStatement(request, playerKeyHex).text;

// ---------------------------------------------------------------------------
// 1. THE WIRE PIN
// ---------------------------------------------------------------------------

test("the open statement is the documented encoding, byte for byte", () => {
  const statement = signalSessionStatement({ kind: "open", authorityId: AUTHORITY, slot: 9 }, PLAYER);
  assert.equal(
    statement.text,
    '{"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1"' +
      ',"authority_id":"4141414141414141414141414141414141414141414141414141414141414141"' +
      ',"slot":9' +
      ',"player_key":"5555555555555555555555555555555555555555555555555555555555555555"}',
  );
  assert.equal(statement.schema, SIGNAL_SESSION_OPEN_SCHEMA);
  assert.equal(statement.kind, "open");
  // The bytes are UTF-8 of the text and nothing else — no BOM, no newline.
  assert.deepEqual(Array.from(statement.bytes), Array.from(new TextEncoder().encode(statement.text)));
});

test("the guess statement is the documented encoding, byte for byte", () => {
  const statement = signalSessionStatement(
    { kind: "guess", authorityId: AUTHORITY, slot: 9, round: 2, guess: { low: 0, mid: 1, high: 5 } },
    PLAYER,
  );
  assert.equal(
    statement.text,
    '{"schema":"POA-SIGNAL-SESSION-GUESS-STATEMENT-1"' +
      ',"authority_id":"4141414141414141414141414141414141414141414141414141414141414141"' +
      ',"slot":9' +
      ',"player_key":"5555555555555555555555555555555555555555555555555555555555555555"' +
      ',"round":2' +
      ',"guess":{"low":0,"mid":1,"high":5}}',
  );
  assert.equal(statement.schema, SIGNAL_SESSION_GUESS_SCHEMA);
});

test("the pin is scraped out of the Rust file, so node-side drift reds here", async () => {
  const rust = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  const anchor = rust.indexOf("fn the_signed_statements_are_the_documented_encodings()");
  assert.ok(anchor > 0, "the Rust pin test moved; re-anchor this scrape");
  const body = rust.slice(anchor, rust.indexOf("\n    }", anchor));

  // Reassemble each `concat!(r#"…"#, …)` literal the Rust test asserts against.
  const literals = [...body.matchAll(/r#"([^]*?)"#/g)].map((m) => m[1]);
  assert.ok(
    literals.length >= 8,
    `expected the two concatenated Rust vectors, scraped ${literals.length} fragments`,
  );
  const joined = literals.join("");
  const openAt = joined.indexOf('{"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1"');
  const guessAt = joined.indexOf('{"schema":"POA-SIGNAL-SESSION-GUESS-STATEMENT-1"');
  assert.ok(openAt === 0 && guessAt > 0, "the scraped Rust vectors are not the two statements");
  const rustOpen = joined.slice(openAt, guessAt);
  const rustGuess = joined.slice(guessAt);

  assert.equal(text({ kind: "open", authorityId: AUTHORITY, slot: 9 }), rustOpen);
  assert.equal(
    text({ kind: "guess", authorityId: AUTHORITY, slot: 9, round: 2, guess: { low: 0, mid: 1, high: 5 } }),
    rustGuess,
  );
});

test("the schema tags are exactly the node's two constants", async () => {
  const rust = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  assert.match(
    rust,
    new RegExp(`POA_SIGNAL_SESSION_OPEN_STATEMENT_V1: &str = "${SIGNAL_SESSION_OPEN_SCHEMA}"`),
  );
  assert.match(
    rust,
    new RegExp(`POA_SIGNAL_SESSION_GUESS_STATEMENT_V1: &str = "${SIGNAL_SESSION_GUESS_SCHEMA}"`),
  );
  assert.deepEqual(Object.keys(SIGNAL_SESSION_SCHEMAS), ["open", "guess"]);
  assert.deepEqual([...SIGNAL_SESSION_KINDS], ["open", "guess"]);
});

test("every field the statement binds changes the bytes", () => {
  const base = { kind: "guess", authorityId: AUTHORITY, slot: 9, round: 2, guess: { low: 0, mid: 1, high: 5 } };
  const original = text(base);
  assert.notEqual(text({ ...base, slot: 10 }), original, "a signature must not carry across slots");
  assert.notEqual(text({ ...base, round: 3 }), original, "a signature covers exactly one round");
  assert.notEqual(text({ ...base, guess: { low: 1, mid: 1, high: 5 } }), original);
  assert.notEqual(text({ ...base, guess: { low: 0, mid: 1, high: 4 } }), original);
  assert.notEqual(text({ ...base, authorityId: "42".repeat(32) }), original);
  assert.notEqual(text(base, "66".repeat(32)), original, "the player key is inside the statement");
  // An open statement is never a prefix-extension of a guess statement or vice
  // versa: the schema tag differs in the first field.
  const open = text({ kind: "open", authorityId: AUTHORITY, slot: 9 });
  assert.ok(!original.startsWith(open.slice(0, -1)));
});

test("slot rides as a bare decimal at both u64 edges", () => {
  assert.match(text({ kind: "open", authorityId: AUTHORITY, slot: 0 }), /"slot":0,/);
  assert.match(
    text({ kind: "open", authorityId: AUTHORITY, slot: "18446744073709551615" }),
    /"slot":18446744073709551615,/,
  );
  assert.equal(U64_MAX, 18446744073709551615n);
  assert.equal(slotWire(9n), 9);
  assert.equal(slotWire(U64_MAX), "18446744073709551615");
});

// ---------------------------------------------------------------------------
// 2. THE REFUSAL POLES — the load-bearing half.
//
// Each pole asserts the hostile INPUT is present before it reads the verdict.
// ---------------------------------------------------------------------------

function refused(input, why) {
  const result = parseSignalSessionRequest(input);
  assert.equal(result.ok, false, `${why} — but the signer ACCEPTED it: ${JSON.stringify(input)}`);
  assert.ok(typeof result.error === "string" && result.error.length > 0, "a refusal must name its cause");
  return result.error;
}

test("POLE: a transfer-shaped request is refused", () => {
  // The thing a signing oracle would let a page do: obtain a player-key
  // signature over a value-moving intent.
  const transfer = {
    kind: "transfer",
    authorityId: AUTHORITY,
    slot: 0,
    recipient: "de".repeat(32),
    amount: 1_000_000,
  };
  // ⚑ Mutation present: this really is a transfer shape, not a mistyped open.
  assert.equal(transfer.kind, "transfer");
  assert.equal(transfer.amount, 1_000_000);
  const error = refused(transfer, "a transfer-shaped request must be refused");
  assert.match(error, /kind must be one of open, guess/);

  // And the same fields smuggled under an ALLOWED kind are refused too — the
  // key set is exact, so `recipient`/`amount` are a named refusal rather than
  // ignored extras that make the caller believe it signed a transfer.
  const smuggled = { kind: "open", authorityId: AUTHORITY, slot: 0, recipient: "de".repeat(32), amount: 1_000_000 };
  assert.ok("recipient" in smuggled && "amount" in smuggled);
  assert.match(refused(smuggled, "a transfer smuggled under an open kind must be refused"), /exactly/);
});

test("POLE: arbitrary caller-chosen bytes cannot enter this path", () => {
  // Every spelling of "here are the bytes, sign them". None of these is a
  // parameter of this method, and an unknown key is a REFUSAL, not an extra.
  const preimage = Array.from({ length: 32 }, (_value, index) => index);
  for (const [field, value] of [
    ["message", preimage],
    ["bytes", preimage],
    ["statement", '{"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1"}'],
    ["preimage", bytesToHex(Uint8Array.from(preimage))],
    ["turnBytes", preimage],
    ["digest", bytesToHex(Uint8Array.from(preimage))],
  ]) {
    const hostile = { kind: "open", authorityId: AUTHORITY, slot: 0, [field]: value };
    assert.ok(field in hostile, `the ${field} mutation must be present before the verdict`);
    assert.notEqual(hostile[field], undefined);
    refused(hostile, `a caller-supplied \`${field}\` must be refused`);
  }

  // A bare bytes request, with no session shape at all.
  assert.ok(Array.isArray(preimage) && preimage.length === 32);
  refused({ message: preimage }, "a bare bytes request must be refused");
  refused(preimage, "an array of bytes must be refused");
  refused("0".repeat(64), "a hex string must be refused");
  refused(new Uint8Array(32), "a Uint8Array must be refused");
});

test("POLE: a page cannot name the schema, only a kind from the allowlist", () => {
  // Naming the schema directly is the move that would turn a kind allowlist
  // into a free choice of template.
  for (const kind of [
    SIGNAL_SESSION_OPEN_SCHEMA,
    SIGNAL_SESSION_GUESS_SCHEMA,
    "OPEN",
    "Open",
    "sign",
    "turn",
    "transfer",
    "",
    "toString",
    "constructor",
    "__proto__",
  ]) {
    const hostile = { kind, authorityId: AUTHORITY, slot: 0 };
    assert.equal(hostile.kind, kind, "the hostile kind must be present before the verdict");
    refused(hostile, `kind ${JSON.stringify(kind)} must be refused`);
  }
  // A `schema` key alongside a legal kind is an unknown key, not an override.
  const withSchema = { kind: "open", authorityId: AUTHORITY, slot: 0, schema: "ANYTHING" };
  assert.equal(withSchema.schema, "ANYTHING");
  refused(withSchema, "a caller-supplied schema must be refused");
  // Non-plain objects (prototype tricks) never reach the key check.
  refused(Object.assign(Object.create({ kind: "open" }), { authorityId: AUTHORITY, slot: 0 }),
    "an inherited kind must be refused");
});

test("POLE: the player key is not a parameter — custody supplies it", () => {
  const hostile = { kind: "open", authorityId: AUTHORITY, slot: 0, playerKey: "66".repeat(32) };
  assert.equal(hostile.playerKey, "66".repeat(32), "the substituted key must be present before the verdict");
  refused(hostile, "a page-chosen player key must be refused");
  assert.notEqual(MIXED_HEX_UPPER, MIXED_HEX, "the case mutation must actually change the string");
  for (const bad of ["", MIXED_HEX_UPPER, PLAYER.slice(0, 63), `${PLAYER}00`, "zz".repeat(32), 0, null]) {
    assert.throws(
      () => signalSessionStatement({ kind: "open", authorityId: AUTHORITY, slot: 0 }, bad),
      TypeError,
      `playerKeyHex ${JSON.stringify(bad)} must be refused`,
    );
  }
});

test("every field-validation denial path is a named refusal", () => {
  const open = { kind: "open", authorityId: AUTHORITY, slot: 0 };
  assert.notEqual(MIXED_HEX_UPPER, MIXED_HEX, "the case mutation must actually change the string");
  assert.equal(parseSignalSessionRequest({ ...open, authorityId: MIXED_HEX }).ok, true);
  refused({ ...open, authorityId: MIXED_HEX_UPPER }, "uppercase hex");
  refused({ ...open, authorityId: AUTHORITY.slice(0, 63) }, "short hex");
  refused({ ...open, authorityId: "zz".repeat(32) }, "non-hex");
  refused({ ...open, authorityId: 0 }, "numeric authority");
  refused({ ...open, slot: -1 }, "negative slot");
  refused({ ...open, slot: 1.5 }, "fractional slot");
  refused({ ...open, slot: "007" }, "non-canonical decimal — two spellings of one slot");
  refused({ ...open, slot: "+7" }, "signed decimal");
  refused({ ...open, slot: " 7 " }, "padded decimal");
  refused({ ...open, slot: "18446744073709551616" }, "slot past u64::MAX");
  refused({ kind: "open", authorityId: AUTHORITY }, "a missing slot");
  refused({ kind: "guess", authorityId: AUTHORITY, slot: 0 }, "a guess with no round or code");

  const guess = { kind: "guess", authorityId: AUTHORITY, slot: 0, round: 0, guess: { low: 0, mid: 0, high: 0 } };
  assert.equal(parseSignalSessionRequest(guess).ok, true, "the all-zero code is a LEGAL guess");
  refused({ ...guess, round: -1 }, "negative round");
  refused({ ...guess, round: U32_MAX + 1 }, "round past u32::MAX");
  refused({ ...guess, guess: { low: 0, mid: 0, high: SIGNAL_BAND_MAX + 1 } }, "a band past 5");
  refused({ ...guess, guess: { low: -1, mid: 0, high: 0 } }, "a negative band");
  refused({ ...guess, guess: { low: 0, mid: 0 } }, "a two-band code");
  refused({ ...guess, guess: { low: 0, mid: 0, high: 0, extra: 1 } }, "a four-key code");
  refused({ ...guess, guess: [0, 0, 0] }, "an array code");
  // The `open` shape may not carry guess fields, and vice versa.
  refused({ ...open, round: 0, guess: { low: 0, mid: 0, high: 0 } }, "an open carrying guess fields");
});

// ---------------------------------------------------------------------------
// 3. DOMAIN SEPARATION — exhibited.
// ---------------------------------------------------------------------------

// The a-priori image of this method: statements over a spread of every field.
function* everyReachableStatement() {
  for (const authorityId of [AUTHORITY, "00".repeat(32), "ff".repeat(32)]) {
    for (const slot of [0, 9, Number.MAX_SAFE_INTEGER, "18446744073709551615"]) {
      for (const playerKey of [PLAYER, "00".repeat(32), "ff".repeat(32)]) {
        yield signalSessionStatement({ kind: "open", authorityId, slot }, playerKey);
        for (const round of [0, 4, U32_MAX]) {
          for (const band of [0, SIGNAL_BAND_MAX]) {
            yield signalSessionStatement(
              { kind: "guess", authorityId, slot, round, guess: { low: band, mid: band, high: band } },
              playerKey,
            );
          }
        }
      }
    }
  }
}

test("no reachable statement is a 32-byte turn-authorization preimage", () => {
  // `TurnExecutor::compute_signing_message` returns [u8; 32] and
  // `authorize.rs` calls `verify_strict` on exactly those 32 bytes. Ed25519 is
  // PureEdDSA — it signs the WHOLE message — so a signature over anything that
  // is not 32 bytes can never be a valid action authorization.
  const TURN_PREIMAGE_BYTES = 32;
  assert.ok(MIN_STATEMENT_BYTES > TURN_PREIMAGE_BYTES);
  let seen = 0;
  for (const statement of everyReachableStatement()) {
    seen += 1;
    assert.ok(
      statement.bytes.length >= MIN_STATEMENT_BYTES,
      `a statement fell below the lower bound: ${statement.text}`,
    );
    assert.notEqual(statement.bytes.length, TURN_PREIMAGE_BYTES);
  }
  assert.ok(seen >= 100, `the image sweep collapsed to ${seen} statements`);
  // The bound is not a slogan: the two 64-char hex fields alone exceed 32 bytes.
  assert.equal(MIN_STATEMENT_BYTES, text({ kind: "open", authorityId: "0".repeat(64), slot: 0 }, "0".repeat(64)).length);
});

test("no reachable statement carries another signable object's domain tag", () => {
  // The other Ed25519 preimages in this system, by their leading domain tag.
  const FOREIGN_DOMAINS = [
    "dregg-offering-turn-v1:",
    "dregg-sovereign-witness-v1:",
    "dregg-sovereign-witness-v2:",
    "dregg-sovereign-effects-v1:",
    "dregg-action-sig-v3:",
    "Ethereum Signed Message:\n",
  ];
  for (const statement of everyReachableStatement()) {
    assert.ok(
      statement.text.startsWith('{"schema":"POA-SIGNAL-SESSION-'),
      `a statement escaped the pinned prefix: ${statement.text}`,
    );
    for (const domain of FOREIGN_DOMAINS) {
      assert.ok(!statement.text.includes(domain), `a statement embedded ${domain}`);
    }
  }
});

// ---------------------------------------------------------------------------
// Sign-then-verify, against the exact relation `verify_player_signature` checks.
// The extension signs with wasm `sign_message` (SigningKey::from_bytes over a
// 32-byte seed); node:crypto implements the same RFC 8032 scheme.
// ---------------------------------------------------------------------------

const PKCS8_ED25519_PREFIX = Buffer.from("302e020100300506032b657004220420", "hex");
const SPKI_ED25519_PREFIX = Buffer.from("302a300506032b6570032100", "hex");

function keyFromSeed(seedByte) {
  const seed = Buffer.alloc(32, seedByte);
  const privateKey = createPrivateKey({
    key: Buffer.concat([PKCS8_ED25519_PREFIX, seed]),
    format: "der",
    type: "pkcs8",
  });
  const spki = createPublicKey(privateKey).export({ format: "der", type: "spki" });
  return { privateKey, pubkeyHex: spki.subarray(SPKI_ED25519_PREFIX.length).toString("hex") };
}

function verifyOver(messageBytes, pubkeyHex, signatureHex) {
  const pub = createPublicKey({
    key: Buffer.concat([SPKI_ED25519_PREFIX, Buffer.from(pubkeyHex, "hex")]),
    format: "der",
    type: "spki",
  });
  return edVerify(null, Buffer.from(messageBytes), pub, Buffer.from(signatureHex, "hex"));
}

test("a session signature verifies against the node's re-derivation, and nothing else", () => {
  const { privateKey, pubkeyHex } = keyFromSeed(7);
  const request = { kind: "guess", authorityId: AUTHORITY, slot: 9, round: 2, guess: { low: 0, mid: 1, high: 5 } };
  const statement = signalSessionStatement(request, pubkeyHex);
  const signatureHex = bytesToHex(new Uint8Array(edSign(null, Buffer.from(statement.bytes), privateKey)));
  assert.equal(signatureHex.length, 128, "the node's parser demands exactly 128 hex digits");
  assert.equal(signatureHex, signatureHex.toLowerCase());

  // The node re-derives from the structured fields and verifies against THAT.
  assert.equal(verifyOver(statement.bytes, pubkeyHex, signatureHex), true);

  // Every splice `verify_player_signature` refuses:
  for (const [why, spliced] of [
    ["a shifted round", { ...request, round: 3 }],
    ["another slot", { ...request, slot: 10 }],
    ["another authority", { ...request, authorityId: "42".repeat(32) }],
    ["a different code", { ...request, guess: { low: 0, mid: 1, high: 4 } }],
    ["the open statement for the same session", { kind: "open", authorityId: AUTHORITY, slot: 9 }],
  ]) {
    const other = signalSessionStatement(spliced, pubkeyHex);
    assert.notDeepEqual(Array.from(other.bytes), Array.from(statement.bytes), `${why} must be different bytes`);
    assert.equal(verifyOver(other.bytes, pubkeyHex, signatureHex), false, `${why} must refuse`);
  }

  // A statement naming a DIFFERENT player does not verify under this key.
  const impostorSubject = signalSessionStatement(request, keyFromSeed(8).pubkeyHex);
  assert.equal(verifyOver(impostorSubject.bytes, pubkeyHex, signatureHex), false);

  // ⚑ THE SEPARATION POLE, constructively: this signature over a 32-byte
  // turn-authorization preimage does not verify, for any such preimage.
  for (const seed of [0x00, 0x41, 0xff]) {
    const turnPreimage = Buffer.alloc(32, seed);
    assert.equal(turnPreimage.length, 32, "the turn preimage must be 32 bytes before the verdict");
    assert.equal(verifyOver(turnPreimage, pubkeyHex, signatureHex), false);
  }
});

test("a turn preimage cannot be signed through this path at all", () => {
  // Not "it would not verify" — it is UNREACHABLE. There is no input that makes
  // this builder emit a 32-byte message, because there is no byte input.
  const turnPreimage = Buffer.alloc(32, 0x41);
  assert.equal(turnPreimage.length, 32);
  for (const attempt of [
    { kind: "open", authorityId: AUTHORITY, slot: 0, message: Array.from(turnPreimage) },
    { kind: "open", authorityId: bytesToHex(turnPreimage), slot: 0 },
  ]) {
    const parsed = parseSignalSessionRequest(attempt);
    if (!parsed.ok) continue;
    // The second attempt IS accepted — a 32-byte digest is a legal authority id
    // — and that is exactly the case worth exhibiting: what comes out is still
    // a session statement about that authority, not the digest.
    const statement = signalSessionStatement(attempt, PLAYER);
    assert.ok(statement.bytes.length > 32);
    assert.ok(statement.text.startsWith('{"schema":"POA-SIGNAL-SESSION-'));
    assert.ok(!statement.text.startsWith("A"), "the digest is quoted as a field, never emitted raw");
  }
});

// ---------------------------------------------------------------------------
// 4. THE SESSION-SCOPED GRANT — and the proof it widens nothing.
// ---------------------------------------------------------------------------
//
// A judged run is 1 open + 5 guesses. Six popups is a usability failure that
// makes nobody play, AND a security failure: a player trained to click through
// six identical dialogs cannot see the seventh. So consent moves to "play this
// judged run", once.
//
// The whole risk of that move is one sentence: DOES THE GRANT WIDEN THE SIGNER
// INTO AN ORACLE? Every structural property of this module is therefore
// re-asserted here UNDER A LIVE GRANT, not merely in its absence.

const ORIGIN = "https://pathofangels.example";
const T0 = 1_770_000_000_000;

const parseOrThrow = (request) => {
  const parsed = parseSignalSessionRequest(request);
  assert.ok(parsed.ok, `fixture must parse: ${parsed.error ?? ""}`);
  return parsed.request;
};

const openReq = (slot = 9) => parseOrThrow({ kind: "open", authorityId: AUTHORITY, slot });
const guessReq = (round = 0, slot = 9, band = 3) =>
  parseOrThrow({ kind: "guess", authorityId: AUTHORITY, slot, round, guess: { low: band, mid: band, high: band } });

const freshGrant = (over = {}) =>
  createSignalSessionGrant({
    authorityId: AUTHORITY,
    slot: 9,
    playerKeyHex: PLAYER,
    origin: ORIGIN,
    nowMs: T0,
    ...over,
  });

test("a grant is exactly one judged run: 1 open + MAX_ROUNDS guesses, and not one more", () => {
  assert.equal(SIGNAL_SESSION_MAX_ROUNDS, 5, "the node's POA_SIGNAL_SESSION_MAX_ROUNDS");
  assert.deepEqual({ ...SIGNAL_SESSION_GRANT_BUDGET }, { open: 1, guess: 5 });
  // The budget is keyed by the FROZEN allowlist and by nothing else: a grant
  // cannot acquire a third kind because there is no third kind.
  assert.deepEqual(Object.keys(SIGNAL_SESSION_GRANT_BUDGET).sort(), [...SIGNAL_SESSION_KINDS].sort());
  assert.ok(Object.isFrozen(SIGNAL_SESSION_GRANT_BUDGET));

  let grant = freshGrant();
  assert.ok(Object.isFrozen(grant));
  // The open.
  let spend = spendSignalSessionGrant(grant, openReq(), PLAYER, ORIGIN, T0);
  assert.ok(spend.ok);
  grant = spend.grant;
  assert.equal(grant.remaining.open, 0);
  // A SECOND open is refused — a grant is one run, not a standing permission to
  // re-open at will.
  const secondOpen = grantCovers(grant, openReq(), PLAYER, ORIGIN, T0);
  assert.equal(secondOpen.ok, false);
  assert.equal(secondOpen.code, "grant-exhausted");

  // Five guesses.
  for (let round = 0; round < SIGNAL_SESSION_MAX_ROUNDS; round++) {
    const step = spendSignalSessionGrant(grant, guessReq(round), PLAYER, ORIGIN, T0);
    assert.ok(step.ok, `guess ${round} must be covered`);
    grant = step.grant;
    assert.equal(grant.remaining.guess, SIGNAL_SESSION_MAX_ROUNDS - round - 1);
  }
  // ⚑ THE SIXTH IS FRESH CONSENT. There is no renewal verb anywhere in the API.
  const sixth = grantCovers(grant, guessReq(5), PLAYER, ORIGIN, T0);
  assert.equal(sixth.ok, false);
  assert.equal(sixth.code, "grant-exhausted");
  assert.match(sixth.error, /fresh consent/);
});

test("a grant for slot N is USELESS at slot N+1", () => {
  const grant = freshGrant({ slot: 9 });
  // The mutation asserted present before the verdict: these really are different slots.
  const here = guessReq(0, 9);
  const next = guessReq(0, 10);
  assert.notEqual(here.slot, next.slot);
  assert.equal(grantCovers(grant, here, PLAYER, ORIGIN, T0).ok, true);

  const refused = grantCovers(grant, next, PLAYER, ORIGIN, T0);
  assert.equal(refused.ok, false);
  assert.equal(refused.code, "grant-scope-slot");
  // And spending cannot get around covering: the successor grant is not produced.
  const spend = spendSignalSessionGrant(grant, next, PLAYER, ORIGIN, T0);
  assert.equal(spend.ok, false);
  assert.equal(spend.code, "grant-scope-slot");
  // The `open` for the next slot is refused too — a new run needs a new consent.
  assert.equal(grantCovers(grant, openReq(10), PLAYER, ORIGIN, T0).code, "grant-scope-slot");
});

test("every scope field is compared for EQUALITY, and each mismatch is named", () => {
  const grant = freshGrant();
  const other = "be".repeat(32);
  assert.notEqual(other, AUTHORITY);
  assert.notEqual(other, PLAYER);

  assert.equal(
    grantCovers(grant, parseOrThrow({ kind: "open", authorityId: other, slot: 9 }), PLAYER, ORIGIN, T0).code,
    "grant-scope-authority",
  );
  assert.equal(grantCovers(grant, openReq(), other, ORIGIN, T0).code, "grant-scope-player");
  assert.equal(grantCovers(grant, openReq(), PLAYER, "https://evil.example", T0).code, "grant-scope-origin");
  // No grant at all is not an accept.
  assert.equal(grantCovers(null, openReq(), PLAYER, ORIGIN, T0).ok, false);
  assert.equal(grantCovers(undefined, openReq(), PLAYER, ORIGIN, T0).ok, false);
});

test("a grant expires, and expiry is fresh consent", () => {
  const grant = freshGrant();
  assert.equal(grant.expiresAtMs, T0 + SIGNAL_SESSION_GRANT_TTL_MS);
  assert.equal(grantCovers(grant, openReq(), PLAYER, ORIGIN, grant.expiresAtMs - 1).ok, true);
  // Exactly AT the expiry is already too late — the comparison is strict.
  const atExpiry = grantCovers(grant, openReq(), PLAYER, ORIGIN, grant.expiresAtMs);
  assert.equal(atExpiry.ok, false);
  assert.equal(atExpiry.code, "grant-expired");
  assert.equal(grantCovers(grant, openReq(), PLAYER, ORIGIN, grant.expiresAtMs + 1e9).code, "grant-expired");
  // A caller cannot ask for a longer one than the policy.
  const greedy = freshGrant({ ttlMs: SIGNAL_SESSION_GRANT_TTL_MS * 1000 });
  assert.equal(greedy.expiresAtMs, T0 + SIGNAL_SESSION_GRANT_TTL_MS);
});

test("⚑ a grant relaxes NONE of the signer's structural properties", () => {
  // Property 1 — NO BYTES PARAMETER. A grant is checked against a PARSED
  // request, and a payload carrying bytes never becomes one.
  const smuggled = parseSignalSessionRequest({
    kind: "open",
    authorityId: AUTHORITY,
    slot: 9,
    message: Array.from(Buffer.alloc(32, 0x41)),
  });
  assert.equal(smuggled.ok, false, "a bytes field must not survive parsing, grant or no grant");
  assert.match(smuggled.error, /exactly/);

  // Property 2 — EXACT KEY SETS still hold; the grant is downstream of them.
  for (const hostile of [
    { kind: "open", authorityId: AUTHORITY, slot: 9, statement: "x" },
    { kind: "guess", authorityId: AUTHORITY, slot: 9, round: 0, guess: { low: 0, mid: 0, high: 0 }, bytes: [1] },
    { kind: "transfer", authorityId: AUTHORITY, slot: 9 },
  ]) {
    assert.equal(parseSignalSessionRequest(hostile).ok, false, `must refuse: ${JSON.stringify(hostile)}`);
  }

  // Property 3 — THE KIND ALLOWLIST IS STILL EXACTLY TWO, and a grant's own
  // budget cannot introduce a third.
  const grant = freshGrant();
  assert.deepEqual(Object.keys(grant.remaining).sort(), ["guess", "open"]);
  assert.ok(Object.isFrozen(grant.remaining));
  assert.equal(grant.remaining.transfer, undefined);
  // Even if a caller hands a forged grant object naming a third kind, the parse
  // upstream means no request with that kind can ever be presented to it.
  const forged = Object.freeze({ ...grant, remaining: Object.freeze({ open: 1, guess: 5, transfer: 99 }) });
  assert.equal(parseSignalSessionRequest({ kind: "transfer", authorityId: AUTHORITY, slot: 9 }).ok, false);
  assert.equal(grantCovers(forged, openReq(), PLAYER, ORIGIN, T0).ok, true, "the real kinds still work");

  // Property 4 — THE PLAYER KEY IS SUPPLIED BY CUSTODY. The grant takes it as a
  // separate argument and refuses a different one; the statement builder still
  // takes it separately too, so a grant cannot make the page name a subject.
  assert.equal(grantCovers(grant, openReq(), keyFromSeed(8).pubkeyHex, ORIGIN, T0).code, "grant-scope-player");
  const statement = signalSessionStatement(openReq(), PLAYER);
  assert.ok(statement.text.includes(`"player_key":"${PLAYER}"`));

  // Property 5 — THE LENGTH FLOOR. Every statement reachable while a grant is
  // live is the SAME statement, and the image is unchanged: 219 bytes minimum,
  // never 32. (⚠ 219, not the 148 this has been quoted as.)
  assert.equal(MIN_STATEMENT_BYTES, 219);
  let live = grant;
  let covered = 0;
  for (const request of [openReq(), guessReq(0), guessReq(1), guessReq(2), guessReq(3), guessReq(4)]) {
    const spend = spendSignalSessionGrant(live, request, PLAYER, ORIGIN, T0);
    assert.ok(spend.ok, "the whole run must be covered by one grant");
    live = spend.grant;
    covered += 1;
    const text = signalSessionStatement(request, PLAYER);
    assert.ok(text.bytes.length >= MIN_STATEMENT_BYTES);
    assert.notEqual(text.bytes.length, 32);
    assert.ok(text.text.startsWith('{"schema":"POA-SIGNAL-SESSION-'));
  }
  assert.equal(covered, 6, "one open plus five guesses");

  // And the a-priori image sweep is byte-identical with a grant held: the grant
  // is not on the statement-building path at all.
  for (const s of everyReachableStatement()) {
    assert.ok(s.bytes.length >= MIN_STATEMENT_BYTES);
    assert.notEqual(s.bytes.length, 32);
  }
});

test("a grant is immutable — spending returns a successor and never mutates the original", () => {
  const grant = freshGrant();
  const spend = spendSignalSessionGrant(grant, guessReq(0), PLAYER, ORIGIN, T0);
  assert.ok(spend.ok);
  assert.equal(grant.remaining.guess, 5, "the original grant is untouched");
  assert.equal(spend.grant.remaining.guess, 4);
  assert.notEqual(spend.grant, grant);
  // Frozen for real: a write throws in module (strict) code rather than silently
  // widening the budget.
  assert.throws(() => {
    grant.remaining.guess = 99;
  }, TypeError);
});

test("the grant book holds ONE grant, applies expiry on read, and clears", () => {
  const book = new SignalSessionGrantBook();
  // With nothing remembered, every request needs consent.
  assert.equal(book.consume(openReq(), PLAYER, ORIGIN, T0).ok, false);

  book.remember(freshGrant());
  assert.equal(book.consume(openReq(), PLAYER, ORIGIN, T0).ok, true);
  assert.equal(book.peek(T0).remaining.open, 0, "consuming spends the stored grant");
  assert.equal(book.consume(openReq(), PLAYER, ORIGIN, T0).code, "grant-exhausted");

  // A second slot's grant REPLACES the first — there is never a set of standing
  // authorizations a player cannot see the size of.
  book.remember(freshGrant({ slot: 10 }));
  assert.equal(book.consume(guessReq(0, 9), PLAYER, ORIGIN, T0).code, "grant-scope-slot");
  assert.equal(book.consume(guessReq(0, 10), PLAYER, ORIGIN, T0).ok, true);

  // Expiry is applied on READ, so a stale grant is never handed out.
  assert.equal(book.peek(T0 + SIGNAL_SESSION_GRANT_TTL_MS), null);
  book.remember(freshGrant());
  book.clear();
  assert.equal(book.peek(T0), null);
  assert.equal(book.consume(openReq(), PLAYER, ORIGIN, T0).ok, false);
});

test("a malformed scope is refused at mint rather than becoming a loose grant", () => {
  const good = { authorityId: AUTHORITY, slot: 9, playerKeyHex: PLAYER, origin: ORIGIN };
  assert.ok(createSignalSessionGrant(good));
  for (const [what, over] of [
    ["an uppercase authority", { authorityId: MIXED_HEX_UPPER }],
    ["a short authority", { authorityId: "ab" }],
    ["an uppercase player key", { playerKeyHex: MIXED_HEX_UPPER }],
    ["a negative slot", { slot: -1 }],
    ["a slot past u64::MAX", { slot: (U64_MAX + 1n).toString() }],
    ["an empty origin", { origin: "" }],
    ["a missing origin", { origin: undefined }],
  ]) {
    assert.throws(() => createSignalSessionGrant({ ...good, ...over }), TypeError, what);
  }
});

test("the consent surface can say what it is granting, in the grant's own words", () => {
  const description = describeSignalSessionGrant(freshGrant());
  // It must name the SLOT, the budget and the origin — a dialog that says
  // "allow this site to sign" is the thing this whole design refuses.
  assert.match(description, /slot 9/);
  assert.match(description, /1 open \+ up to 5 guess signatures/);
  assert.ok(description.includes(ORIGIN));
  assert.ok(description.includes(PLAYER.slice(0, 16)));
  assert.ok(!/sign anything/i.test(description));
});

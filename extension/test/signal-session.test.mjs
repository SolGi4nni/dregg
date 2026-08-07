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
  SIGNAL_SESSION_GUESS_SCHEMA,
  SIGNAL_SESSION_KINDS,
  SIGNAL_SESSION_OPEN_SCHEMA,
  SIGNAL_SESSION_SCHEMAS,
  U32_MAX,
  U64_MAX,
  bytesToHex,
  parseSignalSessionRequest,
  signalSessionStatement,
  slotWire,
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

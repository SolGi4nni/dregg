// Offering-turn signing (G1 rung 2) — src/offering-sign.ts.
//
// THE NON-NEGOTIABLE is the wire pin: the canonical signing message for a
// fixed input, byte for byte, constructed here BY HAND — the SAME
// expected-bytes vector as the Rust pin test
// (dreggnet-offerings/src/signed.rs::the_canonical_signing_message_is_pinned_byte_for_byte),
// so the TS builder and the Rust builder can never drift silently: any layout
// drift (reordered field, dropped separator, endianness flip) is a red test on
// whichever side moved.
//
// Also: a sign-then-verify round trip over the wire encoding (node:crypto
// Ed25519, the same independent verifier the passkey-sign suite uses), u64
// counter edge encodings (0, 1, 2^53-1 as a number, 2^64-1 as a string), i64
// arg two's-complement encoding, and every params-validation denial path.

import { test } from "node:test";
import assert from "node:assert/strict";
import { createPrivateKey, createPublicKey, sign as edSign, verify as edVerify } from "node:crypto";
import {
  I64_MAX,
  I64_MIN,
  OFFERING_TURN_SIGNING_DOMAIN,
  U64_MAX,
  bytesToHex,
  counterWire,
  parseOfferingTurnParams,
  signingMessage,
} from "./.build/offering-sign.mjs";

// ---------------------------------------------------------------------------
// THE WIRE PIN — mirror of the Rust pin test, constructed by hand.
// ---------------------------------------------------------------------------

test("the canonical signing message is pinned byte-for-byte against the Rust vector", () => {
  // signing_message("dungeon", SessionId::new("sess-1"), 7,
  //                 Action::new("press on", "choose", 3, true))  — text: None
  const msg = signingMessage({
    offeringKey: "dungeon",
    sessionId: "sess-1",
    counter: 7,
    turn: "choose",
    arg: 3,
  });

  const enc = new TextEncoder();
  const expected = [];
  const push = (bytes) => expected.push(...bytes);
  push(enc.encode("dregg-offering-turn-v1:"));
  push(enc.encode("dungeon"));
  expected.push(0x00);
  push(enc.encode("sess-1"));
  expected.push(0x00);
  push([7, 0, 0, 0, 0, 0, 0, 0]); // 7u64 LE
  expected.push(0x00);
  push(enc.encode("choose"));
  expected.push(0x00);
  push([3, 0, 0, 0, 0, 0, 0, 0]); // 3i64 LE
  expected.push(0x00);
  // text-or-empty: absent → empty
  assert.deepEqual(
    Array.from(msg),
    expected,
    "the canonical turn signing message drifted from the Rust pin",
  );

  // A text payload rides at the end; a DIFFERENT text is a DIFFERENT message.
  const withText = signingMessage({
    offeringKey: "dungeon",
    sessionId: "sess-1",
    counter: 7,
    turn: "choose",
    arg: 3,
    text: "hello",
  });
  assert.deepEqual(Array.from(withText), [...expected, ...enc.encode("hello")]);
  assert.notDeepEqual(Array.from(msg), Array.from(withText));

  // text: "" encodes identically to text absent (Rust: text.as_deref().unwrap_or("")).
  const emptyText = signingMessage({
    offeringKey: "dungeon",
    sessionId: "sess-1",
    counter: 7,
    turn: "choose",
    arg: 3,
    text: "",
  });
  assert.deepEqual(Array.from(emptyText), expected);
});

test("the domain tag is the exact Rust TURN_SIGNING_DOMAIN", () => {
  assert.equal(OFFERING_TURN_SIGNING_DOMAIN, "dregg-offering-turn-v1:");
});

// ---------------------------------------------------------------------------
// u64 counter edge encoding. The counter's 8 LE bytes sit right after
// domain ‖ offeringKey ‖ 0 ‖ sessionId ‖ 0.
// ---------------------------------------------------------------------------

function counterBytes(counter) {
  const msg = signingMessage({
    offeringKey: "o",
    sessionId: "s",
    counter,
    turn: "t",
    arg: 0,
  });
  const start = OFFERING_TURN_SIGNING_DOMAIN.length + 1 + 1 + 1 + 1;
  return Array.from(msg.slice(start, start + 8));
}

test("u64 counter edges encode little-endian: 0, 1, 2^53-1 (number), 2^64-1 (string)", () => {
  assert.deepEqual(counterBytes(0), [0, 0, 0, 0, 0, 0, 0, 0]);
  assert.deepEqual(counterBytes(1), [1, 0, 0, 0, 0, 0, 0, 0]);
  // 2^53 - 1 = 0x001fffffffffffff, the largest safe-integer number.
  assert.deepEqual(
    counterBytes(Number.MAX_SAFE_INTEGER),
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x1f, 0x00],
  );
  // u64::MAX passed as a decimal string.
  assert.deepEqual(
    counterBytes("18446744073709551615"),
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
  );
  assert.equal(U64_MAX, 18446744073709551615n);
});

test("i64 arg encodes two's-complement little-endian at both edges", () => {
  const argBytes = (arg) => {
    const msg = signingMessage({ offeringKey: "o", sessionId: "s", counter: 0, turn: "t", arg });
    // arg's 8 bytes are followed only by 0x00 ‖ text(empty): last 9 bytes.
    return Array.from(msg.slice(msg.length - 9, msg.length - 1));
  };
  assert.deepEqual(argBytes(3), [3, 0, 0, 0, 0, 0, 0, 0]);
  assert.deepEqual(argBytes(-1), [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);
  // i64::MAX / i64::MIN as decimal strings.
  assert.deepEqual(argBytes("9223372036854775807"), [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]);
  assert.deepEqual(argBytes("-9223372036854775808"), [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80]);
  assert.equal(I64_MAX, 9223372036854775807n);
  assert.equal(I64_MIN, -9223372036854775808n);
});

// ---------------------------------------------------------------------------
// Denial paths — params validation refuses each malformation with a named
// error BEFORE any message is built.
// ---------------------------------------------------------------------------

const GOOD = { offeringKey: "dungeon", sessionId: "sess-1", counter: 7, turn: "choose", arg: 3 };

function refuses(overrides, pattern, label) {
  const r = parseOfferingTurnParams({ ...GOOD, ...overrides });
  assert.equal(r.ok, false, `${label}: refused`);
  assert.match(r.error, pattern, `${label}: names the failure`);
  assert.throws(() => signingMessage({ ...GOOD, ...overrides }), TypeError, `${label}: signingMessage throws too`);
}

test("counter denial paths: non-integer, negative, >u64, unsafe number, junk", () => {
  refuses({ counter: 1.5 }, /integer/, "fractional counter");
  refuses({ counter: -1 }, /negative/, "negative counter");
  refuses({ counter: "-1" }, /decimal/, "negative string counter");
  refuses({ counter: "18446744073709551616" }, /u64/, "u64::MAX + 1");
  // 2^53 as a NUMBER is not a safe integer — must ride as a string.
  refuses({ counter: 2 ** 53 }, /decimal string/, "unsafe-integer number counter");
  refuses({ counter: "0x10" }, /decimal/, "hex string counter");
  refuses({ counter: null }, /number or a decimal string/, "null counter");
  refuses({ counter: undefined }, /number or a decimal string/, "missing counter");
});

test("arg denial paths: out of i64 range both ways, fractional, junk", () => {
  refuses({ arg: "9223372036854775808" }, /i64/, "i64::MAX + 1");
  refuses({ arg: "-9223372036854775809" }, /i64/, "i64::MIN - 1");
  refuses({ arg: 0.25 }, /integer/, "fractional arg");
  refuses({ arg: {} }, /number or a decimal string/, "object arg");
});

test("string-field denial paths: wrong type, empty, embedded NUL", () => {
  refuses({ offeringKey: 7 }, /must be a string/, "numeric offeringKey");
  refuses({ offeringKey: "" }, /empty/, "empty offeringKey");
  refuses({ sessionId: "" }, /empty/, "empty sessionId");
  refuses({ turn: "" }, /empty/, "empty turn");
  // NUL is the canonical field separator — an embedded NUL would let two
  // different field tuples encode to the same signed bytes.
  refuses({ offeringKey: "dun\u0000geon" }, /NUL/, "NUL in offeringKey");
  refuses({ sessionId: "s\u0000" }, /NUL/, "NUL in sessionId");
  refuses({ turn: "cho\u0000ose" }, /NUL/, "NUL in turn");
  refuses({ text: "he\u0000llo" }, /NUL/, "NUL in text");
  refuses({ text: 42 }, /must be a string/, "numeric text");
  assert.equal(parseOfferingTurnParams(null).ok, false, "null params refused");
  assert.equal(parseOfferingTurnParams("x").ok, false, "non-object params refused");
});

test("valid params parse to the canonical bigint form; text defaults to null", () => {
  const r = parseOfferingTurnParams(GOOD);
  assert.equal(r.ok, true);
  assert.equal(r.params.counter, 7n);
  assert.equal(r.params.arg, 3n);
  assert.equal(r.params.text, null);
  // The parsed form is itself valid signingMessage input (what the background hands in).
  assert.deepEqual(Array.from(signingMessage(r.params)), Array.from(signingMessage(GOOD)));
});

test("counterWire: number while safe, decimal string beyond 2^53-1", () => {
  assert.equal(counterWire(7n), 7);
  assert.equal(counterWire(BigInt(Number.MAX_SAFE_INTEGER)), Number.MAX_SAFE_INTEGER);
  assert.equal(counterWire(18446744073709551615n), "18446744073709551615");
});

// ---------------------------------------------------------------------------
// Sign-then-verify round trip over the wire encoding — node:crypto Ed25519,
// the same independent verifier tests/passkey-sign/run.mjs grounds against.
// The extension signs with the wasm `sign_message` (SigningKey::from_bytes,
// i.e. RFC 8032 from a 32-byte seed); node:crypto implements the same scheme,
// so a seed-keyed round trip here exercises the exact verify relation
// `dreggnet-offerings::verify_signed` checks over these exact bytes.
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
  const pubkeyHex = spki.subarray(SPKI_ED25519_PREFIX.length).toString("hex");
  return { privateKey, pubkeyHex };
}

function verifyWire(params, wire) {
  const msg = signingMessage(params);
  const pub = createPublicKey({
    key: Buffer.concat([SPKI_ED25519_PREFIX, Buffer.from(wire.actorPubkeyHex, "hex")]),
    format: "der",
    type: "spki",
  });
  return edVerify(null, Buffer.from(msg), pub, Buffer.from(wire.signatureHex, "hex"));
}

test("sign-then-verify round trip over the SignedAction wire; tampering refuses", () => {
  const { privateKey, pubkeyHex } = keyFromSeed(7);
  const params = { offeringKey: "dungeon", sessionId: "sess-1", counter: 7, turn: "choose", arg: 3, text: "hello" };
  const msg = signingMessage(params);
  const signature = edSign(null, Buffer.from(msg), privateKey);
  assert.equal(signature.length, 64, "Ed25519 signature is 64 bytes");

  // The wire the extension returns: hex-encoded for JSON transport.
  const wire = {
    actorPubkeyHex: pubkeyHex,
    counter: 7,
    signatureHex: bytesToHex(new Uint8Array(signature)),
  };
  assert.equal(wire.actorPubkeyHex.length, 64);
  assert.equal(wire.signatureHex.length, 128);
  assert.equal(wire.signatureHex, wire.signatureHex.toLowerCase(), "wire hex is lowercase");

  // Round trip: hex → bytes → verify over the rebuilt canonical message.
  assert.equal(verifyWire(params, wire), true, "genuine wire verifies");

  // Each splice/tamper class the server's verify_signed refuses:
  assert.equal(verifyWire({ ...params, arg: 4 }, wire), false, "tampered arg refused");
  assert.equal(verifyWire({ ...params, sessionId: "sess-2" }, wire), false, "spliced session refused");
  assert.equal(verifyWire({ ...params, offeringKey: "council" }, wire), false, "spliced offering refused");
  assert.equal(verifyWire({ ...params, counter: 8 }, wire), false, "shifted counter refused");
  assert.equal(verifyWire({ ...params, text: "hellp" }, wire), false, "tampered text refused");
  assert.equal(verifyWire({ ...params, text: undefined }, wire), false, "dropped text refused");

  // Wrong key: an imposter's signature under the claimed pubkey refuses.
  const imposter = keyFromSeed(8);
  const forged = {
    actorPubkeyHex: pubkeyHex,
    counter: 7,
    signatureHex: bytesToHex(new Uint8Array(edSign(null, Buffer.from(msg), imposter.privateKey))),
  };
  assert.equal(verifyWire(params, forged), false, "imposter signature refused");
});

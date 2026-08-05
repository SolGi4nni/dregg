import assert from "node:assert/strict";
import { createHash, webcrypto } from "node:crypto";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  DEFAULT_GALLEY_ENDPOINTS,
  GalleyApiRefusal,
  POA_GALLEY_ACTOR_HEADER,
  POA_GALLEY_COMMAND_PREPARE_FORMAT,
  POA_GALLEY_SESSION_FORMAT,
  POA_GALLEY_STATUS_FORMAT,
  POA_GALLEY_UNSIGNED_TURN_FORMAT,
  checkGalleyReceiptPostcardSha256,
  createGalleyPendingIntentJournal,
  createGalleyTransport,
  galleyActorHeaders,
  normalizeGalleyActorIdentity,
  normalizeGalleySession,
  normalizeGalleySigningResult,
  normalizeGalleyStatus,
  normalizeGalleyUnsignedTurn,
  resolveSameOriginGalleyEndpoint,
} from "../src/galley-runtime.js";
import { renderGalleyWireFixture } from "./fixtures/galley-wire-v1.source.mjs";
import {
  GALLEY_FIXTURE_ORIGIN,
  GALLEY_WIRE_FIXTURE,
  GALLEY_WIRE_FIXTURE_URL,
  galleySession,
  galleyStatus,
  galleyUnsignedTurn,
} from "./galley-fixtures.mjs";

const VECTOR_SHA256 = "b7b1e149c9abd0896a100893ab06ef7a85664062eef1f5d1efb1912d9fa7686e";
const VECTOR_ACTOR = "ab".repeat(32);

function memoryStorage(initial = null) {
  let value = initial;
  return {
    getItem: () => value,
    setItem: (_key, next) => { value = next; },
    removeItem: () => { value = null; },
    value: () => value,
  };
}

function jsonResponse(payload, { status = 200 } = {}) {
  return {
    ok: status >= 200 && status < 300,
    status,
    headers: { get: (name) => name.toLowerCase() === "content-type" ? "application/json; charset=utf-8" : null },
    async json() { return structuredClone(payload); },
  };
}

function queuedFetch(responses, calls = []) {
  const queue = [...responses];
  return async (url, init) => {
    calls.push({ url: String(url), init });
    assert.ok(queue.length > 0, `unexpected request to ${url}`);
    return jsonResponse(queue.shift());
  };
}

test("Galley V1 uses one exact same-origin GET/prepare/status route set", () => {
  assert.deepEqual(DEFAULT_GALLEY_ENDPOINTS, {
    session: "/node/api/poa/galley/v1/session",
    command: "/node/api/poa/galley/v1/command",
    status: "/node/api/poa/galley/v1/status",
  });
  assert.equal(resolveSameOriginGalleyEndpoint(DEFAULT_GALLEY_ENDPOINTS.session, GALLEY_FIXTURE_ORIGIN),
    `${GALLEY_FIXTURE_ORIGIN}/node/api/poa/galley/v1/session`);
  assert.throws(
    () => resolveSameOriginGalleyEndpoint("https://node.attacker.invalid/api/poa/galley/v1/session", GALLEY_FIXTURE_ORIGIN),
    { code: "galley-origin" },
  );
});

test("public preparation actor is exact lowercase hex and cannot inject a hostile header", () => {
  assert.deepEqual(galleyActorHeaders(VECTOR_ACTOR), { [POA_GALLEY_ACTOR_HEADER]: VECTOR_ACTOR });
  assert.deepEqual(normalizeGalleyActorIdentity({ publicKeyHex: VECTOR_ACTOR, profileName: "expedition" }),
    { publicKeyHex: VECTOR_ACTOR, profileName: "expedition" });
  for (const hostile of [undefined, "", "AB".repeat(32), `${VECTOR_ACTOR}\r\nX-Devnet-Key: stolen`, "0".repeat(63)]) {
    assert.throws(() => galleyActorHeaders(hostile), { code: "galley-actor" });
  }
  assert.throws(() => normalizeGalleyActorIdentity({ publicKeyHex: VECTOR_ACTOR, authority: "finalized" }),
    { code: "galley-actor" });
});

test("byte-pinned fixture matches the extension's frozen uppercase wire constants", async () => {
  const raw = await readFile(GALLEY_WIRE_FIXTURE_URL);
  assert.equal(createHash("sha256").update(raw).digest("hex"), VECTOR_SHA256);
  assert.equal(raw.toString("utf8"), renderGalleyWireFixture(), "checked JSON is generated from the deterministic fixture source");
  assert.equal(GALLEY_WIRE_FIXTURE.session.format, POA_GALLEY_SESSION_FORMAT);
  assert.equal(GALLEY_WIRE_FIXTURE.status.format, POA_GALLEY_STATUS_FORMAT);
  assert.equal(GALLEY_WIRE_FIXTURE.prepare.format, POA_GALLEY_COMMAND_PREPARE_FORMAT);
  assert.equal(GALLEY_WIRE_FIXTURE.unsigned_turn.format, POA_GALLEY_UNSIGNED_TURN_FORMAT);

  const extension = await readFile(new URL("../../extension/src/poa-galley.ts", import.meta.url), "utf8");
  for (const format of [
    POA_GALLEY_SESSION_FORMAT,
    POA_GALLEY_STATUS_FORMAT,
    POA_GALLEY_COMMAND_PREPARE_FORMAT,
    POA_GALLEY_UNSIGNED_TURN_FORMAT,
  ]) assert.match(extension, new RegExp(format, "u"));
  assert.match(extension, /POA_GALLEY_API_PATH\s*=\s*"\/api\/poa\/galley\/v1"/u);
});

test("session and status are frozen projections with opaque JSON and exact events", () => {
  const session = normalizeGalleySession(galleySession());
  const status = normalizeGalleyStatus(galleyStatus());
  assert.equal(session.dailyId, "daily-119-third-watch");
  assert.deepEqual(session.actions.map(({ kind }) => kind), ["perform", "visit_commons", "public_vote"]);
  assert.deepEqual(session.projection, GALLEY_WIRE_FIXTURE.session.projection);
  assert.equal(status.events.length, 1);
  assert.equal(status.events[0].turnHash, "88".repeat(32));
  assert.equal(status.replay.eventCount, 1);
  assert.equal(status.replay.totalEventCount, 8);
  assert.equal(Object.isFrozen(session), true);
  assert.equal(Object.isFrozen(session.projection), true);
  assert.equal(Object.isFrozen(status.events), true);
});

test("strict decoder refuses parallel fields, duplicate actions, and broken journal counts", () => {
  const extra = galleySession();
  extra.player_public_key = "44".repeat(32);
  assert.throws(() => normalizeGalleySession(extra), { code: "galley-shape" });

  const duplicate = galleySession();
  duplicate.actions[1].action_token = duplicate.actions[0].action_token;
  assert.throws(() => normalizeGalleySession(duplicate), { code: "galley-actions" });

  const brokenCount = galleyStatus();
  brokenCount.replay.event_count = 2;
  assert.throws(() => normalizeGalleyStatus(brokenCount), { code: "galley-replay" });

  const brokenTotal = galleyStatus();
  brokenTotal.replay.total_event_count = 9;
  assert.throws(() => normalizeGalleyStatus(brokenTotal), { code: "galley-replay" });

  const brokenRange = galleyStatus();
  brokenRange.replay.from_sequence = 7;
  assert.throws(() => normalizeGalleyStatus(brokenRange), { code: "galley-replay" });

  const brokenHead = galleyStatus();
  brokenHead.replay.head_digest = "dd".repeat(32);
  assert.throws(() => normalizeGalleyStatus(brokenHead), { code: "galley-replay" });

  const brokenLastEvent = galleyStatus();
  brokenLastEvent.events[0].event_digest = "dd".repeat(32);
  assert.throws(() => normalizeGalleyStatus(brokenLastEvent), { code: "galley-replay" });

  const unordered = galleyStatus();
  unordered.events.push({ ...structuredClone(unordered.events[0]), sequence: 7 });
  unordered.replay.event_count = 2;
  unordered.replay.from_sequence = 7;
  assert.throws(() => normalizeGalleyStatus(unordered), { code: "galley-events" });
});

test("transport sends GET session, token-only prepare, exact postcard sign, and GET status", async () => {
  const calls = [];
  const transport = createGalleyTransport({
    origin: GALLEY_FIXTURE_ORIGIN,
    fetchImpl: queuedFetch([galleySession(), galleyUnsignedTurn(), galleyStatus()], calls),
    cryptoImpl: webcrypto,
  });
  const view = await transport.openSession(VECTOR_ACTOR);
  const prepared = await transport.requestCommand(view, "perform:vat-pressure:third-watch", VECTOR_ACTOR);
  assert.equal(prepared.kind, "signing");

  let signed = null;
  const provider = { async signTurnV3(turnBytes, federationId) {
    signed = { turnBytes: [...turnBytes], federationId: [...federationId] };
    return {
      turnId: prepared.signingRequest.turnHash,
      submitted: true,
      receipt: { turnHash: prepared.signingRequest.turnHash, proofStatus: "pending" },
    };
  } };
  const admission = await transport.sign(prepared.signingRequest, provider, view.sequence);
  const settled = await transport.status(prepared.signingRequest, VECTOR_ACTOR);

  assert.deepEqual(calls.map(({ init }) => init.method), ["GET", "POST", "GET"]);
  assert.equal("body" in calls[0].init, false);
  assert.deepEqual(calls.map(({ init }) => init.headers[POA_GALLEY_ACTOR_HEADER]),
    [VECTOR_ACTOR, VECTOR_ACTOR, VECTOR_ACTOR]);
  assert.deepEqual(JSON.parse(calls[1].init.body), GALLEY_WIRE_FIXTURE.prepare);
  assert.equal("player" in JSON.parse(calls[1].init.body), false);
  assert.equal("player_public_key" in JSON.parse(calls[1].init.body), false);
  assert.equal("body" in calls[2].init, false);
  assert.deepEqual(signed, { turnBytes: [1, 2, 3, 4], federationId: Array(32).fill(0x55) });
  assert.deepEqual(admission, {
    state: "submitted",
    turnHash: prepared.signingRequest.turnHash,
    outboxId: null,
    error: null,
  });
  assert.equal(settled.state, "settled");
  assert.equal(settled.receiptChecksumMatched, true);
  assert.equal(settled.event.turnHash, prepared.signingRequest.turnHash);
});

test("signing result binds signed and receipt turn hashes, and preserves every admission state", async () => {
  const request = normalizeGalleyUnsignedTurn(galleyUnsignedTurn());
  const expected = request.turnHash;
  assert.deepEqual(normalizeGalleySigningResult({ turnId: expected, submitted: true, receipt: { turnHash: expected } }, expected), {
    state: "submitted", turnHash: expected, outboxId: null, error: null,
  });
  assert.deepEqual(normalizeGalleySigningResult({
    turnId: expected, submitted: false, queued: true, outboxId: "outbox-17", error: "Queued for retry",
  }, expected), {
    state: "queued", turnHash: expected, outboxId: "outbox-17", error: "Queued for retry",
  });
  assert.deepEqual(normalizeGalleySigningResult({ submitted: false, error: "Node refused turn" }, expected), {
    state: "refused", turnHash: null, outboxId: null, error: "Node refused turn",
  });
  assert.deepEqual(normalizeGalleySigningResult({ submitted: false, error: "User declined to sign this turn" }, expected), {
    state: "declined", turnHash: null, outboxId: null, error: "User declined to sign this turn",
  });

  for (const hostile of [
    { submitted: true },
    { turnId: "ef".repeat(32), submitted: true },
    { turnId: expected, submitted: true, receipt: { turnHash: "ef".repeat(32) } },
    { turnId: expected, submitted: true, nodeResult: { turn_hash: "ef".repeat(32) } },
    { turnId: expected, submitted: true, queued: true },
    { turnId: expected, submitted: "yes" },
    { turnId: expected, submitted: true, authoritative: true },
  ]) assert.throws(() => normalizeGalleySigningResult(hostile, expected), GalleyApiRefusal);
});

test("transport turns mismatched, declined, refused, and thrown signer reports into non-pollable outcomes", async () => {
  const request = normalizeGalleyUnsignedTurn(galleyUnsignedTurn());
  const transport = createGalleyTransport({ origin: GALLEY_FIXTURE_ORIGIN, fetchImpl: queuedFetch([]) });
  const cases = [
    [{ turnId: "ef".repeat(32), submitted: true }, "error"],
    [{ submitted: false, error: "User declined to sign this turn" }, "declined"],
    [{ submitted: false, error: "Cipherclerk is locked" }, "refused"],
  ];
  for (const [raw, state] of cases) {
    const outcome = await transport.sign(request, { async signTurnV3() { return raw; } }, 7);
    assert.equal(outcome.state, state);
  }
  const thrown = await transport.sign(request, { async signTurnV3() { throw new Error("bridge disconnected"); } }, 7);
  assert.deepEqual(thrown, { state: "error", turnHash: null, outboxId: null, error: "bridge disconnected" });
});

test("holder sponsorship and caller-authored identity are absent from command preparation", async () => {
  const holderSession = galleySession();
  holderSession.actions.push({
    kind: "holder_sponsorship",
    action_token: "holder:forged-local-cert",
    expires_after_sequence: 7,
  });
  const calls = [];
  const transport = createGalleyTransport({
    origin: GALLEY_FIXTURE_ORIGIN,
    fetchImpl: queuedFetch([holderSession], calls),
  });
  const view = await transport.openSession(VECTOR_ACTOR);
  await assert.rejects(transport.requestCommand(view, "holder:forged-local-cert", VECTOR_ACTOR),
    { code: "galley-holder-cert" });
  assert.equal(calls.length, 1, "refusal occurs before a command request");
});

test("missing or malformed actor refuses before fetch on every Galley read/write route", async () => {
  const calls = [];
  const transport = createGalleyTransport({
    origin: GALLEY_FIXTURE_ORIGIN,
    fetchImpl: queuedFetch([], calls),
  });
  await assert.rejects(transport.openSession(), { code: "galley-actor" });
  await assert.rejects(transport.openSession("AB".repeat(32)), { code: "galley-actor" });
  const view = normalizeGalleySession(galleySession());
  await assert.rejects(transport.requestCommand(view, "perform:vat-pressure:third-watch"), { code: "galley-actor" });
  await assert.rejects(transport.status(normalizeGalleyUnsignedTurn(galleyUnsignedTurn())), { code: "galley-actor" });
  assert.deepEqual(calls, []);
});

test("adjacent receipt-postcard checksum is exact but makes no canonical receipt claim", async () => {
  const status = normalizeGalleyStatus(galleyStatus());
  assert.equal(await checkGalleyReceiptPostcardSha256(status.events[0], webcrypto), true);
  const altered = structuredClone(galleyStatus());
  altered.events[0].receipt.sha256 = "00".repeat(32);
  assert.equal(await checkGalleyReceiptPostcardSha256(normalizeGalleyStatus(altered).events[0], webcrypto), false);
});

test("pending journal persists before signing and reconciles only exact receipt or sequence expiry", () => {
  const storage = memoryStorage();
  const journal = createGalleyPendingIntentJournal({ storage });
  const session = normalizeGalleySession(galleySession());
  const prepared = normalizeGalleyUnsignedTurn(galleyUnsignedTurn());
  const pending = journal.record(session, prepared);
  assert.equal(journal.list().length, 1);
  assert.equal(pending.turnHash, prepared.turnHash);
  assert.equal("turnPostcardBase64" in pending, false, "journal is intent continuity, not a game-state or signing-byte twin");

  const unrelated = normalizeGalleyStatus({
    ...galleyStatus(),
    events: [{ ...galleyStatus().events[0], turn_hash: "ef".repeat(32) }],
  });
  assert.equal(journal.reconcile(unrelated).pending.length, 0, "sequence expiry clears an unobserved exact-world intent");
  assert.equal(journal.reconcile(unrelated).settled.length, 0);

  journal.record(session, prepared);
  const settled = normalizeGalleyStatus(galleyStatus());
  const result = journal.reconcile(settled);
  assert.equal(result.settled.length, 1);
  assert.equal(result.expired.length, 0);
  assert.equal(journal.list().length, 0);

  const hostile = JSON.parse(storage.value());
  hostile.entries = [{ ...pendingWireForTest(pending), turn_hash: "not-a-hash" }];
  storage.setItem("ignored", JSON.stringify(hostile));
  assert.deepEqual(journal.list(), [], "malformed durable journal is cleared, never repaired");
});

function pendingWireForTest(intent) {
  return {
    federation_id: intent.federationId,
    daily_id: intent.dailyId,
    aggregate_id: intent.aggregateId,
    intent_id: intent.intentId,
    turn_hash: intent.turnHash,
    prepared_at_sequence: intent.preparedAtSequence,
    expires_after_sequence: intent.expiresAfterSequence,
  };
}

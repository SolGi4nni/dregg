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
  checkGalleyPreparationPostcardSha256,
  checkGalleyReceiptPostcardSha256,
  createGalleyPendingIntentJournal,
  createGalleyTransport,
  galleyActorHeaders,
  normalizeGalleyActorIdentity,
  normalizeGalleySession,
  normalizeGalleySigningResult,
  normalizeGalleyStatus,
  normalizeGalleyUnsignedTurn,
  projectGalleyWatch,
  resolveSameOriginGalleyEndpoint,
} from "../src/galley-runtime.js";
import { renderGalleyWireFixture } from "./fixtures/galley-wire-v1.source.mjs";
import {
  GALLEY_ACTOR_PUBLIC_KEY,
  GALLEY_FIXTURE_ORIGIN,
  GALLEY_WIRE_FIXTURE,
  GALLEY_WIRE_FIXTURE_URL,
  galleySession,
  galleyStatus,
  galleyStatusBefore,
  galleyUnsignedTurn,
} from "./galley-fixtures.mjs";

const VECTOR_SHA256 = "8079046c826ed0b9f2ce2bdd241d4e9333940865a803828422649c45827ba29f";
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

test("Galley uses the exact same-origin watch, prepare, and status routes", () => {
  assert.deepEqual(DEFAULT_GALLEY_ENDPOINTS, {
    session: "/node/api/poa/galley/v1/session",
    command: "/node/api/poa/galley/v1/command",
    status: "/node/api/poa/galley/v1/status",
  });
  assert.equal(resolveSameOriginGalleyEndpoint(DEFAULT_GALLEY_ENDPOINTS.status, GALLEY_FIXTURE_ORIGIN),
    `${GALLEY_FIXTURE_ORIGIN}/node/api/poa/galley/v1/status`);
  assert.throws(
    () => resolveSameOriginGalleyEndpoint("https://node.attacker.invalid/api/poa/galley/v1/status", GALLEY_FIXTURE_ORIGIN),
    { code: "galley-origin" },
  );
});

test("public preparation actor is exact lowercase hex and never upgrades into authority", () => {
  assert.deepEqual(galleyActorHeaders(VECTOR_ACTOR), { [POA_GALLEY_ACTOR_HEADER]: VECTOR_ACTOR });
  assert.deepEqual(normalizeGalleyActorIdentity({ publicKeyHex: VECTOR_ACTOR, profileName: "expedition" }),
    { publicKeyHex: VECTOR_ACTOR, profileName: "expedition" });
  for (const hostile of [undefined, "", "AB".repeat(32), `${VECTOR_ACTOR}\r\nX-Devnet-Key: stolen`, "0".repeat(63)]) {
    assert.throws(() => galleyActorHeaders(hostile), { code: "galley-actor" });
  }
  assert.throws(() => normalizeGalleyActorIdentity({ publicKeyHex: VECTOR_ACTOR, authority: "finalized" }),
    { code: "galley-actor" });
});

test("byte-pinned fixture matches deterministic source and the current preparation-digest wire", async () => {
  const raw = await readFile(GALLEY_WIRE_FIXTURE_URL);
  assert.equal(createHash("sha256").update(raw).digest("hex"), VECTOR_SHA256);
  assert.equal(raw.toString("utf8"), renderGalleyWireFixture());
  assert.equal(GALLEY_WIRE_FIXTURE.session.format, POA_GALLEY_SESSION_FORMAT);
  assert.equal(GALLEY_WIRE_FIXTURE.status.format, POA_GALLEY_STATUS_FORMAT);
  assert.equal(GALLEY_WIRE_FIXTURE.prepare.format, POA_GALLEY_COMMAND_PREPARE_FORMAT);
  assert.equal(GALLEY_WIRE_FIXTURE.unsigned_turn.format, POA_GALLEY_UNSIGNED_TURN_FORMAT);
  assert.equal("preparation_digest" in GALLEY_WIRE_FIXTURE.unsigned_turn, true);
  assert.equal("turn_hash" in GALLEY_WIRE_FIXTURE.unsigned_turn, false);
});

test("exact replay projection becomes an available then recorded recurring watch", () => {
  const before = normalizeGalleyStatus(galleyStatusBefore());
  const available = projectGalleyWatch(before, GALLEY_ACTOR_PUBLIC_KEY);
  assert.equal(available.state, "available");
  assert.equal(available.availableActions.length, 1);
  assert.equal(available.publicPlayCount, 1);
  assert.equal(available.localServiceTotal, 3);
  assert.equal(available.personalRecords.length, 0);
  assert.match(available.nextVisit, /station is open/i);

  const after = normalizeGalleyStatus(galleyStatus());
  const recorded = projectGalleyWatch(after, GALLEY_ACTOR_PUBLIC_KEY);
  assert.equal(recorded.state, "recorded");
  assert.equal(recorded.availableActions.length, 0);
  assert.equal(recorded.publicPlayCount, 2);
  assert.equal(recorded.localServiceTotal, 6);
  assert.deepEqual(recorded.personalRecords.map(({ sequence, localService }) => ({ sequence, localService })),
    [{ sequence: 2, localService: 3 }]);
  assert.match(recorded.nextVisit, /watch rotates/i);
});

test("unaudited event arrays are inert and cannot create a player record or settled intent", () => {
  const raw = galleyStatus();
  raw.replay.audited = false;
  const view = normalizeGalleyStatus(raw);
  const watch = projectGalleyWatch(view, GALLEY_ACTOR_PUBLIC_KEY);
  assert.equal(watch.state, "unavailable");
  assert.equal(watch.participated, false);
  assert.equal(watch.publicPlayCount, null);
  assert.equal(watch.localServiceTotal, null);
  assert.deepEqual(watch.availableActions, []);
  assert.deepEqual(watch.records, []);
  assert.deepEqual(watch.personalRecords, []);
  assert.match(watch.nextVisit, /audited replay/i);
  assert.doesNotMatch(watch.nextVisit, /recorded for this daily|return after the watch rotates/i);

  for (const finalTurnHash of ["88".repeat(32), "ef".repeat(32)]) {
    const storage = memoryStorage();
    const journal = createGalleyPendingIntentJournal({ storage });
    const pending = journal.record(normalizeGalleyStatus(galleyStatusBefore()), normalizeGalleyUnsignedTurn(galleyUnsignedTurn()));
    journal.confirm(pending, finalTurnHash);
    const beforeBytes = storage.value();
    const outcome = journal.reconcile(view);
    assert.equal(outcome.settled.length, 0, "an unaudited matching event cannot settle a durable intent");
    assert.equal(outcome.expired.length, 0, "an unaudited later sequence cannot expire a durable intent");
    assert.equal(outcome.pending.length, 1);
    assert.equal(outcome.replayRefused.length, 1);
    assert.equal(storage.value(), beforeBytes,
      "matching and nonmatching unaudited events must preserve pending storage byte-for-byte");
  }
});

test("status transport explicitly preserves pending on an advanced unaudited replay", async () => {
  const raw = galleyStatus();
  raw.replay.audited = false;
  for (const finalTurnHash of ["88".repeat(32), "ef".repeat(32)]) {
    const transport = createGalleyTransport({
      origin: GALLEY_FIXTURE_ORIGIN,
      fetchImpl: queuedFetch([raw]),
      cryptoImpl: webcrypto,
    });
    const pending = {
      federationId: GALLEY_WIRE_FIXTURE.unsigned_turn.federation_id,
      dailyId: GALLEY_WIRE_FIXTURE.status.daily_id,
      aggregateId: GALLEY_WIRE_FIXTURE.status.aggregate_id,
      finalTurnHash,
      expiresAfterSequence: 1,
    };
    const result = await transport.status(pending, VECTOR_ACTOR);
    assert.equal(result.state, "replay-refused");
    assert.equal(result.event, null);
    assert.equal(result.view.sequence, 2);
  }
});

test("session and status are deeply frozen exact schemas, not arbitrary JSON authority", () => {
  const session = normalizeGalleySession(galleySession());
  const status = normalizeGalleyStatus(galleyStatus());
  assert.equal(session.projection.publicPlayCount, 1);
  assert.deepEqual(session.actions.map(({ kind }) => kind), ["perform"]);
  assert.equal(status.events.length, 2);
  assert.equal(status.events[1].payload.kind, "public-play");
  assert.equal(status.events[1].payload.actor, GALLEY_ACTOR_PUBLIC_KEY);
  assert.equal(Object.isFrozen(session.projection.publicPlayers), true);
  assert.equal(Object.isFrozen(status.events[1].payload), true);
});

test("strict decoder refuses presentation drift, unactivated actions, and replay lies", () => {
  const extraProjection = galleyStatusBefore();
  extraProjection.projection.summary = "caller-authored story";
  assert.throws(() => normalizeGalleyStatus(extraProjection), { code: "galley-shape" });

  const oldAction = galleyStatusBefore();
  oldAction.actions[0].action_token = "perform:vat-pressure";
  assert.throws(() => normalizeGalleyStatus(oldAction), { code: "galley-digest" });

  const sponsor = galleyStatusBefore();
  sponsor.actions[0].kind = "holder_sponsorship";
  assert.throws(() => normalizeGalleyStatus(sponsor), { code: "galley-action" });

  const countLie = galleyStatusBefore();
  countLie.projection.public_play_count = 2;
  assert.throws(() => normalizeGalleyStatus(countLie), { code: "galley-projection" });

  const actorLie = galleyStatus();
  actorLie.events[1].payload.beneficiary = "ef".repeat(32);
  assert.throws(() => normalizeGalleyStatus(actorLie), { code: "galley-event" });

  const replayLie = galleyStatus();
  replayLie.replay.head_digest = "ef".repeat(32);
  assert.throws(() => normalizeGalleyStatus(replayLie), { code: "galley-replay" });
});

test("transport reads full watch, prepares token-only, checks postcard digest, signs, then reconciles final hash", async () => {
  const calls = [];
  const transport = createGalleyTransport({
    origin: GALLEY_FIXTURE_ORIGIN,
    fetchImpl: queuedFetch([galleyStatusBefore(), galleyUnsignedTurn(), galleyStatus()], calls),
    cryptoImpl: webcrypto,
  });
  const view = await transport.openWatch(VECTOR_ACTOR);
  const token = GALLEY_WIRE_FIXTURE.prepare.action_token;
  const prepared = await transport.requestCommand(view, token, VECTOR_ACTOR);
  let signed = null;
  const provider = { async signTurnV3(turnBytes, federationId) {
    signed = { turnBytes: [...turnBytes], federationId: [...federationId] };
    return { turnId: "88".repeat(32), submitted: true, receipt: { turnHash: "88".repeat(32) } };
  } };
  const admission = await transport.sign(prepared.signingRequest, provider, view.sequence);
  const storage = memoryStorage();
  const journal = createGalleyPendingIntentJournal({ storage });
  const pending = journal.confirm(journal.record(view, prepared.signingRequest), admission.turnHash);
  const settled = await transport.status(pending, VECTOR_ACTOR);

  assert.deepEqual(calls.map(({ init }) => init.method), ["GET", "POST", "GET"]);
  assert.deepEqual(JSON.parse(calls[1].init.body), GALLEY_WIRE_FIXTURE.prepare);
  assert.deepEqual(calls.map(({ init }) => init.headers[POA_GALLEY_ACTOR_HEADER]),
    [VECTOR_ACTOR, VECTOR_ACTOR, VECTOR_ACTOR]);
  assert.deepEqual(signed, { turnBytes: [1, 2, 3, 4], federationId: Array(32).fill(0x55) });
  assert.equal(admission.turnHash, "88".repeat(32));
  assert.notEqual(admission.turnHash, prepared.signingRequest.preparationDigest);
  assert.equal(settled.state, "settled");
  assert.equal(settled.event.turnHash, admission.turnHash);
});

test("preparation digest is recomputed before custody and mismatch never invokes signer", async () => {
  const request = galleyUnsignedTurn();
  request.preparation_digest = "ef".repeat(32);
  const prepared = normalizeGalleyUnsignedTurn(request);
  assert.equal(await checkGalleyPreparationPostcardSha256(prepared, webcrypto), false);
  let invoked = false;
  const transport = createGalleyTransport({ origin: GALLEY_FIXTURE_ORIGIN, fetchImpl: queuedFetch([]), cryptoImpl: webcrypto });
  const outcome = await transport.sign(prepared, { async signTurnV3() { invoked = true; } }, 1);
  assert.equal(outcome.state, "error");
  assert.match(outcome.error, /galley-preparation-digest/);
  assert.equal(invoked, false);
});

test("signing result treats final signed hash as distinct and binds receipt or node reports to it", () => {
  const finalHash = "88".repeat(32);
  assert.deepEqual(normalizeGalleySigningResult({ turnId: finalHash, submitted: true, receipt: { turnHash: finalHash } }), {
    state: "submitted", turnHash: finalHash, outboxId: null, error: null,
  });
  assert.deepEqual(normalizeGalleySigningResult({
    turnId: finalHash, submitted: false, queued: true, outboxId: "outbox-17", error: "Queued for retry",
  }), { state: "queued", turnHash: finalHash, outboxId: "outbox-17", error: "Queued for retry" });
  for (const hostile of [
    { submitted: true },
    { turnId: "not-a-hash", submitted: true },
    { turnId: finalHash, submitted: true, receipt: { turnHash: "ef".repeat(32) } },
    { turnId: finalHash, submitted: true, nodeResult: { turn_hash: "ef".repeat(32) } },
    { turnId: finalHash, submitted: true, queued: true },
    { turnId: finalHash, submitted: true, authoritative: true },
  ]) assert.throws(() => normalizeGalleySigningResult(hostile), GalleyApiRefusal);
});

test("pending recovery stores preparation first, then durably attaches only signer final hash", () => {
  const storage = memoryStorage();
  const journal = createGalleyPendingIntentJournal({ storage });
  const view = normalizeGalleyStatus(galleyStatusBefore());
  const prepared = normalizeGalleyUnsignedTurn(galleyUnsignedTurn());
  const pending = journal.record(view, prepared);
  assert.equal(pending.preparationDigest, prepared.preparationDigest);
  assert.equal(pending.finalTurnHash, null);
  assert.equal("turnPostcardBase64" in pending, false);
  assert.equal(journal.reconcile(normalizeGalleyStatus(galleyStatus())).settled.length, 0,
    "a preparation digest cannot be mistaken for a finalized turn hash");

  const preparedAgain = journal.record(view, prepared);
  const confirmed = journal.confirm(preparedAgain, "88".repeat(32));
  assert.equal(confirmed.finalTurnHash, "88".repeat(32));
  const reopened = createGalleyPendingIntentJournal({ storage });
  assert.equal(reopened.list()[0].finalTurnHash, "88".repeat(32));
  assert.equal(reopened.reconcile(normalizeGalleyStatus(galleyStatus())).settled.length, 1);
  assert.equal(reopened.list().length, 0);
});

test("pending journal refuses unavailable or failed durable storage", () => {
  const view = normalizeGalleyStatus(galleyStatusBefore());
  const prepared = normalizeGalleyUnsignedTurn(galleyUnsignedTurn());
  assert.throws(() => createGalleyPendingIntentJournal({ storage: null }).record(view, prepared),
    { code: "galley-pending-storage" });
  const quotaStorage = {
    getItem: () => null,
    setItem() { throw new Error("quota exceeded"); },
    removeItem() {},
  };
  assert.throws(() => createGalleyPendingIntentJournal({ storage: quotaStorage }).record(view, prepared),
    { code: "galley-pending-storage" });
});

test("prepared-only response loss remains explicit until sequence expiry", () => {
  const storage = memoryStorage();
  const journal = createGalleyPendingIntentJournal({ storage });
  journal.record(normalizeGalleyStatus(galleyStatusBefore()), normalizeGalleyUnsignedTurn(galleyUnsignedTurn()));
  const sameHead = journal.reconcile(normalizeGalleyStatus(galleyStatusBefore()));
  assert.equal(sameHead.pending.length, 1);
  assert.equal(sameHead.settled.length, 0);
  const nextHead = journal.reconcile(normalizeGalleyStatus(galleyStatus()));
  assert.equal(nextHead.expired.length, 1);
  assert.equal(nextHead.replayRefused.length, 0);
  assert.equal(journal.list().length, 0);
});

test("final hash recovery survives a lost status response and settles on restart", () => {
  const storage = memoryStorage();
  const first = createGalleyPendingIntentJournal({ storage });
  const prepared = first.record(normalizeGalleyStatus(galleyStatusBefore()), normalizeGalleyUnsignedTurn(galleyUnsignedTurn()));
  first.confirm(prepared, "88".repeat(32));
  const restarted = createGalleyPendingIntentJournal({ storage });
  const recovered = restarted.list()[0];
  assert.equal(recovered.finalTurnHash, "88".repeat(32));
  const outcome = restarted.reconcile(normalizeGalleyStatus(galleyStatus()));
  assert.equal(outcome.settled.length, 1);
});

test("adjacent receipt postcard checksum is exact but never canonical receipt verification", async () => {
  const status = normalizeGalleyStatus(galleyStatus());
  assert.equal(await checkGalleyReceiptPostcardSha256(status.events[1], webcrypto), true);
  const altered = galleyStatus();
  altered.events[1].receipt.sha256 = "00".repeat(32);
  assert.equal(await checkGalleyReceiptPostcardSha256(normalizeGalleyStatus(altered).events[1], webcrypto), false);
});

test("empty watch renders a waiting projection without fabricating a record", () => {
  const empty = galleyStatusBefore();
  empty.sequence = 0;
  empty.semantic_head = "00".repeat(32);
  empty.projection.sequence = 0;
  empty.projection.public_players = [];
  empty.projection.public_play_count = 0;
  empty.projection.local_service_total = 0;
  empty.actions = [];
  empty.replay = { audited: true, event_count: 0, total_event_count: 0, from_sequence: 0, through_sequence: 0, head_digest: "00".repeat(32) };
  empty.events = [];
  const watch = projectGalleyWatch(normalizeGalleyStatus(empty), GALLEY_ACTOR_PUBLIC_KEY);
  assert.equal(watch.state, "waiting");
  assert.deepEqual(watch.records, []);
  assert.match(watch.nextVisit, /No station is open/);
});

test("presentation refuses a node view that both records and re-offers the same actor", () => {
  const hostile = galleyStatus();
  hostile.actions = [{ kind: "perform", action_token: "11".repeat(32), expires_after_sequence: 2 }];
  const view = normalizeGalleyStatus(hostile);
  assert.throws(() => projectGalleyWatch(view, GALLEY_ACTOR_PUBLIC_KEY), { code: "galley-presentation" });
});

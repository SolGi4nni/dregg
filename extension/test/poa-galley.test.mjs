import test from "node:test";
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";

import {
  POA_GALLEY_ACTOR_HEADER,
  POA_GALLEY_COMMAND_PREPARE_FORMAT,
  checkPoAGalleyReceiptPostcardSha256,
  decodePoAGalleyPostcard,
  findPoAGalleyAction,
  findPoAGalleyEvent,
  makePoAGalleyPendingIntent,
  makePoAGalleyPrepare,
  parsePoAGalleyPendingJournal,
  parsePoAGalleySession,
  parsePoAGalleyStatus,
  parsePoAGalleyUnsignedTurn,
  poAGalleyActionLabel,
  poAGalleyActorHeaders,
  poAGalleyAvailableAtSequence,
  reconcilePoAGalleyPendingIntents,
} from "./.build/poa-galley.mjs";

const H = (byte) => byte.repeat(64);
const ACTOR = "ab".repeat(32);

test("actor header is a canonical public preparation claim, never page-owned authority", async () => {
  assert.deepEqual(poAGalleyActorHeaders(ACTOR), { [POA_GALLEY_ACTOR_HEADER]: ACTOR });
  for (const hostile of [undefined, null, "AB".repeat(32), `${ACTOR}\r\nAuthorization: hostile`, "0".repeat(63)]) {
    assert.equal(poAGalleyActorHeaders(hostile), null);
  }

  const background = await readFile(new URL("../src/background.ts", import.meta.url), "utf8");
  assert.equal(background.match(/headers: actorHeaders/g)?.length, 3,
    "status, session, and command attach the one background-resolved actor header");
  assert.match(background, /poAGalleyActorHeaders\(identity\.publicKeyHex\)/);
  assert.match(background, /preparation identity is background-owned and cannot be supplied by the page/);
  assert.ok(background.indexOf("const identity = await getActiveIdentity()") < background.indexOf("const sessionResponse = await nodeRequest"),
    "background resolves the active identity before Galley session preparation");
});

test("extension consumes the byte-pinned source-built web Galley fixture", async () => {
  const raw = await readFile(new URL("../../poa-web/tests/fixtures/galley-wire-v1.json", import.meta.url));
  assert.equal(createHash("sha256").update(raw).digest("hex"),
    "b7b1e149c9abd0896a100893ab06ef7a85664062eef1f5d1efb1912d9fa7686e");
  const fixture = JSON.parse(raw);
  assert.ok(parsePoAGalleySession(fixture.session));
  assert.ok(parsePoAGalleyStatus(fixture.status));
  assert.ok(parsePoAGalleyUnsignedTurn(fixture.unsigned_turn));
  assert.deepEqual(makePoAGalleyPrepare(fixture.prepare.action_token), fixture.prepare);
});

function replay(count = 1) {
  return {
    audited: true,
    event_count: count,
    total_event_count: 7,
    from_sequence: count ? 7 : 0,
    through_sequence: count ? 7 : 0,
    head_digest: H("6"),
  };
}

function current(format = "POA-GALLEY-SESSION-V1") {
  return {
    format,
    federation_id: H("1"),
    daily_id: "galley:daily:2044-03-19",
    aggregate_id: "khv:galley",
    schema_version: 1,
    sequence: 7,
    semantic_head: H("6"),
    projection_digest: H("3"),
    projection: {
      deliberately_opaque: true,
      progress_current: 3,
      nested: ["server-authored", { score_the_browser_must_not_recompute: 19 }],
    },
    actions: [
      { kind: "public_vote", action_token: "opaque.public.7", expires_after_sequence: 7 },
      { kind: "perform", action_token: "opaque.perform.7", expires_after_sequence: 7 },
      { kind: "visit_commons", action_token: "opaque.commons.7", expires_after_sequence: 7 },
      { kind: "holder_sponsorship", action_token: "opaque.holder.7", expires_after_sequence: 7 },
    ],
    replay: replay(),
  };
}

function event(turn = H("b")) {
  return {
    sequence: 7,
    turn_hash: turn,
    receipt_hash: H("5"),
    event_digest: H("6"),
    payload_digest: H("7"),
    payload: { source: "lean-journal", power_delta: 0 },
    receipt: { index: 12, postcard_base64: "AQIDBA==", sha256: "9f64a747e1b97f131fabb6b447296c9b6f0201e79fb3c5356e6c77e89b6a806a" },
  };
}

test("strict session preserves server projection as opaque data and only admits frozen action kinds", () => {
  const parsed = parsePoAGalleySession(current());
  assert.ok(parsed);
  assert.equal(parsed.projection.nested[1].score_the_browser_must_not_recompute, 19);
  assert.equal(findPoAGalleyAction(parsed, "opaque.commons.7")?.kind, "visit_commons");
  assert.equal(findPoAGalleyAction(parsed, "missing"), null);
  assert.equal(poAGalleyActionLabel(parsed.actions[0].kind), "Cast public vote");

  assert.equal(parsePoAGalleySession({ ...current(), browser_score: 999 }), null, "unknown top-level authority is refused");
  assert.equal(parsePoAGalleySession({ ...current(), format: "POA-GALLEY-SESSION-V2" }), null);
  assert.equal(parsePoAGalleySession({ ...current(), actions: [{ kind: "mint_relic", action_token: "x", expires_after_sequence: 9 }] }), null);
  assert.equal(parsePoAGalleySession({ ...current(), actions: [current().actions[0], current().actions[0]] }), null, "duplicate bearer actions are refused");
});

test("status requires the exact audited replay envelope and finds receipts only by exact turn hash", async () => {
  const turn = H("b");
  const parsed = parsePoAGalleyStatus({ ...current("POA-GALLEY-STATUS-V1"), events: [event(turn)] });
  assert.ok(parsed);
  assert.equal(findPoAGalleyEvent(parsed, turn)?.receipt.sha256, "9f64a747e1b97f131fabb6b447296c9b6f0201e79fb3c5356e6c77e89b6a806a");
  assert.equal(await checkPoAGalleyReceiptPostcardSha256(findPoAGalleyEvent(parsed, turn)), true);
  assert.equal(await checkPoAGalleyReceiptPostcardSha256({ ...findPoAGalleyEvent(parsed, turn), receipt: { ...findPoAGalleyEvent(parsed, turn).receipt, sha256: H("8") } }), false);
  assert.equal(findPoAGalleyEvent(parsed, H("9")), null);
  assert.equal(findPoAGalleyEvent(parsed, turn.toUpperCase()), null, "wire hashes are canonical lowercase");

  const missingAuditCoordinate = { ...replay() };
  delete missingAuditCoordinate.head_digest;
  assert.equal(parsePoAGalleyStatus({ ...current("POA-GALLEY-STATUS-V1"), replay: missingAuditCoordinate, events: [event()] }), null);
  assert.equal(parsePoAGalleyStatus({ ...current("POA-GALLEY-STATUS-V1"), events: [event(), { ...event(H("9")), sequence: 6 }], replay: replay(2) }), null, "journal order is not repaired in-browser");
  assert.equal(parsePoAGalleyStatus({ ...current("POA-GALLEY-STATUS-V1"), events: [], replay: replay(1) }), null, "event count is exact");
  assert.equal(parsePoAGalleyStatus({ ...current("POA-GALLEY-STATUS-V1"), semantic_head: H("9"), events: [event()] }), null, "semantic head binds replay and last event");
  assert.equal(parsePoAGalleyStatus({ ...current("POA-GALLEY-STATUS-V1"), replay: { ...replay(), total_event_count: 8 }, events: [event()] }), null, "total count binds current sequence");
  assert.equal(parsePoAGalleyStatus({ ...current("POA-GALLEY-STATUS-V1"), replay: { ...replay(), from_sequence: 6 }, events: [event()] }), null, "range binds returned first event");
});

test("prepare carries no V1 holding receipt and unsigned turns are byte-bounded and exact", () => {
  assert.deepEqual(makePoAGalleyPrepare("opaque.perform.7"), {
    format: POA_GALLEY_COMMAND_PREPARE_FORMAT,
    action_token: "opaque.perform.7",
  });
  assert.equal(makePoAGalleyPrepare("contains whitespace"), null);

  const unsigned = parsePoAGalleyUnsignedTurn({
    format: "POA-GALLEY-UNSIGNED-TURN-V1",
    intent_id: "intent-7",
    federation_id: H("1"),
    turn_hash: H("b"),
    turn_postcard_base64: "AQIDBA==",
    expires_after_sequence: 7,
  });
  assert.ok(unsigned);
  assert.deepEqual([...decodePoAGalleyPostcard(unsigned.turn_postcard_base64)], [1, 2, 3, 4]);
  assert.equal(parsePoAGalleyUnsignedTurn({ ...unsigned, holding_receipt_id: "unsafe-v1" }), null);
  assert.equal(parsePoAGalleyUnsignedTurn({ ...unsigned, turn_postcard_base64: "not base64" }), null);
  assert.equal(poAGalleyAvailableAtSequence(unsigned.expires_after_sequence, 7), true);
  assert.equal(poAGalleyAvailableAtSequence(unsigned.expires_after_sequence, 8), false);
});

test("pending intent coordinates survive restart and reconcile only by exact turn or sequence expiry", () => {
  const session = parsePoAGalleySession(current());
  const prepared = parsePoAGalleyUnsignedTurn({
    format: "POA-GALLEY-UNSIGNED-TURN-V1",
    intent_id: "intent-7",
    federation_id: H("1"),
    turn_hash: H("b"),
    turn_postcard_base64: "AQIDBA==",
    expires_after_sequence: 7,
  });
  const pending = makePoAGalleyPendingIntent(session, prepared);
  assert.ok(pending);
  const journal = parsePoAGalleyPendingJournal({ format: "POA-GALLEY-PENDING-INTENT-JOURNAL-V1", entries: [pending] });
  assert.ok(journal);
  const status = parsePoAGalleyStatus({ ...current("POA-GALLEY-STATUS-V1"), events: [event(H("b"))] });
  assert.equal(reconcilePoAGalleyPendingIntents(journal.entries, status).observed.length, 1);

  const advanced = parsePoAGalleyStatus({
    ...current("POA-GALLEY-STATUS-V1"),
    sequence: 8,
    semantic_head: H("8"),
    replay: { audited: true, event_count: 1, total_event_count: 8, from_sequence: 8, through_sequence: 8, head_digest: H("8") },
    events: [{ ...event(H("9")), sequence: 8, event_digest: H("8") }],
  });
  assert.equal(reconcilePoAGalleyPendingIntents(journal.entries, advanced).expired.length, 1);
});

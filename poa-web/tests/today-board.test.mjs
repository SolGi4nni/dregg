import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { test } from "node:test";
import {
  CRATE_SURFACE,
  buildTodayBoard,
  loadSlotState,
  mountTodayBoard,
  parseSlotDocument,
  slotStatementMessage,
} from "../src/today-board.js";
import { readyStation } from "./station-fixtures.mjs";

class FakeElement {
  constructor(tagName) {
    this.tagName = tagName.toUpperCase();
    this.children = [];
    this.dataset = {};
    this.className = "";
    this.textContent = "";
  }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; }
}

function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

const AUTHORITY = "b".repeat(64);
const hex = (bytes) => [...bytes].map((byte) => byte.toString(16).padStart(2, "0")).join("");

/** A real curator keypair and a real signature over the documented encoding. */
async function signedOpening({ missionId = 1, slot = 42, commitment = "c".repeat(64) } = {}) {
  const pair = await crypto.subtle.generateKey({ name: "Ed25519" }, true, ["sign", "verify"]);
  const raw = new Uint8Array(await crypto.subtle.exportKey("raw", pair.publicKey));
  const statement = { schema: "POA-SLOT-OPENING-STATEMENT-1", authorityId: AUTHORITY, missionId, slot, commitment };
  const message = new TextEncoder().encode(slotStatementMessage(statement));
  const signature = new Uint8Array(await crypto.subtle.sign({ name: "Ed25519" }, pair.privateKey, message));
  return {
    curatorPublicKey: hex(raw),
    document: {
      format: "POA-SIGNAL-SLOT-1",
      authority_id: AUTHORITY,
      federation_id: AUTHORITY,
      open: true,
      opening: {
        statement: { schema: statement.schema, authority_id: AUTHORITY, mission_id: missionId, slot, commitment },
        curator_key: hex(raw),
        signature: hex(signature),
      },
      consensus_finality: "not-asserted",
    },
  };
}

const jsonFetch = (body, ok = true, status = 200) => async () => ({
  ok,
  status,
  text: async () => JSON.stringify(body),
});

test("the signing message is rebuilt in the documented field order, not restringified", async () => {
  const message = slotStatementMessage({ schema: "x", authorityId: AUTHORITY, missionId: 1, slot: 42, commitment: "c".repeat(64) });
  assert.equal(
    message,
    `{"schema":"POA-SLOT-OPENING-STATEMENT-1","authority_id":"${AUTHORITY}","mission_id":1,"slot":42,"commitment":"${"c".repeat(64)}"}`,
  );
  // ⚠ The order is the node's, not ours. `PoaSlotOpeningStatementV1` says a
  // client re-encoding in any other order verifies nothing, so this is pinned
  // against the Rust struct's declaration order rather than against itself.
  const rust = await readFile(new URL("../../node/src/poa_signal_slot_api.rs", import.meta.url), "utf8");
  const struct = rust.slice(rust.indexOf("pub struct PoaSlotOpeningStatementViewV1"));
  const fields = [...struct.slice(0, struct.indexOf("}")).matchAll(/pub (\w+):/g)].map((match) => match[1]);
  assert.deepEqual(fields, ["schema", "authority_id", "mission_id", "slot", "commitment"]);
  assert.match(rust, /"schema":"POA-SLOT-OPENING-STATEMENT-1","authority_id":"<hex32>","mission_id":<n>,"slot":<n>,"commitment":"<hex32>"/);
});

test("a slot document is checked field by field and cannot carry an unknown one", () => {
  const closed = { format: "POA-SIGNAL-SLOT-1", authority_id: AUTHORITY, federation_id: AUTHORITY, open: false, opening: null, consensus_finality: "not-asserted" };
  assert.equal(parseSlotDocument(closed, AUTHORITY).open, false);
  assert.throws(() => parseSlotDocument({ ...closed, extra: 1 }, AUTHORITY), { code: "slot-field" });
  assert.throws(() => parseSlotDocument({ ...closed, format: "POA-SIGNAL-SLOT-2" }, AUTHORITY), { code: "slot-format" });
  assert.throws(() => parseSlotDocument(closed, "a".repeat(64)), { code: "slot-authority" });
  assert.throws(() => parseSlotDocument({ ...closed, open: true, opening: null }, AUTHORITY), { code: "slot-shape" });
  // A closed slot that smuggles an opening is refused, not quietly believed.
  assert.throws(() => parseSlotDocument({ ...closed, opening: { statement: {}, curator_key: "", signature: "" } }, AUTHORITY), { code: "slot-open" });
});

test("an open slot is VERIFIED against the pinned curator key, never taken on the node's word", async () => {
  const { curatorPublicKey, document } = await signedOpening();
  const open = await loadSlotState({ authorityId: AUTHORITY, curatorPublicKey, baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch(document) });
  assert.equal(open.state, "open", `a correctly signed opening must verify (${open.reason ?? ""})`);
  assert.equal(open.slot, 42);
  assert.equal(open.commitment, "c".repeat(64));

  // ⚠ Constructive mutation, asserted to have actually happened before the
  // verdict is read: flip one hex digit of the commitment and the SAME
  // signature must stop authenticating the statement beside it.
  const tampered = structuredClone(document);
  tampered.opening.statement.commitment = `d${"c".repeat(63)}`;
  assert.notEqual(tampered.opening.statement.commitment, document.opening.statement.commitment);
  const bad = await loadSlotState({ authorityId: AUTHORITY, curatorPublicKey, baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch(tampered) });
  assert.equal(bad.state, "refused");
  assert.equal(bad.code, "slot-bad-signature");

  // A node serving an opening under a key this deployment is not pinned to is
  // refused BEFORE any signature check: a valid signature by the wrong curator
  // is exactly as useless as an invalid one.
  const otherPair = await crypto.subtle.generateKey({ name: "Ed25519" }, true, ["sign", "verify"]);
  const otherKey = hex(new Uint8Array(await crypto.subtle.exportKey("raw", otherPair.publicKey)));
  assert.notEqual(otherKey, curatorPublicKey);
  const wrongKey = await loadSlotState({ authorityId: AUTHORITY, curatorPublicKey: otherKey, baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch(document) });
  assert.equal(wrongKey.state, "refused");
  assert.equal(wrongKey.code, "slot-curator-pin");
});

test("every way of not knowing lands as practice-only, never as an open slot", async () => {
  const closed = { format: "POA-SIGNAL-SLOT-1", authority_id: AUTHORITY, federation_id: AUTHORITY, open: false, opening: null, consensus_finality: "not-asserted" };
  const cases = [
    ["closed", await loadSlotState({ authorityId: AUTHORITY, curatorPublicKey: "a".repeat(64), baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch(closed) })],
    ["http error", await loadSlotState({ authorityId: AUTHORITY, curatorPublicKey: "a".repeat(64), baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch({}, false, 404) })],
    ["network", await loadSlotState({ authorityId: AUTHORITY, curatorPublicKey: "a".repeat(64), baseUrl: "https://poa.invalid/", fetchImpl: async () => { throw new Error("no route"); } })],
    ["no authority", await loadSlotState({ authorityId: null, curatorPublicKey: "a".repeat(64), baseUrl: "https://poa.invalid/" })],
    ["no fetch", await loadSlotState({ authorityId: AUTHORITY, curatorPublicKey: "a".repeat(64), baseUrl: "https://poa.invalid/", fetchImpl: null })],
    ["garbage", await loadSlotState({ authorityId: AUTHORITY, curatorPublicKey: "a".repeat(64), baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch({ format: "SOMETHING" }) })],
  ];
  for (const [label, result] of cases) {
    assert.notEqual(result.state, "open", `${label} produced an open slot`);
  }
  assert.equal(cases[0][1].state, "closed");
  assert.equal(cases[5][1].state, "refused");
  // …and none of them throws, so a missing node cannot seal the whole terminal.
});

test("the slot tile says practice-only whenever no verified opening exists", async () => {
  const closed = buildTodayBoard({ slot: { state: "closed" }, cards: [] }).tiles.find((tile) => tile.id === "slot");
  assert.equal(closed.state, "sealed");
  assert.match(closed.detail, /every drill on the rack is practice/i);

  const unreachable = buildTodayBoard({ slot: { state: "unreachable", reason: "no PoA authority answered on this origin" }, cards: [] }).tiles.find((tile) => tile.id === "slot");
  assert.equal(unreachable.state, "sealed");
  assert.match(unreachable.detail, /practice/i);

  const open = buildTodayBoard({ slot: { state: "open", slot: 42, commitment: "c".repeat(64) }, cards: [] }).tiles.find((tile) => tile.id === "slot");
  assert.equal(open.state, "live");
  assert.match(open.headline, /Slot 42 is open/);
  // Even an open slot does not claim settlement.
  assert.match(open.detail, /settles only once a node finalizes it/);
});

test("the crate tile reads the station the node actually serves, in BOTH directions", async () => {
  // ⚠ THE FALSIFIER, AND IT HAS ALREADY STOPPED FALSIFYING ONCE.
  //
  // Its first form asserted that no crate surface existed, and matched paths
  // containing the substring `crate`. The station lane then served the crate at
  // `/api/poa/station/{authority}/panel` and `/crew/{crew}` — no `crate`
  // anywhere in the path. The surface shipped, the tile kept saying "not wired
  // yet", and this test stayed green guarding the lie. It was re-keyed on the
  // ORGAN (any station/crate/panel route under /api/poa), went red, and the
  // tile was wired.
  //
  // It now guards the wiring rather than its absence, and it guards it BOTH
  // WAYS, because either side can drift: the routes this client is pinned to
  // must be exactly the station routes the node serves. A rename in the node
  // reds it; a rename in `CRATE_SURFACE` reds it; a THIRD station route landing
  // unnoticed reds it too.
  const nodeSrc = new URL("../../node/src/", import.meta.url);
  const files = (await readdir(nodeSrc)).filter((file) => file.endsWith(".rs"));
  assert.ok(files.length > 20, "the node source tree should not be empty");
  const ORGAN = /"(\/api\/poa\/[a-z0-9/{}_-]*(?:crate|station|panel)[a-z0-9/{}_-]*)"/g;
  const routes = [...new Set((await Promise.all(files.map(async (file) => {
    const source = await readFile(new URL(file, nodeSrc), "utf8");
    return [...source.matchAll(ORGAN)].map((match) => match[1]);
  }))).flat())].sort();

  // Self-check: the pattern must still be able to see a route of the shape it
  // guards. A guard whose pattern has stopped matching is not a passing guard.
  ORGAN.lastIndex = 0;
  assert.ok(
    ORGAN.test('"/api/poa/station/{authority}/panel"'),
    "the falsifier's own pattern no longer matches a station route — it has stopped falsifying again",
  );

  // ⚑ IT FIRED A SECOND TIME. The crate-open WRITE landed and this went red
  // naming a route the client had never heard of, which is the guard working —
  // it is not "fixed" by widening it, it is fixed by teaching the client the
  // route that shipped and wiring the action. `openRoute` is that.
  assert.deepEqual(
    routes,
    [CRATE_SURFACE.crewRoute, CRATE_SURFACE.openRoute, CRATE_SURFACE.route].sort(),
    "the station routes the node serves are not the ones this client is pinned to",
  );
  assert.equal(CRATE_SURFACE.route, "/api/poa/station/{authority}/panel");
  assert.equal(CRATE_SURFACE.crewRoute, "/api/poa/station/{authority}/crew/{crew}");
  assert.equal(CRATE_SURFACE.openRoute, "/api/poa/station/{authority}/crate/open");
});

test("the crate tile reports the served crate without ever implying a day passed", () => {
  const tile = (station) => buildTodayBoard({ station, cards: [] }).tiles.find((entry) => entry.id === "crate");

  const installed = tile(readyStation());
  // Read, checked, and still sealed: the schedule is real and no draw is possible.
  assert.equal(installed.state, "sealed");
  assert.equal(installed.headline, "No draw is possible");
  assert.match(installed.detail, /4 loot rows and 14 ticket entries across periods 31–35/);
  assert.match(installed.detail, /no current-period pointer/i);
  assert.match(installed.detail, /the whole authored schedule, not one day of it/);

  // ⚠ The copy law, asserted rather than trusted: no tile may say a day turned
  // over, because the organ carries nothing that could tell it one did.
  for (const state of [installed, tile(readyStation({ admitted: 2, observed: 3 })), tile(null)]) {
    assert.doesNotMatch(`${state.eyebrow} ${state.headline}`, /\btoday\b|\bdaily\b|\byesterday\b/i,
      `the crate tile said a day passed: ${state.headline}`);
  }

  const moved = tile(readyStation({ admitted: 2, observed: 3 }));
  assert.equal(moved.state, "live");
  assert.equal(moved.headline, "2 openings admitted");

  assert.equal(tile({ state: "refused", code: "station-gauge" }).state, "refused");
  assert.equal(tile({ state: "unreachable", code: "station-fetch", reason: "No station answered on this origin" }).state, "sealed");
  assert.equal(tile(null).state, "pending");
});

test("the ship headline is a live figure or an honest absence, never a filled-in number", () => {
  const demo = buildTodayBoard({ recorder: { state: "ready", source: "demo-fixture", transitions: 4, reportedTransitionCount: 4, consensusFinality: "not-asserted" }, cards: [] })
    .tiles.find((tile) => tile.id === "ship");
  assert.equal(demo.state, "sealed");
  assert.equal(demo.headline, "No live figure");
  assert.match(demo.detail, /rehearsal/);

  const live = buildTodayBoard({ recorder: { state: "ready", source: "live-api", transitions: 12, reportedTransitionCount: 2561, consensusFinality: "not-asserted" }, cards: [] })
    .tiles.find((tile) => tile.id === "ship");
  assert.equal(live.state, "live");
  assert.equal(live.headline, "2561 transitions");
  assert.match(live.detail, /12 of them linked/);

  const refused = buildTodayBoard({ recorder: { state: "refused", code: "recorder-status-fetch" }, cards: [] }).tiles.find((tile) => tile.id === "ship");
  assert.equal(refused.state, "refused");
  assert.match(refused.detail, /No ship figure is asserted/);

  const pending = buildTodayBoard({ cards: [] }).tiles.find((tile) => tile.id === "ship");
  assert.equal(pending.state, "pending");
});

test("the rack tile counts the board it is actually looking at", () => {
  const cards = [{ state: "open" }, { state: "open" }, { state: "sealed" }, { state: "reserved" }];
  const ready = buildTodayBoard({ contentAuthority: { state: "ready" }, cards }).tiles.find((tile) => tile.id === "rack");
  assert.equal(ready.headline, "2 drills open");
  assert.match(ready.detail, /2 more slots are on the rack and sealed/);

  const sealed = buildTodayBoard({ contentAuthority: { state: "refused" }, cards: [] }).tiles.find((tile) => tile.id === "rack");
  assert.equal(sealed.state, "refused");
  assert.match(sealed.headline, /sealed/);
});

test("the today board renders four tiles with one anatomy", () => withFakeDocument(() => {
  const root = new FakeElement("section");
  const board = buildTodayBoard({ cards: [] });
  mountTodayBoard(root, board);
  const [lead, grid] = root.children;
  assert.equal(lead.className, "today-board__lead");
  assert.deepEqual(grid.children.map((tile) => tile.dataset.tile), ["rack", "slot", "crate", "ship"]);
  for (const tile of grid.children) {
    assert.deepEqual(tile.children.map((node) => node.className), ["today-tile__eyebrow", "today-tile__headline", "today-tile__detail"]);
    assert.ok(tile.children.every((node) => node.textContent.length > 0));
  }
}));

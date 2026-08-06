import assert from "node:assert/strict";
import { test } from "node:test";
import {
  RUN_RUNGS,
  RUN_STATUSES,
  advanceRunStatus,
  buildRunSummary,
  isScored,
  isSettled,
  mountRunSummary,
  runLadder,
  runOutcome,
} from "../src/run-summary.js";
import { RESULT_OUTCOMES, readRackResults, recordRackResult, resultBucket } from "../src/rack-results.js";
import { buildRack } from "../src/game-rack.js";
import { INSTALLED_GAME_IDS } from "../src/mission-launcher.js";
import { canonicalDescriptors } from "./canonical-descriptors.mjs";

class FakeElement {
  constructor(tagName) {
    this.tagName = tagName.toUpperCase();
    this.children = [];
    this.attributes = new Map();
    this.dataset = {};
    this.className = "";
    this.textContent = "";
    this.listeners = new Map();
  }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  addEventListener(name, callback) { this.listeners.set(name, [...(this.listeners.get(name) ?? []), callback]); }
  dispatch(name) { for (const callback of this.listeners.get(name) ?? []) callback({}); }
}

function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

const all = (node) => [node, ...node.children.flatMap(all)];

function memoryStorage() {
  const map = new Map();
  return {
    getItem: (key) => (map.has(key) ? map.get(key) : null),
    setItem: (key, value) => { map.set(key, String(value)); },
    raw: map,
  };
}

const card = {
  gameId: "relay-repair",
  name: "Relay Repair",
  verification: [{ term: "Rules authority", detail: "POAG1 abcd · content epoch 1.7" }],
};

test("the ladder is exactly practice, submitted, judged, finalized, refused", () => {
  assert.deepEqual(RUN_STATUSES, ["practice", "submitted", "judged", "finalized", "refused"]);
  for (const status of RUN_STATUSES) {
    assert.equal(RUN_RUNGS[status].id, status);
    assert.equal(runLadder(status).length, 5);
  }
  assert.throws(() => runLadder("settled"), { code: "run-status" });
});

test("practice is its own branch, and no judged rung is ever drawn for it", () => {
  const practice = runLadder("practice");
  const byId = new Map(practice.map((rung) => [rung.id, rung.state]));
  assert.equal(byId.get("practice"), "current");
  for (const rung of ["submitted", "judged", "finalized", "refused"]) {
    // ⚠ `unreachable`, not `ahead`. `ahead` would draw a rehearsal as one step
    // of five toward a settled result, which is the exact confusion the mode
    // split exists to prevent.
    assert.equal(byId.get(rung), "unreachable", `practice draws ${rung} as if it were on its path`);
  }
});

test("practice is never a rung of the judged path either", () => {
  for (const status of ["submitted", "judged", "finalized", "refused"]) {
    const practice = runLadder(status).find((rung) => rung.id === "practice");
    assert.equal(practice.state, "unreachable", `${status} draws practice as part of its history`);
  }
});

test("only finalized settles, and only judged or finalized scores", () => {
  for (const status of RUN_STATUSES) {
    assert.equal(isSettled(status), status === "finalized", `${status} disagrees about settlement`);
    assert.equal(isScored(status), status === "judged" || status === "finalized");
  }
  assert.equal(isSettled("practice"), false);
  assert.equal(isScored("practice"), false);
});

test("a practice run cannot be advanced into the judged path", () => {
  assert.throws(() => advanceRunStatus("practice", "submitted"), { code: "run-status-practice-frozen" });
  assert.throws(() => advanceRunStatus("practice", "judged"), { code: "run-status-practice-frozen" });
  assert.throws(() => advanceRunStatus("practice", "finalized"), { code: "run-status-practice-frozen" });
  assert.throws(() => advanceRunStatus("practice", "refused"), { code: "run-status-practice-frozen" });
  assert.throws(() => advanceRunStatus(null, "judged"), { code: "run-status-start" });
  assert.throws(() => advanceRunStatus(null, "finalized"), { code: "run-status-start" });
  assert.throws(() => advanceRunStatus("submitted", "finalized"), { code: "run-status-transition" });
  assert.throws(() => advanceRunStatus("finalized", "refused"), { code: "run-status-transition" });

  assert.equal(advanceRunStatus(null, "practice"), "practice");
  assert.equal(advanceRunStatus(null, "submitted"), "submitted");
  assert.equal(advanceRunStatus("submitted", "judged"), "judged");
  assert.equal(advanceRunStatus("judged", "finalized"), "finalized");
  assert.equal(advanceRunStatus("judged", "refused"), "refused");
});

test("every end screen is the same record, and settled/scored are derived not passed", () => {
  const practice = buildRunSummary({ card, status: "practice", outcome: "solved", actions: 4, actionLimit: 12 });
  assert.equal(practice.settled, false);
  assert.equal(practice.scored, false);
  assert.equal(practice.statusLabel, "PRACTICE");
  assert.deepEqual(practice.controls.map((control) => control.id), ["again", "rack"]);
  assert.equal(practice.detail, "Relay Repair · 4 of 12 actions");
  assert.equal(practice.verification.length, 1);

  const finalized = buildRunSummary({ card, status: "finalized", outcome: "solved", actions: 4, actionLimit: 12 });
  assert.equal(finalized.settled, true);
  assert.equal(finalized.scored, true);
  // Same shape, both times: same keys, same order, same controls.
  assert.deepEqual(Object.keys(practice), Object.keys(finalized));

  // A caller cannot hand in a flattering pair — there is nowhere to put one.
  assert.ok(!("settled" in buildRunSummary({ card, status: "practice", outcome: "unsolved", actions: 0, actionLimit: null, settled: true })) === false);
  assert.equal(buildRunSummary({ card, status: "practice", outcome: "unsolved", actions: 0, actionLimit: null, settled: true }).settled, false);

  assert.throws(() => buildRunSummary({ card, status: "won", outcome: "solved", actions: 1, actionLimit: 2 }), { code: "run-status" });
  assert.throws(() => buildRunSummary({ card, status: "practice", outcome: "great", actions: 1, actionLimit: 2 }), { code: "run-outcome" });
  assert.throws(() => buildRunSummary({ card, status: "practice", outcome: "solved", actions: 1.5, actionLimit: 2 }), { code: "run-actions" });
  assert.throws(() => buildRunSummary({ status: "practice", outcome: "solved", actions: 1, actionLimit: 2 }), { code: "run-summary-card" });
});

test("the rendered end screen draws only reachable rungs and marks the current one", () => withFakeDocument(() => {
  const root = new FakeElement("div");
  const clicked = [];
  const summary = buildRunSummary({ card, status: "practice", outcome: "solved", actions: 4, actionLimit: 12, transcript: "{\"mode\":\"practice\"}" });
  mountRunSummary(root, summary, { onAgain: () => clicked.push("again"), onRack: () => clicked.push("rack") });

  const [shell] = root.children;
  assert.equal(shell.dataset.status, "practice");
  assert.equal(shell.dataset.settled, "false");
  const rungs = all(shell).filter((node) => node.dataset.rung !== undefined);
  assert.deepEqual(rungs.map((node) => node.dataset.rung), ["practice"]);
  assert.equal(rungs[0].attributes.get("aria-current"), "step");

  const controls = all(shell).filter((node) => node.dataset.control !== undefined);
  assert.deepEqual(controls.map((node) => node.dataset.control), ["again", "rack"]);
  controls[0].dispatch("click");
  controls[1].dispatch("click");
  assert.deepEqual(clicked, ["again", "rack"]);

  // Both folds are the SAME disclosure element the cards use.
  const folds = all(shell).filter((node) => node.className.startsWith("verify-fold") && node.tagName === "DETAILS");
  assert.equal(folds.length, 2);

  const judged = new FakeElement("div");
  mountRunSummary(judged, buildRunSummary({ card, status: "judged", outcome: "solved", actions: 4, actionLimit: 12 }));
  const judgedRungs = all(judged.children[0]).filter((node) => node.dataset.rung !== undefined);
  assert.deepEqual(judgedRungs.map((node) => node.dataset.rung), ["submitted", "judged", "finalized", "refused"]);
  assert.equal(judgedRungs.map((node) => node.dataset.state).join(","), "reached,current,ahead,ahead");
}));

test("the end of a run is read by SHAPE, so a new game in an old shape needs nothing", async () => {
  const { relay, salvage, signalJson } = await canonicalDescriptors();
  void signalJson;
  const midRelay = { terminal: false, steps: [{ action: "a" }], mode: "practice" };
  assert.deepEqual(runOutcome("machine-family", midRelay, relay), { over: false, outcome: "unsolved", actions: 1, actionLimit: relay.actionLimit, mode: "practice" });
  assert.equal(runOutcome("machine-family", { terminal: true, steps: [{}, {}], mode: "practice" }, relay).outcome, "solved");
  // Out of actions and not terminal is over, and is honestly `unsolved`.
  const spent = { terminal: false, steps: Array.from({ length: salvage.actionLimit }, () => ({})), mode: "practice" };
  assert.deepEqual(runOutcome("parametric", spent, salvage), { over: true, outcome: "unsolved", actions: salvage.actionLimit, actionLimit: salvage.actionLimit, mode: "practice" });

  assert.equal(runOutcome("deduction", { solved: true, exhausted: false, turns: [1, 2], mode: "practice" }, { maxTurns: 5 }).actions, 2);
  assert.equal(runOutcome("probe-oracle", { solved: false, exhausted: true, probes: [1], mode: "practice" }, { actionLimit: 9 }).outcome, "unsolved");
  // A genuinely NEW shape refuses rather than reaching for the nearest row.
  assert.throws(() => runOutcome("machine", { mode: "practice" }, { actionLimit: 1 }), { code: "run-shape" });
});

test("the local note keeps practice and judged in separate buckets, derived from the status", () => {
  assert.equal(resultBucket("practice"), "practice");
  for (const status of ["submitted", "judged", "finalized", "refused"]) assert.equal(resultBucket(status), "judged");
  assert.throws(() => resultBucket("nope"), { code: "result-status" });

  const storage = memoryStorage();
  recordRackResult(storage, "relay-repair", { status: "practice", outcome: "solved", actions: 5, at: 100 });
  recordRackResult(storage, "relay-repair", { status: "finalized", outcome: "solved", actions: 8, at: 200 });
  const history = readRackResults(storage);
  assert.equal(history["relay-repair"].practice.length, 1);
  assert.equal(history["relay-repair"].judged.length, 1);
  assert.equal(history["relay-repair"].practice[0].actions, 5);
  assert.equal(history["relay-repair"].judged[0].actions, 8);

  assert.throws(() => recordRackResult(storage, "relay-repair", { status: "won", outcome: "solved", actions: 1 }), { code: "result-status" });
  assert.throws(() => recordRackResult(storage, "relay-repair", { status: "practice", outcome: "great", actions: 1 }), { code: "result-outcome" });
  assert.deepEqual([...RESULT_OUTCOMES], ["solved", "unsolved", "refused"]);
});

test("a practice record filed under judged in storage is dropped, not displayed", () => {
  const storage = memoryStorage();
  // Hand-forged storage: a practice run sitting in the judged bucket is exactly
  // what a "best" column would have to swallow for a rehearsal to read as a
  // result. It is dropped on the way out.
  storage.setItem("poa.rack.results.v1", JSON.stringify({
    "relay-repair": {
      practice: [{ status: "practice", outcome: "solved", actions: 5, at: 100 }],
      judged: [{ status: "practice", outcome: "solved", actions: 2, at: 200 }],
    },
  }));
  const history = readRackResults(storage);
  assert.equal(history["relay-repair"].judged.length, 0);
  assert.equal(history["relay-repair"].practice.length, 1);

  storage.setItem("poa.rack.results.v1", "{not json");
  assert.deepEqual(readRackResults(storage), {});
  assert.deepEqual(readRackResults(null), {});
});

test("an end screen built from a real rack card carries that card's verification fold", async () => {
  const { missions } = await canonicalDescriptors();
  const relayCard = buildRack({ missions, installed: INSTALLED_GAME_IDS }).find((entry) => entry.gameId === "relay-repair");
  const summary = buildRunSummary({ card: relayCard, status: "practice", outcome: "unsolved", actions: 3, actionLimit: 3 });
  assert.equal(summary.name, "Relay Repair");
  assert.deepEqual(summary.verification, relayCard.verification);
  assert.match(summary.statusDetail, /Nothing is scored and nothing was sent/);
});

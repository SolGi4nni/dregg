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
import {
  TableOracleQuery,
  TableTransitionRefusal,
  createFiniteTableRun,
  submitFiniteTableAction,
  tableRunIsClosed,
  tableRunView,
} from "../src/finite-table-runtime.js";
import { salvagePracticeOracle } from "../src/salvage-runtime.js";
import { artificerPracticeOracle } from "../src/artificer-runtime.js";
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

/**
 * Play a finite-table run forward, taking the first action the table accepts and
 * answering oracle rows from the emitted practice board. It stops when the run is
 * closed, so what it produces is a REAL end state rather than a hand-shaped record.
 *
 * ⚠ The stubs this replaces (`{ terminal: false, steps: [{}] }`) were the reason
 * the old reading could be wrong and still test green: `finiteOutcome` read
 * `run.terminal` as "solved", a stub could assert whatever it liked about a flag
 * nothing had to earn, and the games where `terminal` does NOT mean solved were
 * invisible. The reading now consults the emitted view, so the run handed to it
 * has to be one the table could actually produce.
 */
function playToTheEnd(descriptor, session) {
  let run = createFiniteTableRun(descriptor, session);
  while (!tableRunIsClosed(descriptor, run)) {
    const before = run;
    for (const action of descriptor.actions) {
      try {
        run = submitFiniteTableAction(descriptor, run, action.id);
        break;
      } catch (error) {
        if (error instanceof TableOracleQuery) {
          run = submitFiniteTableAction(descriptor, run, action.id, session.oracle(tableRunView(descriptor, run), action.id));
          break;
        }
        if (!(error instanceof TableTransitionRefusal)) throw error;
      }
    }
    if (run === before) break;
  }
  return run;
}

test("the end of a run is read by SHAPE, so a new game in an old shape needs nothing", async () => {
  const { relay, salvage } = await canonicalDescriptors();

  // A run that has not started is not over, and says so without guessing.
  const freshRelay = createFiniteTableRun(relay, { mode: "practice", member: relay.memberKeys[0] });
  assert.deepEqual(runOutcome("machine-family", freshRelay, relay), { over: false, outcome: "unsolved", actions: 0, actionLimit: relay.actionLimit, mode: "practice" });

  // ⚑ REAL runs, played to whatever end the emitted table gives them. Every one
  // must land on an outcome this file declares, and `solved` must agree with the
  // view rather than with `terminal`.
  for (const member of relay.memberKeys) {
    const done = playToTheEnd(relay, { mode: "practice", member });
    const reading = runOutcome("machine-family", done, relay);
    assert.equal(reading.over, true, `relay board ${member} did not reach an end`);
    assert.ok(["solved", "unsolved", "lost"].includes(reading.outcome));
    assert.equal(reading.outcome === "solved", tableRunView(relay, done).solved === true);
  }

  const member = 0;
  const salvageDone = playToTheEnd(salvage, { mode: "practice", member, oracle: salvagePracticeOracle(salvage, member) });
  const salvageReading = runOutcome("parametric", salvageDone, salvage);
  assert.equal(salvageReading.over, true);
  assert.equal(salvageReading.actionLimit, salvage.actionLimit);
  assert.equal(salvageReading.outcome === "solved", tableRunView(salvage, salvageDone).solved === true);

  assert.equal(runOutcome("deduction", { solved: true, exhausted: false, turns: [1, 2], mode: "practice" }, { maxTurns: 5 }).actions, 2);
  assert.equal(runOutcome("probe-oracle", { solved: false, exhausted: true, probes: [1], mode: "practice" }, { actionLimit: 9 }).outcome, "unsolved");
  // A genuinely NEW shape refuses rather than reaching for the nearest row.
  assert.throws(() => runOutcome("machine", { mode: "practice" }, { actionLimit: 1 }), { code: "run-shape" });
});

/** Name a law, answering the oracle row the table raises, on the emitted table. */
function nameTheLaw(descriptor, run, oracle, ruleId) {
  const action = descriptor.actions.find((candidate) => candidate.kind === "declare" && candidate.rule === ruleId);
  assert.ok(action, `the emitted table has no naming for ${ruleId}`);
  try {
    return submitFiniteTableAction(descriptor, run, action.id);
  } catch (error) {
    if (!(error instanceof TableOracleQuery)) throw error;
    return submitFiniteTableAction(descriptor, run, action.id, oracle(tableRunView(descriptor, run), action.id));
  }
}

test("a run the table has stopped is LOST, and it is not `solved` and not `unsolved`", async () => {
  // ⚑ THE DISTINCTION THE FOURTH OUTCOME EXISTS FOR, on the real Artificer table.
  // A wrong naming ends the run with charges still on the clock, and the emitted
  // states say so in a way no other game on the rack does: 717 of them carry
  // `verdict: "mistaken"` with `terminal: FALSE`, and every action from them
  // refuses `run-lost`. Under the old reading that was `over: false` — so the end
  // screen never appeared at all — and if the clock had been allowed to run out it
  // would then have printed `Cleared it.`, because `run.terminal` was being read as
  // "solved". Both of those are checked here, on the bytes, not on a stub.
  const artificer = (await canonicalDescriptors()).artificer;
  const member = 0;
  const oracle = artificerPracticeOracle(artificer, member);
  const drawn = artificer.instance.manual.rules[member];
  const wrong = artificer.instance.manual.rules.find((rule) => rule.id !== drawn.id);

  const fresh = createFiniteTableRun(artificer, { mode: "practice", member, oracle });
  assert.equal(runOutcome("parametric", fresh, artificer).over, false);

  const lost = nameTheLaw(artificer, fresh, oracle, wrong.id);
  assert.equal(lost.terminal, false, "the emitted table does not mark a mistaken naming terminal; if it starts to, this test is testing nothing");
  const lostReading = runOutcome("parametric", lost, artificer);
  assert.deepEqual(lostReading, { over: true, outcome: "lost", actions: 1, actionLimit: artificer.actionLimit, mode: "practice" });
  assert.ok(lostReading.actions < artificer.actionLimit, "a lost run ends EARLY; that is what separates it from a closed window");
  assert.equal(tableRunView(artificer, lost).verdict, "mistaken");

  // …and the right naming, on the same table, is `solved`.
  const won = nameTheLaw(artificer, createFiniteTableRun(artificer, { mode: "practice", member, oracle }), oracle, drawn.id);
  assert.equal(won.terminal, true);
  assert.equal(runOutcome("parametric", won, artificer).outcome, "solved");
  assert.equal(tableRunView(artificer, won).verdict, "identified");
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
  assert.deepEqual([...RESULT_OUTCOMES], ["solved", "unsolved", "lost", "refused"]);
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

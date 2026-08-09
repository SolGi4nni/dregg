import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  TableOracleQuery,
  canonicalTableTranscript,
  createFiniteTableRun,
  exactKeys,
  identifier,
  loadFiniteTableDescriptor,
  replayFiniteTable,
  submitFiniteTableAction,
  tableRunView,
} from "../src/finite-table-runtime.js";
import { loadRelayRepairDescriptor } from "../src/relay-runtime.js";
import {
  SALVAGE_FIXTURE_STATES,
  fixtureAuthority,
  fixtureOpening,
  relayFixture,
  salvageFixture,
} from "./finite-table-fixtures.mjs";

const PRACTICE = { mode: "practice", member: 0 };

function loadRelay(game = relayFixture(), authority = fixtureAuthority("per-run-open")) {
  return loadRelayRepairDescriptor(game, authority);
}

/**
 * The parametric-shape fixture is loaded through the SHARED loader with a local
 * spec, because the Salvage loader pins its emitted 1016-state closure and a
 * hand-written fixture cannot honestly carry one. The Salvage-specific pins are
 * exercised against the real Lean bytes in canonical-finite-tables.test.mjs.
 */
function loadParametric(game = salvageFixture(), authority = fixtureAuthority("oracle-only")) {
  return loadFiniteTableDescriptor(game, authority, {
    name: "Parametric fixture",
    gameId: "salvage-lock",
    ruleset: "salvage-v2",
    disclosure: "oracle-only",
    engineModule: "Dregg2.Games.PathOfAngels.SalvageLock",
    actionLimit: 12,
    maxActionLimit: 12,
    stateCount: SALVAGE_FIXTURE_STATES,
    maxStates: SALVAGE_FIXTURE_STATES,
    maxActions: 6,
    allowsResolve: true,
    extraKeys: ["practice"],
    refusalReasons: ["solved", "turn-limit", "cleared-slot", "already-exposed"],
    parseInstance: () => null,
    parseView(value, actionLimit, at) {
      exactKeys(value, ["cleared", "exposed", "turns", "solved"], at);
      return Object.freeze({ ...value, cleared: Object.freeze([...value.cleared]) });
    },
    parseAction(value, at) {
      exactKeys(value, ["id", "label", "slot"], at);
      identifier(value.id, "fixture-action", `${at}.id is invalid`);
      return { ...value };
    },
  });
}

test("a family descriptor plays one member and prices it from that member's board", () => {
  const relay = loadRelay();
  assert.deepEqual(relay.memberKeys, [0, 1, 2, 3, 4, 5, 6, 7]);
  assert.equal(relay.hasFamily, true);
  const run = replayFiniteTable(relay, { mode: "practice", member: 3 }, ["alpha-beta", "beta-delta"]);
  assert.equal(run.terminal, true);
  assert.equal(run.member, 3);
  assert.deepEqual(tableRunView(relay, run).installed, ["alpha-beta", "beta-delta"]);
  // Same steps, different member: a different board, and the transcript says so.
  const other = replayFiniteTable(relay, { mode: "practice", member: 5 }, ["alpha-beta", "beta-delta"]);
  assert.notEqual(canonicalTableTranscript(run), canonicalTableTranscript(other));
  assert.equal(JSON.parse(canonicalTableTranscript(other)).member, 5);
});

test("the runtime follows an authenticated table row even when it contradicts Relay semantics", () => {
  const game = relayFixture();
  const rows = game.state_machine.machines[0].transitions;
  const alphaBeta = rows.find((row) => row.state === "r0" && row.action === "alpha-beta");
  const alphaGamma = rows.find((row) => row.state === "r0" && row.action === "alpha-gamma");
  assert.equal(alphaBeta.next, "r1");
  assert.equal(alphaGamma.next, "r2");
  [alphaBeta.next, alphaGamma.next] = [alphaGamma.next, alphaBeta.next];
  assert.equal(rows.find((row) => row.state === "r0" && row.action === "alpha-beta").next, "r2");

  const descriptor = loadRelay(game);
  const run = submitFiniteTableAction(descriptor, createFiniteTableRun(descriptor, PRACTICE), "alpha-beta");
  assert.equal(run.stateId, "r2");
  assert.deepEqual(tableRunView(descriptor, run).installed, []);
});

test("emitted refusal rows are authoritative", () => {
  const relay = loadRelay();
  const run = submitFiniteTableAction(relay, createFiniteTableRun(relay, PRACTICE), "alpha-beta");
  assert.throws(() => submitFiniteTableAction(relay, run, "alpha-beta"), {
    code: "table-transition-refused",
    reason: "already-installed",
  });
});

test("an oracle row is asked, never guessed, and the answer lands in the transcript", () => {
  const descriptor = loadParametric();
  const opened = submitFiniteTableAction(descriptor, createFiniteTableRun(descriptor, { mode: "practice", member: 0 }), "slot-0");
  assert.equal(opened.stateId, "s1");

  // No answer supplied: the runtime refuses to pick a branch and says which two
  // states the answer chooses between.
  const query = (() => {
    try { submitFiniteTableAction(descriptor, opened, "slot-1"); return null; }
    catch (error) { return error; }
  })();
  assert.ok(query instanceof TableOracleQuery, "an unanswered oracle row must raise TableOracleQuery");
  assert.equal(query.code, "table-oracle-required");
  assert.deepEqual([query.onMatch, query.onMismatch], ["s7", "s9"]);

  const matched = submitFiniteTableAction(descriptor, opened, "slot-1", "match");
  const missed = submitFiniteTableAction(descriptor, opened, "slot-1", "mismatch");
  assert.equal(matched.stateId, "s7");
  assert.equal(missed.stateId, "s9");
  assert.deepEqual(JSON.parse(canonicalTableTranscript(matched)).steps, [
    { action: "slot-0", resolution: null },
    { action: "slot-1", resolution: "match" },
  ]);
  // An answer volunteered for a row the table already determines is refused: a
  // client that could answer a settled row could steer the run.
  assert.throws(
    () => submitFiniteTableAction(descriptor, createFiniteTableRun(descriptor, PRACTICE), "slot-0", "match"),
    { code: "table-run-oracle" },
  );
  assert.throws(() => submitFiniteTableAction(descriptor, opened, "slot-1", "maybe"), { code: "table-run-oracle" });
});

test("a transcript that drops or invents an oracle answer does not replay", () => {
  const descriptor = loadParametric();
  const run = replayFiniteTable(descriptor, PRACTICE, [
    { action: "slot-0" },
    { action: "slot-1", resolution: "match" },
  ]);
  assert.equal(run.stateId, "s7");

  const stripped = { ...run, steps: run.steps.map((step) => ({ ...step, resolution: null })) };
  assert.throws(() => tableRunView(descriptor, stripped), { code: "table-run-oracle" });

  const flipped = { ...run, steps: [run.steps[0], { action: "slot-1", resolution: "mismatch" }] };
  assert.throws(() => tableRunView(descriptor, flipped), { code: "table-run-drift" });
});

test("practice and judged are structurally different objects", () => {
  const descriptor = loadParametric();
  const practice = createFiniteTableRun(descriptor, { mode: "practice", member: 4 });
  const judged = createFiniteTableRun(descriptor, { mode: "judged", opening: fixtureOpening() });
  assert.equal(practice.mode, "practice");
  assert.equal(practice.slot, null);
  assert.equal(practice.slotCommitment, null);
  assert.equal(judged.mode, "judged");
  assert.equal(judged.slot, 41);
  // ⚠ oracle-only: a judged run must NOT carry the member. Carrying it would put
  // the answer in the transcript the host is meant to be answerable for.
  assert.equal(judged.member, null);
  assert.equal(JSON.parse(canonicalTableTranscript(judged)).member, null);
  assert.equal(JSON.parse(canonicalTableTranscript(practice)).member, 4);

  assert.throws(() => createFiniteTableRun(descriptor, { mode: "judged", opening: fixtureOpening(), member: 4 }), { code: "table-run-member" });
  assert.throws(() => createFiniteTableRun(descriptor, { mode: "practice" }), { code: "table-run-member" });
  assert.throws(() => createFiniteTableRun(descriptor, { mode: "judged" }), { code: "instance-shape" });
  assert.throws(() => createFiniteTableRun(descriptor, { mode: "judged", opening: { ...fixtureOpening(), mission_id: 8 } }), { code: "opening-mission" });
  // per-run-open is the opposite: a judged run MUST carry the opened board.
  const relay = loadRelay();
  assert.throws(() => createFiniteTableRun(relay, { mode: "judged", opening: fixtureOpening() }), { code: "table-run-member" });
  assert.equal(createFiniteTableRun(relay, { mode: "judged", opening: fixtureOpening(), member: 2 }).member, 2);
});

test("hostile finite-table count, order, target, verdict, and reason drift is refused", () => {
  const refuses = (mutate, code) => {
    const game = relayFixture();
    const before = JSON.stringify(game);
    mutate(game);
    assert.notEqual(JSON.stringify(game), before, "the hostile mutation must actually change the fixture");
    assert.throws(() => loadRelay(game), { code });
  };
  const machine = (game) => game.state_machine.machines[0];
  // Dropping a state leaves the row count wrong; dropping the state AND its rows
  // leaves the count right but strands every row that pointed at it. Both are
  // refused, and by different checks.
  refuses((game) => machine(game).states.pop(), "table-transition-count");
  refuses((game) => {
    machine(game).states.pop();
    machine(game).transitions.splice(-game.state_machine.actions.length);
  }, "table-transition-target");
  refuses((game) => machine(game).transitions.pop(), "table-transition-count");
  refuses((game) => {
    const rows = machine(game).transitions;
    [rows[0], rows[1]] = [rows[1], rows[0]];
  }, "table-transition-order");
  refuses((game) => { machine(game).transitions[0].next = "absent"; }, "table-transition-target");
  refuses((game) => { machine(game).transitions[0].reason = "secret"; }, "table-transition-target");
  refuses((game) => { machine(game).transitions[2].next = "r1"; }, "table-transition-refusal");
  refuses((game) => { machine(game).transitions[2].reason = "invented-refusal"; }, "table-transition-refusal");
  refuses((game) => { machine(game).transitions[0].verdict = "maybe"; }, "table-transition-verdict");
  // An oracle row in a table declared free of them would be a rule the client
  // has to complete, and Relay's disclosure says there is nothing to ask.
  refuses((game) => {
    const row = machine(game).transitions[0];
    row.verdict = "resolve";
    row.next = null;
  }, "table-transition-verdict");

  // Where a ruleset DOES fix its legal-state closure, the count is pinned and a
  // shrunken closure is refused before any row is read.
  const shrunk = salvageFixture();
  shrunk.state_machine.states.pop();
  shrunk.state_machine.transitions.splice(-shrunk.state_machine.actions.length);
  assert.throws(() => loadParametric(shrunk), { code: "table-state-count" });
});

test("a family cannot be short, reordered, or secretly smaller than it claims", () => {
  const short = relayFixture();
  short.state_machine.machines.pop();
  assert.throws(() => loadRelay(short), { code: "table-family-size" });

  const reordered = relayFixture();
  const machines = reordered.state_machine.machines;
  [machines[0].board, machines[1].board] = [machines[1].board, machines[0].board];
  assert.throws(() => loadRelay(reordered), { code: "table-family-order" });

  // Two identical boards are one board wearing two indices: the draw ranges over
  // a smaller space than the descriptor advertises.
  const twinned = relayFixture();
  twinned.instance.boards[1].costs = { ...twinned.instance.boards[0].costs };
  twinned.instance.boards[1].spares = twinned.instance.boards[0].spares;
  assert.throws(() => loadRelay(twinned), { code: "relay-instance" });
});

test("unreachable states and accepting terminal rows cannot hide inside a complete table", () => {
  const unreachable = relayFixture();
  for (const row of unreachable.state_machine.machines[0].transitions) {
    if (row.next !== "r13") continue;
    row.verdict = "refuse";
    row.next = null;
    row.reason = "turn-limit";
  }
  assert.throws(() => loadRelay(unreachable), { code: "table-state-closure" });

  const terminal = relayFixture();
  const row = terminal.state_machine.machines[0].transitions.find((candidate) => candidate.state === "r14");
  row.verdict = "accept";
  row.next = "r2";
  row.reason = null;
  assert.throws(() => loadRelay(terminal), { code: "table-terminal-row" });

  // Both branches of an oracle row count as reachable. A state only the
  // mismatch branch reaches is still a legal state the live board walks into.
  const parametric = salvageFixture();
  for (const candidate of parametric.state_machine.transitions) {
    if (candidate.verdict === "resolve") candidate.on_mismatch = "s7";
  }
  assert.throws(() => loadParametric(parametric), { code: "table-transition-oracle" });
});

test("authority, reward policy, action limit, disclosure, and instance domains fail closed", () => {
  // ⚠ The signed catalog declares the disclosure; a descriptor cannot widen it.
  assert.throws(() => loadRelay(relayFixture(), fixtureAuthority("oracle-only")), { code: "table-authority" });

  const rewarded = relayFixture();
  rewarded.security.economic_rewards = true;
  assert.throws(() => loadRelay(rewarded), { code: "table-security" });

  const limit = relayFixture();
  limit.action_limit = 2;
  assert.throws(() => loadRelay(limit), { code: "table-action-limit" });

  const unpriced = relayFixture();
  delete unpriced.instance.boards[3].costs["delta-omega"];
  assert.throws(() => loadRelay(unpriced), { code: "table-field" });

  const free = relayFixture();
  free.instance.boards[3].costs["delta-omega"] = 0;
  assert.throws(() => loadRelay(free), { code: "relay-instance" });

  const annex = relayFixture();
  annex.instance.tampered = true;
  assert.throws(() => loadRelay(annex), { code: "table-field" });

  const unbound = relayFixture();
  unbound.instance.draw.commitment.binding_bits = 8;
  assert.throws(() => loadRelay(unbound), { code: "instance-commitment" });

  const scored = relayFixture();
  scored.instance.draw.practice.scored = true;
  assert.throws(() => loadRelay(scored), { code: "instance-practice" });
});

test("the pre-split shape is refused, never reinterpreted", () => {
  for (const field of ["run_seed", "target", "outcomes"]) {
    const stale = relayFixture();
    stale[field] = "0".repeat(64);
    assert.throws(() => loadRelay(stale), { code: "instance-published" });
  }
  for (const field of ["selected", "seed_byte"]) {
    const stale = relayFixture();
    stale.instance[field] = 3;
    assert.throws(() => loadRelay(stale), { code: "instance-published" });
  }
  const glyphed = salvageFixture();
  glyphed.state_machine.actions[0].glyph_id = 2;
  assert.throws(() => loadParametric(glyphed), { code: "instance-published" });
});

test("terminal extension and forged transcript state are refused", () => {
  const descriptor = loadRelay();
  const terminal = replayFiniteTable(descriptor, PRACTICE, ["alpha-beta", "beta-delta"]);
  assert.throws(() => submitFiniteTableAction(descriptor, terminal, "gamma-delta"), { code: "table-run-terminal" });

  const forged = { ...createFiniteTableRun(descriptor, PRACTICE), stateId: "r1" };
  assert.throws(() => tableRunView(descriptor, forged), { code: "table-run-drift" });

  const foreign = { ...createFiniteTableRun(descriptor, PRACTICE), contentSession: "a".repeat(64) };
  assert.throws(() => tableRunView(descriptor, foreign), { code: "table-run-domain" });

  const absent = { ...createFiniteTableRun(descriptor, PRACTICE), member: 99 };
  assert.throws(() => tableRunView(descriptor, absent), { code: "table-member" });
});

test("browser runtimes contain no Relay reachability or Salvage glyph-matching implementation", async () => {
  const files = [
    "../src/finite-table-runtime.js",
    "../src/relay-runtime.js",
    "../src/salvage-runtime.js",
    "../src/finite-table-controller.js",
    "../src/relay-controller.js",
    "../src/salvage-controller.js",
  ];
  const source = (await Promise.all(files.map((file) => readFile(new URL(file, import.meta.url), "utf8")))).join("\n");
  assert.doesNotMatch(source, /function\s+(reachable|glyphAt|step|openB|install|matching)\b/);
  assert.doesNotMatch(source, /Math\.random|crypto\.getRandomValues|Date\s*\(/);
});

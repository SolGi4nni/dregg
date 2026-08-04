import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  canonicalTableTranscript,
  createFiniteTableRun,
  replayFiniteTable,
  submitFiniteTableAction,
  tableRunView,
} from "../src/finite-table-runtime.js";
import { loadRelayRepairDescriptor } from "../src/relay-runtime.js";
import { loadSalvageLockDescriptor } from "../src/salvage-runtime.js";
import { fixtureAuthority, relayFixture, salvageFixture } from "./finite-table-fixtures.mjs";

function loadRelay(game = relayFixture(), authority = fixtureAuthority()) {
  return loadRelayRepairDescriptor(game, authority);
}

function loadSalvage(game = salvageFixture(), authority = fixtureAuthority()) {
  return loadSalvageLockDescriptor(game, authority);
}

test("Relay and Salvage dispatch literal authenticated transition rows deterministically", () => {
  const relay = loadRelay();
  const relayRun = replayFiniteTable(relay, ["alpha-beta", "beta-delta"]);
  assert.equal(relayRun.terminal, true);
  assert.deepEqual(tableRunView(relay, relayRun).installed, ["alpha-beta", "beta-delta"]);

  const salvage = loadSalvage();
  const actions = ["slot-3", "slot-2", "slot-0"];
  const first = replayFiniteTable(salvage, actions);
  const second = replayFiniteTable(salvage, [...actions]);
  assert.equal(first.terminal, true);
  assert.equal(canonicalTableTranscript(first), canonicalTableTranscript(second));
  const transcript = JSON.parse(canonicalTableTranscript(first));
  assert.equal(transcript.settlement, "unsettled-local-transcript");
  assert.equal(transcript.activation_digest, fixtureAuthority().activationDigest);
  assert.equal(transcript.content_root, fixtureAuthority().contentRoot);
  assert.deepEqual(transcript.security, salvage.security);
});

test("emitted refusal rows are authoritative", () => {
  const relay = loadRelay();
  const relayRun = submitFiniteTableAction(relay, createFiniteTableRun(relay), "alpha-beta");
  assert.throws(() => submitFiniteTableAction(relay, relayRun, "alpha-beta"), {
    code: "table-transition-refused",
    reason: "already-installed",
  });

  const salvage = loadSalvage();
  const salvageRun = replayFiniteTable(salvage, ["slot-3", "slot-1", "slot-5"]);
  assert.equal(salvageRun.stateId, "s162");
  assert.throws(() => submitFiniteTableAction(salvage, salvageRun, "slot-0"), {
    code: "table-transition-refused",
    reason: "already-exposed",
  });
});

test("hostile finite-table count, order, target, verdict, and reason drift is refused", () => {
  const refuses = (mutate, code) => {
    const game = relayFixture();
    mutate(game);
    assert.throws(() => loadRelay(game), { code });
  };
  refuses((game) => {
    game.state_machine.states.pop();
    game.state_machine.transitions.splice(-game.state_machine.actions.length);
  }, "table-state-count");
  refuses((game) => game.state_machine.transitions.pop(), "table-transition-count");
  refuses((game) => {
    const rows = game.state_machine.transitions;
    [rows[0], rows[1]] = [rows[1], rows[0]];
  }, "table-transition-order");
  refuses((game) => { game.state_machine.transitions[0].next = "absent"; }, "table-transition-target");
  refuses((game) => { game.state_machine.transitions[0].reason = "secret"; }, "table-transition-target");
  refuses((game) => {
    const row = game.state_machine.transitions[2];
    row.next = "r1";
  }, "table-transition-refusal");
  refuses((game) => { game.state_machine.transitions[2].reason = "invented-refusal"; }, "table-transition-refusal");
});

test("unreachable states and accepting terminal rows cannot hide inside a complete table", () => {
  const unreachable = relayFixture();
  for (const row of unreachable.state_machine.transitions) {
    if (row.next !== "r13") continue;
    row.verdict = "refuse";
    row.next = null;
    row.reason = "turn-limit";
  }
  assert.throws(() => loadRelay(unreachable), { code: "table-state-closure" });

  const terminal = relayFixture();
  const row = terminal.state_machine.transitions.find((candidate) => candidate.state === "r14");
  row.verdict = "accept";
  row.next = "r2";
  row.reason = null;
  assert.throws(() => loadRelay(terminal), { code: "table-terminal-row" });
});

test("authority, reward policy, action limit, and state/action domains fail closed", () => {
  const mismatch = fixtureAuthority("f".repeat(64));
  assert.throws(() => loadRelay(relayFixture(), mismatch), { code: "table-authority" });

  const rewarded = relayFixture();
  rewarded.security.economic_rewards = true;
  assert.throws(() => loadRelay(rewarded), { code: "table-security" });

  const limit = relayFixture();
  limit.action_limit = 3;
  assert.throws(() => loadRelay(limit), { code: "table-action-limit" });

  const actions = salvageFixture();
  actions.state_machine.actions[0].id = "slot-5";
  assert.throws(() => loadSalvage(actions), { code: "salvage-action" });
});

test("terminal extension and forged transcript state are refused", () => {
  const descriptor = loadRelay();
  const terminal = replayFiniteTable(descriptor, ["alpha-beta", "beta-delta"]);
  assert.throws(() => submitFiniteTableAction(descriptor, terminal, "gamma-delta"), { code: "table-run-terminal" });

  const forged = { ...createFiniteTableRun(descriptor), stateId: "r1" };
  assert.throws(() => tableRunView(descriptor, forged), { code: "table-run-drift" });

  const foreign = { ...createFiniteTableRun(descriptor), contentSession: "a".repeat(64) };
  assert.throws(() => tableRunView(descriptor, foreign), { code: "table-run-domain" });
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

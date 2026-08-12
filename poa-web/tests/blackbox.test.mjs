import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  applyHostRefusal,
  canonicalReplay,
  createJudgedRun,
  createPracticeRun,
  loadBlackBoxDescriptor,
  replayPractice,
  submitJudgedProbe,
  submitPracticeProbe,
} from "../src/blackbox-runtime.js";
import { mountBlackBox } from "../src/blackbox-controller.js";
import { blackBoxFixture, blackBoxMission, blackBoxOpening } from "./blackbox-fixture.mjs";

// These run against the SHIPPED descriptor bytes: `blackBoxFixture` now clones
// `poa/artifacts/poag1/games/black-box-reconstruction.json` (see
// tests/blackbox-fixture.mjs), so a green test here means the consumer parses
// the bytes the Lean emitter actually wrote, not a hand-built mirror of them.

const load = (game = blackBoxFixture(), mission = blackBoxMission()) => loadBlackBoxDescriptor(game, mission);

class FakeElement {
  constructor(tagName = "div") {
    this.tagName = tagName.toUpperCase();
    this.children = [];
    this.attributes = new Map();
    this.dataset = {};
    this.className = "";
    this.textContent = "";
    this.disabled = false;
    this.tabIndex = -1;
    this.listeners = new Map();
  }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  removeAttribute(name) { this.attributes.delete(name); }
  addEventListener(name, callback) { this.listeners.set(name, [...(this.listeners.get(name) ?? []), callback]); }
  removeEventListener(name, callback) { this.listeners.set(name, (this.listeners.get(name) ?? []).filter((entry) => entry !== callback)); }
  dispatch(name, extra = {}) {
    const event = { key: undefined, preventDefault() { this.defaultPrevented = true; }, ...extra };
    for (const callback of this.listeners.get(name) ?? []) callback(event);
    return event;
  }
  focus() { this.dispatch("focus"); }
}
const all = (root) => [root, ...root.children.flatMap(all)];
function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

test("the oracle decodes as a complete instances-by-probes matrix", () => {
  const descriptor = load();
  assert.equal(descriptor.oracle.instanceSpace, 120);
  assert.equal(descriptor.oracle.probes.length, 25);
  assert.equal(descriptor.oracle.slotCount, 5);
  assert.equal(descriptor.oracle.fragmentCount, 5);
  assert.equal(descriptor.oracle.requiredPerInstance, 5);
  assert.equal(descriptor.actionLimit, 11);
  assert.equal(descriptor.oracle.table.length, 120);
  assert.ok(descriptor.oracle.table.every((row) => row.length === 25));
  // Every row settles exactly five probes, one per slot, and no two rows agree —
  // so the matrix states every rule and singles out no instance.
  const rows = descriptor.oracle.table.map((row) => [...row].join(""));
  assert.equal(new Set(rows).size, 120);
  for (const row of descriptor.oracle.table) {
    const settling = [...row].flatMap((id, column) => (id === descriptor.oracle.solvingClassId ? [column] : []));
    assert.equal(settling.length, 5);
    assert.equal(new Set(settling.map((column) => descriptor.oracle.probes[column].slot)).size, 5);
  }
});

test("a truncated, degenerate, or self-naming oracle is refused", () => {
  const refuses = (mutate, code) => {
    const game = blackBoxFixture();
    const before = JSON.stringify(game);
    mutate(game);
    assert.notEqual(JSON.stringify(game), before, "the hostile mutation must actually change the fixture");
    assert.throws(() => load(game), { code });
  };
  refuses((game) => game.oracle.table.pop(), "oracle-table");
  refuses((game) => game.oracle.probes.pop(), "oracle-probes");
  refuses((game) => { game.oracle.table[3] = game.oracle.table[4]; }, "oracle-table");
  refuses((game) => { game.oracle.table[0] = "0".repeat(25); }, "oracle-table");
  refuses((game) => { game.oracle.table[0] = `2${game.oracle.table[0].slice(1)}`; }, "oracle-table");
  refuses((game) => { game.oracle.required_per_instance = 4; }, "oracle-table");
  refuses((game) => { game.oracle.classes[0].solving = true; }, "oracle-class");
  refuses((game) => { game.oracle.class_alphabet = "00"; }, "oracle-alphabet");
  refuses((game) => { game.oracle.settles = "slot"; }, "oracle-settles");
  refuses((game) => { game.refusals.pop(); }, "oracle-constant");
  refuses((game) => { game.oracle.probes[7].slot = 4; }, "oracle-probes");
  // The pre-split shape, refused rather than reinterpreted.
  refuses((game) => { game.target = [0, 1, 2, 3, 4]; }, "instance-published");
  refuses((game) => { game.run_seed = "0".repeat(64); }, "instance-published");
  // A relabelled disclosure, and a practice block that claims to be scored.
  refuses((game) => { game.security.instance_visibility = "per-run-open"; }, "blackbox-security");
  refuses((game) => { game.instance.practice.scored = true; }, "instance-practice");
});

test("a practice run reads its own row; a judged run learns nothing", () => {
  const descriptor = load();
  // Instance 0 is the identity order, so probe-0-0 settles and probe-0-1 does not.
  const settled = submitPracticeProbe(descriptor, createPracticeRun(descriptor, 0), "probe-0-0");
  assert.equal(settled.settled, 1);
  assert.equal(settled.probes[0].settling, true);
  const excluded = submitPracticeProbe(descriptor, createPracticeRun(descriptor, 0), "probe-0-1");
  assert.equal(excluded.settled, 0);
  assert.equal(excluded.probes[0].settling, false);

  const solved = replayPractice(descriptor, 0, ["probe-0-0", "probe-1-1", "probe-2-2", "probe-3-3", "probe-4-4"]);
  assert.equal(solved.solved, true);
  assert.equal(solved.settled, 5);
  const practiceTranscript = JSON.parse(canonicalReplay(solved));
  assert.equal(practiceTranscript.mode, "practice");
  assert.equal(practiceTranscript.practice_instance, 0);
  assert.equal(practiceTranscript.slot, null);
  assert.equal(practiceTranscript.settlement, "unsettled-local-transcript");

  const judged = createJudgedRun(descriptor, blackBoxOpening());
  assert.equal(judged.practiceInstance, null);
  assert.equal(judged.slot, 5);
  const answered = submitJudgedProbe(descriptor, judged, "probe-0-0", 1);
  assert.equal(answered.settled, 1);
  const judgedTranscript = JSON.parse(canonicalReplay(answered));
  assert.equal(judgedTranscript.mode, "judged");
  assert.equal(judgedTranscript.practice_instance, null);
  assert.equal(judgedTranscript.slot_commitment, "a".repeat(64));

  // Modes are not interchangeable, and an undeclared class is refused.
  assert.throws(() => submitPracticeProbe(descriptor, judged, "probe-0-0"), { code: "run-mode" });
  assert.throws(() => submitJudgedProbe(descriptor, createPracticeRun(descriptor, 0), "probe-0-0", 1), { code: "run-mode" });
  assert.throws(() => submitJudgedProbe(descriptor, judged, "probe-0-0", 9), { code: "oracle-class" });
  assert.throws(() => submitPracticeProbe(descriptor, createPracticeRun(descriptor, 0), "probe-9-9"), { code: "blackbox-probe" });
  assert.throws(() => createPracticeRun(descriptor, 120), { code: "practice-instance" });
});

test("the probe budget is the emitted action_limit, not a number this client chose", () => {
  const descriptor = load();
  // A pool of probes that never settle: instance 0 places fragment n at slot n, so
  // asking for the wrong fragment is always a mismatch.
  const candidates = [];
  for (let slot = 0; slot < 5; slot += 1) {
    for (const fragment of [(slot + 1) % 5, (slot + 2) % 5, (slot + 3) % 5]) candidates.push(`probe-${slot}-${fragment}`);
  }
  const wrong = candidates.slice(0, descriptor.actionLimit);
  assert.equal(wrong.length, descriptor.actionLimit);
  const spent = replayPractice(descriptor, 0, wrong);
  assert.equal(spent.exhausted, true);
  assert.equal(spent.solved, false);
  assert.equal(spent.settled, 0);
  assert.throws(() => submitPracticeProbe(descriptor, spent, "probe-0-0"), { code: "run-terminal" });
});

test("a host refusal is recorded against the emitted vocabulary and never invented", () => {
  const descriptor = load();
  const judged = createJudgedRun(descriptor, blackBoxOpening());
  const asked = submitJudgedProbe(descriptor, judged, "probe-0-0", 1);
  const refused = applyHostRefusal(descriptor, asked, "probe-0-1", "settled-slot");
  assert.equal(refused.probes.at(-1).refused, "settled-slot");
  assert.equal(refused.probes.at(-1).classId, null);
  assert.throws(() => applyHostRefusal(descriptor, asked, "probe-0-1", "made-up"), { code: "blackbox-refusal" });
  // A refusal has no meaning in practice, where nothing refuses.
  assert.throws(() => applyHostRefusal(descriptor, createPracticeRun(descriptor, 0), "probe-0-1", "settled-slot"), { code: "run-mode" });
});

test("the controller renders answers, and a judged grid waits rather than predicting", () => {
  const descriptor = load();
  withFakeDocument(() => {
    const root = new FakeElement("div");
    const controller = mountBlackBox(root, descriptor, { session: { mode: "judged", opening: blackBoxOpening() } });
    const cells = () => all(root).filter((node) => node.tagName === "BUTTON" && node.dataset.probe);
    assert.equal(cells().length, 25);
    assert.ok(cells().every((cell) => cell.attributes.get("aria-label").includes("Not yet asked")));

    cells()[0].dispatch("click");
    assert.equal(controller.awaitingProbe(), "probe-0-0");
    assert.equal(controller.getRun().probes.length, 0, "an unanswered probe must not advance the run");
    assert.ok(cells().every((cell) => cell.disabled), "the grid freezes while the sealed unit is being asked");

    controller.resolveProbe(1);
    assert.equal(controller.awaitingProbe(), null);
    assert.equal(controller.getRun().settled, 1);
    assert.match(cells()[0].attributes.get("aria-label"), /settled/);

    cells()[1].dispatch("click");
    controller.resolveRefusal("settled-slot");
    assert.match(cells()[1].attributes.get("aria-label"), /refused/);

    // ⚠ The standing question: nothing rendered may narrow the instance beyond
    // the answers actually received. Two probes were asked; no third cell may
    // have moved off "Not yet asked".
    const moved = cells().filter((cell) => !cell.attributes.get("aria-label").includes("Not yet asked"));
    assert.equal(moved.length, 2);
  });
});

test("a practice grid says PRACTICE and answers itself", () => {
  const descriptor = load();
  withFakeDocument(() => {
    const root = new FakeElement("div");
    const controller = mountBlackBox(root, descriptor, { session: { mode: "practice", instance: 0 } });
    const cells = () => all(root).filter((node) => node.tagName === "BUTTON" && node.dataset.probe);
    cells()[0].dispatch("click");
    assert.equal(controller.awaitingProbe(), null);
    assert.equal(controller.getRun().settled, 1);
    const boundary = all(root).find((node) => node.className?.includes("boundary"));
    assert.match(boundary.textContent, /PRACTICE/);
    assert.match(boundary.textContent, /answering its own probes/);
    assert.match(boundary.textContent, /real rules refuse probes this rehearsal will allow/);
    // ⚑ AND IT DOES NOT NAME THE UNIT IT DREW. This line used to print "picked
    // instance 72 of 120"; the oracle table is published, so that names row 72 —
    // the answer — on the screen of the game about deducing it. The rest of this
    // file is careful that no CELL narrows the instance beyond the answers
    // received, and the boundary copy underneath was giving it away outright.
    assert.doesNotMatch(boundary.textContent, /instance \d/);
    assert.doesNotMatch(boundary.textContent, new RegExp(`\\b${controller.getRun().practiceInstance}\\b(?!\\d)`));
  });
});

test("the Black Box runtime contains no reconstruction rule or answer generator", async () => {
  const source = (await Promise.all([
    readFile(new URL("../src/blackbox-runtime.js", import.meta.url), "utf8"),
    readFile(new URL("../src/blackbox-controller.js", import.meta.url), "utf8"),
  ])).join("\n");
  assert.doesNotMatch(source, /function\s+(orderAt|orderRow|permutation|settle|solveFor|reconstruct)\b/);
  assert.doesNotMatch(source, /Math\.random|crypto\.getRandomValues|Date\s*\(/);
});

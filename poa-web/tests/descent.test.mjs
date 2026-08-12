import assert from "node:assert/strict";
import { test } from "node:test";
import { descriptorShape, SHAPES } from "../src/descriptor-shape.js";
import { GAME_RACK, buildRack, loadRackEntry } from "../src/game-rack.js";
import { INSTALLED_GAME_IDS } from "../src/mission-launcher.js";
import { mountDeckDescent } from "../src/descent-controller.js";
import { runOutcome } from "../src/run-summary.js";
import {
  createFiniteTableRun, replayFiniteTable, submitFiniteTableAction, tableRunView,
} from "../src/finite-table-runtime.js";
import {
  chamberStanding, descentPracticeOracle, distanceHome, loadDeckDescentDescriptor, rowFor, targetOf,
} from "../src/descent-runtime.js";
import { canonicalAuthority, canonicalDescriptors, canonicalPayload } from "./canonical-descriptors.mjs";

/**
 * THE REAL LEAN-EMITTED DESCENT DESCRIPTOR, THROUGH THE REAL LOADER.
 *
 * ⚑ IT COMES FROM THE SIGNED BUNDLE NOW. Until counter 10 these bytes sat in
 * `poa/artifacts/poag1-pending/` under a hand-assembled authority envelope,
 * because no signed catalog named the mission. The curator has signed one that
 * does, so the fold-in this docblock promised has happened: the envelope is the
 * real `finiteTableAuthority` off the real catalog, and nothing is hand-written
 * on either side of the loader any more.
 *
 * A hand-written fixture is deliberately NOT used: the loader pins the emitted
 * 1692-state closure and 15228 rows, and a fixture that could satisfy that pin
 * would be a second copy of the table maintained by hand.
 */
const AUTHORITY = await canonicalAuthority("deck-descent");

async function descent() {
  return { json: await canonicalPayload("deck-descent"), descriptor: (await canonicalDescriptors()).descent };
}

test("the emitted descent descriptor loads through the shared finite-table engine", async () => {
  const { json, descriptor } = await descent();
  assert.equal(descriptorShape(json), SHAPES.parametric);
  assert.equal(descriptor.gameId, "deck-descent");
  assert.equal(descriptor.actionLimit, 9);
  assert.equal(descriptor.disclosure, "oracle-only");
  assert.equal(descriptor.members.length, 1);
  assert.equal(descriptor.members[0].states.length, 1692);
  assert.equal(descriptor.members[0].transitions.length, 1692 * 9);
  assert.equal(descriptor.oracleRows, 298);
});

test("the shaft carries PER-CHAMBER relic counts, and the spurs are not a mirror", async () => {
  const { descriptor } = await descent();
  const shaft = descriptor.instance.shaft;
  // ⚑ This is the finding the whole re-emit closed. The pre-second-relic shape
  // was a `relics_per_chamber` SCALAR; a scalar cannot say that the east spur
  // holds two, which is the asymmetry that makes the T-junction a decision.
  assert.deepEqual({ ...shaft.relicCount }, { mouth: 1, west: 1, east: 2 });
  assert.equal(shaft.air, 9);
  assert.equal(shaft.shoring, 1);
  assert.equal(shaft.bankTarget, 2);
  assert.deepEqual([...shaft.chambers], ["mouth", "west", "east"]);
  assert.equal(shaft.surface, "hatch");
});

test("a `relics_per_chamber` scalar is refused rather than reinterpreted", async () => {
  const { json } = await descent();
  const stale = { ...json, shaft: { ...json.shaft } };
  delete stale.shaft.relic_count;
  stale.shaft.relics_per_chamber = 1;
  assert.throws(
    () => loadDeckDescentDescriptor(stale, AUTHORITY),
    (error) => error.name === "ArtifactRefusal",
  );
});

test("the practice family is the whole six, distinct, and names no run", async () => {
  const { json, descriptor } = await descent();
  const practice = descriptor.instance.practice;
  assert.equal(practice.scored, false);
  assert.equal(practice.instanceSpace, 6);
  assert.equal(practice.boards.length, 6);
  assert.equal(new Set(practice.boards.map((board) => JSON.stringify(board))).size, 6);
  // ⚑ THE FAMILY, NOT THE INSTANCE. Every assignment permitted by the public
  // shared-bulkhead law is present. A block that named the drawn board would be
  // a block with fewer than six rows, or one row.
  const shapes = practice.boards.map((board) => `${board.mouth}${board.west}${board.east}`.replace(/sound/g, "s").replace(/flooded/g, "f"));
  assert.deepEqual([...shapes].sort(), ["ffs", "fsf", "fss", "sfs", "ssf", "sss"]);
  // …and nothing anywhere in the bytes names a selection.
  const bytes = JSON.stringify(json);
  for (const leak of ["selected", "seed_byte", "run_seed", "drawn_board"]) {
    assert.ok(!bytes.includes(`"${leak}"`), `the descriptor carries a \`${leak}\` field`);
  }
});

test("a practice family short one board is refused — a missing member IS a leak", async () => {
  const { json } = await descent();
  const short = { ...json, practice: { ...json.practice, boards: json.practice.boards.slice(0, 5) } };
  assert.throws(() => loadDeckDescentDescriptor(short, AUTHORITY), /emits 5 boards for a declared space of 6/);

  const duplicated = {
    ...json,
    practice: { ...json.practice, boards: [...json.practice.boards.slice(0, 5), json.practice.boards[0]] },
  };
  assert.throws(() => loadDeckDescentDescriptor(duplicated, AUTHORITY), /repeats a board/);
});

test("every oracle row's question is derived twice and the two agree", async () => {
  const { descriptor } = await descent();
  const shaft = descriptor.instance.shaft;
  // `loadDeckDescentDescriptor` has already checked this over all 298 rows — a
  // disagreement would have thrown. What is asserted here is that the check saw
  // something: the map is non-empty and says what the shaft's topology says.
  assert.equal(descriptor.questions.size, 6);
  assert.deepEqual(descriptor.questions.get("hatch|survey"), { chamber: "mouth", match: "sound", mismatch: "flooded" });
  assert.deepEqual(descriptor.questions.get("mouth|descend-east"), { chamber: "east", match: "sound", mismatch: "flooded" });
  for (const [key, question] of descriptor.questions) {
    const [node, actionId] = key.split("|");
    const action = descriptor.actions.find((candidate) => candidate.id === actionId);
    assert.equal(targetOf(shaft, node, action), question.chamber);
  }
});

test("an oracle row whose branches agree about every chamber is refused", async () => {
  const { json } = await descent();
  const rows = json.state_machine.transitions;
  const index = rows.findIndex((row) => row.verdict === "resolve");
  assert.notEqual(index, -1, "the emitted table must still carry an oracle row for this to falsify anything");
  // ⚠ Built CONSTRUCTIVELY: the mutation points `on_mismatch` at `on_match`'s own
  // successor's twin — a row whose two branches read every chamber the same way,
  // so nothing can be read off it about what it asked.
  const victim = rows[index];
  const twin = rows.find((row) => row.verdict === "resolve" && row.on_match === victim.on_match && row !== victim);
  const mutated = JSON.parse(JSON.stringify(json));
  mutated.state_machine.transitions[index] = { ...victim, on_mismatch: twin?.on_mismatch ?? victim.on_match };
  assert.notDeepEqual(mutated.state_machine.transitions[index], victim, "the mutation must actually change the row");
  assert.throws(() => loadDeckDescentDescriptor(mutated, AUTHORITY), (error) => error.name === "ArtifactRefusal");
});

test("a practice run answers its own oracle rows and banks, and is not a judged run", async () => {
  const { descriptor } = await descent();
  const board = 0; // the all-sound board: the kindest, and the shortest line out.
  const oracle = descentPracticeOracle(descriptor, board);
  let run = createFiniteTableRun(descriptor, { mode: "practice", member: board });
  assert.equal(run.mode, "practice");
  assert.equal(run.slot, null);

  const play = (actionId) => {
    const row = rowFor(descriptor, run, actionId);
    assert.ok(row, `no emitted row for ${actionId}`);
    assert.notEqual(row.verdict, "refuse", `${actionId} was refused: ${row.reason}`);
    const resolution = row.verdict === "resolve" ? oracle(tableRunView(descriptor, run), actionId) : null;
    run = submitFiniteTableAction(descriptor, run, actionId, resolution);
  };
  // Down the main line on a shaft that floods nowhere: read nothing, take the
  // mouth relic and the west relic, climb back and come out.
  for (const action of ["descend", "lift", "descend", "lift", "ascend", "ascend", "extract"]) play(action);
  const view = tableRunView(descriptor, run);
  assert.equal(view.banked, true);
  assert.equal(run.terminal, true);
  assert.equal(view.carried, 2);
  assert.equal(runOutcome(SHAPES.parametric, run, descriptor).outcome, "solved");
  // ⚠ Every oracle answer is IN the transcript, so a reader with the opened slot
  // secret could recheck each one. A practice transcript records the board it
  // chose; a judged one may not carry a board at all.
  assert.ok(run.steps.some((step) => step.resolution !== null));
  assert.throws(() => createFiniteTableRun(descriptor, { mode: "judged", member: board }));
});

test("a flooded shaft is answered differently by the same rows, and can strand a run", async () => {
  const { descriptor } = await descent();
  // Board 4 floods the mouth and west passage (the shared bulkhead guarantees
  // east stays sound). The same opening move is answered the other way.
  const kind = descentPracticeOracle(descriptor, 0);
  const cruel = descentPracticeOracle(descriptor, 4);
  const opening = tableRunView(descriptor, createFiniteTableRun(descriptor, { mode: "practice", member: 0 }));
  assert.equal(kind(opening, "survey"), "match");
  assert.equal(cruel(opening, "survey"), "mismatch");

  const run = replayFiniteTable(descriptor, { mode: "practice", member: 4 }, [
    { action: "survey", resolution: cruel(opening, "survey") },
  ]);
  const view = tableRunView(descriptor, run);
  assert.equal(view.lore.mouth, "flooded");
  assert.equal(view.air, 8);
  assert.equal(view.turns, 1);
});

test("the emitted `doomed` states are rendered, never recomputed", async () => {
  const { descriptor } = await descent();
  const doomed = descriptor.members[0].states.filter((state) => state.view.doomed);
  // ⚑ 889 of 1692. A client that did not surface this would show a player a live
  // board with nine dead buttons and no reason given — the exact "doomed-but-open"
  // complaint the design gate raises. It is a published field precisely so the
  // browser can say so without holding the rules.
  assert.equal(doomed.length, 889);
  assert.ok(doomed.every((state) => !state.terminal), "a doomed state is not a finished one");
  for (const state of doomed.slice(0, 40)) {
    const rows = descriptor.members[0].transitions.filter((row) => row.state === state.id);
    assert.ok(rows.every((row) => row.verdict === "refuse" && row.reason === "run-doomed"));
  }
});

test("the shaft map is drawn from emitted fields and nothing else", async () => {
  const { descriptor } = await descent();
  const run = createFiniteTableRun(descriptor, { mode: "practice", member: 0 });
  const view = tableRunView(descriptor, run);
  assert.equal(distanceHome(descriptor, view), 0);
  assert.deepEqual(
    chamberStanding(descriptor, view).map((standing) => [standing.chamber, standing.lore, standing.held, standing.crossingsHome]),
    [["mouth", "dark", 1, 1], ["west", "dark", 1, 2], ["east", "dark", 2, 2]],
  );
});

test("the rack teaches Deck Descent and the launcher installs it, so the card is SEALED", () => {
  const record = GAME_RACK.find((entry) => entry.gameId === "deck-descent");
  assert.ok(record, "the rack has no Deck Descent record");
  loadRackEntry(record, "deck-descent");
  assert.equal(record.shape, SHAPES.parametric);
  assert.equal(record.session, "standard");
  assert.ok(INSTALLED_GAME_IDS.includes("deck-descent"), "the launcher has no Deck Descent controller");

  // ⚠ THE STATE THIS LANE EXISTS TO PREVENT is `unsupported` — enrolled by the
  // signed catalog with no controller installed, which `game-rack.js` renders as
  // "this terminal has no controller for it". With the controller in the dispatch
  // table it can no longer occur, whichever way round the ceremony lands.
  const sealed = buildRack({ missions: [], installed: INSTALLED_GAME_IDS });
  assert.equal(sealed.find((card) => card.gameId === "deck-descent").state, "sealed");

  const enrolled = buildRack({
    missions: [{ gameId: "deck-descent", missionId: 5 }],
    installed: INSTALLED_GAME_IDS,
  });
  const card = enrolled.find((entry) => entry.gameId === "deck-descent");
  assert.equal(card.state, "open");
  assert.equal(card.playable, true);

  // …and the falsifier for the line above: WITHOUT the controller the same signed
  // catalog produces the defect, so this test is measuring the install and not
  // simply always green.
  const without = buildRack({
    missions: [{ gameId: "deck-descent", missionId: 5 }],
    installed: INSTALLED_GAME_IDS.filter((id) => id !== "deck-descent"),
  });
  assert.equal(without.find((entry) => entry.gameId === "deck-descent").state, "unsupported");
});

/**
 * ⚠ EVIDENCE THAT THE FACE RENDERS, not that its parts are correct.
 *
 * Everything above tests the RUNTIME. A controller that threw on its first paint
 * would pass all of it — the wound `controller-reach.test.mjs` names one level up
 * (a module can be perfect and dead) has a sibling here: a module can be reached
 * and still be unrenderable, and the only thing that catches that is mounting it.
 * The fake document is the one `minigame-accessibility.test.mjs` uses, so this
 * exercises the real `finite-table-controller.js` shell and the real board.
 */
class FakeElement {
  constructor(tagName) {
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
  addEventListener(name, callback) {
    this.listeners.set(name, [...(this.listeners.get(name) ?? []), callback]);
  }
  removeEventListener(name, callback) {
    this.listeners.set(name, (this.listeners.get(name) ?? []).filter((entry) => entry !== callback));
  }
  dispatch(name, extra = {}) {
    const event = { key: undefined, preventDefault() {}, ...extra };
    for (const callback of this.listeners.get(name) ?? []) callback(event);
    return event;
  }
  focus() { this.dispatch("focus"); }
}

function all(root) {
  return [root, ...root.children.flatMap(all)];
}

function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

test("the descent face mounts, draws the shaft, and plays a whole practice run", async () => {
  const { descriptor } = await descent();
  const transcripts = [];
  withFakeDocument(() => {
    const root = new FakeElement("div");
    const controller = mountDeckDescent(root, descriptor, {
      session: { mode: "practice", member: 0, oracle: descentPracticeOracle(descriptor, 0) },
      onTranscript: (canonical) => transcripts.push(JSON.parse(canonical)),
    });
    const nodes = all(root);
    const press = (actionId) => {
      const button = nodes.find((node) => node.dataset.action === actionId)
        ?? all(root).find((node) => node.dataset.action === actionId);
      assert.ok(button, `no control for ${actionId}`);
      assert.equal(button.disabled, false, `${actionId} is disabled`);
      button.dispatch("click");
    };

    // The shaft map: four rows, surface first, in the order the shaft declares.
    const map = all(root).filter((node) => node.className === "descent-shaft__node");
    assert.deepEqual(map.map((node) => node.dataset.node), ["hatch", "mouth", "west", "east"]);
    assert.equal(map[0].dataset.here, "true", "the body starts at the hatch");
    // Nine verbs, and the four that ask the dark carry the `exposed` marking.
    const board = all(root).filter((node) => node.dataset.action !== undefined);
    assert.equal(board.length, 9);
    assert.ok(board.some((node) => node.className.endsWith("--exposed")), "no verb is marked as asking the instance");

    for (const action of ["descend", "lift", "descend", "lift", "ascend", "ascend", "extract"]) press(action);

    const status = all(root).find((node) => node.className === "poa-minigame__status");
    assert.match(status.textContent, /Out through the hatch with 2 relics/);
    assert.equal(controller.getRun().terminal, true);
    assert.equal(transcripts.at(-1).mode, "practice");
    assert.equal(transcripts.at(-1).settlement, "unsettled-local-transcript");
    // The map followed the body all the way back up.
    const ended = all(root).filter((node) => node.className === "descent-shaft__node");
    assert.equal(ended[0].dataset.here, "true");
    controller.destroy();
  });
});

test("a doomed run says so, on the map and in words, before a player presses anything", async () => {
  const { descriptor } = await descent();
  withFakeDocument(() => {
    const root = new FakeElement("div");
    // Board 4 floods the mouth and west passage. Walk into both blind and take
    // the damage: the emitted table calls it doomed even though east stays dry.
    const oracle = descentPracticeOracle(descriptor, 4);
    mountDeckDescent(root, descriptor, { session: { mode: "practice", member: 4, oracle } });
    const press = (actionId) => {
      const button = all(root).find((node) => node.dataset.action === actionId);
      assert.ok(button && !button.disabled, `${actionId} is unavailable`);
      button.dispatch("click");
    };
    // Three moves: into the flooded mouth (a body), lift its relic, then into the
    // flooded west (another body). The sling can no longer hold the target.
    for (const action of ["descend", "lift", "descend"]) press(action);
    const status = all(root).find((node) => node.className === "poa-minigame__status");
    const map = all(root).find((node) => node.className === "descent-shaft");
    assert.equal(map.dataset.doomed, "true", "a doomed run's map must go cold");
    assert.match(status.textContent, /still brings 2 relics up/);
    assert.match(status.textContent, /6 air left and no line home/);
    // ⚑ EVERY VERB IS DEAD, AND SAYS SO. Nine live-looking buttons over a run
    // that is already lost is the "doomed-but-open" board the design gate raises
    // against other games; the run has six units of clock left and no line, and
    // the board must not pretend otherwise.
    const verbs = all(root).filter((node) => node.dataset.action !== undefined);
    assert.equal(verbs.length, 9);
    assert.ok(verbs.every((node) => node.disabled === true), "a doomed board still offers a move");
    assert.ok(verbs.every((node) => node.attributes.get("aria-label").includes("no longer brings the target up")
      || node.attributes.get("aria-label").includes("Refused")), "a dead verb must say why in its label");
  });
});

import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  CARD_STATES,
  GAME_RACK,
  RACK_ENTRY_KEYS,
  SESSION_LENGTHS,
  buildRack,
  loadRackEntry,
  mountGameRack,
  resultSummary,
  verificationRows,
} from "../src/game-rack.js";
import { INSTALLED_GAME_IDS } from "../src/mission-launcher.js";
import { SHAPES, descriptorShape } from "../src/descriptor-shape.js";
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
  removeAttribute(name) { this.attributes.delete(name); }
  addEventListener(name, callback) { this.listeners.set(name, [...(this.listeners.get(name) ?? []), callback]); }
  dispatch(name) { for (const callback of this.listeners.get(name) ?? []) callback({}); }
}

function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

const all = (node) => [node, ...node.children.flatMap(all)];
const mission = (gameId, missionId) => ({
  gameId,
  missionId,
  title: gameId,
  activatedManifest: `sha256:${"a".repeat(64)}`,
  contentEpoch: 1,
  curatorCounter: 7,
  activation: { state: "detached-signature-required" },
  instanceBinding: "per-run-hidden-draw",
  instanceDisclosure: "oracle-only",
  derivationModule: "Dregg2.Games.PathOfAngels.HiddenInstance",
  rewardClass: "non-economic-demo",
  privacyGrade: "public",
});

test("every shipped presentation record parses, and the exact field set is enforced", () => {
  for (const entry of GAME_RACK) loadRackEntry(entry);
  assert.equal(new Set(GAME_RACK.map((entry) => entry.gameId)).size, GAME_RACK.length);

  const [signal] = GAME_RACK;
  assert.throws(() => loadRackEntry({ ...signal, extra: 1 }), { code: "rack-field" });
  assert.throws(() => loadRackEntry({ ...signal, session: "epic" }), { code: "rack-session" });
  assert.throws(() => loadRackEntry({ ...signal, shape: "machine" }), { code: "rack-shape-claim" });
  assert.throws(() => loadRackEntry({ ...signal, flavor: "a\nb" }), { code: "rack-copy" });
  assert.throws(() => loadRackEntry({ ...signal, gameId: "Signal" }), { code: "rack-game-id" });
  assert.throws(() => loadRackEntry({ ...signal, columns: 0 }), { code: "rack-columns" });
  // Widening the set is the refusal that matters: a record with a new field is
  // a record this rack was never taught, not one it should render anyway.
  const withoutName = { ...signal };
  delete withoutName.name;
  assert.throws(() => loadRackEntry(withoutName), { code: "rack-field" });
  assert.deepEqual([...RACK_ENTRY_KEYS].sort(), Object.keys(signal).sort());
});

test("a record cannot know a length without a shape, and a berth claims neither", () => {
  const [signal] = GAME_RACK;
  assert.throws(() => loadRackEntry({ ...signal, session: null }), { code: "rack-half-taught" });
  assert.throws(() => loadRackEntry({ ...signal, shape: null }), { code: "rack-half-taught" });

  // ⚠ THE RACK NO LONGER CARRIES A BERTH, and this test used to require one.
  // Every record now claims a length and a shape, because every game on the board
  // has a controller that can play it — Artificer Logic, Vent Crawl and Deck
  // Descent were the last three berths and all three were wired on 2026-08-07. An
  // assertion that a berth EXISTS would now be an assertion that the rack is
  // incomplete, which is a strange thing to demand. What must stay true is the
  // RULE, so it is checked in both directions: any berth on the rack is fully
  // absent and uninstalled, and the loader still refuses a half-taught record.
  for (const berth of GAME_RACK.filter((entry) => entry.session === null)) {
    assert.equal(berth.shape, null, `${berth.gameId} states a shape for a game nobody has written`);
    assert.ok(!INSTALLED_GAME_IDS.includes(berth.gameId), `${berth.gameId} has a controller but no shape`);
  }
  const berth = loadRackEntry({ ...signal, gameId: "nobody-has-written-this", name: "Berth", session: null, shape: null });
  assert.equal(berth.session, null);
  assert.equal(berth.shape, null);
  assert.throws(() => loadRackEntry({ ...berth, session: "standard" }), { code: "rack-half-taught" });
  assert.throws(() => loadRackEntry({ ...berth, shape: signal.shape }), { code: "rack-half-taught" });
});

test("every installed controller has a fully taught presentation record", () => {
  const byGame = new Map(GAME_RACK.map((entry) => [entry.gameId, entry]));
  for (const gameId of INSTALLED_GAME_IDS) {
    const entry = byGame.get(gameId);
    assert.ok(entry, `${gameId} is installed in the launcher with no presentation record`);
    assert.notEqual(entry.session, null, `${gameId} is installed and declares no session length`);
    assert.notEqual(entry.shape, null, `${gameId} is installed and declares no shape`);
    assert.ok(Object.hasOwn(SESSION_LENGTHS, entry.session));
  }
});

test("the shape a record claims is the shape the emitted descriptor actually has", async () => {
  const games = new URL("../../poa/artifacts/poag1/games/", import.meta.url);
  const byGame = new Map(GAME_RACK.map((entry) => [entry.gameId, entry]));
  const emitted = [
    ["signal-triangulation", JSON.parse(await readFile(new URL("signal-triangulation.json", games), "utf8"))],
    ["relay-repair", JSON.parse(await readFile(new URL("relay-repair.json", games), "utf8"))],
    ["salvage-lock", JSON.parse(await readFile(new URL("salvage-lock.json", games), "utf8"))],
    ["black-box-reconstruction", JSON.parse(await readFile(new URL("black-box-reconstruction.json", games), "utf8"))],
  ];
  // ⚠ The three games whose descriptors are EMITTED but not yet signed are checked
  // against their real bytes too, out of `poa/artifacts/poag1-pending/`. A card
  // that claimed a shape its descriptor did not have would otherwise go unnoticed
  // until the ceremony, which is the worst possible moment to find out.
  const pending = new URL("../../poa/artifacts/poag1-pending/games/", import.meta.url);
  for (const gameId of ["artificer-logic", "vent-crawl", "deck-descent"]) {
    const doc = JSON.parse(await readFile(new URL(`${gameId}.json`, pending), "utf8"));
    emitted.push([gameId, doc]);
  }
  for (const [gameId, doc] of emitted) {
    assert.equal(byGame.get(gameId).shape, descriptorShape(doc), `${gameId}'s card claims a shape its descriptor does not have`);
  }
  assert.equal(emitted.length, GAME_RACK.length, "every record on the rack must be checked against real emitted bytes");
});

test("the signed catalog decides what is open; a presentation record cannot enrol itself", async () => {
  const { missions } = await canonicalDescriptors();
  const cards = buildRack({ missions, installed: INSTALLED_GAME_IDS });
  const byGame = new Map(cards.map((card) => [card.gameId, card]));
  assert.equal(cards.length, GAME_RACK.length);
  for (const card of cards) assert.ok(CARD_STATES.includes(card.state));

  for (const gameId of ["signal-triangulation", "relay-repair", "salvage-lock", "black-box-reconstruction"]) {
    assert.equal(byGame.get(gameId).state, "open");
    assert.equal(byGame.get(gameId).playable, true);
    assert.equal(byGame.get(gameId).seal, null);
  }
  // Black Box is now enrolled by the signed counter-8 catalog and installed, so
  // it opens like the rest. The honest sealed slot — installed but NOT enrolled —
  // is still a real state, checked directly against a catalog that withholds it:
  // a presentation record still cannot enrol its own game.
  const withheld = buildRack({ missions: missions.filter((mission) => mission.gameId !== "black-box-reconstruction"), installed: INSTALLED_GAME_IDS });
  const sealedBlackBox = withheld.find((card) => card.gameId === "black-box-reconstruction");
  assert.equal(sealedBlackBox.state, "sealed");
  assert.match(sealedBlackBox.seal.label, /AWAITING CURATOR ACTIVATION/);
  // Installed and NOT enrolled: Artificer Logic, Vent Crawl and Deck Descent have
  // controllers and no mission in this counter's signed catalog, which is the
  // sealed slot in its natural habitat rather than a synthesised one. `Emit.lean`
  // enrols all three; the counter that carries their descriptors is unsigned.
  for (const gameId of ["artificer-logic", "vent-crawl", "deck-descent"]) {
    const sealed = byGame.get(gameId);
    assert.equal(sealed.state, "sealed", `${gameId} is installed, so it cannot be a berth`);
    assert.equal(sealed.playable, false);
    assert.match(sealed.seal.label, /AWAITING CURATOR ACTIVATION/);
    // ⚠ A sealed card MAY state its length and shape, because a client that can
    // play the game is not guessing about it. Only a berth must not.
    assert.notEqual(sealed.session, null);
    assert.notEqual(sealed.shape, null);
  }

  // Enrolled with no controller is the one combination that is a defect, and it
  // is LOUD rather than quietly absent from the board.
  const orphan = buildRack({ missions, installed: ["signal-triangulation"] });
  const relay = orphan.find((card) => card.gameId === "relay-repair");
  assert.equal(relay.state, "unsupported");
  assert.equal(relay.playable, false);
  assert.match(relay.seal.copy, /must never approximate a game it was not given/);

  // Every card carries the same anatomy, open or sealed.
  for (const card of cards) {
    for (const field of ["gameId", "name", "flavor", "eyebrow", "sessionLabel", "state", "verification"]) {
      assert.ok(card[field] !== undefined, `${card.gameId} card is missing ${field}`);
    }
    assert.ok(card.verification.length > 0);
  }
});

test("a catalog naming a game with no presentation record refuses rather than dropping it", () => {
  assert.throws(
    () => buildRack({ missions: [mission("stowaway-poker", 9)], installed: [] }),
    { code: "rack-unknown-mission" },
  );
  // A berth the catalog enrols has no controller either, so it cannot open: it
  // renders as the loud defect state rather than as a playable card.
  const berth = buildRack({ missions: [mission("deck-descent", 9)], installed: [] })
    .find((card) => card.gameId === "deck-descent");
  assert.equal(berth.state, "unsupported");
  assert.equal(berth.playable, false);
});

test("a half-taught record can never reach the open state, even fully installed", () => {
  const halfTaught = GAME_RACK.map((entry) => (
    entry.gameId === "relay-repair" ? { ...entry, session: null, shape: null } : entry
  ));
  assert.throws(
    () => buildRack({ entries: halfTaught, missions: [mission("relay-repair", 2)], installed: ["relay-repair"] }),
    { code: "rack-half-taught" },
  );
  // …and the same records are fine while nothing enrols that game.
  const cards = buildRack({ entries: halfTaught, missions: [], installed: ["relay-repair"] });
  assert.equal(cards.find((card) => card.gameId === "relay-repair").state, "sealed");
});

test("the verification fold is derived from the mission, never authored per game", () => {
  const rows = verificationRows(mission("relay-repair", 2));
  const terms = rows.map((row) => row.term);
  assert.deepEqual(terms, ["Rules authority", "Activation", "Hidden instance", "Derived by", "Reward class", "Run status"]);
  assert.match(rows[0].detail, /content epoch 1\.7/);
  assert.match(rows[1].detail, /detached-signature-required/);
  assert.match(rows[2].detail, /per-run-hidden-draw · oracle-only/);
  assert.match(rows.at(-1).detail, /local and unsettled/);
  // ⚠ The forbidding copy was RELOCATED, not deleted: the activation state a
  // first-time player used to meet before any game still exists, one fold away.
  const sealed = verificationRows(null);
  assert.match(sealed[0].detail, /not enrolled in the signed catalog/);
});

test("a practice best is never merged into, or displayed as, a judged best", () => {
  const empty = resultSummary(undefined);
  assert.match(empty.headline, /No run recorded/);
  assert.equal(empty.scored, false);

  const practiceOnly = resultSummary({
    practice: [
      { status: "practice", outcome: "solved", actions: 6, at: 10 },
      { status: "practice", outcome: "unsolved", actions: 12, at: 20 },
    ],
    judged: [],
  });
  assert.equal(practiceOnly.headline, "practice best 6");
  assert.equal(practiceOnly.scored, false);
  assert.match(practiceOnly.detail, /last: practice/);

  const both = resultSummary({
    practice: [{ status: "practice", outcome: "solved", actions: 3, at: 10 }],
    judged: [{ status: "finalized", outcome: "solved", actions: 9, at: 20 }],
  });
  // The practice 3 is better and is still NOT the judged number.
  assert.equal(both.headline, "judged best 9 · practice best 3");
  assert.equal(both.scored, true);
});

test("the rack renders one card shape, and only open cards get a play control", async () => {
  const { missions } = await canonicalDescriptors();
  const cards = buildRack({ missions, installed: INSTALLED_GAME_IDS });
  withFakeDocument(() => {
    const root = new FakeElement("div");
    const opened = [];
    mountGameRack(root, cards, { onOpen: (gameId) => opened.push(gameId) });
    assert.equal(root.children.length, cards.length);

    for (const article of root.children) {
      const nodes = all(article);
      assert.equal(nodes.filter((node) => node.className === "rack-card__name").length, 1);
      assert.equal(nodes.filter((node) => node.className === "rack-card__flavor").length, 1);
      assert.equal(nodes.filter((node) => node.className === "rack-card__length").length, 1);
      assert.equal(nodes.filter((node) => node.className === "verify-fold").length, 1);
      const play = nodes.filter((node) => node.dataset.openGame !== undefined);
      assert.equal(play.length, article.dataset.state === "open" ? 1 : 0);
      // Seven folds on one board need seven names by ear, and each label must
      // still start with the visible word so the two never disagree.
      const [summary] = nodes.filter((node) => node.className === "verify-fold__summary");
      const name = nodes.find((node) => node.className === "rack-card__name").textContent;
      assert.equal(summary.attributes.get("aria-label"), `Verification, ${name}`);
      assert.ok(summary.attributes.get("aria-label").startsWith(summary.textContent));
    }

    const openCard = root.children.find((article) => article.dataset.state === "open");
    all(openCard).find((node) => node.dataset.openGame !== undefined).dispatch("click");
    assert.deepEqual(opened, [openCard.dataset.game]);
  });
});

test("shapes the rack may claim are exactly the shapes the router can decide", () => {
  const claimed = new Set(GAME_RACK.map((entry) => entry.shape).filter((shape) => shape !== null));
  for (const shape of claimed) assert.ok(Object.values(SHAPES).includes(shape));
});

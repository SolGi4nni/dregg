import assert from "node:assert/strict";
import { test } from "node:test";
import { launchCatalogMission } from "../src/mission-launcher.js";
import { salvagePracticeOracle } from "../src/salvage-runtime.js";
import { canonicalDescriptors } from "./canonical-descriptors.mjs";

class FakeElement {
  constructor(tagName = "div") {
    this.tagName = tagName.toUpperCase();
    this.children = [];
    this.attributes = new Map();
    this.dataset = {};
    this.className = "";
    this.textContent = "";
    this.disabled = false;
    this.hidden = false;
    this.tabIndex = -1;
    this.listeners = new Map();
  }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  removeAttribute(name) { this.attributes.delete(name); }
  addEventListener(name, callback) { this.listeners.set(name, [...(this.listeners.get(name) ?? []), callback]); }
  removeEventListener(name, callback) { this.listeners.set(name, (this.listeners.get(name) ?? []).filter((entry) => entry !== callback)); }
  focus() { for (const callback of this.listeners.get("focus") ?? []) callback({}); }
}

function withDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

const mission = (missionId, gameId) => ({ missionId, gameId });

test("each exact catalog game id launches only its matching browser controller", async () => {
  const descriptors = await canonicalDescriptors();
  withDocument(() => {
    const signalRoot = new FakeElement();
    const finiteRoot = new FakeElement();
    let signalLaunches = 0;
    const signal = launchCatalogMission({
      mission: mission(1, "signal-triangulation"),
      descriptor: { gameId: "signal-triangulation", missionId: 1 },
      signalRoot,
      finiteRoot,
      launchSignal: () => { signalLaunches += 1; },
    });
    assert.equal(signal.gameId, "signal-triangulation");
    assert.equal(signalLaunches, 1);
    assert.equal(signalRoot.hidden, false);
    assert.equal(finiteRoot.hidden, true);

    const relayId = descriptors.relay.authority.missionId;
    const relay = launchCatalogMission({
      mission: mission(relayId, "relay-repair"),
      descriptor: descriptors.relay,
      signalRoot,
      finiteRoot,
      launchSignal() {},
      callbacks: { session: { mode: "practice", member: 1 } },
    });
    assert.equal(relay.gameId, "relay-repair");
    assert.equal(relay.controller.getRun().gameId, "relay-repair");
    assert.equal(signalRoot.hidden, true);
    assert.equal(finiteRoot.hidden, false);
    relay.controller.destroy();

    const salvageId = descriptors.salvage.authority.missionId;
    const salvage = launchCatalogMission({
      mission: mission(salvageId, "salvage-lock"),
      descriptor: descriptors.salvage,
      signalRoot,
      finiteRoot,
      launchSignal() {},
      callbacks: { session: { mode: "practice", member: 2, oracle: salvagePracticeOracle(descriptors.salvage, 2) } },
    });
    assert.equal(salvage.gameId, "salvage-lock");
    assert.equal(salvage.controller.getRun().gameId, "salvage-lock");
    salvage.controller.destroy();
  });
});

test("unknown games refuse and descriptor mismatch cannot fall back to Signal", () => withDocument(() => {
  const signalRoot = new FakeElement();
  const finiteRoot = new FakeElement();
  let signalLaunches = 0;
  const launchSignal = () => { signalLaunches += 1; };
  assert.throws(() => launchCatalogMission({
    mission: mission(7, "unknown-game"),
    descriptor: { gameId: "unknown-game", authority: { missionId: 7 } },
    signalRoot,
    finiteRoot,
    launchSignal,
  }), { code: "mission-game-unsupported" });
  assert.throws(() => launchCatalogMission({
    mission: mission(7, "relay-repair"),
    descriptor: { gameId: "signal-triangulation", missionId: 7 },
    signalRoot,
    finiteRoot,
    launchSignal,
  }), { code: "mission-controller-mismatch" });
  assert.equal(signalLaunches, 0);
}));


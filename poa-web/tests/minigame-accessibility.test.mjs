import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { mountRelayRepair } from "../src/relay-controller.js";
import { mountSalvageLock } from "../src/salvage-controller.js";
import { nextRovingIndex } from "../src/finite-table-controller.js";
import { salvagePracticeOracle } from "../src/salvage-runtime.js";
import { canonicalDescriptors } from "./canonical-descriptors.mjs";

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
    const callbacks = this.listeners.get(name) ?? [];
    callbacks.push(callback);
    this.listeners.set(name, callbacks);
  }
  removeEventListener(name, callback) {
    this.listeners.set(name, (this.listeners.get(name) ?? []).filter((candidate) => candidate !== callback));
  }
  dispatch(name, extra = {}) {
    const event = { key: undefined, preventDefault() { this.defaultPrevented = true; }, ...extra };
    for (const callback of this.listeners.get(name) ?? []) callback(event);
    return event;
  }
  focus() { this.focused = true; this.dispatch("focus"); }
}

function all(root) {
  return [root, ...root.children.flatMap(all)];
}

function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

test("roving keyboard navigation covers rows, columns, Home, and End", () => {
  assert.equal(nextRovingIndex(0, "ArrowRight", 6, 3), 1);
  assert.equal(nextRovingIndex(0, "ArrowLeft", 6, 3), 5);
  assert.equal(nextRovingIndex(1, "ArrowDown", 6, 3), 4);
  assert.equal(nextRovingIndex(1, "ArrowUp", 6, 3), 4);
  assert.equal(nextRovingIndex(4, "Home", 6, 3), 0);
  assert.equal(nextRovingIndex(1, "End", 6, 3), 5);
  assert.equal(nextRovingIndex(2, "Enter", 6, 3), 2);
});

test("Relay mounts native labeled buttons, a live region, and keyboard focus movement", async () => {
  const { relay } = await canonicalDescriptors();
  withFakeDocument(() => {
    const root = new FakeElement("div");
    const controller = mountRelayRepair(root, relay, { session: { mode: "practice", member: 3 } });
    const nodes = all(root);
    const buttons = nodes.filter((node) => node.tagName === "BUTTON" && node.dataset.action);
    const live = nodes.find((node) => node.attributes.get("role") === "status");
    assert.equal(buttons.length, 5);
    assert.ok(buttons.every((button) => button.attributes.has("aria-label")));
    assert.equal(live.attributes.get("aria-live"), "polite");
    assert.equal(buttons[0].tabIndex, 0);
    const event = buttons[0].dispatch("keydown", { key: "ArrowRight" });
    assert.equal(event.defaultPrevented, true);
    assert.equal(buttons[1].tabIndex, 0);
    assert.equal(buttons[1].focused, true);
    buttons[0].dispatch("click");
    assert.equal(controller.getRun().steps.length, 1);
    assert.equal(controller.getRun().member, 3);
    assert.equal(buttons[0].attributes.get("aria-pressed"), "true");
    // Per-run-open: the board is named on screen, because prices are the game.
    assert.match(live.textContent, /Board 3 of 8/);
  });
});

test("Salvage renders no glyph anywhere, and parks rather than guessing a sealed pair", async () => {
  const { salvage } = await canonicalDescriptors();
  withFakeDocument(() => {
    const root = new FakeElement("div");
    // A judged session has no local oracle: the controller must ASK, not assume.
    const controller = mountSalvageLock(root, salvage, {
      session: {
        mode: "judged",
        opening: {
          slot: 3,
          mission_id: salvage.authority.missionId,
          commitment: "a".repeat(64),
          curator_pubkey: "b".repeat(64),
          signature: "c".repeat(128),
        },
      },
    });
    const buttons = () => all(root).filter((node) => node.tagName === "BUTTON" && node.dataset.action);
    assert.match(buttons()[0].attributes.get("aria-label"), /sealed/);

    buttons()[0].dispatch("click");
    assert.equal(controller.getRun().steps.length, 1);
    assert.match(buttons()[0].attributes.get("aria-label"), /face up/);
    assert.equal(buttons()[0].attributes.get("aria-pressed"), "true");

    // The second plate is an oracle row. With no oracle in the session the
    // controller parks and says so; it does not pick a branch.
    buttons()[1].dispatch("click");
    assert.equal(controller.pendingAction(), "slot-1");
    assert.equal(controller.getRun().steps.length, 1, "a parked oracle row must not advance the run");
    assert.ok(buttons().every((button) => button.disabled), "controls are frozen while the host is being asked");

    controller.resolveOracle("mismatch");
    assert.equal(controller.pendingAction(), null);
    assert.deepEqual(controller.getRun().steps.map((step) => step.resolution), [null, "mismatch"]);

    // ⚠ The standing question: could a reader reconstruct the board from what is
    // on screen? Nothing rendered may carry a glyph identity.
    const rendered = all(root).map((node) => `${node.textContent} ${[...node.attributes.values()].join(" ")}`).join(" ");
    assert.doesNotMatch(rendered, /glyph/i);
    for (const board of salvage.instance.practice.boards.slice(0, 8)) {
      assert.ok(!rendered.includes(board.join("")), "a practice board arrangement leaked into the rendered DOM");
    }
  });
});

test("a Salvage practice session answers itself and says PRACTICE on screen", async () => {
  const { salvage } = await canonicalDescriptors();
  withFakeDocument(() => {
    const root = new FakeElement("div");
    const controller = mountSalvageLock(root, salvage, {
      session: { mode: "practice", member: 0, oracle: salvagePracticeOracle(salvage, 0) },
    });
    const buttons = () => all(root).filter((node) => node.tagName === "BUTTON" && node.dataset.action);
    buttons()[0].dispatch("click");
    buttons()[1].dispatch("click");
    // Board 0 is [0,0,1,1,2,2]: plates 0 and 1 pair, and no host was involved.
    assert.equal(controller.pendingAction(), null);
    assert.deepEqual(controller.getRun().steps.map((step) => step.resolution), [null, "match"]);
    const boundary = all(root).find((node) => node.className?.includes("boundary"));
    assert.match(boundary.textContent, /PRACTICE/);
    assert.match(boundary.textContent, /nothing here is scored/);
  });
});

test("minigame controls retain touch targets, focus visibility, and mobile layout", async () => {
  const css = await readFile(new URL("../minigames.css", import.meta.url), "utf8");
  assert.match(css, /min-height:\s*48px/);
  assert.match(css, /touch-action:\s*manipulation/);
  assert.match(css, /:focus-visible/);
  assert.match(css, /@media\s*\(max-width:/);
});

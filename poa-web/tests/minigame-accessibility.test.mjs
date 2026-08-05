import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { mountRelayRepair } from "../src/relay-controller.js";
import { mountSalvageLock } from "../src/salvage-controller.js";
import { nextRovingIndex } from "../src/finite-table-controller.js";
import { loadRelayRepairDescriptor } from "../src/relay-runtime.js";
import { loadSalvageLockDescriptor } from "../src/salvage-runtime.js";
import { fixtureAuthority, relayFixture, salvageFixture } from "./finite-table-fixtures.mjs";

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

test("Relay mounts native labeled buttons, a live region, and keyboard focus movement", () => withFakeDocument(() => {
  const root = new FakeElement("div");
  const descriptor = loadRelayRepairDescriptor(relayFixture(), fixtureAuthority());
  const controller = mountRelayRepair(root, descriptor);
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
  assert.equal(controller.getRun().stateId, "r1");
  assert.equal(buttons[0].attributes.get("aria-pressed"), "true");
}));

test("Salvage conceals sealed glyphs and exposes only literal emitted-view selections", () => withFakeDocument(() => {
  const root = new FakeElement("div");
  const descriptor = loadSalvageLockDescriptor(salvageFixture(), fixtureAuthority());
  const controller = mountSalvageLock(root, descriptor);
  const buttons = all(root).filter((node) => node.tagName === "BUTTON" && node.dataset.action);
  assert.match(buttons[0].attributes.get("aria-label"), /glyph concealed/);
  assert.doesNotMatch(buttons[0].attributes.get("aria-label"), /Glyph A/);
  buttons[0].dispatch("click");
  assert.equal(controller.getRun().stateId, "s1");
  assert.match(buttons[0].attributes.get("aria-label"), /glyph-2, exposed/);
  assert.equal(buttons[0].attributes.get("aria-pressed"), "true");
}));

test("minigame controls retain touch targets, focus visibility, and mobile layout", async () => {
  const css = await readFile(new URL("../minigames.css", import.meta.url), "utf8");
  assert.match(css, /min-height:\s*48px/);
  assert.match(css, /touch-action:\s*manipulation/);
  assert.match(css, /:focus-visible/);
  assert.match(css, /@media\s*\(max-width:/);
});

import assert from "node:assert/strict";
import { webcrypto } from "node:crypto";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { mountExpeditionLab, nextExpeditionActionIndex } from "../labs/expedition-lab-controller.js";
import {
  fetchBuiltinExpeditionDescriptor,
  loadExpeditionDescriptor,
} from "../labs/expedition-lab-runtime.js";

class FakeElement {
  constructor(tagName) {
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
    if (name === "click" && this.disabled) return event;
    for (const callback of this.listeners.get(name) ?? []) callback(event);
    return event;
  }
  focus() { this.focused = true; this.dispatch("focus"); }
}

function all(root) {
  return [root, ...root.children.flatMap(all)];
}

async function table(builtIn = false) {
  const fixture = await readFile(new URL("../labs/expedition-demonstrator.fixture.json", import.meta.url), "utf8");
  if (!builtIn) return loadExpeditionDescriptor(JSON.parse(fixture));
  if (!globalThis.crypto) globalThis.crypto = webcrypto;
  const provenance = await readFile(new URL("../labs/expedition-demonstrator.provenance.json", import.meta.url), "utf8");
  const fetchImpl = async (url) => ({
    ok: true,
    status: 200,
    url: String(url),
    async text() { return String(url).includes("provenance") ? provenance : fixture; },
  });
  return fetchBuiltinExpeditionDescriptor("https://fixture.invalid/expedition.json", "https://fixture.invalid/provenance.json", { fetchImpl });
}

async function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return await callback(); } finally { globalThis.document = previous; }
}

test("action-grid keyboard movement stays truthful across responsive column counts", () => {
  assert.equal(nextExpeditionActionIndex(0, "ArrowRight", 16), 1);
  assert.equal(nextExpeditionActionIndex(0, "ArrowLeft", 16), 15);
  assert.equal(nextExpeditionActionIndex(1, "ArrowDown", 16), 2);
  assert.equal(nextExpeditionActionIndex(1, "ArrowUp", 16), 0);
  assert.equal(nextExpeditionActionIndex(9, "Home", 16), 0);
  assert.equal(nextExpeditionActionIndex(1, "End", 16), 15);
  assert.equal(nextExpeditionActionIndex(4, "Enter", 16), 4);
});

test("the mounted lab exposes all accepted and refused rows with native labeled buttons", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const descriptor = await table();
  const controller = mountExpeditionLab(root, descriptor);
  const nodes = all(root);
  const actions = nodes.filter((node) => node.tagName === "BUTTON" && node.dataset.action);
  const routes = nodes.filter((node) => node.tagName === "BUTTON" && node.dataset.route);
  const live = nodes.find((node) => node.attributes.get("role") === "status");
  assert.equal(actions.length, 16);
  assert.equal(routes.length, 2);
  assert.equal(actions.filter((button) => button.className.includes("expedition-action--accept")).length, 2);
  assert.ok(actions.every((button) => button.disabled === false));
  assert.ok(actions.every((button) => !button.attributes.has("aria-disabled")));
  assert.ok(actions.every((button) => button.attributes.has("aria-label")));
  assert.match(actions.find((button) => button.dataset.action === "confront:21:13").attributes.get("aria-label"), /containment role/i);
  assert.match(actions.find((button) => button.dataset.action === "traverse:1001").attributes.get("aria-label"), /Wrong Origin Or Phase/);
  assert.ok(all(root).some((node) => node.textContent === "UNTRUSTED INSTRUMENT"));
  const untrustedSurface = all(root).map((node) => node.textContent).join("\n");
  assert.doesNotMatch(untrustedSurface, /lean|pinned|provenance-verified/i);
  assert.equal(live.attributes.get("aria-live"), "polite");
  assert.equal(actions[0].tabIndex, 0);
  assert.doesNotThrow(() => controller.dispatch("absent-action"));
  assert.equal(controller.getRun().actions.length, 0);
  assert.match(live.textContent, /was not dispatched/);
  assert.doesNotThrow(() => controller.replayRoute("absent-route"));
  assert.equal(controller.getRun().actions.length, 0);
  assert.match(live.textContent, /Route was not replayed/);

  const keyEvent = actions[0].dispatch("keydown", { key: "ArrowRight" });
  assert.equal(keyEvent.defaultPrevented, true);
  assert.equal(actions[1].tabIndex, 0);
  assert.equal(actions[1].focused, true);

  actions[1].dispatch("click");
  assert.equal(controller.getRun().actions.length, 0);
  assert.match(live.textContent, /refused: Wrong Origin Or Phase/);
  actions[0].dispatch("click");
  assert.deepEqual(controller.getRun().actions, ["traverse:1000"]);
  assert.match(live.textContent, /exact table-provided row/);
}));

test("only the provenance-verified built-in receives pinned Lean table language", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  mountExpeditionLab(root, await table(true));
  const text = all(root).map((node) => node.textContent).join("\n");
  assert.match(text, /DECK EXPEDITION \/\/ PINNED LEAN TABLE/);
  assert.match(text, /PROVENANCE \+ OUTPUT PINNED/);
  assert.doesNotMatch(text, /UNTRUSTED INSTRUMENT/);
}));

test("reference-route replay renders extraction receipt, provisional candidate, custody, and transcript", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const descriptor = await table();
  let latestTranscript = null;
  const controller = mountExpeditionLab(root, descriptor, {
    onTranscript: (transcript) => { latestTranscript = JSON.parse(transcript); },
  });
  controller.replayRoute("salvage-relic");
  assert.equal(controller.getRun().terminal, true);
  assert.deepEqual(controller.getRun().lastReceipt.recoveredSalvage, [31]);
  const nodes = all(root);
  const terminal = nodes.find((node) => node.className.includes("expedition-terminal"));
  assert.equal(terminal.hidden, false);
  assert.ok(nodes.some((node) => /Table-provided extraction receipt/.test(node.textContent)));
  assert.ok(nodes.some((node) => node.textContent === "9001"));
  assert.equal(latestTranscript.settlement, "unsettled-local-demonstrator");
  assert.equal(latestTranscript.canon_claim, false);
  assert.equal(latestTranscript.reward_claim, false);
  assert.equal(nodes.filter((node) => node.className === "expedition-transcript-row").length, 9);
  const actions = nodes.filter((node) => node.tagName === "BUTTON" && node.dataset.action);
  assert.ok(actions.every((button) => button.disabled === true));
  assert.doesNotThrow(() => actions[0].dispatch("click"));
  assert.doesNotThrow(() => controller.dispatch("traverse:1000"));
  assert.equal(controller.getRun().actions.length, 8);
}));

test("withdrawal displays a terminal no-receipt edge rather than a fabricated outcome", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const descriptor = await table();
  const controller = mountExpeditionLab(root, descriptor);
  controller.dispatch("withdraw");
  const nodes = all(root);
  assert.equal(controller.getRun().lastEffect, "withdrawn");
  assert.equal(controller.getRun().lastReceipt, null);
  assert.ok(nodes.some((node) => node.textContent === "Run withdrawn"));
  assert.ok(nodes.some((node) => node.textContent === "None provided"));
}));

test("the controller permits the emitted ninth withdrawal edge after eight stranded actions", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const descriptor = await table();
  const controller = mountExpeditionLab(root, descriptor);
  for (const action of [
    "traverse:1000", "traverse:1005", "confront:21:13", "traverse:1006",
    "recover:31:12", "survey:4040:2:11", "traverse:1007", "traverse:1008",
  ]) controller.dispatch(action);
  assert.equal(controller.getRun().actions.length, 8);
  assert.equal(controller.getRun().terminal, false);
  assert.doesNotThrow(() => controller.dispatch("withdraw"));
  assert.equal(controller.getRun().actions.length, 9);
  assert.equal(controller.getRun().terminal, true);
  assert.equal(controller.getRun().lastEffect, "withdrawn");
  const actionButtons = all(root).filter((node) => node.tagName === "BUTTON" && node.dataset.action);
  assert.ok(actionButtons.every((button) => button.disabled));
}));

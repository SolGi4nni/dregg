import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  flightRecorderShareText,
  mountFlightRecorder,
  nextFlightRecorderIndex,
  shortFlightDigest,
} from "../labs/flight-recorder-controller.js";
import { assembleFlightRecorder } from "../labs/flight-recorder-runtime.js";

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
    if (name === "click" && this.disabled) return event;
    for (const callback of this.listeners.get(name) ?? []) callback(event);
    return event;
  }
  focus() { this.focused = true; this.dispatch("focus"); }
}

function all(root) {
  return [root, ...root.children.flatMap(all)];
}

async function recorder(kind = "demo-fixture") {
  const document = JSON.parse(await readFile(new URL("../labs/flight-recorder-demo.fixture.json", import.meta.url), "utf8"));
  return assembleFlightRecorder(document.status, document.transitions, kind === "demo-fixture"
    ? { kind, label: document.label }
    : { kind, apiBaseUrl: "https://node.invalid", authorityId: document.status.authority_id });
}

async function withFakeDocument(callback) {
  const prior = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return await callback(); } finally { globalThis.document = prior; }
}

test("digest shortening and keyboard traversal are deterministic", () => {
  assert.equal(shortFlightDigest("a".repeat(64), 4), "aaaa…aaaa");
  assert.equal(nextFlightRecorderIndex(0, "ArrowUp", 3), 2);
  assert.equal(nextFlightRecorderIndex(2, "ArrowDown", 3), 0);
  assert.equal(nextFlightRecorderIndex(1, "Home", 3), 0);
  assert.equal(nextFlightRecorderIndex(1, "End", 3), 2);
  assert.equal(nextFlightRecorderIndex(1, "Enter", 3), 1);
});

test("demo fallback is impossible to mistake for a live recorder", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  mountFlightRecorder(root, await recorder());
  const surface = all(root).map((node) => node.textContent).join("\n");
  assert.match(surface, /DEMO FALLBACK \/\/ REHEARSAL ONLY/);
  assert.match(surface, /DEMO · NOT LIVE/);
  assert.match(surface, /Crown Relay rehearsal/);
  assert.match(surface, /not connected to a node/i);
  assert.doesNotMatch(surface, /LIVE PUBLIC NODE VIEW/);
}));

test("live view renders the current head, all links, public cross-references, and honest finality", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const mounted = mountFlightRecorder(root, await recorder("live-api"));
  const nodes = all(root);
  const surface = nodes.map((node) => node.textContent).join("\n");
  assert.match(surface, /LIVE PUBLIC NODE VIEW/);
  assert.match(surface, /LIVE REDACTED API/);
  assert.match(surface, /Every transmission leaves a wake/);
  assert.match(surface, /NO FINALITY CERTIFICATE IN THIS VIEW/);
  assert.match(surface, /Canon, configuration, and judge input\/output bytes never enter this surface/);
  assert.equal(nodes.filter((node) => node.className === "flight-event").length, 3);
  assert.equal(nodes.filter((node) => node.className === "flight-event__button").length, 3);
  assert.equal(mounted.selectedTransition().sequence, 3);
  assert.doesNotMatch(surface, /c3c3c3c3|d3d3d3d3/);
}));

test("timeline is keyboard navigable and selection opens only redacted coordinates", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const mounted = mountFlightRecorder(root, await recorder("live-api"));
  const buttons = all(root).filter((node) => node.className === "flight-event__button");
  assert.deepEqual(buttons.map((button) => button.tabIndex), [-1, -1, 0]);
  const event = buttons[2].dispatch("keydown", { key: "ArrowDown" });
  assert.equal(event.defaultPrevented, true);
  assert.equal(buttons[0].focused, true);
  assert.equal(mounted.selectedTransition().sequence, 1);
  buttons[1].dispatch("click");
  assert.equal(mounted.selectedTransition().sequence, 2);
  const detail = all(root).find((node) => node.id === "flight-event-detail");
  const detailText = all(detail).map((node) => node.textContent).join("\n");
  assert.match(detailText, /Transmission 2 · commit 104/);
  assert.match(detailText, /Turn|Receipt|Predecessor|Successor/);
  assert.doesNotMatch(detailText, /c2c2c2c2|d2d2d2d2/);
  assert.match(detailText, /judge input\/output bytes never enter this surface/);
}));

test("replay marks every public link and narrates exactly the bounded check", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const mounted = mountFlightRecorder(root, await recorder("live-api"));
  mounted.replay();
  const nodes = all(root);
  const timeline = nodes.find((node) => node.className === "flight-timeline");
  const live = nodes.find((node) => node.attributes.get("role") === "status");
  assert.equal(timeline.attributes.get("data-replay"), "active");
  assert.ok(nodes.filter((node) => node.className === "flight-event__button").every((button) => button.attributes.get("data-link") === "checked"));
  assert.match(live.textContent, /Replayed 3 contiguous public digest links/);
  assert.match(live.textContent, /final successor resolves to the displayed head/);
}));

test("share text is redacted, source-labeled, and preserves the finality caveat", async () => {
  const demo = await recorder();
  const text = flightRecorderShareText(demo);
  assert.match(text, /demo rehearsal fixture/);
  assert.match(text, /Replay window: 1–3/);
  assert.match(text, /Consensus finality is not asserted/);
  assert.doesNotMatch(text, /judge|config|canon/i);
});

test("buttons are native, touch-sized by class, labeled, and refusal-free presentation never hides source state", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  mountFlightRecorder(root, await recorder());
  const nodes = all(root);
  const buttons = nodes.filter((node) => node.tagName === "BUTTON");
  const live = nodes.find((node) => node.attributes.get("role") === "status");
  assert.equal(buttons.length, 6);
  assert.ok(buttons.every((button) => !button.attributes.has("aria-disabled")));
  assert.ok(nodes.filter((node) => node.className === "flight-event__button").every((button) => button.attributes.has("aria-label")));
  assert.equal(live.attributes.get("aria-live"), "polite");
  assert.match(live.textContent, /Demo fallback loaded/);
}));

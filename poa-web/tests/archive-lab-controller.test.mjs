import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { mountArchiveLab, nextArchiveLabActionIndex } from "../labs/archive-lab-controller.js";
import { loadArchiveLabDescriptor } from "../labs/archive-lab-runtime.js";

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

async function descriptor() {
  const fixture = await readFile(new URL("../labs/archive-lab-demonstrator.fixture.json", import.meta.url), "utf8");
  return loadArchiveLabDescriptor(JSON.parse(fixture));
}

async function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return await callback(); } finally { globalThis.document = previous; }
}

test("archive action keyboard movement stays linear and layout-independent", () => {
  assert.equal(nextArchiveLabActionIndex(0, "ArrowRight", 8), 1);
  assert.equal(nextArchiveLabActionIndex(0, "ArrowLeft", 8), 7);
  assert.equal(nextArchiveLabActionIndex(2, "ArrowDown", 8), 3);
  assert.equal(nextArchiveLabActionIndex(2, "ArrowUp", 8), 1);
  assert.equal(nextArchiveLabActionIndex(6, "Home", 8), 0);
  assert.equal(nextArchiveLabActionIndex(1, "End", 8), 7);
  assert.equal(nextArchiveLabActionIndex(4, "Enter", 8), 4);
});

test("mounted archive exposes accepted and refused rows as native labeled buttons", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const controller = mountArchiveLab(root, await descriptor());
  const nodes = all(root);
  const actions = nodes.filter((node) => node.tagName === "BUTTON" && node.dataset.action);
  const routes = nodes.filter((node) => node.tagName === "BUTTON" && node.dataset.route);
  const live = nodes.find((node) => node.attributes.get("role") === "status");
  assert.equal(actions.length, 8);
  assert.equal(routes.length, 1);
  assert.equal(actions.filter((button) => button.className.includes("archive-action--accept")).length, 2);
  assert.ok(actions.every((button) => !button.disabled));
  assert.ok(actions.every((button) => !button.attributes.has("aria-disabled")));
  assert.ok(actions.every((button) => button.attributes.has("aria-label")));
  assert.equal(actions[0].tabIndex, 0);
  assert.equal(live.attributes.get("aria-live"), "polite");
  assert.ok(nodes.some((node) => node.textContent === "UNTRUSTED INSTRUMENT"));
  const untrustedSurface = nodes.map((node) => node.textContent).join("\n");
  assert.doesNotMatch(untrustedSurface, /lean|pinned|provenance-verified/i);

  const keyEvent = actions[0].dispatch("keydown", { key: "ArrowLeft" });
  assert.equal(keyEvent.defaultPrevented, true);
  assert.equal(actions[7].tabIndex, 0);
  assert.equal(actions[7].focused, true);

  actions.find((button) => button.dataset.action === "test-current").dispatch("click");
  assert.equal(controller.getRun().actions.length, 0);
  assert.match(live.textContent, /refused: Wrong Phase/i);
  actions.find((button) => button.dataset.action === "screen-current").dispatch("click");
  assert.deepEqual(controller.getRun().actions, ["screen-current"]);
  assert.match(live.textContent, /exact table-provided row/i);
  assert.equal(actions.find((button) => button.dataset.action === "test-current").className.includes("archive-action--accept"), true);
}));

test("the controller reveals specimen fields progressively without inventing hidden evidence", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const controller = mountArchiveLab(root, await descriptor());
  const surface = () => all(root).map((node) => node.textContent).join("\n");
  assert.match(surface(), /Bearing sealed/i);
  assert.doesNotMatch(surface(), /Supports Resonance/i);
  controller.dispatch("screen-current");
  assert.match(surface(), /Supports Resonance/i);
  assert.match(surface(), /Verdict\n?Sealed|Sealed/i);
  controller.dispatch("test-current");
  assert.match(surface(), /Sound/i);
  assert.ok(all(root).some((node) => node.className.includes("archive-specimen--tested")));
}));

test("route replay renders the unique beta record, contradiction, notebook, and terminal controls", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  let transcript = null;
  const controller = mountArchiveLab(root, await descriptor(), {
    onTranscript: (value) => { transcript = JSON.parse(value); },
  });
  assert.equal(controller.replayRoute("unique-research-plan"), true);
  assert.equal(controller.getRun().terminal, true);
  assert.equal(controller.getRun().lastRecord.hypothesis, 0);
  const nodes = all(root);
  const publication = nodes.find((node) => node.className.includes("archive-publication"));
  assert.equal(publication.hidden, false);
  assert.ok(nodes.some((node) => node.textContent === "CONTRADICTION"));
  assert.ok(nodes.some((node) => /beta record/i.test(node.textContent)));
  assert.equal(nodes.filter((node) => node.className === "archive-transcript-row").length, 16);
  assert.ok(nodes.filter((node) => node.tagName === "BUTTON" && node.dataset.action).every((button) => button.disabled));
  assert.equal(transcript.settlement, "unsettled-local-demonstrator");
  assert.equal(transcript.record.canonClaim, false);
  assert.equal(transcript.record.rewardClaim, false);
}));

test("refusals, absent commands, rewind, restart, and bad route replay never throw from UI controls", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const controller = mountArchiveLab(root, await descriptor());
  assert.doesNotThrow(() => controller.dispatch("missing"));
  assert.match(all(root).find((node) => node.attributes.get("role") === "status").textContent, /was not dispatched/i);
  assert.equal(controller.replayRoute("missing"), false);
  assert.equal(controller.getRun().actions.length, 0);
  controller.dispatch("screen-current");
  controller.dispatch("test-current");
  assert.equal(controller.getRun().actions.length, 2);
  controller.rewind();
  assert.deepEqual(controller.getRun().actions, ["screen-current"]);
  controller.restart();
  assert.deepEqual(controller.getRun().actions, []);
}));

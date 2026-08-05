import assert from "node:assert/strict";
import { test } from "node:test";
import { mountGalley, nextGalleyChoiceIndex } from "../src/galley-controller.js";
import {
  createGalleyPendingIntentJournal,
  normalizeGalleyStatus,
  normalizeGalleyUnsignedTurn,
} from "../src/galley-runtime.js";
import {
  GALLEY_ACTOR_PUBLIC_KEY,
  createFixtureGalleyTransport,
  galleyStatus,
  galleyStatusBefore,
  galleyUnsignedTurn,
} from "./galley-fixtures.mjs";

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
    this.href = "";
    this.id = "";
    this.tabIndex = -1;
    this.listeners = new Map();
  }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  addEventListener(name, callback) {
    this.listeners.set(name, [...(this.listeners.get(name) ?? []), callback]);
  }
  dispatch(name, extra = {}) {
    const event = { key: undefined, preventDefault() { this.defaultPrevented = true; }, ...extra };
    if (name === "click" && this.disabled) return event;
    for (const callback of this.listeners.get(name) ?? []) callback(event);
    return event;
  }
  focus() { this.focused = true; }
}

function descendants(node) { return [node, ...node.children.flatMap(descendants)]; }
function visibleText(root) { return descendants(root).map(({ textContent }) => textContent).filter(Boolean).join("\n"); }
function memoryStorage() {
  let value = null;
  return {
    getItem: () => value,
    setItem: (_key, next) => { value = next; },
    removeItem: () => { value = null; },
    value: () => value,
  };
}

function actorProvider({ sign = true, identity = { publicKeyHex: GALLEY_ACTOR_PUBLIC_KEY, profileName: "default" } } = {}) {
  return {
    async getActiveIdentity() {
      if (identity instanceof Error) throw identity;
      return identity;
    },
    ...(sign ? { async signTurnV3() { return { submitted: true }; } } : {}),
  };
}

async function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return await callback(); } finally { globalThis.document = previous; }
}

test("action roving navigation supports arrows plus Home and End", () => {
  assert.equal(nextGalleyChoiceIndex(0, "ArrowRight", 4), 1);
  assert.equal(nextGalleyChoiceIndex(0, "ArrowLeft", 4), 3);
  assert.equal(nextGalleyChoiceIndex(1, "ArrowDown", 4), 3);
  assert.equal(nextGalleyChoiceIndex(1, "ArrowUp", 4), 3);
  assert.equal(nextGalleyChoiceIndex(2, "Home", 4), 0);
  assert.equal(nextGalleyChoiceIndex(0, "End", 4), 3);
  assert.equal(nextGalleyChoiceIndex(2, "Enter", 4), 2);
});

test("arrival renders one clear recurring watch, communal totals, replay records, and next visit", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const transport = createFixtureGalleyTransport();
  const controller = mountGalley(root, { transport, dreggProvider: actorProvider() });
  await controller.ready;

  assert.deepEqual(transport.calls, [{ method: "openWatch", actorPublicKeyHex: GALLEY_ACTOR_PUBLIC_KEY }]);
  const text = visibleText(root);
  assert.match(text, /The Galley is open/);
  assert.match(text, /A station is available/);
  assert.match(text, /Take this watch/);
  assert.match(text, /Public shifts\s+1/);
  assert.match(text, /Local service\s+3/);
  assert.match(text, /A crew shift/);
  assert.match(text, /One station is open/);
  assert.match(text, /Technical evidence/);
  assert.doesNotMatch(text, /holder|sponsor/i);
  assert.equal(descendants(root).filter(({ dataset }) => dataset.galleyAction).length, 1);
  assert.equal(descendants(root).filter(({ className }) => className.includes("galley-step")).length >= 5, true);
}));

test("permissioned identity without a signer gets records but no mutation", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const transport = createFixtureGalleyTransport();
  const controller = mountGalley(root, { transport, dreggProvider: actorProvider({ sign: false }) });
  await controller.ready;
  const action = descendants(root).find(({ dataset }) => dataset.galleyAction);
  assert.equal(action.disabled, true);
  await controller.dispatch(action.dataset.galleyAction);
  assert.equal(transport.calls.some(({ method }) => method === "requestCommand"), false);
  assert.match(descendants(root).find((node) => node.attributes.get("role") === "status").textContent,
    /Dregg turn signer is unavailable/);
}));

test("missing, declined, or malformed identity remains read-only before any node request", async () => withFakeDocument(async () => {
  for (const provider of [
    null,
    actorProvider({ identity: Object.assign(new Error("no"), { name: "DreggUserDeclined" }) }),
    actorProvider({ identity: { publicKeyHex: "AB".repeat(32) } }),
  ]) {
    const root = new FakeElement("main");
    const transport = createFixtureGalleyTransport();
    const controller = mountGalley(root, { transport, dreggProvider: provider });
    await controller.ready;
    assert.deepEqual(transport.calls, []);
    assert.equal(controller.getView(), null);
    assert.match(visibleText(root), /READ-ONLY/);
    assert.match(visibleText(root), /No action, projection, or logbook was requested/);
    assert.match(visibleText(root), /Only an exact signed turn/);
  }
}));

test("signed watch progresses prepare, final turn, pending, exact event, logbook, and return state", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const transport = createFixtureGalleyTransport();
  const journal = createGalleyPendingIntentJournal({ storage: memoryStorage() });
  const controller = mountGalley(root, { transport, dreggProvider: actorProvider(), pendingJournal: journal });
  await controller.ready;
  await controller.dispatch("11".repeat(32));

  assert.deepEqual(transport.calls.map(({ method }) => method), ["openWatch", "requestCommand", "sign", "status"]);
  assert.equal(controller.getView().sequence, 2);
  assert.equal(journal.list().length, 0);
  const text = visibleText(root);
  assert.match(text, /Your shift is in the logbook/);
  assert.match(text, /Your signed shift/);
  assert.match(text, /3 local service recorded/);
  assert.match(text, /Return after the watch rotates/);
  assert.match(text, /EXACT EVENT \+ ADJACENT CHECKSUM/);
  assert.match(text, new RegExp("88".repeat(32)));
  assert.match(text, new RegExp("99".repeat(32)));
  assert.match(text, /canonical Dregg receipt verification is not installed/i);
  assert.equal(descendants(root).filter(({ dataset }) => dataset.galleyAction).length, 0);
  const live = descendants(root).find((node) => node.attributes.get("role") === "status");
  assert.match(live.textContent, /exact final turn hash/);
  assert.equal(live.focused, true);
}));

test("queued, refused, declined, and unknown signing outcomes have distinct durable behavior", async () => withFakeDocument(async () => {
  const finalHash = "88".repeat(32);
  const cases = [
    [{ state: "queued", turnHash: finalHash, outboxId: "outbox-17", error: "Queued for retry" }, 1, /SIGNED \/ QUEUED/],
    [{ state: "refused", turnHash: null, outboxId: null, error: "Cipherclerk is locked" }, 0, /REFUSED \/ NOT SUBMITTED/],
    [{ state: "declined", turnHash: null, outboxId: null, error: "User declined" }, 0, /DECLINED \/ NOT SUBMITTED/],
    [{ state: "error", turnHash: null, outboxId: null, error: "bridge response lost" }, 1, /SIGNING RESULT UNKNOWN/],
  ];
  for (const [signingResult, pendingCount, label] of cases) {
    const root = new FakeElement("main");
    const journal = createGalleyPendingIntentJournal({ storage: memoryStorage() });
    const transport = createFixtureGalleyTransport({ signingResult });
    const controller = mountGalley(root, { transport, dreggProvider: actorProvider(), pendingJournal: journal });
    await controller.ready;
    const outcome = await controller.dispatch("11".repeat(32));
    assert.equal(outcome.state, signingResult.state);
    assert.deepEqual(transport.calls.map(({ method }) => method), ["openWatch", "requestCommand", "sign"]);
    assert.equal(journal.list().length, pendingCount);
    assert.match(visibleText(root), label);
    assert.doesNotMatch(visibleText(root), /Shift observed/);
  }
}));

test("durable intent storage failure stops before signer custody and makes no recovery claim", async () => withFakeDocument(async () => {
  for (const storage of [
    null,
    { getItem: () => null, setItem() { throw new Error("quota exceeded"); }, removeItem() {} },
  ]) {
    const root = new FakeElement("main");
    const transport = createFixtureGalleyTransport();
    const controller = mountGalley(root, {
      transport,
      dreggProvider: actorProvider(),
      pendingJournal: createGalleyPendingIntentJournal({ storage }),
    });
    await controller.ready;
    assert.equal(await controller.dispatch("11".repeat(32)), null);
    assert.deepEqual(transport.calls.map(({ method }) => method), ["openWatch", "requestCommand"],
      "the signer must not see bytes before the intent coordinate is durable");
    const status = descendants(root).find((node) => node.attributes.get("role") === "status").textContent;
    assert.match(status, /DURABLE INTENT STORAGE FAILED/);
    assert.match(status, /Nothing was signed or submitted/);
    assert.doesNotMatch(status, /remains durable|exact recovery/i);
  }
}));

test("final signed hash survives restart and recovers after the earlier status response was lost", async () => withFakeDocument(async () => {
  const storage = memoryStorage();
  const firstJournal = createGalleyPendingIntentJournal({ storage });
  const firstRoot = new FakeElement("main");
  const first = mountGalley(firstRoot, {
    transport: createFixtureGalleyTransport({ pending: true }),
    dreggProvider: actorProvider(),
    pendingJournal: firstJournal,
  });
  await first.ready;
  await first.dispatch("11".repeat(32));
  assert.equal(firstJournal.list()[0].finalTurnHash, "88".repeat(32));
  assert.match(visibleText(firstRoot), /not yet in the journal/i);
  first.destroy();

  const secondRoot = new FakeElement("main");
  const secondJournal = createGalleyPendingIntentJournal({ storage });
  const secondTransport = createFixtureGalleyTransport();
  const second = mountGalley(secondRoot, {
    transport: secondTransport,
    dreggProvider: actorProvider(),
    pendingJournal: secondJournal,
  });
  await second.ready;
  assert.deepEqual(secondTransport.calls.map(({ method }) => method), ["openWatch", "status"]);
  assert.equal(secondJournal.list().length, 0);
  assert.match(visibleText(secondRoot), /Your signed shift/);
  assert.match(descendants(secondRoot).find((node) => node.attributes.get("role") === "status").textContent,
    /Recovered the exact pending turn/);
}));

test("signer-response loss preserves preparation digest but performs no false finality lookup", async () => withFakeDocument(async () => {
  const storage = memoryStorage();
  const firstJournal = createGalleyPendingIntentJournal({ storage });
  const first = mountGalley(new FakeElement("main"), {
    transport: createFixtureGalleyTransport({ signingResult: {
      state: "error", turnHash: null, outboxId: null, error: "signer response lost",
    } }),
    dreggProvider: actorProvider(),
    pendingJournal: firstJournal,
  });
  await first.ready;
  await first.dispatch("11".repeat(32));
  assert.equal(firstJournal.list()[0].finalTurnHash, null);
  first.destroy();

  const secondRoot = new FakeElement("main");
  const secondTransport = createFixtureGalleyTransport({ pending: true });
  const second = mountGalley(secondRoot, {
    transport: secondTransport,
    dreggProvider: actorProvider(),
    pendingJournal: createGalleyPendingIntentJournal({ storage }),
  });
  await second.ready;
  assert.deepEqual(secondTransport.calls.map(({ method }) => method), ["openWatch"],
    "a preparation digest is never queried as if it were a final turn hash");
  assert.match(visibleText(secondRoot), /signer did not return a final turn hash/i);
  assert.match(descendants(secondRoot).find((node) => node.attributes.get("role") === "status").textContent,
    /cannot be inferred/i);
}));

test("advanced unaudited replay preserves exact pending coordinate and exposes no totals or expiry", async () => withFakeDocument(async () => {
  const storage = memoryStorage();
  const journal = createGalleyPendingIntentJournal({ storage });
  const pending = journal.record(normalizeGalleyStatus(galleyStatusBefore()),
    normalizeGalleyUnsignedTurn(galleyUnsignedTurn()));
  journal.confirm(pending, "88".repeat(32));
  const storedBytes = storage.value();
  const raw = galleyStatus();
  raw.replay.audited = false;
  const refusedView = normalizeGalleyStatus(raw);
  const calls = [];
  const transport = {
    async openWatch() { calls.push("openWatch"); return refusedView; },
    async requestCommand() { throw new Error("never"); },
    async status() {
      calls.push("status");
      return { state: "replay-refused", event: null, receiptChecksumMatched: false, view: refusedView };
    },
  };
  const root = new FakeElement("main");
  const controller = mountGalley(root, { transport, dreggProvider: actorProvider(), pendingJournal: journal });
  await controller.ready;
  assert.deepEqual(calls, ["openWatch", "status"]);
  assert.equal(journal.list().length, 1);
  assert.equal(storage.value(), storedBytes);
  const live = descendants(root).find((node) => node.attributes.get("role") === "status").textContent;
  assert.match(live, /Replay audit is unavailable/);
  assert.match(live, /pending coordinate is preserved/);
  assert.doesNotMatch(live, /expired/i);
  const gauges = descendants(root).find(({ className }) => className === "galley-header__gauges");
  assert.match(visibleText(gauges), /Daily\s+UNAVAILABLE/);
  assert.match(visibleText(gauges), /Journal head\s+UNAVAILABLE/);
  assert.match(visibleText(gauges), /Public shifts\s+UNAVAILABLE/);
  assert.match(visibleText(gauges), /Local service\s+UNAVAILABLE/);
  assert.doesNotMatch(visibleText(root), /Your signed shift|A crew shift|recorded for this daily/);
}));

test("restart without identity permission preserves recovery coordinate and contacts no node route", async () => withFakeDocument(async () => {
  const storage = memoryStorage();
  const journal = createGalleyPendingIntentJournal({ storage });
  const first = mountGalley(new FakeElement("main"), {
    transport: createFixtureGalleyTransport({ pending: true }),
    dreggProvider: actorProvider(),
    pendingJournal: journal,
  });
  await first.ready;
  await first.dispatch("11".repeat(32));
  first.destroy();

  const root = new FakeElement("main");
  const transport = createFixtureGalleyTransport();
  const declined = Object.assign(new Error("declined"), { name: "DreggUserDeclined" });
  const second = mountGalley(root, {
    transport,
    dreggProvider: actorProvider({ identity: declined }),
    pendingJournal: createGalleyPendingIntentJournal({ storage }),
  });
  await second.ready;
  assert.deepEqual(transport.calls, []);
  assert.equal(journal.list().length, 1);
  assert.match(visibleText(root), /pending-intent coordinate remains local/i);
}));

test("empty, unaudited, and unavailable watches remain clear and disabled", async () => withFakeDocument(async () => {
  const emptyRaw = galleyStatusBefore();
  emptyRaw.actions = [];
  const emptyView = normalizeGalleyStatus(emptyRaw);
  const emptyRoot = new FakeElement("main");
  const empty = mountGalley(emptyRoot, {
    transport: { async openWatch() { return emptyView; }, async requestCommand() { throw new Error("never"); } },
    dreggProvider: actorProvider(),
  });
  await empty.ready;
  assert.match(visibleText(emptyRoot), /No station is offered/);
  assert.match(visibleText(emptyRoot), /No signed shift by this key/);

  const unauditedRaw = galleyStatus();
  unauditedRaw.replay.audited = false;
  const unauditedRoot = new FakeElement("main");
  const unaudited = mountGalley(unauditedRoot, {
    transport: { async openWatch() { return normalizeGalleyStatus(unauditedRaw); }, async requestCommand() { throw new Error("never"); } },
    dreggProvider: actorProvider(),
  });
  await unaudited.ready;
  assert.equal(descendants(unauditedRoot).some(({ dataset }) => dataset.galleyAction), false);
  assert.match(visibleText(unauditedRoot), /Replay\s+REFUSED/);
  assert.match(visibleText(unauditedRoot), /Returned event arrays remain inert/);
  assert.match(visibleText(unauditedRoot), /Logbook unavailable/);
  const unauditedGauges = descendants(unauditedRoot).find(({ className }) => className === "galley-header__gauges");
  assert.match(visibleText(unauditedGauges), /Public shifts\s+UNAVAILABLE/);
  assert.match(visibleText(unauditedGauges), /Local service\s+UNAVAILABLE/);
  assert.equal(descendants(unauditedRoot).filter(({ className }) => className.includes("galley-logbook__record")).length, 0);
  assert.doesNotMatch(visibleText(unauditedRoot), /Your signed shift|A crew shift|recorded for this daily/);

  const errorRoot = new FakeElement("main");
  let offline = true;
  const unavailable = mountGalley(errorRoot, {
    transport: {
      async openWatch() {
        if (offline) throw new Error("node offline");
        return normalizeGalleyStatus(galleyStatusBefore());
      },
      async requestCommand() {},
    },
    dreggProvider: actorProvider(),
  });
  await unavailable.ready;
  assert.match(descendants(errorRoot).find((node) => node.attributes.get("role") === "status").textContent,
    /GALLEY SEALED \/\/ node offline/);
  const retry = descendants(errorRoot).find(({ textContent }) => textContent === "Retry Galley watch");
  assert.ok(retry);
  assert.equal(retry.disabled, false);
  offline = false;
  await unavailable.refresh();
  assert.match(visibleText(errorRoot), /The Galley is open/);
}));

test("render uses native semantic controls and expandable evidence without HTML injection", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const controller = mountGalley(root, { transport: createFixtureGalleyTransport(), dreggProvider: actorProvider() });
  await controller.ready;
  const nodes = descendants(root);
  assert.ok(nodes.some(({ tagName }) => tagName === "BUTTON"));
  assert.ok(nodes.some(({ tagName }) => tagName === "DETAILS"));
  assert.ok(nodes.some(({ tagName }) => tagName === "SUMMARY"));
  assert.ok(nodes.some((node) => node.attributes.get("aria-label") === "Galley watch lifecycle"));
  assert.ok(nodes.some((node) => node.attributes.get("aria-label") === "Personal Galley records"));
  const status = nodes.find((node) => node.attributes.get("role") === "status");
  assert.equal(status.attributes.get("aria-live"), "polite");
  assert.equal(status.attributes.get("aria-atomic"), "true");
}));

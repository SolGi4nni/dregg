import assert from "node:assert/strict";
import { test } from "node:test";
import { mountGalley, nextGalleyChoiceIndex } from "../src/galley-controller.js";
import { createGalleyPendingIntentJournal, normalizeGalleySession } from "../src/galley-runtime.js";
import {
  GALLEY_ACTOR_PUBLIC_KEY,
  createFixtureGalleyTransport,
  galleySession,
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

test("permissioned actor can read a personalized journal without a signer or invented practice state", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const transport = createFixtureGalleyTransport();
  const controller = mountGalley(root, { transport, dreggProvider: actorProvider({ sign: false }) });
  await controller.ready;

  const nodes = descendants(root);
  const status = nodes.find((node) => node.attributes.get("role") === "status");
  const actions = nodes.filter((node) => node.dataset.galleyAction);
  assert.deepEqual(transport.calls, [{ method: "openSession", actorPublicKeyHex: GALLEY_ACTOR_PUBLIC_KEY }]);
  assert.deepEqual(actions.map(({ dataset }) => dataset.actionKind), ["perform", "visit_commons", "public_vote"]);
  assert.ok(actions.every(({ disabled }) => disabled));
  assert.match(visibleText(root), /public key personalized this read-only view/i);
  assert.match(visibleText(root), /preparation claim authorizes no mutation/i);
  assert.match(visibleText(root), /Opaque beta projection/);
  assert.equal(status.attributes.get("aria-live"), "polite");

  await controller.dispatch("perform:vat-pressure:third-watch");
  assert.equal(transport.calls.some(({ method }) => method === "requestCommand"), false);
  assert.match(status.textContent, /Dregg turn signer is unavailable/);
}));

test("missing, declined, or malformed identity keeps UI read-only before any session request", async () => withFakeDocument(async () => {
  for (const provider of [
    null,
    actorProvider({ identity: Object.assign(new Error("no"), { name: "DreggUserDeclined" }) }),
    actorProvider({ identity: { publicKeyHex: "AB".repeat(32) } }),
  ]) {
    const root = new FakeElement("main");
    const transport = createFixtureGalleyTransport();
    const controller = mountGalley(root, { transport, dreggProvider: provider });
    await controller.ready;
    assert.deepEqual(transport.calls, [], "identity resolves before the first session request");
    assert.equal(controller.getView(), null);
    assert.match(visibleText(root), /READ-ONLY/);
    assert.match(visibleText(root), /no session was requested/i);
    assert.match(visibleText(root), /exact signed turn and finalized receipt/i);
  }
}));

test("native action controls expose keyboard movement without replacing activation", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const controller = mountGalley(root, {
    transport: createFixtureGalleyTransport(),
    dreggProvider: actorProvider(),
  });
  await controller.ready;
  const actions = descendants(root).filter((node) => node.dataset.galleyAction);
  assert.deepEqual(actions.map(({ tabIndex }) => tabIndex), [0, -1, -1]);
  const event = actions[0].dispatch("keydown", { key: "ArrowRight" });
  assert.equal(event.defaultPrevented, true);
  assert.equal(actions[1].tabIndex, 0);
  assert.equal(actions[1].focused, true);
}));

test("signed action follows prepare, exact provider sign, journal status, and checksum-matched receipt postcard", async () => withFakeDocument(async () => {
  const root = new FakeElement("main");
  const transport = createFixtureGalleyTransport();
  const provider = actorProvider();
  const controller = mountGalley(root, {
    transport,
    dreggProvider: provider,
    pendingJournal: createGalleyPendingIntentJournal({ storage: memoryStorage() }),
  });
  await controller.ready;
  await controller.dispatch("perform:vat-pressure:third-watch");

  assert.deepEqual(transport.calls.map(({ method }) => method), ["openSession", "requestCommand", "sign", "status"]);
  assert.deepEqual(transport.calls.filter(({ method }) => method !== "sign").map(({ actorPublicKeyHex }) => actorPublicKeyHex),
    [GALLEY_ACTOR_PUBLIC_KEY, GALLEY_ACTOR_PUBLIC_KEY, GALLEY_ACTOR_PUBLIC_KEY]);
  assert.equal(controller.getView().sequence, 8);
  const text = visibleText(root);
  assert.match(text, /Receipt postcard checksum matched/);
  assert.match(text, /ADJACENT SHA-256 CHECKSUM MATCH/);
  assert.match(text, new RegExp("88".repeat(32)));
  assert.match(text, new RegExp("99".repeat(32)));
  assert.equal(descendants(root).filter((node) => node.className === "galley-replay__event").length, 1);
  const live = descendants(root).find((node) => node.attributes.get("role") === "status");
  assert.match(live.textContent, /canonical receipt verification is not yet installed/);
  assert.equal(live.focused, true);
}));

test("queued, refused, declined, and mismatched signing outcomes remain distinct and never auto-poll", async () => withFakeDocument(async () => {
  const turnHash = "88".repeat(32);
  const cases = [
    [{ state: "queued", turnHash, outboxId: "outbox-17", error: "Queued for retry" }, /SIGNED \/ QUEUED/],
    [{ state: "refused", turnHash: null, outboxId: null, error: "Cipherclerk is locked" }, /REFUSED \/ NOT SUBMITTED/],
    [{ state: "declined", turnHash: null, outboxId: null, error: "User declined to sign" }, /DECLINED \/ NOT SUBMITTED/],
    [{ state: "error", turnHash: null, outboxId: null, error: "galley-sign-mismatch: hostile turnId" }, /SIGNING RESULT ERROR/],
  ];
  for (const [signingResult, label] of cases) {
    const root = new FakeElement("main");
    const journal = createGalleyPendingIntentJournal({ storage: memoryStorage() });
    const transport = createFixtureGalleyTransport({ signingResult });
    const controller = mountGalley(root, {
      transport,
      dreggProvider: actorProvider(),
      pendingJournal: journal,
    });
    await controller.ready;
    const outcome = await controller.dispatch("perform:vat-pressure:third-watch");
    assert.equal(outcome.state, signingResult.state);
    assert.deepEqual(transport.calls.map(({ method }) => method), ["openSession", "requestCommand", "sign"],
      `${signingResult.state} must not start status polling`);
    assert.equal(journal.list().length, 1, "failed/queued admission cannot fabricate reconciliation");
    const text = visibleText(root);
    assert.match(text, label);
    assert.doesNotMatch(text, /Receipt postcard checksum matched/);
    assert.match(descendants(root).find((node) => node.attributes.get("role") === "status").textContent,
      /no automatic status poll was started/i);
  }
}));

test("pending intent survives controller restart and clears only on exact receipt observation", async () => withFakeDocument(async () => {
  const storage = memoryStorage();
  const provider = actorProvider();
  const firstRoot = new FakeElement("main");
  const firstJournal = createGalleyPendingIntentJournal({ storage });
  const firstTransport = createFixtureGalleyTransport({ pending: true });
  const first = mountGalley(firstRoot, {
    transport: firstTransport,
    dreggProvider: provider,
    pendingJournal: firstJournal,
  });
  await first.ready;
  await first.dispatch("perform:vat-pressure:third-watch");
  assert.equal(firstJournal.list().length, 1);
  assert.match(visibleText(firstRoot), /not yet observed in the journal/);
  first.destroy();

  const secondRoot = new FakeElement("main");
  const secondJournal = createGalleyPendingIntentJournal({ storage });
  const secondTransport = createFixtureGalleyTransport();
  const second = mountGalley(secondRoot, {
    transport: secondTransport,
    dreggProvider: provider,
    pendingJournal: secondJournal,
  });
  await second.ready;
  assert.deepEqual(secondTransport.calls.map(({ method }) => method), ["openSession", "status"]);
  assert.deepEqual(secondTransport.calls.map(({ actorPublicKeyHex }) => actorPublicKeyHex),
    [GALLEY_ACTOR_PUBLIC_KEY, GALLEY_ACTOR_PUBLIC_KEY], "restart re-resolves and reattaches the active actor");
  assert.equal(secondJournal.list().length, 0);
  assert.match(visibleText(secondRoot), /Receipt postcard checksum matched/);
  assert.match(descendants(secondRoot).find((node) => node.attributes.get("role") === "status").textContent,
    /Recovered pending turn by exact hash/);
}));

test("restart without identity permission preserves pending intent and contacts no session or status route", async () => withFakeDocument(async () => {
  const storage = memoryStorage();
  const firstJournal = createGalleyPendingIntentJournal({ storage });
  const first = mountGalley(new FakeElement("main"), {
    transport: createFixtureGalleyTransport({ pending: true }),
    dreggProvider: actorProvider(),
    pendingJournal: firstJournal,
  });
  await first.ready;
  await first.dispatch("perform:vat-pressure:third-watch");
  assert.equal(firstJournal.list().length, 1);
  first.destroy();

  const secondRoot = new FakeElement("main");
  const secondJournal = createGalleyPendingIntentJournal({ storage });
  const secondTransport = createFixtureGalleyTransport();
  const declined = Object.assign(new Error("declined"), { name: "DreggUserDeclined" });
  const second = mountGalley(secondRoot, {
    transport: secondTransport,
    dreggProvider: actorProvider({ identity: declined }),
    pendingJournal: secondJournal,
  });
  await second.ready;
  assert.deepEqual(secondTransport.calls, []);
  assert.equal(secondJournal.list().length, 1, "identity refusal cannot expire or settle a durable intent");
  assert.match(visibleText(secondRoot), /pending-intent journal is preserved locally/i);
}));

test("holder action remains unadvertised even if an authority projection sends one", async () => withFakeDocument(async () => {
  const raw = galleySession();
  raw.actions.push({ kind: "holder_sponsorship", action_token: "holder:local-only", expires_after_sequence: 7 });
  const view = normalizeGalleySession(raw);
  const calls = [];
  const transport = {
    async openSession() { calls.push("open"); return view; },
    async requestCommand() { calls.push("command"); throw new Error("must not dispatch"); },
  };
  const root = new FakeElement("main");
  const controller = mountGalley(root, {
    transport,
    dreggProvider: actorProvider(),
  });
  await controller.ready;
  assert.equal(descendants(root).some((node) => node.dataset.actionKind === "holder_sponsorship"), false);
  assert.doesNotMatch(visibleText(root), /Holder sponsorship unavailable/);
  await controller.dispatch("holder:local-only");
  assert.equal(calls.includes("command"), true, "manual API dispatch reaches transport, which remains the fail-closed authority");
}));

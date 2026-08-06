import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  GALLEY_ACTOR_REQUIRED_CODE,
  GALLEY_STATUS_ENDPOINT,
  buildGalleyStatus,
  mountGalleyStatus,
  probeGalleyStatus,
} from "../src/galley-status.js";
import { DEFAULT_GALLEY_ENDPOINTS, normalizeGalleyStatus } from "../src/galley-runtime.js";
import { galleyStatusBefore } from "./galley-fixtures.mjs";

class FakeElement {
  constructor(tagName) {
    this.tagName = tagName.toUpperCase();
    this.children = [];
    this.dataset = {};
    this.className = "";
    this.textContent = "";
  }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; }
}

function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

function answer(body, ok, status) {
  const fetchImpl = async (url, init) => {
    fetchImpl.lastInit = init;
    fetchImpl.lastUrl = String(url);
    return { ok, status, text: async () => JSON.stringify(body) };
  };
  return fetchImpl;
}

/**
 * The shapes that would mean this view had manufactured an identity.
 *
 * Deliberately NOT the header's name: the module says `X-Dregg-Actor` in its
 * docblock and in a fallback message precisely to explain that it never sends
 * one, and a guard that matched the name would be measuring prose. These are
 * the three ways a key could actually come into existence here.
 */
const MANUFACTURED_IDENTITY = /galleyActorHeaders|getRandomValues|randomUUID/;

test("the probe is keyed on the node's own refusal code, and that code is read from the node", async () => {
  // ⚠ TWO INDEPENDENT SOURCES. This client decides "the Galley is mounted and
  // wants an actor claim" from one exact string. Held against itself that is
  // decoration; held against the node's error table it is a gate, and a rename
  // there reds here instead of silently downgrading the view to "refused for a
  // reason this terminal does not know".
  const rust = await readFile(new URL("../../node/src/poa_galley_api.rs", import.meta.url), "utf8");
  assert.match(rust, new RegExp(`Self::ActorRequired => "${GALLEY_ACTOR_REQUIRED_CODE}"`));
  // …and the requirement itself is still there. If the header stops being
  // required, the anonymous probe starts succeeding and `open-without-identity`
  // is what fires — but this is the one that says so in a name.
  assert.match(rust, /ActorRequired => StatusCode::UNAUTHORIZED/);
  assert.match(rust, /let value = values\.next\(\)\.ok_or\(GalleyApiError::ActorRequired\)\?;/);

  // The endpoint is the transport's own constant, so one rename cannot leave
  // this view probing a route the terminal below no longer uses.
  assert.equal(GALLEY_STATUS_ENDPOINT, DEFAULT_GALLEY_ENDPOINTS.status);
  assert.match(GALLEY_STATUS_ENDPOINT, /\/api\/poa\/galley\/v1\/status$/);
});

test("the probe sends no actor header at all — the absence IS the experiment", async () => {
  const fetchImpl = answer({ code: GALLEY_ACTOR_REQUIRED_CODE, message: "X-Dregg-Actor is required" }, false, 401);
  const probe = await probeGalleyStatus({ baseUrl: "https://poa.invalid/", fetchImpl });
  assert.equal(probe.state, "identity-required");
  assert.equal(probe.code, GALLEY_ACTOR_REQUIRED_CODE);

  // ⚠ A random 32-byte key would make the node answer, and this page would then
  // be rendering a reading of an identity it invented. Behavioural first: the
  // request carries no header block at all, so there is nowhere for a claim to
  // hide — not a missing `x-dregg-actor` among others, no headers whatsoever.
  assert.ok(!("headers" in (fetchImpl.lastInit ?? {})), "the anonymous probe sent a header block");
  assert.deepEqual(Object.keys(fetchImpl.lastInit ?? {}).sort(), ["cache", "credentials"]);

  // …and structurally: nothing in the module can bring a key into existence.
  const source = await readFile(new URL("../src/galley-status.js", import.meta.url), "utf8");
  // Self-check: the pattern must still match a specimen of the thing it forbids.
  assert.match("const actor = crypto.getRandomValues(new Uint8Array(32));", MANUFACTURED_IDENTITY,
    "the guard's own pattern no longer matches a manufactured identity — it has stopped falsifying");
  assert.doesNotMatch(source, MANUFACTURED_IDENTITY,
    "the standing view has acquired a way to manufacture an actor identity");
});

test("every other answer is a distinct state, and none of them throws", async () => {
  const cases = [
    ["network", await probeGalleyStatus({ baseUrl: "https://poa.invalid/", fetchImpl: async () => { throw new Error("no route"); } })],
    ["no fetch", await probeGalleyStatus({ baseUrl: "https://poa.invalid/", fetchImpl: null })],
    ["unknown refusal", await probeGalleyStatus({ baseUrl: "https://poa.invalid/", fetchImpl: answer({ code: "poa-galley-observation-unavailable", message: "backend down" }, false, 503) })],
    ["bodiless 404", await probeGalleyStatus({ baseUrl: "https://poa.invalid/", fetchImpl: answer(null, false, 404) })],
    ["answered anonymously", await probeGalleyStatus({ baseUrl: "https://poa.invalid/", fetchImpl: answer(galleyStatusBefore(), true, 200) })],
  ];
  assert.deepEqual(cases.map(([, probe]) => probe.state),
    ["unreachable", "unreachable", "refused", "unreachable", "open-without-identity"]);
  // An unfamiliar refusal keeps the node's OWN word rather than being folded
  // into the nearest state this client happens to know…
  assert.equal(cases[2][1].code, "poa-galley-observation-unavailable");
  // …but a bare HTTP error with no Galley error body is not the Galley refusing
  // at all: it is a static host or a proxy answering, and crediting it to the
  // organ would be reading an answer from something that never spoke. Measured
  // against `npm run serve`, where a plain file-server 404 rendered as "the
  // Galley refused for a reason this terminal does not know".
  assert.equal(cases[3][1].code, "http-404");
  assert.match(cases[3][1].detail, /Nothing identifying itself as the Galley/);
});

test("with no identity the view says the organ is open, and says what it will not do to read it", () => {
  const model = buildGalleyStatus({
    probe: { state: "identity-required", code: GALLEY_ACTOR_REQUIRED_CODE, detail: "X-Dregg-Actor is required" },
  });
  assert.equal(model.state, "identity-required");
  assert.equal(model.headline, "The Galley is mounted and answering");
  assert.match(model.standing, /will not invent one/);
  const rows = Object.fromEntries(model.rows);
  assert.equal(rows.Route, GALLEY_STATUS_ENDPOINT);
  assert.match(rows.Answered, new RegExp(GALLEY_ACTOR_REQUIRED_CODE));
  assert.match(rows["What that grants"], /nothing/);

  // ⚠ No figure is invented for a document that was never read: the identity
  // state publishes route facts only, never a journal head or a shift count.
  for (const [term] of model.rows) {
    assert.ok(!/head|sequence|shift|daily/i.test(term), `the identity-less view claimed a journal figure: ${term}`);
  }
});

test("a checked status document supersedes the probe and every figure comes off it", () => {
  const view = normalizeGalleyStatus(galleyStatusBefore());
  const model = buildGalleyStatus({
    probe: { state: "identity-required", code: GALLEY_ACTOR_REQUIRED_CODE, detail: "x" },
    view,
  });
  assert.equal(model.state, "open");
  const rows = Object.fromEntries(model.rows);
  assert.equal(rows["Journal head"], String(view.sequence));
  assert.equal(rows.Daily, view.dailyId);
  assert.equal(rows["Schema version"], String(view.schemaVersion));
  assert.equal(rows["Actions offered"], String(view.actions.length));
  assert.equal(rows["Public shifts"], String(view.projection.publicPlayCount));
  assert.match(model.source, /personalized status document/);

  // A quiet journal is a Galley nobody has worked in, not a page that failed.
  if (view.sequence === 0) assert.match(model.standing, /nobody has worked a shift in/);
});

test("a journal the node did not audit renders no shift and offers no action", () => {
  const view = normalizeGalleyStatus(galleyStatusBefore());
  const unaudited = { ...view, replay: { ...view.replay, audited: false } };
  const model = buildGalleyStatus({ view: unaudited });
  assert.equal(model.state, "refused");
  assert.match(model.headline, /failed its replay audit/);
  assert.match(Object.fromEntries(model.rows).Replay, /REFUSED/);
});

test("an unreachable Galley claims nothing about the day", () => {
  const model = buildGalleyStatus({ probe: { state: "unreachable", code: "galley-fetch", detail: "No Galley answered on this origin" } });
  assert.equal(model.state, "sealed");
  assert.match(model.standing, /Nothing about the journal, the shifts, or the day is claimed here/);
  assert.equal(model.source, null);
  assert.equal(buildGalleyStatus({}).state, "pending");
});

test("the standing view renders text nodes and marks its own state", () => withFakeDocument(() => {
  const root = new FakeElement("section");
  mountGalleyStatus(root, buildGalleyStatus({ view: normalizeGalleyStatus(galleyStatusBefore()) }));
  assert.equal(root.dataset.state, "open");
  assert.ok(root.children.some((node) => node.className === "galley-standing__rows"));
  for (const node of root.children) assert.equal(typeof node.textContent, "string");

  const sealed = new FakeElement("section");
  mountGalleyStatus(sealed, buildGalleyStatus({ probe: { state: "unreachable", code: "galley-fetch", detail: "nothing answered" } }));
  assert.equal(sealed.dataset.state, "sealed");
}));

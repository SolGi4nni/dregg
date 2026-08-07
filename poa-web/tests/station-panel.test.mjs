import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { test } from "node:test";
import {
  STATION_CREW_ROUTE,
  STATION_KEY_SETS,
  STATION_PANEL_ROUTE,
  buildStationPanel,
  loadStationState,
  mountStationPanel,
  parseStationDocument,
  parseStationView,
} from "../src/station-panel.js";
import {
  INSTALLED_STATION_DOCUMENT,
  STATION_AUTHORITY,
  readyStation,
  stationEnvelope,
} from "./station-fixtures.mjs";
import { assertEncoderReaderWorks, emittedKeys } from "./lean-wire.mjs";

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

const jsonFetch = (body, ok = true, status = 200) => async () => ({
  ok, status, text: async () => JSON.stringify(body),
});

const LEAN = new URL("../../metatheory/Dregg2/Games/PathOfAngels/", import.meta.url);

/**
 * Strip Lean comments so a guard can tell a MENTION from a DEFINITION.
 *
 * Block comments nest in Lean and `/--` docstrings open one too, so this tracks
 * depth rather than matching a pair. Without it, every guard below would be
 * satisfied by prose: the tree is full of docblocks that name the very symbols
 * these tests are about.
 */
function stripLeanComments(source) {
  let depth = 0;
  let output = "";
  for (let index = 0; index < source.length; index += 1) {
    if (source.startsWith("/-", index)) { depth += 1; index += 1; continue; }
    if (depth > 0 && source.startsWith("-/", index)) { depth -= 1; index += 1; continue; }
    if (depth > 0) { if (source[index] === "\n") output += "\n"; continue; }
    if (source.startsWith("--", index)) {
      const end = source.indexOf("\n", index);
      index = end === -1 ? source.length : end - 1;
      continue;
    }
    output += source[index];
  }
  return output;
}

test("the fixture is a specimen of the DEPLOYED station, pinned against Lean and not against itself", async () => {
  // ⚠ The copy this page renders quotes these figures — "periods 31 through 35",
  // "4 loot rows". If the curator re-authors the crate they change, and this
  // reds so the fixture and the copy get RE-DERIVED. Do not delete it; a fixture
  // that stopped resembling the deployment is how a test quietly stops being
  // about anything.
  const examples = stripLeanComments(await readFile(new URL("SalvageCrateExamples.lean", LEAN), "utf8"));
  const runtime = stripLeanComments(await readFile(new URL("StationDailyRuntime.lean", LEAN), "utf8"));

  const opens = /opensAt\s*:=\s*⟨(\d+)⟩/.exec(examples);
  const closes = /closesAt\s*:=\s*⟨(\d+)⟩/.exec(examples);
  assert.ok(opens && closes, "the authored crate window moved; re-derive the fixture from SalvageCrateExamples.lean");
  assert.equal(Number(opens[1]), INSTALLED_STATION_DOCUMENT.opens_at);
  assert.equal(Number(closes[1]), INSTALLED_STATION_DOCUMENT.closes_at);

  // Four loot rows, whose weights are the ticket entries (`ticketEntries`
  // replicates each row by its weight).
  const weights = [...examples.matchAll(/weight\s*:=\s*(\d+)/g)].map((match) => Number(match[1]));
  assert.equal(weights.length, INSTALLED_STATION_DOCUMENT.table_rows);
  assert.equal(weights.reduce((sum, weight) => sum + weight, 0), INSTALLED_STATION_DOCUMENT.ticket_count);

  // One dial, and the display scale it is authored with.
  const gauges = /gauges\s*:=\s*\[\{\s*id\s*:=\s*⟨(\d+)⟩,\s*meter\s*:=\s*\.(\w+),\s*fullAt\s*:=\s*(\d+)\s*\}\]/.exec(runtime);
  assert.ok(gauges, "the authored panel gauges moved; re-derive the fixture from StationDailyRuntime.lean");
  const [dial] = INSTALLED_STATION_DOCUMENT.gauges;
  assert.deepEqual([Number(gauges[1]), gauges[2], Number(gauges[3])], [dial.gauge, dial.meter, dial.full_at]);
});

test("the exact key sets are read off the Lean encoders that emit them", async () => {
  const source = await readFile(new URL("StationDailyRuntime.lean", LEAN), "utf8");
  assertEncoderReaderWorks(source, "Reply.toJson", "gauges");

  // ⚠ TWO SOURCES, NOT THREE. The right side is the client's OWN exact set
  // rather than a copy written here, so this cannot pass while the client and
  // the encoder disagree. A Lean-side field lands as a named red instead of in a
  // browser as a total refusal.
  for (const [encoder, set] of [
    ["Reply.toJson", "document"],
    ["GaugeWire.toJson", "gauge"],
    ["CrewWire.toJson", "crew"],
    ["PeriodWire.toJson", "period"],
    ["EntryWire.toJson", "entry"],
  ]) {
    assert.deepEqual(emittedKeys(source, encoder).sort(), [...STATION_KEY_SETS[set]].sort(),
      `${encoder} and the client's exact ${set} key set have drifted apart`);
  }

  // ⚠ THE FIELD WHOSE ABSENCE THE TILE'S COPY RESTS ON. There is no
  // current-period pointer on this wire, and "which period is live is not a
  // question this route answers" is only honest while that stays true. The day
  // Lean emits one, this reds and the copy gets rewritten — rather than the page
  // going on saying the organ cannot answer something it now answers.
  for (const key of emittedKeys(source, "Reply.toJson")) {
    assert.ok(!/current|today|now/.test(key), `the station now emits ${key}; the crate copy claims it has no current-period pointer`);
  }

  // And the envelope, which is Rust: serde emits declaration order.
  const rust = await readFile(new URL("../../node/src/poa_station_api.rs", import.meta.url), "utf8");
  const struct = rust.slice(rust.indexOf("pub struct PoaStationResponseV1"));
  const fields = [...struct.slice(0, struct.indexOf("\n}")).matchAll(/pub (\w+):/g)].map((match) => match[1]);
  assert.deepEqual(fields, [...STATION_KEY_SETS.envelope]);
});

test("the served document parses field by field and cannot carry an unknown one", () => {
  const view = parseStationView(stationEnvelope(), STATION_AUTHORITY);
  assert.equal(view.station.opensAt, 31);
  assert.equal(view.station.ticketCount, 14);
  assert.equal(view.station.crew, null);
  assert.equal(view.authoredHere, true);

  assert.throws(() => parseStationView({ ...stationEnvelope(), extra: 1 }, STATION_AUTHORITY), { code: "station-field" });
  assert.throws(() => parseStationView(stationEnvelope({ format: "POA-STATION-VIEW-2" }), STATION_AUTHORITY), { code: "station-format" });
  assert.throws(() => parseStationView(stationEnvelope(), "a".repeat(64)), { code: "station-authority" });

  const inner = (overrides) => parseStationDocument({ ...structuredClone(INSTALLED_STATION_DOCUMENT), ...overrides });
  assert.throws(() => inner({ format: "POA-STATION-DAILY-OUT-2" }), { code: "station-format" });
  assert.throws(() => inner({ closes_at: 30 }), { code: "station-schedule" });
  assert.throws(() => inner({ ticket_count: -1 }), { code: "station-count" });
  assert.throws(() => parseStationDocument({ ...structuredClone(INSTALLED_STATION_DOCUMENT), rotation: [] }), { code: "station-field" });

  // ⚠ An `exactKeys` refusal is the CORRECT behaviour when a route grows a
  // field, and the fix is to teach this client the new exact set against the
  // bytes that shipped — never to widen it to anything-goes. This asserts the
  // refusal exists so nobody "fixes" it by deleting the check.
  assert.throws(() => inner({ current_period: 33 }), { code: "station-field" });
});

test("a gauge's own arithmetic is re-derived, so a lying needle is refused rather than drawn", () => {
  const gauge = (overrides) => parseStationDocument({
    ...structuredClone(INSTALLED_STATION_DOCUMENT),
    gauges: [{ gauge: 1, meter: "supplies", exact_total: 10, full_at: 64, shown: 10, at_full: false, ...overrides }],
  });
  assert.equal(gauge({}).gauges[0].shown, 10);

  // The needle must be the clipped total: a node that parks it somewhere else is
  // a node whose display scale has become the bound.
  assert.throws(() => gauge({ shown: 64 }), { code: "station-gauge" });
  assert.throws(() => gauge({ shown: 0 }), { code: "station-gauge" });
  // …and the at-full flag must agree with the total it claims to summarize.
  assert.throws(() => gauge({ at_full: true }), { code: "station-gauge" });
  // A total genuinely past the mark clips, and says so.
  const full = gauge({ exact_total: 100, shown: 64, at_full: true }).gauges[0];
  assert.deepEqual([full.shown, full.exactTotal, full.atFull], [64, 100, true]);
});

test("every way of not reading the station lands as a state, and none of them throws", async () => {
  const cases = [
    ["no authority", await loadStationState({ authorityId: null, baseUrl: "https://poa.invalid/" })],
    ["no fetch", await loadStationState({ authorityId: STATION_AUTHORITY, baseUrl: "https://poa.invalid/", fetchImpl: null })],
    ["network", await loadStationState({ authorityId: STATION_AUTHORITY, baseUrl: "https://poa.invalid/", fetchImpl: async () => { throw new Error("no route"); } })],
    ["node refusal", await loadStationState({ authorityId: STATION_AUTHORITY, baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch({ refused: "foreign-authority", detail: "x" }, false, 400) })],
    ["garbage", await loadStationState({ authorityId: STATION_AUTHORITY, baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch({ format: "SOMETHING" }) })],
  ];
  for (const [label, result] of cases) {
    assert.notEqual(result.state, "ready", `${label} produced a readable station`);
    assert.ok(result.code && result.reason, `${label} produced a state with no reason`);
  }
  // The node's own refusal word survives, so "rate-limited" and "wrong
  // federation" do not both read as a bare HTTP number.
  assert.equal(cases[3][1].code, "foreign-authority");
  assert.equal(cases[4][1].state, "refused");

  const ready = await loadStationState({ authorityId: STATION_AUTHORITY, baseUrl: "https://poa.invalid/", fetchImpl: jsonFetch(stationEnvelope()) });
  assert.equal(ready.state, "ready");
  assert.equal(ready.view.station.tableRows, 4);
});

test("the panel says the ship has not moved, and never that a period is live", () => {
  const panel = buildStationPanel(readyStation());
  assert.equal(panel.state, "ready");
  assert.equal(panel.headline, "Nothing has moved the ship");
  assert.match(panel.standing, /exactly as installed, not a station whose figures have not arrived/);
  assert.deepEqual(panel.gauges.map((gauge) => [gauge.label, gauge.reading]), [["SUPPLIES", "0 of 64"]]);
  assert.deepEqual(panel.counts.map(([term, value]) => `${term}=${value}`),
    ["Salvage kinds recovered=0", "Openings observed=0", "Openings admitted=0"]);

  const crate = Object.fromEntries(panel.crate);
  assert.equal(crate["Authored schedule"], "periods 31 through 35");
  assert.equal(crate["Loot table"], "4 rows");
  assert.match(crate["Which period is live"], /no current-period pointer/);
  assert.match(crate["Your rotation"], /not requested/);

  // ⚠ The copy law: nothing in the rendered panel may claim a day turned over.
  const rendered = [panel.headline, panel.standing, ...panel.crate.flat(), ...panel.counts.flat()].join(" ");
  assert.doesNotMatch(rendered, /\btoday\b|\byesterday\b|\bdrawn today\b/i);

  const moved = buildStationPanel(readyStation({ observed: 4, admitted: 1 }));
  assert.equal(moved.headline, "The ship has moved");

  for (const [state, expected] of [["refused", "refused"], ["unreachable", "sealed"]]) {
    const sealed = buildStationPanel({ state, code: "station-fetch", reason: "No station answered on this origin" });
    assert.equal(sealed.state, expected);
    assert.equal(sealed.gauges.length, 0, "a station that was not read must publish no gauge");
  }
  assert.equal(buildStationPanel(null).state, "pending");
});

test("the panel renders text nodes and marks its own state", () => withFakeDocument(() => {
  const root = new FakeElement("section");
  mountStationPanel(root, buildStationPanel(readyStation()));
  assert.equal(root.dataset.state, "ready");
  const classes = root.children.map((node) => node.className);
  assert.ok(classes.includes("station-panel__gauges"));
  assert.ok(classes.includes("station-panel__crate"));
  const dials = root.children.find((node) => node.className === "station-panel__gauges");
  assert.equal(dials.children[0].dataset.atFull, "false");

  const sealed = new FakeElement("section");
  mountStationPanel(sealed, buildStationPanel({ state: "unreachable", code: "station-fetch", reason: "nothing answered" }));
  assert.equal(sealed.dataset.state, "sealed");
  assert.ok(sealed.children.every((node) => node.className !== "station-panel__gauges"));
}));

test("the crate cannot be opened, and this reds the day anything can mint the capability", async () => {
  // ⚠ THE SEALED-STATE FALSIFIER. "No draw is possible" is a claim about the
  // Lean tree, not about the wire: `SalvageCrate.openCrate` demands a
  // `CurrentStateCapability` that is `opaque` with NO PRODUCER ANYWHERE, so no
  // `@[export]` can hand one to a host. The day a producer lands — an `axiom`, a
  // `def`, an instance — the tile's copy becomes a lie, and this is what notices.
  //
  // Keyed on the ORGAN (the capability itself), and keyed on CODE rather than on
  // prose: the tree is full of docblocks that name this symbol, and a guard that
  // counted those would be measuring the documentation.
  const root = new URL("../../metatheory/Dregg2/", import.meta.url);
  const files = [];
  const walk = async (dir) => {
    for (const entry of await readdir(dir, { withFileTypes: true })) {
      if (entry.name === ".lake") continue;
      const next = new URL(`${entry.name}${entry.isDirectory() ? "/" : ""}`, dir);
      if (entry.isDirectory()) await walk(next);
      else if (entry.name.endsWith(".lean")) files.push(next);
    }
  };
  await walk(root);
  assert.ok(files.length > 100, "the Lean source tree should not be empty");

  const occurrences = (await Promise.all(files.map(async (file) => {
    const code = stripLeanComments(await readFile(file, "utf8"));
    return code.split("\n")
      .filter((line) => line.includes("CurrentStateCapability"))
      .map((line) => line.trim());
  }))).flat().sort();

  // Self-check: the stripper must see a producer written in CODE and must not
  // see one written in a COMMENT. A guard that reads prose is measuring prose.
  const specimen = stripLeanComments([
    "/-- a docblock that says axiom mintCurrentStateCapability exists -/",
    "-- and a line comment saying def mintCurrentStateCapability",
    "axiom mintCurrentStateCapability {c : Config} (s : State c) : CurrentStateCapability s",
  ].join("\n"));
  assert.equal(specimen.split("\n").filter((line) => line.includes("CurrentStateCapability")).length, 1,
    "the comment stripper no longer distinguishes code from prose — this guard has stopped falsifying");

  assert.deepEqual(occurrences, [
    "(_current : CurrentStateCapability state) (envelope : OpenEnvelope) :",
    "opaque CurrentStateCapability {config : Config} (state : State config) : Type",
  ], "something now mentions CurrentStateCapability in CODE besides its opaque declaration and openCrate's binder — if it PRODUCES one, the crate is openable and the tile's copy is a lie");
});

test("the two station routes this client knows are the two it uses", () => {
  assert.equal(STATION_PANEL_ROUTE, "/api/poa/station/{authority}/panel");
  assert.equal(STATION_CREW_ROUTE, "/api/poa/station/{authority}/crew/{crew}");
  // The crew route takes a 64-hex crew key and this terminal binds none, so it
  // is recorded and never called. Nothing here may invent one to fill it.
  const source = new URL("../src/station-panel.js", import.meta.url);
  return readFile(source, "utf8").then((text) => {
    assert.doesNotMatch(text, /STATION_CREW_ROUTE\.replace/, "the crew route is being called with a key this terminal does not have");
  });
});

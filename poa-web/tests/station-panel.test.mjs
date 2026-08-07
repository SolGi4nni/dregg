import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { test } from "node:test";
import {
  CRATE_OPEN_DOCUMENT_FORMAT,
  CRATE_OPEN_KEY_SETS,
  CRATE_OPEN_ROUTE,
  CRATE_REFUSALS,
  STATION_CREW_ROUTE,
  STATION_KEY_SETS,
  STATION_PANEL_ROUTE,
  buildCrateOpenAction,
  buildStationPanel,
  loadStationState,
  mountCrateOpenAction,
  mountStationPanel,
  openSalvageCrate,
  parseCrateOpenDocument,
  parseCrateOpenView,
  parseStationDocument,
  parseStationView,
} from "../src/station-panel.js";
import {
  ACCEPTED_OPEN_DOCUMENT,
  CRATE_FINALITY_GAP,
  INSTALLED_STATION_DOCUMENT,
  MOVED_STATION_DOCUMENT,
  OPENER_KEY,
  REFUSED_OPEN_DOCUMENT,
  STATION_AUTHORITY,
  STOWAWAY_KEY,
  crateOpenEnvelope,
  declinedOpenEnvelope,
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
  // ⚠ The panel moved. `StationDailyRuntime.stationPanelRaw` is now an ABBREV of
  // `StationCrateOpen.panelRaw` — there is ONE panel deployment and the write
  // path folds receipts into the same object this read serves — so the authored
  // dial is read where it is authored. Pinning it at the abbreviation would be
  // pinning a name rather than the content.
  const runtime = stripLeanComments(await readFile(new URL("StationCrateOpen.lean", LEAN), "utf8"));

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
  assert.ok(gauges, "the authored panel gauges moved; re-derive the fixture from StationCrateOpen.lean");
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
  // ⚠ THE CORRECTED COPY. This used to assert the page said "No crate opening
  // has ever been accepted here — the opening demands a capability no Lean term
  // in the tree builds", which became false when the write path landed. The
  // honest reading of zeros is an EMPTY LOG, and the page must say that instead
  // of saying opening is impossible.
  assert.match(panel.standing, /the log is empty/);
  assert.match(panel.standing, /not because opening is impossible/);
  assert.doesNotMatch(panel.standing, /no Lean term|opaque|never been accepted|no crate opening has ever/i);
  assert.deepEqual(panel.gauges.map((gauge) => [gauge.label, gauge.reading]), [["SUPPLIES", "0 of 64"]]);
  assert.deepEqual(panel.counts.map(([term, value]) => `${term}=${value}`),
    ["Salvage kinds recovered=0", "Openings observed=0", "Openings admitted=0"]);

  const crate = Object.fromEntries(panel.crate);
  assert.equal(crate["Authored schedule"], "periods 31 through 35");
  assert.equal(crate["Loot table"], "4 rows");
  assert.match(crate["Which period is live"], /no current-period pointer/);
  assert.match(crate["Your rotation"], /not requested/);
  assert.equal(crate["Openings folded"], "0 rows of this node's durable open log");

  // ⚠ The copy law: nothing in the rendered panel may claim a day turned over.
  const rendered = [panel.headline, panel.standing, ...panel.crate.flat(), ...panel.counts.flat()].join(" ");
  assert.doesNotMatch(rendered, /\btoday\b|\byesterday\b|\bdrawn today\b/i);

  // ⭐ THE MOVED SHIP, on the reading the node actually served after one open.
  const afterOne = buildStationPanel(readyStation(MOVED_STATION_DOCUMENT));
  assert.equal(afterOne.headline, "The ship has moved");
  assert.deepEqual(afterOne.gauges.map((gauge) => [gauge.label, gauge.reading, gauge.exactTotal]),
    [["SUPPLIES", "1 of 64", 1]]);
  assert.match(afterOne.standing, /fold of 1 opening recorded in this node's durable log/);
  assert.equal(Object.fromEntries(afterOne.crate)["Openings folded"], "1 row of this node's durable open log");
  assert.doesNotMatch([afterOne.headline, afterOne.standing].join(" "), /\btoday\b|\byesterday\b/i);

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

test("the capability is SEALED, not absent — and this reds the day anything outside SalvageCrate mints one", async () => {
  // ⚠ THIS GUARD'S PREMISE DIED, AND THE GUARD IS REPLACED RATHER THAN DELETED.
  //
  // Its previous form asserted `CurrentStateCapability` appeared in CODE on
  // exactly two lines — its `opaque` declaration and `openCrate`'s binder — and
  // concluded "no draw is possible". That was a real falsifier and it DID fire:
  // the write path landed, the capability became a sealed structure with a
  // private constructor rooted in `genesis`, and this went red. It was red at
  // HEAD, correctly, until now.
  //
  // What is still worth guarding is the property that survived, and it is the
  // one the whole ritual's authority rests on: `CurrentStateCapability.mk` is
  // PRIVATE, so a capability can only be obtained from `genesis` or handed back
  // by an accepted transition. The day a module OUTSIDE `SalvageCrate.lean`
  // constructs one, any caller can move the communal gauges without the crate
  // ever having accepted anything — and the page's "every figure came off an
  // accepted opening" becomes a lie.
  //
  // Keyed on CODE rather than prose: the tree is full of docblocks naming this
  // symbol, and a guard that counted those would be measuring documentation.
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

  // Self-check: the stripper must see a producer written in CODE and must not
  // see one written in a COMMENT. A guard that reads prose is measuring prose.
  const specimen = stripLeanComments([
    "/-- a docblock that says axiom mintCurrentStateCapability exists -/",
    "-- and a line comment saying def mintCurrentStateCapability",
    "axiom mintCurrentStateCapability {c : Config} (s : State c) : CurrentStateCapability s",
  ].join("\n"));
  assert.equal(specimen.split("\n").filter((line) => line.includes("CurrentStateCapability")).length, 1,
    "the comment stripper no longer distinguishes code from prose — this guard has stopped falsifying");

  // Every CODE line naming the CONSTRUCTOR, anywhere in the tree, tagged with
  // the file it lives in. Naming `CurrentStateCapability.mk` is the only way to
  // build one; a mention in a type or a binder is not one, and neither is a
  // docblock — the stripper above removes those, and its self-check proves it
  // still can.
  //
  // ⚠ The list is EXACT rather than a file-level set, because one of these hits
  // is a `fail_if_success` — the NEGATIVE assertion that the constructor is
  // unreachable from outside — and a guard that only counted files would have
  // read that seal as a breach of itself. It nearly did.
  const naming = (await Promise.all(files.map(async (file) => {
    const code = stripLeanComments(await readFile(file, "utf8"));
    const where = file.pathname.slice(file.pathname.lastIndexOf("/PathOfAngels/") + 1);
    return code.split("\n")
      .filter((line) => line.includes("CurrentStateCapability.mk"))
      .map((line) => `${where} :: ${line.trim()}`);
  }))).flat().sort();

  assert.deepEqual(naming, [
    // The seal, asserted as a theorem: the constructor cannot be reached from
    // outside the crate. Making it public turns THIS red first.
    "PathOfAngels/SalvageCrateExamples.lean :: fail_if_success (have _constructor := @CurrentStateCapability.mk)",
    // `genesisCapability` — the one-time install.
    "PathOfAngels/SalvageCrate.lean :: CurrentStateCapability.mk",
    // The successor an accepted `openCrate` hands back.
    "PathOfAngels/SalvageCrate.lean :: CurrentStateCapability.mk",
    // The successor an accepted period advance hands back.
    "PathOfAngels/SalvageCrate.lean :: { next := next, capability := CurrentStateCapability.mk }",
  ].sort(), "something outside SalvageCrate.lean now names the capability CONSTRUCTOR in code — the constructor is private for exactly this reason, and a mint outside the crate means the communal gauges can move without the crate ever having accepted an opening");

  // The seal's own shape, so this cannot pass because the structure was deleted.
  const salvage = stripLeanComments(await readFile(new URL("SalvageCrate.lean", LEAN), "utf8"));
  assert.match(salvage, /structure CurrentStateCapability .*where/,
    "CurrentStateCapability is no longer the sealed structure this guard is about");
});

test("the crate-open key sets are read off the Lean encoders that emit them", async () => {
  const source = await readFile(new URL("StationCrateOpenRuntime.lean", LEAN), "utf8");
  assertEncoderReaderWorks(source, "Reply.toJson", "opened");

  // ⚠ TWO SOURCES, NOT THREE — the same discipline the station read gets. The
  // right side is the client's OWN exact set, so this cannot pass while the
  // client and the encoder disagree.
  for (const [encoder, set] of [
    ["Reply.toJson", "document"],
    ["PanelWire.toJson", "panel"],
  ]) {
    assert.deepEqual(emittedKeys(source, encoder).sort(), [...CRATE_OPEN_KEY_SETS[set]].sort(),
      `${encoder} and the client's exact ${set} key set have drifted apart`);
  }

  // ⚑ ONE SPELLING FOR THE GAUGE AND THE ENTRY, ON BOTH WIRES. The write path
  // does NOT author its own gauge/entry encoders — it calls
  // `StationDailyRuntime.GaugeWire.toJson` / `EntryWire.toJson` — so the client
  // must not carry a second copy of those key sets either. This asserts the
  // write module defines neither, which is what makes the shared sets correct.
  for (const forbidden of ["GaugeWire.toJson", "EntryWire.toJson"]) {
    assert.doesNotMatch(stripLeanComments(source), new RegExp(`def ${forbidden.replace(".", "\\.")}`),
      `${forbidden} is authored a second time in the write path; the read and the write must spell a gauge once`);
  }
  // …and they are the sets the client already holds for the station read.
  assert.deepEqual([...STATION_KEY_SETS.gauge].sort(), ["at_full", "exact_total", "full_at", "gauge", "meter", "shown"]);

  // ⚠ THE FIELD WHOSE ABSENCE THE ACTION'S COPY RESTS ON. There is no streak,
  // attendance or countdown on this wire, and the page must not simulate one.
  // The day Lean emits any of them, this reds and the copy gets rewritten.
  for (const key of emittedKeys(source, "Reply.toJson")) {
    assert.ok(!/streak|attendance|countdown|next_|last_seen/.test(key),
      `the crate open now emits ${key}; the action's copy claims no such state exists`);
  }

  // And the envelope, which is Rust: serde emits declaration order.
  const rust = await readFile(new URL("../../node/src/poa_crate_api.rs", import.meta.url), "utf8");
  const struct = rust.slice(rust.indexOf("pub struct PoaCrateOpenResponseV1"));
  const fields = [...struct.slice(0, struct.indexOf("\n}")).matchAll(/pub (\w+):/g)].map((match) => match[1]);
  assert.deepEqual(fields, [...CRATE_OPEN_KEY_SETS.envelope]);
});

test("the refusal tags this page knows are exactly the ones Lean can emit", async () => {
  // ⚠ Keyed on `Refusal.label`, the function that turns a constructor into the
  // string on the wire. A tag the page has never been taught is REFUSED rather
  // than echoed, so a new Lean constructor must land as a named red here — not
  // as invented copy in a browser for a state nobody has written words for.
  const source = stripLeanComments(await readFile(new URL("StationCrateOpenRuntime.lean", LEAN), "utf8"));
  const body = source.slice(source.indexOf("def Refusal.label"));
  const tags = [...body.slice(0, body.search(/\n(?:private\s+)?(?:def|theorem|structure|inductive|abbrev|@\[)/))
    .matchAll(/=>\s*"([a-z-]+)"/g)].map((match) => match[1]);

  assert.ok(tags.length > 0, "the refusal-tag reader found no tags — it has stopped reading Lean");
  assert.deepEqual(tags.sort(), Object.keys(CRATE_REFUSALS).sort(),
    "Lean's refusal tags and the ones this page has words for have drifted apart");
});

test("an accepted opening shows the prize and the communal ship; a refusal draws no needle at all", () => {
  const opened = buildCrateOpenAction({
    crew: { key: OPENER_KEY, eligible: true },
    open: { state: "opened", view: parseCrateOpenView(crateOpenEnvelope(), STATION_AUTHORITY) },
  });
  assert.equal(opened.state, "opened");
  assert.equal(opened.headline, "You drew communal-salvage:55");
  assert.deepEqual(opened.prize, { id: 13, prize: "communal-salvage:55", supplies: 1 });
  // ⚠ BOTH FIGURES. The needle and the unclipped total are published, so the
  // display scale can never quietly become the bound.
  assert.deepEqual(opened.gauges.map((g) => [g.label, g.reading, g.exactTotal, g.shown]),
    [["SUPPLIES", "1 of 64", 1, 1]]);
  assert.deepEqual(opened.counts.map(([term, value]) => `${term}=${value}`),
    ["Salvage kinds recovered=1", "Openings observed=1", "Openings admitted=1"]);
  // The action is not offered again: one crew key opens the crate once.
  assert.equal(opened.enabled, false);
  // ⚠ VERBATIM, not paraphrased.
  assert.equal(opened.finalityGap, CRATE_FINALITY_GAP);

  // ── A REFUSAL IS NOT A ZERO-MOVE ────────────────────────────────────────────
  const declined = buildCrateOpenAction({
    crew: { key: OPENER_KEY, eligible: true },
    open: { state: "declined", view: parseCrateOpenView(declinedOpenEnvelope(), STATION_AUTHORITY) },
  });
  assert.equal(declined.state, "declined");
  assert.equal(declined.refusal, "already-opened-this-period");
  assert.equal(declined.gauges.length, 0, "a refused opening drew a needle");
  assert.equal(declined.prize, null, "a refused opening showed a prize");
  assert.equal(declined.counts, undefined, "a refused opening published counts");
  assert.match(declined.standing, /already opened the crate at this period/);
  assert.match(declined.standing, /the communal ship is unchanged/);
  assert.equal(declined.finalityGap, CRATE_FINALITY_GAP);

  // ⚠ NO SIMULATED STATE. Nothing rendered may imply a streak, a countdown, an
  // attendance record or a next crate — none of those exist on any wire.
  for (const action of [opened, declined]) {
    const rendered = [action.headline, action.standing, ...(action.counts ?? []).flat()].join(" ");
    assert.doesNotMatch(rendered, /\bstreak\b|\bcountdown\b|\battendance\b|\bcomes back\b|\btomorrow\b|\bnext crate\b/i,
      `the crate action simulated a state that does not exist: ${rendered}`);
  }
});

test("the crate open document cannot claim both a refusal and a moved ship", () => {
  const doc = (overrides) => () => parseCrateOpenDocument({ ...structuredClone(ACCEPTED_OPEN_DOCUMENT), ...overrides });

  assert.equal(parseCrateOpenDocument(structuredClone(ACCEPTED_OPEN_DOCUMENT)).opened, true);
  assert.equal(parseCrateOpenDocument(structuredClone(REFUSED_OPEN_DOCUMENT)).opened, false);

  // ⭐ LEAN'S LAW, RE-DERIVED HERE. `a_refused_open_publishes_no_gauge_and_no
  // _entry` is a fact about the Lean SUM type; what arrives here is JSON from a
  // node, so a document that refuses while carrying a panel is refused outright
  // rather than rendered with the parts that did arrive.
  assert.throws(doc({ opened: false, refusal: "crate-refused" }), { code: "crate-open-verdict" });
  assert.throws(doc({ opened: false, refusal: "crate-refused", entry: null }), { code: "crate-open-verdict" });
  // …and an acceptance must carry all three of entry, panel and period.
  assert.throws(doc({ entry: null }), { code: "crate-open-verdict" });
  assert.throws(doc({ panel: null }), { code: "crate-open-verdict" });
  assert.throws(doc({ period: null }), { code: "crate-open-verdict" });
  assert.throws(doc({ refusal: "crate-refused" }), { code: "crate-open-verdict" });
  // A tag this page has no words for is refused rather than echoed raw.
  assert.throws(doc({ opened: false, entry: null, panel: null, refusal: "invented-tag" }), { code: "crate-open-verdict" });

  // The exact key set refuses a grown field rather than ignoring it, and is
  // never widened. This asserts the refusal exists so nobody deletes the check.
  assert.throws(doc({ streak: 3 }), { code: "crate-open-field" });
  assert.throws(() => parseCrateOpenDocument({ format: CRATE_OPEN_DOCUMENT_FORMAT }), { code: "crate-open-field" });
  // A present-but-unusable verdict is a verdict refusal, not a missing field.
  assert.throws(doc({ opened: "true" }), { code: "crate-open-verdict" });

  // A gauge whose needle lies is refused on this wire exactly as on the read.
  assert.throws(doc({
    panel: { ...structuredClone(ACCEPTED_OPEN_DOCUMENT.panel), gauges: [{ gauge: 1, meter: "supplies", exact_total: 1, full_at: 64, shown: 9, at_full: false }] },
  }), { code: "station-gauge" });

  // The envelope's append flag must agree with the crate's verdict: an
  // acceptance the node did not log is not an opening that is in effect.
  assert.throws(() => parseCrateOpenView(crateOpenEnvelope({ log_appended: false }), STATION_AUTHORITY), { code: "crate-open-verdict" });
  assert.throws(() => parseCrateOpenView(declinedOpenEnvelope({ log_appended: true }), STATION_AUTHORITY), { code: "crate-open-verdict" });
  assert.throws(() => parseCrateOpenView(crateOpenEnvelope(), "a".repeat(64)), { code: "crate-open-authority" });
});

test("the crate action is disabled — never punished — for a crew key that cannot open", () => {
  const unbound = buildCrateOpenAction({});
  assert.equal(unbound.state, "unavailable");
  assert.equal(unbound.enabled, false);
  assert.match(unbound.standing, /binds none, and it will not invent one/);

  const stowaway = buildCrateOpenAction({ crew: { key: STOWAWAY_KEY, eligible: false } });
  assert.equal(stowaway.state, "unavailable");
  assert.equal(stowaway.enabled, false);
  assert.match(stowaway.standing, /the authored roster, not a penalty/);

  const ready = buildCrateOpenAction({ crew: { key: OPENER_KEY, eligible: true } });
  assert.equal(ready.state, "ready");
  assert.equal(ready.enabled, true);
  assert.equal(ready.label, "Open the Salvage Crate");
  // ⚠ THE BROWSER AUTHORS IDENTITY ONLY, and the copy says so.
  assert.match(ready.standing, /sends one thing: the crew key/);
  assert.match(ready.standing, /decided by the authority/);

  // Eligibility UNKNOWN is not eligibility FALSE: the node gets to answer.
  assert.equal(buildCrateOpenAction({ crew: { key: OPENER_KEY } }).enabled, true);

  // Every failure to open is a state with a reason, and none of them draws a gauge.
  for (const open of [
    { state: "unreachable", code: "crate-open-fetch", reason: "No authority answered this opening on this origin" },
    { state: "refused", code: "crate-open-shape", reason: "bad shape" },
  ]) {
    const action = buildCrateOpenAction({ crew: { key: OPENER_KEY, eligible: true }, open });
    assert.ok(action.headline && action.standing);
    assert.equal(action.enabled, false);
    assert.equal(action.gauges.length, 0);
    assert.equal(action.prize, null);
  }
});

test("opening the crate sends one crew key and nothing else, and every failure is a state", async () => {
  let sent = null;
  const capture = async (url, init) => {
    sent = { url: String(url), init };
    return { ok: true, status: 200, text: async () => JSON.stringify(crateOpenEnvelope()) };
  };

  const opened = await openSalvageCrate({
    authorityId: STATION_AUTHORITY, opener: OPENER_KEY,
    baseUrl: "https://poa.invalid/", fetchImpl: capture,
  });
  assert.equal(opened.state, "opened");
  assert.equal(opened.view.document.entry.prize, "communal-salvage:55");

  assert.equal(sent.init.method, "POST");
  assert.ok(sent.url.endsWith(`/node/api/poa/station/${STATION_AUTHORITY}/crate/open`), sent.url);
  // ⭐ THE WHOLE BODY. Not a seed, beacon, date, ticket, entry, contribution,
  // counter, sequence, period or panel state — Lean derives every one of those.
  assert.deepEqual(JSON.parse(sent.init.body), { opener: OPENER_KEY });
  assert.deepEqual(Object.keys(JSON.parse(sent.init.body)), ["opener"]);

  const declined = await openSalvageCrate({
    authorityId: STATION_AUTHORITY, opener: OPENER_KEY, baseUrl: "https://poa.invalid/",
    fetchImpl: async () => ({ ok: true, status: 200, text: async () => JSON.stringify(declinedOpenEnvelope()) }),
  });
  assert.equal(declined.state, "declined", "a crate refusal is an answer, not a fault");
  assert.equal(declined.view.document.refusal, "already-opened-this-period");

  const cases = [
    ["no authority", await openSalvageCrate({ authorityId: null, opener: OPENER_KEY, baseUrl: "https://poa.invalid/" })],
    ["no crew key", await openSalvageCrate({ authorityId: STATION_AUTHORITY, opener: null, baseUrl: "https://poa.invalid/" })],
    ["uppercase key", await openSalvageCrate({ authorityId: STATION_AUTHORITY, opener: OPENER_KEY.toUpperCase(), baseUrl: "https://poa.invalid/" })],
    ["no fetch", await openSalvageCrate({ authorityId: STATION_AUTHORITY, opener: OPENER_KEY, baseUrl: "https://poa.invalid/", fetchImpl: null })],
    ["network", await openSalvageCrate({ authorityId: STATION_AUTHORITY, opener: OPENER_KEY, baseUrl: "https://poa.invalid/", fetchImpl: async () => { throw new Error("no route"); } })],
    ["node refusal", await openSalvageCrate({ authorityId: STATION_AUTHORITY, opener: OPENER_KEY, baseUrl: "https://poa.invalid/", fetchImpl: async () => ({ ok: false, status: 503, text: async () => JSON.stringify({ refused: "lean-crate-open-absent" }) }) })],
    ["garbage", await openSalvageCrate({ authorityId: STATION_AUTHORITY, opener: OPENER_KEY, baseUrl: "https://poa.invalid/", fetchImpl: async () => ({ ok: true, status: 200, text: async () => JSON.stringify({ format: "SOMETHING" }) }) })],
  ];
  for (const [label, result] of cases) {
    assert.notEqual(result.state, "opened", `${label} produced an opening`);
    assert.ok(result.code && result.reason, `${label} produced a state with no reason`);
  }
  assert.equal(cases[5][1].code, "lean-crate-open-absent");
  assert.equal(cases[6][1].state, "refused");
});

test("the crate action renders a disabled control, a prize, and the finality gap verbatim", () => withFakeDocument(() => {
  const root = new FakeElement("section");
  mountCrateOpenAction(root, buildCrateOpenAction({ crew: { key: OPENER_KEY, eligible: true } }));
  assert.equal(root.dataset.state, "ready");
  const button = root.children.find((node) => node.tagName === "BUTTON");
  assert.equal(button.textContent, "Open the Salvage Crate");
  assert.equal(button.disabled, false);

  const unbound = new FakeElement("section");
  mountCrateOpenAction(unbound, buildCrateOpenAction({}));
  assert.equal(unbound.dataset.state, "unavailable");
  assert.equal(unbound.children.find((node) => node.tagName === "BUTTON").disabled, true,
    "a terminal with no crew key must be DISABLED, not offered an action that cannot work");

  const opened = new FakeElement("section");
  mountCrateOpenAction(opened, buildCrateOpenAction({
    crew: { key: OPENER_KEY, eligible: true },
    open: { state: "opened", view: parseCrateOpenView(crateOpenEnvelope(), STATION_AUTHORITY) },
  }));
  assert.equal(opened.dataset.state, "opened");
  // Keyed on the crate-open hook class, which the render node carries ALONGSIDE
  // the station panel's own dial/row classes — those are reused so the crate's
  // gauges are styled by the same rules as the panel's rather than shipping a
  // second, unstyled set.
  const has = (root, hook) => root.children.some((node) => node.className.split(" ").includes(hook));
  assert.ok(has(opened, "crate-open__gauges"));
  assert.ok(has(opened, "crate-open__prize"));
  // ⚠ The node's own sentence, not this page's summary of it.
  const finality = opened.children.find((node) => node.className === "crate-open__finality");
  assert.equal(finality.textContent, CRATE_FINALITY_GAP);

  const declined = new FakeElement("section");
  mountCrateOpenAction(declined, buildCrateOpenAction({
    crew: { key: OPENER_KEY, eligible: true },
    open: { state: "declined", view: parseCrateOpenView(declinedOpenEnvelope(), STATION_AUTHORITY) },
  }));
  assert.equal(declined.dataset.state, "declined");
  assert.ok(!has(declined, "crate-open__gauges"),
    "a refusal drew a gauge; `entry` and `panel` are null and nothing may be drawn from them");
  assert.ok(!has(declined, "crate-open__prize"));
}));

test("the station routes this client knows are the ones it uses, and it invents no identity", () => {
  assert.equal(STATION_PANEL_ROUTE, "/api/poa/station/{authority}/panel");
  assert.equal(STATION_CREW_ROUTE, "/api/poa/station/{authority}/crew/{crew}");
  assert.equal(CRATE_OPEN_ROUTE, "/api/poa/station/{authority}/crate/open");
  const source = new URL("../src/station-panel.js", import.meta.url);
  return readFile(source, "utf8").then((text) => {
    // The crew route takes a 64-hex crew key and this terminal binds none, so it
    // is recorded and never called. Nothing here may invent one to fill it.
    assert.doesNotMatch(text, /STATION_CREW_ROUTE\.replace/, "the crew route is being called with a key this terminal does not have");

    // ⚠ AND NO CREW KEY IS AUTHORED HERE EITHER. The open route DOES take one,
    // and it must be the caller's — a 64-hex literal in this module would be a
    // key this page minted for somebody.
    assert.doesNotMatch(text, /["'`][0-9a-f]{64}["'`]/, "station-panel.js carries a 64-hex literal; the browser authors identity, it does not invent it");

    // ⚑ THE BROWSER PUBLISHES NO ANSWER. The open body is one crew key; none of
    // these may ever be spelled into a request from here.
    const body = text.slice(text.indexOf("export async function openSalvageCrate"));
    const request = body.slice(0, body.indexOf("\n}"));
    for (const key of ["seed", "beacon", "period", "ticket", "entry", "contribution", "counter", "sequence", "panel", "gauge", "history"]) {
      assert.doesNotMatch(request, new RegExp(`["']${key}["']\\s*:`), `openSalvageCrate publishes \`${key}\`; the browser authors identity and intent only`);
    }
  });
});

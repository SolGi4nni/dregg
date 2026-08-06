import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  buildRecordsModel,
  compareHeads,
  loadRecordsState,
  mountRecords,
  parseRecordsView,
  RECORDS_KEY_SETS,
  parseSignalStatus,
} from "../src/records-view.js";
import {
  GENESIS_HEAD,
  RECORDS_AUTHORITY,
  finalizedRun,
  recordsDocument,
  recordsEnvelope,
  signalStatus,
} from "./records-fixtures.mjs";
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

/** Route the two GETs this module makes to two independent fixtures. */
function routedFetch({ records, status, recordsOk = true, statusOk = true }) {
  return async (url) => {
    const path = String(url);
    if (path.includes("/records/")) return { ok: recordsOk, status: recordsOk ? 200 : 503, text: async () => JSON.stringify(records) };
    if (path.includes("/status")) return { ok: statusOk, status: statusOk ? 200 : 503, text: async () => JSON.stringify(status) };
    throw new Error(`unexpected request: ${path}`);
  };
}

const LEAN_RECORDS = new URL("../../metatheory/Dregg2/Games/PathOfAngels/RecordsRuntime.lean", import.meta.url);

test("the exact key sets are read off the Lean encoders, not off a copy of themselves", async () => {
  const source = await readFile(LEAN_RECORDS, "utf8");
  assertEncoderReaderWorks(source, "ViewWire.toJson", "stage");

  // ⚠ TWO SOURCES, NOT THREE. The right side is the client's OWN exact set, not
  // a copy of it written here: a test carrying its own third spelling is a test
  // that passes while the client and the encoder disagree. A Lean-side field
  // addition reds here with a name; held against nothing it would land in a
  // browser as a total refusal with no clue which field moved.
  for (const [encoder, set] of [
    ["ViewWire.toJson", "document"],
    ["RunWire.toJson", "run"],
    ["ChainCoordinate.toJson", "chain"],
    ["PublicMissionWire.toJson", "mission"],
    ["ArtifactRefWire.toJson", "artifact"],
  ]) {
    const lean = encoder === "ArtifactRefWire.toJson"
      ? emittedKeys(await readFile(new URL("../../metatheory/Dregg2/Games/PathOfAngels/NetworkJudgeWire.lean", import.meta.url), "utf8"), encoder)
      : emittedKeys(source, encoder);
    assert.deepEqual(lean.sort(), [...RECORDS_KEY_SETS[set]].sort(),
      `${encoder} and the client's exact ${set} key set have drifted apart`);
  }

  // ⚠ AND THE FIELD THAT MUST NOT BE THERE. `PublicMissionWire` has no
  // `run_seed`, and that is the whole reason this surface can be public:
  // `SignalTriangulation.targetFromSeed` is three modulo operations from a
  // published seed to the answer. If a seed ever appears in this encoder, the
  // records route is publishing the target and this page must stop rendering it.
  assert.ok(!emittedKeys(source, "PublicMissionWire.toJson").includes("run_seed"),
    "the published mission now carries a run seed — this surface publishes the Signal answer");
  assert.ok(!emittedKeys(source, "RunWire.toJson").some((key) => key.includes("transcript")),
    "a run record now carries a transcript field — the plaintext guesses are on a public route");
});

test("a records document is checked field by field and cannot carry an unknown one", () => {
  const view = parseRecordsView(recordsEnvelope(), RECORDS_AUTHORITY);
  assert.equal(view.installed, true);
  assert.equal(view.records.stage, "awaiting-first-run");
  assert.deepEqual(view.records.runs, []);
  assert.equal(view.records.world.sequence, 0);

  assert.throws(() => parseRecordsView({ ...recordsEnvelope(), extra: 1 }, RECORDS_AUTHORITY), { code: "records-field" });
  assert.throws(() => parseRecordsView(recordsEnvelope({ format: "POA-RECORDS-VIEW-2" }), RECORDS_AUTHORITY), { code: "records-format" });
  assert.throws(() => parseRecordsView(recordsEnvelope(), "a".repeat(64)), { code: "records-authority" });
  assert.throws(() => parseRecordsView(recordsEnvelope({}, { format: "POA-RECORDS-OUT-1" }), RECORDS_AUTHORITY), { code: "records-format" });
  // A reader pinned to the old output format must FAIL its own check rather than
  // find two fields missing and a third moved — which is why Lean bumped it.
  assert.throws(() => parseRecordsView(recordsEnvelope({}, { run_seed: "a".repeat(64) }), RECORDS_AUTHORITY), { code: "records-field" });

  // An uninstalled authority is an absence, not an empty world.
  const bare = parseRecordsView(recordsEnvelope({ installed: false, replay: null, records: null }), RECORDS_AUTHORITY);
  assert.equal(bare.installed, false);
  assert.equal(bare.records, null);
  assert.throws(() => parseRecordsView(recordsEnvelope({ installed: false }), RECORDS_AUTHORITY), { code: "records-installed" });
  assert.throws(() => parseRecordsView(recordsEnvelope({ replay: null }), RECORDS_AUTHORITY), { code: "records-installed" });
});

test("a run's rung and its chain coordinate are re-derived against each other", () => {
  const withRun = (run) => parseRecordsView(recordsEnvelope({}, { stage: "active", runs: [run] }), RECORDS_AUTHORITY);
  assert.equal(withRun(finalizedRun()).records.runs[0].chain.commitOrdinal, 4);

  // Lean's `RunWire.coherentB`: a coordinate is exactly the evidence
  // `finalized` claims. Anything else carrying one is malformed, and a
  // `finalized` without one is too.
  assert.throws(() => withRun(finalizedRun({ chain: null })), { code: "records-run" });
  assert.throws(() => withRun(finalizedRun({ status: "judged" })), { code: "records-run" });
  assert.throws(() => withRun(finalizedRun({ status: "promoted" })), { code: "records-run" });

  // …and the stage is a READING of the rows (`stageOf_awaiting_iff_no_runs`), so
  // a document whose stage and rows disagree is one of the two lying.
  assert.throws(() => parseRecordsView(recordsEnvelope({}, { runs: [finalizedRun()] }), RECORDS_AUTHORITY), { code: "records-stage" });
  assert.throws(() => parseRecordsView(recordsEnvelope({}, { stage: "active" }), RECORDS_AUTHORITY), { code: "records-stage" });
});

test("the rebuilt head is checked against the head the authority publishes", () => {
  const replay = { transitionsReplayed: 0, retainedGenesisDigest: "5".repeat(64), rebuiltHeadDigest: GENESIS_HEAD };

  assert.equal(compareHeads(replay, parseSignalStatus(signalStatus(), RECORDS_AUTHORITY)).state, "agreed");

  // The node moving between the two reads is NOT a disagreement, and calling it
  // one would be a gate that cries wolf until somebody switches it off.
  const ahead = parseSignalStatus(signalStatus({}, { head_digest: "9".repeat(64), transition_count: 3 }), RECORDS_AUTHORITY);
  assert.equal(compareHeads(replay, ahead).state, "advanced");

  // ⚠ AND IT CAN GO RED. A served head that is not ahead and not equal means two
  // reads of one durable history disagree, which is a defect either way round.
  const behind = parseSignalStatus(signalStatus({}, { head_digest: "9".repeat(64), transition_count: 0 }), RECORDS_AUTHORITY);
  assert.equal(compareHeads(replay, behind).state, "disagreed");
  assert.match(compareHeads(replay, behind).detail, /cannot both be right/);

  // A status that was never read is not agreement.
  assert.equal(compareHeads(replay, null).state, "unavailable");
});

test("every way of not reading the records lands as a state, and none of them throws", async () => {
  const base = { authorityId: RECORDS_AUTHORITY, baseUrl: "https://poa.invalid/" };
  const cases = [
    ["no authority", await loadRecordsState({ ...base, authorityId: null })],
    ["no fetch", await loadRecordsState({ ...base, fetchImpl: null })],
    ["network", await loadRecordsState({ ...base, fetchImpl: async () => { throw new Error("no route"); } })],
    ["node refusal", await loadRecordsState({ ...base, fetchImpl: routedFetch({ records: { refused: "lean-records-absent" }, status: {}, recordsOk: false }) })],
    ["garbage", await loadRecordsState({ ...base, fetchImpl: routedFetch({ records: { format: "SOMETHING" }, status: signalStatus() }) })],
  ];
  for (const [label, result] of cases) {
    assert.notEqual(result.state, "ready", `${label} produced a readable records view`);
    assert.ok(result.code && result.reason, `${label} produced a state with no reason`);
  }
  assert.equal(cases[3][1].code, "lean-records-absent");
  assert.equal(cases[4][1].state, "refused");

  // A records read that works while the status route does not is still a read —
  // and reports that the cross-check did not happen, never that it passed.
  const oneLegged = await loadRecordsState({ ...base, fetchImpl: routedFetch({ records: recordsEnvelope(), status: {}, statusOk: false }) });
  assert.equal(oneLegged.state, "ready");
  assert.equal(oneLegged.crossCheck.state, "unavailable");

  const both = await loadRecordsState({ ...base, fetchImpl: routedFetch({ records: recordsEnvelope(), status: signalStatus() }) });
  assert.equal(both.crossCheck.state, "agreed");
});

test("at height zero the page renders the installed world as content, not as an apology", () => {
  const model = buildRecordsModel({ state: "ready", view: parseRecordsView(recordsEnvelope(), RECORDS_AUTHORITY), crossCheck: compareHeads({ transitionsReplayed: 0, retainedGenesisDigest: "5".repeat(64), rebuiltHeadDigest: GENESIS_HEAD }, parseSignalStatus(signalStatus(), RECORDS_AUTHORITY)) });
  assert.equal(model.state, "ready");
  assert.equal(model.stage, "awaiting-first-run");
  assert.equal(model.headline, "No run has landed yet");
  assert.match(model.standing, /This is not an empty page/);

  const sections = Object.fromEntries(model.sections.map((section) => [section.id, Object.fromEntries(section.rows)]));
  assert.equal(sections.identity.Stage, "awaiting-first-run");
  assert.equal(sections.world["World sequence"], "0");
  assert.equal(sections.mission["Privacy grade"], "public");
  assert.equal(sections.canon["Canon revision"], "1");
  assert.match(sections.reward.Standing, /unsettled preview/);
  assert.deepEqual(model.runs, []);
  assert.equal(model.crossCheck.state, "agreed");

  // ⚠ The zero-run page must not carry a number nothing produced. Every figure
  // above came out of the parsed document; this asserts the two counters a
  // reader is most likely to over-read are the served zeros.
  assert.equal(sections.canon["Archive entries"], "0");
  assert.equal(sections.canon.Players, "0");

  const active = buildRecordsModel({
    state: "ready",
    view: parseRecordsView(recordsEnvelope({}, { stage: "active", runs: [finalizedRun()] }), RECORDS_AUTHORITY),
    crossCheck: { state: "unavailable", detail: "not read" },
  });
  assert.equal(active.headline, "1 run has landed");
  assert.equal(active.runs.length, 1);
  assert.match(active.runs[0].chain, /commit 4/);
});

test("an unread or refused records surface claims nothing at all", () => {
  const refused = buildRecordsModel({ state: "refused", code: "records-run", reason: "incoherent rung" });
  assert.equal(refused.state, "refused");
  assert.equal(refused.sections.length, 0, "a refused document must not render the parts that happened to parse");

  const unreachable = buildRecordsModel({ state: "unreachable", code: "records-fetch", reason: "No records surface answered on this origin" });
  assert.equal(unreachable.state, "sealed");
  assert.match(unreachable.standing, /no local copy of a world/);

  const bare = buildRecordsModel({ state: "ready", view: parseRecordsView(recordsEnvelope({ installed: false, replay: null, records: null }), RECORDS_AUTHORITY), crossCheck: { state: "unavailable", detail: "" } });
  assert.equal(bare.state, "uninstalled");
  assert.match(bare.headline, /No world is installed/);
  assert.equal(bare.sections.length, 0);

  assert.equal(buildRecordsModel(null).state, "pending");
});

test("the records view renders text nodes and marks its own state", () => withFakeDocument(() => {
  const root = new FakeElement("article");
  mountRecords(root, buildRecordsModel({
    state: "ready",
    view: parseRecordsView(recordsEnvelope(), RECORDS_AUTHORITY),
    crossCheck: { state: "agreed", detail: "two computations, one answer" },
  }));
  assert.equal(root.dataset.state, "ready");
  const sections = root.children.filter((node) => node.className === "records-section").map((node) => node.dataset.section);
  assert.deepEqual(sections, ["identity", "world", "mission", "reward", "canon"]);
  const runs = root.children.find((node) => node.className === "records-runs");
  assert.match(runs.children.at(-1).textContent, /nothing on this page can put one here/);
  assert.equal(root.children.find((node) => node.className === "records-crosscheck").dataset.crosscheck, "agreed");
}));

test("the records document shape this client accepts is the one the node envelope declares", async () => {
  // The envelope is Rust, not Lean, so it is pinned separately: serde emits
  // struct fields in declaration order, and this reads that order out of the
  // struct rather than restating it.
  const rust = await readFile(new URL("../../node/src/poa_records_api.rs", import.meta.url), "utf8");
  const struct = rust.slice(rust.indexOf("pub struct PoaRecordsResponseV1"));
  const fields = [...struct.slice(0, struct.indexOf("\n}")).matchAll(/pub (\w+):/g)].map((match) => match[1]);
  assert.deepEqual(fields, [...RECORDS_KEY_SETS.envelope]);

  const replayStruct = rust.slice(rust.indexOf("pub struct PoaRecordsReplayViewV1"));
  const replayFields = [...replayStruct.slice(0, replayStruct.indexOf("\n}")).matchAll(/pub (\w+):/g)].map((match) => match[1]);
  assert.deepEqual(replayFields, [...RECORDS_KEY_SETS.replay]);

  // And the route this client fetches is the one the node mounts.
  assert.match(rust, /RECORDS_PATH: &str = "\/api\/poa\/records\/\{authority\}"/);
});

import assert from "node:assert/strict";
import { webcrypto } from "node:crypto";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  buildPlatformModel,
  EVIDENCE_URLS,
  loadPlatformEvidence,
  mountPlatformTerminal,
} from "../src/platform-terminal.js";

if (!globalThis.crypto) globalThis.crypto = webcrypto;

const webRoot = new URL("../", import.meta.url);
const baseUrl = "https://beta.pathofangels.network/";
const evidenceFiles = Object.freeze({
  [`/${EVIDENCE_URLS.expeditionProvenance}`]: new URL(`../${EVIDENCE_URLS.expeditionProvenance}`, import.meta.url),
  [`/${EVIDENCE_URLS.archiveProvenance}`]: new URL(`../${EVIDENCE_URLS.archiveProvenance}`, import.meta.url),
  [`/${EVIDENCE_URLS.recorderConfig}`]: new URL(`../${EVIDENCE_URLS.recorderConfig}`, import.meta.url),
  [`/${EVIDENCE_URLS.recorderDemo}`]: new URL(`../${EVIDENCE_URLS.recorderDemo}`, import.meta.url),
});

async function evidenceBodies() {
  return Object.fromEntries(await Promise.all(Object.entries(evidenceFiles).map(async ([path, url]) => [path, await readFile(url, "utf8")])));
}

function fetchFromBodies(bodies, calls = []) {
  return async (input) => {
    const url = new URL(String(input));
    calls.push(url.href);
    const body = bodies[url.pathname];
    return body === undefined
      ? { ok: false, status: 404, url: url.href, async text() { return ""; } }
      : { ok: true, status: 200, url: url.href, async text() { return body; } };
  };
}

async function realEvidence() {
  const bodies = await evidenceBodies();
  return loadPlatformEvidence({ baseUrl, fetchImpl: fetchFromBodies(bodies) });
}

const readyContent = Object.freeze({
  state: "ready",
  manifestDigest: `sha256:${"ab".repeat(32)}`,
  epoch: 1,
  counter: 8,
  missionCount: 4,
});

test("the home terminal reads the exact installed provenance and replay sources", async () => {
  const calls = [];
  const bodies = await evidenceBodies();
  const evidence = await loadPlatformEvidence({ baseUrl, fetchImpl: fetchFromBodies(bodies, calls) });

  assert.deepEqual(calls.sort(), Object.values(EVIDENCE_URLS).map((path) => new URL(path, baseUrl).href).sort());
  assert.deepEqual({
    state: evidence.expedition.state,
    states: evidence.expedition.states,
    actions: evidence.expedition.actions,
    transitions: evidence.expedition.transitions,
    accepting: evidence.expedition.acceptingRows,
    refusing: evidence.expedition.refusingRows,
  }, { state: "ready", states: 53, actions: 16, transitions: 848, accepting: 92, refusing: 756 });
  assert.deepEqual({
    state: evidence.archive.state,
    states: evidence.archive.states,
    actions: evidence.archive.actions,
    transitions: evidence.archive.transitions,
    terminalStates: evidence.archive.terminalStates,
    winningPlans: evidence.archive.winningPlans,
  }, { state: "ready", states: 822, actions: 8, transitions: 6576, terminalStates: 1, winningPlans: 1 });
  assert.deepEqual({
    state: evidence.recorder.state,
    source: evidence.recorder.source,
    transitions: evidence.recorder.transitions,
    reported: evidence.recorder.reportedTransitionCount,
    fullHistory: evidence.recorder.fullHistory,
    finality: evidence.recorder.consensusFinality,
  }, {
    state: "ready",
    source: "demo-fixture",
    transitions: 3,
    reported: 3,
    fullHistory: true,
    finality: "not_asserted_by_this_view",
  });
  assert.equal(Object.isFrozen(evidence), true);
  assert.equal(Object.isFrozen(evidence.archive), true);
});

test("seven platform organs expose separate evidence grades instead of laundering one green light", async () => {
  const model = buildPlatformModel({ contentAuthority: readyContent, evidence: await realEvidence() });
  assert.deepEqual(model.surfaces.map(({ id }) => id), ["daily", "expedition", "archive", "recorder", "crew", "bazaar", "galley"]);
  assert.deepEqual(model.surfaces.map(({ grade }) => grade.label), [
    "SIGNED BY THE CURATOR",
    "PINNED PROVENANCE",
    "PINNED PROVENANCE",
    // The installed recorder is the DEMO fixture, and its grade must say so.
    "LINKED REHEARSAL",
    "NO PROFILE RECEIPT",
    "NO SETTLEMENT",
    "VERSIONED NODE",
  ]);
  assert.match(model.surfaces[0].copy, /4 drills are open/);
  // The grade vouches for the RULES and says so; it must not read as a verdict
  // on anything a player did.
  assert.match(model.surfaces[0].grade.detail, /not for any run you play/);
  // Linked ≠ final, in whatever words. The refused twin below holds the other
  // half: a refusal may not sound like a finality claim either.
  assert.match(model.surfaces[3].grade.detail, /not proof the network settled/);
  assert.deepEqual(model.register.map(({ id }) => id), ["content", "run", "judged", "expedition", "archive", "replay"]);
  assert.equal(model.register.find(({ id }) => id === "run").grade.label, "NO RUN RECEIPT");
  assert.equal(Object.isFrozen(model), true);
  assert.equal(Object.isFrozen(model.surfaces), true);
});

test("the daily card does not claim a run stays in this browser, because a judged one does not", async () => {
  const model = buildPlatformModel({ contentAuthority: readyContent, evidence: await realEvidence() });
  const daily = model.surfaces.find(({ id }) => id === "daily");
  // The false half of the retired sentence. `src/judged-session.js` opens a
  // judged run on the node, which re-derives the committed instance and scores
  // it; the browser classifies nothing.
  assert.doesNotMatch(daily.copy, /A run stays in this browser/);
  assert.match(daily.copy, /practice run stays in this browser and settles nothing/i);
  assert.match(daily.copy, /judged run leaves it/i);
  // …and the true half must survive: nothing here settles.
  assert.match(daily.copy, /settles nothing/);
});

test("a rehearsal fixture may not be graded as a head some node reported", async () => {
  const model = buildPlatformModel({ contentAuthority: readyContent, evidence: await realEvidence() });
  const recorder = model.surfaces.find(({ id }) => id === "recorder");
  assert.equal(recorder.grade.code, "linked-rehearsal");
  // The exact wrongness this grade replaced: crediting a node that never spoke.
  assert.doesNotMatch(recorder.grade.detail, /the head the node reported/);
  assert.match(recorder.grade.detail, /No node reported this head/);
  assert.match(recorder.grade.detail, /not proof the network settled/);
  // The label of the live grade is reserved for a live source, and it is the
  // ONLY thing that may claim a node reported anything.
  const live = buildPlatformModel({
    contentAuthority: readyContent,
    evidence: { recorder: { id: "recorder", state: "ready", source: "live-api", transitions: 12, reportedTransitionCount: 12 } },
  }).surfaces.find(({ id }) => id === "recorder");
  assert.equal(live.grade.label, "LINKED REPLAY");
  assert.match(live.grade.detail, /the authority’s node reported|the authority's node reported/);
  assert.match(live.grade.detail, /not proof the network settled/);
});

test("the judged run keeps a register row of its own, and every branch of it is measured", async () => {
  const evidence = await realEvidence();
  const row = (judged) => buildPlatformModel({ contentAuthority: readyContent, evidence, judged })
    .register.find(({ id }) => id === "judged");

  // Nothing asked yet is NOT an absence.
  assert.equal(row(null).grade.label, "STILL READING");
  assert.equal(row(null).state, "pending");
  assert.doesNotMatch(row(null).grade.detail, /no judged|cannot|unavailable/i);

  const blocked = row({
    custody: { canPlay: false, blocker: { code: "settle-node-curtained", what: "The node answers 401." }, settleBlocker: { code: "settle-node-curtained" } },
    session: { state: "unauthenticated" },
  });
  assert.equal(blocked.grade.label, "NO JUDGED RUN");
  assert.match(blocked.grade.detail, /settle-node-curtained/);

  const reachable = row({
    custody: { canPlay: true, blocker: null, settleBlocker: { code: "settle-node-curtained" } },
    session: { state: "none" },
  });
  assert.equal(reachable.grade.label, "JUDGED RUN REACHABLE");
  // Reachable to PLAY is never reachable to SETTLE, and the row says which.
  assert.match(reachable.grade.detail, /Settling is a separate act and is refused: settle-node-curtained/);

  const settlementReady = row({
    custody: { canPlay: true, canSettle: true, blocker: null, settleBlocker: null },
    session: { state: "none" },
  });
  assert.equal(settlementReady.grade.label, "JUDGED RUN REACHABLE");
  assert.match(settlementReady.grade.detail, /provider also exposes the scoped settlement action/);
  assert.doesNotMatch(settlementReady.grade.detail, /refused|settle-blocked/);

  const scored = row({
    custody: { canPlay: true, blocker: null, settleBlocker: { code: "settle-node-curtained" } },
    session: { state: "ready" },
  });
  assert.equal(scored.grade.label, "NODE-JUDGED, UNSETTLED");
  assert.match(scored.grade.detail, /this browser classified nothing/);
  assert.match(scored.grade.detail, /has not settled/);

  // The practice row keeps its own, weaker grade — the two never merge.
  assert.equal(row(null) === undefined, false);
  const practice = buildPlatformModel({ contentAuthority: readyContent, evidence }).register.find(({ id }) => id === "run");
  assert.equal(practice.grade.label, "NO RUN RECEIPT");
  assert.notEqual(practice.grade.code, scored.grade.code);
});

test("pending checks remain pending and never appear as red refusals", () => {
  const model = buildPlatformModel({ contentAuthority: { state: "pending" } });
  assert.equal(model.surfaces[0].grade.label, "CHECKING THE MANIFEST");
  for (const id of ["expedition", "archive", "recorder"]) {
    const item = model.surfaces.find((surface) => surface.id === id);
    assert.equal(item.state, "pending");
    assert.equal(item.grade.label, "STILL READING");
    assert.equal(item.grade.tone, "dim");
  }
});

test("one damaged provenance source refuses independently without erasing healthy instruments", async () => {
  const bodies = await evidenceBodies();
  bodies[`/${EVIDENCE_URLS.expeditionProvenance}`] = bodies[`/${EVIDENCE_URLS.expeditionProvenance}`].replace(
    '"states": 53',
    '"states": 54',
  );
  const evidence = await loadPlatformEvidence({ baseUrl, fetchImpl: fetchFromBodies(bodies) });
  assert.equal(evidence.expedition.state, "refused");
  assert.equal(evidence.archive.state, "ready");
  assert.equal(evidence.recorder.state, "ready");

  const model = buildPlatformModel({ contentAuthority: readyContent, evidence });
  const expedition = model.surfaces.find(({ id }) => id === "expedition");
  assert.equal(expedition.grade.label, "PROVENANCE REFUSED");
  assert.equal(expedition.grade.tone, "red");
  assert.equal(model.surfaces.find(({ id }) => id === "archive").grade.label, "PINNED PROVENANCE");
});

test("a damaged recorder fixture cannot become a linked replay or finality claim", async () => {
  const bodies = await evidenceBodies();
  bodies[`/${EVIDENCE_URLS.recorderDemo}`] = bodies[`/${EVIDENCE_URLS.recorderDemo}`].replace(
    '"predecessor_head_digest": "4444',
    '"predecessor_head_digest": "9999',
  );
  const evidence = await loadPlatformEvidence({ baseUrl, fetchImpl: fetchFromBodies(bodies) });
  assert.equal(evidence.expedition.state, "ready");
  assert.equal(evidence.archive.state, "ready");
  assert.equal(evidence.recorder.state, "refused");
  const recorder = buildPlatformModel({ contentAuthority: readyContent, evidence }).surfaces.find(({ id }) => id === "recorder");
  assert.equal(recorder.grade.label, "REPLAY REFUSED");
  assert.doesNotMatch(recorder.grade.detail, /finalized|final|settled/i);
});

test("refused signed content seals dailies without demoting independent lab evidence", async () => {
  const model = buildPlatformModel({
    contentAuthority: { state: "refused", reason: "content-signature" },
    evidence: await realEvidence(),
  });
  assert.equal(model.surfaces[0].state, "refused");
  assert.equal(model.surfaces[0].grade.label, "RULES REFUSED");
  assert.equal(model.surfaces.find(({ id }) => id === "expedition").state, "ready");
  assert.equal(model.surfaces.find(({ id }) => id === "recorder").state, "ready");
});

test("crew and bazaar affordances remain visibly non-authoritative", async () => {
  const model = buildPlatformModel({ contentAuthority: readyContent, evidence: await realEvidence() });
  assert.deepEqual(model.crew.roles, ["PATHFINDER", "ENGINEER", "CONTAINMENT", "MEDIC"]);
  assert.deepEqual({ profile: model.crew.profile, custody: model.crew.custody, persistence: model.crew.persistence }, {
    profile: "unbound",
    custody: "none",
    persistence: "not exposed",
  });
  // ⚠ "No officer profile" must not be readable as "nothing about you is kept".
  // The node keeps several player-keyed, durable things — `publicPlayers` in the
  // Galley reducer (which then refuses a second shift from that key) and the
  // judged session store keyed `authority_id || slot_be64 || player_key`. The
  // crew card names that rather than leaving a false absence behind.
  assert.equal(model.crew.nodeKeeps, "your player key where you have acted");
  const crewGrade = model.surfaces.find(({ id }) => id === "crew").grade;
  assert.match(crewGrade.detail, /no officer profile or crew receipt exists on any surface/i);
  assert.match(crewGrade.detail, /What the node does keep is narrower and real/);

  assert.equal(model.bazaar.length, 4);
  assert.equal(model.bazaar.every(({ ready }) => ready === false), true);
  assert.deepEqual(model.bazaar.map(({ label }) => label), [
    "Owned salvage",
    "Private order",
    "Threshold clearing",
    "Settlement receipt",
  ]);
});

test("invalid authority state is refused at the platform boundary", () => {
  assert.throws(
    () => buildPlatformModel({ contentAuthority: { state: "convenient-browser-fallback" } }),
    { code: "platform-content" },
  );
});

class FakeElement {
  constructor(tagName) {
    this.tagName = tagName.toUpperCase();
    this.children = [];
    this.dataset = {};
    this.attributes = {};
    this.className = "";
    this.textContent = "";
    this.href = "";
  }

  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = [...children]; }
  setAttribute(name, value) { this.attributes[name] = String(value); }
}

function descendants(node) {
  return [node, ...node.children.flatMap(descendants)];
}

test("mounting creates navigable organs and aria-disabled market gates", async () => {
  const previousDocument = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try {
    const roots = Object.fromEntries(["home", "register", "crew", "bazaar"].map((name) => [name, new FakeElement("section")]));
    mountPlatformTerminal(roots, buildPlatformModel({ contentAuthority: readyContent, evidence: await realEvidence() }));

    const home = descendants(roots.home);
    const cards = home.filter(({ dataset }) => dataset.surface);
    assert.equal(cards.length, 7);
    assert.deepEqual(home.filter(({ tagName }) => tagName === "A").map(({ href }) => href), [
      "#missions",
      "./labs/expedition-lab.html",
      "./labs/archive-lab.html",
      "./labs/flight-recorder.html",
      "#crew",
      "#bazaar",
      "#galley",
    ]);
    assert.equal(descendants(roots.register).filter(({ dataset }) => dataset.evidence).length, 6);
    assert.equal(descendants(roots.crew).filter(({ className }) => className === "crew-role").length, 4);
    const bazaarRows = descendants(roots.bazaar).filter(({ className }) => className === "bazaar-gate");
    assert.equal(bazaarRows.length, 4);
    assert.equal(bazaarRows.every(({ attributes }) => attributes["aria-disabled"] === "true"), true);
  } finally {
    globalThis.document = previousDocument;
  }
});

test("platform evidence loader does not fetch either multi-megabyte finite table", async () => {
  const calls = [];
  await loadPlatformEvidence({ baseUrl, fetchImpl: fetchFromBodies(await evidenceBodies(), calls) });
  assert.equal(calls.some((url) => url.endsWith("expedition-demonstrator.fixture.json")), false);
  assert.equal(calls.some((url) => url.endsWith("archive-lab-demonstrator.fixture.json")), false);
  assert.equal(calls.length, 4);
  assert.equal(webRoot.protocol, "file:");
});

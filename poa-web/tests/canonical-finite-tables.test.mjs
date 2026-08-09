import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { finiteTableAuthority, loadMissionCatalog, missionByGameId } from "../src/mission-catalog.js";
import { validateManifest } from "../src/poag1.js";
import {
  canonicalTableTranscript,
  createFiniteTableRun,
  replayFiniteTable,
  submitFiniteTableAction,
  tableRunView,
} from "../src/finite-table-runtime.js";
import { loadRelayRepairDescriptor, relayLinkCost } from "../src/relay-runtime.js";
import { loadSalvageLockDescriptor, salvagePracticeOracle } from "../src/salvage-runtime.js";

const canonical = new URL("../../poa/artifacts/poag1/", import.meta.url);
const parse = async (path) => JSON.parse(await readFile(new URL(path, canonical), "utf8"));

async function canonicalUnsignedBundle() {
  const rawManifest = await parse("manifest.json");
  const manifest = validateManifest(rawManifest);
  const payloads = Object.create(null);
  for (const pin of manifest.artifacts) {
    const bytes = new Uint8Array(await readFile(new URL(pin.path, canonical)));
    payloads[pin.path] = { bytes, json: JSON.parse(new TextDecoder().decode(bytes)), mediaType: pin.mediaType };
  }
  const manifestDigest = `sha256:${"d".repeat(64)}`;
  return {
    manifest,
    manifestDigest,
    contentEpoch: {
      schema: "POA-CONTENT-EPOCH-SIGNATURE-V1",
      manifestDigest,
      activationDigest: `sha256:${"e".repeat(64)}`,
      contentEpoch: 1,
      counter: 1,
    },
    payloads,
  };
}

async function canonicalDescriptors() {
  const bundle = await canonicalUnsignedBundle();
  const missions = await loadMissionCatalog(bundle);
  const load = (gameId, loader) => {
    const mission = missionByGameId(missions, gameId);
    return loader(bundle.payloads[mission.descriptorPath].json, finiteTableAuthority(mission));
  };
  return {
    bundle,
    missions,
    relay: load("relay-repair", loadRelayRepairDescriptor),
    salvage: load("salvage-lock", loadSalvageLockDescriptor),
  };
}

test("every enrolled mission is a zero-economy per-run hidden draw, and the manifest carries its descriptor", async () => {
  // ⚑ NOT A LIST OF GAME IDS. This assertion named four ids and their four
  // disclosures; counter 10 enrols seven and turned it red with nothing wrong.
  // What the catalog must satisfy is a PROPERTY of every mission it carries, and
  // that property does not change when the curator activates one more drill.
  const bundle = await canonicalUnsignedBundle();
  const missions = await loadMissionCatalog(bundle);
  assert.ok(missions.length > 0, "the candidate catalog enrols no mission at all");
  assert.ok(missions.every((mission) => mission.rewardClass === "non-economic-demo" && mission.ballotRegime === "none"));
  // ⚠ Every mission binds a per-run hidden draw. Before counter 7 each carried a
  // `run_seed` in this same unauthenticated-readable file, which named the live
  // instance of every game in the bundle.
  assert.ok(missions.every((mission) => mission.instanceBinding === "per-run-hidden-draw"));
  assert.ok(missions.every((mission) => ["oracle-only", "per-run-open"].includes(mission.instanceDisclosure)));
  // The disclosure is not free-floating copy: the descriptor's own security block
  // has to say the same word, or one of the two is describing a different game.
  for (const mission of missions) {
    const descriptor = bundle.payloads[mission.descriptorPath];
    assert.ok(descriptor, `${mission.gameId} is enrolled with no descriptor in the manifest`);
    assert.equal(descriptor.json.security.instance_visibility, mission.instanceDisclosure, `${mission.gameId} disclosure disagrees with its descriptor`);
  }
  const catalog = bundle.payloads["catalog.json"].json;
  assert.ok(catalog.missions.every((mission) => !("run_seed" in mission)));
  assert.ok(catalog.fixtures.every((fixture) => !("run_seed" in fixture)));
});

test("a catalog short one mission is refused, not accepted as a subset", async () => {
  // Dropping ANY single mission must refuse. The old test dropped mission 4 by
  // number and asserted a three-mission remainder, which stopped meaning anything
  // the moment mission 4 stopped being the last one.
  const bundle = await canonicalUnsignedBundle();
  const full = bundle.payloads["catalog.json"].json;
  for (const dropped of full.missions.map((mission) => mission.mission_id)) {
    const catalog = structuredClone(full);
    catalog.missions = catalog.missions.filter((mission) => mission.mission_id !== dropped);
    catalog.fixtures = catalog.fixtures.filter((fixture) => fixture.mission_id !== dropped);
    assert.equal(catalog.missions.length, full.missions.length - 1);
    const altered = {
      ...bundle,
      payloads: { ...bundle.payloads, "catalog.json": { ...bundle.payloads["catalog.json"], json: catalog } },
    };
    await assert.rejects(loadMissionCatalog(altered), { code: "catalog-missions" }, `dropping mission ${dropped} was accepted`);
  }
});

test("canonical Lean-emitted Relay and Salvage bytes match the strict web consumers", async () => {
  const { relay, salvage } = await canonicalDescriptors();

  // Relay ships the whole board family: eight boards, eight complete machines.
  assert.equal(relay.instance.modulus, 8);
  assert.deepEqual(relay.memberKeys, [0, 1, 2, 3, 4, 5, 6, 7]);
  assert.equal(relay.actions.length, 5);
  assert.equal(relay.initialState, "relay:0:0");
  assert.equal(relay.disclosure, "per-run-open");
  for (const member of relay.members) {
    assert.equal(member.transitions.length, member.states.length * relay.actions.length);
    assert.ok(member.states.length > 0 && member.states.length <= 64);
  }
  // Boards are genuinely different, so the draw ranges over eight outcomes.
  assert.equal(new Set(relay.instance.boards.map((board) => JSON.stringify(board))).size, 8);

  // Salvage ships one machine with oracle rows, and the whole practice space.
  assert.equal(salvage.disclosure, "oracle-only");
  assert.equal(salvage.memberKeys.length, 1);
  const machine = salvage.members[0];
  assert.deepEqual([machine.states.length, salvage.actions.length, machine.transitions.length], [1016, 6, 6096]);
  assert.equal(salvage.initialState, "salvage:0:none:0");
  assert.equal(salvage.instance.practice.boards.length, 90);
  const verdicts = machine.transitions.reduce((tally, row) => ({ ...tally, [row.verdict]: (tally[row.verdict] ?? 0) + 1 }), {});
  assert.deepEqual(verdicts, { accept: 456, resolve: 1200, refuse: 2136 });
});

test("no emitted descriptor or catalog byte names its own instance", async () => {
  const { bundle } = await canonicalDescriptors();
  const banned = ["run_seed", "\"target\"", "glyph_id", "glyph_label", "\"selected\"", "seed_byte", "\"outcomes\""];
  for (const [path, payload] of Object.entries(bundle.payloads)) {
    const text = new TextDecoder().decode(payload.bytes);
    for (const field of banned) {
      assert.ok(!text.includes(field), `${path} still carries ${field}, which names the hidden instance`);
    }
  }
});

test("a real Relay run is priced from the board it opened, and only that board", async () => {
  const { relay } = await canonicalDescriptors();
  const runs = relay.memberKeys.map((member) => {
    const run = createFiniteTableRun(relay, { mode: "practice", member });
    const view = tableRunView(relay, run);
    return { member, spares: view.spares, cost: relayLinkCost(relay, member, "alpha-beta") };
  });
  // Different boards really do price the same link differently; a client that
  // read prices off the action row rather than the board would see one number.
  assert.ok(new Set(runs.map((entry) => entry.cost)).size > 1);
  for (const entry of runs) {
    assert.equal(entry.spares, relay.instance.boards[entry.member].spares);
  }
  assert.throws(() => relayLinkCost(relay, 99, "alpha-beta"), { code: "relay-board" });
});

test("a real Salvage run cannot pass an oracle row without an answer", async () => {
  const { salvage } = await canonicalDescriptors();
  const first = submitFiniteTableAction(salvage, createFiniteTableRun(salvage, { mode: "practice", member: 0 }), "slot-0");
  assert.equal(tableRunView(salvage, first).exposed, 0);
  assert.throws(() => submitFiniteTableAction(salvage, first, "slot-1"), { code: "table-oracle-required" });

  // Answered from an emitted practice board, the run walks; the answer is in the
  // transcript, so a reader with the opened secret can recheck it.
  const oracle = salvagePracticeOracle(salvage, 0);
  const answer = oracle(tableRunView(salvage, first), "slot-1");
  assert.ok(answer === "match" || answer === "mismatch");
  const second = submitFiniteTableAction(salvage, first, "slot-1", answer);
  const transcript = JSON.parse(canonicalTableTranscript(second));
  assert.deepEqual(transcript.steps, [
    { action: "slot-0", resolution: null },
    { action: "slot-1", resolution: answer },
  ]);
  assert.equal(transcript.mode, "practice");
  assert.equal(transcript.settlement, "unsettled-local-transcript");

  // Board 0 of the emitted space is [0,0,1,1,2,2], so plates 0 and 1 pair and
  // plates 0 and 2 do not. The oracle reads the board; it does not decide rules.
  assert.deepEqual(salvage.instance.practice.boards[0], [0, 0, 1, 1, 2, 2]);
  assert.equal(answer, "match");
  assert.equal(oracle(tableRunView(salvage, first), "slot-2"), "mismatch");
});

test("a real judged Salvage transcript carries answers, never the board", async () => {
  const { salvage } = await canonicalDescriptors();
  const opening = {
    slot: 12,
    mission_id: salvage.authority.missionId,
    commitment: "a".repeat(64),
    curator_pubkey: "b".repeat(64),
    signature: "c".repeat(128),
  };
  const run = replayFiniteTable(salvage, { mode: "judged", opening }, [
    { action: "slot-0" },
    { action: "slot-1", resolution: "match" },
  ]);
  const transcript = JSON.parse(canonicalTableTranscript(run));
  assert.equal(transcript.mode, "judged");
  assert.equal(transcript.member, null);
  assert.equal(transcript.slot, 12);
  assert.deepEqual(transcript.steps.map((step) => step.resolution), [null, "match"]);
  // Nothing in a judged transcript names the board it was played against.
  assert.ok(!JSON.stringify(transcript).includes("practice"));
});

test("the real descriptors refuse a widened disclosure and a relabelled security block", async () => {
  const bundle = await canonicalUnsignedBundle();
  const missions = await loadMissionCatalog(bundle);
  const salvageMission = missionByGameId(missions, "salvage-lock");
  const salvageJson = bundle.payloads[salvageMission.descriptorPath].json;

  const opened = structuredClone(salvageJson);
  opened.security.instance_visibility = "per-run-open";
  opened.instance.disclosure = "per-run-open";
  assert.throws(() => loadSalvageLockDescriptor(opened, finiteTableAuthority(salvageMission)), { code: "table-security" });

  const rewarded = structuredClone(salvageJson);
  rewarded.security.competitive_rewards = true;
  assert.throws(() => loadSalvageLockDescriptor(rewarded, finiteTableAuthority(salvageMission)), { code: "table-security" });

  // Collapsing every oracle row onto its match branch is what a descriptor that
  // had decided the board would look like. It is refused, though NOT by the
  // "this table has no oracle rows" backstop: the mismatch branches are the only
  // way into a large part of the closure, so the reachability check catches it
  // first. Recorded as measured, because the weaker check never gets to run.
  const settled = structuredClone(salvageJson);
  let collapsed = 0;
  for (const row of settled.state_machine.transitions) {
    if (row.verdict !== "resolve") continue;
    row.verdict = "accept";
    row.next = row.on_match;
    row.on_match = null;
    row.on_mismatch = null;
    collapsed += 1;
  }
  assert.equal(collapsed, 1200, "the mutation must actually remove every oracle row");
  assert.throws(() => loadSalvageLockDescriptor(settled, finiteTableAuthority(salvageMission)), { code: "table-state-closure" });
});

import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { loadPOAG1 } from "../src/poag1.js";
import { loadMissionCatalog, missionByGameId } from "../src/mission-catalog.js";
import {
  canonicalReplay,
  createJudgedRun,
  createPracticeRun,
  loadSignalDescriptor,
  replayPractice,
  submitJudgedGuess,
  submitPracticeGuess,
} from "../src/signal-runtime.js";
import { POA_EXPECTED_CONTENT_EPOCH, POA_EXPECTED_CURATOR_COUNTER } from "../src/trust-config.js";
import { actualFetch } from "./actual-bundle.mjs";

async function authenticatedBundle() {
  return loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
    fetcher: await actualFetch(),
  });
}

async function actualSignal(bundle) {
  bundle ??= await authenticatedBundle();
  const descriptor = bundle.payloads["games/signal-triangulation.json"];
  const mission = missionByGameId(await loadMissionCatalog(bundle), "signal-triangulation");
  return loadSignalDescriptor(descriptor.json, mission, bundle.contentEpoch);
}

const opening = (missionId) => ({
  slot: 19,
  mission_id: missionId,
  commitment: "a".repeat(64),
  curator_pubkey: "b".repeat(64),
  signature: "c".repeat(128),
});

test("the actual artifact is the complete instance-free Signal oracle", async () => {
  const descriptor = await actualSignal();
  const domain = descriptor.alphabet ** descriptor.codeLength;
  assert.equal(domain, 216);
  assert.equal(descriptor.codes.length, domain);
  assert.equal(descriptor.table.length, domain);
  assert.ok(descriptor.table.every((row) => row.length === domain));
  assert.equal(descriptor.maxTurns, descriptor.mission.actionLimit);
  assert.equal(descriptor.mission.rewardClass, "non-economic-demo");
  assert.deepEqual(descriptor.mission.activation, {
    state: "detached-signature-required",
    digestSource: "POA-CONTENT-EPOCH-SIGNATURE-V1",
  });
  assert.deepEqual(descriptor.security, {
    classification: "committed-hidden-instance",
    instanceVisibility: "oracle-only",
    competitiveRewards: false,
    economicRewards: false,
  });
  // ⚠ The property that makes a 216x216 rulebook safe to ship: every row solves
  // at exactly its own index, so the table states every rule and singles out no
  // instance. `loadSignalDescriptor` refuses one that does not.
  descriptor.table.forEach((row, index) => {
    const solvedAt = [...row].flatMap((id, column) => (id === descriptor.solvedClassId ? [column] : []));
    assert.deepEqual(solvedAt, [index]);
  });
  assert.equal(descriptor.instance.disclosure, "oracle-only");
  assert.equal(descriptor.instance.operatorKnowsInstance, true);
});

test("a practice run reads its own row and says PRACTICE in the transcript", async () => {
  const descriptor = await actualSignal();
  const pick = 100;
  const target = descriptor.codes[pick];
  const other = descriptor.codes[(pick + 7) % descriptor.codes.length];
  const first = replayPractice(descriptor, pick, [other, target]);
  const second = replayPractice(descriptor, pick, [[...other], [...target]]);
  assert.equal(canonicalReplay(first), canonicalReplay(second));
  assert.equal(first.solved, true);

  const transcript = JSON.parse(canonicalReplay(first));
  assert.equal(transcript.mode, "practice");
  assert.equal(transcript.practice_instance, pick);
  assert.equal(transcript.slot, null);
  assert.equal(transcript.slot_commitment, null);
  assert.equal(transcript.content_epoch, descriptor.mission.contentEpoch);
  assert.match(transcript.activation_digest, /^sha256:[0-9a-f]{64}$/);
  assert.deepEqual(transcript.security, descriptor.security);
});

test("a judged run learns nothing: no code, no seed, no row index", async () => {
  const descriptor = await actualSignal();
  const run = createJudgedRun(descriptor, opening(descriptor.missionId));
  assert.equal(run.mode, "judged");
  assert.equal(run.practiceInstance, null);
  assert.equal(run.practiceCode, null);
  assert.equal(run.slot, 19);

  // The host answers with a declared class id; the client applies it and cannot
  // derive it, because it does not have the code.
  const guess = descriptor.codes[3];
  const answered = submitJudgedGuess(descriptor, run, guess, 0);
  assert.equal(answered.turns.length, 1);
  assert.equal(answered.turns[0].classId, 0);
  const transcript = JSON.parse(canonicalReplay(answered));
  assert.equal(transcript.mode, "judged");
  assert.equal(transcript.practice_instance, null);
  assert.equal(transcript.slot_commitment, "a".repeat(64));

  // A class the descriptor does not declare is refused, not rendered.
  assert.throws(() => submitJudgedGuess(descriptor, run, guess, descriptor.classes.length), { code: "oracle-class" });
  // The two modes are not interchangeable in either direction.
  assert.throws(() => submitPracticeGuess(descriptor, run, guess), { code: "run-mode" });
  assert.throws(() => submitJudgedGuess(descriptor, createPracticeRun(descriptor, 0), guess, 0), { code: "run-mode" });
  assert.throws(() => createJudgedRun(descriptor, { ...opening(descriptor.missionId), mission_id: 999 }), { code: "opening-mission" });
});

test("a descriptor that names its own instance is refused, never scored", async () => {
  const bundle = await authenticatedBundle();
  const mission = missionByGameId(await loadMissionCatalog(bundle), "signal-triangulation");
  const source = bundle.payloads["games/signal-triangulation.json"].json;

  for (const field of ["target", "run_seed", "outcomes"]) {
    const game = structuredClone(source);
    game[field] = field === "target" ? [1, 2, 3] : "0".repeat(64);
    assert.throws(() => loadSignalDescriptor(game, mission, bundle.contentEpoch), { code: "instance-published" });
  }

  // A row that solves anywhere but at its own index distinguishes an instance.
  const skewed = structuredClone(source);
  const row = [...skewed.rules.table[5]];
  const alphabet = skewed.rules.class_alphabet;
  const solvedChar = alphabet[skewed.rules.classes.findIndex((entry) => entry.solved)];
  const solvedAt = row.indexOf(solvedChar);
  assert.equal(solvedAt, 5, "the fixture row must solve at its own index before it is skewed");
  row[solvedAt] = alphabet[0];
  row[9] = solvedChar;
  skewed.rules.table[5] = row.join("");
  assert.notEqual(skewed.rules.table[5], source.rules.table[5], "the skew must actually change the emitted row");
  assert.throws(() => loadSignalDescriptor(skewed, mission, bundle.contentEpoch), { code: "rules-table" });

  const truncated = structuredClone(source);
  truncated.rules.table.pop();
  assert.throws(() => loadSignalDescriptor(truncated, mission, bundle.contentEpoch), { code: "rules-table" });
});

test("a descriptor cannot silently claim secure or rewarded play", async () => {
  const bundle = await authenticatedBundle();
  const mission = missionByGameId(await loadMissionCatalog(bundle), "signal-triangulation");
  const game = structuredClone(bundle.payloads["games/signal-triangulation.json"].json);
  game.security.economic_rewards = true;
  assert.throws(() => loadSignalDescriptor(game, mission, bundle.contentEpoch), { code: "signal-security" });

  const opened = structuredClone(bundle.payloads["games/signal-triangulation.json"].json);
  opened.security.instance_visibility = "per-run-open";
  opened.instance.disclosure = "per-run-open";
  assert.throws(() => loadSignalDescriptor(opened, mission, bundle.contentEpoch), { code: "signal-security" });

  const unscored = structuredClone(bundle.payloads["games/signal-triangulation.json"].json);
  unscored.instance.practice.scored = true;
  assert.throws(() => loadSignalDescriptor(unscored, mission, bundle.contentEpoch), { code: "instance-practice" });
});

test("catalog v1 refuses mission, fixture, policy, and world-state drift", async () => {
  const bundle = await authenticatedBundle();
  const source = bundle.payloads["catalog.json"].json;
  const refuses = async (mutate, code) => {
    const catalog = structuredClone(source);
    mutate(catalog);
    const altered = {
      ...bundle,
      payloads: { ...bundle.payloads, "catalog.json": { ...bundle.payloads["catalog.json"], json: catalog } },
    };
    await assert.rejects(loadMissionCatalog(altered), { code });
  };

  await refuses((catalog) => catalog.missions.push(structuredClone(catalog.missions[0])), "catalog-missions");
  await refuses((catalog) => catalog.fixtures.push(structuredClone(catalog.fixtures[0])), "catalog-fixtures");
  await refuses((catalog) => { catalog.missions[0].privacy_grade = "process-separated-threshold"; }, "catalog-policy");
  await refuses((catalog) => { catalog.missions[0].ballot_regime = "one-wallet-one-voice"; }, "catalog-policy");
  await refuses((catalog) => { catalog.fixtures[0].base_world.extra = 0; }, "catalog-field");
  await refuses((catalog) => { catalog.fixtures[0].preview_world.intel = 1_000_001; }, "catalog-world");
  await refuses((catalog) => { catalog.fixtures[0].preview_world.discovered_relics.push(catalog.fixtures[0].preview_world.discovered_relics[0]); }, "catalog-array");
  await refuses((catalog) => { catalog.fixtures[0].preview_world.beta_artifacts.push(structuredClone(catalog.fixtures[0].preview_world.beta_artifacts[0])); }, "catalog-preview");
  // ⚠ The signed catalog is what fixes the disclosure. A catalog that widened
  // Signal to per-run-open would be widening it for the descriptor too.
  await refuses((catalog) => { catalog.missions[0].instance.disclosure = "per-run-open"; }, "catalog-instance");
  await refuses((catalog) => { catalog.missions[0].instance.binding = "static"; }, "catalog-instance");
  await refuses((catalog) => { catalog.missions[0].run_seed = "0".repeat(64); }, "catalog-field");
});

test("the web runtime contains no feedback implementation or answer generator", async () => {
  const source = await readFile(new URL("../src/signal-runtime.js", import.meta.url), "utf8");
  assert.doesNotMatch(source, /function\s+(exactCount|presentCount|feedback|targetForDay)\b/);
  assert.doesNotMatch(source, /Math\.random|Date\s*\(/);
});

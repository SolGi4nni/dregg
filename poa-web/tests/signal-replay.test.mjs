import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { loadPOAG1 } from "../src/poag1.js";
import { canonicalReplay, createSignalRun, loadSignalDescriptor, loadSignalMission, replaySignal, submitSignalGuess } from "../src/signal-runtime.js";
import { actualFetch } from "./actual-bundle.mjs";

async function authenticatedBundle() {
  return loadPOAG1({
    baseUrl: "https://poa.test/artifacts/poag1/",
    curatorKeyUrl: "https://poa.test/poa-curator-key.json",
    expectedContentEpoch: 1,
    expectedCounter: 1,
    fetcher: await actualFetch(),
  });
}

async function actualSignal(bundle) {
  bundle ??= await authenticatedBundle();
  const decode = (bytes) => JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes));
  const descriptor = bundle.payloads["games/signal-triangulation.json"];
  const mission = await loadSignalMission(bundle.payloads["catalog.json"].json, descriptor.bytes);
  return loadSignalDescriptor(descriptor.json, mission, bundle.contentEpoch);
}

test("the actual artifact is the complete finite Signal transition table", async () => {
  const descriptor = await actualSignal();
  assert.equal(descriptor.outcomes.size, descriptor.alphabet ** descriptor.codeLength);
  assert.equal(descriptor.outcomes.size, 216);
  assert.equal(descriptor.maxTurns, descriptor.mission.actionLimit);
  assert.equal(descriptor.mission.rewardClass, "non-economic-demo");
  assert.deepEqual(descriptor.mission.activation, {
    state: "detached-signature-required",
    digestSource: "POA-CONTENT-EPOCH-SIGNATURE-V1",
  });
  assert.deepEqual(descriptor.security, {
    classification: "transparent-beta-demo",
    targetVisibility: "public",
    competitiveRewards: false,
    economicRewards: false,
  });
});

test("actual Lean-emitted rows replay deterministically", async () => {
  const descriptor = await actualSignal();
  const unsolved = [...descriptor.outcomes.entries()].find(([, row]) => !row.solved);
  const solved = [...descriptor.outcomes.entries()].find(([, row]) => row.solved);
  assert.ok(unsolved && solved);
  const parseCode = ([key]) => key.split(",").map(Number);
  const guesses = [parseCode(unsolved), parseCode(solved)];
  const first = replaySignal(descriptor, guesses);
  const second = replaySignal(descriptor, guesses.map((guess) => [...guess]));
  assert.equal(canonicalReplay(first), canonicalReplay(second));
  assert.equal(first.solved, true);
  const transcript = JSON.parse(canonicalReplay(first));
  assert.equal(transcript.content_epoch, descriptor.mission.contentEpoch);
  assert.equal(transcript.activation_digest, descriptor.mission.activationDigest);
  assert.match(transcript.activation_digest, /^sha256:[0-9a-f]{64}$/);
  assert.deepEqual(transcript.security, descriptor.security);
});

test("a descriptor with an omitted row is refused, never locally scored", async () => {
  const bundle = await authenticatedBundle();
  const game = structuredClone(bundle.payloads["games/signal-triangulation.json"].json);
  game.outcomes.pop();
  const mission = await loadSignalMission(
    bundle.payloads["catalog.json"].json,
    bundle.payloads["games/signal-triangulation.json"].bytes,
  );
  assert.throws(() => loadSignalDescriptor(game, mission, bundle.contentEpoch), { code: "outcome-count" });
});

test("terminal transcripts refuse extension", async () => {
  const descriptor = await actualSignal();
  const [key] = [...descriptor.outcomes.entries()].find(([, row]) => row.solved);
  const solved = submitSignalGuess(descriptor, createSignalRun(descriptor), key.split(",").map(Number));
  assert.equal(solved.solved, true);
  assert.throws(() => submitSignalGuess(descriptor, solved, [0, 0, 0]), { code: "run-terminal" });
});

test("a descriptor cannot silently claim secure or rewarded play", async () => {
  const bundle = await authenticatedBundle();
  const game = structuredClone(bundle.payloads["games/signal-triangulation.json"].json);
  game.security.economic_rewards = true;
  const mission = await loadSignalMission(
    bundle.payloads["catalog.json"].json,
    bundle.payloads["games/signal-triangulation.json"].bytes,
  );
  assert.throws(
    () => loadSignalDescriptor(game, mission, bundle.contentEpoch),
    { code: "signal-security" },
  );
});

test("catalog v1 refuses mission, fixture, policy, and world-state drift", async () => {
  const bundle = await authenticatedBundle();
  const descriptorBytes = bundle.payloads["games/signal-triangulation.json"].bytes;
  const source = bundle.payloads["catalog.json"].json;
  const refuses = async (mutate, code) => {
    const catalog = structuredClone(source);
    mutate(catalog);
    await assert.rejects(loadSignalMission(catalog, descriptorBytes), { code });
  };

  await refuses((catalog) => catalog.missions.push(structuredClone(catalog.missions[0])), "catalog-missions");
  await refuses((catalog) => catalog.fixtures.push(structuredClone(catalog.fixtures[0])), "catalog-fixtures");
  await refuses((catalog) => { catalog.missions[0].privacy_grade = "process-separated-threshold"; }, "mission-policy");
  await refuses((catalog) => { catalog.missions[0].ballot_regime = "one-wallet-one-voice"; }, "mission-policy");
  await refuses((catalog) => { catalog.fixtures[0].base_world.extra = 0; }, "signal-field");
  await refuses((catalog) => { catalog.fixtures[0].preview_world.intel = 1_000_001; }, "world-state");
  await refuses((catalog) => { catalog.fixtures[0].preview_world.discovered_relics.push(catalog.fixtures[0].preview_world.discovered_relics[0]); }, "world-state");
  await refuses((catalog) => { catalog.fixtures[0].preview_world.beta_artifacts.push(structuredClone(catalog.fixtures[0].preview_world.beta_artifacts[0])); }, "world-state");
});

test("the web runtime contains no feedback implementation or answer generator", async () => {
  const source = await readFile(new URL("../src/signal-runtime.js", import.meta.url), "utf8");
  assert.doesNotMatch(source, /function\s+(exactCount|presentCount|feedback|targetForDay)\b/);
  assert.doesNotMatch(source, /Math\.random|Date\s*\(/);
});

import assert from "node:assert/strict";
import { execFile as execFileCallback } from "node:child_process";
import { createHash, webcrypto } from "node:crypto";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";
import { test } from "node:test";
import {
  BUILTIN_FIXTURE_SHA256,
  BUILTIN_PROVENANCE_SHA256,
  BUILTIN_SOURCE_COMMIT,
  ExpeditionTransitionRefusal,
  availableExpeditionActions,
  canonicalExpeditionTranscript,
  createExpeditionRun,
  currentExpeditionState,
  fetchBuiltinExpeditionDescriptor,
  fetchExpeditionDescriptor,
  loadExpeditionDescriptor,
  replayExpeditionActions,
  replayExpeditionRoute,
  rewindExpeditionRun,
  submitExpeditionAction,
  traceExpeditionRun,
  validateBuiltinProvenance,
} from "../labs/expedition-lab-runtime.js";

const fixtureUrl = new URL("../labs/expedition-demonstrator.fixture.json", import.meta.url);
const provenanceUrl = new URL("../labs/expedition-demonstrator.provenance.json", import.meta.url);
const repositoryRoot = fileURLToPath(new URL("../../", import.meta.url));
const metatheoryRoot = fileURLToPath(new URL("../../metatheory/", import.meta.url));
const execFile = promisify(execFileCallback);

async function fixtureText() {
  return readFile(fixtureUrl, "utf8");
}

async function fixtureDocument() {
  return JSON.parse(await fixtureText());
}

async function provenanceText() {
  return readFile(provenanceUrl, "utf8");
}

async function provenanceDocument() {
  return JSON.parse(await provenanceText());
}

async function descriptor() {
  return loadExpeditionDescriptor(await fixtureDocument(), {
    url: fixtureUrl.href,
    artifactSha256: "549c60d1c02be6c6c399020b1872dd4246b95d86a5bcadf21f6982e2ec2155ed",
    pinned: true,
  });
}

function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

async function builtinFetch(url) {
  const href = String(url);
  const body = href.includes("provenance") ? await provenanceText() : await fixtureText();
  return {
    ok: true,
    status: 200,
    url: href,
    async text() { return body; },
  };
}

test("the checked-in fixture is byte-pinned to its Lean sources and generated artifact", async () => {
  const provenance = JSON.parse(await readFile(provenanceUrl, "utf8"));
  const artifact = await fixtureText();
  assert.equal(Buffer.byteLength(artifact), provenance.artifact.bytes);
  assert.equal(sha256(artifact), provenance.artifact.sha256);
  assert.equal(sha256(await provenanceText()), BUILTIN_PROVENANCE_SHA256);
  assert.equal(provenance.artifact.sha256, BUILTIN_FIXTURE_SHA256);
  assert.equal(provenance.source_repository_commit, BUILTIN_SOURCE_COMMIT);
  assert.equal(provenance.source_repository_commit.length, 40);
  assert.match(provenance.generator.command, /lake env lean --run Dregg2\/Games\/PathOfAngels\/ExpeditionDemonstratorEmit\.lean/);
  for (const source of provenance.generator.sources) {
    const body = await readFile(new URL(`../../${source.path}`, import.meta.url));
    assert.equal(body.byteLength, source.bytes, source.path);
    assert.equal(sha256(body), source.sha256, source.path);
    assert.match(source.git_blob, /^[0-9a-f]{40}$/);
  }
  assert.deepEqual(provenance.boundary, {
    fiction_status: "non-canon-demonstrator",
    beta_candidates: "provisional-only",
    canon_promotion: false,
    asset_minting: false,
    settlement: false,
  });
});

test("the built-in loader verifies provenance bytes, claims, exact output, identity, counts, and routes", async () => {
  if (!globalThis.crypto) globalThis.crypto = webcrypto;
  const table = await fetchBuiltinExpeditionDescriptor(fixtureUrl.href, provenanceUrl.href, {
    fetchImpl: builtinFetch,
  });
  assert.equal(table.source.trust, "builtin-provenance-verified");
  assert.equal(table.source.pinned, true);
  assert.equal(table.source.artifactSha256, BUILTIN_FIXTURE_SHA256);
  assert.equal(table.source.artifactBytes, 294538);
  assert.equal(table.source.provenance.sourceCommit, BUILTIN_SOURCE_COMMIT);
  assert.deepEqual(table.referenceRoutes.map(({ id, actions }) => ({ id, actions })), [
    {
      id: "safe-beta",
      actions: [
        "traverse:1000", "traverse:1001", "traverse:1002", "survey:4040:1:11",
        "traverse:1003", "traverse:1004", "traverse:1008", "extract",
      ],
    },
    {
      id: "salvage-relic",
      actions: [
        "traverse:1000", "traverse:1005", "confront:21:13", "traverse:1006",
        "recover:31:12", "traverse:1007", "traverse:1008", "extract",
      ],
    },
  ]);
});

test("the public parsed-document loader cannot self-assert built-in trust and still refuses malformed transitions", async () => {
  const provenance = await provenanceDocument();
  const document = await fixtureDocument();
  const selfAsserted = loadExpeditionDescriptor(document, {
    url: "https://attacker.invalid/self-asserted.json",
    artifactSha256: BUILTIN_FIXTURE_SHA256,
    artifactBytes: 294538,
    pinned: true,
    builtIn: true,
    provenance,
    provenanceSha256: BUILTIN_PROVENANCE_SHA256,
  });
  assert.equal(selfAsserted.source.trust, "untrusted-instrument");
  assert.equal(selfAsserted.source.pinned, false);
  assert.equal(selfAsserted.source.artifactSha256, null);
  assert.equal(selfAsserted.source.artifactBytes, null);
  assert.equal(selfAsserted.source.provenance, null);

  const malformed = await fixtureDocument();
  malformed.state_machine.transitions.find((row) => row.verdict === "accept").next = "attacker-state";
  assert.throws(
    () => loadExpeditionDescriptor(malformed, {
      builtIn: true,
      artifactSha256: BUILTIN_FIXTURE_SHA256,
      artifactBytes: 294538,
      pinned: true,
      provenance,
      provenanceSha256: BUILTIN_PROVENANCE_SHA256,
    }),
    { code: "expedition-transition-target" },
  );
});

test("the raw-byte built-in path refuses a self-consistent mutated transition table before trust elevation", async () => {
  if (!globalThis.crypto) globalThis.crypto = webcrypto;
  const document = await fixtureDocument();
  const traverse = document.state_machine.transitions.find(
    (row) => row.state === document.state_machine.initial_state && row.action === "traverse:1000",
  );
  const withdraw = document.state_machine.transitions.find(
    (row) => row.state === document.state_machine.initial_state && row.action === "withdraw",
  );
  [traverse.next, withdraw.next] = [withdraw.next, traverse.next];
  const mutatedFixture = JSON.stringify(document);
  const fetchImpl = async (url) => ({
    ok: true,
    status: 200,
    url: String(url),
    async text() { return String(url).includes("provenance") ? provenanceText() : mutatedFixture; },
  });
  await assert.rejects(
    fetchBuiltinExpeditionDescriptor(fixtureUrl.href, provenanceUrl.href, { fetchImpl }),
    { code: "expedition-byte-pin" },
  );
});

test("provenance validation refuses a source-commit self-assertion", async () => {
  const provenance = await provenanceDocument();
  const wrongCommit = structuredClone(provenance);
  wrongCommit.source_repository_commit = "0".repeat(40);
  assert.throws(
    () => validateBuiltinProvenance(wrongCommit, BUILTIN_PROVENANCE_SHA256),
    { code: "expedition-provenance-commit" },
  );
});

test("the provenance commit tree binds each named source path to its claimed blob and digest", async () => {
  const provenance = await provenanceDocument();
  await execFile("git", ["cat-file", "-e", `${provenance.source_repository_commit}^{commit}`], { cwd: repositoryRoot });
  for (const source of provenance.generator.sources) {
    const { stdout: treeLine } = await execFile(
      "git",
      ["ls-tree", provenance.source_repository_commit, "--", source.path],
      { cwd: repositoryRoot },
    );
    assert.match(treeLine, new RegExp(`^100644 blob ${source.git_blob}\\t${source.path}\\n$`));
    const { stdout: blob } = await execFile(
      "git",
      ["cat-file", "blob", source.git_blob],
      { cwd: repositoryRoot, encoding: "buffer", maxBuffer: 1024 * 1024 },
    );
    assert.equal(blob.byteLength, source.bytes, source.path);
    assert.equal(sha256(blob), source.sha256, source.path);
  }
});

test("the pinned Lean emitter regenerates the checked-in fixture byte-for-byte", { timeout: 120_000 }, async (context) => {
  let emitted;
  try {
    ({ stdout: emitted } = await execFile(
      "lake",
      ["env", "lean", "--run", "Dregg2/Games/PathOfAngels/ExpeditionDemonstratorEmit.lean"],
      {
        cwd: metatheoryRoot,
        env: { ...process.env, LEAN_NUM_THREADS: "4" },
        encoding: "utf8",
        maxBuffer: 2 * 1024 * 1024,
        timeout: 110_000,
      },
    ));
  } catch (error) {
    if (error?.code === "ENOENT") return context.skip("lake is unavailable in this environment");
    throw error;
  }
  assert.equal(emitted, await fixtureText());
  assert.equal(sha256(emitted), BUILTIN_FIXTURE_SHA256);
});

test("the complete Lean table loads with exact counts, explicit refusals, and literal roles", async () => {
  const table = await descriptor();
  assert.equal(table.states.length, 53);
  assert.equal(table.actions.length, 16);
  assert.equal(table.transitions.length, 848);
  assert.equal(table.transitions.filter((row) => row.verdict === "accept").length, 92);
  assert.equal(table.transitions.filter((row) => row.verdict === "refuse").length, 756);
  assert.ok(table.transitions.filter((row) => row.verdict === "refuse").every((row) => row.reason));
  assert.deepEqual(
    table.actions.filter((action) => action.role).map(({ tag, role }) => [tag, role]),
    [
      ["confront", "containment"],
      ["survey", "pathfinder"],
      ["survey", "pathfinder"],
      ["recover", "engineer"],
      ["treat", "medic"],
    ],
  );
  const rows = availableExpeditionActions(table, createExpeditionRun(table));
  assert.equal(rows.length, 16);
  assert.deepEqual(rows.filter(({ row }) => row.verdict === "accept").map(({ action }) => action.id), ["traverse:1000", "withdraw"]);
});

test("safe and salvage reference routes replay only emitted next pointers and retain distinct receipts", async () => {
  const table = await descriptor();
  const safe = replayExpeditionRoute(table, "safe-beta");
  assert.equal(safe.terminal, true);
  assert.equal(safe.lastEffect, "extracted");
  assert.deepEqual(safe.lastReceipt.provisionalCandidates, ["4040:1"]);
  assert.deepEqual(safe.lastReceipt.recoveredSalvage, []);
  assert.deepEqual(safe.lastReceipt.relicDiscoveries, []);

  const salvage = replayExpeditionRoute(table, "salvage-relic");
  assert.equal(salvage.terminal, true);
  assert.equal(salvage.lastEffect, "extracted");
  assert.deepEqual(salvage.lastReceipt.provisionalCandidates, []);
  assert.deepEqual(salvage.lastReceipt.recoveredSalvage, [31]);
  assert.deepEqual(salvage.lastReceipt.relicDiscoveries, [9001]);
  assert.equal(currentExpeditionState(table, salvage).view.status, "inactive-with-secured-salvage");
});

test("refused orders report the emitted reason without changing state", async () => {
  const table = await descriptor();
  const initial = createExpeditionRun(table);
  assert.throws(() => submitExpeditionAction(table, initial, "traverse:1001"), (error) => {
    assert.ok(error instanceof ExpeditionTransitionRefusal);
    assert.equal(error.code, "expedition-transition-refused");
    assert.equal(error.reason, "wrong-origin-or-phase");
    assert.equal(error.stateId, initial.stateId);
    assert.match(error.message, /Table-provided expedition row refused/);
    assert.doesNotMatch(error.message, /Lean|pinned|provenance/i);
    return true;
  });
  assert.equal(initial.actions.length, 0);
  assert.equal(currentExpeditionState(table, initial).view.room, 100);

  const junction = submitExpeditionAction(table, initial, "traverse:1000");
  assert.equal(currentExpeditionState(table, junction).view.room, 101);
  assert.throws(() => submitExpeditionAction(table, junction, "traverse:1006"), {
    code: "expedition-transition-refused",
    reason: "wrong-origin-or-phase",
  });
});

test("withdrawal is a terminal edge without an extraction receipt", async () => {
  const table = await descriptor();
  const withdrawn = submitExpeditionAction(table, createExpeditionRun(table), "withdraw");
  assert.equal(withdrawn.terminal, true);
  assert.equal(withdrawn.lastEffect, "withdrawn");
  assert.equal(withdrawn.lastReceipt, null);
  assert.equal(currentExpeditionState(table, withdrawn).view.status, "inactive");
  assert.throws(() => submitExpeditionAction(table, withdrawn, "traverse:1000"), { code: "expedition-run-terminal" });
});

test("an eight-action stranded extraction state still dispatches Lean's accepted withdrawal as action nine", async () => {
  const table = await descriptor();
  const strandedActions = [
    "traverse:1000",
    "traverse:1005",
    "confront:21:13",
    "traverse:1006",
    "recover:31:12",
    "survey:4040:2:11",
    "traverse:1007",
    "traverse:1008",
  ];
  const stranded = replayExpeditionActions(table, strandedActions);
  assert.equal(stranded.actions.length, 8);
  assert.equal(stranded.terminal, false);
  const view = currentExpeditionState(table, stranded).view;
  assert.equal(view.room, 108);
  assert.equal(view.turns, 8);
  const withdrawalRow = availableExpeditionActions(table, stranded)
    .find(({ action }) => action.id === "withdraw").row;
  assert.equal(withdrawalRow.verdict, "accept");
  assert.equal(withdrawalRow.effect, "withdrawn");

  const withdrawn = submitExpeditionAction(table, stranded, "withdraw");
  assert.equal(withdrawn.actions.length, 9);
  assert.equal(withdrawn.terminal, true);
  assert.equal(withdrawn.lastEffect, "withdrawn");
  assert.equal(withdrawn.lastReceipt, null);
});

test("rewind, replay, and trace are exact transcript operations", async () => {
  const table = await descriptor();
  const actions = ["traverse:1000", "traverse:1005", "confront:21:13", "traverse:1006"];
  const run = replayExpeditionActions(table, actions);
  assert.equal(currentExpeditionState(table, run).view.room, 106);
  assert.equal(traceExpeditionRun(table, run).length, actions.length + 1);
  const rewound = rewindExpeditionRun(table, run);
  assert.deepEqual(rewound.actions, actions.slice(0, -1));
  assert.equal(currentExpeditionState(table, rewound).view.room, 105);
  assert.deepEqual(replayExpeditionActions(table, run.actions), run);

  const transcript = JSON.parse(canonicalExpeditionTranscript(table, run));
  assert.equal(transcript.settlement, "unsettled-local-demonstrator");
  assert.equal(transcript.fiction_status, "non-canon-demonstrator");
  assert.equal(transcript.source_pinned, false);
  assert.equal(transcript.source_trust, "untrusted-instrument");
  assert.equal(transcript.canon_claim, false);
  assert.equal(transcript.reward_claim, false);
});

test("the dispatcher follows a complete accepted table even when its next pointers contradict action names", async () => {
  const document = await fixtureDocument();
  const original = loadExpeditionDescriptor(structuredClone(document));
  const routeStates = new Set();
  for (const route of original.referenceRoutes) {
    for (const entry of traceExpeditionRun(original, replayExpeditionRoute(original, route))) {
      routeStates.add(entry.state.id);
    }
  }
  const candidateState = original.states.find((state) => {
    if (routeStates.has(state.id)) return false;
    return original.transitions.filter((row) => row.state === state.id && row.verdict === "accept").length >= 2;
  });
  assert.ok(candidateState, "fixture needs a non-reference state with two accepted rows");
  const accepted = document.state_machine.transitions.filter(
    (row) => row.state === candidateState.id && row.verdict === "accept",
  );
  const originalTargets = [accepted[0].next, accepted[1].next];
  [accepted[0].next, accepted[1].next] = [accepted[1].next, accepted[0].next];
  const table = loadExpeditionDescriptor(document);

  const queue = [{ stateId: original.initialState, actions: [] }];
  const seen = new Set([original.initialState]);
  let prefix = null;
  while (queue.length && prefix === null) {
    const current = queue.shift();
    if (current.stateId === candidateState.id) {
      prefix = current.actions;
      break;
    }
    for (const row of original.transitions) {
      if (row.state !== current.stateId || row.verdict !== "accept" || seen.has(row.next)) continue;
      seen.add(row.next);
      queue.push({ stateId: row.next, actions: [...current.actions, row.action] });
    }
  }
  assert.ok(prefix, "candidate state must be reachable");
  const run = submitExpeditionAction(table, replayExpeditionActions(table, prefix), accepted[0].action);
  assert.equal(run.stateId, originalTargets[1]);
  assert.notEqual(run.stateId, originalTargets[0]);
});

test("hostile shape, boundary, row order, target, and terminal drift fail closed", async () => {
  const refuses = async (mutate, code) => {
    const document = await fixtureDocument();
    mutate(document);
    assert.throws(() => loadExpeditionDescriptor(document), { code });
  };
  await refuses((document) => { document.authority.canon_promotion = true; }, "expedition-authority");
  await refuses((document) => { document.fiction_status = "alpha-canon"; }, "expedition-fiction");
  await refuses((document) => { document.state_machine.transitions.pop(); }, "expedition-transition-count");
  await refuses((document) => {
    const rows = document.state_machine.transitions;
    [rows[0], rows[1]] = [rows[1], rows[0]];
  }, "expedition-transition-order");
  await refuses((document) => {
    document.state_machine.transitions.find((row) => row.verdict === "accept").next = "absent";
  }, "expedition-transition-target");
  await refuses((document) => {
    const terminal = document.state_machine.states.find((state) => state.terminal);
    const row = document.state_machine.transitions.find((candidate) => candidate.state === terminal.id);
    row.reason = "invented";
  }, "expedition-terminal-row");
});

test("URL loading enforces optional exact byte pins before parsing", async () => {
  if (!globalThis.crypto) globalThis.crypto = webcrypto;
  const body = await fixtureText();
  const fetchImpl = async () => ({
    ok: true,
    status: 200,
    url: "https://example.invalid/expedition.json",
    async text() { return body; },
  });
  const exact = sha256(body);
  const table = await fetchExpeditionDescriptor("https://example.invalid/expedition.json", {
    fetchImpl,
    expectedSha256: exact,
  });
  assert.equal(table.source.pinned, true);
  assert.equal(table.source.artifactSha256, exact);
  assert.equal(table.source.trust, "untrusted-instrument");
  await assert.rejects(
    fetchExpeditionDescriptor("https://example.invalid/expedition.json", {
      fetchImpl,
      expectedSha256: "0".repeat(64),
    }),
    { code: "expedition-byte-pin" },
  );
});

test("the lab runtime contains no expedition transition or scoring implementation", async () => {
  const source = await readFile(new URL("../labs/expedition-lab-runtime.js", import.meta.url), "utf8");
  assert.doesNotMatch(source, /function\s+(step|traverse|confront|survey|recover|treat|extract|withdraw|score|reward)\b/);
  assert.doesNotMatch(source, /Math\.random|crypto\.getRandomValues|Date\s*\(/);
  assert.doesNotMatch(source, /suppliesSpent\s*\+|turns\s*\+|injury\s*\+/);
  assert.doesNotMatch(source, /run\.actions\.length[^\n]*authoredHorizon|authoredHorizon[^\n]*run\.actions\.length/);
});

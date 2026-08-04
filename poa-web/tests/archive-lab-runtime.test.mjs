import assert from "node:assert/strict";
import { execFile as execFileCallback } from "node:child_process";
import { createHash, webcrypto } from "node:crypto";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";
import { test } from "node:test";
import {
  ArchiveLabTransitionRefusal,
  BUILTIN_ARCHIVE_FIXTURE_SHA256,
  BUILTIN_ARCHIVE_PROVENANCE_SHA256,
  BUILTIN_ARCHIVE_SOURCE_COMMIT,
  availableArchiveLabActions,
  canonicalArchiveLabTranscript,
  createArchiveLabRun,
  currentArchiveLabState,
  fetchBuiltinArchiveLabDescriptor,
  loadArchiveLabDescriptor,
  replayArchiveLabActions,
  replayArchiveLabRoute,
  rewindArchiveLabRun,
  submitArchiveLabAction,
  traceArchiveLabRun,
  validateBuiltinArchiveProvenance,
} from "../labs/archive-lab-runtime.js";

const fixtureUrl = new URL("../labs/archive-lab-demonstrator.fixture.json", import.meta.url);
const provenanceUrl = new URL("../labs/archive-lab-demonstrator.provenance.json", import.meta.url);
const repositoryRoot = fileURLToPath(new URL("../../", import.meta.url));
const metatheoryRoot = fileURLToPath(new URL("../../metatheory/", import.meta.url));
const execFile = promisify(execFileCallback);

const fixtureText = () => readFile(fixtureUrl, "utf8");
const fixtureDocument = async () => JSON.parse(await fixtureText());
const provenanceText = () => readFile(provenanceUrl, "utf8");
const provenanceDocument = async () => JSON.parse(await provenanceText());
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

async function descriptor() {
  return loadArchiveLabDescriptor(await fixtureDocument(), {
    url: fixtureUrl.href,
    artifactSha256: BUILTIN_ARCHIVE_FIXTURE_SHA256,
    pinned: true,
  });
}

async function builtinFetch(url) {
  const href = String(url);
  const body = href.includes("provenance") ? await provenanceText() : await fixtureText();
  return { ok: true, status: 200, url: href, async text() { return body; } };
}

test("archive fixture and all three Lean source byte streams are explicitly pinned", async () => {
  const provenance = await provenanceDocument();
  const artifact = await fixtureText();
  assert.equal(Buffer.byteLength(artifact), provenance.artifact.bytes);
  assert.equal(sha256(artifact), provenance.artifact.sha256);
  assert.equal(sha256(await provenanceText()), BUILTIN_ARCHIVE_PROVENANCE_SHA256);
  assert.equal(provenance.artifact.sha256, BUILTIN_ARCHIVE_FIXTURE_SHA256);
  assert.equal(provenance.source_repository_commit, BUILTIN_ARCHIVE_SOURCE_COMMIT);
  for (const source of provenance.generator.sources) {
    const body = await readFile(new URL(`../../${source.path}`, import.meta.url));
    assert.equal(body.byteLength, source.bytes, source.path);
    assert.equal(sha256(body), source.sha256, source.path);
    if (source.binding === "git-tree") assert.match(source.git_blob, /^[0-9a-f]{40}$/);
    else assert.deepEqual({ binding: source.binding, git_blob: source.git_blob }, { binding: "workspace-sha256", git_blob: null });
  }
  assert.deepEqual(provenance.boundary, {
    fiction_status: "beta-only-demonstrator",
    canon_promotion: false,
    asset_minting: false,
    reward_settlement: false,
  });
});

test("archive provenance commit tree binds committed semantics while the new emitter is honestly workspace-pinned", async () => {
  const provenance = await provenanceDocument();
  await execFile("git", ["cat-file", "-e", `${provenance.source_repository_commit}^{commit}`], { cwd: repositoryRoot });
  for (const source of provenance.generator.sources) {
    if (source.binding !== "git-tree") continue;
    const { stdout: treeLine } = await execFile("git", ["ls-tree", provenance.source_repository_commit, "--", source.path], { cwd: repositoryRoot });
    assert.match(treeLine, new RegExp(`^100644 blob ${source.git_blob}\\t${source.path}\\n$`));
    const { stdout: blob } = await execFile("git", ["cat-file", "blob", source.git_blob], { cwd: repositoryRoot, encoding: "buffer", maxBuffer: 1024 * 1024 });
    assert.equal(blob.byteLength, source.bytes, source.path);
    assert.equal(sha256(blob), source.sha256, source.path);
  }
});

test("the Archive Lean emitter regenerates the checked-in finite table byte-for-byte", { timeout: 900_000 }, async (context) => {
  if (process.env.POA_SKIP_LEAN_REGEN === "1") return context.skip("explicitly skipped for the fast local loop");
  let emitted;
  try {
    ({ stdout: emitted } = await execFile(
      "lake",
      ["env", "lean", "--run", "Dregg2/Games/PathOfAngels/ArchiveLabDemonstratorEmit.lean"],
      {
        cwd: metatheoryRoot,
        env: { ...process.env, LEAN_NUM_THREADS: "4" },
        encoding: "utf8",
        maxBuffer: 8 * 1024 * 1024,
        timeout: 890_000,
      },
    ));
  } catch (error) {
    if (error?.code === "ENOENT") return context.skip("lake is unavailable in this environment");
    throw error;
  }
  assert.equal(emitted, await fixtureText());
  assert.equal(sha256(emitted), BUILTIN_ARCHIVE_FIXTURE_SHA256);
});

test("the private built-in loader verifies source, output, identity, exact counts, and the unique route", async () => {
  if (!globalThis.crypto) globalThis.crypto = webcrypto;
  const table = await fetchBuiltinArchiveLabDescriptor(fixtureUrl.href, provenanceUrl.href, { fetchImpl: builtinFetch });
  assert.equal(table.source.trust, "builtin-provenance-verified");
  assert.equal(table.source.pinned, true);
  assert.equal(table.source.artifactSha256, BUILTIN_ARCHIVE_FIXTURE_SHA256);
  assert.equal(table.source.artifactBytes, 3618452);
  assert.equal(table.source.provenance.sourceCommit, BUILTIN_ARCHIVE_SOURCE_COMMIT);
  assert.deepEqual(table.research, {
    missionId: 701,
    artifactId: 900,
    sourceMissionId: 700,
    contentEpoch: 17,
    observationCount: 8,
    hypothesisCount: 4,
    operationBudget: 14,
    winningPlanCount: 1,
  });
  assert.deepEqual(table.referenceRoutes.map(({ id, actions }) => ({ id, actions })), [{
    id: "unique-research-plan",
    actions: [
      "screen-current", "test-current", "screen-current", "test-current",
      "pass-current", "screen-current", "test-current", "screen-current",
      "test-current", "screen-current", "test-current", "pass-current",
      "screen-current", "test-current", "triangulate:0:1", "publish:0",
    ],
  }]);
});

test("public parsing cannot self-assert provenance trust", async () => {
  const document = await fixtureDocument();
  const selfAsserted = loadArchiveLabDescriptor(document, {
    artifactSha256: BUILTIN_ARCHIVE_FIXTURE_SHA256,
    artifactBytes: 3618452,
    pinned: true,
    builtIn: true,
    provenance: await provenanceDocument(),
    provenanceSha256: BUILTIN_ARCHIVE_PROVENANCE_SHA256,
  });
  assert.equal(selfAsserted.source.trust, "untrusted-instrument");
  assert.equal(selfAsserted.source.pinned, false);
  assert.equal(selfAsserted.source.artifactSha256, null);
  assert.equal(selfAsserted.source.provenance, null);
});

test("the raw-byte trusted path refuses a self-consistent mutation before parsing", async () => {
  if (!globalThis.crypto) globalThis.crypto = webcrypto;
  const document = await fixtureDocument();
  const initialRows = document.state_machine.transitions.filter((row) => row.state === document.state_machine.initial_state);
  const screen = initialRows.find((row) => row.action === "screen-current");
  const pass = initialRows.find((row) => row.action === "pass-current");
  [screen.next, pass.next] = [pass.next, screen.next];
  const mutated = JSON.stringify(document);
  const fetchImpl = async (url) => ({
    ok: true, status: 200, url: String(url),
    async text() { return String(url).includes("provenance") ? provenanceText() : mutated; },
  });
  await assert.rejects(fetchBuiltinArchiveLabDescriptor(fixtureUrl.href, provenanceUrl.href, { fetchImpl }), { code: "archive-byte-pin" });
});

test("provenance validation refuses a source-commit self-assertion", async () => {
  const wrong = await provenanceDocument();
  wrong.source_repository_commit = "0".repeat(40);
  assert.throws(() => validateBuiltinArchiveProvenance(wrong, BUILTIN_ARCHIVE_PROVENANCE_SHA256), { code: "archive-provenance-commit" });
});

test("the complete table has exact Cartesian counts, reachability, refusals, and one terminal", async () => {
  const table = await descriptor();
  assert.equal(table.states.length, 822);
  assert.equal(table.actions.length, 8);
  assert.equal(table.transitions.length, 6576);
  assert.equal(table.transitions.filter((row) => row.verdict === "accept").length, 821);
  assert.equal(table.transitions.filter((row) => row.verdict === "refuse").length, 5755);
  assert.equal(table.states.filter((state) => state.terminal).length, 1);
  assert.ok(table.transitions.filter((row) => row.verdict === "refuse").every((row) => row.reason));
  const initialRows = availableArchiveLabActions(table, createArchiveLabRun(table));
  assert.deepEqual(initialRows.filter(({ row }) => row.verdict === "accept").map(({ action }) => action.id), ["screen-current", "pass-current"]);
});

test("the unique route publishes only the literal beta record emitted by Lean", async () => {
  const table = await descriptor();
  const run = replayArchiveLabRoute(table, "unique-research-plan");
  assert.equal(run.terminal, true);
  assert.equal(run.actions.length, 16);
  assert.deepEqual(run.lastRecord, {
    fictionStatus: "beta-only",
    hypothesis: 0,
    artifact: "701:900",
    evidence: [0, 1, 3, 4, 5, 7],
    triangulations: ["0:1"],
    support: 5,
    refutation: 0,
    information: 20,
    operationsSpent: 14,
    canonClaim: false,
    rewardClaim: false,
  });
  assert.equal(currentArchiveLabState(table, run).view.published, 0);
  assert.equal(traceArchiveLabRun(table, run).length, 17);
  assert.match(canonicalArchiveLabTranscript(table, run), /"settlement": "unsettled-local-demonstrator"/);
});

test("contaminated specimens, contradictions, and budget exhaustion are table outcomes rather than browser rules", async () => {
  const table = await descriptor();
  const throughContamination = replayArchiveLabActions(table, [
    "pass-current", "pass-current", "screen-current", "test-current",
  ]);
  const contaminated = currentArchiveLabState(table, throughContamination).view;
  assert.equal(contaminated.observations[2].verdict, "contaminated");
  assert.equal(contaminated.observations[2].weight, 2);
  assert.equal(contaminated.hypotheses[1].support, 0);

  const contradiction = replayArchiveLabActions(table, [
    "pass-current", "pass-current", "pass-current", "pass-current",
    "screen-current", "test-current", "screen-current", "test-current",
  ]);
  assert.deepEqual(currentArchiveLabState(table, contradiction).view.contradictions, [2]);

  const exhausted = replayArchiveLabActions(table, [
    "screen-current", "test-current", "screen-current", "test-current",
    "screen-current", "test-current", "screen-current", "test-current",
    "screen-current", "test-current", "screen-current", "test-current",
    "pass-current", "screen-current", "test-current",
  ]);
  const exhaustedView = currentArchiveLabState(table, exhausted).view;
  assert.equal(exhaustedView.operationsSpent, 14);
  assert.equal(exhaustedView.operationsRemaining, 0);
  assert.throws(() => submitArchiveLabAction(table, exhausted, "triangulate:0:1"), {
    name: "ArchiveLabTransitionRefusal",
    reason: "budget-exhausted",
  });
});

test("refused moves spend nothing, while replay and rewind are transcript-exact", async () => {
  const table = await descriptor();
  const initial = createArchiveLabRun(table);
  assert.throws(() => submitArchiveLabAction(table, initial, "test-current"), ArchiveLabTransitionRefusal);
  assert.equal(initial.actions.length, 0);
  let run = submitArchiveLabAction(table, initial, "screen-current");
  run = submitArchiveLabAction(table, run, "test-current");
  const rewound = rewindArchiveLabRun(table, run);
  assert.deepEqual(rewound.actions, ["screen-current"]);
  assert.deepEqual(replayArchiveLabActions(table, run.actions), run);
});

test("browser runtime contains no deduction or scoring twin", async () => {
  const runtime = await readFile(new URL("../labs/archive-lab-runtime.js", import.meta.url), "utf8");
  const controller = await readFile(new URL("../labs/archive-lab-controller.js", import.meta.url), "utf8");
  for (const source of [runtime, controller]) {
    assert.doesNotMatch(source, /supportScore|refuteScore|informationGain|publishableB|witnessedContradiction|Math\.random|crypto\.getRandomValues/);
  }
  assert.match(runtime, /literal Lean-emitted rows/);
});

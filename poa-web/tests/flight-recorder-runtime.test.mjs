import assert from "node:assert/strict";
import { createHash, webcrypto } from "node:crypto";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  FLIGHT_RECORDER_DEMO_SHA256,
  FlightRecorderRefusal,
  assembleFlightRecorder,
  fetchDemoFlightRecorder,
  fetchLiveFlightRecorder,
  loadConfiguredFlightRecorder,
  parseFlightRecorderConfig,
  parseFlightRecorderStatus,
  parseFlightRecorderTransition,
} from "../labs/flight-recorder-runtime.js";

const fixtureUrl = new URL("../labs/flight-recorder-demo.fixture.json", import.meta.url);
const configUrl = new URL("../labs/flight-recorder.config.json", import.meta.url);
const fixtureText = () => readFile(fixtureUrl, "utf8");
const fixture = async () => JSON.parse(await fixtureText());
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

function liveConfig(maxTransitions = 64) {
  return parseFlightRecorderConfig({
    format: "POA-FLIGHT-RECORDER-CONFIG-1",
    mode: "live",
    api_base_url: "https://node.invalid/",
    authority_id: "ab".repeat(32),
    max_transitions: maxTransitions,
  });
}

test("the visibly labeled demo fixture is raw-byte pinned and forms one exact public chain", async () => {
  const raw = await fixtureText();
  assert.equal(Buffer.byteLength(raw), 4101);
  assert.equal(sha256(raw), FLIGHT_RECORDER_DEMO_SHA256);
  const document = JSON.parse(raw);
  const recorder = assembleFlightRecorder(document.status, document.transitions, {
    kind: "demo-fixture",
    label: document.label,
  });
  assert.equal(recorder.source.kind, "demo-fixture");
  assert.equal(recorder.status.head.transitionCount, 3);
  assert.deepEqual(recorder.transitions.map((transition) => transition.sequence), [1, 2, 3]);
  assert.equal(recorder.hasFullHistory, true);
  assert.equal(recorder.transitions.at(-1).successorHeadDigest, recorder.status.head.headDigest);
  assert.equal(recorder.transitions.at(-1).transitionDigest, recorder.status.head.lastTransitionDigest);
});

test("demo loading requires the exact fixture bytes", async () => {
  if (!globalThis.crypto) globalThis.crypto = webcrypto;
  const raw = await fixtureText();
  const fetchImpl = async (url) => ({ ok: true, status: 200, url: String(url), async text() { return raw; } });
  const recorder = await fetchDemoFlightRecorder(fixtureUrl.href, { fetchImpl });
  assert.equal(recorder.source.kind, "demo-fixture");
  assert.equal(recorder.source.sha256, FLIGHT_RECORDER_DEMO_SHA256);
  await assert.rejects(fetchDemoFlightRecorder(fixtureUrl.href, {
    fetchImpl: async (url) => ({ ok: true, status: 200, url: String(url), async text() { return raw.replace("Crown Relay", "Crown relay"); } }),
  }), { code: "recorder-demo-pin" });
});

test("config chooses one explicit mode and rejects hybrid or attacker-shaped selectors", () => {
  assert.deepEqual(parseFlightRecorderConfig({
    format: "POA-FLIGHT-RECORDER-CONFIG-1",
    mode: "demo",
    api_base_url: null,
    authority_id: null,
    max_transitions: 64,
  }), {
    format: "POA-FLIGHT-RECORDER-CONFIG-1",
    mode: "demo",
    apiBaseUrl: null,
    authorityId: null,
    maxTransitions: 64,
  });
  assert.throws(() => parseFlightRecorderConfig({
    format: "POA-FLIGHT-RECORDER-CONFIG-1",
    mode: "demo",
    api_base_url: "https://attacker.invalid",
    authority_id: "ab".repeat(32),
    max_transitions: 64,
  }), { code: "recorder-config-demo" });
  assert.throws(() => parseFlightRecorderConfig({
    format: "POA-FLIGHT-RECORDER-CONFIG-1",
    mode: "live",
    api_base_url: "javascript:alert(1)",
    authority_id: "ab".repeat(32),
    max_transitions: 64,
  }), { code: "recorder-config-url" });
  assert.throws(() => parseFlightRecorderConfig({
    format: "POA-FLIGHT-RECORDER-CONFIG-1",
    mode: "live",
    api_base_url: "https://user:pass@node.invalid/?source=other",
    authority_id: "ab".repeat(32),
    max_transitions: 64,
  }), { code: "recorder-config-url" });
});

test("status and transition parsers accept only exact committed public API shapes", async () => {
  const document = await fixture();
  const status = parseFlightRecorderStatus(document.status);
  assert.equal(status.authorityId, "ab".repeat(32));
  const transition = parseFlightRecorderTransition(document.transitions[0], status.authorityId);
  assert.equal(transition.sequence, 1);
  assert.equal(transition.consensusFinality, "not_asserted_by_this_view");

  const leakedStatus = structuredClone(document.status);
  leakedStatus.head.canon = { secret: true };
  assert.throws(() => parseFlightRecorderStatus(leakedStatus), { code: "recorder-field" });
  const leakedTransition = structuredClone(document.transitions[0]);
  leakedTransition.judge_input = "private bytes";
  assert.throws(() => parseFlightRecorderTransition(leakedTransition, status.authorityId), { code: "recorder-field" });
  const overstated = structuredClone(document.status);
  overstated.consensus_finality = "finalized";
  assert.throws(() => parseFlightRecorderStatus(overstated), { code: "recorder-finality" });
});

test("gaps and response reordering refuse rather than being repaired in the browser", async () => {
  const document = await fixture();
  assert.throws(
    () => assembleFlightRecorder(document.status, [document.transitions[0], document.transitions[2]]),
    { code: "recorder-gap" },
  );
  assert.throws(
    () => assembleFlightRecorder(document.status, [document.transitions[1], document.transitions[0], document.transitions[2]]),
    { code: "recorder-gap" },
  );
});

test("digest-link, head, last-transition, identity, and commit tampering all fail closed", async () => {
  const document = await fixture();
  const brokenLink = structuredClone(document);
  brokenLink.transitions[1].predecessor_head_digest = "99".repeat(32);
  assert.throws(() => assembleFlightRecorder(brokenLink.status, brokenLink.transitions), { code: "recorder-link" });

  const falseHead = structuredClone(document);
  falseHead.status.head.head_digest = "99".repeat(32);
  assert.throws(() => assembleFlightRecorder(falseHead.status, falseHead.transitions), { code: "recorder-head-link" });

  const falseLast = structuredClone(document);
  falseLast.status.head.last_transition_digest = "99".repeat(32);
  assert.throws(() => assembleFlightRecorder(falseLast.status, falseLast.transitions), { code: "recorder-last-transition" });

  const wrongAuthority = structuredClone(document);
  wrongAuthority.transitions[1].authority_id = "99".repeat(32);
  assert.throws(() => assembleFlightRecorder(wrongAuthority.status, wrongAuthority.transitions), { code: "recorder-authority" });

  const reorderedCommit = structuredClone(document);
  reorderedCommit.transitions[1].commit_ordinal = 100;
  assert.throws(() => assembleFlightRecorder(reorderedCommit.status, reorderedCommit.transitions), { code: "recorder-reorder" });
});

test("stale head observations and false current-head markers refuse", async () => {
  const document = await fixture();
  const stale = structuredClone(document);
  stale.transitions[0].observed_head_transition_count = 2;
  assert.throws(() => assembleFlightRecorder(stale.status, stale.transitions), { code: "recorder-stale" });
  const marker = structuredClone(document);
  marker.transitions[1].is_observed_head_transition = true;
  assert.throws(() => assembleFlightRecorder(marker.status, marker.transitions), { code: "recorder-head-marker" });
});

test("live loading calls only status and canonical transition coordinates and validates a bounded tail", async () => {
  const document = await fixture();
  const calls = [];
  const fetchImpl = async (url) => {
    const href = String(url);
    calls.push(href);
    let body;
    if (href.endsWith("/status")) body = document.status;
    else {
      const sequence = Number(href.split("/").at(-1));
      body = document.transitions[sequence - 1];
    }
    return { ok: true, status: 200, url: href, async text() { return JSON.stringify(body); } };
  };
  const recorder = await fetchLiveFlightRecorder(liveConfig(2), { fetchImpl });
  assert.deepEqual(calls, [
    `https://node.invalid/api/poa/signal/${"ab".repeat(32)}/status`,
    `https://node.invalid/api/poa/signal/${"ab".repeat(32)}/transitions/2`,
    `https://node.invalid/api/poa/signal/${"ab".repeat(32)}/transitions/3`,
  ]);
  assert.deepEqual(recorder.transitions.map((transition) => transition.sequence), [2, 3]);
  assert.equal(recorder.hasFullHistory, false);
  assert.equal(recorder.source.kind, "live-api");
});

test("a configured live source never silently falls back to demo on transport or validation failure", async () => {
  const liveDocument = {
    format: "POA-FLIGHT-RECORDER-CONFIG-1",
    mode: "live",
    api_base_url: "https://node.invalid",
    authority_id: "ab".repeat(32),
    max_transitions: 64,
  };
  const calls = [];
  const fetchImpl = async (url) => {
    const href = String(url);
    calls.push(href);
    if (href === configUrl.href) return { ok: true, status: 200, url: href, async text() { return JSON.stringify(liveDocument); } };
    return { ok: false, status: 503, url: href, async text() { return ""; } };
  };
  await assert.rejects(loadConfiguredFlightRecorder(configUrl.href, fixtureUrl.href, { fetchImpl }), { code: "recorder-status-fetch" });
  assert.equal(calls.includes(fixtureUrl.href), false);
});

test("checked config selects the pinned demo explicitly rather than because live failed", async () => {
  if (!globalThis.crypto) globalThis.crypto = webcrypto;
  const config = await readFile(configUrl, "utf8");
  const demo = await fixtureText();
  const calls = [];
  const fetchImpl = async (url) => {
    const href = String(url);
    calls.push(href);
    return { ok: true, status: 200, url: href, async text() { return href === configUrl.href ? config : demo; } };
  };
  const recorder = await loadConfiguredFlightRecorder(configUrl.href, fixtureUrl.href, { fetchImpl });
  assert.equal(recorder.source.kind, "demo-fixture");
  assert.deepEqual(calls, [configUrl.href, fixtureUrl.href]);
});

test("uninstalled status is a truthful empty recorder, not an invented genesis event", async () => {
  const document = await fixture();
  document.status.installed = false;
  document.status.head = null;
  const recorder = assembleFlightRecorder(document.status, [], { kind: "live-api" });
  assert.equal(recorder.status.installed, false);
  assert.deepEqual(recorder.transitions, []);
  assert.equal(recorder.windowStart, null);
  assert.throws(() => assembleFlightRecorder(document.status, [document.transitions[0]]), { code: "recorder-uninstalled" });
});

test("runtime never implements Signal state semantics or admits forbidden private byte fields", async () => {
  const source = await readFile(new URL("../labs/flight-recorder-runtime.js", import.meta.url), "utf8");
  assert.doesNotMatch(source, /processSignalWire|verifySignalTransition|canonTransition|applyContribution|signalFeedback|Math\.random/);
  assert.doesNotMatch(source, /value\.(canon|config|judge_input|judge_output)(?!_)/);
  assert.match(source, /does not reconstruct Signal semantics/);
});

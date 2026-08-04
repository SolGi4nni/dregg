const STATUS_FORMAT = "POA-SIGNAL-STATUS-1";
const TRANSITION_FORMAT = "POA-SIGNAL-TRANSITION-VIEW-1";
const CONFIG_FORMAT = "POA-FLIGHT-RECORDER-CONFIG-1";
const DEMO_FORMAT = "POA-FLIGHT-RECORDER-DEMO-1";
const VIEW_FINALITY = "not_asserted_by_this_view";
const HEX32 = /^[0-9a-f]{64}$/;

export const FLIGHT_RECORDER_DEMO_SHA256 = "5d06c3a0590ce0b050b694f6d90e8a20ffeaf218769b4f32c0a67dcd09ea3413";

export class FlightRecorderRefusal extends Error {
  constructor(code, message) {
    super(message);
    this.name = "FlightRecorderRefusal";
    this.code = code;
  }
}

function refuse(condition, code, message) {
  if (!condition) throw new FlightRecorderRefusal(code, message);
}

function isObject(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, keys, at) {
  refuse(isObject(value), "recorder-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  refuse(
    actual.length === expected.length && actual.every((key, index) => key === expected[index]),
    "recorder-field",
    `${at} has an unknown or missing field`,
  );
}

function integer(value, min, max, code, at) {
  refuse(Number.isSafeInteger(value) && value >= min && value <= max, code, `${at} is invalid`);
  return value;
}

function digest(value, code, at) {
  refuse(typeof value === "string" && HEX32.test(value), code, `${at} is not a lowercase 32-byte digest`);
  return value;
}

function exactIdentity(value, expected, code, at) {
  const parsed = digest(value, code, at);
  if (expected !== undefined) refuse(parsed === expected, code, `${at} disagrees with the recorder authority`);
  return parsed;
}

function parseHead(value, at) {
  exactKeys(value, [
    "head_digest", "deployment_digest", "transition_count", "world_sequence",
    "canon_revision", "last_transition_digest",
  ], at);
  return Object.freeze({
    headDigest: digest(value.head_digest, "recorder-head", `${at}.head_digest`),
    deploymentDigest: digest(value.deployment_digest, "recorder-head", `${at}.deployment_digest`),
    transitionCount: integer(value.transition_count, 0, Number.MAX_SAFE_INTEGER, "recorder-head", `${at}.transition_count`),
    worldSequence: integer(value.world_sequence, 0, Number.MAX_SAFE_INTEGER, "recorder-head", `${at}.world_sequence`),
    canonRevision: integer(value.canon_revision, 0, Number.MAX_SAFE_INTEGER, "recorder-head", `${at}.canon_revision`),
    lastTransitionDigest: digest(value.last_transition_digest, "recorder-head", `${at}.last_transition_digest`),
  });
}

export function parseFlightRecorderStatus(value) {
  exactKeys(value, ["format", "authority_id", "federation_id", "installed", "head", "consensus_finality"], "status");
  refuse(value.format === STATUS_FORMAT, "recorder-status-format", "status format is unsupported");
  const authorityId = exactIdentity(value.authority_id, undefined, "recorder-authority", "status.authority_id");
  const federationId = exactIdentity(value.federation_id, authorityId, "recorder-authority", "status.federation_id");
  refuse(typeof value.installed === "boolean", "recorder-status", "status.installed is invalid");
  refuse(value.consensus_finality === VIEW_FINALITY, "recorder-finality", "status overstates or changes its finality claim");
  refuse((value.head !== null) === value.installed, "recorder-status", "status head and installed flag disagree");
  return Object.freeze({
    format: value.format,
    authorityId,
    federationId,
    installed: value.installed,
    head: value.head === null ? null : parseHead(value.head, "status.head"),
    consensusFinality: value.consensus_finality,
  });
}

export function parseFlightRecorderTransition(value, authorityId, at = "transition") {
  exactKeys(value, [
    "format", "authority_id", "federation_id", "sequence", "observed_head_transition_count",
    "is_observed_head_transition", "commit_ordinal", "turn_hash", "receipt_hash",
    "predecessor_head_digest", "successor_head_digest", "transition_digest",
    "judge_input_digest", "judge_output_digest", "consensus_finality",
  ], at);
  refuse(value.format === TRANSITION_FORMAT, "recorder-transition-format", `${at}.format is unsupported`);
  refuse(typeof value.is_observed_head_transition === "boolean", "recorder-transition", `${at}.is_observed_head_transition is invalid`);
  refuse(value.consensus_finality === VIEW_FINALITY, "recorder-finality", `${at} overstates or changes its finality claim`);
  return Object.freeze({
    format: value.format,
    authorityId: exactIdentity(value.authority_id, authorityId, "recorder-authority", `${at}.authority_id`),
    federationId: exactIdentity(value.federation_id, authorityId, "recorder-authority", `${at}.federation_id`),
    sequence: integer(value.sequence, 1, Number.MAX_SAFE_INTEGER, "recorder-sequence", `${at}.sequence`),
    observedHeadTransitionCount: integer(value.observed_head_transition_count, 0, Number.MAX_SAFE_INTEGER, "recorder-sequence", `${at}.observed_head_transition_count`),
    isObservedHeadTransition: value.is_observed_head_transition,
    commitOrdinal: integer(value.commit_ordinal, 0, Number.MAX_SAFE_INTEGER, "recorder-commit", `${at}.commit_ordinal`),
    turnHash: digest(value.turn_hash, "recorder-transition", `${at}.turn_hash`),
    receiptHash: digest(value.receipt_hash, "recorder-transition", `${at}.receipt_hash`),
    predecessorHeadDigest: digest(value.predecessor_head_digest, "recorder-transition", `${at}.predecessor_head_digest`),
    successorHeadDigest: digest(value.successor_head_digest, "recorder-transition", `${at}.successor_head_digest`),
    transitionDigest: digest(value.transition_digest, "recorder-transition", `${at}.transition_digest`),
    // These public digests are admitted structurally but never rendered. The
    // API intentionally supplies no judge input/output bytes.
    judgeInputDigest: digest(value.judge_input_digest, "recorder-transition", `${at}.judge_input_digest`),
    judgeOutputDigest: digest(value.judge_output_digest, "recorder-transition", `${at}.judge_output_digest`),
    consensusFinality: value.consensus_finality,
  });
}

function unique(values, code, message) {
  refuse(new Set(values).size === values.length, code, message);
}

/**
 * Validate one complete public replay window. This checks only redacted API
 * coordinates and digest continuity; it does not reconstruct Signal semantics,
 * inspect Canon, or manufacture a consensus-finality certificate.
 */
export function assembleFlightRecorder(statusDocument, transitionDocuments, source = {}) {
  const status = parseFlightRecorderStatus(statusDocument);
  refuse(Array.isArray(transitionDocuments), "recorder-transitions", "transitions must be an array");
  refuse(transitionDocuments.length <= 256, "recorder-window", "transition window exceeds the browser limit");
  if (!status.installed) {
    refuse(transitionDocuments.length === 0, "recorder-uninstalled", "an uninstalled authority cannot expose transitions");
    return Object.freeze({
      status,
      transitions: Object.freeze([]),
      windowStart: null,
      windowEnd: null,
      hasFullHistory: true,
      source: Object.freeze({ ...source }),
    });
  }

  const count = status.head.transitionCount;
  refuse((count === 0) === (transitionDocuments.length === 0), "recorder-window", "transition window is inconsistent with the current head");
  refuse(transitionDocuments.length <= count, "recorder-window", "transition window is longer than the current history");
  const windowStart = count === 0 ? null : count - transitionDocuments.length + 1;
  const transitions = transitionDocuments.map((value, index) => parseFlightRecorderTransition(
    value,
    status.authorityId,
    `transitions[${index}]`,
  ));

  transitions.forEach((transition, index) => {
    const expectedSequence = windowStart + index;
    refuse(transition.sequence === expectedSequence, "recorder-gap", `transition window is gapped or reordered at sequence ${expectedSequence}`);
    refuse(transition.observedHeadTransitionCount === count, "recorder-stale", `transition ${transition.sequence} was observed against a different head`);
    refuse(transition.isObservedHeadTransition === (transition.sequence === count), "recorder-head-marker", `transition ${transition.sequence} has a false current-head marker`);
    if (index > 0) {
      const prior = transitions[index - 1];
      refuse(prior.successorHeadDigest === transition.predecessorHeadDigest, "recorder-link", `digest link breaks between transitions ${prior.sequence} and ${transition.sequence}`);
      refuse(prior.commitOrdinal < transition.commitOrdinal, "recorder-reorder", `commit order does not advance at transition ${transition.sequence}`);
    }
  });
  unique(transitions.map((transition) => transition.transitionDigest), "recorder-duplicate", "transition digest repeats inside the replay window");
  unique(transitions.map((transition) => transition.receiptHash), "recorder-duplicate", "receipt hash repeats inside the replay window");
  if (transitions.length > 0) {
    const finalTransition = transitions.at(-1);
    refuse(finalTransition.successorHeadDigest === status.head.headDigest, "recorder-head-link", "latest successor does not equal the current ship head");
    refuse(finalTransition.transitionDigest === status.head.lastTransitionDigest, "recorder-last-transition", "current head names a different last transition");
  }
  return Object.freeze({
    status,
    transitions: Object.freeze(transitions),
    windowStart,
    windowEnd: count === 0 ? null : count,
    hasFullHistory: windowStart === null || windowStart === 1,
    source: Object.freeze({ ...source }),
  });
}

function parseApiBaseUrl(value, configUrl) {
  refuse(typeof value === "string" && value.length <= 2048, "recorder-config-url", "api_base_url is invalid");
  let parsed;
  try { parsed = new URL(value, configUrl); } catch { throw new FlightRecorderRefusal("recorder-config-url", "api_base_url is invalid"); }
  refuse(parsed.protocol === "http:" || parsed.protocol === "https:", "recorder-config-url", "api_base_url must use HTTP or HTTPS");
  refuse(!parsed.username && !parsed.password && !parsed.search && !parsed.hash, "recorder-config-url", "api_base_url cannot contain credentials, query, or fragment");
  return parsed.href.replace(/\/$/, "");
}

export function parseFlightRecorderConfig(value, configUrl = "https://invalid.local/flight-recorder.config.json") {
  exactKeys(value, ["format", "mode", "api_base_url", "authority_id", "max_transitions"], "config");
  refuse(value.format === CONFIG_FORMAT, "recorder-config-format", "flight recorder config format is unsupported");
  refuse(value.mode === "live" || value.mode === "demo", "recorder-config-mode", "flight recorder mode must be live or demo");
  const maxTransitions = integer(value.max_transitions, 1, 256, "recorder-config-window", "config.max_transitions");
  if (value.mode === "demo") {
    refuse(value.api_base_url === null && value.authority_id === null, "recorder-config-demo", "demo mode cannot carry a live endpoint or authority");
    return Object.freeze({ format: value.format, mode: value.mode, apiBaseUrl: null, authorityId: null, maxTransitions });
  }
  return Object.freeze({
    format: value.format,
    mode: value.mode,
    apiBaseUrl: parseApiBaseUrl(value.api_base_url, configUrl),
    authorityId: exactIdentity(value.authority_id, undefined, "recorder-config-authority", "config.authority_id"),
    maxTransitions,
  });
}

export async function flightRecorderSha256(value) {
  refuse(typeof value === "string", "recorder-sha256", "SHA-256 input must be text");
  refuse(globalThis.crypto?.subtle, "recorder-sha256", "Web Crypto SHA-256 is unavailable");
  const bytes = new TextEncoder().encode(value);
  const output = await globalThis.crypto.subtle.digest("SHA-256", bytes);
  return [...new Uint8Array(output)].map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

async function fetchText(url, options, code) {
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  refuse(typeof fetchImpl === "function", "recorder-fetch", "fetch is unavailable");
  const response = await fetchImpl(url, { cache: "no-store", signal: options.signal });
  refuse(response?.ok, code, `request failed (${response?.status ?? "no response"})`);
  return Object.freeze({ url: response.url || String(url), text: await response.text() });
}

function parseJson(text, code, message) {
  try { return JSON.parse(text); } catch { throw new FlightRecorderRefusal(code, message); }
}

export async function fetchFlightRecorderConfig(url, options = {}) {
  const response = await fetchText(url, options, "recorder-config-fetch");
  return parseFlightRecorderConfig(parseJson(response.text, "recorder-config-json", "flight recorder config is not valid JSON"), response.url);
}

export async function fetchDemoFlightRecorder(url, options = {}) {
  const response = await fetchText(url, options, "recorder-demo-fetch");
  const actualSha256 = await flightRecorderSha256(response.text);
  refuse(actualSha256 === FLIGHT_RECORDER_DEMO_SHA256, "recorder-demo-pin", "demo fixture bytes do not match the compiled pin");
  const value = parseJson(response.text, "recorder-demo-json", "demo fixture is not valid JSON");
  exactKeys(value, ["format", "label", "status", "transitions"], "demo fixture");
  refuse(value.format === DEMO_FORMAT, "recorder-demo-format", "demo fixture format is unsupported");
  refuse(typeof value.label === "string" && value.label.length >= 1 && value.label.length <= 128, "recorder-demo-label", "demo label is invalid");
  return assembleFlightRecorder(value.status, value.transitions, {
    kind: "demo-fixture",
    label: value.label,
    url: response.url,
    sha256: actualSha256,
  });
}

async function fetchJson(url, options, code, message) {
  const response = await fetchText(url, options, code);
  return parseJson(response.text, `${code}-json`, message);
}

export async function fetchLiveFlightRecorder(config, options = {}) {
  refuse(config?.mode === "live", "recorder-config-mode", "live recorder requires a live config");
  const root = `${config.apiBaseUrl}/api/poa/signal/${config.authorityId}`;
  const statusDocument = await fetchJson(`${root}/status`, options, "recorder-status-fetch", "status response is not valid JSON");
  const status = parseFlightRecorderStatus(statusDocument);
  refuse(status.authorityId === config.authorityId, "recorder-authority", "status belongs to another authority");
  if (!status.installed || status.head.transitionCount === 0) {
    return assembleFlightRecorder(statusDocument, [], {
      kind: "live-api",
      apiBaseUrl: config.apiBaseUrl,
      authorityId: config.authorityId,
    });
  }
  const end = status.head.transitionCount;
  const start = Math.max(1, end - config.maxTransitions + 1);
  const transitionDocuments = [];
  for (let sequence = start; sequence <= end; sequence += 8) {
    const batchEnd = Math.min(end, sequence + 7);
    const batch = [];
    for (let item = sequence; item <= batchEnd; item += 1) {
      batch.push(fetchJson(`${root}/transitions/${item}`, options, "recorder-transition-fetch", `transition ${item} response is not valid JSON`));
    }
    transitionDocuments.push(...await Promise.all(batch));
  }
  return assembleFlightRecorder(statusDocument, transitionDocuments, {
    kind: "live-api",
    apiBaseUrl: config.apiBaseUrl,
    authorityId: config.authorityId,
  });
}

/** Config mode is the only selector. There is no query-selected endpoint. */
export async function loadConfiguredFlightRecorder(configUrl, demoUrl, options = {}) {
  const config = await fetchFlightRecorderConfig(configUrl, options);
  if (config.mode === "demo") return fetchDemoFlightRecorder(demoUrl, options);
  return fetchLiveFlightRecorder(config, options);
}

const FORMAT = "POA-ARCHIVE-LAB-TABLE";
const ENGINE_MODULE = "Dregg2.Games.PathOfAngels.ArchiveLab";
const FIXTURE_MODULE = "Dregg2.Games.PathOfAngels.ArchiveLabDemonstrator";
const FICTION_STATUS = "beta-only-demonstrator";
const HEX256 = /^(?:sha256:)?[0-9a-f]{64}$/;
const SHORT_ID = /^[a-z0-9][a-z0-9._:-]{0,127}$/;
const ACTION_TAGS = new Set(["screen", "pass", "test", "triangulate", "publish"]);
const EFFECTS = new Set(["screened", "passed", "tested", "triangulated", "published"]);
const OBSERVATION_STATUSES = new Set(["pending", "screened", "tested", "passed"]);
const BUILTIN_LOAD_CAPABILITY = Symbol("verified built-in archive bytes");

export const BUILTIN_ARCHIVE_FIXTURE_SHA256 = "c3721fe6c03d6d6a5f1184a9c29c4e594c8941def7b3aa1a600ebed623489a27";
export const BUILTIN_ARCHIVE_PROVENANCE_SHA256 = "fdcaeb5b2727c7de36f32c7111034322e600d3b3d10758092e4ea9b91c912a17";
export const BUILTIN_ARCHIVE_SOURCE_COMMIT = "60d7e52215e0cd2ca360e8edf7aa69fbb2499817";

const BUILTIN_SOURCES = Object.freeze([
  Object.freeze({
    path: "metatheory/Dregg2/Games/PathOfAngels/ArchiveLab.lean",
    binding: "git-tree",
    git_blob: "e9f8b94ecb6c461c69f19836c59e1a1f1db867e4",
    sha256: "7f361c3e555805cd806b68de9585a203dd4e7f006d6fe49d5418be16c1c90399",
    bytes: 30446,
  }),
  Object.freeze({
    path: "metatheory/Dregg2/Games/PathOfAngels/ArchiveLabDemonstrator.lean",
    binding: "git-tree",
    git_blob: "3f37d1e5ae0cf27eaef4f55a359b59ec2e3f4234",
    sha256: "357a6d0375986890887e22abbc066877a6c178ff0c86831df9bfc6f9c630530a",
    bytes: 20613,
  }),
  Object.freeze({
    path: "metatheory/Dregg2/Games/PathOfAngels/ArchiveLabDemonstratorEmit.lean",
    binding: "workspace-sha256",
    git_blob: null,
    sha256: "a39853a91c47bf575b6e93a5aaf348f58dceb55e8cba90438db97494fa10153d",
    bytes: 22194,
  }),
]);

const BUILTIN_ROUTE = Object.freeze({
  id: "unique-research-plan",
  actions: Object.freeze([
    "screen-current", "test-current", "screen-current", "test-current",
    "pass-current", "screen-current", "test-current", "screen-current",
    "test-current", "screen-current", "test-current", "pass-current",
    "screen-current", "test-current", "triangulate:0:1", "publish:0",
  ]),
});

export class ArchiveLabArtifactRefusal extends Error {
  constructor(code, message) {
    super(message);
    this.name = "ArchiveLabArtifactRefusal";
    this.code = code;
  }
}

export class ArchiveLabTransitionRefusal extends Error {
  constructor(reason, actionId, stateId) {
    super(`Table-provided archive row refused ${actionId}: ${reason}`);
    this.name = "ArchiveLabTransitionRefusal";
    this.code = "archive-transition-refused";
    this.reason = reason;
    this.actionId = actionId;
    this.stateId = stateId;
  }
}

function refuse(condition, code, message) {
  if (!condition) throw new ArchiveLabArtifactRefusal(code, message);
}

function isObject(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, keys, at) {
  refuse(isObject(value), "archive-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  refuse(
    actual.length === expected.length && actual.every((key, index) => key === expected[index]),
    "archive-field",
    `${at} has an unknown or missing field`,
  );
}

function integer(value, min, max, code, at) {
  refuse(Number.isSafeInteger(value) && value >= min && value <= max, code, `${at} is invalid`);
  return value;
}

function text(value, max, code, at) {
  refuse(typeof value === "string" && value.length >= 1 && value.length <= max, code, `${at} is invalid`);
  return value;
}

function shortId(value, code, at) {
  refuse(typeof value === "string" && SHORT_ID.test(value), code, `${at} is invalid`);
  return value;
}

function unique(values, code, at) {
  refuse(new Set(values).size === values.length, code, `${at} contains a duplicate`);
  return values;
}

function integerArray(value, maxLength, code, at) {
  refuse(Array.isArray(value) && value.length <= maxLength, code, `${at} must be a bounded array`);
  return Object.freeze(unique(value.map((item, index) => integer(
    item, 0, Number.MAX_SAFE_INTEGER, code, `${at}[${index}]`,
  )), code, at));
}

function stringArray(value, maxLength, code, at) {
  refuse(Array.isArray(value) && value.length <= maxLength, code, `${at} must be a bounded array`);
  return Object.freeze(unique(value.map((item, index) => text(
    item, 256, code, `${at}[${index}]`,
  )), code, at));
}

function normalizeSha256(value, at = "sha256") {
  refuse(typeof value === "string" && HEX256.test(value), "archive-sha256", `${at} is invalid`);
  return value.startsWith("sha256:") ? value.slice(7) : value;
}

function exactJson(value, expected, code, message) {
  refuse(JSON.stringify(value) === JSON.stringify(expected), code, message);
}

function parseAuthority(value) {
  exactKeys(value, ["transition", "deduction", "canon_promotion", "asset_minting", "reward_settlement"], "authority");
  refuse(
    value.transition === "lean-table" && value.deduction === "lean-projection" &&
      value.canon_promotion === false && value.asset_minting === false &&
      value.reward_settlement === false,
    "archive-authority",
    "archive authority must remain a Lean projection with no canon, asset, or reward authority",
  );
  return Object.freeze({
    transition: value.transition,
    deduction: value.deduction,
    canonPromotion: value.canon_promotion,
    assetMinting: value.asset_minting,
    rewardSettlement: value.reward_settlement,
  });
}

function parseResearch(value) {
  exactKeys(value, [
    "mission_id", "artifact_id", "source_mission_id", "content_epoch",
    "observation_count", "hypothesis_count", "operation_budget", "winning_plan_count",
  ], "research");
  return Object.freeze({
    missionId: integer(value.mission_id, 0, Number.MAX_SAFE_INTEGER, "archive-research", "research.mission_id"),
    artifactId: integer(value.artifact_id, 0, Number.MAX_SAFE_INTEGER, "archive-research", "research.artifact_id"),
    sourceMissionId: integer(value.source_mission_id, 0, Number.MAX_SAFE_INTEGER, "archive-research", "research.source_mission_id"),
    contentEpoch: integer(value.content_epoch, 0, Number.MAX_SAFE_INTEGER, "archive-research", "research.content_epoch"),
    observationCount: integer(value.observation_count, 1, 256, "archive-research", "research.observation_count"),
    hypothesisCount: integer(value.hypothesis_count, 1, 256, "archive-research", "research.hypothesis_count"),
    operationBudget: integer(value.operation_budget, 1, 4096, "archive-research", "research.operation_budget"),
    winningPlanCount: integer(value.winning_plan_count, 0, 4096, "archive-research", "research.winning_plan_count"),
  });
}

function nullableInteger(value, max, code, at) {
  return value === null ? null : integer(value, 0, max, code, at);
}

function parseBearing(value, hypothesisCount, at) {
  if (value === null) return null;
  exactKeys(value, ["kind", "hypothesis"], at);
  refuse(value.kind === "supports" || value.kind === "refutes", "archive-bearing", `${at}.kind is invalid`);
  return Object.freeze({
    kind: value.kind,
    hypothesis: integer(value.hypothesis, 0, hypothesisCount - 1, "archive-bearing", `${at}.hypothesis`),
  });
}

function parseObservation(value, research, at) {
  exactKeys(value, [
    "id", "label", "status", "artifact_id", "source_mission", "custodian",
    "transfer_sequence", "bearing", "weight", "information", "verdict",
  ], at);
  refuse(OBSERVATION_STATUSES.has(value.status), "archive-observation", `${at}.status is invalid`);
  refuse(typeof value.custodian === "string" && /^[0-9a-f]{64}$/.test(value.custodian), "archive-custody", `${at}.custodian is invalid`);
  refuse(value.verdict === null || value.verdict === "sound" || value.verdict === "contaminated", "archive-verdict", `${at}.verdict is invalid`);
  return Object.freeze({
    id: integer(value.id, 0, research.observationCount - 1, "archive-observation", `${at}.id`),
    label: text(value.label, 256, "archive-observation", `${at}.label`),
    status: value.status,
    artifactId: integer(value.artifact_id, 0, Number.MAX_SAFE_INTEGER, "archive-observation", `${at}.artifact_id`),
    sourceMission: integer(value.source_mission, 0, Number.MAX_SAFE_INTEGER, "archive-observation", `${at}.source_mission`),
    custodian: value.custodian,
    transferSequence: integer(value.transfer_sequence, 0, Number.MAX_SAFE_INTEGER, "archive-custody", `${at}.transfer_sequence`),
    bearing: parseBearing(value.bearing, research.hypothesisCount, `${at}.bearing`),
    weight: nullableInteger(value.weight, 4096, "archive-observation", `${at}.weight`),
    information: nullableInteger(value.information, 4096, "archive-observation", `${at}.information`),
    verdict: value.verdict,
  });
}

function parseHypothesis(value, research, at) {
  exactKeys(value, ["id", "label", "support", "refutation", "contradiction", "publishable"], at);
  refuse(typeof value.contradiction === "boolean" && typeof value.publishable === "boolean", "archive-hypothesis", `${at} flags are invalid`);
  return Object.freeze({
    id: integer(value.id, 0, research.hypothesisCount - 1, "archive-hypothesis", `${at}.id`),
    label: text(value.label, 256, "archive-hypothesis", `${at}.label`),
    support: integer(value.support, 0, 65535, "archive-hypothesis", `${at}.support`),
    refutation: integer(value.refutation, 0, 65535, "archive-hypothesis", `${at}.refutation`),
    contradiction: value.contradiction,
    publishable: value.publishable,
  });
}

function parseView(value, research, terminal, at) {
  exactKeys(value, [
    "cursor", "phase", "current_observation", "operations_spent", "operation_budget",
    "operations_remaining", "screened", "tested", "triangulations", "published",
    "information", "contradictions", "observations", "hypotheses",
  ], at);
  refuse(value.phase === "choose" || value.phase === "screened", "archive-view", `${at}.phase is invalid`);
  refuse(value.operation_budget === research.operationBudget, "archive-view", `${at}.operation_budget disagrees with research`);
  const observations = value.observations;
  refuse(Array.isArray(observations) && observations.length === research.observationCount, "archive-observations", `${at}.observations has the wrong length`);
  const parsedObservations = observations.map((item, index) => parseObservation(item, research, `${at}.observations[${index}]`));
  unique(parsedObservations.map((item) => item.id), "archive-observations", `${at}.observations`);
  const hypotheses = value.hypotheses;
  refuse(Array.isArray(hypotheses) && hypotheses.length === research.hypothesisCount, "archive-hypotheses", `${at}.hypotheses has the wrong length`);
  const parsedHypotheses = hypotheses.map((item, index) => parseHypothesis(item, research, `${at}.hypotheses[${index}]`));
  unique(parsedHypotheses.map((item) => item.id), "archive-hypotheses", `${at}.hypotheses`);
  const published = nullableInteger(value.published, research.hypothesisCount - 1, "archive-view", `${at}.published`);
  refuse(terminal === (published !== null), "archive-terminal-view", `${at}.published disagrees with terminal`);
  return Object.freeze({
    cursor: integer(value.cursor, 0, research.observationCount, "archive-view", `${at}.cursor`),
    phase: value.phase,
    currentObservation: nullableInteger(value.current_observation, research.observationCount - 1, "archive-view", `${at}.current_observation`),
    operationsSpent: integer(value.operations_spent, 0, research.operationBudget, "archive-view", `${at}.operations_spent`),
    operationBudget: value.operation_budget,
    operationsRemaining: integer(value.operations_remaining, 0, research.operationBudget, "archive-view", `${at}.operations_remaining`),
    screened: integerArray(value.screened, research.observationCount, "archive-view", `${at}.screened`),
    tested: integerArray(value.tested, research.observationCount, "archive-view", `${at}.tested`),
    triangulations: stringArray(value.triangulations, 256, "archive-view", `${at}.triangulations`),
    published,
    information: integer(value.information, 0, 65535, "archive-view", `${at}.information`),
    contradictions: integerArray(value.contradictions, research.hypothesisCount, "archive-view", `${at}.contradictions`),
    observations: Object.freeze(parsedObservations),
    hypotheses: Object.freeze(parsedHypotheses),
  });
}

function parseAction(value, research, at) {
  exactKeys(value, ["id", "tag", "label", "hypothesis"], at);
  const tag = shortId(value.tag, "archive-action", `${at}.tag`);
  refuse(ACTION_TAGS.has(tag), "archive-action", `${at}.tag is unknown`);
  return Object.freeze({
    id: text(value.id, 256, "archive-action", `${at}.id`),
    tag,
    label: text(value.label, 256, "archive-action", `${at}.label`),
    hypothesis: nullableInteger(value.hypothesis, research.hypothesisCount - 1, "archive-action", `${at}.hypothesis`),
  });
}

function parseRecord(value, research, at) {
  if (value === null) return null;
  exactKeys(value, [
    "fiction_status", "hypothesis", "artifact", "evidence", "triangulations",
    "support", "refutation", "information", "operations_spent", "canon_claim", "reward_claim",
  ], at);
  refuse(value.fiction_status === "beta-only" && value.canon_claim === false && value.reward_claim === false, "archive-record-boundary", `${at} exceeds beta authority`);
  return Object.freeze({
    fictionStatus: value.fiction_status,
    hypothesis: integer(value.hypothesis, 0, research.hypothesisCount - 1, "archive-record", `${at}.hypothesis`),
    artifact: text(value.artifact, 256, "archive-record", `${at}.artifact`),
    evidence: integerArray(value.evidence, research.observationCount, "archive-record", `${at}.evidence`),
    triangulations: stringArray(value.triangulations, 256, "archive-record", `${at}.triangulations`),
    support: integer(value.support, 0, 65535, "archive-record", `${at}.support`),
    refutation: integer(value.refutation, 0, 65535, "archive-record", `${at}.refutation`),
    information: integer(value.information, 0, 65535, "archive-record", `${at}.information`),
    operationsSpent: integer(value.operations_spent, 0, research.operationBudget, "archive-record", `${at}.operations_spent`),
    canonClaim: value.canon_claim,
    rewardClaim: value.reward_claim,
  });
}

function transitionKey(stateId, actionId) {
  return `${stateId}\u0000${actionId}`;
}

export function validateBuiltinArchiveProvenance(value, provenanceSha256) {
  refuse(normalizeSha256(provenanceSha256, "provenanceSha256") === BUILTIN_ARCHIVE_PROVENANCE_SHA256, "archive-provenance-pin", "built-in provenance bytes do not match the compiled pin");
  exactKeys(value, ["format", "schema_version", "generated_at", "source_repository_commit", "generator", "artifact", "lean_gates", "boundary"], "built-in provenance");
  refuse(value.format === "POA-ARCHIVE-LAB-FIXTURE-PROVENANCE" && value.schema_version === 1, "archive-provenance-format", "built-in provenance format is unsupported");
  refuse(typeof value.generated_at === "string" && /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$/.test(value.generated_at), "archive-provenance-time", "built-in provenance time is invalid");
  refuse(value.source_repository_commit === BUILTIN_ARCHIVE_SOURCE_COMMIT, "archive-provenance-commit", "built-in provenance names the wrong source commit");
  exactKeys(value.generator, ["command", "stdout_is_artifact", "sources"], "built-in provenance.generator");
  refuse(value.generator.command === "cd metatheory && LEAN_NUM_THREADS=4 lake env lean --run Dregg2/Games/PathOfAngels/ArchiveLabDemonstratorEmit.lean" && value.generator.stdout_is_artifact === true, "archive-provenance-generator", "built-in provenance names the wrong Lean generator");
  exactJson(value.generator.sources, BUILTIN_SOURCES, "archive-provenance-sources", "built-in provenance source bytes drifted");
  exactJson(value.artifact, {
    path: "poa-web/labs/archive-lab-demonstrator.fixture.json",
    sha256: BUILTIN_ARCHIVE_FIXTURE_SHA256,
    bytes: 3618452,
    format: FORMAT,
    schema_version: 1,
  }, "archive-provenance-artifact", "built-in provenance artifact output pin drifted");
  exactJson(value.lean_gates, {
    states: 822,
    actions: 8,
    transitions: 6576,
    accepting_rows: 821,
    refusing_rows: 5755,
    terminal_states: 1,
    winning_plans: 1,
    claims: [
      "winning_lab_route_is_exact_archive_lab_play",
      "emitted_winning_route_accepts",
      "emitted_has_exactly_822_reachable_states",
      "emitted_has_exactly_8_actions",
      "emitted_has_exactly_6576_transition_rows",
      "emitted_state_ids_unique",
      "emitted_move_ids_unique",
      "emitted_transition_keys_unique",
      "emitted_table_closed",
      "emitted_refusals_are_explicit",
      "emitted_has_exactly_one_terminal_research_plan",
      "emitted_descriptor_is_json",
    ],
  }, "archive-provenance-gates", "built-in provenance Lean gate inventory drifted");
  exactJson(value.boundary, {
    fiction_status: FICTION_STATUS,
    canon_promotion: false,
    asset_minting: false,
    reward_settlement: false,
  }, "archive-provenance-boundary", "built-in provenance boundary drifted");
  return Object.freeze({
    sha256: BUILTIN_ARCHIVE_PROVENANCE_SHA256,
    sourceCommit: value.source_repository_commit,
    generatedAt: value.generated_at,
    sources: BUILTIN_SOURCES,
    artifact: Object.freeze({ ...value.artifact }),
  });
}

/** Validate and index literal Lean-emitted rows. This never derives a deduction or score. */
function loadArchiveLabDescriptorInternal(document, source = {}, capability = null) {
  exactKeys(document, [
    "format", "schema_version", "engine_module", "fixture_module", "fiction_status",
    "authority", "research", "state_machine", "reference_routes",
  ], "archive descriptor");
  refuse(document.format === FORMAT && document.schema_version === 1, "archive-format", "archive descriptor format is unsupported");
  refuse(document.engine_module === ENGINE_MODULE && document.fixture_module === FIXTURE_MODULE, "archive-module", "archive descriptor names an unsupported Lean module");
  refuse(document.fiction_status === FICTION_STATUS, "archive-fiction", "archive demonstrator must remain beta-only");
  const authority = parseAuthority(document.authority);
  const research = parseResearch(document.research);

  const machine = document.state_machine;
  exactKeys(machine, ["initial_state", "states", "actions", "transitions"], "state_machine");
  const initialState = text(machine.initial_state, 2048, "archive-initial", "state_machine.initial_state");
  refuse(Array.isArray(machine.states) && machine.states.length >= 1 && machine.states.length <= 4096, "archive-states", "state_machine.states is invalid");
  const states = machine.states.map((state, index) => {
    const at = `state_machine.states[${index}]`;
    exactKeys(state, ["id", "terminal", "view"], at);
    const id = text(state.id, 2048, "archive-state", `${at}.id`);
    refuse(typeof state.terminal === "boolean", "archive-state", `${at}.terminal is invalid`);
    return Object.freeze({ id, terminal: state.terminal, view: parseView(state.view, research, state.terminal, `${at}.view`) });
  });
  unique(states.map((state) => state.id), "archive-state-duplicate", "state_machine.states");
  const stateIndex = new Map(states.map((state) => [state.id, state]));
  refuse(stateIndex.has(initialState) && !stateIndex.get(initialState).terminal, "archive-initial", "initial state is absent or terminal");

  refuse(Array.isArray(machine.actions) && machine.actions.length >= 1 && machine.actions.length <= 256, "archive-actions", "state_machine.actions is invalid");
  const actions = machine.actions.map((action, index) => parseAction(action, research, `state_machine.actions[${index}]`));
  unique(actions.map((action) => action.id), "archive-action-duplicate", "state_machine.actions");
  const actionIndex = new Map(actions.map((action) => [action.id, action]));

  const expectedRows = states.length * actions.length;
  refuse(Array.isArray(machine.transitions) && machine.transitions.length === expectedRows, "archive-transition-count", `state_machine.transitions must contain exactly ${expectedRows} rows`);
  const rowIndex = new Map();
  const transitions = machine.transitions.map((row, index) => {
    const at = `state_machine.transitions[${index}]`;
    exactKeys(row, ["state", "action", "verdict", "next", "reason", "effect", "record"], at);
    refuse(row.state === states[Math.floor(index / actions.length)].id && row.action === actions[index % actions.length].id, "archive-transition-order", `${at} is reordered or duplicated`);
    refuse(row.verdict === "accept" || row.verdict === "refuse", "archive-transition-verdict", `${at}.verdict is invalid`);
    let parsed;
    if (row.verdict === "accept") {
      refuse(typeof row.next === "string" && stateIndex.has(row.next), "archive-transition-target", `${at}.next is invalid`);
      refuse(row.reason === null && EFFECTS.has(row.effect), "archive-transition-accept", `${at} has an invalid accepted projection`);
      const record = parseRecord(row.record, research, `${at}.record`);
      refuse((row.effect === "published") === (record !== null), "archive-transition-record", `${at} publication effect and record disagree`);
      parsed = Object.freeze({ state: row.state, action: row.action, verdict: row.verdict, next: row.next, reason: null, effect: row.effect, record });
    } else {
      refuse(row.next === null && row.effect === null && row.record === null && typeof row.reason === "string" && SHORT_ID.test(row.reason), "archive-transition-refusal", `${at} has an invalid refusal projection`);
      parsed = Object.freeze({ state: row.state, action: row.action, verdict: row.verdict, next: null, reason: row.reason, effect: null, record: null });
    }
    rowIndex.set(transitionKey(parsed.state, parsed.action), parsed);
    return parsed;
  });
  refuse(rowIndex.size === expectedRows, "archive-transition-duplicate", "state_machine.transitions contains a duplicate cell");

  for (const state of states) {
    if (!state.terminal) continue;
    for (const action of actions) {
      const row = rowIndex.get(transitionKey(state.id, action.id));
      refuse(row.verdict === "refuse" && row.reason === "terminal", "archive-terminal-row", "terminal state does not explicitly refuse every action as terminal");
    }
  }
  const reachable = new Set([initialState]);
  let grew = true;
  while (grew) {
    grew = false;
    for (const row of transitions) {
      if (row.verdict === "accept" && reachable.has(row.state) && !reachable.has(row.next)) {
        reachable.add(row.next);
        grew = true;
      }
    }
  }
  refuse(reachable.size === states.length, "archive-state-closure", "descriptor contains a state outside its reachable closure");

  refuse(Array.isArray(document.reference_routes) && document.reference_routes.length <= 64, "archive-routes", "reference_routes is invalid");
  const referenceRoutes = document.reference_routes.map((route, index) => {
    const at = `reference_routes[${index}]`;
    exactKeys(route, ["id", "initial_state", "actions"], at);
    const id = shortId(route.id, "archive-route", `${at}.id`);
    refuse(route.initial_state === initialState, "archive-route", `${at}.initial_state disagrees with the machine`);
    refuse(Array.isArray(route.actions) && route.actions.length <= 64, "archive-route", `${at}.actions is invalid`);
    const routeActions = route.actions.map((actionId, actionOffset) => {
      text(actionId, 256, "archive-route", `${at}.actions[${actionOffset}]`);
      refuse(actionIndex.has(actionId), "archive-route", `${at}.actions[${actionOffset}] is unknown`);
      return actionId;
    });
    return Object.freeze({ id, initialState, actions: Object.freeze(routeActions) });
  });
  unique(referenceRoutes.map((route) => route.id), "archive-route-duplicate", "reference_routes");

  const artifactSha256 = source.artifactSha256 === undefined || source.artifactSha256 === null
    ? null
    : normalizeSha256(source.artifactSha256, "source.artifactSha256");
  const builtIn = capability === BUILTIN_LOAD_CAPABILITY;
  let provenance = null;
  if (builtIn) {
    refuse(source.pinned === true && artifactSha256 === BUILTIN_ARCHIVE_FIXTURE_SHA256, "archive-builtin-pin", "built-in fixture requires its exact compiled output pin");
    refuse(source.artifactBytes === 3618452, "archive-builtin-size", "built-in fixture byte length drifted");
    provenance = validateBuiltinArchiveProvenance(source.provenance, source.provenanceSha256);
    refuse(states.length === 822 && actions.length === 8 && transitions.length === 6576, "archive-builtin-counts", "built-in finite table counts drifted");
    refuse(states.filter((state) => state.terminal).length === 1, "archive-builtin-terminal", "built-in table must have exactly one terminal state");
    exactJson(research, {
      missionId: 701,
      artifactId: 900,
      sourceMissionId: 700,
      contentEpoch: 17,
      observationCount: 8,
      hypothesisCount: 4,
      operationBudget: 14,
      winningPlanCount: 1,
    }, "archive-builtin-identity", "built-in research identity drifted");
    exactJson(referenceRoutes.map((route) => ({ id: route.id, actions: route.actions })), [BUILTIN_ROUTE], "archive-builtin-route", "built-in winning route drifted");
  }

  const descriptor = {
    format: document.format,
    schemaVersion: document.schema_version,
    engineModule: document.engine_module,
    fixtureModule: document.fixture_module,
    fictionStatus: document.fiction_status,
    authority,
    research,
    initialState,
    states: Object.freeze(states),
    actions: Object.freeze(actions),
    transitions: Object.freeze(transitions),
    referenceRoutes: Object.freeze(referenceRoutes),
    source: Object.freeze({
      url: source.url ? String(source.url) : null,
      artifactSha256,
      artifactBytes: source.artifactBytes ?? null,
      pinned: Boolean(source.pinned),
      trust: builtIn ? "builtin-provenance-verified" : "untrusted-instrument",
      provenance,
    }),
    stateIndex,
    actionIndex,
    rowIndex,
  };
  for (const route of referenceRoutes) replayArchiveLabRoute(descriptor, route);
  return Object.freeze(descriptor);
}

/** Caller-provided metadata can never authenticate itself and is stripped of trust. */
export function loadArchiveLabDescriptor(document, source = {}) {
  return loadArchiveLabDescriptorInternal(document, {
    url: source.url ? String(source.url) : null,
    artifactSha256: null,
    artifactBytes: null,
    pinned: false,
  });
}

export async function archiveSha256Text(value) {
  refuse(typeof value === "string", "archive-sha256", "sha256 input must be text");
  refuse(globalThis.crypto?.subtle, "archive-sha256", "Web Crypto SHA-256 is unavailable");
  const digest = await globalThis.crypto.subtle.digest("SHA-256", new TextEncoder().encode(value));
  return [...new Uint8Array(digest)].map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

export async function fetchArchiveLabDescriptor(url, options = {}) {
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  refuse(typeof fetchImpl === "function", "archive-fetch", "fetch is unavailable");
  const response = await fetchImpl(url, { cache: "no-store", signal: options.signal });
  refuse(response?.ok, "archive-fetch", `descriptor fetch failed (${response?.status ?? "no response"})`);
  const sourceText = await response.text();
  const artifactSha256 = await archiveSha256Text(sourceText);
  const expected = options.expectedSha256 ? normalizeSha256(options.expectedSha256, "expectedSha256") : null;
  refuse(expected === null || artifactSha256 === expected, "archive-byte-pin", "descriptor bytes do not match the requested SHA-256 pin");
  let document;
  try { document = JSON.parse(sourceText); } catch { throw new ArchiveLabArtifactRefusal("archive-json", "descriptor is not valid JSON"); }
  return loadArchiveLabDescriptorInternal(document, {
    url: response.url || String(url),
    artifactSha256,
    artifactBytes: new TextEncoder().encode(sourceText).byteLength,
    pinned: expected !== null,
  });
}

/** The sole trusted loader: exact provenance bytes plus exact Lean output bytes. */
export async function fetchBuiltinArchiveLabDescriptor(fixtureUrl, provenanceUrl, options = {}) {
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  refuse(typeof fetchImpl === "function", "archive-fetch", "fetch is unavailable");
  const provenanceResponse = await fetchImpl(provenanceUrl, { cache: "no-store", signal: options.signal });
  refuse(provenanceResponse?.ok, "archive-provenance-fetch", `provenance fetch failed (${provenanceResponse?.status ?? "no response"})`);
  const provenanceText = await provenanceResponse.text();
  const provenanceSha256 = await archiveSha256Text(provenanceText);
  refuse(provenanceSha256 === BUILTIN_ARCHIVE_PROVENANCE_SHA256, "archive-provenance-pin", "built-in provenance bytes do not match the compiled pin");
  let provenance;
  try { provenance = JSON.parse(provenanceText); } catch { throw new ArchiveLabArtifactRefusal("archive-provenance-json", "built-in provenance is not valid JSON"); }
  validateBuiltinArchiveProvenance(provenance, provenanceSha256);

  const artifactResponse = await fetchImpl(fixtureUrl, { cache: "no-store", signal: options.signal });
  refuse(artifactResponse?.ok, "archive-fetch", `descriptor fetch failed (${artifactResponse?.status ?? "no response"})`);
  const artifactText = await artifactResponse.text();
  const artifactSha256 = await archiveSha256Text(artifactText);
  refuse(artifactSha256 === BUILTIN_ARCHIVE_FIXTURE_SHA256, "archive-byte-pin", "built-in descriptor bytes do not match the compiled output pin");
  let document;
  try { document = JSON.parse(artifactText); } catch { throw new ArchiveLabArtifactRefusal("archive-json", "built-in descriptor is not valid JSON"); }
  return loadArchiveLabDescriptorInternal(document, {
    url: artifactResponse.url || String(fixtureUrl),
    artifactSha256,
    artifactBytes: new TextEncoder().encode(artifactText).byteLength,
    pinned: true,
    provenance,
    provenanceSha256,
  }, BUILTIN_LOAD_CAPABILITY);
}

function stateFor(descriptor, stateId) {
  const state = descriptor.stateIndex.get(stateId);
  refuse(state, "archive-run-state", "run names a state absent from the provided table");
  return state;
}

function rowFor(descriptor, stateId, actionId) {
  const row = descriptor.rowIndex.get(transitionKey(stateId, actionId));
  refuse(row, "archive-row-missing", "provided table has no row for this state/action pair");
  return row;
}

export function createArchiveLabRun(descriptor) {
  return Object.freeze({
    format: "POA-ARCHIVE-LAB-LOCAL-TRANSCRIPT-V1",
    stateId: descriptor.initialState,
    actions: Object.freeze([]),
    terminal: false,
    lastEffect: null,
    lastRecord: null,
  });
}

export function traceArchiveLabRun(descriptor, run) {
  refuse(isObject(run) && run.format === "POA-ARCHIVE-LAB-LOCAL-TRANSCRIPT-V1", "archive-run", "run format is invalid");
  refuse(Array.isArray(run.actions), "archive-run", "run action list is invalid");
  let stateId = descriptor.initialState;
  let lastEffect = null;
  let lastRecord = null;
  const trace = [{ state: stateFor(descriptor, stateId), action: null, row: null }];
  for (const actionId of run.actions) {
    refuse(descriptor.actionIndex.has(actionId), "archive-run-action", "run contains an unknown action");
    const row = rowFor(descriptor, stateId, actionId);
    refuse(row.verdict === "accept", "archive-run-refusal", "run contains a refused action");
    stateId = row.next;
    lastEffect = row.effect;
    lastRecord = row.record;
    trace.push({ state: stateFor(descriptor, stateId), action: descriptor.actionIndex.get(actionId), row });
  }
  const finalState = stateFor(descriptor, stateId);
  refuse(
    run.stateId === stateId && run.terminal === finalState.terminal && run.lastEffect === lastEffect &&
      JSON.stringify(run.lastRecord) === JSON.stringify(lastRecord),
    "archive-run-drift",
    "run does not replay exactly against the provided table",
  );
  return Object.freeze(trace.map((entry) => Object.freeze(entry)));
}

export function currentArchiveLabState(descriptor, run) {
  traceArchiveLabRun(descriptor, run);
  return stateFor(descriptor, run.stateId);
}

export function availableArchiveLabActions(descriptor, run) {
  traceArchiveLabRun(descriptor, run);
  return Object.freeze(descriptor.actions.map((action) => Object.freeze({
    action,
    row: rowFor(descriptor, run.stateId, action.id),
  })));
}

export function submitArchiveLabAction(descriptor, run, actionId) {
  traceArchiveLabRun(descriptor, run);
  refuse(descriptor.actionIndex.has(actionId), "archive-run-action", "action is absent from the provided action alphabet");
  refuse(!run.terminal, "archive-run-terminal", "terminal run cannot be extended");
  const row = rowFor(descriptor, run.stateId, actionId);
  if (row.verdict === "refuse") throw new ArchiveLabTransitionRefusal(row.reason, actionId, run.stateId);
  const next = stateFor(descriptor, row.next);
  return Object.freeze({
    format: run.format,
    stateId: next.id,
    actions: Object.freeze([...run.actions, actionId]),
    terminal: next.terminal,
    lastEffect: row.effect,
    lastRecord: row.record,
  });
}

export function replayArchiveLabActions(descriptor, actionIds) {
  return actionIds.reduce((run, actionId) => submitArchiveLabAction(descriptor, run, actionId), createArchiveLabRun(descriptor));
}

export function replayArchiveLabRoute(descriptor, routeOrId) {
  const route = typeof routeOrId === "string"
    ? descriptor.referenceRoutes.find((candidate) => candidate.id === routeOrId)
    : routeOrId;
  refuse(route && route.initialState === descriptor.initialState, "archive-route", "reference route is unknown or belongs to another initial state");
  return replayArchiveLabActions(descriptor, route.actions);
}

export function rewindArchiveLabRun(descriptor, run) {
  traceArchiveLabRun(descriptor, run);
  return replayArchiveLabActions(descriptor, run.actions.slice(0, -1));
}

export function canonicalArchiveLabTranscript(descriptor, run) {
  traceArchiveLabRun(descriptor, run);
  return JSON.stringify({
    format: run.format,
    fiction_status: descriptor.fictionStatus,
    settlement: "unsettled-local-demonstrator",
    transition_authority: descriptor.authority.transition,
    source_trust: descriptor.source.trust,
    state: run.stateId,
    terminal: run.terminal,
    actions: run.actions,
    record: run.lastRecord,
  }, null, 2);
}

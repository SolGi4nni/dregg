const FORMAT = "POA-EXPEDITION-TABLE";
const ENGINE_MODULE = "Dregg2.Games.PathOfAngels.DeckExpedition";
const FIXTURE_MODULE = "Dregg2.Games.PathOfAngels.ExpeditionDemonstrator";
const FICTION_STATUS = "non-canon-demonstrator";
const HEX256 = /^(?:sha256:)?[0-9a-f]{64}$/;
const SHORT_ID = /^[a-z0-9][a-z0-9._:-]{0,127}$/;
const ROLES = new Set(["pathfinder", "engineer", "containment", "medic"]);
const ACTION_TAGS = new Set([
  "begin", "traverse", "confront", "survey", "recover", "treat", "extract", "withdraw",
]);
const EFFECTS = new Set(["advanced", "extracted", "withdrawn"]);
const BUILTIN_LOAD_CAPABILITY = Symbol("verified built-in expedition bytes");

export const BUILTIN_FIXTURE_SHA256 = "549c60d1c02be6c6c399020b1872dd4246b95d86a5bcadf21f6982e2ec2155ed";
export const BUILTIN_PROVENANCE_SHA256 = "8452cbafe0a246cc36f85406ffecd63e59479565b096333f89d36c82e6116da2";
export const BUILTIN_SOURCE_COMMIT = "9d4f597c7112f8374379b481f26a7d48af2c35be";

const BUILTIN_SOURCES = Object.freeze([
  Object.freeze({
    path: "metatheory/Dregg2/Games/PathOfAngels/ExpeditionDemonstrator.lean",
    git_blob: "f7f32bbbcfeb8e0e88693fc64ee21803dc4a8c0c",
    sha256: "9ab7bb98aec9d844a648e8ad077db210c57ede0c0fed2a970492a97966876654",
    bytes: 19399,
  }),
  Object.freeze({
    path: "metatheory/Dregg2/Games/PathOfAngels/ExpeditionDemonstratorEmit.lean",
    git_blob: "cb120acdc30bd68884e674a7cecf19325f6539a4",
    sha256: "fc1287c7de55ec5f48def5d6f4b679eb8b4c51be7c97e20893a4f86730bfbb51",
    bytes: 26606,
  }),
]);

const BUILTIN_REFERENCE_ROUTES = Object.freeze([
  Object.freeze({
    id: "safe-beta",
    actions: Object.freeze([
      "traverse:1000", "traverse:1001", "traverse:1002", "survey:4040:1:11",
      "traverse:1003", "traverse:1004", "traverse:1008", "extract",
    ]),
  }),
  Object.freeze({
    id: "salvage-relic",
    actions: Object.freeze([
      "traverse:1000", "traverse:1005", "confront:21:13", "traverse:1006",
      "recover:31:12", "traverse:1007", "traverse:1008", "extract",
    ]),
  }),
]);

export class ExpeditionArtifactRefusal extends Error {
  constructor(code, message) {
    super(message);
    this.name = "ExpeditionArtifactRefusal";
    this.code = code;
  }
}

export class ExpeditionTransitionRefusal extends Error {
  constructor(reason, actionId, stateId) {
    super(`Table-provided expedition row refused ${actionId}: ${reason}`);
    this.name = "ExpeditionTransitionRefusal";
    this.code = "expedition-transition-refused";
    this.reason = reason;
    this.actionId = actionId;
    this.stateId = stateId;
  }
}

function refuse(condition, code, message) {
  if (!condition) throw new ExpeditionArtifactRefusal(code, message);
}

function isObject(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, keys, at) {
  refuse(isObject(value), "expedition-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  refuse(
    actual.length === expected.length && actual.every((key, index) => key === expected[index]),
    "expedition-field",
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

function integerArray(value, max, code, at) {
  refuse(Array.isArray(value) && value.length <= max, code, `${at} must be a bounded array`);
  return Object.freeze(unique(value.map((item, index) => integer(
    item,
    0,
    Number.MAX_SAFE_INTEGER,
    code,
    `${at}[${index}]`,
  )), code, at));
}

function stringArray(value, max, code, at) {
  refuse(Array.isArray(value) && value.length <= max, code, `${at} must be a bounded array`);
  return Object.freeze(unique(value.map((item, index) => text(item, 256, code, `${at}[${index}]`)), code, at));
}

function parseAuthority(value) {
  exactKeys(value, ["transition", "beta_candidates", "canon_promotion", "asset_minting"], "authority");
  refuse(
    value.transition === "lean-table" && value.beta_candidates === "provisional-only" &&
      value.canon_promotion === false && value.asset_minting === false,
    "expedition-authority",
    "the demonstrator must remain a Lean table with provisional-only candidates and no canon or asset authority",
  );
  return Object.freeze({
    transition: value.transition,
    betaCandidates: value.beta_candidates,
    canonPromotion: value.canon_promotion,
    assetMinting: value.asset_minting,
  });
}

function parsePack(value) {
  exactKeys(value, ["id", "activation_counter", "content_epoch", "rooms", "hotspots"], "pack");
  return Object.freeze({
    id: integer(value.id, 0, Number.MAX_SAFE_INTEGER, "expedition-pack", "pack.id"),
    activationCounter: integer(value.activation_counter, 0, Number.MAX_SAFE_INTEGER, "expedition-pack", "pack.activation_counter"),
    contentEpoch: integer(value.content_epoch, 0, Number.MAX_SAFE_INTEGER, "expedition-pack", "pack.content_epoch"),
    rooms: integer(value.rooms, 1, 4096, "expedition-pack", "pack.rooms"),
    hotspots: integer(value.hotspots, 0, 16384, "expedition-pack", "pack.hotspots"),
  });
}

function parseLimits(value) {
  exactKeys(value, ["authored_horizon", "turns", "operational_supplies"], "limits");
  return Object.freeze({
    authoredHorizon: integer(value.authored_horizon, 1, 64, "expedition-limits", "limits.authored_horizon"),
    turns: integer(value.turns, 1, 64, "expedition-limits", "limits.turns"),
    operationalSupplies: integer(value.operational_supplies, 0, 4096, "expedition-limits", "limits.operational_supplies"),
  });
}

function parseOfficer(value, at) {
  exactKeys(value, ["id", "role", "injury", "available"], at);
  const role = shortId(value.role, "expedition-officer", `${at}.role`);
  refuse(ROLES.has(role), "expedition-officer", `${at}.role is unknown`);
  refuse(typeof value.available === "boolean", "expedition-officer", `${at}.available is invalid`);
  return Object.freeze({
    id: integer(value.id, 0, Number.MAX_SAFE_INTEGER, "expedition-officer", `${at}.id`),
    role,
    injury: integer(value.injury, 0, 4096, "expedition-officer", `${at}.injury`),
    available: value.available,
  });
}

function parseSalvage(value, at) {
  exactKeys(value, ["id", "custody"], at);
  return Object.freeze({
    id: integer(value.id, 0, Number.MAX_SAFE_INTEGER, "expedition-salvage", `${at}.id`),
    custody: text(value.custody, 256, "expedition-salvage", `${at}.custody`),
  });
}

function nullableInteger(value, max, code, at) {
  return value === null ? null : integer(value, 0, max, code, at);
}

function nullableArray(value, parser, code, at) {
  if (value === null) return null;
  refuse(Array.isArray(value), code, `${at} must be an array or null`);
  return parser(value, 256, code, at);
}

function parseView(value, terminal, limits, at) {
  exactKeys(value, [
    "status", "room", "phase", "turns", "turn_limit", "supplies_spent", "supply_limit",
    "officers", "visited_rooms", "resolved_hazards", "provisional_candidates", "salvage",
  ], at);
  refuse(
    ["active", "inactive", "inactive-with-secured-salvage"].includes(value.status),
    "expedition-view",
    `${at}.status is unknown`,
  );
  const room = nullableInteger(value.room, Number.MAX_SAFE_INTEGER, "expedition-view", `${at}.room`);
  const phase = nullableInteger(value.phase, Number.MAX_SAFE_INTEGER, "expedition-view", `${at}.phase`);
  const turns = nullableInteger(value.turns, limits.turns, "expedition-view", `${at}.turns`);
  const suppliesSpent = nullableInteger(
    value.supplies_spent,
    limits.operationalSupplies,
    "expedition-view",
    `${at}.supplies_spent`,
  );
  refuse(value.turn_limit === limits.turns, "expedition-view", `${at}.turn_limit disagrees with limits.turns`);
  refuse(
    value.supply_limit === limits.operationalSupplies,
    "expedition-view",
    `${at}.supply_limit disagrees with limits.operational_supplies`,
  );
  if (terminal) {
    refuse(
      value.status !== "active" && room === null && phase === null && turns === null && suppliesSpent === null,
      "expedition-terminal-view",
      `${at} does not describe an inactive terminal projection`,
    );
  } else {
    refuse(
      value.status === "active" && room !== null && phase !== null && turns !== null && suppliesSpent !== null,
      "expedition-active-view",
      `${at} does not describe an active projection`,
    );
  }
  refuse(Array.isArray(value.officers) && value.officers.length >= 1 && value.officers.length <= 64, "expedition-officers", `${at}.officers is invalid`);
  const officers = value.officers.map((officer, index) => parseOfficer(officer, `${at}.officers[${index}]`));
  unique(officers.map((officer) => officer.id), "expedition-officers", `${at}.officers`);
  refuse(Array.isArray(value.salvage) && value.salvage.length <= 256, "expedition-salvage", `${at}.salvage is invalid`);
  const salvage = value.salvage.map((record, index) => parseSalvage(record, `${at}.salvage[${index}]`));
  unique(salvage.map((record) => record.id), "expedition-salvage", `${at}.salvage`);
  return Object.freeze({
    status: value.status,
    room,
    phase,
    turns,
    turnLimit: value.turn_limit,
    suppliesSpent,
    supplyLimit: value.supply_limit,
    officers: Object.freeze(officers),
    visitedRooms: integerArray(value.visited_rooms, 4096, "expedition-visited", `${at}.visited_rooms`),
    resolvedHazards: nullableArray(value.resolved_hazards, integerArray, "expedition-hazards", `${at}.resolved_hazards`),
    provisionalCandidates: nullableArray(value.provisional_candidates, stringArray, "expedition-candidates", `${at}.provisional_candidates`),
    salvage: Object.freeze(salvage),
  });
}

function parseAction(value, at) {
  exactKeys(value, ["id", "tag", "label", "role"], at);
  const id = text(value.id, 256, "expedition-action", `${at}.id`);
  const tag = shortId(value.tag, "expedition-action", `${at}.tag`);
  refuse(ACTION_TAGS.has(tag), "expedition-action", `${at}.tag is unknown`);
  const role = value.role === null ? null : shortId(value.role, "expedition-action", `${at}.role`);
  refuse(role === null || ROLES.has(role), "expedition-action", `${at}.role is unknown`);
  return Object.freeze({ id, tag, label: text(value.label, 256, "expedition-action", `${at}.label`), role });
}

function parseReceipt(value, at) {
  exactKeys(value, [
    "turns", "supplies_spent", "final_room", "recovered_salvage",
    "provisional_candidates", "relic_discoveries",
  ], at);
  return Object.freeze({
    turns: integer(value.turns, 0, 64, "expedition-receipt", `${at}.turns`),
    suppliesSpent: integer(value.supplies_spent, 0, 4096, "expedition-receipt", `${at}.supplies_spent`),
    finalRoom: integer(value.final_room, 0, Number.MAX_SAFE_INTEGER, "expedition-receipt", `${at}.final_room`),
    recoveredSalvage: integerArray(value.recovered_salvage, 256, "expedition-receipt", `${at}.recovered_salvage`),
    provisionalCandidates: stringArray(value.provisional_candidates, 256, "expedition-receipt", `${at}.provisional_candidates`),
    relicDiscoveries: integerArray(value.relic_discoveries, 256, "expedition-receipt", `${at}.relic_discoveries`),
  });
}

function transitionKey(stateId, actionId) {
  return `${stateId}\u0000${actionId}`;
}

function normalizeSha256(value, at = "sha256") {
  refuse(typeof value === "string" && HEX256.test(value), "expedition-sha256", `${at} is invalid`);
  return value.startsWith("sha256:") ? value.slice(7) : value;
}

function exactJson(value, expected, code, message) {
  refuse(JSON.stringify(value) === JSON.stringify(expected), code, message);
}

/** Validate every provenance claim whose bytes are pinned by the lab module. */
export function validateBuiltinProvenance(value, provenanceSha256) {
  refuse(
    normalizeSha256(provenanceSha256, "provenanceSha256") === BUILTIN_PROVENANCE_SHA256,
    "expedition-provenance-pin",
    "built-in provenance bytes do not match the lab's compiled pin",
  );
  exactKeys(value, [
    "format", "schema_version", "generated_at", "source_repository_commit", "generator",
    "artifact", "lean_gates", "boundary",
  ], "built-in provenance");
  refuse(
    value.format === "POA-EXPEDITION-FIXTURE-PROVENANCE" && value.schema_version === 1,
    "expedition-provenance-format",
    "built-in provenance format is unsupported",
  );
  refuse(
    typeof value.generated_at === "string" && /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$/.test(value.generated_at),
    "expedition-provenance-time",
    "built-in provenance generation time is invalid",
  );
  refuse(
    value.source_repository_commit === BUILTIN_SOURCE_COMMIT,
    "expedition-provenance-commit",
    "built-in provenance names the wrong source commit",
  );
  exactKeys(value.generator, ["command", "stdout_is_artifact", "sources"], "built-in provenance.generator");
  refuse(
    value.generator.command === "cd metatheory && LEAN_NUM_THREADS=4 lake env lean --run Dregg2/Games/PathOfAngels/ExpeditionDemonstratorEmit.lean" &&
      value.generator.stdout_is_artifact === true,
    "expedition-provenance-generator",
    "built-in provenance names the wrong Lean generator",
  );
  exactJson(
    value.generator.sources,
    BUILTIN_SOURCES,
    "expedition-provenance-sources",
    "built-in provenance source blob, digest, size, or order drifted",
  );
  exactKeys(value.artifact, ["path", "sha256", "bytes", "format", "schema_version"], "built-in provenance.artifact");
  exactJson(value.artifact, {
    path: "poa-web/labs/expedition-demonstrator.fixture.json",
    sha256: BUILTIN_FIXTURE_SHA256,
    bytes: 294538,
    format: FORMAT,
    schema_version: 1,
  }, "expedition-provenance-artifact", "built-in provenance artifact output pin drifted");
  exactKeys(value.lean_gates, [
    "states", "actions", "transitions", "accepting_rows", "refusing_rows", "claims",
  ], "built-in provenance.lean_gates");
  exactJson(value.lean_gates, {
    states: 53,
    actions: 16,
    transitions: 848,
    accepting_rows: 92,
    refusing_rows: 756,
    claims: [
      "emitted_horizon_is_one_step_closed",
      "emitted_rows_have_explicit_refusals",
      "emitted_rows_need_no_invariant_fallback",
      "emitted_table_closed",
      "emitted_lookup_is_exact_step",
      "emitted_safe_route_replays_exactly",
      "emitted_salvage_route_replays_exactly",
      "emitted_safe_route_returns_beta",
      "emitted_salvage_route_returns_relic",
      "emitted_descriptor_is_json",
    ],
  }, "expedition-provenance-gates", "built-in provenance Lean gate inventory drifted");
  exactKeys(value.boundary, [
    "fiction_status", "beta_candidates", "canon_promotion", "asset_minting", "settlement",
  ], "built-in provenance.boundary");
  exactJson(value.boundary, {
    fiction_status: FICTION_STATUS,
    beta_candidates: "provisional-only",
    canon_promotion: false,
    asset_minting: false,
    settlement: false,
  }, "expedition-provenance-boundary", "built-in provenance boundary drifted");
  return Object.freeze({
    sha256: BUILTIN_PROVENANCE_SHA256,
    sourceCommit: value.source_repository_commit,
    generatedAt: value.generated_at,
    sources: BUILTIN_SOURCES,
    artifact: Object.freeze({ ...value.artifact }),
  });
}

/**
 * Validate and index the exact finite table emitted by Lean. Validation checks
 * schema, Cartesian closure, and literal edge consistency; it never computes a
 * room move, injury, resource spend, custody change, or extraction outcome.
 */
function loadExpeditionDescriptorInternal(document, source = {}, capability = null) {
  exactKeys(document, [
    "format", "schema_version", "engine_module", "fixture_module", "fiction_status",
    "authority", "pack", "player_key", "limits", "state_machine", "reference_routes",
  ], "expedition descriptor");
  refuse(document.format === FORMAT && document.schema_version === 1, "expedition-format", "expedition descriptor format is unsupported");
  refuse(
    document.engine_module === ENGINE_MODULE && document.fixture_module === FIXTURE_MODULE,
    "expedition-module",
    "expedition descriptor names an unsupported Lean module",
  );
  refuse(document.fiction_status === FICTION_STATUS, "expedition-fiction", "expedition fixture must remain explicitly non-canon");
  refuse(typeof document.player_key === "string" && /^[0-9a-f]{64}$/.test(document.player_key), "expedition-player", "player_key is invalid");
  const authority = parseAuthority(document.authority);
  const pack = parsePack(document.pack);
  const limits = parseLimits(document.limits);

  const machine = document.state_machine;
  exactKeys(machine, ["initial_state", "states", "actions", "transitions"], "state_machine");
  const initialState = text(machine.initial_state, 2048, "expedition-initial", "state_machine.initial_state");
  refuse(Array.isArray(machine.states) && machine.states.length >= 1 && machine.states.length <= 4096, "expedition-states", "state_machine.states is invalid");
  const states = machine.states.map((state, index) => {
    const at = `state_machine.states[${index}]`;
    exactKeys(state, ["id", "terminal", "view"], at);
    const id = text(state.id, 2048, "expedition-state", `${at}.id`);
    refuse(typeof state.terminal === "boolean", "expedition-state", `${at}.terminal is invalid`);
    return Object.freeze({ id, terminal: state.terminal, view: parseView(state.view, state.terminal, limits, `${at}.view`) });
  });
  unique(states.map((state) => state.id), "expedition-state-duplicate", "state_machine.states");
  const stateIndex = new Map(states.map((state) => [state.id, state]));
  refuse(stateIndex.has(initialState) && !stateIndex.get(initialState).terminal, "expedition-initial", "initial state is absent or terminal");

  refuse(Array.isArray(machine.actions) && machine.actions.length >= 1 && machine.actions.length <= 256, "expedition-actions", "state_machine.actions is invalid");
  const actions = machine.actions.map((action, index) => parseAction(action, `state_machine.actions[${index}]`));
  unique(actions.map((action) => action.id), "expedition-action-duplicate", "state_machine.actions");
  const actionIndex = new Map(actions.map((action) => [action.id, action]));

  const expectedRows = states.length * actions.length;
  refuse(Array.isArray(machine.transitions) && machine.transitions.length === expectedRows, "expedition-transition-count", `state_machine.transitions must contain exactly ${expectedRows} rows`);
  const rowIndex = new Map();
  const transitions = machine.transitions.map((row, index) => {
    const at = `state_machine.transitions[${index}]`;
    exactKeys(row, ["state", "action", "verdict", "next", "reason", "effect", "receipt"], at);
    const expectedState = states[Math.floor(index / actions.length)].id;
    const expectedAction = actions[index % actions.length].id;
    refuse(row.state === expectedState && row.action === expectedAction, "expedition-transition-order", `${at} is reordered or duplicated`);
    refuse(row.verdict === "accept" || row.verdict === "refuse", "expedition-transition-verdict", `${at}.verdict is invalid`);
    let parsed;
    if (row.verdict === "accept") {
      refuse(typeof row.next === "string" && stateIndex.has(row.next), "expedition-transition-target", `${at}.next is invalid`);
      refuse(row.reason === null && EFFECTS.has(row.effect), "expedition-transition-accept", `${at} has an invalid accepted edge projection`);
      const receipt = row.receipt === null ? null : parseReceipt(row.receipt, `${at}.receipt`);
      refuse((row.effect === "extracted") === (receipt !== null), "expedition-transition-receipt", `${at} extraction effect and receipt disagree`);
      parsed = Object.freeze({ state: row.state, action: row.action, verdict: row.verdict, next: row.next, reason: null, effect: row.effect, receipt });
    } else {
      refuse(
        row.next === null && row.effect === null && row.receipt === null &&
          typeof row.reason === "string" && SHORT_ID.test(row.reason),
        "expedition-transition-refusal",
        `${at} has an invalid refusal projection`,
      );
      parsed = Object.freeze({ state: row.state, action: row.action, verdict: row.verdict, next: null, reason: row.reason, effect: null, receipt: null });
    }
    rowIndex.set(transitionKey(parsed.state, parsed.action), parsed);
    return parsed;
  });
  refuse(rowIndex.size === expectedRows, "expedition-transition-duplicate", "state_machine.transitions contains a duplicate cell");

  for (const state of states) {
    if (!state.terminal) continue;
    for (const action of actions) {
      const row = rowIndex.get(transitionKey(state.id, action.id));
      refuse(row.verdict === "refuse" && row.reason === "terminal", "expedition-terminal-row", "terminal state does not explicitly refuse every action as terminal");
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
  refuse(reachable.size === states.length, "expedition-state-closure", "descriptor contains a state outside the provided reachable closure");

  refuse(Array.isArray(document.reference_routes) && document.reference_routes.length <= 64, "expedition-routes", "reference_routes is invalid");
  const referenceRoutes = document.reference_routes.map((route, index) => {
    const at = `reference_routes[${index}]`;
    exactKeys(route, ["id", "initial_state", "actions"], at);
    const id = shortId(route.id, "expedition-route", `${at}.id`);
    refuse(route.initial_state === initialState, "expedition-route", `${at}.initial_state disagrees with the machine`);
    refuse(Array.isArray(route.actions) && route.actions.length <= limits.authoredHorizon, "expedition-route", `${at}.actions is invalid`);
    const routeActions = route.actions.map((actionId, actionIndexInRoute) => {
      text(actionId, 256, "expedition-route", `${at}.actions[${actionIndexInRoute}]`);
      refuse(actionIndex.has(actionId), "expedition-route", `${at}.actions[${actionIndexInRoute}] is unknown`);
      return actionId;
    });
    return Object.freeze({ id, initialState, actions: Object.freeze(routeActions) });
  });
  unique(referenceRoutes.map((route) => route.id), "expedition-route-duplicate", "reference_routes");

  const artifactSha256 = source.artifactSha256 === undefined || source.artifactSha256 === null
    ? null
    : normalizeSha256(source.artifactSha256, "source.artifactSha256");
  const builtIn = capability === BUILTIN_LOAD_CAPABILITY;
  let provenance = null;
  if (builtIn) {
    refuse(
      source.pinned === true && artifactSha256 === BUILTIN_FIXTURE_SHA256,
      "expedition-builtin-pin",
      "built-in fixture requires its exact compiled artifact SHA-256 pin",
    );
    refuse(source.artifactBytes === 294538, "expedition-builtin-size", "built-in fixture byte length drifted");
    provenance = validateBuiltinProvenance(source.provenance, source.provenanceSha256);
    refuse(
      states.length === 53 && actions.length === 16 && transitions.length === 848,
      "expedition-builtin-counts",
      "built-in fixture must contain exactly 53 states, 16 actions, and 848 transitions",
    );
    exactJson(pack, {
      id: 404,
      activationCounter: 7,
      contentEpoch: 42,
      rooms: 9,
      hotspots: 9,
    }, "expedition-builtin-identity", "built-in pack identity drifted");
    exactJson(limits, {
      authoredHorizon: 8,
      turns: 8,
      operationalSupplies: 3,
    }, "expedition-builtin-identity", "built-in limit identity drifted");
    refuse(document.player_key === "0".repeat(64), "expedition-builtin-identity", "built-in player identity drifted");
    refuse(referenceRoutes.length > 0, "expedition-builtin-routes", "built-in reference routes cannot be empty");
    exactJson(
      referenceRoutes.map((route) => ({ id: route.id, actions: route.actions })),
      BUILTIN_REFERENCE_ROUTES,
      "expedition-builtin-routes",
      "built-in reference route ids, actions, or order drifted",
    );
  }
  const descriptor = {
    format: document.format,
    schemaVersion: document.schema_version,
    engineModule: document.engine_module,
    fixtureModule: document.fixture_module,
    fictionStatus: document.fiction_status,
    authority,
    pack,
    playerKey: document.player_key,
    limits,
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

  // Reference routes are also emitted claims. Confirm only that their literal
  // rows form accepted paths; do not infer why those rows accept.
  for (const route of referenceRoutes) replayExpeditionRoute(descriptor, route);
  return Object.freeze(descriptor);
}

/**
 * Parse a caller-provided document as an untrusted instrument. Parsed metadata
 * cannot authenticate its own bytes and is intentionally stripped of trust.
 */
export function loadExpeditionDescriptor(document, source = {}) {
  return loadExpeditionDescriptorInternal(document, {
    url: source.url ? String(source.url) : null,
    artifactSha256: null,
    artifactBytes: null,
    pinned: false,
  });
}

export async function sha256Text(value) {
  refuse(typeof value === "string", "expedition-sha256", "sha256 input must be text");
  refuse(globalThis.crypto?.subtle, "expedition-sha256", "Web Crypto SHA-256 is unavailable");
  const digest = await globalThis.crypto.subtle.digest("SHA-256", new TextEncoder().encode(value));
  return [...new Uint8Array(digest)].map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

/** Fetch an untrusted instrument descriptor and optionally require an exact byte pin. */
export async function fetchExpeditionDescriptor(url, options = {}) {
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  refuse(typeof fetchImpl === "function", "expedition-fetch", "fetch is unavailable");
  const response = await fetchImpl(url, { cache: "no-store", signal: options.signal });
  refuse(response?.ok, "expedition-fetch", `descriptor fetch failed (${response?.status ?? "no response"})`);
  const sourceText = await response.text();
  const artifactSha256 = await sha256Text(sourceText);
  const artifactBytes = new TextEncoder().encode(sourceText).byteLength;
  const expected = options.expectedSha256 === undefined || options.expectedSha256 === null || options.expectedSha256 === ""
    ? null
    : normalizeSha256(options.expectedSha256, "expectedSha256");
  refuse(expected === null || artifactSha256 === expected, "expedition-byte-pin", "descriptor bytes do not match the requested SHA-256 pin");
  let document;
  try {
    document = JSON.parse(sourceText);
  } catch {
    throw new ExpeditionArtifactRefusal("expedition-json", "descriptor is not valid JSON");
  }
  return loadExpeditionDescriptorInternal(document, {
    url: response.url || String(url),
    artifactSha256,
    artifactBytes,
    pinned: expected !== null,
  });
}

/**
 * Load the one built-in authoritative demonstrator. Both provenance and output
 * bytes are pinned in this module; no query-selected source can enter this path.
 */
export async function fetchBuiltinExpeditionDescriptor(fixtureUrl, provenanceUrl, options = {}) {
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  refuse(typeof fetchImpl === "function", "expedition-fetch", "fetch is unavailable");
  const response = await fetchImpl(provenanceUrl, { cache: "no-store", signal: options.signal });
  refuse(response?.ok, "expedition-provenance-fetch", `provenance fetch failed (${response?.status ?? "no response"})`);
  const provenanceText = await response.text();
  const provenanceSha256 = await sha256Text(provenanceText);
  refuse(
    provenanceSha256 === BUILTIN_PROVENANCE_SHA256,
    "expedition-provenance-pin",
    "built-in provenance bytes do not match the lab's compiled pin",
  );
  let provenance;
  try {
    provenance = JSON.parse(provenanceText);
  } catch {
    throw new ExpeditionArtifactRefusal("expedition-provenance-json", "built-in provenance is not valid JSON");
  }
  validateBuiltinProvenance(provenance, provenanceSha256);
  const artifactResponse = await fetchImpl(fixtureUrl, { cache: "no-store", signal: options.signal });
  refuse(artifactResponse?.ok, "expedition-fetch", `descriptor fetch failed (${artifactResponse?.status ?? "no response"})`);
  const artifactText = await artifactResponse.text();
  const artifactSha256 = await sha256Text(artifactText);
  const artifactBytes = new TextEncoder().encode(artifactText).byteLength;
  refuse(
    artifactSha256 === BUILTIN_FIXTURE_SHA256,
    "expedition-byte-pin",
    "built-in descriptor bytes do not match the lab's compiled output pin",
  );
  let document;
  try {
    document = JSON.parse(artifactText);
  } catch {
    throw new ExpeditionArtifactRefusal("expedition-json", "built-in descriptor is not valid JSON");
  }
  return loadExpeditionDescriptorInternal(document, {
    url: artifactResponse.url || String(fixtureUrl),
    artifactSha256,
    artifactBytes,
    pinned: true,
    provenance,
    provenanceSha256,
  }, BUILTIN_LOAD_CAPABILITY);
}

function stateFor(descriptor, stateId) {
  const state = descriptor.stateIndex.get(stateId);
  refuse(state, "expedition-run-state", "run names a state absent from the provided table");
  return state;
}

function rowFor(descriptor, stateId, actionId) {
  const row = descriptor.rowIndex.get(transitionKey(stateId, actionId));
  refuse(row, "expedition-row-missing", "provided table has no row for this state/action pair");
  return row;
}

export function createExpeditionRun(descriptor) {
  return Object.freeze({
    format: "POA-EXPEDITION-LOCAL-TRANSCRIPT-V1",
    stateId: descriptor.initialState,
    actions: Object.freeze([]),
    terminal: false,
    lastEffect: null,
    lastReceipt: null,
  });
}

export function traceExpeditionRun(descriptor, run) {
  refuse(isObject(run) && run.format === "POA-EXPEDITION-LOCAL-TRANSCRIPT-V1", "expedition-run", "run format is invalid");
  refuse(Array.isArray(run.actions), "expedition-run", "run action list is invalid");
  let stateId = descriptor.initialState;
  let lastEffect = null;
  let lastReceipt = null;
  const trace = [{ state: stateFor(descriptor, stateId), action: null, row: null }];
  for (const actionId of run.actions) {
    refuse(descriptor.actionIndex.has(actionId), "expedition-run-action", "run contains an unknown action");
    const row = rowFor(descriptor, stateId, actionId);
    refuse(row.verdict === "accept", "expedition-run-refusal", "run contains a refused action");
    stateId = row.next;
    lastEffect = row.effect;
    lastReceipt = row.receipt;
    trace.push({ state: stateFor(descriptor, stateId), action: descriptor.actionIndex.get(actionId), row });
  }
  const finalState = stateFor(descriptor, stateId);
  refuse(
    run.stateId === stateId && run.terminal === finalState.terminal &&
      run.lastEffect === lastEffect && JSON.stringify(run.lastReceipt) === JSON.stringify(lastReceipt),
    "expedition-run-drift",
    "run does not replay exactly against the provided table",
  );
  return Object.freeze(trace.map((entry) => Object.freeze(entry)));
}

export function currentExpeditionState(descriptor, run) {
  traceExpeditionRun(descriptor, run);
  return stateFor(descriptor, run.stateId);
}

export function availableExpeditionActions(descriptor, run) {
  traceExpeditionRun(descriptor, run);
  return Object.freeze(descriptor.actions.map((action) => Object.freeze({
    action,
    row: rowFor(descriptor, run.stateId, action.id),
  })));
}

export function submitExpeditionAction(descriptor, run, actionId) {
  traceExpeditionRun(descriptor, run);
  refuse(descriptor.actionIndex.has(actionId), "expedition-run-action", "action is absent from the provided action alphabet");
  refuse(!run.terminal, "expedition-run-terminal", "terminal run cannot be extended");
  const row = rowFor(descriptor, run.stateId, actionId);
  if (row.verdict === "refuse") throw new ExpeditionTransitionRefusal(row.reason, actionId, run.stateId);
  const next = stateFor(descriptor, row.next);
  return Object.freeze({
    format: run.format,
    stateId: next.id,
    actions: Object.freeze([...run.actions, actionId]),
    terminal: next.terminal,
    lastEffect: row.effect,
    lastReceipt: row.receipt,
  });
}

export function replayExpeditionActions(descriptor, actionIds) {
  return actionIds.reduce(
    (run, actionId) => submitExpeditionAction(descriptor, run, actionId),
    createExpeditionRun(descriptor),
  );
}

export function replayExpeditionRoute(descriptor, routeOrId) {
  const route = typeof routeOrId === "string"
    ? descriptor.referenceRoutes.find((candidate) => candidate.id === routeOrId)
    : routeOrId;
  refuse(route && route.initialState === descriptor.initialState, "expedition-route", "reference route is unknown or belongs to another initial state");
  return replayExpeditionActions(descriptor, route.actions);
}

export function rewindExpeditionRun(descriptor, run) {
  traceExpeditionRun(descriptor, run);
  return replayExpeditionActions(descriptor, run.actions.slice(0, -1));
}

export function canonicalExpeditionTranscript(descriptor, run) {
  traceExpeditionRun(descriptor, run);
  return JSON.stringify({
    format: run.format,
    fiction_status: descriptor.fictionStatus,
    settlement: "unsettled-local-demonstrator",
    transition_authority: descriptor.authority.transition,
    engine_module: descriptor.engineModule,
    fixture_module: descriptor.fixtureModule,
    pack_id: descriptor.pack.id,
    content_epoch: descriptor.pack.contentEpoch,
    source_sha256: descriptor.source.artifactSha256,
    source_pinned: descriptor.source.pinned,
    source_trust: descriptor.source.trust,
    actions: run.actions,
    final_state: run.stateId,
    terminal: run.terminal,
    final_effect: run.lastEffect,
    extraction_receipt: run.lastReceipt,
    canon_claim: false,
    reward_claim: false,
  });
}

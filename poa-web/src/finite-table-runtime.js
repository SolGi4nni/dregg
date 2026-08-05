import { ArtifactRefusal } from "./poag1.js";

const FORMAT = "POAG1-GAME";
const SHA256 = /^sha256:[0-9a-f]{64}$/;
const HEX32 = /^[0-9a-f]{64}$/;
const ID = /^[a-z0-9][a-z0-9._:-]{0,95}$/;

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

export function isObject(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

export function exactKeys(value, keys, at) {
  refuse(isObject(value), "table-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  refuse(
    actual.length === expected.length && actual.every((key, index) => key === expected[index]),
    "table-field",
    `${at} has an unknown or missing field`,
  );
}

export function boundedInteger(value, min, max, code, message) {
  refuse(Number.isSafeInteger(value) && value >= min && value <= max, code, message);
  return value;
}

export function identifier(value, code, message) {
  refuse(typeof value === "string" && ID.test(value), code, message);
  return value;
}

/**
 * ⚠ `runSeed` is GONE from the authority envelope. It used to be cross-checked
 * against the descriptor's `run_seed`; both named the live instance, so the check
 * confirmed that two copies of the answer agreed. The live seed is now derived
 * per run and never travels to the client at all.
 */
function validateAuthority(authority, expected) {
  exactKeys(authority, [
    "missionId", "manifestDigest", "activationDigest", "contentEpoch", "curatorCounter",
    "federationId", "contentRoot", "contentSession", "rewardClass",
  ], `${expected.gameId} authenticated authority`);
  boundedInteger(authority.missionId, 0, Number.MAX_SAFE_INTEGER, "table-authority", "missionId is invalid");
  boundedInteger(authority.contentEpoch, 0, Number.MAX_SAFE_INTEGER, "table-authority", "contentEpoch is invalid");
  boundedInteger(authority.curatorCounter, 0, Number.MAX_SAFE_INTEGER, "table-authority", "curatorCounter is invalid");
  refuse(typeof authority.manifestDigest === "string" && SHA256.test(authority.manifestDigest), "table-authority", "manifestDigest is invalid");
  refuse(typeof authority.activationDigest === "string" && SHA256.test(authority.activationDigest), "table-authority", "activationDigest is invalid");
  refuse(typeof authority.contentRoot === "string" && SHA256.test(authority.contentRoot), "table-authority", "contentRoot is invalid");
  for (const field of ["federationId", "contentSession"]) {
    refuse(typeof authority[field] === "string" && HEX32.test(authority[field]), "table-authority", `${field} is invalid`);
  }
  refuse(authority.rewardClass === "non-economic-demo", "table-authority", "dormant table games must be non-economic demos");
  return Object.freeze({ ...authority });
}

/**
 * Fields that named the live instance in the pre-split bundle. A descriptor
 * carrying any of them is the old shape: the instance was derived from a
 * published run seed, so the client could compute the answer before playing.
 * These are REFUSED, not ignored — reinterpreting a stale descriptor as a
 * hidden-instance one would let a leak load quietly.
 */
const BANNED_TOP_LEVEL = Object.freeze({
  run_seed: "determines the instance through the public derivation",
  target: "states the hidden instance outright",
  outcomes: "tabulates the rules against one instance, which is the instance",
});
const BANNED_ACTION_FIELDS = Object.freeze({
  glyph_id: "names the glyph sealed under a plate",
  glyph_label: "names the glyph sealed under a plate",
});
const BANNED_INSTANCE_FIELDS = Object.freeze({
  selected: "names which member of the family is live",
  seed_byte: "names the published byte that draws it",
});

export function refuseStaleShape(game, at) {
  for (const [field, why] of Object.entries(BANNED_TOP_LEVEL)) {
    refuse(!(field in game), "instance-published", `${at} carries \`${field}\`, which ${why}; this is the pre-split POAG1 shape and must be re-emitted from Lean`);
  }
  if (game.instance && typeof game.instance === "object") {
    for (const [field, why] of Object.entries(BANNED_INSTANCE_FIELDS)) {
      refuse(!(field in game.instance), "instance-published", `${at} carries \`instance.${field}\`, which ${why}`);
    }
  }
  const actions = game.state_machine?.actions;
  if (Array.isArray(actions)) {
    for (const action of actions) {
      for (const [field, why] of Object.entries(BANNED_ACTION_FIELDS)) {
        refuse(!(action && field in action), "instance-published", `${at} carries \`state_machine.actions[].${field}\`, which ${why}`);
      }
    }
  }
}

function validateSecurity(value, at, disclosure) {
  exactKeys(value, ["classification", "instance_visibility", "competitive_rewards", "economic_rewards"], at);
  refuse(
    value.classification === "committed-hidden-instance" &&
      value.instance_visibility === disclosure &&
      value.competitive_rewards === false && value.economic_rewards === false,
    "table-security",
    `${at} must declare a committed ${disclosure} instance and zero rewards`,
  );
  return Object.freeze({
    classification: value.classification,
    instanceVisibility: value.instance_visibility,
    competitiveRewards: value.competitive_rewards,
    economicRewards: value.economic_rewards,
  });
}

/**
 * Parse a complete Lean-emitted finite state/action table. `parseView` and
 * `parseAction` only decode literal presentation fields; transition meaning is
 * never recomputed in JavaScript.
 */
export function loadFiniteTableDescriptor(game, authorityInput, spec) {
  // Before any field is read for meaning: is this the pre-split bundle?
  refuseStaleShape(game, `${spec.name} descriptor`);
  exactKeys(game, [
    "format", "schema_version", "game_id", "ruleset", "engine_module", "action_limit",
    "security", "instance", "state_machine", "output", ...(spec.extraKeys ?? []),
  ], `${spec.name} descriptor`);
  refuse(game.format === FORMAT && game.schema_version === 1, "table-format", `${spec.name} format is unsupported`);
  refuse(
    game.game_id === spec.gameId && game.ruleset === spec.ruleset && game.engine_module === spec.engineModule,
    "table-identity",
    `${spec.name} identity is invalid`,
  );
  boundedInteger(game.action_limit, 1, spec.maxActionLimit, "table-action-limit", `${spec.name} action_limit is invalid`);
  refuse(game.action_limit === spec.actionLimit, "table-action-limit", `${spec.name} action_limit disagrees with its Lean ruleset`);
  const authority = validateAuthority(authorityInput, { gameId: spec.gameId });
  const security = validateSecurity(game.security, `${spec.name} security`, spec.disclosure);

  exactKeys(game.output, ["requires", "contribution", "artifact"], `${spec.name} output`);
  refuse(
    game.output.requires === "terminal" && game.output.contribution === "mission_reward" && game.output.artifact === "mission_artifact",
    "table-output",
    `${spec.name} output projection is unsupported`,
  );

  const instance = spec.parseInstance ? spec.parseInstance(game, `${spec.name} instance`) : null;

  const machine = game.state_machine;
  exactKeys(machine, ["initial_state", "states", "actions", "transitions"], `${spec.name} state_machine`);
  identifier(machine.initial_state, "table-initial", `${spec.name} initial_state is invalid`);
  refuse(Array.isArray(machine.states) && machine.states.length > 0 && machine.states.length <= spec.maxStates, "table-states", `${spec.name} state count is invalid`);
  refuse(machine.states.length === spec.stateCount, "table-state-count", `${spec.name} legal-state closure has the wrong size`);
  refuse(Array.isArray(machine.actions) && machine.actions.length > 0 && machine.actions.length <= spec.maxActions, "table-actions", `${spec.name} action count is invalid`);

  const stateIds = new Set();
  const states = machine.states.map((state, index) => {
    exactKeys(state, ["id", "terminal", "view"], `${spec.name} states[${index}]`);
    identifier(state.id, "table-state-id", `${spec.name} states[${index}].id is invalid`);
    refuse(!stateIds.has(state.id), "table-state-duplicate", `${spec.name} state ${state.id} is duplicated`);
    stateIds.add(state.id);
    refuse(typeof state.terminal === "boolean", "table-state-terminal", `${spec.name} state ${state.id}.terminal is invalid`);
    const view = spec.parseView(state.view, game.action_limit, `${spec.name} state ${state.id}.view`);
    refuse(view.solved === state.terminal, "table-state-terminal", `${spec.name} state ${state.id} terminal bit disagrees with its emitted view`);
    return Object.freeze({ id: state.id, terminal: state.terminal, view });
  });
  refuse(stateIds.has(machine.initial_state), "table-initial", `${spec.name} initial_state is absent`);
  refuse(!states.find((state) => state.id === machine.initial_state).terminal, "table-initial", `${spec.name} initial_state cannot be terminal`);

  const actionIds = new Set();
  const actions = machine.actions.map((action, index) => {
    const parsed = spec.parseAction(action, `${spec.name} actions[${index}]`);
    identifier(parsed.id, "table-action-id", `${spec.name} actions[${index}].id is invalid`);
    refuse(!actionIds.has(parsed.id), "table-action-duplicate", `${spec.name} action ${parsed.id} is duplicated`);
    actionIds.add(parsed.id);
    return Object.freeze(parsed);
  });

  const expectedTransitions = states.length * actions.length;
  refuse(
    Array.isArray(machine.transitions) && machine.transitions.length === expectedTransitions,
    "table-transition-count",
    `${spec.name} must emit exactly ${expectedTransitions} state/action transitions`,
  );
  const transitions = machine.transitions.map((transition, index) => {
    exactKeys(transition, ["state", "action", "verdict", "next", "reason"], `${spec.name} transitions[${index}]`);
    const expectedState = states[Math.floor(index / actions.length)].id;
    const expectedAction = actions[index % actions.length].id;
    refuse(transition.state === expectedState && transition.action === expectedAction, "table-transition-order", `${spec.name} transition table is reordered or has a duplicate cell at index ${index}`);
    refuse(transition.verdict === "accept" || transition.verdict === "refuse", "table-transition-verdict", `${spec.name} transition verdict is invalid`);
    if (transition.verdict === "accept") {
      refuse(typeof transition.next === "string" && stateIds.has(transition.next) && transition.reason === null, "table-transition-target", `${spec.name} accepted transition has an invalid target/reason`);
    } else {
      refuse(transition.next === null && typeof transition.reason === "string" && ID.test(transition.reason), "table-transition-refusal", `${spec.name} refused transition has an invalid target/reason`);
      refuse(spec.refusalReasons.includes(transition.reason), "table-transition-refusal", `${spec.name} refused transition has an unknown reason`);
    }
    return Object.freeze({ ...transition });
  });

  const reachable = new Set([machine.initial_state]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const row of transitions) {
      if (reachable.has(row.state) && row.verdict === "accept" && !reachable.has(row.next)) {
        reachable.add(row.next);
        changed = true;
      }
    }
  }
  refuse(reachable.size === states.length, "table-state-closure", `${spec.name} contains a state outside the emitted legal-state closure`);
  for (const state of states) {
    if (!state.terminal) continue;
    const rows = transitions.filter((row) => row.state === state.id);
    refuse(rows.every((row) => row.verdict === "refuse" && row.reason === "solved"), "table-terminal-row", `${spec.name} terminal state must refuse every action as solved`);
  }

  return Object.freeze({
    gameId: game.game_id,
    ruleset: game.ruleset,
    engineModule: game.engine_module,
    actionLimit: game.action_limit,
    security,
    instance,
    authority,
    initialState: machine.initial_state,
    states: Object.freeze(states),
    actions: Object.freeze(actions),
    transitions: Object.freeze(transitions),
  });
}

function stateById(descriptor, stateId) {
  return descriptor.states.find((state) => state.id === stateId);
}

function sameAuthority(run, descriptor) {
  const authority = descriptor.authority;
  return run.gameId === descriptor.gameId &&
    run.missionId === authority.missionId && run.manifestDigest === authority.manifestDigest &&
    run.activationDigest === authority.activationDigest && run.contentEpoch === authority.contentEpoch &&
    run.curatorCounter === authority.curatorCounter && run.federationId === authority.federationId &&
    run.contentRoot === authority.contentRoot && run.contentSession === authority.contentSession &&
    run.security?.classification === descriptor.security.classification &&
    run.security?.instanceVisibility === descriptor.security.instanceVisibility &&
    run.security?.competitiveRewards === descriptor.security.competitiveRewards &&
    run.security?.economicRewards === descriptor.security.economicRewards;
}

const RUN_KEYS = [
  "format", "gameId", "missionId", "manifestDigest", "activationDigest", "contentEpoch",
  "curatorCounter", "federationId", "contentRoot", "contentSession", "mode", "slot",
  "slotCommitment", "stateId", "security", "actions", "terminal",
];

function validateRun(descriptor, run) {
  exactKeys(run, RUN_KEYS, "finite-table transcript");
  exactKeys(run.security, ["classification", "instanceVisibility", "competitiveRewards", "economicRewards"], "finite-table transcript security");
  refuse(run.mode === "practice" || run.mode === "judged", "table-run-mode", "table transcript declares no run mode");
  refuse(run.mode === "practice" ? (run.slot === null && run.slotCommitment === null) : (Number.isSafeInteger(run.slot) && typeof run.slotCommitment === "string"), "table-run-mode", "table transcript mode disagrees with its slot opening");
  refuse(run.format === "POAG1-LOCAL-TABLE-TRANSCRIPT-V1" && sameAuthority(run, descriptor), "table-run-domain", "table transcript belongs to a different authenticated mission");
  refuse(Array.isArray(run.actions) && run.actions.length <= descriptor.actionLimit, "table-run-actions", "table transcript action list is invalid");
  refuse(run.actions.every((action) => descriptor.actions.some((candidate) => candidate.id === action)), "table-run-action", "table transcript contains an unknown action");
  refuse(typeof run.terminal === "boolean", "table-run-terminal", "table transcript terminal bit is invalid");

  let stateId = descriptor.initialState;
  let terminal = false;
  for (const action of run.actions) {
    refuse(!terminal, "table-run-terminal", "table transcript extends a terminal state");
    const row = descriptor.transitions.find((candidate) => candidate.state === stateId && candidate.action === action);
    refuse(row?.verdict === "accept", "table-run-refusal", "table transcript contains a refused action");
    stateId = row.next;
    terminal = stateById(descriptor, stateId).terminal;
  }
  refuse(run.stateId === stateId && run.terminal === terminal, "table-run-drift", "table transcript state does not replay against the authenticated table");
}

/**
 * `opening === null` starts a PRACTICE run: unscored, no slot, no commitment.
 * A judged run needs the curator-signed slot opening it was shown, because that
 * commitment is what the host's answers will be checked against once the slot
 * closes and the secret is opened.
 */
export function createFiniteTableRun(descriptor, opening = null) {
  const authority = descriptor.authority;
  return Object.freeze({
    format: "POAG1-LOCAL-TABLE-TRANSCRIPT-V1",
    gameId: descriptor.gameId,
    missionId: authority.missionId,
    manifestDigest: authority.manifestDigest,
    activationDigest: authority.activationDigest,
    contentEpoch: authority.contentEpoch,
    curatorCounter: authority.curatorCounter,
    federationId: authority.federationId,
    contentRoot: authority.contentRoot,
    contentSession: authority.contentSession,
    mode: opening === null ? "practice" : "judged",
    slot: opening === null ? null : opening.slot,
    slotCommitment: opening === null ? null : opening.commitment,
    security: descriptor.security,
    stateId: descriptor.initialState,
    actions: Object.freeze([]),
    terminal: false,
  });
}

export class TableTransitionRefusal extends Error {
  constructor(reason) {
    super(`Lean-emitted table refused action: ${reason}`);
    this.name = "TableTransitionRefusal";
    this.code = "table-transition-refused";
    this.reason = reason;
  }
}

export function submitFiniteTableAction(descriptor, run, actionId) {
  validateRun(descriptor, run);
  refuse(!run.terminal, "table-run-terminal", "table transcript is already terminal");
  refuse(run.actions.length < descriptor.actionLimit, "table-run-limit", "table transcript reached its authenticated action limit");
  refuse(descriptor.actions.some((action) => action.id === actionId), "table-run-action", "table action is unknown");
  const row = descriptor.transitions.find((transition) => transition.state === run.stateId && transition.action === actionId);
  refuse(row, "table-transition-missing", "authenticated table has no row for this state/action pair");
  if (row.verdict === "refuse") throw new TableTransitionRefusal(row.reason);
  const next = stateById(descriptor, row.next);
  return Object.freeze({
    ...run,
    stateId: next.id,
    actions: Object.freeze([...run.actions, actionId]),
    terminal: next.terminal,
  });
}

export function replayFiniteTable(descriptor, actionIds) {
  return actionIds.reduce((run, actionId) => submitFiniteTableAction(descriptor, run, actionId), createFiniteTableRun(descriptor));
}

export function tableRunView(descriptor, run) {
  validateRun(descriptor, run);
  const state = stateById(descriptor, run.stateId);
  refuse(state, "table-run-state", "table transcript names an unknown state");
  return state.view;
}

export function canonicalTableTranscript(run) {
  return JSON.stringify({
    format: run.format,
    game_id: run.gameId,
    mission_id: run.missionId,
    manifest_digest: run.manifestDigest,
    activation_digest: run.activationDigest,
    content_epoch: run.contentEpoch,
    curator_counter: run.curatorCounter,
    federation_id: run.federationId,
    content_root: run.contentRoot,
    content_session: run.contentSession,
    mode: run.mode,
    slot: run.slot,
    slot_commitment: run.slotCommitment,
    security: run.security,
    actions: run.actions,
    final_state: run.stateId,
    terminal: run.terminal,
    settlement: "unsettled-local-transcript",
  });
}

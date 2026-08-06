import { ArtifactRefusal } from "./poag1.js";
import { loadHiddenInstanceDeclaration, loadSlotOpening, refuseNamedInstance } from "./hidden-instance.js";

/**
 * The shared consumer for Lean-emitted finite state/action tables, after the
 * counter-7 instance/rules split.
 *
 * A pre-split descriptor was one machine over one instance, so holding the
 * machine was holding the answer. A counter-7 descriptor publishes the complete
 * RULE FAMILY and withholds only which member is live, in one of two ways:
 *
 *   A FAMILY OF MACHINES (`state_machine.machines`) — Relay ships all eight
 *     damage boards as eight complete tables. Which board is live is drawn per
 *     run. Its disclosure is `per-run-open`: once the run starts the player is
 *     told the board, because a player who cannot see the prices cannot play.
 *     The commitment is what stops the host choosing the board afterwards.
 *
 *   ONE MACHINE WITH ORACLE ROWS (`verdict: "resolve"`) — Salvage ships one
 *     632-state table in which some rows do not have one successor. Such a row
 *     carries `on_match` and `on_mismatch`, and WHICH of the two is taken
 *     depends on the hidden board. The client cannot know, so it asks and
 *     applies the answer. Its disclosure is `oracle-only`: the board is never
 *     named during the run.
 *
 * Nothing here derives a transition. `submitFiniteTableAction` looks up a row
 * and, if the row defers to the instance, requires an answer to be handed in.
 * The answer's provenance is the caller's business — the host in a judged run, a
 * locally chosen board in practice — and it is recorded in the transcript, so a
 * reader with the opened slot secret can recheck every one of them.
 */

const FORMAT = "POAG1-GAME";
const TRANSCRIPT_FORMAT = "POAG1-LOCAL-TABLE-TRANSCRIPT-V1";
const SHA256 = /^sha256:[0-9a-f]{64}$/;
const HEX32 = /^[0-9a-f]{64}$/;
const ID = /^[a-z0-9][a-z0-9._:-]{0,95}$/;
const RESOLUTIONS = Object.freeze(["match", "mismatch"]);

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
 * only confirmed that two copies of the answer agreed. The live seed is derived
 * per (slot, mission, player) from a curator-held secret and never travels here.
 */
function validateAuthority(authority, expected) {
  exactKeys(authority, [
    "missionId", "manifestDigest", "activationDigest", "contentEpoch", "curatorCounter",
    "federationId", "contentRoot", "contentSession", "rewardClass", "instanceDisclosure",
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
  refuse(
    authority.instanceDisclosure === expected.disclosure,
    "table-authority",
    `the signed catalog declares ${authority.instanceDisclosure} for ${expected.gameId}, not ${expected.disclosure}`,
  );
  return Object.freeze({ ...authority });
}

const BANNED_ACTION_FIELDS = Object.freeze({
  glyph_id: "names the glyph sealed under a plate",
  glyph_label: "names the glyph sealed under a plate",
});

/**
 * Refuse the pre-split shape wherever it could still be hiding: at the top
 * level, inside the instance block, and on every action row.
 */
export function refuseStaleShape(game, at) {
  refuseNamedInstance(game, `${at} descriptor`);
  refuseNamedInstance(game.instance, `${at} instance`);
  const rows = game.state_machine?.actions;
  if (Array.isArray(rows)) {
    for (const action of rows) {
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
 * Parse one complete machine: its states, and one transition row for every
 * state/action pair in row-major order. A missing, reordered or duplicated cell
 * is refused — a partial table is one a client would have to complete itself.
 */
function loadMachine(machine, actions, spec, memberKey, at) {
  refuse(
    Array.isArray(machine.states) && machine.states.length > 0 && machine.states.length <= spec.maxStates,
    "table-states",
    `${at} state count is invalid`,
  );
  refuse(
    spec.stateCount === undefined || machine.states.length === spec.stateCount,
    "table-state-count",
    `${at} legal-state closure has the wrong size`,
  );
  identifier(machine.initial_state, "table-initial", `${at} initial_state is invalid`);

  const stateIds = new Set();
  const states = machine.states.map((state, index) => {
    exactKeys(state, ["id", "terminal", "view"], `${at} states[${index}]`);
    identifier(state.id, "table-state-id", `${at} states[${index}].id is invalid`);
    refuse(!stateIds.has(state.id), "table-state-duplicate", `${at} state ${state.id} is duplicated`);
    stateIds.add(state.id);
    refuse(typeof state.terminal === "boolean", "table-state-terminal", `${at} state ${state.id}.terminal is invalid`);
    const view = spec.parseView(state.view, spec.actionLimit, `${at} state ${state.id}.view`, memberKey);
    refuse(view.solved === state.terminal, "table-state-terminal", `${at} state ${state.id} terminal bit disagrees with its emitted view`);
    return Object.freeze({ id: state.id, terminal: state.terminal, view });
  });
  refuse(stateIds.has(machine.initial_state), "table-initial", `${at} initial_state is absent`);
  refuse(!states.find((state) => state.id === machine.initial_state).terminal, "table-initial", `${at} initial_state cannot be terminal`);

  const expectedTransitions = states.length * actions.length;
  refuse(
    Array.isArray(machine.transitions) && machine.transitions.length === expectedTransitions,
    "table-transition-count",
    `${at} must emit exactly ${expectedTransitions} state/action transitions`,
  );
  const rowKeys = spec.allowsResolve
    ? ["state", "action", "verdict", "next", "reason", "on_match", "on_mismatch"]
    : ["state", "action", "verdict", "next", "reason"];
  const transitions = machine.transitions.map((transition, index) => {
    exactKeys(transition, rowKeys, `${at} transitions[${index}]`);
    const expectedState = states[Math.floor(index / actions.length)].id;
    const expectedAction = actions[index % actions.length].id;
    refuse(
      transition.state === expectedState && transition.action === expectedAction,
      "table-transition-order",
      `${at} transition table is reordered or has a duplicate cell at index ${index}`,
    );
    const branches = spec.allowsResolve;
    if (transition.verdict === "accept") {
      refuse(
        typeof transition.next === "string" && stateIds.has(transition.next) && transition.reason === null &&
          (!branches || (transition.on_match === null && transition.on_mismatch === null)),
        "table-transition-target",
        `${at} accepted transition has an invalid target/reason`,
      );
    } else if (transition.verdict === "refuse") {
      refuse(
        transition.next === null && typeof transition.reason === "string" && ID.test(transition.reason) &&
          (!branches || (transition.on_match === null && transition.on_mismatch === null)),
        "table-transition-refusal",
        `${at} refused transition has an invalid target/reason`,
      );
      refuse(spec.refusalReasons.includes(transition.reason), "table-transition-refusal", `${at} refused transition has an unknown reason`);
    } else if (transition.verdict === "resolve") {
      // A row that defers to the hidden instance. Both branches must be real
      // states: a `resolve` with one dead branch would leak which way it goes.
      refuse(branches, "table-transition-verdict", `${at} emits an oracle row in a table declared free of them`);
      refuse(
        transition.next === null && transition.reason === null &&
          typeof transition.on_match === "string" && stateIds.has(transition.on_match) &&
          typeof transition.on_mismatch === "string" && stateIds.has(transition.on_mismatch),
        "table-transition-oracle",
        `${at} oracle transition does not name two reachable branches`,
      );
      refuse(
        transition.on_match !== transition.on_mismatch,
        "table-transition-oracle",
        `${at} oracle transition sends both answers to one state, so it is not an oracle row`,
      );
    } else {
      refuse(false, "table-transition-verdict", `${at} transition verdict is invalid`);
    }
    return Object.freeze({ ...transition });
  });

  // Reachability treats BOTH oracle branches as reachable: a state only one
  // answer can reach is still a legal state, and dropping it would let a table
  // hide an unreachable-looking region that the live instance walks straight in.
  const reachable = new Set([machine.initial_state]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const row of transitions) {
      if (!reachable.has(row.state)) continue;
      for (const next of [row.next, row.on_match, row.on_mismatch]) {
        if (typeof next === "string" && !reachable.has(next)) {
          reachable.add(next);
          changed = true;
        }
      }
    }
  }
  refuse(reachable.size === states.length, "table-state-closure", `${at} contains a state outside the emitted legal-state closure`);

  for (const state of states) {
    if (!state.terminal) continue;
    const rows = transitions.filter((row) => row.state === state.id);
    refuse(
      rows.every((row) => row.verdict === "refuse" && row.reason === "solved"),
      "table-terminal-row",
      `${at} terminal state must refuse every action as solved`,
    );
  }

  return Object.freeze({
    key: memberKey,
    initialState: machine.initial_state,
    states: Object.freeze(states),
    transitions: Object.freeze(transitions),
  });
}

/**
 * Parse a complete Lean-emitted finite table. `parseView` and `parseAction` only
 * decode literal presentation fields; transition meaning is never recomputed in
 * JavaScript.
 */
export function loadFiniteTableDescriptor(game, authorityInput, spec) {
  // Before any field is read for meaning: is this the pre-split bundle?
  refuseStaleShape(game, spec.name);
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
  const authority = validateAuthority(authorityInput, { gameId: spec.gameId, disclosure: spec.disclosure });
  const security = validateSecurity(game.security, `${spec.name} security`, spec.disclosure);

  exactKeys(game.output, ["requires", "contribution", "artifact"], `${spec.name} output`);
  refuse(
    game.output.requires === "terminal" && game.output.contribution === "mission_reward" && game.output.artifact === "mission_artifact",
    "table-output",
    `${spec.name} output projection is unsupported`,
  );

  const instance = spec.parseInstance(game, `${spec.name} instance`);

  const machine = game.state_machine;
  exactKeys(
    machine,
    spec.familyKeys ? ["initial_state", "actions", "machines"] : ["initial_state", "states", "actions", "transitions"],
    `${spec.name} state_machine`,
  );
  refuse(
    Array.isArray(machine.actions) && machine.actions.length > 0 && machine.actions.length <= spec.maxActions,
    "table-actions",
    `${spec.name} action count is invalid`,
  );

  const actionIds = new Set();
  const actions = machine.actions.map((action, index) => {
    const parsed = spec.parseAction(action, `${spec.name} actions[${index}]`);
    identifier(parsed.id, "table-action-id", `${spec.name} actions[${index}].id is invalid`);
    refuse(!actionIds.has(parsed.id), "table-action-duplicate", `${spec.name} action ${parsed.id} is duplicated`);
    actionIds.add(parsed.id);
    return Object.freeze(parsed);
  });

  let members;
  if (spec.familyKeys) {
    // Every member of the family must be present. A family that ships seven of
    // its eight boards has told the client which board it is not playing.
    const expected = spec.familyKeys(instance);
    refuse(
      Array.isArray(machine.machines) && machine.machines.length === expected.length,
      "table-family-size",
      `${spec.name} must emit one machine per family member (${expected.length})`,
    );
    members = machine.machines.map((entry, index) => {
      exactKeys(entry, ["board", "states", "transitions"], `${spec.name} machines[${index}]`);
      refuse(entry.board === expected[index], "table-family-order", `${spec.name} machines[${index}] is out of family order`);
      return loadMachine(
        { ...entry, initial_state: machine.initial_state },
        actions,
        spec,
        entry.board,
        `${spec.name} machine ${entry.board}`,
      );
    });
  } else {
    members = [loadMachine(machine, actions, spec, null, spec.name)];
  }

  return Object.freeze({
    gameId: game.game_id,
    ruleset: game.ruleset,
    engineModule: game.engine_module,
    actionLimit: game.action_limit,
    disclosure: spec.disclosure,
    security,
    instance,
    authority,
    initialState: machine.initial_state,
    actions: Object.freeze(actions),
    members: Object.freeze(members),
    memberKeys: Object.freeze(members.map((member) => member.key)),
    // A single-member table is played directly; a family is played through the
    // member the run opened. Nothing here picks one.
    hasFamily: Boolean(spec.familyKeys),
  });
}

export function memberOf(descriptor, key) {
  const member = descriptor.members.find((candidate) => candidate.key === key);
  refuse(member, "table-member", "the run names a family member the descriptor does not emit");
  return member;
}

function stateById(member, stateId) {
  return member.states.find((state) => state.id === stateId);
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
  "slotCommitment", "member", "stateId", "security", "steps", "terminal",
];

/**
 * What a run is allowed to know about the instance, by mode and disclosure, and
 * which machine it therefore replays against.
 *
 * `member` means two different things depending on the shape, and conflating
 * them is how a client ends up holding an answer it should not have:
 *
 *   per-run-open (a FAMILY)   `member` selects the machine. It is present in
 *                             both modes, because the board is open by design —
 *                             chosen locally in practice, opened by the host in
 *                             a judged run — and it must be a key the descriptor
 *                             actually emits.
 *
 *   oracle-only (ONE machine) there is one machine and `member` never selects
 *                             it. In practice it records which instance out of
 *                             the emitted practice space this rehearsal answered
 *                             itself from. In a JUDGED run it MUST be null: the
 *                             client is not told, and a transcript carrying it
 *                             would carry the answer the host is answerable for.
 */
function machineFor(descriptor, run) {
  if (descriptor.disclosure === "per-run-open") {
    refuse(run.member !== null, "table-run-member", "a per-run-open run must carry the board it plays");
    return memberOf(descriptor, run.member);
  }
  if (run.mode === "practice") {
    refuse(
      Number.isSafeInteger(run.member) && run.member >= 0,
      "table-run-member",
      "a practice run must name the instance it chose, so its transcript cannot pass as judged",
    );
  } else {
    refuse(run.member === null, "table-run-member", "a judged oracle-only run must not carry the hidden instance");
  }
  return descriptor.members[0];
}

function validateRun(descriptor, run) {
  exactKeys(run, RUN_KEYS, "finite-table transcript");
  exactKeys(run.security, ["classification", "instanceVisibility", "competitiveRewards", "economicRewards"], "finite-table transcript security");
  refuse(run.mode === "practice" || run.mode === "judged", "table-run-mode", "table transcript declares no run mode");
  refuse(
    run.mode === "practice"
      ? (run.slot === null && run.slotCommitment === null)
      : (Number.isSafeInteger(run.slot) && typeof run.slotCommitment === "string" && HEX32.test(run.slotCommitment)),
    "table-run-mode",
    "table transcript mode disagrees with its slot opening",
  );
  refuse(run.format === TRANSCRIPT_FORMAT && sameAuthority(run, descriptor), "table-run-domain", "table transcript belongs to a different authenticated mission");
  refuse(typeof run.terminal === "boolean", "table-run-terminal", "table transcript terminal bit is invalid");
  refuse(Array.isArray(run.steps) && run.steps.length <= descriptor.actionLimit, "table-run-actions", "table transcript step list is invalid");

  // A judged oracle-only run does not know its instance, so it replays against
  // the rows alone: every `resolve` it walked is carried with the answer it was
  // given, and that answer is what a later reader rechecks against the opened
  // secret. This is the only shape in which the client can replay at all.
  const member = machineFor(descriptor, run);
  let stateId = member.initialState;
  let terminal = false;
  for (const step of run.steps) {
    exactKeys(step, ["action", "resolution"], "finite-table transcript step");
    refuse(!terminal, "table-run-terminal", "table transcript extends a terminal state");
    refuse(descriptor.actions.some((candidate) => candidate.id === step.action), "table-run-action", "table transcript contains an unknown action");
    const row = member.transitions.find((candidate) => candidate.state === stateId && candidate.action === step.action);
    refuse(row, "table-transition-missing", "authenticated table has no row for this state/action pair");
    refuse(row.verdict !== "refuse", "table-run-refusal", "table transcript contains a refused action");
    if (row.verdict === "resolve") {
      refuse(RESOLUTIONS.includes(step.resolution), "table-run-oracle", "table transcript walked an oracle row without recording the answer");
      stateId = step.resolution === "match" ? row.on_match : row.on_mismatch;
    } else {
      refuse(step.resolution === null, "table-run-oracle", "table transcript records an oracle answer for a row that has no question");
      stateId = row.next;
    }
    terminal = stateById(member, stateId).terminal;
  }
  refuse(run.stateId === stateId && run.terminal === terminal, "table-run-drift", "table transcript state does not replay against the authenticated table");
  return member;
}

/**
 * Start a run.
 *
 *   PRACTICE  `member` is chosen by the caller out of the emitted family. It is
 *             answerable to nobody and is never scored. It is a structurally
 *             different object from a judged run — `mode` is in the canonical
 *             transcript — so a rehearsal cannot be presented as a result.
 *
 *   JUDGED    needs the curator-signed slot opening the client was shown,
 *             because that commitment is what the host's answers get checked
 *             against once the slot closes and the secret is opened. For an
 *             `oracle-only` game `member` MUST be null: the client is not told.
 */
export function createFiniteTableRun(descriptor, session = {}) {
  const mode = session.mode ?? "practice";
  refuse(mode === "practice" || mode === "judged", "table-run-mode", "a run mode is required");
  const opening = mode === "judged" ? loadSlotOpening(session.opening ?? null, descriptor.authority.missionId) : null;
  const member = session.member === undefined ? null : session.member;
  const run = Object.freeze({
    format: TRANSCRIPT_FORMAT,
    gameId: descriptor.gameId,
    missionId: descriptor.authority.missionId,
    manifestDigest: descriptor.authority.manifestDigest,
    activationDigest: descriptor.authority.activationDigest,
    contentEpoch: descriptor.authority.contentEpoch,
    curatorCounter: descriptor.authority.curatorCounter,
    federationId: descriptor.authority.federationId,
    contentRoot: descriptor.authority.contentRoot,
    contentSession: descriptor.authority.contentSession,
    mode,
    slot: opening === null ? null : opening.slot,
    slotCommitment: opening === null ? null : opening.commitment,
    member,
    security: descriptor.security,
    stateId: descriptor.initialState,
    steps: Object.freeze([]),
    terminal: false,
  });
  validateRun(descriptor, run);
  return run;
}

export class TableTransitionRefusal extends Error {
  constructor(reason) {
    super(`Lean-emitted table refused action: ${reason}`);
    this.name = "TableTransitionRefusal";
    this.code = "table-transition-refused";
    this.reason = reason;
  }
}

/**
 * An oracle row was reached and no answer was supplied. This is not an error in
 * the table; it is the client being asked a question only the instance holder
 * can answer, and it names the two states the answer chooses between.
 */
export class TableOracleQuery extends Error {
  constructor(stateId, actionId, row) {
    super(`the authenticated table defers this action to the hidden instance`);
    this.name = "TableOracleQuery";
    this.code = "table-oracle-required";
    this.stateId = stateId;
    this.actionId = actionId;
    this.onMatch = row.on_match;
    this.onMismatch = row.on_mismatch;
  }
}

/**
 * Dispatch one action. `resolution` is required exactly when the emitted row
 * defers to the hidden instance, and is refused otherwise — a client that could
 * volunteer an answer to a determined row could steer the run.
 */
export function submitFiniteTableAction(descriptor, run, actionId, resolution = null) {
  const member = validateRun(descriptor, run);
  refuse(!run.terminal, "table-run-terminal", "table transcript is already terminal");
  refuse(run.steps.length < descriptor.actionLimit, "table-run-limit", "table transcript reached its authenticated action limit");
  refuse(descriptor.actions.some((action) => action.id === actionId), "table-run-action", "table action is unknown");
  const row = member.transitions.find((transition) => transition.state === run.stateId && transition.action === actionId);
  refuse(row, "table-transition-missing", "authenticated table has no row for this state/action pair");
  if (row.verdict === "refuse") throw new TableTransitionRefusal(row.reason);

  let nextId;
  if (row.verdict === "resolve") {
    if (resolution === null) throw new TableOracleQuery(run.stateId, actionId, row);
    refuse(RESOLUTIONS.includes(resolution), "table-run-oracle", "the oracle returned an answer the table does not offer");
    nextId = resolution === "match" ? row.on_match : row.on_mismatch;
  } else {
    refuse(resolution === null, "table-run-oracle", "an oracle answer was supplied for a row the table already determines");
    nextId = row.next;
  }
  const next = stateById(member, nextId);
  return Object.freeze({
    ...run,
    stateId: next.id,
    steps: Object.freeze([...run.steps, Object.freeze({ action: actionId, resolution: row.verdict === "resolve" ? resolution : null })]),
    terminal: next.terminal,
  });
}

/**
 * Replay a list of steps. `steps` are `{action, resolution}` pairs or bare
 * action ids for tables with no oracle rows.
 */
export function replayFiniteTable(descriptor, session, steps) {
  return steps.reduce((run, step) => {
    const [action, resolution] = typeof step === "string" ? [step, null] : [step.action, step.resolution ?? null];
    return submitFiniteTableAction(descriptor, run, action, resolution);
  }, createFiniteTableRun(descriptor, session));
}

export function tableRunView(descriptor, run) {
  const member = validateRun(descriptor, run);
  const state = stateById(member, run.stateId);
  refuse(state, "table-run-state", "table transcript names an unknown state");
  return state.view;
}

/**
 * `mode` sits next to the format tag, and `member` next to it, so a practice
 * rehearsal and a judged result are different objects at the byte level. A
 * practice transcript also has no slot and no commitment, so there is nothing
 * for a judge to check it against even if somebody relabelled it.
 */
export function canonicalTableTranscript(run) {
  return JSON.stringify({
    format: run.format,
    mode: run.mode,
    member: run.member,
    game_id: run.gameId,
    mission_id: run.missionId,
    manifest_digest: run.manifestDigest,
    activation_digest: run.activationDigest,
    content_epoch: run.contentEpoch,
    curator_counter: run.curatorCounter,
    federation_id: run.federationId,
    content_root: run.contentRoot,
    content_session: run.contentSession,
    slot: run.slot,
    slot_commitment: run.slotCommitment,
    security: run.security,
    steps: run.steps.map((step) => ({ action: step.action, resolution: step.resolution })),
    final_state: run.stateId,
    terminal: run.terminal,
    settlement: "unsettled-local-transcript",
  });
}

export { loadHiddenInstanceDeclaration, loadSlotOpening };

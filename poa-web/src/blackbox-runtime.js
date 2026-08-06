import { ArtifactRefusal } from "./poag1.js";
import { loadHiddenInstanceDeclaration, loadSlotOpening, refuseNamedInstance } from "./hidden-instance.js";

/**
 * Black Box Reconstruction — the PROBE-ORACLE shape.
 *
 * This is the fourth descriptor shape and it is not a state machine. There is no
 * `state_machine` key: what ships is `oracle`, a complete instances-by-probes
 * matrix. Every instance is a row, every probe a column, and the cell is the
 * answer that instance gives that probe. Holding the whole matrix tells you
 * every rule and singles out no instance, which is what makes it publishable.
 *
 * ⚠ WHAT THIS DESCRIPTOR DOES NOT CARRY, and what that costs.
 *
 * It states an `action_limit` and a `refusals` vocabulary — `repeated-probe`,
 * `settled-slot`, `settled-fragment` — but NO transition rows and no predicate
 * saying when each fires. The machine shapes (Relay, Salvage) emit a total table
 * and a client dispatches rows out of it; here there is nothing to dispatch.
 *
 * So this client does NOT enforce those refusals, and must not: writing "a probe
 * whose slot is already settled is refused" in JavaScript is authoring a rule,
 * which is the drift this repo pays for over and over. What it does instead:
 *
 *   - decodes and checks the oracle completely (that part IS fully specified),
 *   - answers a PRACTICE probe by one lookup into an emitted row,
 *   - applies the class a JUDGED host returns, and applies a REFUSAL the host
 *     returns, checked against the emitted vocabulary,
 *   - counts settled probes against the emitted `required_per_instance`.
 *
 * A practice run is therefore permissive where a judged run is not — a rehearsal
 * can spend probes the real rules would have refused. That is a real gap and the
 * fix is on the Lean side: emit the refusal predicate, or emit this game the way
 * Salvage is emitted, as a total table with oracle rows. Recorded rather than
 * papered over, because a JavaScript reimplementation would look like a feature.
 */

const FORMAT = "POAG1-GAME";
const TRANSCRIPT_FORMAT = "POAG1-LOCAL-PROBE-TRANSCRIPT-V1";
const ENGINE = "Dregg2.Games.PathOfAngels.BlackBoxReconstruction";
const ID = /^[a-z0-9][a-z0-9._:-]{0,95}$/;
const REFUSALS = Object.freeze(["solved", "turn-limit", "repeated-probe", "settled-slot", "settled-fragment"]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}
function object(value) { return value !== null && typeof value === "object" && !Array.isArray(value); }
function exactKeys(value, keys, at) {
  refuse(object(value), "oracle-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  refuse(actual.length === expected.length && actual.every((key, index) => key === expected[index]), "oracle-field", `${at} has an unknown or missing field`);
}
function integer(value, min, max) { return Number.isSafeInteger(value) && value >= min && value <= max; }
function exactArray(value, expected, at) {
  refuse(
    Array.isArray(value) && value.length === expected.length && value.every((item, index) => item === expected[index]),
    "oracle-constant",
    `${at} does not match the POAG1 contract`,
  );
}

/**
 * Decode the oracle. Every check here is on emitted data against emitted claims;
 * none of it reconstructs the game.
 */
function loadOracle(block, actionLimit, at) {
  exactKeys(block, [
    "instance_space", "instance_shape", "required_per_instance", "settles",
    "class_alphabet", "classes", "probes", "table",
  ], at);
  refuse(integer(block.instance_space, 2, 100_000), "oracle-space", `${at}.instance_space is invalid`);
  refuse(typeof block.instance_shape === "string" && block.instance_shape.length > 0, "oracle-space", `${at}.instance_shape is absent`);
  refuse(block.settles === "slot-and-fragment", "oracle-settles", `${at} declares an unsupported settlement`);

  // Classes. Exactly one solving class, as in every other POAG1 oracle.
  refuse(Array.isArray(block.classes) && block.classes.length >= 2 && block.classes.length <= 64, "oracle-class", `${at}.classes is invalid`);
  const classes = block.classes.map((row, index) => {
    exactKeys(row, ["id", "solving"], `${at}.classes[${index}]`);
    refuse(typeof row.id === "string" && ID.test(row.id), "oracle-class", `${at}.classes[${index}].id is invalid`);
    refuse(typeof row.solving === "boolean", "oracle-class", `${at}.classes[${index}].solving is invalid`);
    return Object.freeze({ id: row.id, solving: row.solving });
  });
  refuse(new Set(classes.map((row) => row.id)).size === classes.length, "oracle-class", `${at}.classes repeats a class id`);
  const solvingIds = classes.flatMap((row, index) => (row.solving ? [index] : []));
  refuse(solvingIds.length === 1, "oracle-class", `${at} must declare exactly one settling class`);
  const solvingClassId = solvingIds[0];

  // ⚠ Decode through the declared alphabet. Hard-coding '1' would work today and
  // silently mean something else the first time the alphabet grows.
  const alphabet = block.class_alphabet;
  refuse(typeof alphabet === "string" && alphabet.length >= classes.length, "oracle-alphabet", `${at}.class_alphabet is too short`);
  const charId = new Map([...alphabet.slice(0, classes.length)].map((char, index) => [char, index]));
  refuse(charId.size === classes.length, "oracle-alphabet", `${at}.class_alphabet repeats a character`);

  // Probes: the action domain, slot-major.
  refuse(Array.isArray(block.probes) && block.probes.length > 0 && block.probes.length <= 4096, "oracle-probes", `${at}.probes is invalid`);
  const probeIds = new Set();
  const probes = block.probes.map((probe, index) => {
    exactKeys(probe, ["id", "label", "slot", "fragment"], `${at}.probes[${index}]`);
    refuse(typeof probe.id === "string" && ID.test(probe.id), "oracle-probes", `${at}.probes[${index}].id is invalid`);
    refuse(typeof probe.label === "string" && probe.label.length > 0 && probe.label.length <= 128, "oracle-probes", `${at}.probes[${index}].label is invalid`);
    refuse(integer(probe.slot, 0, 4095) && integer(probe.fragment, 0, 4095), "oracle-probes", `${at}.probes[${index}} coordinates are invalid`);
    refuse(!probeIds.has(probe.id), "oracle-probes", `${at}.probes contains ${probe.id} twice`);
    probeIds.add(probe.id);
    return Object.freeze({ index, id: probe.id, label: probe.label, slot: probe.slot, fragment: probe.fragment });
  });
  const slots = new Set(probes.map((probe) => probe.slot));
  const fragments = new Set(probes.map((probe) => probe.fragment));
  // The probe list must be the COMPLETE grid. A missing cell is a question the
  // player cannot ask, which narrows the instance space without saying so.
  refuse(
    probes.length === slots.size * fragments.size,
    "oracle-probes",
    `${at}.probes is not the complete ${slots.size}x${fragments.size} probe grid`,
  );
  refuse(
    probes.every((probe, index) => probe.index === index && probe.slot === Math.floor(index / fragments.size)),
    "oracle-probes",
    `${at}.probes is not in slot-major order`,
  );
  refuse(integer(block.required_per_instance, 1, slots.size), "oracle-required", `${at}.required_per_instance is invalid`);

  // The matrix. One row per instance, one cell per probe.
  refuse(Array.isArray(block.table) && block.table.length === block.instance_space, "oracle-table", `${at}.table must have one row per instance`);
  const seen = new Set();
  const table = block.table.map((row, index) => {
    refuse(typeof row === "string" && row.length === probes.length, "oracle-table", `${at}.table[${index}] is not one cell per probe`);
    const decoded = new Uint8Array(probes.length);
    let settling = 0;
    const settledSlots = new Set();
    for (let column = 0; column < probes.length; column += 1) {
      const id = charId.get(row[column]);
      refuse(id !== undefined, "oracle-table", `${at}.table[${index}] names a class outside the declared alphabet`);
      decoded[column] = id;
      if (id !== solvingClassId) continue;
      settling += 1;
      settledSlots.add(probes[column].slot);
    }
    // Every row must settle exactly the declared number, one per slot. A row
    // that settled a different number would be a distinguishable instance —
    // findable from the published matrix alone, before playing.
    refuse(
      settling === block.required_per_instance && settledSlots.size === settling,
      "oracle-table",
      `${at}.table[${index}] settles ${settling} probes over ${settledSlots.size} slots, not ${block.required_per_instance} over ${block.required_per_instance}`,
    );
    refuse(!seen.has(row), "oracle-table", `${at}.table[${index}] repeats an earlier row, so the instance space is smaller than it claims`);
    seen.add(row);
    return decoded;
  });

  return Object.freeze({
    instanceSpace: block.instance_space,
    instanceShape: block.instance_shape,
    requiredPerInstance: block.required_per_instance,
    settles: block.settles,
    classes: Object.freeze(classes),
    solvingClassId,
    probes: Object.freeze(probes),
    slotCount: slots.size,
    fragmentCount: fragments.size,
    table: Object.freeze(table),
    actionLimit,
  });
}

/** Decode Black Box Reconstruction's authenticated Lean-emitted oracle. */
export function loadBlackBoxDescriptor(game, mission) {
  refuseNamedInstance(game, "Black Box descriptor");
  refuseNamedInstance(game.instance, "Black Box descriptor instance");
  exactKeys(game, [
    "format", "schema_version", "game_id", "ruleset", "engine_module", "action_limit",
    "security", "instance", "oracle", "refusals", "output",
  ], "Black Box descriptor");
  refuse(game.format === FORMAT && game.schema_version === 1, "blackbox-format", "unsupported Black Box descriptor");
  refuse(
    game.game_id === "black-box-reconstruction" && game.ruleset === "blackbox-v2" && game.engine_module === ENGINE,
    "blackbox-identity",
    "Black Box descriptor identity is invalid",
  );
  refuse(integer(game.action_limit, 1, 256), "blackbox-action-limit", "Black Box action_limit is invalid");
  refuse(game.action_limit === mission.actionLimit, "blackbox-action-limit", "descriptor and catalog action limits disagree");

  exactKeys(game.security, ["classification", "instance_visibility", "competitive_rewards", "economic_rewards"], "Black Box security");
  refuse(
    game.security.classification === "committed-hidden-instance" &&
      game.security.instance_visibility === mission.instanceDisclosure &&
      game.security.instance_visibility === "oracle-only" &&
      game.security.competitive_rewards === false && game.security.economic_rewards === false,
    "blackbox-security",
    "Black Box must remain a committed, oracle-only, zero-reward demo",
  );
  const declaration = loadHiddenInstanceDeclaration(game.instance, mission.instanceDisclosure, "Black Box descriptor instance");

  exactArray(game.refusals, REFUSALS, "Black Box refusals");
  exactKeys(game.output, ["requires", "contribution", "artifact"], "Black Box output");
  refuse(
    game.output.requires === "terminal" && game.output.contribution === "mission_reward" && game.output.artifact === "mission_artifact",
    "blackbox-output",
    "Black Box output projection is unsupported",
  );

  const oracle = loadOracle(game.oracle, game.action_limit, "Black Box oracle");
  return Object.freeze({
    gameId: game.game_id,
    ruleset: game.ruleset,
    engineModule: game.engine_module,
    actionLimit: game.action_limit,
    disclosure: game.security.instance_visibility,
    missionId: mission.missionId,
    instance: declaration,
    oracle,
    refusals: Object.freeze([...game.refusals]),
    security: Object.freeze({
      classification: game.security.classification,
      instanceVisibility: game.security.instance_visibility,
      competitiveRewards: game.security.competitive_rewards,
      economicRewards: game.security.economic_rewards,
    }),
    mission: Object.freeze({ ...mission }),
  });
}

function baseRun(descriptor, mode, extra) {
  return Object.freeze({
    schema: TRANSCRIPT_FORMAT,
    mode,
    gameId: descriptor.gameId,
    missionId: descriptor.missionId,
    federationId: descriptor.mission.federationId,
    contentSession: descriptor.mission.contentSession,
    contentRoot: descriptor.mission.contentRoot,
    contentEpoch: descriptor.mission.contentEpoch,
    curatorCounter: descriptor.mission.curatorCounter,
    activationDigest: descriptor.mission.activationDigest,
    security: descriptor.security,
    probes: Object.freeze([]),
    settled: 0,
    solved: false,
    exhausted: false,
    ...extra,
  });
}

/**
 * A rehearsal against an instance the client chose for itself out of the emitted
 * matrix. It is not the Lean derivation and must not become one.
 */
export function createPracticeRun(descriptor, pick) {
  refuse(integer(pick, 0, descriptor.oracle.instanceSpace - 1), "practice-instance", "practice instance is outside the emitted space");
  return baseRun(descriptor, "practice", { practiceInstance: pick, slot: null, slotCommitment: null });
}

/**
 * A scored run. The client holds no instance and no seed: it holds the slot it
 * opened in and the commitment it was shown, which is what its transcript will
 * be judged against once the secret opens.
 */
export function createJudgedRun(descriptor, opening) {
  const checked = loadSlotOpening(opening, descriptor.missionId);
  return baseRun(descriptor, "judged", { practiceInstance: null, slot: checked.slot, slotCommitment: checked.commitment });
}

function probeByIdOrRefuse(descriptor, probeId) {
  const probe = descriptor.oracle.probes.find((candidate) => candidate.id === probeId);
  refuse(probe, "blackbox-probe", "the run names a probe the oracle does not declare");
  return probe;
}

function checkSubmission(descriptor, run, probeId) {
  refuse(run?.schema === TRANSCRIPT_FORMAT, "run-shape", "invalid Black Box transcript state");
  refuse(
    run.gameId === descriptor.gameId && run.missionId === descriptor.missionId &&
      run.federationId === descriptor.mission.federationId &&
      run.contentSession === descriptor.mission.contentSession &&
      run.contentRoot === descriptor.mission.contentRoot &&
      run.contentEpoch === descriptor.mission.contentEpoch &&
      run.curatorCounter === descriptor.mission.curatorCounter &&
      run.activationDigest === descriptor.mission.activationDigest &&
      run.security === descriptor.security,
    "run-domain",
    "Black Box transcript is bound to a different mission, federation, content session, or epoch",
  );
  refuse(!run.solved && !run.exhausted, "run-terminal", "Black Box run is already terminal");
  return probeByIdOrRefuse(descriptor, probeId);
}

function applyClass(descriptor, run, probe, classId) {
  const row = descriptor.oracle.classes[classId];
  refuse(row !== undefined, "oracle-class", "the oracle returned a class the descriptor does not declare");
  const probes = Object.freeze([...run.probes, Object.freeze({ probe: probe.id, slot: probe.slot, fragment: probe.fragment, classId, settling: row.solving })]);
  const settled = run.settled + (row.solving ? 1 : 0);
  return Object.freeze({
    ...run,
    probes,
    settled,
    // Both of these read EMITTED parameters — the required count and the action
    // limit — rather than deciding anything. Whether a settled run earns
    // anything is not this client's call and never appears here.
    solved: settled >= descriptor.oracle.requiredPerInstance,
    exhausted: settled < descriptor.oracle.requiredPerInstance && probes.length >= descriptor.actionLimit,
  });
}

/** PRACTICE: one lookup into the client's own row of the emitted matrix. */
export function submitPracticeProbe(descriptor, run, probeId) {
  refuse(run?.mode === "practice", "run-mode", "submitPracticeProbe called on a judged run");
  const probe = checkSubmission(descriptor, run, probeId);
  return applyClass(descriptor, run, probe, descriptor.oracle.table[run.practiceInstance][probe.index]);
}

/**
 * JUDGED: the class comes from the host, which holds the derived run seed. The
 * client checks the class is declared and applies it. It never derives one, and
 * it cannot, because it does not have the instance.
 */
export function submitJudgedProbe(descriptor, run, probeId, classId) {
  refuse(run?.mode === "judged", "run-mode", "submitJudgedProbe called on a practice run");
  const probe = checkSubmission(descriptor, run, probeId);
  refuse(integer(classId, 0, descriptor.oracle.classes.length - 1), "oracle-class", "the oracle returned an undeclared class id");
  return applyClass(descriptor, run, probe, classId);
}

/**
 * A refusal the HOST returned. The client records it against the emitted
 * vocabulary; it does not decide when a probe is refused, because this
 * descriptor does not say. See the file header.
 */
export function applyHostRefusal(descriptor, run, probeId, reason) {
  refuse(run?.mode === "judged", "run-mode", "a host refusal has no meaning in a practice run");
  const probe = checkSubmission(descriptor, run, probeId);
  refuse(descriptor.refusals.includes(reason), "blackbox-refusal", "the host returned a refusal the descriptor does not declare");
  return Object.freeze({
    ...run,
    probes: Object.freeze([...run.probes, Object.freeze({ probe: probe.id, slot: probe.slot, fragment: probe.fragment, classId: null, settling: false, refused: reason })]),
  });
}

export function replayPractice(descriptor, pick, probeIds) {
  return probeIds.reduce((run, probeId) => submitPracticeProbe(descriptor, run, probeId), createPracticeRun(descriptor, pick));
}

/**
 * `mode` sits next to the format tag, so a rehearsal and a judged attempt are
 * different objects at the byte level, and a practice run carries the instance
 * it chose while a judged one carries a slot and a commitment instead.
 */
export function canonicalReplay(run) {
  return JSON.stringify({
    format: run.schema,
    mode: run.mode,
    game_id: run.gameId,
    mission_id: run.missionId,
    federation_id: run.federationId,
    content_session: run.contentSession,
    content_root: run.contentRoot,
    content_epoch: run.contentEpoch,
    curator_counter: run.curatorCounter,
    activation_digest: run.activationDigest,
    slot: run.slot,
    slot_commitment: run.slotCommitment,
    practice_instance: run.practiceInstance,
    security: run.security,
    probes: run.probes.map((entry) => ({
      probe: entry.probe,
      class_id: entry.classId,
      settling: entry.settling,
      refused: entry.refused ?? null,
    })),
    settled: run.settled,
    solved: run.solved,
    exhausted: run.exhausted,
    settlement: "unsettled-local-transcript",
  });
}

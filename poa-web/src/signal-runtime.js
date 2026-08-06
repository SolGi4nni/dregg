import { ArtifactRefusal, sha256Hex } from "./poag1.js";
import { loadHiddenInstanceDeclaration, loadSlotOpening, refuseNamedInstance } from "./hidden-instance.js";

/**
 * Signal Triangulation after the instance/rules split.
 *
 * ⚠ What this file no longer reads, because the descriptor no longer carries it:
 * `target`, `run_seed`, and `outcomes`. The first stated the code outright, the
 * second determined it through the public derivation, and the third tabulated
 * feedback against one target — which IS the target. A descriptor carrying any
 * of them is the pre-split shape and is refused rather than reinterpreted.
 *
 * What it reads instead is `rules`: the complete 216-by-216 oracle, every target
 * against every guess. That states every rule and distinguishes no instance —
 * every row solves at exactly its own index — so a client can hold the whole
 * rulebook and still not know the code.
 *
 * Two run modes, and they are not interchangeable:
 *
 *   PRACTICE  the client picks its own instance out of `rules.codes` and answers
 *             its own guesses from the table. Nothing about this touches the live
 *             instance and nothing about it is scored. The pick is deliberately
 *             NOT the Lean practice derivation: reproducing `HiddenInstance` here
 *             would be a second copy of the rules in JavaScript, and a local
 *             uniform pick over an emitted array is a lookup, not a rule.
 *
 *   JUDGED    the client knows nothing. It sends a guess and the host — which
 *             holds the live run seed derived from the committed slot secret —
 *             returns the class id. The client checks the id is one the
 *             descriptor declares and renders it. It never derives feedback, and
 *             it cannot, because it does not have the code.
 *
 * `mode` is in the canonical replay, so a practice transcript is structurally a
 * different object from a judged one and no amount of relabelling turns one into
 * the other.
 */

const SIGNAL_FORMAT = "POAG1-GAME";
const ENGINE = "Dregg2.Games.PathOfAngels.SignalTriangulation";
const SHA256 = /^sha256:[0-9a-f]{64}$/;
const PALETTE = ["#9bd8bf", "#d6e779", "#dcac62", "#a9cbd6", "#bb9dd1", "#d2786c"];
const CONTENT_ROOT_DOMAIN = new TextEncoder().encode("path-of-angels/content-root/v1\0");

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}
function object(value) { return value !== null && typeof value === "object" && !Array.isArray(value); }
function exactKeys(value, keys, at) {
  refuse(object(value), "signal-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  refuse(actual.length === expected.length && actual.every((key, i) => key === expected[i]), "signal-field", `${at} has an unknown or missing field`);
}
function exactArray(value, expected, at) {
  refuse(Array.isArray(value) && value.length === expected.length && value.every((item, i) => item === expected[i]), "signal-constant", `${at} does not match the POAG1 v1 contract`);
}
function codeKey(code) { return code.join(","); }
function integer(value, min, max) { return Number.isSafeInteger(value) && value >= min && value <= max; }
function u64be(value) {
  const bytes = new Uint8Array(8);
  new DataView(bytes.buffer).setBigUint64(0, BigInt(value), false);
  return bytes;
}
function concat(parts) {
  const out = new Uint8Array(parts.reduce((total, part) => total + part.byteLength, 0));
  let offset = 0;
  for (const part of parts) { out.set(part, offset); offset += part.byteLength; }
  return out;
}

/** Exact POAG1 content-root preimage, independent of JSON canonicalization. */
export async function contentRoot(files) {
  const encoder = new TextEncoder();
  const entries = [...files].sort(([a], [b]) => a.localeCompare(b));
  const parts = [CONTENT_ROOT_DOMAIN, u64be(entries.length)];
  for (const [path, bytes] of entries) {
    const pathBytes = encoder.encode(path);
    parts.push(u64be(pathBytes.byteLength), pathBytes, u64be(bytes.byteLength), bytes);
  }
  return `sha256:${await sha256Hex(concat(parts))}`;
}

export { loadHiddenInstanceDeclaration, loadSlotOpening };

/**
 * Compile the emitted oracle into a read-only lookup table. JavaScript never
 * derives exact/present/solved feedback: it decodes what Lean wrote.
 */
export function loadSignalDescriptor(game, mission, contentEpoch) {
  // Before any field is read for meaning: is this the pre-split bundle?
  refuseNamedInstance(game, "Signal descriptor");
  refuseNamedInstance(game.instance, "Signal descriptor instance");
  exactKeys(game, ["format", "schema_version", "game_id", "ruleset", "engine_module", "action_limit", "security", "instance", "state", "action", "feedback", "transition", "output", "rules"], "Signal descriptor");
  refuse(game.format === SIGNAL_FORMAT && game.schema_version === 1, "signal-format", "unsupported Signal descriptor");
  refuse(
    contentEpoch?.schema === mission.activation.digestSource &&
      typeof contentEpoch.activationDigest === "string" && SHA256.test(contentEpoch.activationDigest) &&
      contentEpoch.contentEpoch === mission.epoch,
    "signal-activation",
    "Signal mission requires an authenticated matching content epoch",
  );
  refuse(game.game_id === "signal-triangulation" && game.ruleset === "signal-v2" && game.engine_module === ENGINE, "signal-identity", "Signal descriptor identity is invalid");
  refuse(integer(game.action_limit, 1, 32) && game.action_limit === mission.actionLimit, "signal-action-limit", "descriptor and catalog action limits disagree");
  exactKeys(game.security, ["classification", "instance_visibility", "competitive_rewards", "economic_rewards"], "Signal security");
  refuse(
    game.security.classification === "committed-hidden-instance" &&
      game.security.instance_visibility === "oracle-only" &&
      game.security.competitive_rewards === false &&
      game.security.economic_rewards === false,
    "signal-security",
    "Signal v2 must remain a committed, oracle-only, zero-reward beta demo",
  );
  // The disclosure comes from the SIGNED catalog, not from the descriptor, so a
  // descriptor cannot relabel itself and start naming the code it withholds.
  refuse(mission.instanceDisclosure === "oracle-only", "signal-security", "the signed catalog does not declare Signal oracle-only");
  const declaration = loadHiddenInstanceDeclaration(game.instance, mission.instanceDisclosure, "Signal descriptor instance");

  exactKeys(game.action, ["tag", "code"], "Signal action");
  refuse(game.action.tag === "submit", "signal-action", "unsupported Signal action");
  exactKeys(game.action.code, ["bands", "alphabet"], "Signal code");
  const bands = game.action.code.bands;
  const alphabet = game.action.code.alphabet;
  refuse(integer(bands, 1, 8) && integer(alphabet, 2, 16), "signal-domain", "Signal code domain is invalid");
  const validCode = (code) => Array.isArray(code) && code.length === bands && code.every((value) => integer(value, 0, alphabet - 1));

  exactKeys(game.state, ["fields"], "Signal state");
  exactArray(game.state.fields, ["turns", "solved", "last_feedback"], "Signal state fields");
  exactKeys(game.feedback, ["exact_max", "present_max", "exact_plus_present_max", "present_semantics", "solved_when_exact"], "Signal feedback");
  refuse(game.feedback.exact_max === bands && game.feedback.present_max === bands && game.feedback.exact_plus_present_max === bands && game.feedback.solved_when_exact === bands, "signal-feedback-bounds", "Signal feedback bounds disagree with the code domain");
  refuse(game.feedback.present_semantics === "multiplicity_intersection_minus_exact", "signal-feedback-semantics", "unsupported Signal feedback projection");
  exactKeys(game.transition, ["open_when", "on_submit", "refuse_when"], "Signal transition");
  exactKeys(game.transition.open_when, ["solved", "turns_lt"], "Signal open_when");
  refuse(game.transition.open_when.solved === false && game.transition.open_when.turns_lt === game.action_limit, "signal-open", "unsupported Signal open condition");
  exactKeys(game.transition.on_submit, ["lookup", "turns", "solved", "last_feedback"], "Signal on_submit");
  refuse(game.transition.on_submit.lookup === "rules.table[instance][guess]" && game.transition.on_submit.turns === "increment" && game.transition.on_submit.solved === "class.solved", "signal-transition", "unsupported Signal transition dispatch");
  exactArray(game.transition.on_submit.last_feedback, ["class.exact", "class.present"], "Signal last_feedback projection");
  exactArray(game.transition.refuse_when, ["solved", "turns_gte_action_limit"], "Signal refusal conditions");
  exactKeys(game.output, ["requires", "contribution", "artifact"], "Signal output");
  refuse(game.output.requires === "solved" && game.output.contribution === "mission_reward" && game.output.artifact === "mission_artifact", "signal-output", "unsupported Signal output projection");

  // ---- the oracle ---------------------------------------------------------
  exactKeys(game.rules, ["class_alphabet", "classes", "codes", "table"], "Signal rules");
  const domainSize = alphabet ** bands;
  refuse(Array.isArray(game.rules.codes) && game.rules.codes.length === domainSize, "rules-domain", `Signal rules must name the complete ${domainSize}-code domain`);
  const codes = game.rules.codes.map((code, index) => {
    refuse(validCode(code), "rules-code", `Signal rules codes[${index}] is outside the emitted domain`);
    return Object.freeze([...code]);
  });
  const codeIndex = new Map();
  codes.forEach((code, index) => {
    const key = codeKey(code);
    refuse(!codeIndex.has(key), "rules-code", `Signal rules codes contains ${key} twice`);
    codeIndex.set(key, index);
  });

  const classes = game.rules.classes.map((row, index) => {
    exactKeys(row, ["exact", "present", "solved"], `Signal rules classes[${index}]`);
    refuse(integer(row.exact, 0, bands) && integer(row.present, 0, bands), "rules-class", `Signal rules classes[${index}] is out of bounds`);
    refuse(row.exact + row.present <= bands, "rules-class", `Signal rules classes[${index}] exceeds the code width`);
    refuse(typeof row.solved === "boolean" && row.solved === (row.exact === game.feedback.solved_when_exact), "rules-class", `Signal rules classes[${index}] solved bit contradicts the terminal threshold`);
    return Object.freeze({ exact: row.exact, present: row.present, solved: row.solved });
  });
  const solvedIds = classes.map((row, index) => (row.solved ? index : -1)).filter((index) => index >= 0);
  refuse(solvedIds.length === 1, "rules-class", "Signal rules must declare exactly one solving class");
  const solvedClassId = solvedIds[0];

  const alphabetChars = game.rules.class_alphabet;
  refuse(typeof alphabetChars === "string" && alphabetChars.length >= classes.length, "rules-alphabet", "Signal rules class alphabet is too short");
  const charId = new Map([...alphabetChars.slice(0, classes.length)].map((char, index) => [char, index]));
  refuse(charId.size === classes.length, "rules-alphabet", "Signal rules class alphabet repeats a character");

  refuse(Array.isArray(game.rules.table) && game.rules.table.length === domainSize, "rules-table", `Signal rules table must have one row per code`);
  const table = game.rules.table.map((row, index) => {
    refuse(typeof row === "string" && row.length === domainSize, "rules-table", `Signal rules table[${index}] is not one cell per code`);
    const decoded = new Uint8Array(domainSize);
    for (let column = 0; column < domainSize; column += 1) {
      const id = charId.get(row[column]);
      refuse(id !== undefined, "rules-table", `Signal rules table[${index}] names a class outside the declared alphabet`);
      decoded[column] = id;
    }
    // The property that makes this table instance-free: each row solves at
    // exactly its own index. A row that solved elsewhere would name an instance.
    let solvedAt = -1;
    for (let column = 0; column < domainSize; column += 1) {
      if (decoded[column] === solvedClassId) {
        refuse(solvedAt < 0, "rules-table", `Signal rules table[${index}] solves at more than one guess`);
        solvedAt = column;
      }
    }
    refuse(solvedAt === index, "rules-table", `Signal rules table[${index}] solves at ${solvedAt}, not at itself: the table distinguishes a row and therefore names an instance`);
    return decoded;
  });

  const symbols = Object.freeze(Array.from({ length: alphabet }, (_, id) => Object.freeze({
    id,
    label: `BAND ${id}`,
    glyph: String(id),
    color: PALETTE[id % PALETTE.length],
  })));
  return Object.freeze({
    gameId: game.game_id,
    missionId: mission.missionId,
    codeLength: bands,
    alphabet,
    maxTurns: game.action_limit,
    symbols,
    codes: Object.freeze(codes),
    codeIndex,
    classes: Object.freeze(classes),
    solvedClassId,
    table: Object.freeze(table),
    instance: declaration,
    security: Object.freeze({
      classification: game.security.classification,
      instanceVisibility: game.security.instance_visibility,
      competitiveRewards: game.security.competitive_rewards,
      economicRewards: game.security.economic_rewards,
    }),
    mission: Object.freeze({
      ...mission,
      activationDigest: contentEpoch.activationDigest,
      contentEpoch: contentEpoch.contentEpoch,
      curatorCounter: contentEpoch.counter,
      activatedManifest: contentEpoch.manifestDigest,
    }),
  });
}

function baseRun(descriptor, mode, extra) {
  return Object.freeze({
    schema: "POAG1-SIGNAL-TRANSCRIPT",
    mode,
    gameId: descriptor.gameId,
    missionId: descriptor.missionId,
    federationId: descriptor.mission.federationId,
    contentSession: descriptor.mission.contentSession,
    contentRoot: descriptor.mission.contentRoot,
    contentEpoch: descriptor.mission.contentEpoch,
    curatorCounter: descriptor.mission.curatorCounter,
    activationDigest: descriptor.mission.activationDigest,
    activatedManifest: descriptor.mission.activatedManifest,
    security: descriptor.security,
    turns: Object.freeze([]),
    solved: false,
    exhausted: false,
    ...extra,
  });
}

/**
 * A rehearsal against an instance the client chose for itself.
 *
 * `pick` is a client-chosen index into the emitted code list. It defaults to a
 * uniform draw from the platform CSPRNG. This is NOT the Lean practice
 * derivation and must not be made into it: reproducing `HiddenInstance` here
 * would put a second copy of the rules in JavaScript, and there is nothing to
 * gain, because a practice instance is answerable to nobody.
 */
export function createPracticeRun(descriptor, pick) {
  let index = pick;
  if (index === undefined) {
    const draw = new Uint32Array(1);
    crypto.getRandomValues(draw);
    index = draw[0] % descriptor.codes.length;
  }
  refuse(integer(index, 0, descriptor.codes.length - 1), "practice-instance", "practice instance index is outside the emitted code domain");
  return baseRun(descriptor, "practice", {
    practiceInstance: index,
    // Deliberately present and deliberately local: a practice run knows its own
    // answer, which is exactly why it is not scored.
    practiceCode: descriptor.codes[index],
    slot: null,
    slotCommitment: null,
  });
}

/**
 * A scored run. The client learns nothing here: no code, no seed, no row index.
 * It carries the slot it opened in and the commitment it was shown, which is
 * what its transcript will be judged against.
 */
export function createJudgedRun(descriptor, opening) {
  const checked = loadSlotOpening(opening, descriptor.missionId);
  return baseRun(descriptor, "judged", {
    practiceInstance: null,
    practiceCode: null,
    slot: checked.slot,
    slotCommitment: checked.commitment,
  });
}

function checkSubmission(descriptor, run, guess) {
  refuse(run?.schema === "POAG1-SIGNAL-TRANSCRIPT", "run-shape", "invalid Signal transcript state");
  refuse(
    run.gameId === descriptor.gameId && run.missionId === descriptor.missionId &&
      run.federationId === descriptor.mission.federationId &&
      run.contentSession === descriptor.mission.contentSession &&
      run.contentRoot === descriptor.mission.contentRoot &&
      run.contentEpoch === descriptor.mission.contentEpoch &&
      run.curatorCounter === descriptor.mission.curatorCounter &&
      run.activationDigest === descriptor.mission.activationDigest &&
      run.activatedManifest === descriptor.mission.activatedManifest &&
      run.security === descriptor.security,
    "run-domain",
    "Signal transcript is bound to a different mission, federation, content session, or epoch",
  );
  refuse(!run.solved && !run.exhausted, "run-terminal", "Signal run is already terminal");
  refuse(Array.isArray(guess) && guess.length === descriptor.codeLength && guess.every((id) => integer(id, 0, descriptor.alphabet - 1)), "guess-shape", "Signal guess is invalid");
  const index = descriptor.codeIndex.get(codeKey(guess));
  refuse(index !== undefined, "missing-transition", "Lean artifact contains no column for this Signal guess");
  return index;
}

function applyClass(descriptor, run, guess, classId) {
  const row = descriptor.classes[classId];
  refuse(row !== undefined, "oracle-class", "the oracle returned a class the descriptor does not declare");
  const turns = Object.freeze([...run.turns, Object.freeze({ guess: Object.freeze([...guess]), classId, exact: row.exact, present: row.present, solved: row.solved })]);
  return Object.freeze({ ...run, turns, solved: row.solved, exhausted: !row.solved && turns.length >= descriptor.maxTurns });
}

/** Practice: read the client's own row of the emitted oracle. */
export function submitPracticeGuess(descriptor, run, guess) {
  refuse(run?.mode === "practice", "run-mode", "submitPracticeGuess called on a judged run");
  const column = checkSubmission(descriptor, run, guess);
  return applyClass(descriptor, run, guess, descriptor.table[run.practiceInstance][column]);
}

/**
 * Judged: the class id comes from the host, which holds the live run seed. The
 * client checks the id is declared and applies it; it does not and cannot derive
 * it. After the slot closes and the secret is opened, every answer in the
 * transcript is recomputable by anyone, which is what makes the host answerable.
 */
export function submitJudgedGuess(descriptor, run, guess, classId) {
  refuse(run?.mode === "judged", "run-mode", "submitJudgedGuess called on a practice run");
  checkSubmission(descriptor, run, guess);
  refuse(integer(classId, 0, descriptor.classes.length - 1), "oracle-class", "the oracle returned an undeclared class id");
  return applyClass(descriptor, run, guess, classId);
}

export function replayPractice(descriptor, pick, guesses) {
  return guesses.reduce((run, guess) => submitPracticeGuess(descriptor, run, guess), createPracticeRun(descriptor, pick));
}

/**
 * `mode` is the first field after the format tag, so a practice transcript and a
 * judged one are different objects at the byte level and no relabelling turns one
 * into the other. A practice run also has no slot and no commitment, so there is
 * nothing for a judge to check it against.
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
    activated_manifest: run.activatedManifest,
    slot: run.slot,
    slot_commitment: run.slotCommitment,
    practice_instance: run.practiceInstance,
    security: run.security,
    turns: run.turns.map((turn) => ({ guess: turn.guess, class_id: turn.classId, exact: turn.exact, present: turn.present, solved: turn.solved })),
    solved: run.solved,
    exhausted: run.exhausted,
  });
}

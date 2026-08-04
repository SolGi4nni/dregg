import { ArtifactRefusal, sha256Hex } from "./poag1.js";

const SIGNAL_FORMAT = "POAG1-GAME";
const ENGINE = "Dregg2.Games.PathOfAngels.SignalTriangulation";
const SHA256 = /^sha256:[0-9a-f]{64}$/;
const HEX_32 = /^[0-9a-f]{64}$/;
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

/**
 * Compile the 216 Lean-computed rows into a read-only lookup table. JavaScript
 * never derives exact/present/solved feedback.
 */
export function loadSignalDescriptor(game, mission, contentEpoch) {
  exactKeys(game, ["format", "schema_version", "game_id", "ruleset", "engine_module", "action_limit", "run_seed", "target", "security", "state", "action", "feedback", "transition", "output", "outcomes"], "Signal descriptor");
  refuse(game.format === SIGNAL_FORMAT && game.schema_version === 1, "signal-format", "unsupported Signal descriptor");
  refuse(
    contentEpoch?.schema === mission.activation.digestSource &&
      typeof contentEpoch.activationDigest === "string" && SHA256.test(contentEpoch.activationDigest) &&
      contentEpoch.contentEpoch === mission.epoch,
    "signal-activation",
    "Signal mission requires an authenticated matching content epoch",
  );
  refuse(game.game_id === "signal-triangulation" && game.ruleset === "signal-v1" && game.engine_module === ENGINE, "signal-identity", "Signal descriptor identity is invalid");
  refuse(integer(game.action_limit, 1, 32) && game.action_limit === mission.actionLimit, "signal-action-limit", "descriptor and catalog action limits disagree");
  refuse(typeof game.run_seed === "string" && HEX_32.test(game.run_seed) && game.run_seed === mission.runSeed, "signal-run-seed", "descriptor and mission run_seed disagree");
  exactKeys(game.security, ["classification", "target_visibility", "competitive_rewards", "economic_rewards"], "Signal security");
  refuse(
    game.security.classification === "transparent-beta-demo" &&
      game.security.target_visibility === "public" &&
      game.security.competitive_rewards === false &&
      game.security.economic_rewards === false,
    "signal-security",
    "Signal v1 must remain a transparent, public-target, zero-reward beta demo",
  );

  exactKeys(game.action, ["tag", "code"], "Signal action");
  refuse(game.action.tag === "submit", "signal-action", "unsupported Signal action");
  exactKeys(game.action.code, ["bands", "alphabet"], "Signal code");
  const bands = game.action.code.bands;
  const alphabet = game.action.code.alphabet;
  refuse(integer(bands, 1, 8) && integer(alphabet, 2, 16), "signal-domain", "Signal code domain is invalid");
  const validCode = (code) => Array.isArray(code) && code.length === bands && code.every((value) => integer(value, 0, alphabet - 1));
  refuse(validCode(game.target), "signal-target", "Signal target is outside the emitted code domain");

  exactKeys(game.state, ["fields"], "Signal state");
  exactArray(game.state.fields, ["turns", "solved", "last_feedback"], "Signal state fields");
  exactKeys(game.feedback, ["exact_max", "present_max", "exact_plus_present_max", "present_semantics", "solved_when_exact"], "Signal feedback");
  refuse(game.feedback.exact_max === bands && game.feedback.present_max === bands && game.feedback.exact_plus_present_max === bands && game.feedback.solved_when_exact === bands, "signal-feedback-bounds", "Signal feedback bounds disagree with the code domain");
  refuse(game.feedback.present_semantics === "multiplicity_intersection_minus_exact", "signal-feedback-semantics", "unsupported Signal feedback projection");
  exactKeys(game.transition, ["open_when", "on_submit", "refuse_when"], "Signal transition");
  exactKeys(game.transition.open_when, ["solved", "turns_lt"], "Signal open_when");
  refuse(game.transition.open_when.solved === false && game.transition.open_when.turns_lt === game.action_limit, "signal-open", "unsupported Signal open condition");
  exactKeys(game.transition.on_submit, ["lookup", "turns", "solved", "last_feedback"], "Signal on_submit");
  refuse(game.transition.on_submit.lookup === "outcomes.guess" && game.transition.on_submit.turns === "increment" && game.transition.on_submit.solved === "row.solved", "signal-transition", "unsupported Signal transition dispatch");
  exactArray(game.transition.on_submit.last_feedback, ["row.exact", "row.present"], "Signal last_feedback projection");
  exactArray(game.transition.refuse_when, ["solved", "turns_gte_action_limit"], "Signal refusal conditions");
  exactKeys(game.output, ["requires", "contribution", "artifact"], "Signal output");
  refuse(game.output.requires === "solved" && game.output.contribution === "mission_reward" && game.output.artifact === "mission_artifact", "signal-output", "unsupported Signal output projection");

  const domainSize = alphabet ** bands;
  refuse(Array.isArray(game.outcomes) && game.outcomes.length === domainSize, "outcome-count", `Signal outcomes must contain the complete ${domainSize}-row domain`);
  const outcomes = new Map();
  for (const [index, row] of game.outcomes.entries()) {
    exactKeys(row, ["guess", "exact", "present", "solved"], `Signal outcomes[${index}]`);
    refuse(validCode(row.guess), "outcome-guess", `Signal outcomes[${index}] has an invalid guess`);
    refuse(integer(row.exact, 0, game.feedback.exact_max) && integer(row.present, 0, game.feedback.present_max), "outcome-feedback", `Signal outcomes[${index}] feedback is out of bounds`);
    refuse(row.exact + row.present <= bands, "outcome-feedback", `Signal outcomes[${index}] total feedback exceeds the code width`);
    refuse(typeof row.solved === "boolean" && row.solved === (row.exact === game.feedback.solved_when_exact), "outcome-solved", `Signal outcomes[${index}] solved bit contradicts the emitted terminal threshold`);
    const key = codeKey(row.guess);
    refuse(!outcomes.has(key), "duplicate-outcome", `Signal outcome ${key} is duplicated`);
    outcomes.set(key, Object.freeze({ exact: row.exact, present: row.present, solved: row.solved }));
  }
  refuse(outcomes.size === domainSize, "outcome-domain", "Signal outcome table is not a complete finite domain");

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
    outcomes,
    security: Object.freeze({
      classification: game.security.classification,
      targetVisibility: game.security.target_visibility,
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

export function createSignalRun(descriptor) {
  return Object.freeze({
    schema: "POAG1-SIGNAL-TRANSCRIPT",
    gameId: descriptor.gameId,
    missionId: descriptor.missionId,
    federationId: descriptor.mission.federationId,
    contentSession: descriptor.mission.contentSession,
    runSeed: descriptor.mission.runSeed,
    contentRoot: descriptor.mission.contentRoot,
    contentEpoch: descriptor.mission.contentEpoch,
    curatorCounter: descriptor.mission.curatorCounter,
    activationDigest: descriptor.mission.activationDigest,
    activatedManifest: descriptor.mission.activatedManifest,
    security: descriptor.security,
    turns: Object.freeze([]),
    solved: false,
    exhausted: false,
  });
}

export function submitSignalGuess(descriptor, run, guess) {
  refuse(run?.schema === "POAG1-SIGNAL-TRANSCRIPT", "run-shape", "invalid Signal transcript state");
  refuse(
    run.gameId === descriptor.gameId && run.missionId === descriptor.missionId &&
      run.federationId === descriptor.mission.federationId &&
      run.contentSession === descriptor.mission.contentSession &&
      run.runSeed === descriptor.mission.runSeed &&
      run.contentRoot === descriptor.mission.contentRoot &&
      run.contentEpoch === descriptor.mission.contentEpoch &&
      run.curatorCounter === descriptor.mission.curatorCounter &&
      run.activationDigest === descriptor.mission.activationDigest &&
      run.activatedManifest === descriptor.mission.activatedManifest &&
      run.security === descriptor.security,
    "run-domain",
    "Signal transcript is bound to a different mission, federation, content session, or run seed",
  );
  refuse(!run.solved && !run.exhausted, "run-terminal", "Signal run is already terminal");
  refuse(Array.isArray(guess) && guess.length === descriptor.codeLength && guess.every((id) => integer(id, 0, descriptor.alphabet - 1)), "guess-shape", "Signal guess is invalid");
  const row = descriptor.outcomes.get(codeKey(guess));
  refuse(row, "missing-transition", "Lean artifact contains no transition for this Signal guess");
  const turns = Object.freeze([...run.turns, Object.freeze({ guess: Object.freeze([...guess]), ...row })]);
  return Object.freeze({ ...run, turns, solved: row.solved, exhausted: !row.solved && turns.length >= descriptor.maxTurns });
}

export function replaySignal(descriptor, guesses) {
  return guesses.reduce((run, guess) => submitSignalGuess(descriptor, run, guess), createSignalRun(descriptor));
}

export function canonicalReplay(run) {
  return JSON.stringify({
    format: run.schema,
    game_id: run.gameId,
    mission_id: run.missionId,
    federation_id: run.federationId,
    content_session: run.contentSession,
    run_seed: run.runSeed,
    content_root: run.contentRoot,
    content_epoch: run.contentEpoch,
    curator_counter: run.curatorCounter,
    activation_digest: run.activationDigest,
    activated_manifest: run.activatedManifest,
    security: run.security,
    turns: run.turns.map((turn) => ({ guess: turn.guess, exact: turn.exact, present: turn.present, solved: turn.solved })),
    solved: run.solved,
    exhausted: run.exhausted,
  });
}

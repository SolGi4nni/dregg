import { ArtifactRefusal } from "./poag1.js";
import { RUN_STATUSES, isRunStatus } from "./run-summary.js";

/**
 * "Your best/last result", and nothing more than that.
 *
 * This is a note this browser keeps for itself. It is not a score, not a rank,
 * and not evidence: no node ever reads it, nothing signs it, and clearing site
 * data erases it without consequence. It exists so a card can say "you have been
 * here before".
 *
 * ⚠ TWO BUCKETS, AND THE BUCKET IS DERIVED. A practice best and a judged best are
 * stored apart and are never merged, because a single "best" column is precisely
 * how a rehearsal ends up being displayed as a result. The bucket comes from the
 * status, so a caller cannot file a practice run under judged by asking nicely.
 *
 * Anything malformed on the way IN or OUT is dropped rather than repaired — a
 * record this code cannot fully account for is a record it should not be
 * displaying a number from.
 */

export const RESULTS_STORAGE_KEY = "poa.rack.results.v1";
export const RESULT_KEYS = Object.freeze(["status", "outcome", "actions", "at"]);
export const RESULT_OUTCOMES = Object.freeze(["solved", "unsolved", "refused"]);
const PER_GAME_LIMIT = 32;

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

/** Which bucket a status files under. Practice is alone in its own. */
export function resultBucket(status) {
  refuse(isRunStatus(status), "result-status", `unknown run status: ${status}`);
  return status === "practice" ? "practice" : "judged";
}

function validRecord(value, bucket) {
  if (!object(value)) return false;
  const keys = Object.keys(value).sort();
  const wanted = [...RESULT_KEYS].sort();
  if (keys.length !== wanted.length || !keys.every((key, index) => key === wanted[index])) return false;
  if (!RUN_STATUSES.includes(value.status) || resultBucket(value.status) !== bucket) return false;
  if (!RESULT_OUTCOMES.includes(value.outcome)) return false;
  if (!Number.isSafeInteger(value.actions) || value.actions < 0) return false;
  return Number.isSafeInteger(value.at) && value.at > 0;
}

function cleanGame(value) {
  if (!object(value)) return null;
  const buckets = {};
  for (const bucket of ["practice", "judged"]) {
    const records = Array.isArray(value[bucket]) ? value[bucket] : [];
    buckets[bucket] = Object.freeze(
      records.filter((record) => validRecord(record, bucket)).slice(-PER_GAME_LIMIT).map((record) => Object.freeze({ ...record })),
    );
  }
  if (buckets.practice.length === 0 && buckets.judged.length === 0) return null;
  return Object.freeze(buckets);
}

/** Read the local history, dropping anything that does not validate. */
export function readRackResults(storage) {
  if (!storage || typeof storage.getItem !== "function") return Object.freeze({});
  let raw;
  try { raw = storage.getItem(RESULTS_STORAGE_KEY); } catch { return Object.freeze({}); }
  if (typeof raw !== "string" || raw.length === 0) return Object.freeze({});
  let parsed;
  try { parsed = JSON.parse(raw); } catch { return Object.freeze({}); }
  if (!object(parsed)) return Object.freeze({});
  const out = {};
  for (const [gameId, value] of Object.entries(parsed)) {
    const cleaned = cleanGame(value);
    if (cleaned) out[gameId] = cleaned;
  }
  return Object.freeze(out);
}

/**
 * File one finished run. Returns the new history; writing is best-effort, and a
 * storage that refuses (private mode, quota, disabled) costs nothing but the
 * note — it never blocks or alters play.
 */
export function recordRackResult(storage, gameId, { status, outcome, actions, at = Date.now() }) {
  refuse(typeof gameId === "string" && gameId.length > 0, "result-game", "a result needs a game id");
  refuse(isRunStatus(status), "result-status", `unknown run status: ${status}`);
  refuse(RESULT_OUTCOMES.includes(outcome), "result-outcome", `unknown run outcome: ${outcome}`);
  refuse(Number.isSafeInteger(actions) && actions >= 0, "result-actions", "a result needs an exact action count");
  refuse(Number.isSafeInteger(at) && at > 0, "result-at", "a result needs an exact timestamp");
  const bucket = resultBucket(status);
  const history = readRackResults(storage);
  const game = history[gameId] ?? { practice: [], judged: [] };
  const next = {
    ...history,
    [gameId]: Object.freeze({
      practice: Object.freeze([...game.practice]),
      judged: Object.freeze([...game.judged]),
      [bucket]: Object.freeze([...game[bucket], Object.freeze({ status, outcome, actions, at })].slice(-PER_GAME_LIMIT)),
    }),
  };
  if (storage && typeof storage.setItem === "function") {
    try { storage.setItem(RESULTS_STORAGE_KEY, JSON.stringify(next)); } catch { /* a note nobody can keep is still only a note */ }
  }
  return Object.freeze(next);
}

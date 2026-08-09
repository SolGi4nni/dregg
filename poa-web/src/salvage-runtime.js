import {
  boundedInteger,
  exactKeys,
  identifier,
  loadFiniteTableDescriptor,
  loadHiddenInstanceDeclaration,
} from "./finite-table-runtime.js";
import { ArtifactRefusal } from "./poag1.js";

/**
 * Salvage Lock after the instance/rules split.
 *
 * ⚠ `glyph_id` and `glyph_label` are GONE from every action row, and are refused
 * by the shared loader. They named the glyph sealed under each plate, which is
 * the entire board — the game was face-up and called concealed.
 *
 * What ships instead is ONE 1016-state machine whose rows do not all have one
 * successor. A row that turns over a second plate cannot know whether it pairs
 * until the board is known, so it carries `on_match` and `on_mismatch` and a
 * verdict of `resolve`. The client walks the table and, at those rows, asks.
 *
 * Salvage's disclosure is `oracle-only`: the board is never named during the
 * run, and a judged transcript carries the answers rather than the board. When
 * the slot closes and the secret opens, every answer becomes recomputable, which
 * is what makes the host answerable for them.
 *
 * `practice.boards` is the emitted instance space — all 90 boards — so a
 * rehearsal can pick one and answer itself. See `salvagePracticeOracle`.
 */

const SLOT_COUNT = 6;
const GLYPH_COUNT = 3;
const COPIES_PER_GLYPH = 2;
const INSTANCE_SPACE = 90;
const ACTION_IDS = Object.freeze(Array.from({ length: SLOT_COUNT }, (_, slot) => `slot-${slot}`));
const REFUSALS = Object.freeze(["solved", "turn-limit", "cleared-slot", "already-exposed"]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function label(value, at) {
  refuse(typeof value === "string" && value.length >= 1 && value.length <= 64, "salvage-label", `${at} is invalid`);
  return value;
}

function plate(value, at) {
  return boundedInteger(value, 0, SLOT_COUNT - 1, "salvage-slot", `${at} is invalid`);
}

function salvageView(value, actionLimit, at) {
  exactKeys(value, ["cleared", "exposed", "turns", "solved"], at);
  refuse(Array.isArray(value.cleared), "salvage-cleared", `${at}.cleared must be an array`);
  const cleared = value.cleared.map((entry, index) => plate(entry, `${at}.cleared[${index}]`));
  refuse(new Set(cleared).size === cleared.length, "salvage-cleared", `${at}.cleared contains a duplicate`);
  refuse(cleared.every((entry, index) => index === 0 || cleared[index - 1] < entry), "salvage-cleared", `${at}.cleared is not in canonical slot order`);
  const exposed = value.exposed === null ? null : plate(value.exposed, `${at}.exposed`);
  refuse(exposed === null || !cleared.includes(exposed), "salvage-cleared", `${at} exposes a plate it has already cleared`);
  boundedInteger(value.turns, 0, actionLimit, "salvage-turns", `${at}.turns is invalid`);
  refuse(typeof value.solved === "boolean", "salvage-solved", `${at}.solved is invalid`);
  return Object.freeze({ cleared: Object.freeze(cleared), exposed, turns: value.turns, solved: value.solved });
}

function salvageAction(value, at) {
  exactKeys(value, ["id", "label", "slot"], at);
  identifier(value.id, "salvage-action", `${at}.id is invalid`);
  const actionSlot = plate(value.slot, `${at}.slot`);
  refuse(value.id === ACTION_IDS[actionSlot], "salvage-action", `${at}.id disagrees with its slot`);
  refuse(label(value.label, `${at}.label`) === `Expose plate ${actionSlot}`, "salvage-action", `${at}.label disagrees with its slot`);
  return { id: value.id, label: value.label, slot: actionSlot };
}

/**
 * The emitted practice instance space. This is NOT the live board and is never
 * the live board: it exists so a rehearsal has something to answer itself with.
 * Every board in it is checked to be the declared shape, and the space is
 * checked to be complete and duplicate-free, because a practice family that is
 * smaller than it claims would make rehearsal easier than the real thing.
 */
function salvagePractice(value, at) {
  exactKeys(value, ["instance_space", "instance_shape", "scored", "boards"], at);
  refuse(value.scored === false, "salvage-practice", `${at} declares practice runs scored`);
  refuse(typeof value.instance_shape === "string" && value.instance_shape.length > 0, "salvage-practice", `${at}.instance_shape is absent`);
  refuse(value.instance_space === INSTANCE_SPACE, "salvage-practice", `${at}.instance_space is not the ${INSTANCE_SPACE}-board Salvage space`);
  refuse(Array.isArray(value.boards) && value.boards.length === value.instance_space, "salvage-practice", `${at}.boards does not fill the declared instance space`);
  const seen = new Set();
  const boards = value.boards.map((board, index) => {
    refuse(Array.isArray(board) && board.length === SLOT_COUNT, "salvage-practice", `${at}.boards[${index}] is not a ${SLOT_COUNT}-plate board`);
    const glyphs = board.map((glyph, slot) => boundedInteger(glyph, 0, GLYPH_COUNT - 1, "salvage-practice", `${at}.boards[${index}][${slot}] is invalid`));
    const counts = new Map();
    for (const glyph of glyphs) counts.set(glyph, (counts.get(glyph) ?? 0) + 1);
    refuse(
      counts.size === GLYPH_COUNT && [...counts.values()].every((count) => count === COPIES_PER_GLYPH),
      "salvage-practice",
      `${at}.boards[${index}] is not ${COPIES_PER_GLYPH} copies of each of ${GLYPH_COUNT} glyphs`,
    );
    const key = glyphs.join(",");
    refuse(!seen.has(key), "salvage-practice", `${at}.boards contains ${key} twice, so the practice space is smaller than it claims`);
    seen.add(key);
    return Object.freeze(glyphs);
  });
  return Object.freeze({
    instanceSpace: value.instance_space,
    instanceShape: value.instance_shape,
    scored: value.scored,
    boards: Object.freeze(boards),
  });
}

/** Decode Salvage Lock's authenticated Lean-emitted parametric table. */
export function loadSalvageLockDescriptor(game, authority) {
  refuse(game !== null && typeof game === "object" && !Array.isArray(game), "salvage-shape", "Salvage Lock descriptor must be an object");
  let practice = null;
  const descriptor = loadFiniteTableDescriptor(game, authority, {
    name: "Salvage Lock",
    gameId: "salvage-lock",
    ruleset: "salvage-v2",
    disclosure: "oracle-only",
    engineModule: "Dregg2.Games.PathOfAngels.SalvageLock",
    // ⚑ THE BUDGET IS 18 EXPOSURES (nine comparisons), not 12, and these four
    // numbers are the flag day. `SalvageLock.MAX_TURNS` went 12 -> 18 because 12
    // sat exactly at the mean of optimal play — a perfect player cleared the hatch
    // 60% of the time and had no way to know they had been beaten by the budget
    // rather than by the board. 18 is the exact adversarial worst case of the
    // one-bit game, so perfect play NEVER loses to the clock and the budget is
    // still spent to its last exposure. The parametric closure carries `turns`, so
    // a bigger budget is a bigger table: 632 states / 3792 rows became 1016 / 6096.
    //
    // ⚠ These pins REFUSE the previously signed bundle, deliberately. Until the
    // ceremony re-emits and re-signs `poa/artifacts/poag1/`, Salvage will not load
    // — which is the flag day being loud instead of two shapes quietly disagreeing.
    actionLimit: 18,
    maxActionLimit: 18,
    stateCount: 1016,
    maxStates: 1016,
    maxActions: SLOT_COUNT,
    allowsResolve: true,
    extraKeys: ["practice"],
    refusalReasons: REFUSALS,
    parseInstance: (value, at) => {
      practice = salvagePractice(value.practice, `${at} practice space`);
      return Object.freeze({
        draw: loadHiddenInstanceDeclaration(value.instance, "oracle-only", at),
        practice,
      });
    },
    parseView: salvageView,
    parseAction: salvageAction,
  });
  refuse(
    descriptor.actions.length === SLOT_COUNT && descriptor.actions.every((action, index) => action.id === ACTION_IDS[index] && action.slot === index),
    "salvage-action-domain",
    "Salvage Lock must emit all six slots in canonical order",
  );
  // A table with no oracle rows would be a table that decides the board, which
  // for an oracle-only game means it published one.
  //
  // ⚠ This is a BACKSTOP, not the working gate, and it is worth saying which.
  // On the emitted 1016-state closure the mismatch branches are the only way into
  // a large part of the table, so collapsing the oracle rows strands those
  // states and `table-state-closure` refuses first — measured, in
  // canonical-finite-tables.test.mjs. This line catches only a table that never
  // had oracle rows at all.
  refuse(
    descriptor.members[0].transitions.some((row) => row.verdict === "resolve"),
    "salvage-oracle",
    "Salvage Lock emits no oracle rows, so its table settles pairing without the hidden board",
  );
  return descriptor;
}

/**
 * The PRACTICE instance oracle, and the only place this client answers a
 * question about an instance.
 *
 * Read what it does and does not do. The RULE — what a match and a mismatch do
 * to the run — is emitted: it is `on_match` and `on_mismatch` on the row, and
 * this function never looks at either. What this answers is the one question the
 * row defers: are the two plates the same glyph. Both plate indices come from
 * emitted fields (`view.exposed` on the current state, `slot` on the action), so
 * the question is read rather than inferred, and the answer is two lookups into
 * an emitted practice board.
 *
 * It is confined to practice on purpose. A judged run has no board to look in
 * and gets its answers from the host, which holds the derived seed.
 *
 * ⚠ WORTH RE-EMITTING: the row does not state the pair it asks about, so this
 * function has to take it from `view.exposed`. If a resolve row carried the two
 * plate indices it compares, the client would read the question instead of
 * assembling it, and this would be a pure lookup like Signal's.
 */
export function salvagePracticeOracle(descriptor, boardIndex) {
  const board = descriptor.instance.practice.boards[boardIndex];
  refuse(board, "salvage-practice", "the practice run names a board outside the emitted instance space");
  return (view, actionId) => {
    const action = descriptor.actions.find((candidate) => candidate.id === actionId);
    refuse(action, "salvage-practice", "the practice oracle was asked about an unknown action");
    refuse(
      view.exposed !== null,
      "salvage-practice",
      "an oracle row was reached with no plate exposed, so the emitted table asks a question it did not set up",
    );
    return board[view.exposed] === board[action.slot] ? "match" : "mismatch";
  };
}

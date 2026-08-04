import {
  boundedInteger,
  exactKeys,
  identifier,
  loadFiniteTableDescriptor,
} from "./finite-table-runtime.js";
import { ArtifactRefusal } from "./poag1.js";

const SLOT_COUNT = 6;
const ACTION_IDS = Object.freeze(Array.from({ length: SLOT_COUNT }, (_, slot) => `slot-${slot}`));
const REFUSALS = Object.freeze(["solved", "turn-limit", "cleared-slot", "already-exposed"]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function label(value, at) {
  refuse(typeof value === "string" && value.length >= 1 && value.length <= 64, "salvage-label", `${at} is invalid`);
  return value;
}

function slot(value, at) {
  return boundedInteger(value, 0, SLOT_COUNT - 1, "salvage-slot", `${at} is invalid`);
}

function salvageView(value, actionLimit, at) {
  exactKeys(value, ["cleared", "exposed", "turns", "solved"], at);
  refuse(Array.isArray(value.cleared), "salvage-cleared", `${at}.cleared must be an array`);
  const cleared = value.cleared.map((value, index) => slot(value, `${at}.cleared[${index}]`));
  refuse(new Set(cleared).size === cleared.length, "salvage-cleared", `${at}.cleared contains a duplicate`);
  refuse(cleared.every((value, index) => index === 0 || cleared[index - 1] < value), "salvage-cleared", `${at}.cleared is not in canonical slot order`);
  const exposed = value.exposed === null ? null : slot(value.exposed, `${at}.exposed`);
  boundedInteger(value.turns, 0, actionLimit, "salvage-turns", `${at}.turns is invalid`);
  refuse(typeof value.solved === "boolean", "salvage-solved", `${at}.solved is invalid`);
  return Object.freeze({ cleared: Object.freeze(cleared), exposed, turns: value.turns, solved: value.solved });
}

function salvageAction(value, at) {
  exactKeys(value, ["id", "label", "slot", "glyph_id", "glyph_label"], at);
  identifier(value.id, "salvage-action", `${at}.id is invalid`);
  const actionSlot = slot(value.slot, `${at}.slot`);
  refuse(value.id === ACTION_IDS[actionSlot], "salvage-action", `${at}.id disagrees with its slot`);
  boundedInteger(value.glyph_id, 0, 2, "salvage-glyph", `${at}.glyph_id is invalid`);
  refuse(label(value.label, `${at}.label`) === `Expose plate ${actionSlot}`, "salvage-action", `${at}.label disagrees with its slot`);
  refuse(label(value.glyph_label, `${at}.glyph_label`) === `glyph-${value.glyph_id}`, "salvage-glyph", `${at}.glyph_label disagrees with its glyph id`);
  return {
    id: value.id,
    label: value.label,
    slot: actionSlot,
    glyphId: value.glyph_id,
    glyphLabel: value.glyph_label,
  };
}

/** Decode Salvage Lock's authenticated Lean-emitted legal-state closure. */
export function loadSalvageLockDescriptor(game, authority) {
  const descriptor = loadFiniteTableDescriptor(game, authority, {
    name: "Salvage Lock",
    gameId: "salvage-lock",
    ruleset: "salvage-v1",
    engineModule: "Dregg2.Games.PathOfAngels.SalvageLock",
    actionLimit: 12,
    maxActionLimit: 12,
    stateCount: 164,
    maxStates: 164,
    maxActions: SLOT_COUNT,
    refusalReasons: REFUSALS,
    parseView: salvageView,
    parseAction: salvageAction,
  });
  refuse(
    descriptor.actions.length === SLOT_COUNT && descriptor.actions.every((action, index) => action.id === ACTION_IDS[index] && action.slot === index),
    "salvage-action-domain",
    "Salvage Lock must emit all six slots in canonical order",
  );
  return descriptor;
}

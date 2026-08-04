import {
  boundedInteger,
  exactKeys,
  identifier,
  loadFiniteTableDescriptor,
} from "./finite-table-runtime.js";
import { ArtifactRefusal } from "./poag1.js";

const ACTIONS = Object.freeze([
  Object.freeze({ id: "alpha-beta", from: "alpha", to: "beta" }),
  Object.freeze({ id: "alpha-gamma", from: "alpha", to: "gamma" }),
  Object.freeze({ id: "beta-delta", from: "beta", to: "delta" }),
  Object.freeze({ id: "gamma-delta", from: "gamma", to: "delta" }),
]);
const ACTION_IDS = ACTIONS.map((action) => action.id);
const REFUSALS = Object.freeze(["solved", "turn-limit", "no-spares", "already-installed"]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function label(value, at) {
  refuse(typeof value === "string" && value.length >= 1 && value.length <= 64, "relay-label", `${at} is invalid`);
  return value;
}

function relayView(value, actionLimit, at) {
  exactKeys(value, ["installed", "spares", "turns", "solved"], at);
  refuse(Array.isArray(value.installed), "relay-installed", `${at}.installed must be an array`);
  const installed = value.installed.map((id, index) => identifier(id, "relay-installed", `${at}.installed[${index}] is invalid`));
  refuse(new Set(installed).size === installed.length, "relay-installed", `${at}.installed contains a duplicate`);
  refuse(installed.every((id) => ACTION_IDS.includes(id)), "relay-installed", `${at}.installed contains an unknown link`);
  const canonical = ACTION_IDS.filter((id) => installed.includes(id));
  refuse(canonical.every((id, index) => id === installed[index]), "relay-installed", `${at}.installed is not in canonical link order`);
  boundedInteger(value.spares, 0, 4, "relay-spares", `${at}.spares is invalid`);
  boundedInteger(value.turns, 0, actionLimit, "relay-turns", `${at}.turns is invalid`);
  refuse(typeof value.solved === "boolean", "relay-solved", `${at}.solved is invalid`);
  return Object.freeze({ installed: Object.freeze(installed), spares: value.spares, turns: value.turns, solved: value.solved });
}

function relayAction(value, at) {
  exactKeys(value, ["id", "label", "from", "to"], at);
  identifier(value.id, "relay-action", `${at}.id is invalid`);
  const index = ACTION_IDS.indexOf(value.id);
  refuse(index >= 0, "relay-action", `${at}.id is unknown`);
  const expected = ACTIONS[index];
  const expectedLabel = `Install ${expected.from[0].toUpperCase()}${expected.from.slice(1)}-${expected.to[0].toUpperCase()}${expected.to.slice(1)}`;
  refuse(value.from === expected.from && value.to === expected.to, "relay-action", `${at} endpoints disagree with its action id`);
  refuse(label(value.label, `${at}.label`) === expectedLabel, "relay-action", `${at}.label disagrees with its action id`);
  return { id: value.id, label: value.label, from: value.from, to: value.to };
}

/** Decode Relay Repair's authenticated Lean-emitted legal-state closure. */
export function loadRelayRepairDescriptor(game, authority) {
  const descriptor = loadFiniteTableDescriptor(game, authority, {
    name: "Relay Repair",
    gameId: "relay-repair",
    ruleset: "relay-v1",
    engineModule: "Dregg2.Games.PathOfAngels.RelayRepair",
    actionLimit: 4,
    maxActionLimit: 4,
    stateCount: 15,
    maxStates: 15,
    maxActions: 4,
    refusalReasons: REFUSALS,
    parseView: relayView,
    parseAction: relayAction,
  });
  refuse(
    descriptor.actions.length === ACTIONS.length && descriptor.actions.every((action, index) => action.id === ACTIONS[index].id),
    "relay-action-domain",
    "Relay Repair must emit all four links in canonical order",
  );
  return descriptor;
}

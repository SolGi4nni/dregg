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
  Object.freeze({ id: "delta-omega", from: "delta", to: "omega" }),
]);
const ACTION_IDS = ACTIONS.map((action) => action.id);
const REFUSALS = Object.freeze([
  "solved", "turn-limit", "already-installed", "no-spares", "stranded",
]);
const MAX_COST = 64;
const MAX_BOARDS = 64;

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function label(value, at) {
  refuse(typeof value === "string" && value.length >= 1 && value.length <= 64, "relay-label", `${at} is invalid`);
  return value;
}

/**
 * Decode the seeded damage board. This reads emitted data and checks its shape; it
 * does not price, route, or decide anything. The one rule checked here is the board
 * draw, and only because it makes the published board answerable to the run seed the
 * authority block already pins: a curator who swaps the board without swapping the
 * seed is refused.
 */
function relayInstance(game, at) {
  const block = game.instance;
  exactKeys(block, ["seed_byte", "modulus", "selected", "source", "sink", "boards"], at);
  boundedInteger(block.seed_byte, 0, 31, "relay-instance", `${at}.seed_byte is invalid`);
  boundedInteger(block.modulus, 1, MAX_BOARDS, "relay-instance", `${at}.modulus is invalid`);
  boundedInteger(block.selected, 0, block.modulus - 1, "relay-instance", `${at}.selected is invalid`);
  identifier(block.source, "relay-instance", `${at}.source is invalid`);
  identifier(block.sink, "relay-instance", `${at}.sink is invalid`);
  refuse(block.source !== block.sink, "relay-instance", `${at} routes the intake to itself`);
  refuse(
    ACTIONS.some((action) => action.from === block.source) && ACTIONS.some((action) => action.to === block.sink),
    "relay-instance",
    `${at} names endpoints outside the emitted link graph`,
  );

  refuse(typeof game.run_seed === "string" && game.run_seed.length === 64, "relay-instance", `${at} has no run seed to draw from`);
  const byte = Number.parseInt(game.run_seed.slice(2 * block.seed_byte, 2 * block.seed_byte + 2), 16);
  refuse(
    byte % block.modulus === block.selected,
    "relay-instance-draw",
    `${at} publishes a board the authenticated run seed does not draw`,
  );

  refuse(Array.isArray(block.boards) && block.boards.length === block.modulus, "relay-instance", `${at}.boards is invalid`);
  const boards = block.boards.map((board, index) => {
    exactKeys(board, ["index", "spares", "costs"], `${at}.boards[${index}]`);
    refuse(board.index === index, "relay-instance", `${at}.boards[${index}] is out of order`);
    boundedInteger(board.spares, 1, MAX_COST * ACTION_IDS.length, "relay-instance", `${at}.boards[${index}].spares is invalid`);
    exactKeys(board.costs, ACTION_IDS, `${at}.boards[${index}].costs`);
    for (const id of ACTION_IDS) {
      boundedInteger(board.costs[id], 1, MAX_COST, "relay-instance", `${at}.boards[${index}].costs.${id} is invalid`);
    }
    return Object.freeze({ index, spares: board.spares, costs: Object.freeze({ ...board.costs }) });
  });

  return Object.freeze({
    seedByte: block.seed_byte,
    modulus: block.modulus,
    selected: block.selected,
    source: block.source,
    sink: block.sink,
    boards: Object.freeze(boards),
    board: boards[block.selected],
  });
}

function relayView(instance, value, actionLimit, at) {
  exactKeys(value, ["installed", "spares", "turns", "solved", "stranded"], at);
  refuse(Array.isArray(value.installed), "relay-installed", `${at}.installed must be an array`);
  const installed = value.installed.map((id, index) => identifier(id, "relay-installed", `${at}.installed[${index}] is invalid`));
  refuse(new Set(installed).size === installed.length, "relay-installed", `${at}.installed contains a duplicate`);
  refuse(installed.every((id) => ACTION_IDS.includes(id)), "relay-installed", `${at}.installed contains an unknown link`);
  const canonical = ACTION_IDS.filter((id) => installed.includes(id));
  refuse(canonical.every((id, index) => id === installed[index]), "relay-installed", `${at}.installed is not in canonical link order`);
  boundedInteger(value.spares, 0, instance.board.spares, "relay-spares", `${at}.spares is invalid`);
  boundedInteger(value.turns, 0, actionLimit, "relay-turns", `${at}.turns is invalid`);
  refuse(typeof value.solved === "boolean", "relay-solved", `${at}.solved is invalid`);
  refuse(typeof value.stranded === "boolean", "relay-stranded", `${at}.stranded is invalid`);
  refuse(!(value.solved && value.stranded), "relay-stranded", `${at} is both routed and stranded`);
  return Object.freeze({
    installed: Object.freeze(installed),
    spares: value.spares,
    turns: value.turns,
    solved: value.solved,
    stranded: value.stranded,
  });
}

function relayAction(instance, value, at) {
  exactKeys(value, ["id", "label", "from", "to"], at);
  identifier(value.id, "relay-action", `${at}.id is invalid`);
  const index = ACTION_IDS.indexOf(value.id);
  refuse(index >= 0, "relay-action", `${at}.id is unknown`);
  const expected = ACTIONS[index];
  const expectedLabel = `Install ${expected.from[0].toUpperCase()}${expected.from.slice(1)}-${expected.to[0].toUpperCase()}${expected.to.slice(1)}`;
  refuse(value.from === expected.from && value.to === expected.to, "relay-action", `${at} endpoints disagree with its action id`);
  refuse(label(value.label, `${at}.label`) === expectedLabel, "relay-action", `${at}.label disagrees with its action id`);
  return { id: value.id, label: value.label, from: value.from, to: value.to, cost: instance.board.costs[value.id] };
}

/** Decode Relay Repair's authenticated Lean-emitted legal-state closure. */
export function loadRelayRepairDescriptor(game, authority) {
  refuse(game !== null && typeof game === "object" && !Array.isArray(game), "relay-shape", "Relay Repair descriptor must be an object");
  const instance = relayInstance(game, "Relay Repair instance");
  const descriptor = loadFiniteTableDescriptor(game, authority, {
    name: "Relay Repair",
    gameId: "relay-repair",
    ruleset: "relay-v3",
    disclosure: "per-run-open",
    engineModule: "Dregg2.Games.PathOfAngels.RelayRepair",
    actionLimit: 3,
    maxActionLimit: 3,
    stateCount: 25,
    maxStates: 25,
    maxActions: 5,
    extraKeys: ["instance"],
    refusalReasons: REFUSALS,
    parseInstance: () => instance,
    parseView: (value, actionLimit, at) => relayView(instance, value, actionLimit, at),
    parseAction: (value, at) => relayAction(instance, value, at),
  });
  refuse(
    descriptor.actions.length === ACTIONS.length && descriptor.actions.every((action, index) => action.id === ACTIONS[index].id),
    "relay-action-domain",
    "Relay Repair must emit all five links in canonical order",
  );
  return descriptor;
}

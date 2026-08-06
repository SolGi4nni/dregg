import {
  boundedInteger,
  exactKeys,
  identifier,
  loadFiniteTableDescriptor,
  loadHiddenInstanceDeclaration,
} from "./finite-table-runtime.js";
import { ArtifactRefusal } from "./poag1.js";

/**
 * Relay Repair after the instance/rules split.
 *
 * ⚠ What this file no longer reads, because the descriptor no longer carries it:
 * `run_seed`, `instance.seed_byte` and `instance.selected`. Together they were a
 * published derivation of the live board — one modulo of one byte of a seed
 * printed in the same file — so a reader could name the board before playing.
 * The old loader checked that the published `selected` agreed with the published
 * seed, which confirmed only that two copies of the answer matched.
 *
 * What ships instead is all eight boards AND all eight complete machines. The
 * family states every rule and distinguishes no member. The live board is drawn
 * per (slot, mission, player) from a curator-held secret.
 *
 * Relay's disclosure is `per-run-open`: the board is opened when the run starts,
 * because spare counts and link prices are the whole game and a player who
 * cannot see them is not playing. Hiding it would buy nothing — the commitment,
 * not the concealment, is what stops the host picking a board after the fact.
 */

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
 * Decode the emitted board family. This reads data and checks its shape; it does
 * not price, route or decide anything, and it no longer checks a draw, because
 * there is no published draw left to check.
 */
function relayInstance(game, at) {
  const block = game.instance;
  exactKeys(block, ["modulus", "source", "sink", "draw", "boards"], at);
  boundedInteger(block.modulus, 2, MAX_BOARDS, "relay-instance", `${at}.modulus is invalid`);
  identifier(block.source, "relay-instance", `${at}.source is invalid`);
  identifier(block.sink, "relay-instance", `${at}.sink is invalid`);
  refuse(block.source !== block.sink, "relay-instance", `${at} routes the intake to itself`);
  refuse(
    ACTIONS.some((action) => action.from === block.source) && ACTIONS.some((action) => action.to === block.sink),
    "relay-instance",
    `${at} names endpoints outside the emitted link graph`,
  );

  const declaration = loadHiddenInstanceDeclaration(block.draw, "per-run-open", `${at} draw`);

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

  // Two boards with identical prices and spares would be one board wearing two
  // indices, and would shrink the space the draw ranges over without saying so.
  const shapes = new Set(boards.map((board) => JSON.stringify([board.spares, board.costs])));
  refuse(shapes.size === boards.length, "relay-instance", `${at}.boards contains two identical boards, so the family is smaller than it claims`);

  return Object.freeze({
    modulus: block.modulus,
    source: block.source,
    sink: block.sink,
    draw: declaration,
    boards: Object.freeze(boards),
  });
}

function relayView(instance, value, actionLimit, at, board) {
  exactKeys(value, ["installed", "spares", "turns", "solved", "stranded"], at);
  refuse(Array.isArray(value.installed), "relay-installed", `${at}.installed must be an array`);
  const installed = value.installed.map((id, index) => identifier(id, "relay-installed", `${at}.installed[${index}] is invalid`));
  refuse(new Set(installed).size === installed.length, "relay-installed", `${at}.installed contains a duplicate`);
  refuse(installed.every((id) => ACTION_IDS.includes(id)), "relay-installed", `${at}.installed contains an unknown link`);
  const canonical = ACTION_IDS.filter((id) => installed.includes(id));
  refuse(canonical.every((id, index) => id === installed[index]), "relay-installed", `${at}.installed is not in canonical link order`);
  boundedInteger(value.spares, 0, instance.boards[board].spares, "relay-spares", `${at}.spares is invalid`);
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

/**
 * An action row is presentation only. Costs are per board, so they are read out
 * of the emitted board rather than off the action, and `relayLinkCost` is how a
 * controller asks for one.
 */
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

/** Decode Relay Repair's authenticated Lean-emitted board family. */
export function loadRelayRepairDescriptor(game, authority) {
  refuse(game !== null && typeof game === "object" && !Array.isArray(game), "relay-shape", "Relay Repair descriptor must be an object");
  let instance = null;
  const descriptor = loadFiniteTableDescriptor(game, authority, {
    name: "Relay Repair",
    gameId: "relay-repair",
    ruleset: "relay-v3",
    disclosure: "per-run-open",
    engineModule: "Dregg2.Games.PathOfAngels.RelayRepair",
    actionLimit: 3,
    maxActionLimit: 3,
    // Per-board state counts are a function of that board's prices, so pinning
    // them here would be re-deriving the rule. What is pinned is the family
    // size, the link set, and that every machine is complete and closed.
    maxStates: 64,
    maxActions: 5,
    allowsResolve: false,
    refusalReasons: REFUSALS,
    parseInstance: (value, at) => { instance = relayInstance(value, at); return instance; },
    familyKeys: (parsed) => Array.from({ length: parsed.modulus }, (_, index) => index),
    parseView: (value, actionLimit, at, board) => relayView(instance, value, actionLimit, at, board),
    parseAction: (value, at) => relayAction(value, at),
  });
  refuse(
    descriptor.actions.length === ACTIONS.length && descriptor.actions.every((action, index) => action.id === ACTIONS[index].id),
    "relay-action-domain",
    "Relay Repair must emit all five links in canonical order",
  );
  return descriptor;
}

/** The emitted price of a link on one board. A lookup, not a calculation. */
export function relayLinkCost(descriptor, board, actionId) {
  const row = descriptor.instance.boards[board];
  refuse(row, "relay-board", "the run names a board the descriptor does not emit");
  const cost = row.costs[actionId];
  refuse(cost !== undefined, "relay-board", "the emitted board does not price this link");
  return cost;
}

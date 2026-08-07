/**
 * Deck Descent — decode the authenticated Lean-emitted descent table.
 *
 * ⚑ THE SAME ENGINE AS SALVAGE AND ARTIFICER, NOT A THIRD ONE. Descent is a
 * `parametric` descriptor: one machine, 1924 states, and 316 rows that do not
 * have one successor because the answer depends on a board nobody in this
 * browser holds. That is precisely the shape `finite-table-runtime.js` exists
 * for, so every verdict, successor, refusal and view below comes through it and
 * nothing in this file walks a transition. What is HERE is the part the shared
 * engine cannot know: the `shaft` — the public rules of the mine — and the eight
 * practice boards.
 *
 * ## What this file derives, and why each derivation is a LOOKUP
 *
 * Three things, and every one of them is a second opinion about a number a
 * player is shown, computed from fields the descriptor already publishes:
 *
 *   1. `capacity` must be `base_capacity - damage`, and `turns` must be
 *      `air − air_budget`'s complement. Both are emitted AND derivable, so the
 *      two are compared and a disagreement is a refusal. A client that showed a
 *      player the wrong number of turns left would be lying about the clock, and
 *      the clock binds exactly (the design gate measures slack 0).
 *
 *   2. WHICH CHAMBER a `resolve` row is asking about. Read TWICE and compared:
 *      once off the row's two branch views — they differ in exactly one
 *      chamber's `lore`, and that chamber is the question — and once off the
 *      action's emitted `line` and the shaft's child maps, which is the reading
 *      `DeckDescentEmit.line_determines_target` PROVES is the kernel's
 *      `Action.target`. Two sources, checked against each other on all 316 rows
 *      at load. Neither is a rule this file invented.
 *
 *   3. That `on_match` IS the sound branch. The emitter says so in a docblock,
 *      and a docblock is not a check: the branch views state it themselves — the
 *      questioned chamber reads `sound` on `on_match` and `flooded` on
 *      `on_mismatch` — so it is verified here rather than believed.
 *
 * ## What it never does
 *
 * It never decides whether a move is legal, where it lands, or whether a run is
 * doomed. `doomed` in particular is EMITTED and rendered verbatim: it is a fact
 * about what the player knows (`reachableBankB` assumes every dark chamber
 * sound), and a browser that recomputed it would be carrying the second copy of
 * the rules this whole boundary exists to prevent.
 */
import { ArtifactRefusal } from "./poag1.js";
import {
  boundedInteger,
  exactKeys,
  identifier,
  loadFiniteTableDescriptor,
  loadHiddenInstanceDeclaration,
} from "./finite-table-runtime.js";

const GAME_ID = "deck-descent";
const RULESET = "descent-v1";
const ENGINE = "Dregg2.Games.PathOfAngels.DeckDescent";
/** `DeckDescent.AIR`: nine actions, and the design gate measures slack 0. */
const ACTION_LIMIT = 9;
const STATE_COUNT = 1924;
const ACTION_COUNT = 9;
const KINDS = Object.freeze(["survey", "shore", "descend", "lift", "ascend", "extract"]);
const LINES = Object.freeze(["main", "spur", "here"]);
/** ⚠ Terminal is `run-banked`, not `solved`. A descent ends by getting OUT. */
const TERMINAL_REASON = "run-banked";
/**
 * `DeckDescent.refusalReason`'s complete vocabulary — the same thirteen
 * `scripts/poa-design-gate.py` declares.
 *
 * ⚠ THIRTEEN, not the twelve the current table actually produces. `no-air` is
 * reachable in the kernel and unreachable in the emitted closure (a run out of air
 * is already `run-doomed`, and `refusalReason` tests doom first), so pinning the
 * OBSERVED twelve would make this client refuse a legal table the day a budget
 * changes. The declared vocabulary is the contract; the observed subset is a
 * measurement of today's numbers.
 */
const REFUSALS = Object.freeze([
  "already-read", "already-safe", "at-the-hatch", "chamber-emptied", "no-air",
  "no-passage", "no-shoring", "not-at-the-hatch", "not-in-a-chamber",
  "over-capacity", "run-banked", "run-doomed", "short-sling",
]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function text(value, at, max = 400) {
  refuse(typeof value === "string" && value.length >= 1 && value.length <= max, "descent-copy", `${at} is invalid`);
  return value;
}

/** A per-chamber count map, exactly keyed by the chambers. */
function countMap(value, chambers, at, max) {
  exactKeys(value, chambers, at);
  const out = Object.create(null);
  for (const chamber of chambers) {
    boundedInteger(value[chamber], 0, max, "descent-count", `${at}.${chamber} is invalid`);
    out[chamber] = value[chamber];
  }
  return Object.freeze(out);
}

/**
 * The shaft: the public rules, true on all eight boards.
 *
 * ⚑ This block is checked as hard as the table is, because it is what the whole
 * board is DRAWN from — the map a player navigates, how far from the hatch they
 * are standing, and how many relics each chamber still owes them. A topology
 * that disagreed with itself would put a player somewhere the table cannot go.
 */
function descentShaft(value, at) {
  exactKeys(
    value,
    ["budgets", "nodes", "surface", "chambers", "relic_count", "parent", "main_child",
     "spur_child", "crossings_to_hatch", "crossings", "forfeit_order", "lore",
     "damaging_lore", "air_per_action", "reserve"],
    at,
  );
  const budgets = value.budgets;
  exactKeys(budgets, ["air", "shoring", "base_capacity", "bank_target"], `${at}.budgets`);
  for (const field of ["air", "shoring", "base_capacity", "bank_target"]) {
    boundedInteger(budgets[field], 0, 64, "descent-budget", `${at}.budgets.${field} is invalid`);
  }
  refuse(budgets.air === ACTION_LIMIT, "descent-budget", `${at}.budgets.air disagrees with its Lean ruleset`);
  refuse(budgets.base_capacity >= 1, "descent-budget", `${at} declares a sling that holds nothing`);
  refuse(budgets.bank_target >= 1, "descent-budget", `${at} declares a run that banks nothing`);
  refuse(value.air_per_action === 1, "descent-budget", `${at} prices an action at something other than one unit of air`);

  const nodes = value.nodes.map((node, index) => identifier(node, "descent-topology", `${at}.nodes[${index}] is invalid`));
  refuse(new Set(nodes).size === nodes.length, "descent-topology", `${at} names a node twice`);
  const surface = identifier(value.surface, "descent-topology", `${at}.surface is invalid`);
  refuse(nodes.includes(surface), "descent-topology", `${at}.surface is not one of the nodes`);
  const chambers = value.chambers.map((chamber, index) => identifier(chamber, "descent-topology", `${at}.chambers[${index}] is invalid`));
  refuse(
    chambers.length === nodes.length - 1 && chambers.every((chamber) => nodes.includes(chamber)) && !chambers.includes(surface),
    "descent-topology",
    `${at} chambers and surface do not exhaust the nodes`,
  );

  const relicCount = countMap(value.relic_count, chambers, `${at}.relic_count`, 16);
  for (const chamber of chambers) {
    refuse(relicCount[chamber] >= 1, "descent-topology", `${at}.relic_count says ${chamber} holds nothing to lift`);
  }

  // ⚑ The east spur holds TWO. If it ever holds one again the two spurs are a
  // mirror, the T-junction stops being a decision, and the game loses 215 of its
  // outcome-changing forks. That is a design fact and it is checked, not assumed.
  refuse(
    Object.values(relicCount).some((count) => count !== relicCount[chambers[0]]),
    "descent-topology",
    `${at}.relic_count gives every chamber the same number of relics, so the spurs ` +
      `are a relabelling of each other and the junction is a labelled corridor`,
  );

  exactKeys(value.parent, chambers, `${at}.parent`);
  const parent = Object.create(null);
  for (const chamber of chambers) {
    refuse(nodes.includes(value.parent[chamber]), "descent-topology", `${at}.parent.${chamber} is not a node`);
    parent[chamber] = value.parent[chamber];
  }
  const childMap = (raw, label) => {
    refuse(object(raw), "descent-topology", `${label} must be an object`);
    const out = Object.create(null);
    for (const [node, child] of Object.entries(raw)) {
      refuse(nodes.includes(node) && chambers.includes(child), "descent-topology", `${label} names a node or chamber that is not declared`);
      refuse(parent[child] === node, "descent-topology", `${label}.${node} claims ${child}, whose declared parent is ${parent[child]}`);
      out[node] = child;
    }
    return Object.freeze(out);
  };
  const mainChild = childMap(value.main_child, `${at}.main_child`);
  const spurChild = childMap(value.spur_child, `${at}.spur_child`);

  const dist = new Map();
  refuse(Array.isArray(value.crossings), "descent-topology", `${at}.crossings must be an array`);
  for (const entry of value.crossings) {
    refuse(Array.isArray(entry) && entry.length === 3, "descent-topology", `${at}.crossings has an entry that is not a [from, to, cost] triple`);
    const [from, to, cost] = entry;
    refuse(nodes.includes(from) && nodes.includes(to), "descent-topology", `${at}.crossings names an undeclared node`);
    boundedInteger(cost, 0, 64, "descent-topology", `${at}.crossings ${from}->${to} is invalid`);
    refuse(!dist.has(`${from}|${to}`), "descent-topology", `${at}.crossings names ${from}->${to} twice`);
    dist.set(`${from}|${to}`, cost);
  }
  for (const from of nodes) {
    for (const to of nodes) {
      const cost = dist.get(`${from}|${to}`);
      refuse(cost !== undefined, "descent-topology", `${at}.crossings has no entry for ${from} -> ${to}`);
      refuse(from !== to || cost === 0, "descent-topology", `${at}.crossings charges ${from} for standing still`);
      refuse(cost === dist.get(`${to}|${from}`), "descent-topology", `${at}.crossings is not symmetric at ${from}/${to}`);
    }
  }
  exactKeys(value.crossings_to_hatch, nodes, `${at}.crossings_to_hatch`);
  const toHatch = Object.create(null);
  for (const node of nodes) {
    refuse(
      value.crossings_to_hatch[node] === dist.get(`${node}|${surface}`),
      "descent-topology",
      `${at}.crossings_to_hatch and ${at}.crossings disagree at ${node}`,
    );
    toHatch[node] = value.crossings_to_hatch[node];
  }

  const forfeitOrder = value.forfeit_order.map((chamber, index) => identifier(chamber, "descent-topology", `${at}.forfeit_order[${index}] is invalid`));
  refuse(
    forfeitOrder.length === chambers.length && chambers.every((chamber) => forfeitOrder.includes(chamber)),
    "descent-topology",
    `${at}.forfeit_order is not a permutation of the chambers`,
  );

  const lore = value.lore.map((reading, index) => identifier(reading, "descent-lore", `${at}.lore[${index}] is invalid`));
  refuse(new Set(lore).size === lore.length && lore.length >= 3, "descent-lore", `${at}.lore is not a distinct reading alphabet`);
  const damaging = value.damaging_lore.map((reading, index) => {
    refuse(lore.includes(reading), "descent-lore", `${at}.damaging_lore[${index}] is not a declared reading`);
    return reading;
  });
  // No damaging reading means no crossing can ever cost a body, and the shaft
  // holds no risk at all — a descent that cannot hurt is not a descent.
  refuse(damaging.length >= 1 && damaging.length < lore.length, "descent-lore", `${at}.damaging_lore is empty or is every reading`);

  return Object.freeze({
    air: budgets.air,
    shoring: budgets.shoring,
    baseCapacity: budgets.base_capacity,
    bankTarget: budgets.bank_target,
    nodes: Object.freeze(nodes),
    surface,
    chambers: Object.freeze(chambers),
    relicCount,
    parent: Object.freeze(parent),
    mainChild,
    spurChild,
    crossingsToHatch: Object.freeze(toHatch),
    forfeitOrder: Object.freeze(forfeitOrder),
    lore: Object.freeze(lore),
    damaging: Object.freeze(damaging),
    reserve: text(value.reserve, `${at}.reserve`),
  });
}

/**
 * The practice family: ALL EIGHT boards, and no answer.
 *
 * ⚑ Publishing the family is not publishing the instance, and here the family
 * was public before this block existed. `shaft` names three chambers and two
 * readings that a passage can have; every `resolve` row carries both successors;
 * `scripts/poa-design-gate.py` rebuilds all eight boards from exactly that and
 * walks them, reading nothing from this block. So the block adds no bits — it
 * replaces a RULE a client would otherwise carry ("each chamber is independently
 * sound or flooded, so there are two-to-the-chambers of them") with a lookup.
 *
 * ⚠ Which board a JUDGED run drew is not here and cannot be: it comes from
 * `HiddenInstance` under purpose tag 1 off a slot secret this artifact does not
 * contain. A practice run picks a row locally, is `scored:false` here and
 * `mode:"practice"` in its transcript, and is a different object at the byte
 * level from a judged one.
 */
function descentPractice(value, shaft, at) {
  exactKeys(value, ["instance_space", "instance_shape", "scored", "boards"], at);
  refuse(value.scored === false, "descent-practice", `${at} declares practice runs scored`);
  text(value.instance_shape, `${at}.instance_shape`, 200);
  boundedInteger(value.instance_space, 2, 4096, "descent-practice", `${at}.instance_space is invalid`);
  refuse(Array.isArray(value.boards), "descent-practice", `${at}.boards must be an array`);
  refuse(
    value.boards.length === value.instance_space,
    "descent-practice",
    `${at} emits ${value.boards.length} boards for a declared space of ${value.instance_space}`,
  );
  const seen = new Set();
  const boards = value.boards.map((board, index) => {
    exactKeys(board, shaft.chambers, `${at}.boards[${index}]`);
    const row = Object.create(null);
    for (const chamber of shaft.chambers) {
      refuse(shaft.lore.includes(board[chamber]), "descent-practice", `${at}.boards[${index}].${chamber} is not a declared reading`);
      row[chamber] = board[chamber];
    }
    const shape = shaft.chambers.map((chamber) => row[chamber]).join("|");
    // ⚠ A duplicate is a LEAK dressed as a count: eight rows naming seven boards
    // tells a reader one board is twice as likely as the others.
    refuse(!seen.has(shape), "descent-practice", `${at}.boards[${index}] repeats a board the family already names`);
    seen.add(shape);
    return Object.freeze(row);
  });
  return Object.freeze({
    scored: false,
    instanceSpace: value.instance_space,
    instanceShape: value.instance_shape,
    boards: Object.freeze(boards),
  });
}

function descentViewFactory(shaft) {
  return function descentView(value, actionLimit, at) {
    exactKeys(
      value,
      ["node", "air", "shoring", "damage", "capacity", "lore", "taken", "sling",
       "banked", "turns", "doomed", "solved"],
      at,
    );
    refuse(shaft.nodes.includes(value.node), "descent-view", `${at}.node is not a declared node`);
    boundedInteger(value.air, 0, shaft.air, "descent-view", `${at}.air is invalid`);
    boundedInteger(value.shoring, 0, shaft.shoring, "descent-view", `${at}.shoring is invalid`);
    boundedInteger(value.damage, 0, shaft.baseCapacity, "descent-view", `${at}.damage is invalid`);
    boundedInteger(value.capacity, 0, shaft.baseCapacity, "descent-view", `${at}.capacity is invalid`);
    boundedInteger(value.turns, 0, actionLimit, "descent-view", `${at}.turns is invalid`);
    // The two second opinions. Both numbers are on screen in front of a player
    // making a decision the clock binds exactly, so both are recomputed.
    refuse(value.capacity === shaft.baseCapacity - value.damage, "descent-view", `${at}.capacity disagrees with the damage it carries`);
    refuse(value.turns === shaft.air - value.air, "descent-view", `${at}.turns disagrees with the air it has left`);

    exactKeys(value.lore, shaft.chambers, `${at}.lore`);
    const lore = Object.create(null);
    for (const chamber of shaft.chambers) {
      refuse(shaft.lore.includes(value.lore[chamber]), "descent-view", `${at}.lore.${chamber} is not a declared reading`);
      lore[chamber] = value.lore[chamber];
    }
    const taken = countMap(value.taken, shaft.chambers, `${at}.taken`, 16);
    const sling = countMap(value.sling, shaft.chambers, `${at}.sling`, 16);
    let carried = 0;
    for (const chamber of shaft.chambers) {
      refuse(taken[chamber] <= shaft.relicCount[chamber], "descent-view", `${at}.taken.${chamber} exceeds what the chamber holds`);
      // A relic in the sling has left the deck, so the sling can never hold more
      // of a chamber than the run has lifted out of it.
      refuse(sling[chamber] <= taken[chamber], "descent-view", `${at}.sling.${chamber} carries relics the run never lifted`);
      carried += sling[chamber];
    }
    refuse(carried <= value.capacity, "descent-view", `${at}.sling carries more than the capacity it declares`);
    for (const flag of ["banked", "doomed", "solved"]) {
      refuse(typeof value[flag] === "boolean", "descent-view", `${at}.${flag} is invalid`);
    }
    refuse(value.solved === value.banked, "descent-view", `${at}.solved disagrees with its own bank`);
    refuse(!(value.doomed && value.banked), "descent-view", `${at} is both banked and doomed`);
    refuse(!value.banked || value.node === shaft.surface, "descent-view", `${at} banks a run that is not at the surface`);
    refuse(!value.banked || carried >= shaft.bankTarget, "descent-view", `${at} banks a run short of the target`);
    return Object.freeze({
      node: value.node,
      air: value.air,
      shoring: value.shoring,
      damage: value.damage,
      capacity: value.capacity,
      lore: Object.freeze(lore),
      taken,
      sling,
      carried,
      banked: value.banked,
      turns: value.turns,
      doomed: value.doomed,
      solved: value.solved,
    });
  };
}

function descentAction(value, at) {
  exactKeys(value, ["id", "label", "kind", "line"], at);
  identifier(value.id, "descent-action", `${at}.id is invalid`);
  text(value.label, `${at}.label`, 96);
  refuse(KINDS.includes(value.kind), "descent-action", `${at}.kind is not a declared verb`);
  refuse(LINES.includes(value.line), "descent-action", `${at}.line is not a declared line`);
  return { id: value.id, label: value.label, kind: value.kind, line: value.line };
}

/**
 * Where an action reaches from a node — the reading
 * `DeckDescentEmit.line_determines_target` proves is the kernel's `Action.target`.
 * `here` acts where the body stands and reaches nothing.
 */
export function targetOf(shaft, node, action) {
  if (action.line === "spur") return shaft.spurChild[node] ?? null;
  if (action.line === "main") return shaft.mainChild[node] ?? null;
  return null;
}

/**
 * ⚑ WHAT EVERY ORACLE ROW IS ASKING, DERIVED TWICE AND COMPARED.
 *
 * A `resolve` row's two branch views differ in exactly one chamber's `lore`, and
 * that chamber is the passage the row is about to read. That is one derivation.
 * The other is `targetOf` — the action's `line` against the shaft's child maps.
 * They are independent (one reads state views, the other reads topology and
 * action metadata) and they must agree on every row, which is checked here over
 * all of them at load rather than trusted at play.
 *
 * The by-product is the question map a practice run answers from: the question
 * is a function of WHERE YOU STAND and WHAT YOU DO, not of how you got there,
 * and that too is checked — two rows at the same node under the same action that
 * asked about different chambers would mean the game reads a bit that depends on
 * history, and no client could answer either.
 */
function descentQuestions(descriptor, shaft) {
  const [member] = descriptor.members;
  const view = new Map(member.states.map((state) => [state.id, state.view]));
  const questions = new Map();
  let rows = 0;
  for (const row of member.transitions) {
    if (row.verdict !== "resolve") continue;
    rows += 1;
    const here = view.get(row.state);
    const match = view.get(row.on_match);
    const mismatch = view.get(row.on_mismatch);
    const differing = shaft.chambers.filter((chamber) => match.lore[chamber] !== mismatch.lore[chamber]);
    refuse(
      differing.length === 1,
      "descent-oracle",
      `${row.state}/${row.action} defers to the instance and its two branches differ ` +
        `in ${differing.length} chambers' readings, so what it is asking cannot be read off it`,
    );
    const [chamber] = differing;
    // `on_match` is the SOUND branch. The emitter documents it; the views state
    // it; this is where the documentation stops being taken on trust.
    refuse(
      match.lore[chamber] !== here.lore[chamber] && mismatch.lore[chamber] !== here.lore[chamber],
      "descent-oracle",
      `${row.state}/${row.action} names a branch that reads ${chamber} the way it already reads`,
    );
    refuse(
      !shaft.damaging.includes(match.lore[chamber]) && shaft.damaging.includes(mismatch.lore[chamber]),
      "descent-oracle",
      `${row.state}/${row.action} puts the damaging reading on on_match; every other row ` +
        `puts it on on_mismatch, and a client answering them uniformly would invert this one`,
    );
    const reached = targetOf(shaft, here.node, descriptor.actions.find((action) => action.id === row.action));
    refuse(
      reached === chamber,
      "descent-oracle",
      `${row.state}/${row.action} asks about ${chamber}; its emitted line reaches ${reached}`,
    );
    const key = `${here.node}|${row.action}`;
    const known = questions.get(key);
    refuse(
      known === undefined || (known.chamber === chamber && known.match === match.lore[chamber]),
      "descent-oracle",
      `standing at ${here.node}, ${row.action} asks about ${chamber} on one row and ` +
        `${known?.chamber} on another, so what it reads depends on how the run got there`,
    );
    questions.set(key, Object.freeze({ chamber, match: match.lore[chamber], mismatch: mismatch.lore[chamber] }));
  }
  refuse(rows > 0, "descent-oracle", "no emitted row defers to the instance, so the board cannot affect play");
  return Object.freeze({ questions, rows });
}

/**
 * ⚑ THE PRACTICE ORACLE IS TOTAL — and this is the check without which it fails
 * SILENTLY rather than loudly.
 *
 * The oracle answers `board[chamber] === question.match ? "match" : "mismatch"`.
 * A board whose reading of that chamber were NEITHER of the two the row offers —
 * `dark`, say, or `shored` — would fall through the ternary and be answered
 * `mismatch`, which is a wrong answer that looks exactly like a right one. So
 * every question is held against every board of the family before a rehearsal can
 * start: each board must read every questioned chamber as one of the two readings
 * that question names, and both readings must actually occur across the family —
 * a family in which no board ever floods the east spur is a family in which the
 * spur's bit is not a bit.
 */
function practiceAnswersEveryQuestion(questions, practice, at) {
  for (const [key, question] of questions) {
    const readings = new Set(practice.boards.map((board) => board[question.chamber]));
    for (const reading of readings) {
      refuse(
        reading === question.match || reading === question.mismatch,
        "descent-practice",
        `${at} reads ${question.chamber} as ${reading} on some board, and the row at ` +
          `${key} offers only ${question.match} or ${question.mismatch}, so a rehearsal on ` +
          `that board would be answered by a fall-through rather than by the family`,
      );
    }
    refuse(
      readings.has(question.match) && readings.has(question.mismatch),
      "descent-practice",
      `${at} never reads ${question.chamber} both ways, so the bit the row at ${key} ` +
        `spends a unit of air to buy is not a bit`,
    );
  }
}

/** Decode Deck Descent's authenticated Lean-emitted parametric table. */
export function loadDeckDescentDescriptor(game, authority) {
  let shaft = null;
  let practice = null;
  const base = loadFiniteTableDescriptor(game, authority, {
    name: "Deck Descent",
    gameId: GAME_ID,
    ruleset: RULESET,
    disclosure: "oracle-only",
    engineModule: ENGINE,
    actionLimit: ACTION_LIMIT,
    maxActionLimit: ACTION_LIMIT,
    stateCount: STATE_COUNT,
    maxStates: STATE_COUNT,
    maxActions: ACTION_COUNT,
    allowsResolve: true,
    extraKeys: ["shaft", "practice"],
    refusalReasons: REFUSALS,
    terminalReason: TERMINAL_REASON,
    parseInstance: (value, at) => {
      shaft = descentShaft(value.shaft, `${at} shaft`);
      practice = descentPractice(value.practice, shaft, `${at} practice family`);
      return Object.freeze({
        draw: loadHiddenInstanceDeclaration(value.instance, "oracle-only", at),
        shaft,
        practice,
      });
    },
    parseView: (value, actionLimit, at) => descentViewFactory(shaft)(value, actionLimit, at),
    parseAction: (value, at) => descentAction(value, at),
  });
  refuse(base.actions.length === ACTION_COUNT, "descent-actions", "Deck Descent emits a verb set it does not declare");
  const { questions, rows } = descentQuestions(base, shaft);
  practiceAnswersEveryQuestion(questions, practice, "Deck Descent practice family");
  // ⚠ `shaft` and `practice` live under `instance` and NOWHERE ELSE, exactly where
  // Salvage and Artificer put theirs. A convenience copy at the top level would be
  // two names for one emitted block, which is the shape that agrees today.
  // `rows` and `questions` are DERIVED — an index and a checked reading — so they
  // are not a second copy of anything the descriptor carries.
  const index = new Map(base.members[0].transitions.map((row) => [`${row.state}|${row.action}`, row]));
  return Object.freeze({ ...base, rows: index, questions, oracleRows: rows });
}

/** The emitted row for what a run is about to do. A lookup, not a decision. */
export function rowFor(descriptor, run, actionId) {
  return descriptor.rows.get(`${run.stateId}|${actionId}`);
}

/**
 * The practice oracle: TWO LOOKUPS, never a computation.
 *
 * The question is read off the question map built at load — which chamber this
 * row is about, and which reading `on_match` means — and the answer is read off
 * one row of the emitted practice family. Nothing about what a match DOES is
 * consulted; `on_match`/`on_mismatch` stay in the table, so a rehearsal walks
 * exactly the rows a judged run walks.
 *
 * ⚠ `boardIndex` is a LOCAL, UNSCORED choice out of the published eight. It is
 * not `HiddenInstance.boardFromRunSeed` and must never become it: reproducing the
 * Lean draw here would put a second copy of it in a browser that has no secret to
 * feed it, and would make a rehearsal look like a judged run.
 */
export function descentPracticeOracle(descriptor, boardIndex) {
  const board = descriptor.instance.practice.boards[boardIndex];
  refuse(board, "descent-practice", "the practice run names a board outside the published family");
  return (view, actionId) => {
    const question = descriptor.questions.get(`${view.node}|${actionId}`);
    refuse(
      question,
      "descent-practice",
      `the practice oracle was asked about ${actionId} at ${view.node}, where no emitted row defers to the instance`,
    );
    return board[question.chamber] === question.match ? "match" : "mismatch";
  };
}

/**
 * How far the body is from air, and what a crossing home would cost it — both
 * read straight out of `shaft.crossings_to_hatch`. This is the number a player
 * is deciding against every turn and it is not derived from a rule; it is the
 * emitted distance table indexed by the emitted node.
 */
export function distanceHome(descriptor, view) {
  return descriptor.instance.shaft.crossingsToHatch[view.node];
}

/**
 * What the shaft still owes, per chamber: how many relics are left in it. Read
 * off `relic_count` minus the emitted `taken` — a subtraction over two published
 * counts, which is what the chamber pills on the board render.
 */
export function chamberStanding(descriptor, view) {
  const shaft = descriptor.instance.shaft;
  return Object.freeze(shaft.chambers.map((chamber) => Object.freeze({
    chamber,
    lore: view.lore[chamber],
    held: shaft.relicCount[chamber] - view.taken[chamber],
    carried: view.sling[chamber],
    total: shaft.relicCount[chamber],
    damaging: shaft.damaging.includes(view.lore[chamber]),
    here: view.node === chamber,
    crossingsHome: shaft.crossingsToHatch[chamber],
  })));
}

export { ACTION_LIMIT, STATE_COUNT, REFUSALS, TERMINAL_REASON, GAME_ID };

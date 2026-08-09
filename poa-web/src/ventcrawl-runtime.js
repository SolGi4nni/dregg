import { ArtifactRefusal } from "./poag1.js";
import { loadHiddenInstanceDeclaration, refuseNamedInstance } from "./hidden-instance.js";

/**
 * Vent Crawl — push-your-luck over a PUBLISHED hazard and a HIDDEN shared table.
 *
 * ⚠ The split that matters here is not the one the other games have. Signal,
 * Salvage and Relay hide the thing you are trying to find. Vent Crawl hides the
 * REWARD and publishes the RISK in full:
 *
 *   * `vent.flood_below` gives, per rung, how many of `vent.faces` outcomes drown
 *     a crawler entering it. Every wager row repeats the number for the rung it
 *     is about to enter, and every state view repeats it again as
 *     `next_flood_below`. A client renders exact odds before every choice, and
 *     `ventCrawlTableRefinesKernel` on the Lean side proves the number a row
 *     publishes IS the number the transition compares against.
 *   * `vent.veins` gives ALL FOUR yield ladders. Which one is running today is a
 *     per-slot draw off the committed slot secret and is in no artifact.
 *
 * So this file derives NO odds and NO payout. It reads them.
 *
 * Two run modes, and they are not interchangeable:
 *
 *   PRACTICE  the client picks a vein out of `vent.veins` and rolls its own rung
 *             draws with `crypto.getRandomValues`. Nothing here touches the live
 *             slot secret and nothing here is scored. ⚠ The pick is deliberately
 *             NOT the Lean practice derivation: reproducing `HiddenInstance` in
 *             JavaScript would be a second copy of the rules, and a local uniform
 *             pick over an emitted array is a lookup, not a rule.
 *
 *   JUDGED    the client knows neither the vein nor its own tape. It sends
 *             `crawl` and the host — which holds the day's vein derived from the
 *             committed slot secret, and the crawler's tape derived from the
 *             per-player run seed — returns the state id it landed on. The client
 *             checks the id is one the row it just played actually named, and
 *             renders it. It cannot derive the outcome, because it has neither
 *             hidden value.
 *
 * `mode` is in the canonical replay, so a practice transcript is structurally a
 * different object from a judged one.
 */

const FORMAT = "POAG1-GAME";
const ENGINE = "Dregg2.Games.PathOfAngels.VentCrawl";

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}
function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}
function exactKeys(value, keys, at) {
  refuse(object(value), "vent-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  refuse(
    actual.length === expected.length && actual.every((key, i) => key === expected[i]),
    "vent-field",
    `${at} has an unknown or missing field`,
  );
}
function integer(value, min, max) {
  return Number.isSafeInteger(value) && value >= min && value <= max;
}

/**
 * Compile the emitted descriptor into a read-only machine.
 *
 * ⚠ Nothing below reconstructs a rule. Every verdict, successor, refusal reason
 * and hazard numerator is read out of the table Lean rendered. The one thing this
 * function DERIVES is a cross-check: it recomputes each state's still-possible
 * vein set from the carry ladders and refuses if the emitted `still_possible`
 * disagrees. That is a second opinion about the one field a client uses to decide
 * what to show a player, and it costs nothing.
 */
export function loadVentCrawlDescriptor(game, mission, contentEpoch) {
  refuseNamedInstance(game, "Vent Crawl descriptor");
  refuseNamedInstance(game.instance, "Vent Crawl descriptor instance");
  exactKeys(
    game,
    ["format", "schema_version", "game_id", "ruleset", "engine_module", "action_limit",
     "security", "instance", "vent", "state_machine", "output"],
    "Vent Crawl descriptor",
  );
  refuse(game.format === FORMAT && game.schema_version === 1,
    "vent-format", "unsupported Vent Crawl descriptor");
  refuse(game.game_id === "vent-crawl" && game.ruleset === "push-your-luck-v1" &&
    game.engine_module === ENGINE,
    "vent-identity", "Vent Crawl descriptor identity is invalid");
  refuse(
    contentEpoch?.schema === mission.activation.digestSource &&
      contentEpoch.contentEpoch === mission.epoch,
    "vent-activation",
    "Vent Crawl mission requires an authenticated matching content epoch",
  );
  exactKeys(game.security,
    ["classification", "instance_visibility", "competitive_rewards", "economic_rewards"],
    "Vent Crawl security");
  refuse(
    game.security.classification === "committed-hidden-instance" &&
      game.security.instance_visibility === "oracle-only" &&
      game.security.competitive_rewards === false &&
      game.security.economic_rewards === false,
    "vent-security",
    "Vent Crawl must remain a committed, oracle-only, zero-reward beta demo",
  );
  // The disclosure comes from the SIGNED catalog, not from the descriptor, so a
  // descriptor cannot relabel itself and start naming the day it withholds.
  refuse(mission.instanceDisclosure === "oracle-only",
    "vent-security", "the signed catalog does not declare Vent Crawl oracle-only");
  const declaration =
    loadHiddenInstanceDeclaration(game.instance, mission.instanceDisclosure,
      "Vent Crawl descriptor instance");

  // ---- the vent: the public rules ----------------------------------------
  const vent = game.vent;
  exactKeys(vent,
    ["depth_cap", "faces", "mouth_salvage", "initial_depth", "flood_below", "veins",
     "vein_scope", "tape_scope", "bank_rule", "flood_effect", "payout",
     "refusal_vocabulary", "reserve"],
    "Vent Crawl vent");
  const depthCap = vent.depth_cap;
  const faces = vent.faces;
  refuse(integer(depthCap, 2, 32) && integer(faces, 2, 256),
    "vent-domain", "Vent Crawl depth cap or face count is outside the supported range");
  refuse(vent.vein_scope === "per-slot-shared" && vent.tape_scope === "per-player",
    "vent-scope",
    "Vent Crawl requires a per-slot shared table and per-player draws; a descriptor " +
    "that says otherwise is describing a different social game");

  const floodBelow = new Map();
  refuse(Array.isArray(vent.flood_below) && vent.flood_below.length === depthCap,
    "vent-hazard", "the flood ladder does not cover every rung");
  let previous = -1;
  for (const entry of vent.flood_below) {
    refuse(Array.isArray(entry) && entry.length === 2, "vent-hazard",
      "a flood ladder entry is not a [rung, below] pair");
    const [rung, below] = entry;
    refuse(integer(rung, 1, depthCap) && !floodBelow.has(rung), "vent-hazard",
      `the flood ladder names rung ${rung} twice or out of range`);
    // ⚑ Both of these are refusals and not warnings. A hazard that does not rise
    // is not push-your-luck, and a rung nobody survives is a wall.
    refuse(integer(below, 0, faces - 1), "vent-hazard",
      `rung ${rung} floods on ${below} of ${faces}, which no crawler survives`);
    refuse(below >= previous, "vent-hazard",
      `the hazard falls at rung ${rung}; a descent whose risk does not escalate ` +
      `gives a player no reason to ever stop`);
    previous = below;
    floodBelow.set(rung, below);
  }

  const veins = vent.veins.map((vein, index) => {
    exactKeys(vein, ["id", "yields", "carry"], `Vent Crawl vein[${index}]`);
    refuse(typeof vein.id === "string" && vein.id.length > 0, "vent-vein",
      `vein[${index}] has no id`);
    refuse(Array.isArray(vein.yields) && vein.yields.length === depthCap,
      "vent-vein", `vein ${vein.id} does not pay every rung`);
    refuse(Array.isArray(vein.carry) && vein.carry.length === depthCap + 1 &&
      vein.carry[0] === 0, "vent-vein",
      `vein ${vein.id}'s carry ladder is not a cumulative sum from zero`);
    for (let i = 0; i < depthCap; i += 1) {
      refuse(integer(vein.yields[i], 1, 1e6), "vent-vein",
        `vein ${vein.id} pays nothing at rung ${i + 1}`);
      refuse(vein.carry[i + 1] === vein.carry[i] + vein.yields[i], "vent-vein",
        `vein ${vein.id}'s carry ladder disagrees with its own yields at rung ${i + 1}`);
    }
    return Object.freeze({
      id: vein.id,
      yields: Object.freeze([...vein.yields]),
      carry: Object.freeze([...vein.carry]),
    });
  });
  refuse(veins.length >= 2, "vent-vein",
    "fewer than two veins is no hidden table at all");
  refuse(new Set(veins.map((v) => v.id)).size === veins.length, "vent-vein",
    "the vent names a vein twice");
  refuse(new Set(veins.map((v) => v.carry[vent.initial_depth])).size === 1, "vent-vein",
    "the veins disagree at the opening rung, so a run's starting sling already " +
    "names the day");

  // ---- the machine --------------------------------------------------------
  const sm = game.state_machine;
  exactKeys(sm, ["initial_state", "states", "actions", "transitions"],
    "Vent Crawl state machine");
  const states = new Map();
  for (const state of sm.states) {
    exactKeys(state, ["id", "terminal", "view"], "Vent Crawl state");
    exactKeys(state.view,
      ["depth", "carried", "outcome", "banked", "drowned", "still_possible",
       "next_rung", "next_flood_below", "solved"],
      `Vent Crawl view ${state.id}`);
    refuse(!states.has(state.id), "vent-state", `state ${state.id} is declared twice`);
    // The second opinion: the still-possible set is a FUNCTION of (depth, carried)
    // and this recomputes it rather than trusting the field a player is shown.
    const mine = veins
      .filter((v) => v.carry[state.view.depth] === state.view.carried)
      .map((v) => v.id);
    if (state.view.outcome === "crawling") {
      refuse(
        Array.isArray(state.view.still_possible) &&
          state.view.still_possible.length === mine.length &&
          state.view.still_possible.every((id, i) => id === mine[i]),
        "vent-state",
        `${state.id} says the day could still be ${state.view.still_possible}; ` +
        `the emitted carry ladders leave ${mine}`,
      );
      refuse(mine.length > 0, "vent-state",
        `${state.id} is a live state no vein can produce`);
    }
    const rungOdds = floodBelow.get(state.view.depth + 1);
    if (rungOdds !== undefined) {
      refuse(state.view.next_flood_below === rungOdds, "vent-hazard",
        `${state.id} publishes odds for the next rung that the flood ladder ` +
        `contradicts; the hazard is the one thing this descriptor is trusted to state`);
    }
    states.set(state.id, Object.freeze({
      id: state.id,
      terminal: state.terminal === true,
      depth: state.view.depth,
      carried: state.view.carried,
      outcome: state.view.outcome,
      banked: state.view.banked === true,
      drowned: state.view.drowned === true,
      stillPossible: Object.freeze([...mine]),
      nextRung: state.view.next_rung,
      nextFloodBelow: state.view.next_flood_below,
    }));
  }
  refuse(states.has(sm.initial_state), "vent-state",
    "the initial state is not among the declared states");

  const actions = sm.actions.map((action) => {
    exactKeys(action, ["id", "label"], "Vent Crawl action");
    return Object.freeze({ id: action.id, label: action.label });
  });

  const vocabulary = new Set(vent.refusal_vocabulary);
  const rows = new Map();
  for (const t of sm.transitions) {
    exactKeys(t,
      ["state", "action", "verdict", "reason", "next", "flood_below", "on_flood", "hauls"],
      "Vent Crawl transition");
    refuse(states.has(t.state), "vent-row", `a row names an undeclared state ${t.state}`);
    const key = `${t.state}\u0000${t.action}`;
    refuse(!rows.has(key), "vent-row", `${t.state}/${t.action} has two rows`);
    if (t.verdict === "refuse") {
      refuse(vocabulary.has(t.reason), "vent-row",
        `${t.state}/${t.action} refuses for ${t.reason}, which the vent does not declare`);
      rows.set(key, Object.freeze({ verdict: "refuse", reason: t.reason }));
    } else if (t.verdict === "accept") {
      refuse(states.has(t.next), "vent-row",
        `${t.state}/${t.action} accepts into an undeclared state`);
      rows.set(key, Object.freeze({ verdict: "accept", next: t.next }));
    } else if (t.verdict === "wager") {
      refuse(states.has(t.on_flood), "vent-row",
        `${t.state}/${t.action} floods into an undeclared state`);
      refuse(integer(t.flood_below, 0, faces - 1), "vent-row",
        `${t.state}/${t.action} publishes odds outside the die`);
      const here = states.get(t.state);
      refuse(t.flood_below === floodBelow.get(here.depth + 1), "vent-row",
        `${t.state}/${t.action} publishes odds the flood ladder contradicts`);
      refuse(Array.isArray(t.hauls) && t.hauls.length === here.stillPossible.length,
        "vent-row",
        `${t.state}/${t.action} names ${t.hauls?.length} hauls where ` +
        `${here.stillPossible.length} veins are still possible — a row that has ` +
        `dropped a day is a row that has leaked one`);
      const hauls = t.hauls.map((haul, i) => {
        exactKeys(haul, ["vein", "next"], `Vent Crawl haul ${t.state}/${t.action}[${i}]`);
        refuse(haul.vein === here.stillPossible[i], "vent-row",
          `${t.state}/${t.action} haul ${i} names ${haul.vein}, not ` +
          `${here.stillPossible[i]}`);
        refuse(states.has(haul.next), "vent-row",
          `${t.state}/${t.action} haul ${i} names an undeclared state`);
        return Object.freeze({ vein: haul.vein, next: haul.next });
      });
      rows.set(key, Object.freeze({
        verdict: "wager",
        floodBelow: t.flood_below,
        onFlood: t.on_flood,
        hauls: Object.freeze(hauls),
      }));
    } else {
      refuse(false, "vent-row", `${t.state}/${t.action} carries an unknown verdict`);
    }
  }
  refuse(rows.size === states.size * actions.length, "vent-row",
    "the transition table is not total");

  const crawlAction = actions.find((a) =>
    [...rows.values()].some((r) => r.verdict === "wager") &&
    [...rows.entries()].some(([k, r]) =>
      r.verdict === "wager" && k.endsWith(`\u0000${a.id}`)));
  refuse(crawlAction !== undefined, "vent-row",
    "no verb wagers, so the hidden table cannot affect play");
  const bankAction = actions.find((a) => a.id !== crawlAction.id);
  refuse(bankAction !== undefined, "vent-row",
    "Vent Crawl needs exactly two verbs");

  return Object.freeze({
    gameId: game.game_id,
    missionId: mission.missionId,
    engineModule: game.engine_module,
    actionLimit: game.action_limit,
    depthCap,
    faces,
    mouthSalvage: vent.mouth_salvage,
    floodBelow: Object.freeze(Object.fromEntries(floodBelow)),
    veins: Object.freeze(veins),
    veinById: new Map(veins.map((v) => [v.id, v])),
    payout: Object.freeze({ ...vent.payout }),
    initialState: sm.initial_state,
    states,
    actions: Object.freeze(actions),
    crawlAction: crawlAction.id,
    bankAction: bankAction.id,
    rows,
    instance: declaration,
    mission: Object.freeze({ ...mission }),
  });
}

/** The exact odds of the rung a crawler is standing before, as a rendered pair. */
export function rungOdds(descriptor, state) {
  const below = descriptor.floodBelow[state.depth + 1];
  if (below === undefined) return null;
  return Object.freeze({
    below,
    faces: descriptor.faces,
    percent: (below / descriptor.faces) * 100,
  });
}

/**
 * What the next rung pays, per day still on the table. This is the reward half of
 * "the player sees the current odds and the next rung's odds before choosing":
 * the risk is one number and the prize is a small set of numbers, and a client
 * that shows only the first has shown half the decision.
 */
export function nextRungHauls(descriptor, state) {
  const row = descriptor.rows.get(`${state.id}\u0000${descriptor.crawlAction}`);
  if (!row || row.verdict !== "wager") return [];
  return row.hauls.map((haul) => Object.freeze({
    vein: haul.vein,
    carried: descriptor.states.get(haul.next).carried,
    gain: descriptor.states.get(haul.next).carried - state.carried,
  }));
}

function randomBelow(bound) {
  // Rejection sampling, so a bound that does not divide 2^32 is still uniform.
  const limit = Math.floor(0x100000000 / bound) * bound;
  const buffer = new Uint32Array(1);
  for (;;) {
    crypto.getRandomValues(buffer);
    if (buffer[0] < limit) return buffer[0] % bound;
  }
}

/**
 * Start a run.
 *
 * PRACTICE draws a vein and a tape locally. JUDGED draws neither: `session.step`
 * is the host round-trip, and every state it returns is checked against the row
 * the client actually played before it is rendered.
 */
export function startRun(descriptor, session = { mode: "practice" }) {
  const mode = session.mode === "judged" ? "judged" : "practice";
  let vein = null;
  if (mode === "practice") {
    vein = session.vein ?? descriptor.veins[randomBelow(descriptor.veins.length)].id;
    refuse(descriptor.veinById.has(vein), "vent-practice",
      "the practice vein is not one the descriptor declares");
  }
  return {
    mode,
    vein,
    stateId: descriptor.initialState,
    steps: [],
    // ⚠ Practice tape draws are recorded so a practice transcript is REPLAYABLE
    // and visibly local. A judged transcript has no such field, which is one of
    // the structural reasons the two cannot be confused.
    ...(mode === "practice" ? { draws: [] } : {}),
  };
}

export function currentState(descriptor, run) {
  return descriptor.states.get(run.stateId);
}

export function rowFor(descriptor, run, actionId) {
  return descriptor.rows.get(`${run.stateId}\u0000${actionId}`);
}

/**
 * Play one action.
 *
 * `hostStep` is required in judged mode and is the ONLY source of the outcome: it
 * returns a state id and this function refuses any id the row it just played did
 * not name. In practice mode the outcome is rolled here, against the PUBLISHED
 * numerator — the same one the player was shown.
 */
export function play(descriptor, run, actionId, hostStep = null) {
  const row = rowFor(descriptor, run, actionId);
  refuse(row !== undefined, "vent-play", "no such action here");
  if (row.verdict === "refuse") {
    return { run, refused: row.reason };
  }
  if (row.verdict === "accept") {
    return {
      run: { ...run, stateId: row.next, steps: [...run.steps, { action: actionId }] },
      refused: null,
    };
  }

  if (run.mode === "judged") {
    refuse(typeof hostStep === "function", "vent-play",
      "a judged crawl needs the host: the client has neither the day's vein nor " +
      "its own tape and must not invent either");
    const landed = hostStep(run.stateId, actionId);
    const named = [row.onFlood, ...row.hauls.map((h) => h.next)];
    refuse(named.includes(landed), "vent-judged",
      `the host returned ${landed}, which the row it answered did not name`);
    return {
      run: { ...run, stateId: landed, steps: [...run.steps, { action: actionId }] },
      refused: null,
    };
  }

  const draw = randomBelow(descriptor.faces);
  const flooded = draw < row.floodBelow;
  const haul = row.hauls.find((h) => h.vein === run.vein);
  refuse(flooded || haul !== undefined, "vent-practice",
    "the practice vein is no longer among the day's possibilities, which cannot " +
    "happen unless the table and the ladders disagree");
  return {
    run: {
      ...run,
      stateId: flooded ? row.onFlood : haul.next,
      steps: [...run.steps, { action: actionId }],
      draws: [...run.draws, { rung: descriptor.states.get(run.stateId).depth + 1, draw }],
    },
    refused: null,
  };
}

/**
 * The end-of-run reading for the `push-your-luck` shape, in the exact record
 * `run-summary.js`'s `OUTCOME_BY_SHAPE` rows produce.
 *
 * ⚑ A DROWNING IS `lost`, AND THAT WORD NOW EXISTS. This function used to return
 * `unsolved` for a flood and say so in a warning: for every other shape `unsolved`
 * means "the window closed" — the run ran out of turns with the puzzle unfinished
 * — and a drowned crawl is not that. It ended EARLY, on a wager the player chose
 * to take and lost, with turns still on the clock. The repair named here was one
 * of two, a fourth outcome or a note, and `run-summary.js` took the fourth
 * outcome: a note under a headline reading "Window closed." would have left the
 * headline lying. ⚠ It is still not `solved`, and no reading may make it one.
 */
export function ventCrawlOutcome(run, descriptor) {
  const state = descriptor.states.get(run.stateId);
  return {
    over: state.terminal === true,
    outcome: state.banked === true ? "solved" : "lost",
    actions: run.steps.length,
    actionLimit: descriptor.actionLimit,
  };
}

/** The canonical replay. `mode` is in it, so the two run kinds are different objects. */
export function transcript(descriptor, run) {
  return Object.freeze({
    game_id: descriptor.gameId,
    engine_module: descriptor.engineModule,
    mode: run.mode,
    actions: run.steps.map((s) => s.action),
    final_state: run.stateId,
    ...(run.mode === "practice"
      ? { practice_vein: run.vein, practice_draws: run.draws }
      : {}),
  });
}

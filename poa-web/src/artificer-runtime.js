/**
 * Artificer Logic — decode the authenticated Lean-emitted induction table.
 *
 * ⚑ The verb is different from every other game on the rack.  Signal, Relay,
 * Salvage and Deck Descent hide a VALUE and ask the player to find it.  This one
 * hides a RULE, publishes the whole lattice of rules it could be, and asks the
 * player to name which.  So the descriptor carries a `manual` block that is
 * PUBLIC BY DESIGN — every rule with the charges it engages on — and the only
 * thing withheld is which entry the run seed drew.
 *
 * That block is also the reason this file exists rather than a `parseInstance`
 * one-liner: the manual is what a client renders, what a practice oracle answers
 * from, and what the design gate rebuilds distinguishability from.  It is
 * checked here to be the shape it claims, complete, and free of an
 * indistinguishable pair — a manual with two entries no experiment separates
 * makes a perfectly played run lose to a coin flip, and a client that renders it
 * anyway is showing a player a lattice they cannot narrow.
 *
 * ⚠ This module does NOT reimplement `Rule.accepts`.  The `engages` list is read
 * out of the emitted bytes.  Reproducing the rule semantics in JavaScript would
 * put a second model of the game in the browser, which is the wound the whole
 * POAG1 split exists to close.
 */
import { ArtifactRefusal } from "./poag1.js";
import {
  boundedInteger,
  exactKeys,
  identifier,
  loadFiniteTableDescriptor,
  loadHiddenInstanceDeclaration,
} from "./finite-table-runtime.js";

const COGS_PER_CHARGE = 3;
const METALS = Object.freeze(["iron", "brass"]);
const SEATS = Object.freeze(["first", "second", "third"]);
const CHARGE_SPACE = METALS.length ** COGS_PER_CHARGE;
const MANUAL_SIZE = 16;
const PROBE_BUDGET = 4;
const ACTION_LIMIT = PROBE_BUDGET + 1;
const VERDICTS = Object.freeze(["probing", "identified", "mistaken"]);
// ⚠ `solved` is not decoration and not a synonym for `run-lost`.  The shared
// engine requires a terminal state to refuse every action as `solved`, and this
// is the game on the rack where "the run ended" and "the run was won" come
// apart — a mistaken naming stops the machine exactly as a right one does.
const REFUSALS = Object.freeze([
  "solved",
  "run-lost",
  "no-charges-left",
  "already-answered",
  "refuted",
]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function label(value, at, max = 96) {
  refuse(
    typeof value === "string" && value.length >= 1 && value.length <= max,
    "artificer-label",
    `${at} is invalid`,
  );
  return value;
}

/**
 * The published field manual.  Complete, duplicate-free, and — the load-bearing
 * check — DISTINGUISHING.
 */
function artificerManual(value, at) {
  exactKeys(
    value,
    [
      "cogs_per_charge", "metals", "seats", "families", "charges", "rules",
      "probe_budget", "refusal_reasons", "answer", "probe_admissible",
      "declaration_admissible", "reserve",
    ],
    at,
  );
  refuse(value.cogs_per_charge === COGS_PER_CHARGE, "artificer-manual", `${at}.cogs_per_charge is not ${COGS_PER_CHARGE}`);
  refuse(
    Array.isArray(value.metals) && value.metals.length === METALS.length &&
      value.metals.every((metal, index) => metal === METALS[index]),
    "artificer-manual",
    `${at}.metals is not the declared two-metal alphabet`,
  );
  refuse(
    Array.isArray(value.seats) && value.seats.length === SEATS.length &&
      value.seats.every((seat, index) => seat === SEATS[index]),
    "artificer-manual",
    `${at}.seats is not the declared three-seat train`,
  );
  refuse(value.probe_budget === PROBE_BUDGET, "artificer-manual", `${at}.probe_budget disagrees with its Lean ruleset`);
  refuse(
    Array.isArray(value.refusal_reasons) &&
      value.refusal_reasons.length === REFUSALS.length &&
      value.refusal_reasons.every((reason, index) => reason === REFUSALS[index]),
    "artificer-manual",
    `${at}.refusal_reasons is not the declared vocabulary`,
  );
  for (const key of ["answer", "probe_admissible", "declaration_admissible", "reserve"]) {
    label(value[key], `${at}.${key}`, 400);
  }

  refuse(
    Array.isArray(value.families) && value.families.length > 0,
    "artificer-manual",
    `${at}.families is absent`,
  );
  const families = value.families.map((family, index) =>
    identifier(family, "artificer-manual", `${at}.families[${index}] is invalid`));
  refuse(new Set(families).size === families.length, "artificer-manual", `${at}.families repeats a family`);

  // ⚑ The charge space must be the FULL product.  A manual that publishes fewer
  // charges than metals-to-the-seats has quietly removed experiments the player
  // is allowed to reason about, and every separation argument below would then
  // be measured against the wrong space.
  refuse(
    Array.isArray(value.charges) && value.charges.length === CHARGE_SPACE,
    "artificer-manual",
    `${at}.charges is not the complete ${CHARGE_SPACE}-charge space`,
  );
  const chargeIds = [];
  const charges = value.charges.map((entry, index) => {
    exactKeys(entry, ["id", "cogs", "brass"], `${at}.charges[${index}]`);
    identifier(entry.id, "artificer-manual", `${at}.charges[${index}].id is invalid`);
    refuse(
      Array.isArray(entry.cogs) && entry.cogs.length === COGS_PER_CHARGE &&
        entry.cogs.every((cog) => METALS.includes(cog)),
      "artificer-manual",
      `${at}.charges[${index}].cogs is not a ${COGS_PER_CHARGE}-cog train`,
    );
    const brass = entry.cogs.filter((cog) => cog === "brass").length;
    refuse(entry.brass === brass, "artificer-manual", `${at}.charges[${index}].brass miscounts its own cogs`);
    refuse(!chargeIds.includes(entry.id), "artificer-manual", `${at}.charges names ${entry.id} twice`);
    chargeIds.push(entry.id);
    return Object.freeze({ id: entry.id, cogs: Object.freeze([...entry.cogs]), brass });
  });

  refuse(
    Array.isArray(value.rules) && value.rules.length === MANUAL_SIZE,
    "artificer-manual",
    `${at}.rules is not the declared ${MANUAL_SIZE}-rule manual`,
  );
  const ruleIds = [];
  const signatures = new Map();
  const rules = value.rules.map((entry, index) => {
    exactKeys(entry, ["id", "family", "label", "engages"], `${at}.rules[${index}]`);
    identifier(entry.id, "artificer-manual", `${at}.rules[${index}].id is invalid`);
    refuse(families.includes(entry.family), "artificer-manual", `${at}.rules[${index}] claims an undeclared family`);
    label(entry.label, `${at}.rules[${index}].label`);
    refuse(Array.isArray(entry.engages), "artificer-manual", `${at}.rules[${index}].engages must be an array`);
    const engages = entry.engages.map((charge, position) => {
      refuse(chargeIds.includes(charge), "artificer-manual", `${at}.rules[${index}].engages[${position}] is not a charge`);
      return charge;
    });
    refuse(new Set(engages).size === engages.length, "artificer-manual", `${at}.rules[${index}].engages repeats a charge`);
    refuse(
      engages.every((charge, position) =>
        position === 0 || chargeIds.indexOf(engages[position - 1]) < chargeIds.indexOf(charge)),
      "artificer-manual",
      `${at}.rules[${index}].engages is not in canonical charge order`,
    );
    refuse(!ruleIds.includes(entry.id), "artificer-manual", `${at}.rules names ${entry.id} twice`);
    ruleIds.push(entry.id);

    // ⚑ THE DESIGN GATE, CLIENT-SIDE.  Two rules that engage on exactly the same
    // charges cannot be told apart by ANY legal experiment, so a player who runs
    // all eight and narrows perfectly is still handed a coin.  The Lean side
    // proves this cannot happen (`manual_has_no_synonyms`) and the design gate
    // rebuilds it from these same bytes; a client that renders the lattice is the
    // third place it has to hold, because it is the client that tells a player
    // the space is narrowable.
    const signature = engages.join(",");
    const twin = signatures.get(signature);
    refuse(
      twin === undefined,
      "artificer-indistinguishable",
      `${at} publishes ${entry.id} and ${twin} engaging on exactly the same charges, ` +
        `so no experiment separates them and a perfectly played run can still lose to a coin flip`,
    );
    signatures.set(signature, entry.id);

    return Object.freeze({
      id: entry.id,
      family: entry.family,
      label: entry.label,
      engages: Object.freeze(engages),
    });
  });

  return Object.freeze({
    cogsPerCharge: value.cogs_per_charge,
    metals: Object.freeze([...value.metals]),
    seats: Object.freeze([...value.seats]),
    families: Object.freeze(families),
    charges: Object.freeze(charges),
    chargeIds: Object.freeze(chargeIds),
    rules: Object.freeze(rules),
    ruleIds: Object.freeze(ruleIds),
    probeBudget: value.probe_budget,
    refusalReasons: Object.freeze([...value.refusal_reasons]),
    answer: value.answer,
    probeAdmissible: value.probe_admissible,
    declarationAdmissible: value.declaration_admissible,
    reserve: value.reserve,
  });
}

/**
 * The practice space is a COUNT and a pointer, not a list of instances: the
 * members of this family are the manual's own entries, which are already
 * published in full.  There is deliberately no second copy of them here.
 */
function artificerPractice(value, manual, at) {
  exactKeys(value, ["scored", "instance_space", "member_names", "purpose_tag"], at);
  refuse(value.scored === false, "artificer-practice", `${at} declares practice runs scored`);
  refuse(
    value.instance_space === manual.rules.length,
    "artificer-practice",
    `${at}.instance_space is not the ${manual.rules.length}-rule manual`,
  );
  refuse(value.member_names === "manual.rules", "artificer-practice", `${at}.member_names does not point at the manual`);
  boundedInteger(value.purpose_tag, 0, 255, "artificer-practice", `${at}.purpose_tag is invalid`);
  return Object.freeze({
    scored: value.scored,
    instanceSpace: value.instance_space,
    memberNames: value.member_names,
    purposeTag: value.purpose_tag,
  });
}

function artificerViewFactory(manual) {
  return function artificerView(value, actionLimit, at) {
    exactKeys(
      value,
      ["candidates", "remaining", "turns", "charges_left", "verdict", "certain",
       "certifiable", "doomed", "solved"],
      at,
    );
    refuse(Array.isArray(value.candidates), "artificer-candidates", `${at}.candidates must be an array`);
    const candidates = value.candidates.map((rule, index) => {
      refuse(manual.ruleIds.includes(rule), "artificer-candidates", `${at}.candidates[${index}] is not a manual rule`);
      return rule;
    });
    refuse(new Set(candidates).size === candidates.length, "artificer-candidates", `${at}.candidates repeats a rule`);
    refuse(
      candidates.every((rule, index) =>
        index === 0 || manual.ruleIds.indexOf(candidates[index - 1]) < manual.ruleIds.indexOf(rule)),
      "artificer-candidates",
      `${at}.candidates is not in canonical manual order`,
    );
    // ⚑ The hidden rule is always among the survivors, so a state with none is a
    // state no instance can produce.  A client that rendered it would be showing
    // a player a run in which no naming can be right.
    refuse(candidates.length >= 1, "artificer-candidates", `${at} declares an empty candidate set`);
    refuse(value.remaining === candidates.length, "artificer-candidates", `${at}.remaining miscounts its own candidates`);
    boundedInteger(value.turns, 0, actionLimit, "artificer-turns", `${at}.turns is invalid`);
    boundedInteger(value.charges_left, 0, manual.probeBudget, "artificer-turns", `${at}.charges_left is invalid`);
    refuse(
      value.charges_left === Math.max(0, manual.probeBudget - value.turns),
      "artificer-turns",
      `${at}.charges_left disagrees with the clock`,
    );
    refuse(VERDICTS.includes(value.verdict), "artificer-verdict", `${at}.verdict is invalid`);
    for (const flag of ["certain", "certifiable", "doomed", "solved"]) {
      refuse(typeof value[flag] === "boolean", "artificer-flag", `${at}.${flag} is invalid`);
    }
    refuse(value.certain === (candidates.length === 1), "artificer-flag", `${at}.certain miscounts its own candidates`);
    refuse(value.solved === (value.verdict === "identified"), "artificer-flag", `${at}.solved disagrees with its verdict`);
    refuse(value.doomed === (value.verdict === "mistaken"), "artificer-flag", `${at}.doomed disagrees with its verdict`);
    refuse(!(value.certifiable && value.verdict !== "probing"), "artificer-flag", `${at} claims a finished run is still certifiable`);
    return Object.freeze({
      candidates: Object.freeze(candidates),
      remaining: value.remaining,
      turns: value.turns,
      chargesLeft: value.charges_left,
      verdict: value.verdict,
      certain: value.certain,
      certifiable: value.certifiable,
      doomed: value.doomed,
      solved: value.solved,
    });
  };
}

function artificerActionFactory(manual) {
  return function artificerAction(value, at) {
    exactKeys(value, ["id", "label", "kind", "charge", "rule"], at);
    identifier(value.id, "artificer-action", `${at}.id is invalid`);
    label(value.label, `${at}.label`);
    refuse(value.kind === "probe" || value.kind === "declare", "artificer-action", `${at}.kind is invalid`);
    if (value.kind === "probe") {
      refuse(manual.chargeIds.includes(value.charge), "artificer-action", `${at}.charge is not a manual charge`);
      refuse(value.rule === null, "artificer-action", `${at} is a probe and names a rule`);
      refuse(value.id === `feed-${value.charge}`, "artificer-action", `${at}.id disagrees with its charge`);
    } else {
      refuse(manual.ruleIds.includes(value.rule), "artificer-action", `${at}.rule is not a manual rule`);
      refuse(value.charge === null, "artificer-action", `${at} is a declaration and names a charge`);
      refuse(value.id === `name-${value.rule}`, "artificer-action", `${at}.id disagrees with its rule`);
    }
    return { id: value.id, label: value.label, kind: value.kind, charge: value.charge, rule: value.rule };
  };
}

/** Decode Artificer Logic's authenticated Lean-emitted parametric table. */
export function loadArtificerLogicDescriptor(game, authority) {
  let manual = null;
  let practice = null;
  const descriptor = loadFiniteTableDescriptor(game, authority, {
    name: "Artificer Logic",
    gameId: "artificer-logic",
    ruleset: "artificer-v1",
    disclosure: "oracle-only",
    engineModule: "Dregg2.Games.PathOfAngels.ArtificerLogic",
    actionLimit: ACTION_LIMIT,
    maxActionLimit: ACTION_LIMIT,
    stateCount: 1197,
    maxStates: 1197,
    maxActions: CHARGE_SPACE + MANUAL_SIZE,
    allowsResolve: true,
    extraKeys: ["manual", "practice"],
    refusalReasons: REFUSALS,
    parseInstance: (value, at) => {
      manual = artificerManual(value.manual, `${at} manual`);
      practice = artificerPractice(value.practice, manual, `${at} practice space`);
      return Object.freeze({
        draw: loadHiddenInstanceDeclaration(value.instance, "oracle-only", at),
        manual,
        practice,
      });
    },
    parseView: (value, actionLimit, at) => artificerViewFactory(manual)(value, actionLimit, at),
    parseAction: (value, at) => artificerActionFactory(manual)(value, at),
  });
  return descriptor;
}

/**
 * The practice oracle: TWO LOOKUPS, never a computation.
 *
 * The question an emitted row asks is read off the action — a probe asks whether
 * the mechanism engages on its charge, a declaration asks whether its rule is the
 * one drawn — and the answer is read off the emitted manual.  What a "match"
 * DOES stays in `on_match`/`on_mismatch`, and this function never looks at
 * either.  Rehearsal therefore exercises the same table a judged run does.
 *
 * ⚠ `ruleIndex` is a LOCAL, UNSCORED choice out of the published manual.  It is
 * not `HiddenInstance.runSeedFor` and must never become it: reproducing the Lean
 * derivation here would put a second copy of the draw in a browser that has no
 * secret to feed it.
 */
export function artificerPracticeOracle(descriptor, ruleIndex) {
  const manual = descriptor.instance.manual;
  const drawn = manual.rules[ruleIndex];
  refuse(drawn, "artificer-practice", "the practice run names a rule outside the published manual");
  return (view, actionId) => {
    const action = descriptor.actions.find((candidate) => candidate.id === actionId);
    refuse(action, "artificer-practice", "the practice oracle was asked about an unknown action");
    if (action.kind === "probe") {
      return drawn.engages.includes(action.charge) ? "match" : "mismatch";
    }
    refuse(
      view.candidates.includes(action.rule),
      "artificer-practice",
      "an oracle row was reached for a rule the evidence has already refuted, so the emitted table asks a question it did not set up",
    );
    return action.rule === drawn.id ? "match" : "mismatch";
  };
}

export { MANUAL_SIZE, CHARGE_SPACE, PROBE_BUDGET, ACTION_LIMIT, REFUSALS };

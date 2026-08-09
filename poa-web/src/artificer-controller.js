/**
 * Artificer Logic — presentation only.
 *
 * Every verdict, successor and refusal reason comes from the Lean-emitted table
 * through `finite-table-runtime.js`.  This file decides nothing about the game;
 * it decides what a charge and a naming LOOK like, and it renders the one thing
 * this game has that no other on the rack does — the surviving candidate set,
 * which IS the player's state.
 *
 * ⚑ The manual is rendered because the manual is public.  An induction game that
 * hides its hypothesis space is Zendo, where a loss feels arbitrary; the whole
 * fairness argument here is that the player narrows a lattice they can see.
 */
import { mountFiniteTableController } from "./finite-table-controller.js";
import { artificerPracticeOracle } from "./artificer-runtime.js";

const REFUSAL_COPY = Object.freeze({
  solved: "Named and documented. Reset to take another mechanism.",
  "run-lost": "The mechanism kept its secret. Reset to take another one.",
  "no-charges-left": "No charges left. Name a rule the evidence still permits.",
  "already-answered":
    "The mechanism has already answered that charge — every rule still standing agrees on it, so feeding it would buy nothing.",
  refuted: "The evidence has already ruled that one out.",
});

function ruleOf(descriptor, id) {
  return descriptor.instance.manual.rules.find((rule) => rule.id === id);
}

export function mountArtificerLogic(root, descriptor, callbacks = {}) {
  const manual = descriptor.instance.manual;
  const session = callbacks.session ?? {
    mode: "practice",
    member: 0,
    oracle: artificerPracticeOracle(descriptor, 0),
  };
  return mountFiniteTableController(root, descriptor, {
    id: "artificer-logic",
    className: "artificer-logic",
    eyebrow: "ARTIFICER BENCH",
    title: "Artificer Logic",
    brief:
      `The mechanism obeys one of the ${manual.rules.length} laws in the field manual and will not say which. ` +
      `Feed it a train of three cogs and watch: it engages, or it slips. ` +
      `You have ${manual.probeBudget} charges, and a charge that every surviving law already agrees on is refused — ` +
      `so the only question is WHICH charge. Name the law when one is left standing.`,
    boardLabel: `Eight charges and the ${manual.rules.length}-law manual`,
    columns: 4,
    /**
     * ⚑ THE DECISION THIS GAME ASKS, MADE VISIBLE.
     *
     * Deck Descent gilds its four dark-asking verbs because its whole decision is
     * *when to buy information*. Artificer's is the same question with a second
     * half: every charge buys, and the run ends the moment you COMMIT to a law.
     * Twenty-four identical cells in one column said neither, and put a wrong
     * naming one mis-tap below the charge a player meant to spend.
     *
     * ⚠ The split ("9 engage / 7 slip") stays exactly as emitted and nothing here
     * ranks the charges. Marking the most informative one would be playing the
     * game for the player, which is a different sin from hiding it.
     */
    boardGroups: (game) => [
      {
        id: "charges",
        label: `Spend a charge — ${manual.probeBudget} to spend, and each one narrows the manual`,
        columns: 4,
        actionIds: game.actions.filter((action) => action.kind === "probe").map((action) => action.id),
      },
      {
        id: "manual",
        label: `Name the law — this ends the run, right or wrong`,
        columns: 2,
        actionIds: game.actions.filter((action) => action.kind !== "probe").map((action) => action.id),
      },
    ],
    session,
    /**
     * ⚑ A VERB THE TABLE WILL REFUSE IS NOT OFFERED. This is the defect that
     * shipped on Deck Descent — "a doomed descent offered nine live buttons, and
     * none of them could be pressed" — and Artificer had it in two places at
     * once: a charge every surviving law agrees on (`already-answered`) and a law
     * the evidence has ruled out (`refuted`) both stayed pressable, and their
     * computed `spent` state had no rendering at all, so they were visually
     * identical to a live one.
     *
     * ⚠ WHAT IS SAID HERE IS COPY, NOT THE RULE. This file tried to work out the
     * refusal predicate for itself and got two of the three ways a charge can be
     * refused, missing `no-charges-left` — eight dead buttons at the end of every
     * run, which is the same defect wearing a fix. `finite-table-controller.js`
     * now disables from the emitted row's own `verdict` for every game, so what
     * these branches decide is the WORDS on a closed control, never whether it is
     * closed. `tests/minigame-accessibility.test.mjs` holds enabled ⟺ accepted.
     */
    presentAction: (action, view) => {
      if (action.kind === "probe") {
        const charge = manual.charges.find((entry) => entry.id === action.charge);
        const splits = view.candidates.filter((id) =>
          ruleOf(descriptor, id).engages.includes(action.charge)).length;
        const buysNothing = splits === 0 || splits === view.candidates.length;
        return {
          label: charge.cogs.map((cog) => (cog === "brass" ? "B" : "I")).join(""),
          // The split this charge would make, out of the survivors.  It is derived
          // from the emitted manual and the emitted view, so it tells the player
          // exactly what they could work out and nothing they could not.
          detail: buysNothing
            ? `all ${view.candidates.length} agree — buys nothing`
            : `${splits} engage / ${view.candidates.length - splits} slip`,
          ariaLabel: buysNothing
            ? `Feed the mechanism ${charge.cogs.join(", ")}. Unavailable: all ${view.candidates.length} surviving laws already agree on it, so it would buy nothing.`
            : `Feed the mechanism ${charge.cogs.join(", ")}. ` +
              `${splits} of ${view.candidates.length} surviving laws engage on it.`,
          state: buysNothing ? "spent" : "live",
          disabled: buysNothing,
        };
      }
      const rule = ruleOf(descriptor, action.rule);
      const standing = view.candidates.includes(action.rule);
      return {
        label: rule.label,
        detail: standing ? rule.family : "ruled out by the evidence",
        ariaLabel: `Name the law: ${rule.label}.` + (standing ? "" : " Unavailable: the evidence has ruled this one out."),
        state: standing ? "live" : "spent",
        disabled: !standing,
      };
    },
    presentStatus: (view) => {
      if (view.verdict === "identified") {
        return `Named it — ${ruleOf(descriptor, view.candidates[0]).label}. The mechanism is documented.`;
      }
      if (view.verdict === "mistaken") {
        return "Wrong law. The mechanism keeps its secret; the bench is closed.";
      }
      if (view.certain) {
        return `One law left standing: ${ruleOf(descriptor, view.candidates[0]).label}. Name it.`;
      }
      const skill = view.certifiable
        ? "still reachable on skill"
        : "no longer reachable on skill — from here a naming is a wager";
      return (
        `${view.remaining} laws still fit, ${view.chargesLeft} ` +
        `${view.chargesLeft === 1 ? "charge" : "charges"} left. ` +
        `Certainty is ${skill}.`
      );
    },
    presentRefusal: (reason) => REFUSAL_COPY[reason] ?? "That move is closed here.",
    presentOracleQuery: () =>
      "Waiting for the host to run that charge against the sealed mechanism.",
    onTranscript: callbacks.onTranscript,
    onRefusal: callbacks.onRefusal,
    onReset: callbacks.onReset,
    onOracleQuery: callbacks.onOracleQuery,
    afterRender: callbacks.afterRender,
  });
}

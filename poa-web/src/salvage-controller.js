import { mountFiniteTableController } from "./finite-table-controller.js";
import { tableRunTrail } from "./finite-table-runtime.js";
import { salvagePracticeOracle } from "./salvage-runtime.js";

/**
 * Salvage is `oracle-only`: the board is never named during the run, so a plate
 * has no glyph to show until the table itself resolves a pair. The controller
 * renders sealed / exposed / cleared and nothing else — before the split it
 * rendered `glyph_label` off the action row, which was the answer key.
 *
 * ⚑ AND UNTIL NOW IT RENDERED NOTHING ELSE EITHER, WHICH ERASED THE GAME.
 *
 * Salvage hands a player exactly one bit per comparison — did these two plates
 * match — and that bit is the whole of the skill. After a mismatch both plates
 * went back to an identical "sealed" button: no glyph, no ledger, no history, so
 * the six controls a player faced on turn 15 looked exactly like the six they
 * faced on turn 1. Every ruled-out pair the run had paid two exposures for lived
 * only in the player's head, and the interface actively worked against it.
 * Measured against the solve: perfect play is worth 37 points over clicking at
 * random, and a board that shows nothing is a board that asks you to hold nine
 * facts in your head to collect them.
 *
 * `ruledOut` below fixes that, and the line it does not cross is the one
 * `blackbox-controller.js` drew in fd23cbd4b: what a client's OWN TRANSCRIPT
 * contains is a fact about the transcript, not a rule of the game. Each entry is
 * one emitted `resolve` row that came back `mismatch`; the two plates are the one
 * the run had face up (the row's own `from` view, from `tableRunTrail`) and the
 * one the action names. No board is consulted, no glyph is guessed, and nothing
 * is derived that the table did not already say out loud.
 *
 * ⚠ AND IT DOES NOT DISABLE ANYTHING. Salvage's emitted refusal vocabulary is
 * `solved` / `turn-limit` / `cleared-slot` / `already-exposed` — there is no
 * `already-compared`, so the real rules ALLOW re-testing a pair you have already
 * ruled out. Greying it out would be this face authoring a rule the kernel does
 * not have. (That is the difference from blackbox, where `repeated-probe` IS in
 * the emitted vocabulary and only the rehearsal was charging for it.) Spending a
 * comparison on a settled pair is a bad move, not an illegal one, and telling a
 * player which pairs are settled is how you let them not make it.
 */

const NAMES = ["A", "B", "C", "D", "E", "F"];

/** The pairs this transcript has already settled, read out of the transcript. */
function ledgerOf(descriptor, run) {
  const slotOf = new Map(descriptor.actions.map((action) => [action.id, action.slot]));
  const missed = [];
  const matched = [];
  for (const step of tableRunTrail(descriptor, run)) {
    if (step.verdict !== "resolve") continue;
    const slot = slotOf.get(step.action);
    const first = step.from.exposed;
    if (slot === undefined || first === null) continue;
    const pair = first < slot ? [first, slot] : [slot, first];
    (step.resolution === "match" ? matched : missed).push(pair);
  }
  return { missed, matched };
}

const key = (pair) => `${pair[0]}:${pair[1]}`;
const plate = (slot) => `${slot} (${NAMES[slot]})`;

export function mountSalvageLock(root, descriptor, callbacks = {}) {
  const session = callbacks.session ?? {
    mode: "practice",
    member: 0,
    oracle: salvagePracticeOracle(descriptor, 0),
  };

  // One walk per run, not one per button. Runs are frozen and replaced whole on
  // every step, so identity is a sound cache key.
  let cachedRun = null;
  let cachedLedger = null;
  function ledger(run) {
    if (run !== cachedRun) {
      cachedRun = run;
      cachedLedger = ledgerOf(descriptor, run);
    }
    return cachedLedger;
  }

  return mountFiniteTableController(root, descriptor, {
    id: "salvage-lock",
    className: "salvage-lock",
    eyebrow: "SALVAGE HATCH",
    title: "Salvage Lock",
    brief:
      "Expose sealed plates two at a time. Whether a pair matches depends on a board " +
      "you cannot see; the authenticated table asks, and records the answer it was " +
      "given. Cleared pairs stay cleared, and every pair you have already ruled out " +
      "stays on the plate that ruled it out.",
    boardLabel: "Six salvage-lock plates",
    columns: 3,
    session,
    presentAction(action, view, run) {
      const cleared = view.cleared.includes(action.slot);
      const exposed = view.exposed === action.slot;
      const state = cleared ? "cleared" : exposed ? "exposed" : "sealed";
      // Which plates THIS plate has already been compared against and did not
      // match. Straight off the transcript; see the docblock.
      const ruledOut = cleared
        ? []
        : ledger(run).missed
            .filter((pair) => pair.includes(action.slot))
            .map((pair) => (pair[0] === action.slot ? pair[1] : pair[0]))
            .filter((slot, index, all) => all.indexOf(slot) === index)
            .sort((a, b) => a - b);
      const not = ruledOut.length === 0
        ? ""
        : ` — not ${ruledOut.map((slot) => plate(slot)).join(", ")}`;
      const detail = cleared
        ? "cleared pair"
        : exposed
          ? `face up, awaiting its pair${not}`
          : `sealed${not}`;
      return {
        label: action.label,
        detail,
        ariaLabel: ruledOut.length === 0
          ? `${action.label}, ${detail}`
          : `${action.label}, ${cleared ? "cleared pair" : exposed ? "face up" : "sealed"}, ` +
            `ruled out against ${ruledOut.length} ${ruledOut.length === 1 ? "plate" : "plates"}: ` +
            `${ruledOut.map((slot) => plate(slot)).join(", ")}`,
        state,
        disabled: cleared,
        pressed: exposed,
      };
    },
    presentStatus(view, run, game) {
      if (view.solved) return `Salvage lock cleared in ${run.steps.length} exposure${run.steps.length === 1 ? "" : "s"}. The transcript is written down here and anyone can check it.`;
      // ⚠ The slot index is rendered RAW. Every action label the descriptor emits is
      // `Expose plate ${slot}` — 0-based, and pinned by `salvageAction` — so a status
      // line that said `${slot + 1}` named a different plate from the button the
      // player had just pressed. In a game whose whole content is remembering which
      // indices you have already compared, that disagreement is not cosmetic.
      const exposed = view.exposed === null ? "No plate is exposed." : `Plate ${plate(view.exposed)} is exposed.`;
      // The comparison, not the exposure, is the unit a player spends: two
      // exposures buy one bit, and the budget is an even number for that reason.
      const spent = Math.floor(view.turns / 2);
      const settled = new Set(ledger(run).missed.map(key)).size;
      const ruled = settled === 0
        ? "Nothing ruled out yet."
        : `${settled} ${settled === 1 ? "pair" : "pairs"} ruled out.`;
      return `Comparison ${spent} of ${Math.floor(game.actionLimit / 2)} — turn ${view.turns} of ${game.actionLimit}. ${exposed} ${ruled}`;
    },
    presentRefusal(reason) {
      return `The signed Salvage table refused this plate: ${reason}.`;
    },
    presentOracleQuery() {
      return "This pair is settled by the sealed board. Waiting for the host to answer.";
    },
    onTranscript: callbacks.onTranscript,
    onRefusal: callbacks.onRefusal,
    onReset: callbacks.onReset,
    onOracleQuery: callbacks.onOracleQuery,
    afterRender: callbacks.afterRender,
  });
}

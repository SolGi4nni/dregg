import { mountFiniteTableController } from "./finite-table-controller.js";
import { salvagePracticeOracle } from "./salvage-runtime.js";

/**
 * Salvage is `oracle-only`: the board is never named during the run, so a plate
 * has no glyph to show until the table itself resolves a pair. The controller
 * renders sealed / exposed / cleared and nothing else — before the split it
 * rendered `glyph_label` off the action row, which was the answer key.
 */
export function mountSalvageLock(root, descriptor, callbacks = {}) {
  const session = callbacks.session ?? {
    mode: "practice",
    member: 0,
    oracle: salvagePracticeOracle(descriptor, 0),
  };
  return mountFiniteTableController(root, descriptor, {
    id: "salvage-lock",
    className: "salvage-lock",
    eyebrow: "SALVAGE HATCH",
    title: "Salvage Lock",
    brief:
      "Expose sealed plates two at a time. Whether a pair matches depends on a board " +
      "you cannot see; the authenticated table asks, and records the answer it was " +
      "given. Cleared pairs stay cleared.",
    boardLabel: "Six salvage-lock plates",
    columns: 3,
    session,
    presentAction(action, view) {
      const cleared = view.cleared.includes(action.slot);
      const exposed = view.exposed === action.slot;
      const state = cleared ? "cleared" : exposed ? "exposed" : "sealed";
      const detail = cleared ? "cleared pair" : exposed ? "face up, awaiting its pair" : "sealed";
      return {
        label: action.label,
        detail,
        ariaLabel: `${action.label}, ${detail}`,
        state,
        disabled: cleared,
        pressed: exposed,
      };
    },
    presentStatus(view, run, game) {
      if (view.solved) return `Salvage lock cleared in ${run.steps.length} exposures. Local transcript ready for external verification.`;
      const exposed = view.exposed === null ? "No plate is exposed." : `Plate ${view.exposed + 1} is exposed.`;
      return `Turn ${view.turns} of ${game.actionLimit}. ${exposed}`;
    },
    presentRefusal(reason) {
      return `Authenticated Salvage table refused this plate: ${reason}.`;
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

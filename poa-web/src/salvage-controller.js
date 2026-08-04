import { mountFiniteTableController } from "./finite-table-controller.js";

export function mountSalvageLock(root, descriptor, callbacks = {}) {
  return mountFiniteTableController(root, descriptor, {
    id: "salvage-lock",
    className: "salvage-lock",
    eyebrow: "SALVAGE HATCH // TRANSPARENT DRILL",
    title: "Salvage Lock",
    brief: "Expose sealed plates. The authenticated state reveals glyphs and records cleared pairs.",
    boardLabel: "Six salvage-lock plates",
    columns: 3,
    presentAction(action, view) {
      const cleared = view.cleared.includes(action.slot);
      const exposed = view.exposed === action.slot;
      const visible = cleared || exposed;
      const state = cleared ? "cleared" : exposed ? "exposed" : "sealed";
      const glyph = visible ? action.glyphLabel : "glyph concealed";
      return {
        label: action.label,
        detail: `${glyph} · ${state}`,
        ariaLabel: `${action.label}, ${glyph}, ${state}`,
        state,
        disabled: cleared,
        pressed: exposed,
      };
    },
    presentStatus(view, run, game) {
      if (view.solved) return `Salvage lock cleared in ${run.actions.length} exposures. Local transcript ready for external verification.`;
      const exposed = view.exposed === null ? "No plate is exposed." : `Plate ${view.exposed + 1} is exposed.`;
      return `Turn ${view.turns} of ${game.actionLimit}. ${exposed}`;
    },
    presentRefusal(reason) {
      return `Authenticated Salvage table refused this plate: ${reason}.`;
    },
    onTranscript: callbacks.onTranscript,
    onRefusal: callbacks.onRefusal,
    onReset: callbacks.onReset,
    afterRender: callbacks.afterRender,
  });
}

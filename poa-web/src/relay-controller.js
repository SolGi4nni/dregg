import { mountFiniteTableController } from "./finite-table-controller.js";

const TITLE = new Map([
  ["alpha", "Alpha"],
  ["beta", "Beta"],
  ["gamma", "Gamma"],
  ["delta", "Delta"],
]);

export function mountRelayRepair(root, descriptor, callbacks = {}) {
  return mountFiniteTableController(root, descriptor, {
    id: "relay-repair",
    className: "relay-repair",
    eyebrow: "DECK RELAY // TRANSPARENT DRILL",
    title: "Relay Repair",
    brief: "Install physical links until the emitted panel state reports a restored route.",
    boardLabel: "Relay links",
    columns: 2,
    presentAction(action, view) {
      const installed = view.installed.includes(action.id);
      const route = `${TITLE.get(action.from)} to ${TITLE.get(action.to)}`;
      return {
        label: action.label,
        detail: installed ? `${route} · installed` : `${route} · spare link`,
        ariaLabel: `${route}, ${installed ? "installed" : "available"}`,
        state: installed ? "installed" : "available",
        disabled: installed,
        pressed: installed,
      };
    },
    presentStatus(view, run, game) {
      if (view.solved) return `Route restored in ${run.actions.length} actions. Local transcript ready for external verification.`;
      return `Turn ${view.turns} of ${game.actionLimit}. ${view.spares} spare links remain.`;
    },
    presentRefusal(reason) {
      return `Authenticated Relay table refused this link: ${reason}.`;
    },
    onTranscript: callbacks.onTranscript,
    onRefusal: callbacks.onRefusal,
    onReset: callbacks.onReset,
    afterRender: callbacks.afterRender,
  });
}

import { mountFiniteTableController } from "./finite-table-controller.js";

const TITLE = new Map([
  ["alpha", "Alpha"],
  ["beta", "Beta"],
  ["gamma", "Gamma"],
  ["delta", "Delta"],
  ["omega", "Omega"],
]);

function spares(count) {
  return `${count} spare${count === 1 ? "" : "s"}`;
}

export function mountRelayRepair(root, descriptor, callbacks = {}) {
  return mountFiniteTableController(root, descriptor, {
    id: "relay-repair",
    className: "relay-repair",
    eyebrow: "DECK RELAY // TRANSPARENT DRILL",
    title: "Relay Repair",
    brief:
      "Read the damage report, then install one route from intake to mast. Every link " +
      "costs spares out of one crate, and the emitted panel reports when the run can no " +
      "longer be completed.",
    boardLabel: "Relay links",
    columns: 2,
    presentAction(action, view) {
      const installed = view.installed.includes(action.id);
      const route = `${TITLE.get(action.from)} to ${TITLE.get(action.to)}`;
      const price = spares(action.cost);
      return {
        label: action.label,
        detail: installed ? `${route} · installed` : `${route} · ${price}`,
        ariaLabel: `${route}, ${installed ? "installed" : `costs ${price}`}`,
        state: installed ? "installed" : "available",
        disabled: installed,
        pressed: installed,
      };
    },
    presentStatus(view, run, game) {
      if (view.solved) return `Route restored in ${run.actions.length} actions. Local transcript ready for external verification.`;
      if (view.stranded) return `Relay stranded: no route completes within the remaining turns and ${spares(view.spares)}. Reset the drill.`;
      return `Turn ${view.turns} of ${game.actionLimit}. ${spares(view.spares)} left in the crate.`;
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

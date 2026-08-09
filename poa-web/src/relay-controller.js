import { mountFiniteTableController } from "./finite-table-controller.js";
import { relayLinkCost } from "./relay-runtime.js";

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

/**
 * Relay is `per-run-open`, so the run always names the board it is playing and
 * prices come out of that board. `session.member` is which one — chosen locally
 * in practice, opened by the host in a judged run.
 */
export function mountRelayRepair(root, descriptor, callbacks = {}) {
  const session = callbacks.session ?? { mode: "practice", member: descriptor.memberKeys[0] };
  return mountFiniteTableController(root, descriptor, {
    id: "relay-repair",
    className: "relay-repair",
    eyebrow: "DECK RELAY",
    title: "Relay Repair",
    brief:
      "Read the damage report, then install one route from intake to mast. Every link " +
      "costs spares out of one crate, and the emitted panel reports when the run can no " +
      "longer be completed. Eight boards are published; this run plays one of them.",
    boardLabel: "Relay links",
    columns: 2,
    session,
    presentAction(action, view, run, game) {
      const installed = view.installed.includes(action.id);
      const route = `${TITLE.get(action.from)} to ${TITLE.get(action.to)}`;
      const price = spares(relayLinkCost(game, run.member, action.id));
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
      const which = `Board ${run.member} of ${game.instance.modulus}`;
      if (view.solved) return `Route restored in ${run.steps.length} action${run.steps.length === 1 ? "" : "s"}. ${which}. The transcript is written down here and anyone can check it.`;
      if (view.stranded) return `Relay stranded: no route completes within the remaining turns and ${spares(view.spares)}. ${which}. Reset the drill.`;
      return `Turn ${view.turns} of ${game.actionLimit}. ${spares(view.spares)} left in the crate. ${which}.`;
    },
    presentRefusal(reason) {
      return `The signed Relay table refused this link: ${reason}.`;
    },
    onTranscript: callbacks.onTranscript,
    onRefusal: callbacks.onRefusal,
    onReset: callbacks.onReset,
    afterRender: callbacks.afterRender,
  });
}

/**
 * Deck Descent — presentation only.
 *
 * Every verdict, successor and refusal reason comes from the Lean-emitted table
 * through `finite-table-runtime.js`. This file decides nothing about the game; it
 * decides what a shaft LOOKS like, and it renders the two things this game has
 * that no other on the rack does — a PLACE the body is standing in, and a run
 * that can be over while it is still going.
 *
 * ⚑ THE SHAFT IS DRAWN BECAUSE THE SHAFT IS PUBLIC. Everything on the map — the
 * topology, how many relics each chamber holds, how many crossings from the
 * hatch, which reading damages — is in the `shaft` block, true on all eight
 * boards, and a player is entitled to all of it. What is withheld is the three
 * bits, and the map shows those as `unread` until the table resolves them.
 *
 * ⚑ `doomed` IS ON SCREEN, LOUDLY. 1030 of the 1924 emitted states are ones no
 * board still rescues, and the emitter publishes the flag precisely so a client
 * can say so. A descent whose air has already run out in every future, rendered
 * as a live board with nine dead buttons, is the exact "doomed-but-open" failure
 * the design gate raises against other games. So the status line leads with it
 * and the map goes cold.
 *
 * ⚠ It is READ, never computed. `doomedB` assumes every unread chamber sound —
 * it is a statement about what the player knows, not about the draw — and a
 * browser that recomputed it would be carrying a second copy of the rules.
 */
import { mountFiniteTableController } from "./finite-table-controller.js";
import {
  chamberStanding, descentPracticeOracle, distanceHome, rowFor, targetOf,
} from "./descent-runtime.js";

/**
 * One line per refusal, and each one says WHAT FAILED rather than "not now".
 * These follow `DeckDescent.refusalReason` case for case; that function tests its
 * conjuncts in the order `openB` does, so the reason a player is shown is the
 * first thing that actually failed and not a plausible one.
 */
const REFUSAL_COPY = Object.freeze({
  "run-banked": "You are out through the hatch. Reset to take another descent.",
  "run-doomed": "No line from here still brings the target up. Reset to take another descent.",
  "no-air": "The air is gone.",
  "no-passage": "No passage runs that way from where you are standing.",
  "already-read": "You have already read that passage — a second look buys nothing.",
  "no-shoring": "No shoring left. The supply was two and it is spent.",
  "already-safe": "That passage is already safe.",
  "not-in-a-chamber": "There is nothing to lift at the hatch.",
  "chamber-emptied": "This chamber has given up everything it holds.",
  "over-capacity": "The sling is full. A flooded crossing cost you the room.",
  "at-the-hatch": "You are at the surface; there is nothing above you.",
  "not-at-the-hatch": "You have to be at the hatch to come through it.",
  "short-sling": "Not enough in the sling to make the climb count.",
});

/** The reading a chamber shows, as one word a player can act on. */
const READING_COPY = Object.freeze({
  dark: "unread",
  sound: "sound",
  flooded: "flooded",
  shored: "shored",
});

function el(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function plural(count, one, many) {
  return `${count} ${count === 1 ? one : many}`;
}

function reading(value) {
  return READING_COPY[value] ?? value;
}

/**
 * The map. One row per node, surface first, in the order the shaft declares —
 * so a shaft that grew a chamber would grow a row here without this file being
 * told, and a shaft that renamed one would rename it here.
 */
function shaftRows(descriptor, view) {
  const shaft = descriptor.instance.shaft;
  const surface = Object.freeze({
    node: shaft.surface,
    title: "Hatch",
    detail: `${view.carried} of ${shaft.bankTarget} in the sling · air out`,
    reading: null,
    here: view.node === shaft.surface,
    cold: false,
  });
  const chambers = chamberStanding(descriptor, view).map((standing) => Object.freeze({
    node: standing.chamber,
    title: standing.chamber,
    detail: [
      standing.held > 0 ? `${plural(standing.held, "relic", "relics")} left` : "emptied",
      standing.carried > 0 ? `${standing.carried} in the sling` : null,
      `${plural(standing.crossingsHome, "crossing", "crossings")} from air`,
    ].filter(Boolean).join(" · "),
    reading: reading(standing.lore),
    here: standing.here,
    cold: standing.damaging,
  }));
  return Object.freeze([surface, ...chambers]);
}

export function mountDeckDescent(root, descriptor, callbacks = {}) {
  const shaft = descriptor.instance.shaft;
  const session = callbacks.session ?? {
    mode: "practice",
    member: 0,
    oracle: descentPracticeOracle(descriptor, 0),
  };
  const map = el("ol", "descent-shaft");
  map.setAttribute("aria-label", "The shaft, from the hatch down");
  let attached = false;

  return mountFiniteTableController(root, descriptor, {
    id: "deck-descent",
    className: "deck-descent",
    eyebrow: "LOWER SPINE",
    title: "Deck Descent",
    brief:
      // ⚠ "shoring costs supply INSTEAD" was wrong and contradicted this brief's own
      // first clause: `air_per_action` is 1 for every verb, so shoring spends an
      // action of air AND one of the two shorings. Measured: 9 air before the shore,
      // 8 after. A player who budgeted on "instead" planned a route one action longer
      // than the air pays for.
      `${shaft.air} actions of air, and every one of them costs the same whether you spend it ` +
      `walking or looking. Each passage is sound or flooded and you are told neither: reading one ` +
      `buys the answer, shoring one spends a supply on top of the air and makes the crossing safe ` +
      `without answering anything — you have ${shaft.shoring}. A flooded ` +
      `crossing takes a body — it costs you room in the sling, not a life. Come back through the ` +
      `hatch with ${shaft.bankTarget} relics.`,
    boardLabel: `Nine verbs over the ${shaft.chambers.length}-chamber shaft`,
    columns: 3,
    session,
    presentAction: (action, view, run) => {
      const row = rowFor(descriptor, run, action.id);
      const target = targetOf(shaft, view.node, action);
      if (!row || row.verdict === "refuse") {
        return {
          label: action.label,
          detail: row ? shortRefusal(row.reason) : "closed here",
          ariaLabel: `${action.label}. Refused: ${REFUSAL_COPY[row?.reason] ?? "closed here"}`,
          state: "spent",
          // ⚑ DISABLED, not merely greyed — and this game is the one where it
          // matters. 1030 of the 1924 emitted states are doomed, and in every one
          // of them all nine rows refuse. Nine live-looking buttons over a run
          // that is already lost is the "doomed-but-open" board the design gate
          // raises against other games; the reason is on the button face and the
          // doom is in the status line, so nothing is hidden by the control being
          // honestly dead.
          disabled: true,
        };
      }
      const asks = row.verdict === "resolve";
      const detail = actionDetail(descriptor, action, view, target, asks);
      return {
        label: action.label,
        detail,
        ariaLabel: `${action.label}. ${detail}.` +
          (asks ? " This move reads a passage nobody has read; the shaft answers it." : ""),
        // ⚑ The gold border means "this move asks the dark a question". It is the
        // whole decision in this game — when to buy information — so it is a
        // visible property of the button and not something to work out.
        state: asks ? "exposed" : "live",
      };
    },
    presentStatus: (view) => {
      if (view.banked) {
        return `Out through the hatch with ${plural(view.carried, "relic", "relics")}. ` +
          `${view.turns} of ${shaft.air} air spent.`;
      }
      if (view.doomed) {
        return `Nothing from here still brings ${shaft.bankTarget} relics up — not on any shaft ` +
          `still consistent with what you have read. ${view.air} air left and no line home.`;
      }
      const home = distanceHome(descriptor, view);
      const unread = shaft.chambers.filter((chamber) => view.lore[chamber] === "dark").length;
      return [
        `At the ${view.node}`,
        `${plural(view.air, "action", "actions")} of air`,
        `sling ${view.carried} of ${view.capacity}`,
        `${plural(home, "crossing", "crossings")} from air`,
        unread > 0 ? `${plural(unread, "passage", "passages")} unread` : "every passage read",
      ].join(" · ");
    },
    presentRefusal: (reason) => REFUSAL_COPY[reason] ?? "That move is closed here.",
    presentOracleQuery: () =>
      "Waiting for the host to read that passage against the sealed shaft.",
    afterRender: (shell, view) => {
      if (!attached) {
        shell.append(map);
        attached = true;
      }
      map.dataset.doomed = String(view.doomed);
      map.replaceChildren(...shaftRows(descriptor, view).map((row) => {
        const item = el("li", "descent-shaft__node");
        item.dataset.node = row.node;
        if (row.here) item.dataset.here = "true";
        if (row.cold) item.dataset.cold = "true";
        item.append(el("span", "descent-shaft__name", row.title));
        if (row.reading !== null) item.append(el("span", "descent-shaft__reading", row.reading));
        item.append(el("span", "descent-shaft__detail", row.detail));
        return item;
      }));
      callbacks.afterRender?.(shell, view);
    },
    onTranscript: callbacks.onTranscript,
    onRefusal: callbacks.onRefusal,
    onReset: callbacks.onReset,
    onOracleQuery: callbacks.onOracleQuery,
  });
}

/** The refusal, short enough for a button face. */
function shortRefusal(reason) {
  switch (reason) {
    case "run-banked": return "run is over";
    case "run-doomed": return "run is over";
    case "no-air": return "no air";
    case "no-passage": return "no passage";
    case "already-read": return "already read";
    case "no-shoring": return "no shoring left";
    case "already-safe": return "already safe";
    case "not-in-a-chamber": return "nothing here to lift";
    case "chamber-emptied": return "emptied";
    case "over-capacity": return "sling full";
    case "at-the-hatch": return "at the surface";
    case "not-at-the-hatch": return "not at the hatch";
    case "short-sling": return "sling too light";
    default: return reason;
  }
}

/**
 * What a verb is about to do, in one line, from emitted fields only.
 *
 * ⚠ The `descend` line is the one that has to stay honest. When the passage is
 * unread this says so and says nothing about the odds, because THERE ARE NO
 * PUBLISHED ODDS: the descriptor names both successors and withholds which, and
 * a client that offered a probability would be inventing a distribution over a
 * draw it cannot see. Vent Crawl publishes its hazard and so its buttons carry
 * numbers; this game does not, and so these do not.
 */
function actionDetail(descriptor, action, view, target, asks) {
  const shaft = descriptor.instance.shaft;
  switch (action.kind) {
    case "survey":
      return `Read the ${target} passage · costs 1 air`;
    case "shore":
      return `Make the ${target} passage safe · ${plural(view.shoring, "shoring", "shoring")} left`;
    case "descend": {
      const known = reading(view.lore[target]);
      if (asks) return `Cross into the ${target} — unread, and the shaft decides`;
      return shaft.damaging.includes(view.lore[target])
        ? `Cross into the ${target} — ${known}, and it costs a body`
        : `Cross into the ${target} — ${known}`;
    }
    case "lift": {
      const held = shaft.relicCount[view.node] - view.taken[view.node];
      return `${plural(held, "relic", "relics")} still in this chamber · sling ${view.carried} of ${view.capacity}`;
    }
    case "ascend":
      return `Climb to the ${shaft.parent[view.node]}`;
    case "extract":
      return `${view.carried} of ${shaft.bankTarget} in the sling`;
    default:
      return action.label;
  }
}

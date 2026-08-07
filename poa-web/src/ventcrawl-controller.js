import {
  currentState, nextRungHauls, play, rowFor, rungOdds, startRun, transcript,
} from "./ventcrawl-runtime.js";

/**
 * Vent Crawl — the browser face.
 *
 * ⚠ This controller does NOT mount `finite-table-controller.js`. That controller
 * presents a grid of same-shaped actions, and this game has two verbs whose whole
 * tension is that they are NOT the same shape: one is a wager with published odds
 * and a set of possible prizes, the other is certain. Rendering them as two cells
 * of a table would flatten exactly the thing the game is about. (It is also the
 * suite-rack lane's file this cycle and not this lane's to widen.)
 *
 * ## The one rule this face has to obey
 *
 * **The player sees the current odds and the next rung's odds before choosing.**
 * Push-your-luck is near-misses you could see coming; a hidden die feel is the
 * failure mode. So the crawl button always carries, in this order:
 *
 *   1. the exact flood chance of the rung it enters, as `n/faces` AND as a
 *      percentage, read out of the descriptor and never computed from a model;
 *   2. what that rung pays on each day still on the table — a range when the day
 *      is ambiguous, a single number once the carry ladder has named it;
 *   3. what is in the sling right now, which is what a flood takes.
 *
 * And the bank button carries the certain number, so the comparison is on screen
 * rather than in the player's head.
 *
 * ## What it never does
 *
 * It never derives an outcome. In a judged run the host answers, and
 * `ventcrawl-runtime.js` refuses any state the row did not name. In practice the
 * roll is local and visible and the transcript says so.
 */

// Display names only, and `veinName` falls back to the raw id, so this map can
// never refuse a day the descriptor declares — it is a nicety, not a schema.
// The eight veins are four SEAMS by what the bottom rung does: the seam is
// readable by rung 3 and the bottom is not readable at all until you are on it.
const VEIN_TITLE = new Map([
  ["barren", "Barren"],
  ["barren-pocket", "Barren, pocket at the bottom"],
  ["patchy", "Patchy"],
  ["patchy-pocket", "Patchy, pocket at the bottom"],
  ["layered", "Layered"],
  ["layered-pocket", "Layered, pocket at the bottom"],
  ["fools-lode", "Fool's lode"],
  ["motherlode", "Motherlode"],
]);

function el(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function veinName(id) {
  return VEIN_TITLE.get(id) ?? id;
}

function oddsLabel(odds) {
  if (!odds) return "no deeper rung";
  return `${odds.below}/${odds.faces} — ${odds.percent.toFixed(1)}% flood`;
}

/**
 * Describe the prize half of the wager. A RANGE while the day is ambiguous is the
 * honest rendering: the player genuinely does not know which, and collapsing it to
 * an average would be this face inventing a number the rules do not state.
 */
function haulLabel(hauls) {
  if (hauls.length === 0) return "nothing deeper";
  const gains = hauls.map((h) => h.gain);
  const low = Math.min(...gains);
  const high = Math.max(...gains);
  if (low === high) return `+${low} salvage`;
  return `+${low} to +${high} salvage, depending on the day`;
}

export function mountVentCrawl(root, descriptor, callbacks = {}) {
  const session = callbacks.session ?? { mode: "practice" };
  let run = startRun(descriptor, session);
  let lastRefusal = null;

  const frame = el("section", "vent-crawl");
  frame.id = "vent-crawl";
  const eyebrow = el("p", "vent-crawl__eyebrow", "KHOVOKHI VENT SHAFTS");
  const title = el("h2", "vent-crawl__title", "Vent Crawl");
  const brief = el("p", "vent-crawl__brief",
    "Salvage in the dark with the water behind you. Every rung down is worth more " +
    "and is likelier to flood — the odds are printed on the button. What the shaft " +
    "is paying today is the same for every crew and nobody is told; you find out by " +
    "going down and looking.");
  frame.append(eyebrow, title, brief);

  const shaft = el("ol", "vent-crawl__shaft");
  const status = el("p", "vent-crawl__status");
  status.setAttribute("role", "status");
  status.setAttribute("aria-live", "polite");
  const day = el("p", "vent-crawl__day");
  const controls = el("div", "vent-crawl__controls");
  const crawlButton = el("button", "vent-crawl__verb vent-crawl__verb--crawl");
  crawlButton.type = "button";
  const bankButton = el("button", "vent-crawl__verb vent-crawl__verb--bank");
  bankButton.type = "button";
  controls.append(crawlButton, bankButton);
  const resetButton = el("button", "vent-crawl__reset", "Drop into another shaft");
  resetButton.type = "button";
  frame.append(shaft, day, status, controls, resetButton);

  function renderShaft(state) {
    shaft.replaceChildren();
    for (let rung = 1; rung <= descriptor.depthCap; rung += 1) {
      const below = descriptor.floodBelow[rung];
      const item = el("li", "vent-crawl__rung");
      item.dataset.rung = String(rung);
      if (rung === state.depth) item.dataset.here = "true";
      if (rung < state.depth) item.dataset.passed = "true";
      item.append(el("span", "vent-crawl__rung-index", `Rung ${rung}`));
      // ⚑ The whole ladder is on screen at once, not just the next step. A player
      // choosing at rung 3 is choosing against rungs 4, 5 and 6 as well, and the
      // escalation is only legible if it is visible.
      item.append(el("span", "vent-crawl__rung-odds",
        `${below}/${descriptor.faces}`));
      const paying = descriptor.veins
        .filter((v) => state.stillPossible.includes(v.id))
        .map((v) => v.yields[rung - 1]);
      const low = Math.min(...paying);
      const high = Math.max(...paying);
      item.append(el("span", "vent-crawl__rung-pay",
        low === high ? `+${low}` : `+${low}–${high}`));
      shaft.append(item);
    }
  }

  function renderDay(state) {
    const possible = state.stillPossible;
    if (possible.length === 0) {
      day.textContent = "";
      return;
    }
    if (possible.length === 1) {
      const vein = descriptor.veinById.get(possible[0]);
      day.textContent =
        `The shaft has named itself: ${veinName(possible[0])}. ` +
        `Bottom rung pays out at ${vein.carry[descriptor.depthCap]}.`;
      return;
    }
    day.textContent =
      `Today could still be ${possible.map(veinName).join(" or ")} — ` +
      `${possible.length} of ${descriptor.veins.length} days still fit what you have ` +
      `pulled.`;
  }

  function render() {
    const state = currentState(descriptor, run);
    renderShaft(state);
    renderDay(state);

    const crawlRow = rowFor(descriptor, run, descriptor.crawlAction);
    const bankRow = rowFor(descriptor, run, descriptor.bankAction);
    const odds = rungOdds(descriptor, state);
    const hauls = nextRungHauls(descriptor, state);

    if (crawlRow?.verdict === "wager") {
      crawlButton.disabled = false;
      crawlButton.replaceChildren(
        el("span", "vent-crawl__verb-name", `Crawl to rung ${state.depth + 1}`),
        el("span", "vent-crawl__verb-risk", oddsLabel(odds)),
        el("span", "vent-crawl__verb-prize", haulLabel(hauls)),
        el("span", "vent-crawl__verb-stake", `${state.carried} in the sling to lose`),
      );
      crawlButton.setAttribute("aria-label",
        `Crawl to rung ${state.depth + 1}. Floods ${odds.below} times in ` +
        `${odds.faces}. ${haulLabel(hauls)}. You are carrying ${state.carried}, and a ` +
        `flood takes all of it.`);
    } else {
      crawlButton.disabled = true;
      crawlButton.replaceChildren(
        el("span", "vent-crawl__verb-name", "Crawl"),
        el("span", "vent-crawl__verb-risk",
          crawlRow ? refusalCopy(crawlRow.reason) : "—"),
      );
      crawlButton.setAttribute("aria-label",
        `Crawl unavailable: ${crawlRow ? refusalCopy(crawlRow.reason) : "unavailable"}`);
    }

    if (bankRow?.verdict === "accept") {
      bankButton.disabled = false;
      bankButton.replaceChildren(
        el("span", "vent-crawl__verb-name", "Bank the sling"),
        el("span", "vent-crawl__verb-risk", "certain"),
        el("span", "vent-crawl__verb-prize", `${state.carried} salvage, banked`),
      );
      bankButton.setAttribute("aria-label",
        `Bank the sling. Certain. ${state.carried} salvage.`);
    } else {
      bankButton.disabled = true;
      bankButton.replaceChildren(
        el("span", "vent-crawl__verb-name", "Bank"),
        el("span", "vent-crawl__verb-risk",
          bankRow ? refusalCopy(bankRow.reason) : "—"),
      );
    }

    status.textContent = statusCopy(state);
    resetButton.hidden = !state.terminal;
    if (lastRefusal) {
      status.textContent =
        `The authenticated vent table refused that: ${refusalCopy(lastRefusal)}.`;
    }
  }

  function refusalCopy(reason) {
    switch (reason) {
      case "run-banked": return "you are already out of the shaft";
      case "run-drowned": return "the water took this run";
      case "at-the-bottom": return "there is no rung below this one";
      default: return reason;
    }
  }

  // ⚠ The END SCREEN is global and keyed by shape (`run-summary.js`); this game
  // has none of its own, and the two terminal lines below are the in-run status
  // strip only — one factual sentence each, so the screen that follows is not
  // pre-empted by a second, differently-worded ending. Practice copy is likewise
  // standardized upstream and is deliberately absent here.
  function statusCopy(state) {
    if (state.banked) {
      return `Banked ${state.carried} salvage out of rung ${state.depth}.`;
    }
    if (state.drowned) {
      return `Flooded at rung ${state.depth}. The sling is empty; the shaft map is not.`;
    }
    const odds = rungOdds(descriptor, state);
    return `Rung ${state.depth}. ${state.carried} in the sling. ` +
      `The next rung floods ${oddsLabel(odds)}.`;
  }

  function act(actionId) {
    const result = play(descriptor, run, actionId, callbacks.hostStep ?? null);
    lastRefusal = result.refused;
    run = result.run;
    render();
    if (result.refused) {
      callbacks.onRefusal?.(result.refused);
      return;
    }
    const state = currentState(descriptor, run);
    if (state.terminal) {
      // ⚠ TWO arguments, and the second is not optional decoration. The shared
      // end screen reads a finished run through `runOutcome(shape, run,
      // descriptor)`, so a controller that reported only the transcript would
      // reach `app.js` with `run` undefined and the screen would refuse. This is
      // the same call shape `finite-table-controller.js` makes.
      callbacks.onTranscript?.(transcript(descriptor, run), run);
    }
  }

  function restart() {
    run = startRun(descriptor, session);
    lastRefusal = null;
    render();
    return run;
  }

  crawlButton.addEventListener("click", () => act(descriptor.crawlAction));
  bankButton.addEventListener("click", () => act(descriptor.bankAction));
  resetButton.addEventListener("click", () => {
    restart();
    callbacks.onReset?.();
  });

  root.replaceChildren(frame);
  render();
  callbacks.afterRender?.(frame);

  return {
    element: frame,
    get run() { return run; },
    get transcript() { return transcript(descriptor, run); },
    /**
     * ⚠ `reset` is part of the mount CONTRACT, not a convenience: the rack's
     * "Run it again" control calls it on whatever controller is active, and a
     * controller without one would silently do nothing at the one moment a
     * player has asked for another run.
     */
    reset() { return restart(); },
    destroy() { root.replaceChildren(); },
  };
}

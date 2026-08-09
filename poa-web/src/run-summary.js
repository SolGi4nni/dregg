import { ArtifactRefusal } from "./poag1.js";
import { verificationFold } from "./game-rack.js";
import { tableRunIsClosed, tableRunIsStuck, tableRunView } from "./finite-table-runtime.js";
import { ventCrawlOutcome } from "./ventcrawl-runtime.js";

/**
 * ONE END-OF-RUN SCREEN, AND ONE LADDER, FOR EVERY GAME.
 *
 * ⚠ PRACTICE IS NOT RUNG ZERO. It is the whole of its own branch. The judged path
 * is submitted → judged → finalized, with refused hanging off it; a practice run
 * never enters that path and never leaves its own, because a practice board was
 * chosen by this browser and there is no commitment binding it to anything. If
 * practice were drawn as the first step of five, a rehearsal would read as
 * "1 of 5 done" toward a settled result, which is exactly the confusion the mode
 * split in `finite-table-controller.js` and `hidden-instance.js` exists to stop.
 *
 * So the reachability table below is written OUT, one row per status, rather than
 * computed from an index. An index would make practice look like a prefix of the
 * judged path — the arithmetic would be doing the lying, quietly.
 */

export const RUN_STATUSES = Object.freeze(["practice", "submitted", "judged", "finalized", "refused"]);

export const RUN_RUNGS = Object.freeze({
  practice: Object.freeze({
    id: "practice",
    label: "PRACTICE",
    detail: "This browser picked the board and answered itself. Nothing is scored and nothing was sent.",
  }),
  submitted: Object.freeze({
    id: "submitted",
    label: "SUBMITTED",
    detail: "The transcript reached a PoA node against an open, curator-committed slot. Nothing is judged yet.",
  }),
  judged: Object.freeze({
    id: "judged",
    label: "JUDGED",
    detail: "The node re-derived the committed instance and judged the run. It is not final yet.",
  }),
  finalized: Object.freeze({
    id: "finalized",
    label: "FINALIZED",
    detail: "The judged run is in a finalized block. This is the only rung on which anything settles.",
  }),
  refused: Object.freeze({
    id: "refused",
    label: "REFUSED",
    detail: "The node refused the run and said why. Nothing settled, and the reason is on the record.",
  }),
});

const CURRENT = "current";
const REACHED = "reached";
const AHEAD = "ahead";
const UNREACHABLE = "unreachable";

/**
 * Rung state per status, written out. `unreachable` means *not on this run's
 * path at all* and is drawn as absent, never as "not yet".
 */
const LADDER = Object.freeze({
  practice: Object.freeze({ practice: CURRENT, submitted: UNREACHABLE, judged: UNREACHABLE, finalized: UNREACHABLE, refused: UNREACHABLE }),
  submitted: Object.freeze({ practice: UNREACHABLE, submitted: CURRENT, judged: AHEAD, finalized: AHEAD, refused: AHEAD }),
  judged: Object.freeze({ practice: UNREACHABLE, submitted: REACHED, judged: CURRENT, finalized: AHEAD, refused: AHEAD }),
  finalized: Object.freeze({ practice: UNREACHABLE, submitted: REACHED, judged: REACHED, finalized: CURRENT, refused: UNREACHABLE }),
  refused: Object.freeze({ practice: UNREACHABLE, submitted: REACHED, judged: UNREACHABLE, finalized: UNREACHABLE, refused: CURRENT }),
});

/** The legal moves. Practice has none: a rehearsal cannot become a result. */
const ADVANCE = Object.freeze({
  practice: Object.freeze([]),
  submitted: Object.freeze(["judged", "refused"]),
  judged: Object.freeze(["finalized", "refused"]),
  finalized: Object.freeze([]),
  refused: Object.freeze([]),
});

/**
 * ⚑ `lost` IS THE FOURTH OUTCOME, AND IT WAS OWED.
 *
 * For a long time this list had three values and `unsolved` carried two different
 * endings: "the window closed" and "you took a bet and it went against you". They
 * are not the same thing and the difference is the entire point of a game that
 * lets you lose. `ventcrawl-runtime.js` named the gap in its own docblock — a
 * drowned crawl ends EARLY, on a wager the player chose, with turns still on the
 * clock — and said the repair was one of two: a fourth outcome, or a note. It is
 * the fourth outcome, because a note under a headline reading "Window closed."
 * would have left the headline lying.
 *
 * Artificer Logic makes it unavoidable: 717 of its states are a wrong law named,
 * every action from them refuses, and the run is over on a MISTAKE with charges
 * unspent. `refused` is not that either — that rung is for a NODE refusing a
 * submitted run, not for a table refusing a move.
 */
const OUTCOMES = Object.freeze(["solved", "unsolved", "lost", "refused"]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

export function isRunStatus(value) {
  return RUN_STATUSES.includes(value);
}

/** A run has settled exactly once, and only on one rung. */
export function isSettled(status) {
  refuse(isRunStatus(status), "run-status", `unknown run status: ${status}`);
  return status === "finalized";
}

/** A run counts toward anything only after a node has judged it. */
export function isScored(status) {
  refuse(isRunStatus(status), "run-status", `unknown run status: ${status}`);
  return status === "judged" || status === "finalized";
}

export function runLadder(status) {
  refuse(isRunStatus(status), "run-status", `unknown run status: ${status}`);
  const states = LADDER[status];
  return Object.freeze(RUN_STATUSES.map((id) => Object.freeze({ ...RUN_RUNGS[id], state: states[id] })));
}

/**
 * Move a run along the ladder, or refuse. The refusal that matters is
 * `run-status-practice-frozen`: without it, one careless assignment turns a
 * rehearsal into a submitted run and every honest label downstream is repeating
 * a lie it was handed.
 */
export function advanceRunStatus(from, to) {
  refuse(isRunStatus(to), "run-status", `unknown run status: ${to}`);
  if (from === null || from === undefined) {
    refuse(to === "practice" || to === "submitted", "run-status-start", `a run cannot start at ${to}`);
    return to;
  }
  refuse(isRunStatus(from), "run-status", `unknown run status: ${from}`);
  refuse(from !== "practice", "run-status-practice-frozen", "a practice run cannot be advanced: it was never submitted and there is no commitment binding its board");
  refuse(ADVANCE[from].includes(to), "run-status-transition", `a ${from} run cannot become ${to}`);
  return to;
}

const HEADLINE = Object.freeze({
  solved: "Cleared it.",
  unsolved: "Window closed.",
  lost: "Lost it.",
  refused: "Refused.",
});

/**
 * ⚠ SOLVED IS READ OFF THE VIEW, NOT OFF `run.terminal`.
 *
 * `terminal` is a per-state flag and the emitters do not all use it to mean the
 * same thing: Relay emits `terminal = routed`, so there it IS solved; Artificer
 * emits `terminal` only on an identification and leaves a wrong naming at
 * `terminal: false` with every action refusing. Reading `run.terminal` as "solved"
 * therefore reported a lost artificer run as `Cleared it.` — and, because `over`
 * was read the same way, never reported it at all until the clock ran out.
 *
 * So: solved comes from `view.solved`, over comes from the ROWS, and the choice
 * between `lost` and `unsolved` is whether the table stopped the run or the clock
 * did.
 */
const finiteOutcome = (run, descriptor) => {
  const view = tableRunView(descriptor, run);
  return {
    over: tableRunIsClosed(descriptor, run),
    outcome: view.solved === true
      ? "solved"
      : (tableRunIsStuck(descriptor, run) ? "lost" : "unsolved"),
    actions: run.steps.length,
    actionLimit: descriptor.actionLimit,
  };
};

/**
 * "Is this run over, and how did it go" — keyed by SHAPE, never by game id.
 *
 * `descriptor-shape.js` already establishes that a game landing in an existing
 * shape needs no new runtime and no new controller. This is the same promise on
 * the way out: a new machine-family or parametric game reaches the end screen
 * through the row that is already here, and only a genuinely NEW shape has to
 * teach this anything — at which point it refuses rather than picking a row that
 * looks close, because "close" would mean reporting the wrong action count.
 */
const OUTCOME_BY_SHAPE = Object.freeze({
  deduction: (run, descriptor) => ({
    over: run.solved === true || run.exhausted === true,
    outcome: run.solved === true ? "solved" : "unsolved",
    actions: run.turns.length,
    actionLimit: descriptor.maxTurns,
  }),
  "probe-oracle": (run, descriptor) => ({
    over: run.solved === true || run.exhausted === true,
    outcome: run.solved === true ? "solved" : "unsolved",
    actions: run.probes.length,
    actionLimit: descriptor.actionLimit,
  }),
  "machine-family": finiteOutcome,
  parametric: finiteOutcome,
  // ⚠ Vent Crawl does NOT come through `finiteOutcome`: its runtime is its own,
  // its rows carry `wager` rather than `resolve`, and its terminal states are the
  // two ways out of a shaft. The reading lives beside that runtime, in the record
  // this table's rows produce.
  "push-your-luck": ventCrawlOutcome,
});

export function runOutcome(shape, run, descriptor) {
  const read = OUTCOME_BY_SHAPE[shape];
  refuse(typeof read === "function", "run-shape", `no end-of-run reading exists for the ${shape} shape`);
  refuse(run && descriptor, "run-shape", "reading a run needs the run and its descriptor");
  const result = read(run, descriptor);
  refuse(Number.isSafeInteger(result.actions) && result.actions >= 0, "run-actions", "run action count is not an exact integer");
  return Object.freeze({ ...result, mode: run.mode });
}

/**
 * The end-of-run screen, as data. Every game builds the same record, so the
 * screen is the same size and says the same things in the same order — and the
 * honest bits (`settled`, `scored`) are DERIVED from the status rather than
 * passed in beside it, so no caller can hand in a flattering pair.
 */
export function buildRunSummary({ card, status, outcome, actions, actionLimit, transcript = null, note = null } = {}) {
  refuse(card && typeof card.gameId === "string", "run-summary-card", "an end screen needs the rack card it belongs to");
  refuse(isRunStatus(status), "run-status", `unknown run status: ${status}`);
  refuse(OUTCOMES.includes(outcome), "run-outcome", `unknown run outcome: ${outcome}`);
  refuse(Number.isSafeInteger(actions) && actions >= 0, "run-actions", "an end screen needs an exact action count");
  refuse(
    actionLimit === null || (Number.isSafeInteger(actionLimit) && actionLimit >= 0),
    "run-action-limit",
    "an end screen action limit must be an exact integer or absent",
  );
  refuse(note === null || (typeof note === "string" && note.length <= 240), "run-note", "an end screen note is at most one short line");

  const settled = isSettled(status);
  const scored = isScored(status);
  const spent = actionLimit === null
    ? `${actions} action${actions === 1 ? "" : "s"}`
    : `${actions} of ${actionLimit} actions`;
  return Object.freeze({
    gameId: card.gameId,
    name: card.name,
    headline: HEADLINE[outcome],
    outcome,
    actions,
    actionLimit,
    detail: `${card.name} · ${spent}`,
    status,
    settled,
    scored,
    statusLabel: RUN_RUNGS[status].label,
    statusDetail: note ?? RUN_RUNGS[status].detail,
    ladder: runLadder(status),
    controls: Object.freeze([
      Object.freeze({ id: "again", label: "Run it again" }),
      Object.freeze({ id: "rack", label: "Back to the rack" }),
    ]),
    transcript: typeof transcript === "string" ? transcript : null,
    verification: card.verification ?? Object.freeze([]),
  });
}

function element(tag, className, textContent) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (textContent !== undefined) node.textContent = textContent;
  return node;
}

/** Render the end screen. Same nodes, same order, every game. */
export function mountRunSummary(root, summary, { onAgain, onRack } = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a run-summary root is required");
  const shell = element("section", "run-summary");
  shell.dataset.status = summary.status;
  shell.dataset.outcome = summary.outcome;
  shell.dataset.settled = String(summary.settled);
  shell.setAttribute("role", "status");
  shell.setAttribute("aria-live", "polite");

  const head = element("div", "run-summary__head");
  head.append(element("h3", "run-summary__headline", summary.headline), element("p", "run-summary__detail", summary.detail));

  const ladder = element("ol", "run-summary__ladder");
  ladder.setAttribute("aria-label", "Run status ladder");
  for (const rung of summary.ladder) {
    if (rung.state === "unreachable") continue;
    const item = element("li", `run-summary__rung run-summary__rung--${rung.state}`);
    item.dataset.rung = rung.id;
    item.dataset.state = rung.state;
    // Labels only: the note below carries the current rung's sentence, and
    // repeating it inside the rung made the screen say the same thing twice.
    item.append(element("b", "", rung.label));
    if (rung.state === "current") item.setAttribute("aria-current", "step");
    ladder.append(item);
  }

  const note = element("p", "run-summary__note", summary.statusDetail);
  const controls = element("div", "run-summary__controls");
  const handlers = { again: onAgain, rack: onRack };
  for (const control of summary.controls) {
    const button = element("button", `run-summary__control run-summary__control--${control.id}`, control.label);
    button.type = "button";
    button.dataset.control = control.id;
    const handler = handlers[control.id];
    if (typeof handler === "function") button.addEventListener("click", () => handler(summary));
    controls.append(button);
  }

  shell.append(head, ladder, note, controls);
  if (summary.transcript !== null) {
    const fold = element("details", "verify-fold verify-fold--transcript");
    fold.append(element("summary", "verify-fold__summary", "Transcript"));
    fold.append(element("pre", "verify-fold__transcript", summary.transcript));
    shell.append(fold);
  }
  shell.append(verificationFold(summary.verification, summary.name));
  root.replaceChildren(shell);
  return shell;
}

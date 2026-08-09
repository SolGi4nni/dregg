import {
  TableOracleQuery,
  TableTransitionRefusal,
  canonicalTableTranscript,
  createFiniteTableRun,
  submitFiniteTableAction,
  tableRowFor,
  tableRunView,
} from "./finite-table-runtime.js";

const NAVIGATION_KEYS = new Set(["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Home", "End"]);

export function nextRovingIndex(current, key, count, columns) {
  if (!NAVIGATION_KEYS.has(key) || count < 1) return current;
  if (key === "Home") return 0;
  if (key === "End") return count - 1;
  const delta = key === "ArrowLeft" ? -1 : key === "ArrowRight" ? 1 : key === "ArrowUp" ? -columns : columns;
  return (current + delta + count * (Math.ceil(Math.abs(delta) / count) + 1)) % count;
}

function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

/**
 * What the player is told about the run they are in. A practice rehearsal and a
 * judged attempt produce different transcripts, so they must not look alike on
 * screen either — the point of the split is lost if a player cannot tell which
 * one they just finished.
 */
function boundaryCopy(run) {
  if (run.mode === "practice") {
    return "PRACTICE — this browser chose the board itself, so nothing here is scored: " +
      "no ranking, no reward, and no receipt anybody else can read.";
  }
  return `JUDGED — slot ${run.slot}, commitment ${run.slotCommitment.slice(0, 16)}…. ` +
    "The board came out of a secret the curator holds, and it is opened when the slot closes. " +
    "This transcript is written down here and settles nothing until a node checks it.";
}

/**
 * Mount a finite-table game's controls. The controller dispatches authenticated
 * rows and renders their literal views; it has no game transition function.
 *
 * A row whose successor depends on the hidden instance raises `TableOracleQuery`
 * rather than guessing. `session.oracle` answers it locally in practice; in a
 * judged run the controller parks, reports the question through `onOracleQuery`,
 * and waits for `resolveOracle` to bring the host's answer back. It never
 * invents one, and it cannot: it does not have the board.
 */
export function mountFiniteTableController(root, descriptor, options) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a mount root is required");
  const session = options.session ?? { mode: "practice", member: descriptor.memberKeys[0] };
  let run = createFiniteTableRun(descriptor, session);
  let pending = null;
  let rovingIndex = 0;
  const listeners = [];

  const shell = element("section", `poa-minigame ${options.className}`);
  shell.setAttribute("aria-labelledby", `${options.id}-title`);
  shell.dataset.mode = run.mode;
  const header = element("header", "poa-minigame__header");
  const heading = element("div");
  const eyebrow = element("p", "poa-minigame__eyebrow", `${options.eyebrow} // ${run.mode === "practice" ? "PRACTICE" : "JUDGED"}`);
  const title = element("h2", "poa-minigame__title", options.title);
  title.id = `${options.id}-title`;
  heading.append(eyebrow, title);
  const reset = element("button", "poa-minigame__reset", "Reset drill");
  reset.type = "button";
  header.append(heading, reset);

  const brief = element("p", "poa-minigame__brief", options.brief);

  /**
   * ⚑ ONE BOARD, OR ONE BOARD PER VERB CLASS.
   *
   * A game whose actions are all the same KIND of decision — six plates, five
   * links — is one grid, and that is what every game shipped as. Artificer Logic
   * is not: eight of its actions BUY INFORMATION and sixteen COMMIT AN ANSWER,
   * and rendering twenty-four identical cells in one column made the only
   * decision the game asks invisible, with a wrong answer one mis-tap away from
   * a question. It also wants different widths — "IIB" and "no two neighbouring
   * cogs share a metal" do not belong in the same track.
   *
   * `boardGroups` is therefore optional and must PARTITION the action list: every
   * action lands on exactly one board, or the controller refuses. A verb quietly
   * dropped from the board is a move a player cannot make and cannot see.
   */
  const groups = (options.boardGroups?.(descriptor) ?? [
    { id: "all", label: options.boardLabel, columns: options.columns, actionIds: descriptor.actions.map((action) => action.id) },
  ]).map((group) => ({ ...group, actionIds: [...group.actionIds] }));
  const partitioned = groups.flatMap((group) => group.actionIds);
  if (partitioned.length !== descriptor.actions.length ||
      new Set(partitioned).size !== partitioned.length ||
      !descriptor.actions.every((action) => partitioned.includes(action.id))) {
    throw new TypeError(`${options.id} board groups do not partition its actions`);
  }

  const boards = element("div", "poa-minigame__boards");
  const grids = groups.map((group) => {
    const grid = element("div", "poa-minigame__board");
    grid.dataset.group = group.id;
    // ⚠ A data attribute, not `style.setProperty`. This page serves
    // `style-src 'self'` with no `unsafe-inline`, so an inline style property is
    // BLOCKED by the terminal's own CSP — the board would have silently fallen
    // back to two columns on the real site while every test passed.
    grid.dataset.columns = String(group.columns);
    grid.setAttribute("role", options.boardRole ?? "group");
    grid.setAttribute("aria-label", group.label);
    // A single unnamed board needs no visible heading; two do, or the split is a
    // gap in the layout and nothing a player can name.
    if (groups.length > 1) {
      const legend = element("p", "poa-minigame__board-label", group.label);
      legend.setAttribute("aria-hidden", "true");
      boards.append(legend);
    }
    boards.append(grid);
    return grid;
  });
  const status = element("p", "poa-minigame__status");
  status.id = `${options.id}-status`;
  status.setAttribute("role", "status");
  status.setAttribute("aria-live", "polite");
  status.setAttribute("aria-atomic", "true");
  const boundary = element("p", "poa-minigame__boundary", boundaryCopy(run));
  shell.append(header, brief, boards, status, boundary);
  root.replaceChildren(shell);

  const groupOfAction = new Map(groups.flatMap((group, index) => group.actionIds.map((id) => [id, index])));
  const buttons = descriptor.actions.map((action, index) => {
    const button = element("button", "poa-minigame__action");
    button.type = "button";
    button.dataset.action = action.id;
    button.setAttribute("aria-describedby", status.id);
    button.tabIndex = index === rovingIndex ? 0 : -1;
    grids[groupOfAction.get(action.id)].append(button);
    return button;
  });
  // Arrow keys stay INSIDE the board the focus is on, and step by that board's
  // own column count. One roving index across a grid of 4 and a grid of 2 walks a
  // geometry neither board has.
  const ring = descriptor.actions.map((_, index) => index);
  const ringOf = groups.map((group, groupIndex) => ring.filter((index) => groupOfAction.get(descriptor.actions[index].id) === groupIndex));

  function listen(target, event, callback) {
    target.addEventListener(event, callback);
    listeners.push(() => target.removeEventListener(event, callback));
  }

  function setRoving(index, focus = false) {
    rovingIndex = index;
    buttons.forEach((button, buttonIndex) => { button.tabIndex = buttonIndex === index ? 0 : -1; });
    if (focus) buttons[index]?.focus();
  }

  function moveRoving(index, key) {
    const groupIndex = groupOfAction.get(descriptor.actions[index].id);
    const members = ringOf[groupIndex];
    const columns = groups[groupIndex].columns;
    let local = members.indexOf(index);
    for (let attempts = 0; attempts < members.length; attempts += 1) {
      local = nextRovingIndex(local, key, members.length, columns);
      if (!buttons[members[local]].disabled) return setRoving(members[local], true);
    }
  }

  function render(message) {
    const view = tableRunView(descriptor, run);
    buttons.forEach((button, index) => {
      const presentation = options.presentAction(descriptor.actions[index], view, run, descriptor);
      button.replaceChildren();
      const name = element("span", "poa-minigame__action-name", presentation.label);
      const detail = element("span", "poa-minigame__action-detail", presentation.detail);
      button.append(name, detail);
      button.className = `poa-minigame__action poa-minigame__action--${presentation.state}`;
      // ⚑ THE TABLE DECIDES WHETHER A CONTROL IS LIVE, not the presenter. A
      // presenter may grey a button it wants to discourage, but it may not OFFER
      // one the emitted row refuses — that is the "nine live buttons on a doomed
      // run" defect, and it recurred in Artificer the moment a presenter tried to
      // work out the refusal predicate for itself. Read `verdict`; do not restate
      // it. A missing row is also closed: `submitFiniteTableAction` refuses it.
      const row = tableRowFor(descriptor, run, descriptor.actions[index].id);
      const closed = !row || row.verdict === "refuse" || run.steps.length >= descriptor.actionLimit;
      button.disabled = Boolean(presentation.disabled || closed || run.terminal || pending !== null);
      button.setAttribute("aria-label", presentation.ariaLabel);
      if (presentation.pressed === undefined) button.removeAttribute("aria-pressed");
      else button.setAttribute("aria-pressed", String(presentation.pressed));
    });
    const enabled = buttons.findIndex((button) => !button.disabled);
    if (enabled < 0) buttons.forEach((button) => { button.tabIndex = -1; });
    else if (buttons[rovingIndex].disabled) setRoving(enabled);
    reset.disabled = run.steps.length === 0 && pending === null;
    status.textContent = message ?? options.presentStatus(view, run, descriptor);
    options.afterRender?.(shell, view, run, descriptor);
  }

  function apply(actionId, resolution) {
    run = submitFiniteTableAction(descriptor, run, actionId, resolution);
    pending = null;
    render();
    options.onTranscript?.(canonicalTableTranscript(run), run);
  }

  function submit(actionId) {
    if (pending !== null) return;
    try {
      apply(actionId, null);
    } catch (error) {
      if (error instanceof TableTransitionRefusal) {
        render(options.presentRefusal(error.reason));
        options.onRefusal?.(error.reason, run);
        return;
      }
      if (!(error instanceof TableOracleQuery)) throw error;
      // The emitted row defers to the hidden instance. Ask; never assume.
      const oracle = session.oracle;
      if (typeof oracle === "function") {
        apply(actionId, oracle(tableRunView(descriptor, run), actionId));
        return;
      }
      pending = actionId;
      render(options.presentOracleQuery?.(error) ?? "Waiting for the host to answer this move against the sealed board.");
      options.onOracleQuery?.(error, run);
    }
  }

  function start(message) {
    run = createFiniteTableRun(descriptor, session);
    pending = null;
    setRoving(0);
    render(message);
    return run;
  }

  buttons.forEach((button, index) => {
    listen(button, "click", () => submit(descriptor.actions[index].id));
    listen(button, "focus", () => setRoving(index));
    listen(button, "keydown", (event) => {
      if (!NAVIGATION_KEYS.has(event.key)) return;
      event.preventDefault();
      moveRoving(index, event.key);
    });
  });
  listen(reset, "click", () => {
    start("Drill reset to the authenticated initial state.");
    options.onReset?.(run);
  });

  render();
  return Object.freeze({
    destroy() {
      listeners.splice(0).forEach((remove) => remove());
      root.replaceChildren();
    },
    getRun() { return run; },
    /** The action the table is waiting on an instance answer for, or null. */
    pendingAction() { return pending; },
    /** Deliver the host's answer to a parked oracle row. */
    resolveOracle(resolution) {
      if (pending === null) throw new TypeError("no oracle question is outstanding");
      const actionId = pending;
      pending = null;
      apply(actionId, resolution);
      return run;
    },
    reset() {
      return start("Drill reset to the authenticated initial state.");
    },
  });
}

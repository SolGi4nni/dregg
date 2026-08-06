import {
  TableOracleQuery,
  TableTransitionRefusal,
  canonicalTableTranscript,
  createFiniteTableRun,
  submitFiniteTableAction,
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
    return "PRACTICE — you chose this board yourself and nothing here is scored. " +
      "No competitive reward, economic reward, or settled RunReceipt.";
  }
  return `JUDGED — slot ${run.slot}, commitment ${run.slotCommitment.slice(0, 16)}…. ` +
    "The board was drawn from a curator-held secret and is opened when the slot closes. " +
    "This transcript is still local and unsettled until a PoA node validates it.";
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
  const board = element("div", "poa-minigame__board");
  board.setAttribute("role", options.boardRole ?? "group");
  board.setAttribute("aria-label", options.boardLabel);
  const status = element("p", "poa-minigame__status");
  status.id = `${options.id}-status`;
  status.setAttribute("role", "status");
  status.setAttribute("aria-live", "polite");
  status.setAttribute("aria-atomic", "true");
  const boundary = element("p", "poa-minigame__boundary", boundaryCopy(run));
  shell.append(header, brief, board, status, boundary);
  root.replaceChildren(shell);

  const buttons = descriptor.actions.map((action, index) => {
    const button = element("button", "poa-minigame__action");
    button.type = "button";
    button.dataset.action = action.id;
    button.setAttribute("aria-describedby", status.id);
    button.tabIndex = index === rovingIndex ? 0 : -1;
    board.append(button);
    return button;
  });

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
    let candidate = index;
    for (let attempts = 0; attempts < buttons.length; attempts += 1) {
      candidate = nextRovingIndex(candidate, key, buttons.length, options.columns);
      if (!buttons[candidate].disabled) return setRoving(candidate, true);
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
      button.disabled = Boolean(presentation.disabled || run.terminal || pending !== null);
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

import {
  applyHostRefusal,
  canonicalReplay,
  createJudgedRun,
  createPracticeRun,
  submitJudgedProbe,
  submitPracticeProbe,
} from "./blackbox-runtime.js";

const NAVIGATION_KEYS = new Set(["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Home", "End"]);

export function nextProbeIndex(current, key, count, columns) {
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

function boundaryCopy(run, descriptor) {
  if (run.mode === "practice") {
    return `PRACTICE — this client picked instance ${run.practiceInstance} of ` +
      `${descriptor.oracle.instanceSpace} out of the published oracle and is answering itself. ` +
      "Nothing here is scored, and the real rules refuse probes this rehearsal will allow.";
  }
  return `JUDGED — slot ${run.slot}, commitment ${run.slotCommitment.slice(0, 16)}…. ` +
    "Answers come from the host, which holds the derived seed; the instance is opened when the slot closes. " +
    "This transcript is local and unsettled until a PoA node validates it.";
}

/**
 * Mount Black Box Reconstruction: a slot-by-fragment probe grid over the emitted
 * oracle. The controller renders answers and never derives one.
 *
 * ⚠ It does not grey out probes the real rules would refuse — `settled-slot` and
 * friends are declared as a vocabulary but no emitted row says when they fire,
 * and inventing that predicate here would be authoring the game in JavaScript.
 * In a judged run the host refuses and `onRefusal` reports it. See the runtime's
 * header for what should be re-emitted to close this properly.
 */
export function mountBlackBox(root, descriptor, options = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a mount root is required");
  const session = options.session ?? { mode: "practice", instance: 0 };
  const start = () => (session.mode === "judged"
    ? createJudgedRun(descriptor, session.opening)
    : createPracticeRun(descriptor, session.instance ?? 0));
  let run = start();
  let awaiting = null;
  let cursor = 0;
  const listeners = [];
  const { probes, slotCount, fragmentCount, requiredPerInstance } = descriptor.oracle;

  const shell = element("section", "poa-minigame black-box");
  shell.setAttribute("aria-labelledby", "black-box-title");
  shell.dataset.mode = run.mode;
  const header = element("header", "poa-minigame__header");
  const heading = element("div");
  heading.append(
    element("p", "poa-minigame__eyebrow", `RECONSTRUCTION BAY // ${run.mode === "practice" ? "PRACTICE" : "JUDGED"}`),
    (() => { const title = element("h2", "poa-minigame__title", "Black Box Reconstruction"); title.id = "black-box-title"; return title; })(),
  );
  const reset = element("button", "poa-minigame__reset", "Reset drill");
  reset.type = "button";
  header.append(heading, reset);

  const brief = element(
    "p",
    "poa-minigame__brief",
    `Ask whether a fragment belongs at a position. The sealed unit answers one bit and nothing else. ` +
      `Settle ${requiredPerInstance} positions within ${descriptor.actionLimit} probes.`,
  );
  const board = element("div", "poa-minigame__board black-box__grid");
  board.setAttribute("role", "grid");
  board.setAttribute("aria-label", `${slotCount} positions by ${fragmentCount} fragments`);
  const status = element("p", "poa-minigame__status");
  status.id = "black-box-status";
  status.setAttribute("role", "status");
  status.setAttribute("aria-live", "polite");
  status.setAttribute("aria-atomic", "true");
  const boundary = element("p", "poa-minigame__boundary", boundaryCopy(run, descriptor));
  shell.append(header, brief, board, status, boundary);
  root.replaceChildren(shell);

  const buttons = probes.map((probe, index) => {
    const button = element("button", "poa-minigame__action");
    button.type = "button";
    button.dataset.probe = probe.id;
    button.dataset.slot = String(probe.slot);
    button.dataset.fragment = String(probe.fragment);
    button.setAttribute("aria-describedby", status.id);
    button.tabIndex = index === cursor ? 0 : -1;
    board.append(button);
    return button;
  });

  function listen(target, event, callback) {
    target.addEventListener(event, callback);
    listeners.push(() => target.removeEventListener(event, callback));
  }

  function setCursor(index, focus = false) {
    cursor = index;
    buttons.forEach((button, position) => { button.tabIndex = position === index ? 0 : -1; });
    if (focus) buttons[index]?.focus();
  }

  /** What the transcript already recorded about a probe. Read, never inferred. */
  function answered(probe) {
    return run.probes.filter((entry) => entry.probe === probe.id);
  }

  function render(message) {
    buttons.forEach((button, index) => {
      const probe = probes[index];
      const history = answered(probe);
      const settling = history.some((entry) => entry.settling);
      const excluded = history.some((entry) => entry.classId !== null && !entry.settling);
      const refused = history.find((entry) => entry.refused);
      const state = settling ? "settled" : excluded ? "excluded" : refused ? "refused" : "open";
      button.replaceChildren(
        element("span", "poa-minigame__action-name", `${probe.slot + 1}·${probe.fragment + 1}`),
        element("span", "poa-minigame__action-detail", state === "open" ? "unasked" : state),
      );
      button.className = `poa-minigame__action poa-minigame__action--${state}`;
      button.disabled = Boolean(run.solved || run.exhausted || awaiting !== null);
      button.setAttribute("aria-label", `${probe.label}. ${state === "open" ? "Not yet asked" : state}.`);
      button.setAttribute("aria-pressed", String(state !== "open"));
    });
    if (buttons[cursor]?.disabled) {
      const open = buttons.findIndex((button) => !button.disabled);
      if (open >= 0) setCursor(open);
    }
    reset.disabled = run.probes.length === 0 && awaiting === null;
    status.textContent = message ?? (
      run.solved ? `Reconstructed: ${run.settled} of ${requiredPerInstance} positions settled in ${run.probes.length} probes. Local transcript ready for external verification.`
        : run.exhausted ? `Probe budget spent with ${run.settled} of ${requiredPerInstance} settled. Reset the drill.`
          : `${run.settled} of ${requiredPerInstance} settled. Probe ${run.probes.length} of ${descriptor.actionLimit}.`
    );
    options.afterRender?.(shell, run, descriptor);
  }

  function commit(next) {
    run = next;
    awaiting = null;
    render();
    options.onTranscript?.(canonicalReplay(run), run);
  }

  function ask(probeId) {
    if (awaiting !== null) return;
    if (run.mode === "practice") {
      commit(submitPracticeProbe(descriptor, run, probeId));
      return;
    }
    // Judged: the client has no instance, so it asks and waits. It does not
    // pre-render an outcome, and there is nothing here it could pre-render from.
    awaiting = probeId;
    render("Probe sent. Waiting for the sealed unit to answer.");
    options.onProbe?.(probeId, run);
  }

  buttons.forEach((button, index) => {
    listen(button, "click", () => ask(probes[index].id));
    listen(button, "focus", () => setCursor(index));
    listen(button, "keydown", (event) => {
      if (!NAVIGATION_KEYS.has(event.key)) return;
      event.preventDefault();
      setCursor(nextProbeIndex(index, event.key, buttons.length, fragmentCount), true);
    });
  });
  listen(reset, "click", () => {
    run = start();
    awaiting = null;
    setCursor(0);
    render("Drill reset. No probe has been asked.");
    options.onReset?.(run);
  });

  render();
  return Object.freeze({
    destroy() {
      listeners.splice(0).forEach((remove) => remove());
      root.replaceChildren();
    },
    getRun() { return run; },
    /** The probe the host has not answered yet, or null. */
    awaitingProbe() { return awaiting; },
    /** Deliver the host's class for the outstanding probe. */
    resolveProbe(classId) {
      if (awaiting === null) throw new TypeError("no probe is outstanding");
      commit(submitJudgedProbe(descriptor, run, awaiting, classId));
      return run;
    },
    /** Deliver a refusal the host returned for the outstanding probe. */
    resolveRefusal(reason) {
      if (awaiting === null) throw new TypeError("no probe is outstanding");
      const next = applyHostRefusal(descriptor, run, awaiting, reason);
      awaiting = null;
      run = next;
      render(`The sealed unit refused that probe: ${reason}.`);
      options.onRefusal?.(reason, run);
      return run;
    },
  });
}

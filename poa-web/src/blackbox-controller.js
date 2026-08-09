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
    // ⚠ THE INDEX IS NOT PRINTED. This line used to name the exact instance the
    // client drew — "picked instance 72 of 120" — and the oracle table is
    // PUBLISHED, so row 72 is the answer, on screen, in the game about deducing
    // it. Every other practice boundary on the rack says which board it is
    // playing without saying which one it drew; this one is now the same.
    return `PRACTICE — this client drew one of the ${descriptor.oracle.instanceSpace} ` +
      "published units for itself and is answering its own probes. " +
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
 * ⚠ It does not grey out probes the real rules would refuse for a reason it cannot
 * see — `settled-slot` and `settled-fragment` are declared as a vocabulary but no
 * emitted row says when they fire, and inventing that predicate here would be
 * authoring the game in JavaScript. In a judged run the host refuses and
 * `onRefusal` reports it. See the runtime's header for what should be re-emitted to
 * close this properly.
 *
 * The one exception is `repeated-probe`, and it is an exception on purpose: whether
 * this client already sent a given probe is a fact about its own transcript, not a
 * rule of the game, so declining to send it twice reads no predicate this face is
 * not entitled to. See the `disabled` line in `render`.
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
  /**
   * ⚑ THE BOARD IS A MATRIX AND WAS BEING DRAWN AS A LIST.
   *
   * Every probe is a (position, fragment) cell, and the entire skill of this game
   * is reading a ROW and a COLUMN — one settled cell rules out four others in each
   * direction. `.black-box__grid` had no column rule anywhere, so the 25 probes
   * fell into the default two-wide stack and came out as "1·1, 1·2, 1·3, 1·4,
   * 1·5, 2·1, …": the one structure that makes the game playable, deleted by a
   * missing stylesheet rule. Keyboard navigation stepped by `fragmentCount`, so
   * arrow keys were already walking the grid CSS was not drawing.
   *
   * It is `columns + 1` wide with a header rank and a header file, which is the
   * `columns: 6` its presentation record has claimed all along.
   *
   * ⚠ `role="grid"` is GONE, not fixed. An ARIA grid requires `row` children
   * holding `gridcell`s; this had 25 buttons as direct children, which is a grid
   * with no rows — malformed, and announced as such. Each button's own label
   * already names its position and fragment, so the honest markup is the same
   * `group` every other board on the rack uses.
   */
  const board = element("div", "poa-minigame__board black-box__grid");
  board.dataset.columns = String(fragmentCount + 1);
  board.setAttribute("role", "group");
  board.setAttribute("aria-label", `${slotCount} positions by ${fragmentCount} fragments`);
  const status = element("p", "poa-minigame__status");
  status.id = "black-box-status";
  status.setAttribute("role", "status");
  status.setAttribute("aria-live", "polite");
  status.setAttribute("aria-atomic", "true");
  const boundary = element("p", "poa-minigame__boundary", boundaryCopy(run, descriptor));
  shell.append(header, brief, board, status, boundary);
  root.replaceChildren(shell);

  // The header rank. Purely a reading aid over labels each button already
  // carries, so it is hidden from the accessibility tree rather than repeated
  // into it 25 more times.
  function headerCell(text) {
    const cell = element("span", "black-box__header", text);
    cell.setAttribute("aria-hidden", "true");
    board.append(cell);
  }
  headerCell("");
  // ⚠ 0-based, because the emitted probe labels are: `Ask whether fragment 0 belongs
  // at position 0` is what the descriptor says and what the aria-label reads out. A
  // 1-based grid meant the cell a sighted player called `1·1` was the cell a screen
  // reader called fragment 0 / position 0 — two coordinate systems for one board, so
  // two people at one screen could not name the same square.
  for (let fragment = 0; fragment < fragmentCount; fragment += 1) headerCell(`f${fragment}`);

  const buttons = probes.map((probe, index) => {
    if (probe.fragment === 0) headerCell(`p${probe.slot}`);
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
        element("span", "poa-minigame__action-name", `${probe.slot}·${probe.fragment}`),
        element("span", "poa-minigame__action-detail", state === "open" ? "unasked" : state),
      );
      button.className = `poa-minigame__action poa-minigame__action--${state}`;
      // ⚠ `history.length > 0` is NOT one of the emitted refusal predicates and is not
      // pretending to be. `settled-slot` and `settled-fragment` need a rule this face
      // does not have and must not invent — but "this client already sent this exact
      // probe" is a fact about THIS CLIENT'S OWN TRANSCRIPT, which `answered()` above
      // already reads. Measured before this line existed: an already-`excluded` cell
      // stayed live, and re-pressing it spent a probe and changed nothing, so a
      // rehearsal could burn 12 of its 15 probes re-asking one dead question with no
      // refusal, no message, and no visible difference from an unasked cell.
      // `repeated-probe` is declared in the emitted refusal vocabulary: the real rules
      // reject this, and only the rehearsal was charging for it.
      button.disabled = Boolean(
        run.solved || run.exhausted || awaiting !== null || history.length > 0,
      );
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

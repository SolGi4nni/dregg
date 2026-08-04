const NAVIGATION_KEYS = new Set(["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Home", "End"]);

export function nextFlightRecorderIndex(current, key, count) {
  if (!NAVIGATION_KEYS.has(key) || count < 1) return current;
  if (key === "Home") return 0;
  if (key === "End") return count - 1;
  const delta = key === "ArrowLeft" || key === "ArrowUp" ? -1 : 1;
  return (current + delta + count) % count;
}

export function shortFlightDigest(value, width = 10) {
  if (typeof value !== "string") return "—";
  if (value.length <= width * 2 + 1) return value;
  return `${value.slice(0, width)}…${value.slice(-width)}`;
}

export function flightRecorderShareText(recorder) {
  const head = recorder.status.head;
  return [
    "PATH OF ANGELS // FLIGHT RECORDER",
    `Source: ${recorder.source.kind === "live-api" ? "live public node view" : "demo rehearsal fixture"}`,
    `Authority: ${recorder.status.authorityId}`,
    `Ship head: ${head?.headDigest ?? "not installed"}`,
    `Transitions: ${head?.transitionCount ?? 0}`,
    recorder.windowStart === null ? "Replay window: empty" : `Replay window: ${recorder.windowStart}–${recorder.windowEnd}`,
    "Digest continuity checked. Consensus finality is not asserted by this public view.",
  ].join("\n");
}

function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function pill(text, modifier = "") {
  return element("span", `flight-pill ${modifier}`.trim(), text);
}

function labelledValue(label, value, modifier = "") {
  const wrapper = element("div", `flight-value ${modifier}`.trim());
  wrapper.append(element("dt", "flight-value__label", label), element("dd", "flight-value__data", value));
  return wrapper;
}

function sourceWords(recorder) {
  return recorder.source.kind === "live-api"
    ? { eyebrow: "LIVE PUBLIC NODE VIEW", badge: "LIVE REDACTED API", projection: "node-reported" }
    : { eyebrow: "DEMO FALLBACK // REHEARSAL ONLY", badge: "DEMO · NOT LIVE", projection: "fixture-provided" };
}

/** Render the redacted public chain without ever requesting authority-bearing bytes. */
export function mountFlightRecorder(root, recorder, options = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a flight recorder mount root is required");
  const listeners = [];
  const words = sourceWords(recorder);
  const isDemo = recorder.source.kind === "demo-fixture";
  let selectedIndex = recorder.transitions.length > 0 ? recorder.transitions.length - 1 : -1;

  const shell = element("section", "flight-shell");
  shell.setAttribute("aria-labelledby", "flight-title");
  const headingCopy = element("div", "flight-heading__copy");
  headingCopy.append(
    element("p", "flight-eyebrow", words.eyebrow),
    element("h1", "flight-title", "Every transmission leaves a wake"),
    element("p", "flight-intro", "The Khovokhi does not remember in stories first. It remembers in linked states: one head yielding to the next, each receipt pointing back through the dark."),
  );
  headingCopy.children[1].id = "flight-title";
  const boundary = element("aside", `flight-boundary${isDemo ? " flight-boundary--demo" : ""}`);
  boundary.setAttribute("aria-label", isDemo ? "demo fallback boundary" : "public view boundary");
  boundary.append(
    pill(words.badge, isDemo ? "flight-pill--demo" : "flight-pill--live"),
    element("p", "", isDemo
      ? `${recorder.source.label} is a bundled rehearsal fixture. It is not connected to a node, does not describe the live ship, and proves nothing about finality.`
      : "This is the node’s public, redacted durable history. Digest continuity is checked here; this view is not itself a quorum-finality certificate."),
  );
  const heading = element("header", "flight-heading");
  heading.append(headingCopy, boundary);

  const liveStatus = element("p", "flight-live");
  liveStatus.id = "flight-live-status";
  liveStatus.setAttribute("role", "status");
  liveStatus.setAttribute("aria-live", "polite");
  liveStatus.setAttribute("aria-atomic", "true");

  const toolbar = element("div", "flight-toolbar");
  toolbar.setAttribute("aria-label", "flight recorder controls");
  const replayButton = element("button", "flight-button flight-button--signal", "Replay digest wake");
  const copyButton = element("button", "flight-button", "Copy share summary");
  const refreshButton = element("button", "flight-button", "Refresh recorder");
  for (const button of [replayButton, copyButton, refreshButton]) button.type = "button";
  replayButton.disabled = recorder.transitions.length === 0;
  refreshButton.disabled = typeof options.onRefresh !== "function";
  toolbar.append(replayButton, copyButton, refreshButton);

  const headPanel = element("section", "flight-head");
  headPanel.setAttribute("aria-labelledby", "flight-head-title");
  const headHalo = element("div", "flight-head__halo");
  headHalo.setAttribute("aria-hidden", "true");
  headHalo.append(element("span"), element("span"), element("span"));
  const headCopy = element("div", "flight-head__copy");
  headCopy.append(element("p", "flight-panel__eyebrow", "CURRENT SHIP HEAD"));
  const headTitle = element("h2", "flight-head__title", recorder.status.installed ? shortFlightDigest(recorder.status.head.headDigest, 12) : "Signal authority dormant");
  headTitle.id = "flight-head-title";
  const headDescription = element("p", "flight-head__description", recorder.status.installed
    ? `The last visible successor resolves to this exact ${words.projection} head.`
    : "This authority is configured on the node but its Signal head has not been installed.");
  const headValues = element("dl", "flight-head__values");
  const head = recorder.status.head;
  headValues.append(
    labelledValue("Transmissions", String(head?.transitionCount ?? 0)),
    labelledValue("World sequence", String(head?.worldSequence ?? 0)),
    labelledValue("Archive revision", String(head?.canonRevision ?? 0)),
    labelledValue("Deployment", head ? shortFlightDigest(head.deploymentDigest, 8) : "—"),
  );
  headCopy.append(headTitle, headDescription, headValues);
  headPanel.append(headHalo, headCopy);

  const timelinePanel = element("section", "flight-panel flight-timeline-panel");
  timelinePanel.setAttribute("aria-labelledby", "flight-timeline-title");
  timelinePanel.append(element("p", "flight-panel__eyebrow", "PREDECESSOR → SUCCESSOR"));
  const timelineTitle = element("h2", "flight-panel__title", "Transmission wake");
  timelineTitle.id = "flight-timeline-title";
  const timelineNote = element("p", "flight-panel__copy", recorder.transitions.length === 0
    ? "No durable transitions are exposed at this head."
    : recorder.hasFullHistory
      ? `Showing the complete visible history: ${recorder.transitions.length} transmission${recorder.transitions.length === 1 ? "" : "s"}.`
      : `Showing the latest ${recorder.transitions.length} of ${head.transitionCount} transmissions. Earlier links remain outside this browser window.`);
  const timeline = element("ol", "flight-timeline");
  const eventButtons = recorder.transitions.map((transition, index) => {
    const item = element("li", "flight-event");
    if (transition.isObservedHeadTransition) item.setAttribute("aria-current", "step");
    const button = element("button", "flight-event__button");
    button.type = "button";
    button.dataset.sequence = String(transition.sequence);
    button.tabIndex = index === selectedIndex ? 0 : -1;
    button.setAttribute("aria-controls", "flight-event-detail");
    const marker = element("span", "flight-event__marker", String(transition.sequence).padStart(2, "0"));
    marker.setAttribute("aria-hidden", "true");
    const copy = element("span", "flight-event__copy");
    copy.append(
      element("b", "", `Transmission ${transition.sequence}`),
      element("span", "", `commit ${transition.commitOrdinal} · ${shortFlightDigest(transition.transitionDigest, 6)}`),
    );
    const link = element("span", "flight-event__link");
    link.append(
      element("code", "", shortFlightDigest(transition.predecessorHeadDigest, 5)),
      element("span", "flight-event__arrow", "→"),
      element("code", "", shortFlightDigest(transition.successorHeadDigest, 5)),
    );
    button.append(marker, copy, link);
    button.setAttribute("aria-label", `Transmission ${transition.sequence}, commit ${transition.commitOrdinal}. Predecessor ${transition.predecessorHeadDigest}, successor ${transition.successorHeadDigest}.`);
    item.append(button);
    timeline.append(item);
    return button;
  });
  if (eventButtons.length === 0) timeline.append(element("li", "flight-empty", "The recorder is quiet."));
  timelinePanel.append(timelineTitle, timelineNote, timeline);

  const detailPanel = element("section", "flight-panel flight-detail");
  detailPanel.id = "flight-event-detail";
  detailPanel.setAttribute("aria-labelledby", "flight-detail-title");
  detailPanel.append(element("p", "flight-panel__eyebrow", "SELECTED CROSS-REFERENCES"));
  const detailTitle = element("h2", "flight-panel__title", "No transmission selected");
  detailTitle.id = "flight-detail-title";
  const detailValues = element("dl", "flight-detail__values");
  const detailBoundary = element("p", "flight-detail__boundary", "Only public digests and commit coordinates are shown. Canon, configuration, and judge input/output bytes never enter this surface.");
  detailPanel.append(detailTitle, detailValues, detailBoundary);

  const verifyPanel = element("section", "flight-panel flight-verify");
  verifyPanel.setAttribute("aria-labelledby", "flight-verify-title");
  verifyPanel.append(element("p", "flight-panel__eyebrow", "WHAT REPLAY MEANS HERE"));
  const verifyTitle = element("h2", "flight-panel__title", "Follow the wake, don’t invent the voyage");
  verifyTitle.id = "flight-verify-title";
  const verifySteps = element("ol", "flight-verify__steps");
  [
    "Accept only the exact redacted status and transition response shapes.",
    "Require one authority, a contiguous sequence, and increasing commit coordinates.",
    "Feed every successor digest into the next transition’s predecessor slot.",
    "Require the final successor and transition digest to equal the current head’s pointers.",
  ].forEach((copy, index) => {
    const item = element("li", "flight-verify__step");
    item.append(element("span", "flight-verify__number", String(index + 1)), element("p", "", copy));
    verifySteps.append(item);
  });
  const finality = element("aside", "flight-finality");
  finality.append(
    pill("NO FINALITY CERTIFICATE IN THIS VIEW", "flight-pill--warning"),
    element("p", "", "A coherent durable chain is not the same thing as a quorum proof. The API explicitly reports “not asserted by this view,” and the recorder preserves that weaker claim."),
  );
  verifyPanel.append(verifyTitle, verifySteps, finality);

  const layout = element("div", "flight-layout");
  layout.append(timelinePanel, detailPanel, verifyPanel);
  shell.append(heading, toolbar, liveStatus, headPanel, layout);
  root.replaceChildren(shell);

  function listen(target, event, callback) {
    target.addEventListener(event, callback);
    listeners.push(() => target.removeEventListener(event, callback));
  }

  function select(index, focus = false) {
    if (index < 0 || index >= recorder.transitions.length) return;
    selectedIndex = index;
    const transition = recorder.transitions[index];
    eventButtons.forEach((button, buttonIndex) => {
      button.tabIndex = buttonIndex === index ? 0 : -1;
      if (buttonIndex === index) button.setAttribute("data-selected", "true");
      else button.removeAttribute("data-selected");
    });
    if (focus) eventButtons[index].focus();
    detailTitle.textContent = `Transmission ${transition.sequence} · commit ${transition.commitOrdinal}`;
    detailValues.replaceChildren(
      labelledValue("Transition", shortFlightDigest(transition.transitionDigest, 10), "flight-value--wide"),
      labelledValue("Turn", shortFlightDigest(transition.turnHash, 8)),
      labelledValue("Receipt", shortFlightDigest(transition.receiptHash, 8)),
      labelledValue("Predecessor", shortFlightDigest(transition.predecessorHeadDigest, 8)),
      labelledValue("Successor", shortFlightDigest(transition.successorHeadDigest, 8)),
    );
  }

  eventButtons.forEach((button, index) => {
    listen(button, "click", () => {
      select(index);
      liveStatus.textContent = `Opened public cross-references for transmission ${recorder.transitions[index].sequence}.`;
    });
    listen(button, "focus", () => { selectedIndex = index; });
    listen(button, "keydown", (event) => {
      const next = nextFlightRecorderIndex(selectedIndex, event.key, eventButtons.length);
      if (next === selectedIndex && !NAVIGATION_KEYS.has(event.key)) return;
      event.preventDefault();
      select(next, true);
    });
  });

  function replay() {
    timeline.setAttribute("data-replay", "active");
    eventButtons.forEach((button) => button.setAttribute("data-link", "checked"));
    liveStatus.textContent = `Replayed ${recorder.transitions.length} contiguous public digest link${recorder.transitions.length === 1 ? "" : "s"}; the final successor resolves to the displayed head.`;
  }
  listen(replayButton, "click", replay);
  listen(copyButton, "click", async () => {
    try {
      await globalThis.navigator?.clipboard?.writeText(flightRecorderShareText(recorder));
      liveStatus.textContent = "Copied a redacted flight-recorder summary.";
    } catch {
      liveStatus.textContent = "Summary copy was unavailable. No recorder state changed.";
    }
  });
  listen(refreshButton, "click", () => options.onRefresh?.());

  if (selectedIndex >= 0) select(selectedIndex);
  liveStatus.textContent = isDemo
    ? "Demo fallback loaded. This rehearsal is visibly separate from the live ship."
    : `Loaded and linked the latest ${recorder.transitions.length} public transition${recorder.transitions.length === 1 ? "" : "s"}.`;

  return Object.freeze({
    select,
    replay,
    shareText() { return flightRecorderShareText(recorder); },
    selectedTransition() { return selectedIndex < 0 ? null : recorder.transitions[selectedIndex]; },
    destroy() { listeners.splice(0).forEach((dispose) => dispose()); root.replaceChildren(); },
  });
}

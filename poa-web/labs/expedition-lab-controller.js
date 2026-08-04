import {
  ExpeditionArtifactRefusal,
  ExpeditionTransitionRefusal,
  availableExpeditionActions,
  canonicalExpeditionTranscript,
  createExpeditionRun,
  currentExpeditionState,
  replayExpeditionActions,
  replayExpeditionRoute,
  rewindExpeditionRun,
  submitExpeditionAction,
  traceExpeditionRun,
} from "./expedition-lab-runtime.js";

const NAVIGATION_KEYS = new Set(["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Home", "End"]);

export function nextExpeditionActionIndex(current, key, count) {
  if (!NAVIGATION_KEYS.has(key) || count < 1) return current;
  if (key === "Home") return 0;
  if (key === "End") return count - 1;
  const delta = key === "ArrowLeft" || key === "ArrowUp" ? -1 : 1;
  return (current + delta + count) % count;
}

export function humanizeExpeditionId(value) {
  return String(value).replaceAll("-", " ").replace(/\b\w/g, (letter) => letter.toUpperCase());
}

function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function labelledValue(label, value, className = "") {
  const wrapper = element("div", `expedition-value ${className}`.trim());
  wrapper.append(element("dt", "expedition-value__label", label), element("dd", "expedition-value__data", value));
  return wrapper;
}

function pill(text, modifier = "") {
  return element("span", `expedition-pill ${modifier}`.trim(), text);
}

function emptyState(text) {
  return element("p", "expedition-empty", text);
}

function setChildren(root, values, render, emptyText) {
  root.replaceChildren();
  if (values?.length) root.append(...values.map(render));
  else root.append(emptyState(emptyText));
}

function describeEdge(run, projectionWord) {
  if (run.lastEffect === "extracted") return `Extraction edge accepted; a ${projectionWord} extraction receipt closed the run.`;
  if (run.lastEffect === "withdrawn") return "Withdrawal edge accepted; the run closed without an extraction receipt.";
  if (run.lastEffect === "advanced") return `The ${projectionWord} table accepted the last action and advanced to its named state.`;
  return "No expedition edge has been dispatched yet.";
}

function custodyLabel(value) {
  const [kind, detail] = String(value).split(":", 2);
  if (!detail) return humanizeExpeditionId(kind);
  return `${humanizeExpeditionId(kind)} · ${detail}`;
}

/**
 * Render the demonstrator as a playable lab. All state changes are dispatched
 * through exact rows from the validated descriptor; this controller owns only
 * presentation, focus, transcript affordances, and local copy/export.
 */
export function mountExpeditionLab(root, descriptor, options = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("an expedition lab mount root is required");
  let run = createExpeditionRun(descriptor);
  let rovingIndex = 0;
  const listeners = [];
  const builtIn = descriptor.source.trust === "builtin-provenance-verified";
  const projectionWord = builtIn ? "emitted" : "table-provided";

  const shell = element("section", "expedition-shell");
  shell.setAttribute("aria-labelledby", "expedition-lab-title");

  const titleBlock = element("div", "expedition-heading__copy");
  titleBlock.append(
    element("p", "expedition-eyebrow", builtIn
      ? "DECK EXPEDITION // PINNED LEAN TABLE"
      : "DECK EXPEDITION // UNTRUSTED TABLE INSTRUMENT"),
    element("h1", "expedition-title", "The ship below the ship"),
    element(
      "p",
      "expedition-deck-copy",
      builtIn
        ? "Take a four-officer team through a nine-room demonstrator. Safe survey, rapid containment, salvage, treatment, extraction, and withdrawal compete across exact emitted rows."
        : "Explore a nine-room instrument supplied by an untrusted table. Its rows are usable for design play, but make no claim to authority.",
    ),
  );
  titleBlock.children[1].id = "expedition-lab-title";

  const boundary = element("aside", "expedition-boundary");
  boundary.setAttribute("aria-label", "demonstrator boundary");
  boundary.append(
    pill(builtIn ? "β NON-CANON" : "UNTRUSTED INSTRUMENT", "expedition-pill--warning"),
    element("p", "", `${builtIn ? "This pinned fixture is" : "This source has not been admitted as authority; it is only"} a fiction-neutral design instrument. Candidate observations remain provisional. No result here promotes canon, mints an asset, settles a reward, or changes the show.`),
  );
  const heading = element("header", "expedition-heading");
  heading.append(titleBlock, boundary);

  const sourceStatus = element("div", "expedition-source");
  const sourceTrust = builtIn ? "PROVENANCE + OUTPUT PINNED" : "UNTRUSTED INSTRUMENT";
  sourceStatus.append(
    pill(sourceTrust, builtIn ? "expedition-pill--ok" : "expedition-pill--warning"),
    element("code", "expedition-source__hash", descriptor.source.artifactSha256 ? `sha256:${descriptor.source.artifactSha256}` : "no artifact digest"),
    element("span", "expedition-source__url", descriptor.source.url ?? "in-memory descriptor"),
  );

  const toolbar = element("div", "expedition-toolbar");
  toolbar.setAttribute("aria-label", "run controls");
  const resetButton = element("button", "expedition-button expedition-button--quiet", "Restart run");
  const rewindButton = element("button", "expedition-button expedition-button--quiet", "Rewind one row");
  const replayButton = element("button", "expedition-button expedition-button--quiet", "Replay transcript");
  const copyButton = element("button", "expedition-button expedition-button--quiet", "Copy local transcript");
  for (const button of [resetButton, rewindButton, replayButton, copyButton]) button.type = "button";
  toolbar.append(resetButton, rewindButton, replayButton, copyButton);

  const liveStatus = element("p", "expedition-live");
  liveStatus.id = "expedition-live-status";
  liveStatus.setAttribute("role", "status");
  liveStatus.setAttribute("aria-live", "polite");
  liveStatus.setAttribute("aria-atomic", "true");

  const runPanel = element("aside", "expedition-panel expedition-run-panel");
  runPanel.append(element("p", "expedition-panel__eyebrow", "RUN PRESSURE"), element("h2", "expedition-panel__title", "Field clock"));
  const pressure = element("dl", "expedition-pressure");
  const turnValue = labelledValue("Turns", "0 / 0");
  const supplyValue = labelledValue("Supplies spent", "0 / 0");
  const phaseValue = labelledValue("Phase", "—");
  const statusValue = labelledValue("Run state", "—");
  pressure.append(turnValue, supplyValue, phaseValue, statusValue);
  const turnProgress = element("progress", "expedition-progress");
  turnProgress.setAttribute("aria-label", "turns used");
  const supplyProgress = element("progress", "expedition-progress expedition-progress--supply");
  supplyProgress.setAttribute("aria-label", "operational supplies spent");
  const routePickerTitle = element("h3", "expedition-subtitle", builtIn
    ? "Pinned Lean-emitted reference routes"
    : "Untrusted table-provided routes");
  const routePicker = element("div", "expedition-route-picker");
  const routeButtons = descriptor.referenceRoutes.map((route) => {
    const button = element("button", "expedition-route-button", `Replay ${humanizeExpeditionId(route.id)}`);
    button.type = "button";
    button.dataset.route = route.id;
    routePicker.append(button);
    return button;
  });
  runPanel.append(pressure, turnProgress, supplyProgress, routePickerTitle, routePicker);

  const chamber = element("section", "expedition-panel expedition-chamber");
  chamber.setAttribute("aria-labelledby", "expedition-room-title");
  const chamberHeading = element("div", "expedition-chamber__heading");
  const chamberCopy = element("div");
  chamberCopy.append(element("p", "expedition-panel__eyebrow", "CURRENT PROJECTION"));
  const roomTitle = element("h2", "expedition-room-title", "Deck room —");
  roomTitle.id = "expedition-room-title";
  chamberCopy.append(roomTitle);
  const edgePill = pill("NO EDGE", "expedition-pill--muted");
  chamberHeading.append(chamberCopy, edgePill);
  const roomGlyph = element("div", "expedition-room-glyph");
  roomGlyph.setAttribute("aria-hidden", "true");
  roomGlyph.append(element("span"), element("span"), element("span"));
  const roomReadout = element("p", "expedition-room-readout");
  const visitedTitle = element("h3", "expedition-subtitle", `Rooms in ${projectionWord} visited set`);
  const visitedRooms = element("ol", "expedition-visited");
  chamber.append(chamberHeading, roomGlyph, roomReadout, visitedTitle, visitedRooms);

  const findings = element("section", "expedition-findings");
  const candidatePanel = element("article", "expedition-panel expedition-finding");
  candidatePanel.append(
    element("p", "expedition-panel__eyebrow", "PROVISIONAL OBSERVATIONS"),
    element("h2", "expedition-panel__title", "β candidates"),
  );
  const candidateList = element("ul", "expedition-list");
  candidatePanel.append(candidateList);
  const salvagePanel = element("article", "expedition-panel expedition-finding");
  salvagePanel.append(
    element("p", "expedition-panel__eyebrow", "IDENTITY-PRESERVING CUSTODY"),
    element("h2", "expedition-panel__title", "Salvage chain"),
  );
  const salvageList = element("ul", "expedition-list");
  salvagePanel.append(salvageList);
  findings.append(candidatePanel, salvagePanel);

  const officerPanel = element("section", "expedition-panel expedition-officers");
  officerPanel.append(
    element("p", "expedition-panel__eyebrow", "FOUR-OFFICER PARTY"),
    element("h2", "expedition-panel__title", "Readiness & injury"),
  );
  const officerGrid = element("div", "expedition-officer-grid");
  officerPanel.append(officerGrid);

  const actionPanel = element("section", "expedition-panel expedition-actions-panel");
  actionPanel.setAttribute("aria-labelledby", "expedition-actions-title");
  actionPanel.append(element("p", "expedition-panel__eyebrow", "EXACT STATE × ACTION ROWS"));
  const actionTitle = element("h2", "expedition-panel__title", "Issue field order");
  actionTitle.id = "expedition-actions-title";
  actionPanel.append(
    actionTitle,
    element("p", "expedition-actions-help", builtIn
      ? "Every order remains visible. Accepted rows advance; refused rows keep their explicit emitted reason. Arrow keys move through orders."
      : "Every order remains visible. Accepted rows advance; refused rows show the untrusted table-provided reason. The table itself has no authority. Arrow keys move through orders."),
  );
  const actionGrid = element("div", "expedition-action-grid");
  actionGrid.setAttribute("role", "group");
  actionGrid.setAttribute("aria-label", "expedition action rows");
  const actionButtons = descriptor.actions.map((action, index) => {
    const button = element("button", "expedition-action");
    button.type = "button";
    button.dataset.action = action.id;
    button.tabIndex = index === 0 ? 0 : -1;
    button.setAttribute("aria-describedby", liveStatus.id);
    actionGrid.append(button);
    return button;
  });
  actionPanel.append(actionGrid);

  const transcriptPanel = element("section", "expedition-panel expedition-transcript");
  transcriptPanel.append(
    element("p", "expedition-panel__eyebrow", "LOCAL ROUTE / REPLAY"),
    element("h2", "expedition-panel__title", "Dispatched rows"),
  );
  const transcriptList = element("ol", "expedition-transcript-list");
  transcriptPanel.append(transcriptList);

  const terminalPanel = element("section", "expedition-panel expedition-terminal");
  terminalPanel.setAttribute("aria-labelledby", "expedition-edge-title");
  terminalPanel.hidden = true;
  const terminalTitle = element("h2", "expedition-panel__title", "Terminal edge");
  terminalTitle.id = "expedition-edge-title";
  const terminalSummary = element("p", "expedition-terminal__summary");
  const receiptGrid = element("dl", "expedition-receipt-grid");
  terminalPanel.append(element("p", "expedition-panel__eyebrow", "EXTRACTION / WITHDRAWAL EFFECT"), terminalTitle, terminalSummary, receiptGrid);

  const mainGrid = element("div", "expedition-layout");
  const center = element("div", "expedition-center");
  center.append(chamber, findings, officerPanel, transcriptPanel, terminalPanel);
  mainGrid.append(runPanel, center, actionPanel);
  shell.append(heading, sourceStatus, toolbar, liveStatus, mainGrid);
  root.replaceChildren(shell);

  function listen(target, event, callback) {
    target.addEventListener(event, callback);
    listeners.push(() => target.removeEventListener(event, callback));
  }

  function setRoving(index, focus = false) {
    rovingIndex = index;
    actionButtons.forEach((button, buttonIndex) => { button.tabIndex = buttonIndex === index ? 0 : -1; });
    if (focus) actionButtons[index]?.focus();
  }

  function renderActions(rows) {
    rows.forEach(({ action, row }, index) => {
      const button = actionButtons[index];
      const accepted = row.verdict === "accept" && !run.terminal;
      button.className = `expedition-action expedition-action--${accepted ? "accept" : "refuse"}`;
      button.disabled = run.terminal;
      const top = element("span", "expedition-action__top");
      top.append(element("span", "expedition-action__label", action.label));
      if (action.role) top.append(pill(`${humanizeExpeditionId(action.role)} role`, "expedition-pill--role"));
      const detail = accepted
        ? `Accepted row · ${humanizeExpeditionId(row.effect)}`
        : `Refused · ${humanizeExpeditionId(row.reason)}`;
      button.replaceChildren(top, element("span", "expedition-action__detail", detail));
      button.setAttribute(
        "aria-label",
        `${action.label}${action.role ? `, ${action.role} role` : ""}. ${detail}.`,
      );
    });
  }

  function renderOfficers(officers) {
    setChildren(officerGrid, officers, (officer) => {
      const card = element("article", `expedition-officer ${officer.available ? "" : "expedition-officer--unavailable"}`.trim());
      const monogram = element("span", "expedition-officer__monogram", officer.role.slice(0, 2).toUpperCase());
      monogram.setAttribute("aria-hidden", "true");
      const copy = element("div", "expedition-officer__copy");
      copy.append(
        element("b", "", humanizeExpeditionId(officer.role)),
        element("span", "", `Officer ${officer.id} · injury ${officer.injury}`),
      );
      card.append(monogram, copy, pill(officer.available ? "AVAILABLE" : "UNAVAILABLE", officer.available ? "expedition-pill--ok" : "expedition-pill--warning"));
      return card;
    }, `No officer projection was ${builtIn ? "emitted" : "provided"}.`);
  }

  function renderTranscript() {
    const trace = traceExpeditionRun(descriptor, run);
    transcriptList.replaceChildren();
    trace.forEach((entry, index) => {
      const item = element("li", "expedition-transcript-row");
      const room = entry.state.view.room === null ? "CLOSED" : `ROOM ${entry.state.view.room}`;
      const marker = element("span", "expedition-transcript-row__marker", String(index).padStart(2, "0"));
      const copy = element("span", "expedition-transcript-row__copy");
      copy.append(
        element("b", "", entry.action?.label ?? "Expedition entry"),
        element("small", "", `${room}${entry.row ? ` · ${humanizeExpeditionId(entry.row.effect)}` : " · initial state"}`),
      );
      item.append(marker, copy);
      transcriptList.append(item);
    });
  }

  function renderTerminal() {
    terminalPanel.hidden = !run.terminal;
    if (!run.terminal) return;
    terminalTitle.textContent = run.lastEffect === "extracted"
      ? (builtIn ? "Extraction receipt emitted" : "Table-provided extraction receipt")
      : "Run withdrawn";
    terminalSummary.textContent = describeEdge(run, projectionWord);
    receiptGrid.replaceChildren();
    if (!run.lastReceipt) {
      receiptGrid.append(labelledValue("Receipt", builtIn ? "None emitted" : "None provided", "expedition-value--wide"));
      return;
    }
    const receipt = run.lastReceipt;
    receiptGrid.append(
      labelledValue("Turns", String(receipt.turns)),
      labelledValue("Supplies spent", String(receipt.suppliesSpent)),
      labelledValue("Final room", String(receipt.finalRoom)),
      labelledValue("Recovered salvage", receipt.recoveredSalvage.join(", ") || "none"),
      labelledValue("Provisional β candidates", receipt.provisionalCandidates.join(", ") || "none", "expedition-value--wide"),
      labelledValue("Relic discoveries", receipt.relicDiscoveries.join(", ") || "none", "expedition-value--wide"),
    );
  }

  function render(message) {
    const state = currentExpeditionState(descriptor, run);
    const view = state.view;
    const rows = availableExpeditionActions(descriptor, run);
    turnValue.children[1].textContent = `${view.turns ?? "—"} / ${view.turnLimit}`;
    supplyValue.children[1].textContent = `${view.suppliesSpent ?? "—"} / ${view.supplyLimit}`;
    phaseValue.children[1].textContent = view.phase === null ? "closed" : String(view.phase);
    statusValue.children[1].textContent = humanizeExpeditionId(view.status);
    turnProgress.max = view.turnLimit;
    turnProgress.value = view.turns ?? view.turnLimit;
    supplyProgress.max = Math.max(1, view.supplyLimit);
    supplyProgress.value = view.suppliesSpent ?? 0;
    roomTitle.textContent = view.room === null ? "Expedition channel closed" : `Deck room ${view.room}`;
    edgePill.textContent = run.lastEffect ? humanizeExpeditionId(run.lastEffect).toUpperCase() : "NO EDGE";
    edgePill.className = `expedition-pill ${run.terminal ? "expedition-pill--warning" : "expedition-pill--muted"}`;
    roomReadout.textContent = describeEdge(run, projectionWord);
    setChildren(visitedRooms, view.visitedRooms, (room) => {
      const item = element("li", "", String(room));
      if (room === view.room) item.setAttribute("aria-current", "location");
      return item;
    }, `No visited rooms were ${builtIn ? "emitted" : "provided"}.`);
    setChildren(candidateList, view.provisionalCandidates ?? [], (candidate) => {
      const item = element("li", "expedition-list__item");
      item.append(pill("β", "expedition-pill--warning"), element("span", "", candidate), element("small", "", "candidate only · not canon"));
      return item;
    }, view.provisionalCandidates === null ? "Run closed; candidates are available only on an extraction receipt." : "No candidate observation surveyed yet.");
    setChildren(salvageList, view.salvage, (record) => {
      const item = element("li", "expedition-list__item");
      item.append(pill(`#${record.id}`, "expedition-pill--muted"), element("span", "", custodyLabel(record.custody)));
      return item;
    }, `No salvage record was ${builtIn ? "emitted" : "provided"}.`);
    renderOfficers(view.officers);
    renderActions(rows);
    if (run.terminal) actionButtons.forEach((button) => { button.tabIndex = -1; });
    else setRoving(Math.min(rovingIndex, actionButtons.length - 1));
    renderTranscript();
    renderTerminal();
    resetButton.disabled = run.actions.length === 0;
    rewindButton.disabled = run.actions.length === 0;
    replayButton.disabled = run.actions.length === 0;
    liveStatus.textContent = message ?? `${view.room === null ? "Expedition closed" : `Room ${view.room}`}. ${view.turns ?? run.actions.length} dispatched rows. ${describeEdge(run, projectionWord)}`;
    options.onTranscript?.(canonicalExpeditionTranscript(descriptor, run), run);
  }

  function submit(actionId) {
    try {
      run = submitExpeditionAction(descriptor, run, actionId);
      render(`${descriptor.actionIndex.get(actionId).label}: ${humanizeExpeditionId(run.lastEffect)} by exact ${projectionWord} row.`);
    } catch (error) {
      const actionLabel = descriptor.actionIndex.get(actionId)?.label ?? String(actionId);
      if (error instanceof ExpeditionTransitionRefusal) {
        render(`${actionLabel} refused: ${humanizeExpeditionId(error.reason)}. State unchanged.`);
        options.onRefusal?.(error.reason, run);
        return;
      }
      if (error instanceof ExpeditionArtifactRefusal) {
        render(`${actionLabel} was not dispatched: ${error.message}. State unchanged.`);
        options.onArtifactRefusal?.(error, run);
        return;
      }
      throw error;
    }
  }

  actionButtons.forEach((button, index) => {
    listen(button, "click", () => submit(descriptor.actions[index].id));
    listen(button, "focus", () => setRoving(index));
    listen(button, "keydown", (event) => {
      if (!NAVIGATION_KEYS.has(event.key)) return;
      event.preventDefault();
      setRoving(nextExpeditionActionIndex(index, event.key, actionButtons.length), true);
    });
  });

  listen(resetButton, "click", () => {
    run = createExpeditionRun(descriptor);
    setRoving(0);
    render(`Run restarted at the ${projectionWord} initial state.`);
  });
  listen(rewindButton, "click", () => {
    run = rewindExpeditionRun(descriptor, run);
    render(`Rewound one dispatched row by replaying the shortened transcript against the ${projectionWord} table.`);
  });
  listen(replayButton, "click", () => {
    const actions = [...run.actions];
    run = replayExpeditionActions(descriptor, actions);
    render(`Replayed ${actions.length} rows from the ${projectionWord} initial state.`);
  });
  listen(copyButton, "click", async () => {
    const transcript = canonicalExpeditionTranscript(descriptor, run);
    try {
      await globalThis.navigator?.clipboard?.writeText(transcript);
      render("Copied an unsettled local demonstrator transcript. It carries no canon or reward claim.");
    } catch {
      render("Clipboard unavailable. The local transcript remains available to the embedding callback.");
    }
  });
  routeButtons.forEach((button, index) => {
    listen(button, "click", () => {
      const route = descriptor.referenceRoutes[index];
      run = replayExpeditionRoute(descriptor, route);
      render(`Replayed ${builtIn ? "pinned Lean-emitted" : "untrusted table-provided"} reference route ${humanizeExpeditionId(route.id)} across ${route.actions.length} exact rows.`);
    });
  });

  render();
  return Object.freeze({
    destroy() {
      listeners.splice(0).forEach((remove) => remove());
      root.replaceChildren();
    },
    getRun() { return run; },
    reset() {
      run = createExpeditionRun(descriptor);
      render(`Run restarted at the ${projectionWord} initial state.`);
      return run;
    },
    dispatch(actionId) {
      submit(actionId);
      return run;
    },
    replayRoute(routeId) {
      try {
        run = replayExpeditionRoute(descriptor, routeId);
        render(`Replayed ${builtIn ? "pinned Lean-emitted" : "untrusted table-provided"} reference route ${humanizeExpeditionId(routeId)}.`);
      } catch (error) {
        if (!(error instanceof ExpeditionArtifactRefusal)) throw error;
        render(`Route was not replayed: ${error.message}. State unchanged.`);
        options.onArtifactRefusal?.(error, run);
      }
      return run;
    },
  });
}

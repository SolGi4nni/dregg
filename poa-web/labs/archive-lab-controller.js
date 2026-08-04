import {
  ArchiveLabArtifactRefusal,
  ArchiveLabTransitionRefusal,
  availableArchiveLabActions,
  canonicalArchiveLabTranscript,
  createArchiveLabRun,
  currentArchiveLabState,
  replayArchiveLabActions,
  replayArchiveLabRoute,
  rewindArchiveLabRun,
  submitArchiveLabAction,
  traceArchiveLabRun,
} from "./archive-lab-runtime.js";

const NAVIGATION_KEYS = new Set(["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Home", "End"]);

export function nextArchiveLabActionIndex(current, key, count) {
  if (!NAVIGATION_KEYS.has(key) || count < 1) return current;
  if (key === "Home") return 0;
  if (key === "End") return count - 1;
  const delta = key === "ArrowLeft" || key === "ArrowUp" ? -1 : 1;
  return (current + delta + count) % count;
}

export function humanizeArchiveId(value) {
  return String(value).replaceAll("-", " ").replaceAll(":", " · ").replace(/\b\w/g, (letter) => letter.toUpperCase());
}

function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function pill(text, modifier = "") {
  return element("span", `archive-pill ${modifier}`.trim(), text);
}

function labelledValue(label, value, modifier = "") {
  const wrapper = element("div", `archive-value ${modifier}`.trim());
  wrapper.append(element("dt", "archive-value__label", label), element("dd", "archive-value__data", value));
  return wrapper;
}

function setChildren(root, values, render, emptyText) {
  root.replaceChildren();
  if (values.length) root.append(...values.map(render));
  else root.append(element("p", "archive-empty", emptyText));
}

function hypothesisById(view, id) {
  return view.hypotheses.find((hypothesis) => hypothesis.id === id);
}

/**
 * Mount a finite evidence instrument. It presents literal fields and dispatches
 * literal rows; all deduction, scores, contradictions, and publication records
 * remain outputs of the loaded table.
 */
export function mountArchiveLab(root, descriptor, options = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("an archive lab mount root is required");
  let run = createArchiveLabRun(descriptor);
  let rovingIndex = 0;
  const listeners = [];
  const builtIn = descriptor.source.trust === "builtin-provenance-verified";
  const projectionWord = builtIn ? "emitted" : "table-provided";

  const shell = element("section", "archive-shell");
  shell.setAttribute("aria-labelledby", "archive-title");
  const headingCopy = element("div", "archive-heading__copy");
  headingCopy.append(
    element("p", "archive-eyebrow", builtIn ? "FIELD ARCHIVE // PINNED LEAN TABLE" : "FIELD ARCHIVE // UNTRUSTED TABLE INSTRUMENT"),
    element("h1", "archive-title", "The signal does not explain itself"),
    element("p", "archive-intro", builtIn
      ? "Eight sealed observations compete for fourteen operations. Screen, test, triangulate, and decide what—if anything—the evidence permits you to publish."
      : "Explore an evidence instrument supplied by an untrusted table. Its fields are useful for design play, but make no authority claim."),
  );
  headingCopy.children[1].id = "archive-title";
  const boundary = element("aside", "archive-boundary");
  boundary.setAttribute("aria-label", "demonstrator boundary");
  boundary.append(
    pill(builtIn ? "β NON-CANON" : "UNTRUSTED INSTRUMENT", "archive-pill--warning"),
    element("p", "", `${builtIn ? "This pinned fixture is" : "This source is"} a beta research instrument. Its findings do not promote canon, mint an asset, settle a reward, or change the show.`),
  );
  const heading = element("header", "archive-heading");
  heading.append(headingCopy, boundary);

  const sourceStatus = element("div", "archive-source");
  sourceStatus.append(
    pill(builtIn ? "PROVENANCE + OUTPUT PINNED" : "UNTRUSTED INSTRUMENT", builtIn ? "archive-pill--ok" : "archive-pill--warning"),
    element("code", "archive-source__hash", descriptor.source.artifactSha256 ? `sha256:${descriptor.source.artifactSha256}` : "no artifact digest"),
    element("span", "archive-source__url", descriptor.source.url ?? "in-memory descriptor"),
  );

  const toolbar = element("div", "archive-toolbar");
  toolbar.setAttribute("aria-label", "research run controls");
  const restartButton = element("button", "archive-button archive-button--quiet", "Restart research");
  const rewindButton = element("button", "archive-button archive-button--quiet", "Rewind one row");
  const replayButton = element("button", "archive-button archive-button--quiet", "Replay transcript");
  const routeButton = element("button", "archive-button archive-button--signal", "Replay unique research plan");
  const copyButton = element("button", "archive-button archive-button--quiet", "Copy local transcript");
  for (const button of [restartButton, rewindButton, replayButton, routeButton, copyButton]) button.type = "button";
  routeButton.dataset.route = "unique-research-plan";
  toolbar.append(restartButton, rewindButton, replayButton, routeButton, copyButton);

  const liveStatus = element("p", "archive-live");
  liveStatus.id = "archive-live";
  liveStatus.setAttribute("role", "status");
  liveStatus.setAttribute("aria-live", "polite");
  liveStatus.setAttribute("aria-atomic", "true");

  const budgetPanel = element("aside", "archive-panel archive-budget");
  budgetPanel.append(element("p", "archive-panel__eyebrow", "FINITE ANALYSIS WINDOW"), element("h2", "archive-panel__title", "Operations ledger"));
  const budgetValues = element("dl", "archive-budget__values");
  const spentValue = labelledValue("Spent", "0");
  const remainingValue = labelledValue("Remaining", "0");
  const informationValue = labelledValue("Information", "0");
  const phaseValue = labelledValue("Station", "—");
  budgetValues.append(spentValue, remainingValue, informationValue, phaseValue);
  const budgetProgress = element("progress", "archive-progress");
  budgetProgress.setAttribute("aria-label", "research operations spent");
  const constraint = element("p", "archive-budget__constraint", "Opening a specimen commits two operations: one screen, then one test. Passing costs nothing, but the seal stays closed.");
  budgetPanel.append(budgetValues, budgetProgress, constraint);

  const specimenPanel = element("section", "archive-panel archive-specimens");
  specimenPanel.setAttribute("aria-labelledby", "archive-specimens-title");
  specimenPanel.append(element("p", "archive-panel__eyebrow", "CUSTODY-PRESERVING TRAY"));
  const specimenTitle = element("h2", "archive-panel__title", "Eight sealed observations");
  specimenTitle.id = "archive-specimens-title";
  const specimenList = element("ol", "archive-specimen-list");
  specimenPanel.append(specimenTitle, specimenList);

  const dossierPanel = element("section", "archive-panel archive-dossier");
  dossierPanel.setAttribute("aria-labelledby", "archive-dossier-title");
  dossierPanel.append(element("p", "archive-panel__eyebrow", "CURRENT SPECIMEN"));
  const dossierTitle = element("h2", "archive-panel__title", "Specimen —");
  dossierTitle.id = "archive-dossier-title";
  const dossierSummary = element("p", "archive-dossier__summary");
  const dossierValues = element("dl", "archive-dossier__values");
  dossierPanel.append(dossierTitle, dossierSummary, dossierValues);

  const hypothesisPanel = element("section", "archive-panel archive-hypotheses");
  hypothesisPanel.setAttribute("aria-labelledby", "archive-hypotheses-title");
  hypothesisPanel.append(element("p", "archive-panel__eyebrow", "LIVE DEDUCTION PROJECTION"));
  const hypothesisTitle = element("h2", "archive-panel__title", "Competing explanations");
  hypothesisTitle.id = "archive-hypotheses-title";
  const hypothesisList = element("div", "archive-hypothesis-list");
  hypothesisPanel.append(hypothesisTitle, hypothesisList);

  const actionPanel = element("section", "archive-panel archive-actions-panel");
  actionPanel.setAttribute("aria-labelledby", "archive-actions-title");
  actionPanel.append(element("p", "archive-panel__eyebrow", "EXACT STATE × MOVE ROWS"));
  const actionTitle = element("h2", "archive-panel__title", "Choose the next procedure");
  actionTitle.id = "archive-actions-title";
  actionPanel.append(
    actionTitle,
    element("p", "archive-actions__help", builtIn
      ? "Every move remains visible. Accepted rows advance; refused rows preserve their explicit emitted reason. Arrow keys move through procedures."
      : "Every move remains visible. Accepted rows advance; refused rows show the table-provided reason. Arrow keys move through procedures."),
  );
  const actionGrid = element("div", "archive-action-grid");
  actionGrid.setAttribute("role", "group");
  actionGrid.setAttribute("aria-label", "archive procedure rows");
  const actionButtons = descriptor.actions.map((action, index) => {
    const button = element("button", "archive-action");
    button.type = "button";
    button.dataset.action = action.id;
    button.tabIndex = index === 0 ? 0 : -1;
    button.setAttribute("aria-describedby", liveStatus.id);
    actionGrid.append(button);
    return button;
  });
  actionPanel.append(actionGrid);

  const transcriptPanel = element("section", "archive-panel archive-transcript");
  transcriptPanel.append(element("p", "archive-panel__eyebrow", "LOCAL ROUTE / REPLAY"), element("h2", "archive-panel__title", "Lab notebook"));
  const transcriptList = element("ol", "archive-transcript-list");
  transcriptPanel.append(transcriptList);

  const publicationPanel = element("section", "archive-panel archive-publication");
  publicationPanel.setAttribute("aria-labelledby", "archive-publication-title");
  publicationPanel.hidden = true;
  publicationPanel.append(element("p", "archive-panel__eyebrow", "BETA RESEARCH RECORD"));
  const publicationTitle = element("h2", "archive-panel__title", "Publication accepted");
  publicationTitle.id = "archive-publication-title";
  const publicationSummary = element("p", "archive-publication__summary");
  const publicationValues = element("dl", "archive-publication__values");
  publicationPanel.append(publicationTitle, publicationSummary, publicationValues);

  const layout = element("div", "archive-layout");
  const center = element("div", "archive-center");
  center.append(dossierPanel, hypothesisPanel, transcriptPanel, publicationPanel);
  layout.append(budgetPanel, specimenPanel, center, actionPanel);
  shell.append(heading, sourceStatus, toolbar, liveStatus, layout);
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

  function renderSpecimens(view) {
    setChildren(specimenList, view.observations, (observation) => {
      const item = element("li", `archive-specimen archive-specimen--${observation.status}`);
      if (observation.id === view.currentObservation) item.setAttribute("aria-current", "location");
      const top = element("div", "archive-specimen__top");
      top.append(element("b", "", `#${observation.id + 1} ${observation.label}`), pill(observation.status.toUpperCase(), observation.status === "tested" ? "archive-pill--ok" : "archive-pill--muted"));
      const bearing = observation.bearing
        ? `${humanizeArchiveId(observation.bearing.kind)} ${hypothesisById(view, observation.bearing.hypothesis)?.label ?? `hypothesis ${observation.bearing.hypothesis}`}`
        : observation.status === "passed" ? "Seal left intact" : "Bearing sealed";
      const detail = observation.verdict
        ? `${bearing} · ${humanizeArchiveId(observation.verdict)} · weight ${observation.weight} · information ${observation.information}`
        : bearing;
      item.append(top, element("span", "archive-specimen__detail", detail));
      return item;
    }, "No specimen projection was provided.");
  }

  function renderDossier(view) {
    const observation = view.observations.find((candidate) => candidate.id === view.currentObservation);
    dossierValues.replaceChildren();
    if (!observation) {
      dossierTitle.textContent = "Analysis bench";
      dossierSummary.textContent = "The tray is exhausted. Triangulate independent observations, then attempt a publication—or discover why the table refuses it.";
      dossierValues.append(
        labelledValue("Tested", String(view.tested.length)),
        labelledValue("Triangulations", String(view.triangulations.length)),
        labelledValue("Contradictions", String(view.contradictions.length), view.contradictions.length ? "archive-value--alert" : ""),
      );
      return;
    }
    dossierTitle.textContent = `#${observation.id + 1} · ${observation.label}`;
    dossierSummary.textContent = observation.status === "pending"
      ? "The seal exposes custody metadata only. Screening reveals the bearing and commits the lab to complete the test."
      : observation.status === "screened"
        ? "Bearing exposed. Complete the test to reveal reliability, weight, and information value."
        : "This specimen is no longer current.";
    const bearing = observation.bearing
      ? `${humanizeArchiveId(observation.bearing.kind)} ${hypothesisById(view, observation.bearing.hypothesis)?.label}`
      : "Sealed";
    dossierValues.append(
      labelledValue("Artifact", String(observation.artifactId)),
      labelledValue("Custody seq.", String(observation.transferSequence)),
      labelledValue("Bearing", bearing),
      labelledValue("Verdict", observation.verdict ? humanizeArchiveId(observation.verdict) : "Sealed"),
      labelledValue("Weight", observation.weight === null ? "Sealed" : String(observation.weight)),
      labelledValue("Information", observation.information === null ? "Sealed" : String(observation.information)),
    );
  }

  function renderHypotheses(view) {
    setChildren(hypothesisList, view.hypotheses, (hypothesis) => {
      const card = element("article", `archive-hypothesis${hypothesis.contradiction ? " archive-hypothesis--contradiction" : ""}${hypothesis.publishable ? " archive-hypothesis--publishable" : ""}`);
      const top = element("div", "archive-hypothesis__top");
      top.append(element("h3", "", hypothesis.label));
      if (hypothesis.contradiction) top.append(pill("CONTRADICTION", "archive-pill--warning"));
      else if (hypothesis.publishable) top.append(pill("PUBLICATION OPEN", "archive-pill--ok"));
      const scores = element("dl", "archive-hypothesis__scores");
      scores.append(labelledValue("Support", String(hypothesis.support)), labelledValue("Refutation", String(hypothesis.refutation)));
      card.append(top, scores);
      return card;
    }, "No hypothesis projection was provided.");
  }

  function renderActions(rows) {
    rows.forEach(({ action, row }, index) => {
      const accepted = row.verdict === "accept" && !run.terminal;
      const button = actionButtons[index];
      button.className = `archive-action archive-action--${accepted ? "accept" : "refuse"}`;
      button.disabled = run.terminal;
      const detail = accepted ? `Accepted row · ${humanizeArchiveId(row.effect)}` : `Refused · ${humanizeArchiveId(row.reason)}`;
      button.replaceChildren(element("span", "archive-action__label", action.label), element("span", "archive-action__detail", detail));
      button.setAttribute("aria-label", `${action.label}. ${detail}.`);
    });
  }

  function renderTranscript() {
    const trace = traceArchiveLabRun(descriptor, run);
    transcriptList.replaceChildren();
    trace.slice(1).forEach((entry, index) => {
      const item = element("li", "archive-transcript-row");
      item.append(element("span", "archive-transcript-row__number", String(index + 1)), element("b", "", entry.action.label), element("span", "", humanizeArchiveId(entry.row.effect)));
      transcriptList.append(item);
    });
    if (trace.length === 1) transcriptList.append(element("li", "archive-empty", "No procedures dispatched yet."));
  }

  function renderPublication(view) {
    publicationPanel.hidden = !run.terminal;
    publicationValues.replaceChildren();
    if (!run.terminal || !run.lastRecord) return;
    const record = run.lastRecord;
    const hypothesis = hypothesisById(view, record.hypothesis);
    publicationTitle.textContent = `${hypothesis?.label ?? `Hypothesis ${record.hypothesis}`} · beta record`;
    publicationSummary.textContent = `${projectionWord[0].toUpperCase()}${projectionWord.slice(1)} publication record accepted. It remains provisional and has no canon or reward authority.`;
    publicationValues.append(
      labelledValue("Support", String(record.support)),
      labelledValue("Refutation", String(record.refutation)),
      labelledValue("Information", String(record.information)),
      labelledValue("Operations", String(record.operationsSpent)),
      labelledValue("Evidence", record.evidence.join(", ")),
      labelledValue("Artifact", record.artifact),
    );
  }

  function render(message = "Ready. Choose a procedure from the exact table rows.") {
    const state = currentArchiveLabState(descriptor, run);
    const view = state.view;
    spentValue.children[1].textContent = `${view.operationsSpent} / ${view.operationBudget}`;
    remainingValue.children[1].textContent = String(view.operationsRemaining);
    informationValue.children[1].textContent = String(view.information);
    phaseValue.children[1].textContent = view.currentObservation === null ? "Analysis" : humanizeArchiveId(view.phase);
    budgetProgress.max = view.operationBudget;
    budgetProgress.value = view.operationsSpent;
    restartButton.disabled = run.actions.length === 0;
    rewindButton.disabled = run.actions.length === 0;
    replayButton.disabled = run.actions.length === 0;
    routeButton.disabled = false;
    renderSpecimens(view);
    renderDossier(view);
    renderHypotheses(view);
    renderActions(availableArchiveLabActions(descriptor, run));
    renderTranscript();
    renderPublication(view);
    liveStatus.textContent = message;
    options.onTranscript?.(canonicalArchiveLabTranscript(descriptor, run));
  }

  function dispatch(actionId) {
    try {
      run = submitArchiveLabAction(descriptor, run, actionId);
      render(`Accepted exact ${projectionWord} row: ${humanizeArchiveId(run.lastEffect)}.`);
      return true;
    } catch (error) {
      if (error instanceof ArchiveLabTransitionRefusal) {
        render(`Procedure refused: ${humanizeArchiveId(error.reason)}. No operation was spent.`);
        return false;
      }
      if (error instanceof ArchiveLabArtifactRefusal) {
        render(`Procedure was not dispatched: ${error.message}`);
        return false;
      }
      throw error;
    }
  }

  function replayRoute(routeId = "unique-research-plan") {
    try {
      run = replayArchiveLabRoute(descriptor, routeId);
      render("Replayed the table-provided unique research plan from the initial state.");
      return true;
    } catch (error) {
      if (error instanceof ArchiveLabArtifactRefusal || error instanceof ArchiveLabTransitionRefusal) {
        render(`Route was not replayed: ${error.message}`);
        return false;
      }
      throw error;
    }
  }

  actionButtons.forEach((button, index) => {
    listen(button, "click", () => dispatch(button.dataset.action));
    listen(button, "focus", () => { rovingIndex = index; });
    listen(button, "keydown", (event) => {
      const next = nextArchiveLabActionIndex(rovingIndex, event.key, actionButtons.length);
      if (next === rovingIndex && !NAVIGATION_KEYS.has(event.key)) return;
      event.preventDefault();
      setRoving(next, true);
    });
  });
  listen(restartButton, "click", () => {
    run = createArchiveLabRun(descriptor);
    render("Research restarted from the sealed tray.");
  });
  listen(rewindButton, "click", () => {
    run = rewindArchiveLabRun(descriptor, run);
    render("Rewound one accepted table row.");
  });
  listen(replayButton, "click", () => {
    run = replayArchiveLabActions(descriptor, [...run.actions]);
    render("Replayed the local notebook from the initial state.");
  });
  listen(routeButton, "click", () => replayRoute(routeButton.dataset.route));
  listen(copyButton, "click", async () => {
    try {
      await globalThis.navigator?.clipboard?.writeText(canonicalArchiveLabTranscript(descriptor, run));
      render("Copied the local beta transcript.");
    } catch {
      render("Transcript copy was unavailable; the local run remains unchanged.");
    }
  });

  render();
  return Object.freeze({
    dispatch,
    replayRoute,
    restart() { run = createArchiveLabRun(descriptor); render("Research restarted from the sealed tray."); },
    rewind() { run = rewindArchiveLabRun(descriptor, run); render("Rewound one accepted table row."); },
    getRun() { return run; },
    transcript() { return canonicalArchiveLabTranscript(descriptor, run); },
    destroy() { listeners.splice(0).forEach((dispose) => dispose()); root.replaceChildren(); },
  });
}

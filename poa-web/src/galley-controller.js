import {
  GalleyApiRefusal,
  createGalleyPendingIntentJournal,
  galleyActionLabel,
  galleyAvailableAtSequence,
  normalizeGalleyActorIdentity,
  projectGalleyWatch,
} from "./galley-runtime.js";

const CHOICE_KEYS = new Set(["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Home", "End"]);

export function nextGalleyChoiceIndex(current, key, count, columns = 2) {
  if (!CHOICE_KEYS.has(key) || count < 1) return current;
  if (key === "Home") return 0;
  if (key === "End") return count - 1;
  const delta = key === "ArrowLeft" ? -1 : key === "ArrowRight" ? 1 : key === "ArrowUp" ? -columns : columns;
  return (current + delta + count * (Math.ceil(Math.abs(delta) / count) + 1)) % count;
}

function el(documentRef, tag, className, text) {
  const node = documentRef.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function button(documentRef, className, text) {
  const node = el(documentRef, "button", className, text);
  node.type = "button";
  return node;
}

function appendFact(documentRef, root, term, detail, code = false) {
  const row = el(documentRef, "div");
  row.append(el(documentRef, "dt", "", term), el(documentRef, code ? "code" : "dd", "", detail));
  root.append(row);
}

function short(value, head = 8, tail = 6) {
  return `${value.slice(0, head)}…${value.slice(-tail)}`;
}

function friendlyError(error) {
  if (error instanceof GalleyApiRefusal) return `${error.code}: ${error.message}`;
  if (error?.name === "DreggUserDeclined" || error?.code === "user-declined") return "The turn was not signed. Nothing changed.";
  return error instanceof Error ? error.message : "The Galley refused the request.";
}

function providerCandidate(provider) {
  return provider && typeof provider.signTurnV3 === "function" ? provider : null;
}

function identityProviderCandidate(provider) {
  return provider && typeof provider.getActiveIdentity === "function" ? provider : null;
}

function identityFailure(error) {
  if (error?.name === "DreggUserDeclined" || error?.code === "user-declined") {
    return "Active-identity sharing was declined. The Galley remains read-only and no watch was requested.";
  }
  if (error instanceof GalleyApiRefusal) return `${error.code}: ${error.message}. No watch was requested.`;
  return "An active Dregg public identity is unavailable. The Galley remains read-only and no watch was requested.";
}

function lifecycleState(state, watch) {
  if (state.lastEvent || watch.participated) return "finalized";
  if (state.pending && state.admission?.state === "submitted") return "pending";
  if (state.pending && state.admission?.state === "queued") return "queued";
  if (state.pending) return "prepared";
  return watch.state;
}

/** Render a player-facing read projection of the exact V1 journal. This code
 * presents node-authored state; it never carries a Galley reducer or judge. */
export function mountGalley(root, {
  transport,
  dreggProvider = globalThis.window?.dregg ?? null,
  pendingJournal = createGalleyPendingIntentJournal(),
  onView = () => {},
} = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("Galley mount root is required");
  if (!transport || typeof transport.openWatch !== "function" || typeof transport.requestCommand !== "function") {
    throw new TypeError("Galley watch transport is required");
  }
  const documentRef = root.ownerDocument ?? globalThis.document;
  if (!documentRef?.createElement) throw new TypeError("DOM document is required");

  const shell = el(documentRef, "section", "galley-terminal");
  shell.setAttribute("aria-labelledby", "galley-scene-title");
  const headerRoot = el(documentRef, "header", "galley-header");
  const live = el(documentRef, "p", "galley-live", "Opening the Galley watch…");
  live.id = "galley-live-status";
  live.tabIndex = -1;
  live.setAttribute("role", "status");
  live.setAttribute("aria-live", "polite");
  live.setAttribute("aria-atomic", "true");
  const body = el(documentRef, "div", "galley-body");
  const watchRoot = el(documentRef, "section", "galley-maintenance");
  const logbookRoot = el(documentRef, "section", "galley-commons");
  const evidenceRoot = el(documentRef, "aside", "galley-side");
  body.append(watchRoot, logbookRoot, evidenceRoot);
  shell.append(headerRoot, live, body);
  root.replaceChildren(shell);

  const state = {
    busy: false,
    destroyed: false,
    pending: null,
    lastEvent: null,
    admission: null,
    view: null,
    actorPublicKeyHex: null,
    controls: [],
  };

  function setBusy(value) {
    state.busy = value;
    shell.setAttribute("aria-busy", String(value));
    for (const control of state.controls) {
      control.disabled = value || control.dataset.available !== "true";
    }
  }

  function announce(message, { focus = false, error = false } = {}) {
    live.textContent = message;
    live.dataset.state = error ? "refused" : "ready";
    if (focus) live.focus?.();
  }

  function renderHeader(view, watch) {
    const copy = el(documentRef, "div", "galley-header__copy");
    copy.append(
      el(documentRef, "p", "eyebrow", "DECK 119 // DAILY WATCH"),
      el(documentRef, "h2", "", !view.replay.audited
        ? "Galley replay unavailable"
        : watch.state === "recorded" ? "Your shift is in the logbook" : "The Galley is open"),
      el(documentRef, "p", "galley-header__description", view.replay.audited
        ? "A small ship-life loop: arrive, take one offered station, sign the exact turn, and return to a replayable record."
        : "This node response did not pass its replay-audit gate, so it cannot populate the player loop."),
    );
    copy.children[1].id = "galley-scene-title";
    const gauges = el(documentRef, "dl", "galley-header__gauges");
    appendFact(documentRef, gauges, "Daily", view.replay.audited ? short(view.dailyId) : "UNAVAILABLE");
    appendFact(documentRef, gauges, "Journal head", view.replay.audited ? String(view.sequence) : "UNAVAILABLE");
    appendFact(documentRef, gauges, "Public shifts", view.replay.audited ? String(watch.publicPlayCount) : "UNAVAILABLE");
    appendFact(documentRef, gauges, "Local service", view.replay.audited ? String(watch.localServiceTotal) : "UNAVAILABLE");
    appendFact(documentRef, gauges, "Replay", view.replay.audited ? "NODE REPORTS COMPLETE" : "REFUSED");
    const boundary = el(documentRef, "p", "galley-mode galley-mode--durable", view.replay.audited
      ? "The shared public key selects this read view and authorizes nothing. The signer chooses the exact prepared turn; an exact matching event in the node-audited journal records the outcome. The postcard SHA-256 shown here is an adjacent checksum, not canonical receipt verification."
      : "Replay audit is refused. Returned event arrays remain inert: this page shows no player records and enables no action from this response.");
    headerRoot.replaceChildren(copy, gauges, boundary);
  }

  function renderIdentityUnavailable() {
    state.view = null;
    state.actorPublicKeyHex = null;
    state.pending = null;
    state.lastEvent = null;
    const copy = el(documentRef, "div", "galley-header__copy");
    copy.append(
      el(documentRef, "p", "eyebrow", "DECK 119 // READ-ONLY"),
      el(documentRef, "h2", "", "The Galley"),
      el(documentRef, "p", "galley-header__description",
        "Share the active Dregg public identity to request its current watch and logbook from the node."),
    );
    copy.children[1].id = "galley-scene-title";
    headerRoot.replaceChildren(copy, el(documentRef, "p", "galley-mode",
      "The identity header is a preparation claim. Only an exact signed turn and its finalized journal event can record a shift."));
    watchRoot.replaceChildren(el(documentRef, "p", "galley-empty",
      "No action, projection, or logbook was requested without identity permission."));
    logbookRoot.replaceChildren();
    const retry = button(documentRef, "galley-provider__connect", "Share active identity and retry");
    retry.dataset.available = "true";
    retry.addEventListener("click", () => { void open(); });
    evidenceRoot.replaceChildren(el(documentRef, "p", "galley-empty",
      "Any pending-intent coordinate remains local and is not reconciled against an unpersonalized response."), retry);
    state.controls = [retry];
  }

  function renderWatchUnavailable(error) {
    state.view = null;
    state.pending = null;
    state.lastEvent = null;
    state.admission = null;
    const copy = el(documentRef, "div", "galley-header__copy");
    copy.append(
      el(documentRef, "p", "eyebrow", "DECK 119 // WATCH UNAVAILABLE"),
      el(documentRef, "h2", "", "The Galley watch could not be read"),
      el(documentRef, "p", "galley-header__description",
        "The node returned no validated watch. No action, projection, or player record is shown."),
    );
    copy.children[1].id = "galley-scene-title";
    headerRoot.replaceChildren(copy);
    watchRoot.replaceChildren(el(documentRef, "p", "galley-empty", `Watch unavailable: ${friendlyError(error)}`));
    logbookRoot.replaceChildren();
    const retry = button(documentRef, "galley-provider__connect", "Retry Galley watch");
    retry.dataset.available = "true";
    retry.addEventListener("click", () => { void open(); });
    evidenceRoot.replaceChildren(el(documentRef, "p", "galley-empty",
      "Retry requests a fresh node response; this page does not reconstruct a missing watch."), retry);
    state.controls = [retry];
  }

  function actionControl(view, action, index, controls) {
    const control = button(documentRef, "galley-action galley-action--maintenance", galleyActionLabel(action.kind));
    const unavailable = Boolean(state.pending) || !providerCandidate(dreggProvider) ||
      !view.replay.audited || !galleyAvailableAtSequence(action.expiresAfterSequence, view.sequence);
    control.dataset.galleyAction = action.actionToken;
    control.dataset.actionKind = action.kind;
    control.dataset.available = String(!unavailable);
    control.disabled = unavailable;
    control.tabIndex = index === 0 ? 0 : -1;
    control.setAttribute("aria-describedby", live.id);
    control.append(
      el(documentRef, "small", "", "Sign one node-authored maintenance turn. No token transfer is requested."),
      el(documentRef, "small", "galley-action__expiry", `offered at journal sequence ${action.expiresAfterSequence}`),
    );
    control.addEventListener("click", () => { void dispatch(action.actionToken); });
    control.addEventListener("keydown", (event) => {
      if (!CHOICE_KEYS.has(event.key)) return;
      event.preventDefault();
      const target = nextGalleyChoiceIndex(index, event.key, controls.length, 2);
      controls.forEach((candidate, candidateIndex) => { candidate.tabIndex = candidateIndex === target ? 0 : -1; });
      controls[target]?.focus?.();
    });
    return control;
  }

  function appendStage(list, number, label, stageState) {
    const item = el(documentRef, "li", `galley-step galley-step--${stageState}`);
    item.append(
      el(documentRef, "span", "galley-step__index", String(number).padStart(2, "0")),
      el(documentRef, "span", "galley-step__label", label),
      el(documentRef, "span", "galley-step__state", stageState),
    );
    list.append(item);
  }

  function renderWatch(view, watch) {
    const heading = el(documentRef, "div", "galley-section-heading");
    const headingCopy = el(documentRef, "div");
    headingCopy.append(el(documentRef, "p", "panel-label", "YOUR DAILY LOOP"), el(documentRef, "h3", "", "Take one watch"));
    heading.append(headingCopy, el(documentRef, "span", "quiet-chip", lifecycleState(state, watch).toUpperCase()));

    const statusCopy = !view.replay.audited
      ? "The node did not return an audited replay. No station or player record is available from this response."
      : ({
      available: "A station is available for this key at the current journal head.",
      recorded: "The journal contains a signed public shift by this key. This daily offers no second shift.",
      waiting: "No station is offered to this key at the current journal head.",
    }[watch.state]);
    const intro = el(documentRef, "p", "galley-instruction", statusCopy);

    const stages = el(documentRef, "ol", "galley-steps");
    stages.setAttribute("aria-label", "Galley watch lifecycle");
    const phase = lifecycleState(state, watch);
    appendStage(stages, 1, "Arrive and read the current watch", "completed");
    appendStage(stages, 2, "Choose the offered maintenance station",
      ["prepared", "queued", "pending", "finalized", "recorded"].includes(phase) ? "completed" : "current");
    appendStage(stages, 3, "Review and sign the exact Dregg turn",
      ["queued", "pending", "finalized", "recorded"].includes(phase) ? "completed" : phase === "prepared" ? "current" : "waiting");
    appendStage(stages, 4, "Find the exact turn in the replayed journal",
      ["finalized", "recorded"].includes(phase) ? "completed" : ["queued", "pending"].includes(phase) ? "current" : "waiting");
    appendStage(stages, 5, "Return after the daily watch rotates",
      ["finalized", "recorded"].includes(phase) ? "current" : "waiting");

    const region = el(documentRef, "div", "galley-maintenance__actions");
    region.setAttribute("role", "group");
    region.setAttribute("aria-label", "Node-authored Galley actions");
    const controls = [];
    watch.availableActions.forEach((action, index) => controls.push(actionControl(view, action, index, controls)));
    if (controls.length === 0) region.append(el(documentRef, "p", "galley-empty", watch.nextVisit));
    else region.append(...controls);
    const next = el(documentRef, "p", "galley-next-visit", watch.nextVisit);
    const refresh = button(documentRef, "galley-provider__connect", "Refresh this watch");
    refresh.dataset.available = "true";
    refresh.addEventListener("click", () => { void open(); });
    state.controls = [...controls, refresh];
    watchRoot.replaceChildren(heading, intro, stages, region, next, refresh);
  }

  function recordRow(record) {
    const row = el(documentRef, "li", `galley-logbook__record${record.isPersonal ? " galley-logbook__record--personal" : ""}`);
    row.append(
      el(documentRef, "span", "galley-logbook__sequence", `#${record.sequence}`),
      el(documentRef, "b", "", record.isPersonal ? "Your signed shift" : "A crew shift"),
      el(documentRef, "span", "", `${record.localService} local service recorded`),
      el(documentRef, "small", "", `turn ${short(record.turnHash)}`),
    );
    return row;
  }

  function renderLogbook(view, watch) {
    const heading = el(documentRef, "div", "galley-section-heading");
    const headingCopy = el(documentRef, "div");
    headingCopy.append(
      el(documentRef, "p", "panel-label", view.replay.audited ? "REPLAYED RECORDS" : "REPLAY REFUSED"),
      el(documentRef, "h3", "", view.replay.audited ? "Your logbook" : "Logbook unavailable"),
    );
    heading.append(headingCopy, el(documentRef, "span", "quiet-chip",
      view.replay.audited ? `${watch.personalRecords.length} YOURS` : "UNAVAILABLE"));

    if (!view.replay.audited) {
      logbookRoot.replaceChildren(heading, el(documentRef, "p", "galley-empty",
        "Logbook unavailable. Returned event arrays remain inert until the node reports an audited replay."));
      return;
    }

    const totals = el(documentRef, "dl", "galley-logbook__totals");
    appendFact(documentRef, totals, "Public shifts", String(watch.publicPlayCount));
    appendFact(documentRef, totals, "Local service", String(watch.localServiceTotal));
    appendFact(documentRef, totals, "Returned records", String(watch.records.length));

    const personalTitle = el(documentRef, "h4", "", "This key");
    const personal = el(documentRef, "ol", "galley-logbook");
    personal.setAttribute("aria-label", "Personal Galley records");
    if (watch.personalRecords.length === 0) personal.append(el(documentRef, "li", "galley-empty", "No signed shift by this key appears in the returned journal."));
    else personal.append(...watch.personalRecords.map(recordRow));

    const allTitle = el(documentRef, "h4", "", "Ship log");
    const all = el(documentRef, "ol", "galley-logbook galley-logbook--all");
    all.setAttribute("aria-label", "Returned Galley event records");
    if (watch.records.length === 0) all.append(el(documentRef, "li", "galley-empty", "The returned journal is empty."));
    else all.append(...watch.records.slice(-12).reverse().map(recordRow));

    const note = el(documentRef, "p", "galley-commons__scene",
      "These records are projected only from exact events returned by the node's replay audit. Page text and local storage cannot add a shift.");
    logbookRoot.replaceChildren(heading, totals, personalTitle, personal, allTitle, all, note);
  }

  function renderEvidence(view) {
    const outcome = el(documentRef, "section", "galley-outcome");
    outcome.append(el(documentRef, "p", "panel-label", "CURRENT OUTCOME"));
    const outcomeTitle = el(documentRef, "h3", "", !view.replay.audited
      ? "Replay refused"
      : state.lastEvent ? "Shift observed" : state.pending ? "Shift not final yet" : "Watch read");
    outcomeTitle.id = "galley-outcome-title";
    outcome.setAttribute("aria-labelledby", outcomeTitle.id);
    outcome.append(outcomeTitle);

    if (state.admission) {
      const labels = {
        submitted: "SUBMITTED / AWAITING JOURNAL",
        queued: "SIGNED / QUEUED",
        refused: "REFUSED / NOT SUBMITTED",
        declined: "DECLINED / NOT SUBMITTED",
        error: "SIGNING RESULT UNKNOWN",
      };
      const admission = el(documentRef, "div", `galley-admission galley-admission--${state.admission.state}`);
      admission.append(el(documentRef, "p", "panel-label", labels[state.admission.state] ?? "UNKNOWN ADMISSION"));
      if (state.admission.turnHash) admission.append(el(documentRef, "code", "", state.admission.turnHash));
      if (state.admission.error) admission.append(el(documentRef, "small", "galley-admission__error", state.admission.error));
      outcome.append(admission);
    } else {
      outcome.append(el(documentRef, "p", "", "No turn is currently being submitted from this page."));
    }

    if (state.lastEvent) {
      const receipt = el(documentRef, "div", "galley-receipt");
      receipt.append(el(documentRef, "p", "panel-label", "EXACT EVENT + ADJACENT CHECKSUM"),
        el(documentRef, "h4", "", `Journal event ${state.lastEvent.sequence}`));
      const facts = el(documentRef, "dl");
      appendFact(documentRef, facts, "Turn", state.lastEvent.turnHash, true);
      appendFact(documentRef, facts, "Receipt", state.lastEvent.receiptHash, true);
      appendFact(documentRef, facts, "Postcard SHA", state.lastEvent.receipt.sha256, true);
      receipt.append(facts, el(documentRef, "small", "",
        "The checksum matches the returned postcard bytes. Canonical Dregg receipt verification is not installed in this page."));
      outcome.append(receipt);
    }
    if (state.pending) {
      const check = button(documentRef, "galley-evidence__check", "Check exact turn again");
      check.dataset.available = String(Boolean(state.pending.finalTurnHash));
      check.disabled = !state.pending.finalTurnHash;
      check.addEventListener("click", () => { void checkPending(); });
      state.controls.push(check);
      outcome.append(el(documentRef, "code", "galley-preparation-digest", state.pending.preparationDigest));
      if (!state.pending.finalTurnHash) outcome.append(el(documentRef, "p", "galley-empty",
        "The preparation digest is durable, but the signer did not return a final turn hash. This page cannot invent a journal coordinate."));
      outcome.append(check);
    }

    const details = el(documentRef, "details", "galley-technical");
    const summary = el(documentRef, "summary", "", "Technical evidence");
    const boundary = el(documentRef, "p", "", view.replay.audited
      ? "The node reports a complete Lean-replayed journal. This browser checks envelope shape, exact turn-hash reconciliation, and postcard SHA-256; it does not independently verify quorum finality or the canonical receipt."
      : "Replay audit is refused. Event arrays are retained only as inert response evidence and cannot populate the player logbook or finalize a turn here.");
    const facts = el(documentRef, "dl", "galley-evidence__facts");
    appendFact(documentRef, facts, "Federation", view.federationId, true);
    appendFact(documentRef, facts, "Aggregate", view.aggregateId, true);
    appendFact(documentRef, facts, "Semantic head", view.semanticHead, true);
    appendFact(documentRef, facts, "Projection", view.projectionDigest, true);
    appendFact(documentRef, facts, "Replay window", `${view.replay.fromSequence}–${view.replay.throughSequence}`);
    const publicPlayProjection = {
      sequence: view.projection.sequence,
      publicPlayers: view.projection.publicPlayers,
      publicPlayCount: view.projection.publicPlayCount,
      localServiceTotal: view.projection.localServiceTotal,
      powerRoot: view.projection.powerRoot,
      lootRoot: view.projection.lootRoot,
      canonRoot: view.projection.canonRoot,
      canonRevision: view.projection.canonRevision,
    };
    const projection = el(documentRef, "pre", "galley-projection", JSON.stringify(publicPlayProjection, null, 2));
    projection.tabIndex = 0;
    projection.setAttribute("aria-label", "Schema-validated Galley response fields; replay authority shown separately");
    details.append(summary, boundary, facts, projection);
    evidenceRoot.replaceChildren(outcome, details);
  }

  function render(view) {
    if (state.destroyed) return;
    state.view = view;
    const watch = projectGalleyWatch(view, state.actorPublicKeyHex);
    renderHeader(view, watch);
    renderWatch(view, watch);
    renderLogbook(view, watch);
    renderEvidence(view);
    onView(view);
    setBusy(state.busy);
  }

  async function open() {
    if (state.destroyed || state.busy) return null;
    setBusy(true);
    announce("Requesting the active public Dregg identity before reading this watch…");
    try {
      const provider = identityProviderCandidate(dreggProvider);
      if (!provider) throw new GalleyApiRefusal("galley-actor", "active identity permission is unavailable");
      const identity = normalizeGalleyActorIdentity(await provider.getActiveIdentity());
      state.actorPublicKeyHex = identity.publicKeyHex;
    } catch (error) {
      renderIdentityUnavailable();
      announce(identityFailure(error), { error: true });
      setBusy(false);
      return null;
    }
    announce("Reading the current replayed Galley watch and its returned records…");
    try {
      const view = await transport.openWatch(state.actorPublicKeyHex);
      const recoverable = pendingJournal.forView(view);
      state.pending = recoverable.at(-1) ?? null;
      if (state.lastEvent && (!view.replay.audited ||
        !view.events.some(({ turnHash }) => turnHash === state.lastEvent.turnHash))) state.lastEvent = null;
      render(view);
      if (state.pending) {
        if (!state.pending.finalTurnHash) {
          const unresolved = pendingJournal.reconcile(view);
          if (unresolved.replayRefused.length > 0) {
            announce("Replay audit is unavailable. The durable prepared intent is preserved; no event or expiry is inferred.", { error: true });
            return view;
          }
          if (unresolved.expired.length > 0) {
            state.pending = null;
            render(view);
            announce("A prepared-only intent expired before a final signed turn hash was returned.", { error: true });
            return view;
          }
          announce("Recovered a preparation digest without a final signed turn hash. A journal event cannot be inferred from it.", { error: true });
          return view;
        }
        const resumed = await transport.status(state.pending, state.actorPublicKeyHex);
        if (resumed.state === "settled") {
          pendingJournal.reconcile(resumed.view);
          state.lastEvent = resumed.event;
          state.pending = null;
          render(resumed.view);
          announce("Recovered the exact pending turn from the journal; its returned postcard checksum matched.");
          return resumed.view;
        }
        if (resumed.state === "replay-refused") {
          render(resumed.view);
          announce("Replay audit is unavailable. The exact pending coordinate is preserved; no event or expiry is inferred.", { error: true });
          return resumed.view;
        }
        if (resumed.state === "expired") {
          pendingJournal.reconcile(resumed.view);
          state.pending = null;
          render(resumed.view);
          announce("The recovered intent expired by journal sequence without an exact event.", { error: true });
          return resumed.view;
        }
        render(resumed.view);
        announce("A durable pending turn was recovered. Its exact hash is still absent from the journal.");
        return resumed.view;
      }
      const watch = projectGalleyWatch(view, state.actorPublicKeyHex);
      announce(!view.replay.audited
        ? "The node did not return an audited replay. No logbook record or action is claimed."
        : watch.state === "recorded"
        ? "Your signed shift is present in the returned logbook. Come back after the daily watch rotates."
        : watch.state === "available"
          ? "A maintenance station is open. The action remains inert until you approve its exact Dregg turn."
          : "No station is open at this journal head. The returned records remain available below.");
      return view;
    } catch (error) {
      renderWatchUnavailable(error);
      announce(`GALLEY SEALED // ${friendlyError(error)}`, { error: true });
      return null;
    } finally { setBusy(false); }
  }

  async function dispatch(actionToken) {
    if (state.destroyed || state.busy || !state.view) return null;
    setBusy(true);
    announce("Preparing the node's exact maintenance turn…");
    let phase = "preparation";
    let durableIntentStored = false;
    try {
      if (!providerCandidate(dreggProvider)) throw new GalleyApiRefusal("galley-provider", "Dregg turn signer is unavailable");
      if (!state.actorPublicKeyHex) throw new GalleyApiRefusal("galley-actor", "active preparation identity is unavailable");
      state.admission = null;
      state.lastEvent = null;
      const prepared = await transport.requestCommand(state.view, actionToken, state.actorPublicKeyHex);
      phase = "intent-storage";
      state.pending = pendingJournal.record(state.view, prepared.signingRequest);
      durableIntentStored = true;
      render(prepared.view);
      announce("Review the exact Dregg turn. No transaction or token transfer is requested.");
      phase = "signing";
      const admission = await transport.sign(prepared.signingRequest, dreggProvider, state.view.sequence);
      state.admission = admission;
      if (admission.state === "submitted" || admission.state === "queued") {
        phase = "final-hash-storage";
        state.pending = pendingJournal.confirm(state.pending, admission.turnHash);
      } else if (admission.state === "declined" || admission.state === "refused") {
        pendingJournal.discard(state.pending);
        state.pending = null;
      }
      render(prepared.view);
      if (admission.state === "submitted") {
        announce("The exact signed turn was submitted. Looking separately for its final journal event.");
        return await checkPending({ focus: true, alreadyBusy: true });
      }
      if (admission.state === "queued") {
        announce("The exact signed turn is queued for retry. No journal event is claimed yet.", { focus: true });
      } else if (admission.state === "declined") {
        announce("Turn consent was declined. Nothing was submitted.", { focus: true, error: true });
      } else if (admission.state === "refused") {
        announce("The signer or node refused this turn. Nothing was submitted.", { focus: true, error: true });
      } else {
        announce("The signing result is unknown. The prepared hash remains durable in case the response was lost; no journal event is claimed.", { focus: true, error: true });
      }
      return admission;
    } catch (error) {
      if (!durableIntentStored) {
        state.pending = null;
        state.admission = null;
        if (state.view) render(state.view);
        const label = phase === "intent-storage" ? "DURABLE INTENT STORAGE FAILED" : "TURN NOT PREPARED";
        announce(`${label} // ${friendlyError(error)}. Nothing was signed or submitted.`, { focus: true, error: true });
        return null;
      }
      if (phase === "final-hash-storage" && state.admission?.turnHash && state.pending) {
        state.pending = Object.freeze({ ...state.pending, finalTurnHash: state.admission.turnHash });
        if (state.view) render(state.view);
        announce(`FINAL HASH STORAGE FAILED // ${friendlyError(error)}. The signer returned a final hash, but restart recovery is unavailable; keep this page open.`, { focus: true, error: true });
        return null;
      }
      if (state.pending && state.view) {
        state.admission = Object.freeze({ state: "error", turnHash: null, outboxId: null, error: friendlyError(error).slice(0, 320) });
        render(state.view);
      }
      announce(`TURN STATUS UNKNOWN // ${friendlyError(error)}. The prepared hash remains durable for exact recovery.`, { focus: true, error: true });
      return null;
    } finally { setBusy(false); }
  }

  async function checkPending({ focus = true, alreadyBusy = false } = {}) {
    if (state.destroyed || !state.pending) return null;
    if (!state.pending.finalTurnHash) {
      announce("A preparation digest is not a final turn hash. Exact journal reconciliation is unavailable until the signer returns one.", { focus, error: true });
      return null;
    }
    if (!alreadyBusy) setBusy(true);
    announce("Looking for the exact final turn hash in the replayed Galley journal…");
    try {
      if (!state.actorPublicKeyHex) throw new GalleyApiRefusal("galley-actor", "active preparation identity is unavailable");
      const result = await transport.status(state.pending, state.actorPublicKeyHex);
      if (result.state === "settled") {
        pendingJournal.reconcile(result.view);
        state.lastEvent = result.event;
        state.pending = null;
        render(result.view);
        announce("Shift observed by exact final turn hash. Its returned postcard SHA-256 matched; canonical receipt verification is not installed here.", { focus });
      } else if (result.state === "pending") {
        render(result.view);
        announce("The signed turn is not yet in the journal. Its exact coordinate remains durable; check again or refresh later.", { focus });
      } else if (result.state === "replay-refused") {
        render(result.view);
        announce("Replay audit is unavailable. The exact pending coordinate is preserved; no event or expiry is inferred.", { focus, error: true });
      } else {
        pendingJournal.reconcile(result.view);
        state.pending = null;
        render(result.view);
        announce("The prepared intent expired by journal sequence without an exact event.", { focus, error: true });
      }
      return result;
    } catch (error) {
      announce(`TURN STATUS UNKNOWN // ${friendlyError(error)}. The durable coordinate was preserved.`, { focus, error: true });
      return null;
    } finally { if (!alreadyBusy) setBusy(false); }
  }

  const ready = open();
  return Object.freeze({
    ready,
    dispatch,
    refresh: open,
    checkPending,
    getView: () => state.view,
    destroy() {
      state.destroyed = true;
      root.replaceChildren();
    },
  });
}

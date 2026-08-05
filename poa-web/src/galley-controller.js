import {
  GalleyApiRefusal,
  createGalleyPendingIntentJournal,
  galleyActionLabel,
  galleyAvailableAtSequence,
  normalizeGalleyActorIdentity,
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

function friendlyError(error) {
  if (error instanceof GalleyApiRefusal) return `${error.code}: ${error.message}`;
  if (error?.name === "DreggUserDeclined" || error?.code === "user-declined") return "The turn was not signed. Nothing changed.";
  return error instanceof Error ? error.message : "The Galley instrument refused the request.";
}

function actionCopy(kind) {
  switch (kind) {
    case "public_vote": return "Answer one node-authored public call for this watch.";
    case "perform": return "Take the currently offered maintenance action.";
    case "visit_commons": return "Visit the ship commons through its offered action.";
    case "holder_sponsorship": return "Held closed until eligibility can be verified by the federation.";
    default: return "Unknown action.";
  }
}

function providerCandidate(provider) {
  return provider && typeof provider.signTurnV3 === "function" ? provider : null;
}

function identityProviderCandidate(provider) {
  return provider && typeof provider.getActiveIdentity === "function" ? provider : null;
}

function identityFailure(error) {
  if (error?.name === "DreggUserDeclined" || error?.code === "user-declined") {
    return "Active-identity sharing was declined. The Galley remains read-only and no session was requested.";
  }
  if (error instanceof GalleyApiRefusal) return `${error.code}: ${error.message}. No session was requested.`;
  return "An active Dregg public identity is unavailable. The Galley remains read-only and no session was requested.";
}

/**
 * Render the frozen Galley V1 journal contract. Projection/payload JSON remains
 * opaque: the browser never infers a second game state from convenient keys.
 */
export function mountGalley(root, {
  transport,
  dreggProvider = globalThis.window?.dregg ?? null,
  pendingJournal = createGalleyPendingIntentJournal(),
  onView = () => {},
} = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("Galley mount root is required");
  if (!transport || typeof transport.openSession !== "function" || typeof transport.requestCommand !== "function") {
    throw new TypeError("Galley transport is required");
  }
  const documentRef = root.ownerDocument ?? globalThis.document;
  if (!documentRef?.createElement) throw new TypeError("DOM document is required");

  const shell = el(documentRef, "section", "galley-terminal");
  shell.setAttribute("aria-labelledby", "galley-scene-title");
  const headerRoot = el(documentRef, "header", "galley-header");
  const live = el(documentRef, "p", "galley-live", "Opening the Galley journal…");
  live.id = "galley-live-status";
  live.tabIndex = -1;
  live.setAttribute("role", "status");
  live.setAttribute("aria-live", "polite");
  live.setAttribute("aria-atomic", "true");
  const body = el(documentRef, "div", "galley-body");
  const actionsRoot = el(documentRef, "section", "galley-maintenance");
  const projectionRoot = el(documentRef, "section", "galley-commons");
  const evidenceRoot = el(documentRef, "aside", "galley-side");
  body.append(actionsRoot, projectionRoot, evidenceRoot);
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

  function renderHeader(view) {
    const copy = el(documentRef, "div", "galley-header__copy");
    copy.append(
      el(documentRef, "p", "eyebrow", "DECK COMMONS // LIVE JOURNAL"),
      el(documentRef, "h2", "", "The Galley"),
      el(documentRef, "p", "galley-header__description",
        "Take a watch action, sign the exact postcard, and follow its wake into the node journal."),
    );
    copy.children[1].id = "galley-scene-title";
    const gauges = el(documentRef, "dl", "galley-header__gauges");
    appendFact(documentRef, gauges, "Daily", view.dailyId);
    appendFact(documentRef, gauges, "Sequence", String(view.sequence));
    appendFact(documentRef, gauges, "Schema", String(view.schemaVersion));
    appendFact(documentRef, gauges, "Replay", view.replay.audited ? "AUDITED BY NODE" : "NOT AUDITED");
    appendFact(documentRef, gauges, "Prep identity", "CLAIMED / NON-AUTHORITATIVE");
    const boundary = el(documentRef, "p", "galley-mode galley-mode--durable",
      "The permission-shared active public key only personalizes preparation. It does not prove who finalized anything: the exact turn signature and finalized receipt remain authoritative. No Solana wallet is needed for ordinary Galley play.");
    headerRoot.replaceChildren(copy, gauges, boundary);
  }

  function renderIdentityUnavailable() {
    state.view = null;
    state.actorPublicKeyHex = null;
    state.pending = null;
    state.lastEvent = null;
    const copy = el(documentRef, "div", "galley-header__copy");
    copy.append(
      el(documentRef, "p", "eyebrow", "DECK COMMONS // READ-ONLY"),
      el(documentRef, "h2", "", "The Galley"),
      el(documentRef, "p", "galley-header__description",
        "Share the active Dregg public identity to request a personalized public watch from the node."),
    );
    copy.children[1].id = "galley-scene-title";
    headerRoot.replaceChildren(copy, el(documentRef, "p", "galley-mode",
      "This preparation identity is only a claim. An exact signed turn and finalized receipt—not this header—authorize a game transition."));
    actionsRoot.replaceChildren(el(documentRef, "p", "galley-empty",
      "No action or personalized projection was requested without identity permission."));
    projectionRoot.replaceChildren();
    const retry = button(documentRef, "galley-provider__connect", "Share active identity and retry");
    retry.dataset.available = "true";
    retry.addEventListener("click", () => { void open(); });
    evidenceRoot.replaceChildren(el(documentRef, "p", "galley-empty",
      "The pending-intent journal is preserved locally; it is not reconciled against an unpersonalized node response."), retry);
    state.controls = [retry];
  }

  function actionControl(view, action, index, controls) {
    const control = button(documentRef, `galley-action galley-action--${action.kind}`, galleyActionLabel(action.kind));
    const unavailable = action.kind === "holder_sponsorship" || !providerCandidate(dreggProvider) ||
      !view.replay.audited || !galleyAvailableAtSequence(action.expiresAfterSequence, view.sequence);
    control.dataset.galleyAction = action.actionToken;
    control.dataset.actionKind = action.kind;
    control.dataset.available = String(!unavailable);
    control.disabled = unavailable;
    control.tabIndex = index === 0 ? 0 : -1;
    control.setAttribute("aria-describedby", live.id);
    control.append(
      el(documentRef, "small", "", actionCopy(action.kind)),
      el(documentRef, "small", "galley-action__expiry", `valid through journal sequence ${action.expiresAfterSequence}`),
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

  function renderActions(view) {
    const heading = el(documentRef, "div", "galley-section-heading");
    const headingCopy = el(documentRef, "div");
    headingCopy.append(el(documentRef, "p", "panel-label", "CURRENT WATCH"), el(documentRef, "h3", "", "Available stations"));
    heading.append(headingCopy, el(documentRef, "span", "quiet-chip", `${view.actions.length} OFFERED`));
    const intro = el(documentRef, "p", "galley-instruction",
      "Every button carries an opaque, expiring action token issued by the node. Refresh if the watch changes.");
    const region = el(documentRef, "div", "galley-maintenance__actions");
    region.setAttribute("role", "group");
    region.setAttribute("aria-label", "Node-authored Galley actions");
    const visible = view.actions.filter(({ kind }) => kind !== "holder_sponsorship");
    const controls = [];
    visible.forEach((action, index) => controls.push(actionControl(view, action, index, controls)));
    if (controls.length === 0) region.append(el(documentRef, "p", "galley-empty", "No ordinary action is offered at this journal head."));
    else region.append(...controls);
    const refresh = button(documentRef, "galley-provider__connect", "Refresh current watch");
    refresh.dataset.available = "true";
    refresh.addEventListener("click", () => { void open(); });
    state.controls = [...controls, refresh];
    actionsRoot.replaceChildren(heading, intro, region, refresh);
  }

  function renderProjection(view) {
    const heading = el(documentRef, "div", "galley-section-heading");
    const headingCopy = el(documentRef, "div");
    headingCopy.append(el(documentRef, "p", "panel-label", "NODE PROJECTION"), el(documentRef, "h3", "", "Opaque until the presentation schema freezes"));
    heading.append(headingCopy, el(documentRef, "span", "quiet-chip", `V${view.schemaVersion}`));
    const note = el(documentRef, "p", "galley-commons__scene",
      "These bytes are rendered for inspection, not interpreted as a browser-owned score, resource ledger, or rules engine.");
    const projection = el(documentRef, "pre", "galley-projection", JSON.stringify(view.projection, null, 2));
    projection.tabIndex = 0;
    projection.setAttribute("aria-label", "Opaque Galley projection JSON");
    projectionRoot.replaceChildren(heading, note, projection);
  }

  function renderEvidence(view) {
    const provider = el(documentRef, "section", "galley-provider");
    provider.append(el(documentRef, "p", "panel-label", "DREGG TURN LINK"));
    const providerTitle = el(documentRef, "h3", "", providerCandidate(dreggProvider) ? "Signer available" : "Read-only journal");
    providerTitle.id = "galley-provider-title";
    provider.setAttribute("aria-labelledby", providerTitle.id);
    provider.append(providerTitle, el(documentRef, "p", "",
      providerCandidate(dreggProvider)
        ? "The shared public key claims a preparation identity. Consent to the exact turn chooses the actual signer; finalized receipt evidence—not this claim—authorizes the outcome."
        : "The public key personalized this read-only view, but no Dregg turn signer is available. The preparation claim authorizes no mutation."));

    const evidence = el(documentRef, "section", "galley-evidence");
    evidence.append(el(documentRef, "p", "panel-label", "EVENT / RECEIPT / REPLAY"));
    const evidenceTitle = el(documentRef, "h3", "", state.lastEvent ? "Receipt postcard checksum matched" : "The exact wake");
    evidenceTitle.id = "galley-evidence-title";
    evidence.setAttribute("aria-labelledby", evidenceTitle.id);
    evidence.append(evidenceTitle);
    const facts = el(documentRef, "dl", "galley-evidence__facts");
    appendFact(documentRef, facts, "Federation", view.federationId, true);
    appendFact(documentRef, facts, "Aggregate", view.aggregateId, true);
    appendFact(documentRef, facts, "Semantic head", view.semanticHead, true);
    appendFact(documentRef, facts, "Projection", view.projectionDigest, true);
    appendFact(documentRef, facts, "Replay head", view.replay.headDigest, true);
    appendFact(documentRef, facts, "Journal", `${view.replay.eventCount} events · ${view.replay.fromSequence}–${view.replay.throughSequence}`);
    evidence.append(facts);

    if (state.lastEvent) {
      const receipt = el(documentRef, "div", "galley-receipt");
      receipt.append(el(documentRef, "p", "panel-label", "ADJACENT SHA-256 CHECKSUM MATCH"), el(documentRef, "h4", "", `Event ${state.lastEvent.sequence}`));
      const receiptFacts = el(documentRef, "dl");
      appendFact(documentRef, receiptFacts, "Turn", state.lastEvent.turnHash, true);
      appendFact(documentRef, receiptFacts, "Event", state.lastEvent.eventDigest, true);
      appendFact(documentRef, receiptFacts, "Receipt", state.lastEvent.receiptHash, true);
      appendFact(documentRef, receiptFacts, "Postcard", state.lastEvent.receipt.sha256, true);
      receipt.append(receiptFacts);
      evidence.append(receipt);
    }

    const replay = el(documentRef, "ol", "galley-replay");
    replay.setAttribute("aria-label", "Galley event journal");
    for (const event of view.events.slice(-20)) {
      const row = el(documentRef, "li", "galley-replay__event");
      row.append(
        el(documentRef, "span", "galley-replay__sequence", String(event.sequence).padStart(3, "0")),
        el(documentRef, "b", "", `turn ${event.turnHash.slice(0, 12)}…`),
        el(documentRef, "code", "", event.eventDigest),
        el(documentRef, "small", "", `receipt ${event.receiptHash}`),
      );
      replay.append(row);
    }
    evidence.append(replay);
    if (state.admission) {
      const admission = el(documentRef, "div", `galley-admission galley-admission--${state.admission.state}`);
      const labels = {
        submitted: "SUBMITTED / AWAITING JOURNAL",
        queued: "SIGNED / QUEUED",
        refused: "REFUSED / NOT SUBMITTED",
        declined: "DECLINED / NOT SUBMITTED",
        error: "SIGNING RESULT ERROR",
      };
      admission.append(el(documentRef, "p", "panel-label", labels[state.admission.state] ?? "UNKNOWN ADMISSION"));
      const details = {
        submitted: "The node accepted the exact signed turn. Journal observation is checked separately.",
        queued: "The exact signed turn is queued for retry. No node admission or journal receipt is being claimed.",
        refused: "The signer or node refused submission. No journal success is being claimed.",
        declined: "Turn consent was declined. Nothing was submitted and no journal success is being claimed.",
        error: "The signing result was malformed, mismatched, or unavailable. No status poll was started.",
      };
      admission.append(el(documentRef, "p", "", details[state.admission.state] ?? "No admission state is available."));
      const admissionFacts = el(documentRef, "dl");
      if (state.admission.turnHash) appendFact(documentRef, admissionFacts, "Signed turn", state.admission.turnHash, true);
      if (state.admission.outboxId) appendFact(documentRef, admissionFacts, "Outbox", state.admission.outboxId, true);
      if (admissionFacts.children.length > 0) admission.append(admissionFacts);
      if (state.admission.error) admission.append(el(documentRef, "small", "galley-admission__error", state.admission.error));
      evidence.append(admission);
    }
    if (state.pending) {
      const check = button(documentRef, "galley-evidence__check", "Check submitted turn");
      check.dataset.available = "true";
      check.addEventListener("click", () => { void checkPending(); });
      state.controls.push(check);
      evidence.append(check);
    }
    evidenceRoot.replaceChildren(provider, evidence);
  }

  function render(view) {
    if (state.destroyed) return;
    state.view = view;
    renderHeader(view);
    renderActions(view);
    renderProjection(view);
    renderEvidence(view);
    onView(view);
    setBusy(state.busy);
  }

  async function open() {
    if (state.destroyed || state.busy) return null;
    setBusy(true);
    announce("Requesting the active public Dregg identity before contacting the Galley node…");
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
    announce("Reading the current node-authored Galley session for the claimed preparation identity…");
    try {
      const view = await transport.openSession(state.actorPublicKeyHex);
      const recoverable = pendingJournal.forView(view);
      state.pending = recoverable.at(-1) ?? null;
      state.lastEvent = null;
      state.admission = null;
      render(view);
      if (state.pending) {
        const resumed = await transport.status(state.pending, state.actorPublicKeyHex);
        pendingJournal.reconcile(resumed.view);
        if (resumed.state === "settled") {
          state.lastEvent = resumed.event;
          state.pending = null;
          render(resumed.view);
          announce("Recovered pending turn by exact hash; its adjacent receipt-postcard SHA-256 checksum matched.");
          return resumed.view;
        }
        if (resumed.state === "expired") {
          state.pending = null;
          render(resumed.view);
          announce("The recovered pending intent expired by journal sequence without an observed receipt.");
          return resumed.view;
        }
        render(resumed.view);
        announce("Recovered a pending Galley intent. Its exact turn hash is still absent from the current journal.");
        return resumed.view;
      }
      announce(providerCandidate(dreggProvider)
        ? "Galley watch personalized for the claimed preparation identity. Choose an action; the exact turn consent selects the authoritative signer."
        : "Galley watch open read-only. The claimed preparation identity is not a signer and no browser state was substituted.");
      return view;
    } catch (error) {
      announce(`GALLEY SEALED // ${friendlyError(error)}`, { error: true });
      return null;
    } finally { setBusy(false); }
  }

  async function dispatch(actionToken) {
    if (state.destroyed || state.busy || !state.view) return null;
    setBusy(true);
    announce("Preparing the node's exact turn postcard…");
    try {
      if (!providerCandidate(dreggProvider)) throw new GalleyApiRefusal("galley-provider", "Dregg turn signer is unavailable");
      if (!state.actorPublicKeyHex) throw new GalleyApiRefusal("galley-actor", "active preparation identity is unavailable");
      state.admission = null;
      const prepared = await transport.requestCommand(state.view, actionToken, state.actorPublicKeyHex);
      state.pending = pendingJournal.record(state.view, prepared.signingRequest);
      render(prepared.view);
      announce("Review the Dregg turn consent prompt. No transaction or token transfer is requested.");
      const admission = await transport.sign(prepared.signingRequest, dreggProvider, state.view.sequence);
      state.admission = admission;
      render(prepared.view);
      if (admission.state === "submitted") {
        announce("The exact prepared turn was signed and submitted. Looking separately for its exact journal receipt.");
        return await checkPending({ focus: true, alreadyBusy: true });
      }
      if (admission.state === "queued") {
        announce("The exact signed turn is queued for retry. No node admission or journal receipt is claimed; no automatic status poll was started.", { focus: true });
      } else if (admission.state === "declined") {
        announce("Turn consent was declined. Nothing was submitted and no automatic status poll was started.", { focus: true, error: true });
      } else if (admission.state === "refused") {
        announce("The signer or node refused this turn. Nothing was submitted and no automatic status poll was started.", { focus: true, error: true });
      } else {
        announce("The signing result was malformed, mismatched, or unavailable. No automatic status poll was started.", { focus: true, error: true });
      }
      return admission;
    } catch (error) {
      if (state.pending && state.view) {
        state.admission = Object.freeze({
          state: error?.name === "DreggUserDeclined" || error?.code === "user-declined" ? "declined" : "error",
          turnHash: null,
          outboxId: null,
          error: friendlyError(error).slice(0, 320),
        });
        render(state.view);
      }
      announce(`NO CHANGE // ${friendlyError(error)}`, { focus: true, error: true });
      return null;
    } finally { setBusy(false); }
  }

  async function checkPending({ focus = true, alreadyBusy = false } = {}) {
    if (state.destroyed || !state.pending) return null;
    if (!alreadyBusy) setBusy(true);
    announce("Looking for the exact turn hash in the Galley journal…");
    try {
      if (!state.actorPublicKeyHex) throw new GalleyApiRefusal("galley-actor", "active preparation identity is unavailable");
      const result = await transport.status(state.pending, state.actorPublicKeyHex);
      pendingJournal.reconcile(result.view);
      if (result.state === "settled") {
        state.lastEvent = result.event;
        state.pending = null;
        render(result.view);
        announce("Turn observed. Its adjacent receipt-postcard SHA-256 checksum matched; canonical receipt verification is not yet installed.", { focus });
      } else if (result.state === "pending") {
        render(result.view);
        announce("Turn submitted but not yet observed in the journal. Check again from the evidence panel.", { focus });
      } else {
        state.pending = null;
        render(result.view);
        announce("The pending intent expired by journal sequence without an observed receipt.", { focus, error: true });
      }
      return result;
    } catch (error) {
      announce(`TURN STATUS UNKNOWN // ${friendlyError(error)}`, { focus, error: true });
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

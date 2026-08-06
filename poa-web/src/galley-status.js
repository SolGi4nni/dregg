import { DEFAULT_GALLEY_ENDPOINTS } from "./galley-runtime.js";

/**
 * THE GALLEY, AS A STANDING — visible whether or not you can act in it.
 *
 * The Galley is the one organ on this terminal that is genuinely OPEN: the node
 * projects a live journal, offers server-issued actions, and records a shift as
 * a finalized event. The terminal below this view already renders all of that
 * — but only for a visitor who can share an active Dregg public key, because
 * `GET /api/poa/galley/v1/status` requires an `X-Dregg-Actor` header and refuses
 * without one. Everyone else met a door and a request for permission, with no
 * way to tell whether there was a Galley behind it at all.
 *
 * ⚠ AND THIS VIEW DOES NOT SOLVE THAT BY INVENTING AN ACTOR. A random 32-byte
 * key would make the node answer — the header is a personalization claim that
 * authorizes nothing — and it would be this page manufacturing an identity to
 * get a document it could then present as a reading. What it does instead is ask
 * ANONYMOUSLY and report exactly what came back. A node that answers
 * `poa-galley-actor-required` has told us something true and worth showing: the
 * organ is mounted, it is answering, and it wants a claim we do not have.
 *
 * ⚠ THE PROBE IS KEYED ON THE NODE'S OWN REFUSAL CODE, not on the HTTP number.
 * 401 is also what a bearer layer says, and the difference between "the Galley
 * wants an actor" and "this route moved behind auth" is the whole meaning of the
 * answer. When the code is not one this client knows, it is shown verbatim
 * rather than folded into the nearest familiar state.
 *
 * When the terminal below DOES obtain a real personalized watch it hands it here
 * through `onView`, and every figure in this view comes from that checked
 * document instead of from the probe.
 */

/** Pinned to the transport's own constant, so one rename cannot leave two spellings. */
export const GALLEY_STATUS_ENDPOINT = DEFAULT_GALLEY_ENDPOINTS.status;
export const GALLEY_ACTOR_REQUIRED_CODE = "poa-galley-actor-required";

/**
 * Ask the Galley status route with NO actor header, and report what it said.
 *
 * Never throws, and never sends a header. The absence of the header is the
 * entire experiment: it is what makes the answer evidence about the route rather
 * than about whatever key we chose.
 */
export async function probeGalleyStatus({ baseUrl, fetchImpl = globalThis.fetch, endpoint = GALLEY_STATUS_ENDPOINT } = {}) {
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "galley-fetch", detail: "No fetch is available in this environment" });
  }
  const url = new URL(endpoint, baseUrl ?? globalThis.location?.href ?? "https://invalid.local/");
  let response;
  let body = null;
  try {
    response = await fetchImpl(url, { cache: "no-store", credentials: "same-origin" });
    const text = await response.text();
    try { body = JSON.parse(text); } catch { body = null; }
  } catch {
    return Object.freeze({ state: "unreachable", code: "galley-fetch", detail: "No Galley answered on this origin" });
  }
  if (response?.ok) {
    // Surprising and loud on purpose. If this ever fires, the actor requirement
    // is gone and a document meant to be personalized is being served to nobody
    // in particular — which is a finding, not a nicer outcome.
    return Object.freeze({ state: "open-without-identity", code: null, detail: "The Galley answered a status request that carried no actor claim at all" });
  }
  const code = typeof body?.code === "string" ? body.code : null;
  if (code === GALLEY_ACTOR_REQUIRED_CODE) {
    return Object.freeze({ state: "identity-required", code, detail: typeof body?.message === "string" ? body.message : "X-Dregg-Actor is required" });
  }
  if (code === null) {
    // ⚠ THE DISCRIMINATOR IS THE ERROR BODY, NOT THE HTTP NUMBER. A refusal
    // carrying the Galley's own `code` came from the Galley; a bare 404 from a
    // static host or a 502 from a proxy came from something that is not the
    // Galley at all, and calling that "the Galley refused" would credit an
    // answer to an organ that never spoke. Measured against the local dev
    // server, where this said "refused for a reason this terminal does not
    // know" about a plain file-server 404.
    return Object.freeze({
      state: "unreachable",
      code: `http-${response?.status ?? "none"}`,
      detail: `Nothing identifying itself as the Galley answered on this origin (HTTP ${response?.status ?? "nothing"})`,
    });
  }
  return Object.freeze({
    state: "refused",
    code,
    detail: typeof body?.message === "string" ? body.message : `The Galley answered ${code}`,
  });
}

function short(value) {
  return `${value.slice(0, 12)}…${value.slice(-4)}`;
}

function viewRows(view) {
  const replay = view.replay;
  const projection = view.projection;
  return Object.freeze([
    Object.freeze(["Daily", view.dailyId]),
    Object.freeze(["Aggregate", view.aggregateId]),
    Object.freeze(["Schema version", String(view.schemaVersion)]),
    Object.freeze(["Journal head", String(view.sequence)]),
    Object.freeze(["Semantic head", short(view.semanticHead)]),
    Object.freeze(["Projection digest", short(view.projectionDigest)]),
    Object.freeze(["Replay", replay.audited
      ? `node reports the journal audited: ${replay.eventCount} of ${replay.totalEventCount} events returned, sequences ${replay.fromSequence}–${replay.throughSequence}`
      : "REFUSED by the node's own replay-audit gate; no event from this response is treated as a record"]),
    Object.freeze(["Actions offered", String(view.actions.length)]),
    Object.freeze(["Public shifts", String(projection.publicPlayCount)]),
    Object.freeze(["Sponsorships", String(projection.sponsorshipCount)]),
    Object.freeze(["Local service", String(projection.localServiceTotal)]),
    Object.freeze(["Canon revision", String(projection.canonRevision)]),
    Object.freeze(["Canon root", short(projection.canonRoot)]),
    Object.freeze(["Loot root", short(projection.lootRoot)]),
    Object.freeze(["Power root", short(projection.powerRoot)]),
  ]);
}

/**
 * One model for the Galley's standing.
 *
 * A checked view always wins over a probe: once the terminal has a real
 * document, the probe's "somebody is answering" is a strictly weaker statement
 * about the same route and there is no reason to show it.
 */
export function buildGalleyStatus({ probe = null, view = null } = {}) {
  if (view) {
    const quiet = view.sequence === 0;
    return Object.freeze({
      state: view.replay.audited ? "open" : "refused",
      headline: view.replay.audited
        ? (quiet ? "The Galley is open, and no shift has been taken yet" : "The Galley is open")
        : "The Galley journal failed its replay audit",
      standing: view.replay.audited
        ? (quiet
          ? "The node is projecting a live journal at sequence zero. That is not a page that failed to load: it is a Galley nobody has worked a shift in, and the next one starts the record."
          : "Every figure below is read off the node's projection of its own journal, checked against the head it publishes.")
        : "The node did not audit this journal, so the returned events are inert here: no shift is shown and no action is offered from this response.",
      rows: viewRows(view),
      source: "a personalized status document, checked field by field",
    });
  }
  if (!probe || probe.state === "pending") {
    return Object.freeze({ state: "pending", headline: "Reading the Galley", standing: "Asking the node whether the Galley is answering.", rows: Object.freeze([]), source: null });
  }
  if (probe.state === "identity-required") {
    return Object.freeze({
      state: "identity-required",
      headline: "The Galley is mounted and answering",
      standing: "It will not project a watch without an actor claim, and this terminal will not invent one — a made-up key would produce a document that looked like a reading of somebody. Share an active Dregg identity below and every figure here fills in from the node.",
      rows: Object.freeze([
        Object.freeze(["Route", GALLEY_STATUS_ENDPOINT]),
        Object.freeze(["Answered", `yes — ${probe.code}`]),
        Object.freeze(["What it wants", probe.detail]),
        Object.freeze(["What that grants", "nothing. The actor header selects which read view you get; only an exact signed turn and its finalized journal event can record a shift."]),
      ]),
      source: "an anonymous probe of the status route",
    });
  }
  if (probe.state === "open-without-identity") {
    return Object.freeze({
      state: "open-without-identity",
      headline: "The Galley answered a request with no identity at all",
      standing: "This route is documented as requiring an actor claim and it did not ask for one. No figure is rendered from that response: a document served to nobody in particular is not a reading of anybody, and this page will not present it as one.",
      rows: Object.freeze([Object.freeze(["Route", GALLEY_STATUS_ENDPOINT]), Object.freeze(["Answered", probe.detail])]),
      source: "an anonymous probe of the status route",
    });
  }
  if (probe.state === "refused") {
    return Object.freeze({
      state: "refused",
      headline: "The Galley refused for a reason this terminal does not know",
      standing: `The node answered ${probe.code}, which is not the actor-claim refusal this client understands. That is shown as it arrived rather than folded into the nearest familiar state.`,
      rows: Object.freeze([Object.freeze(["Route", GALLEY_STATUS_ENDPOINT]), Object.freeze(["Answered", probe.detail])]),
      source: "an anonymous probe of the status route",
    });
  }
  return Object.freeze({
    state: "sealed",
    headline: "No Galley answered",
    standing: `${probe.detail}. Nothing about the journal, the shifts, or the day is claimed here, because nothing was read.`,
    rows: Object.freeze([Object.freeze(["Route", GALLEY_STATUS_ENDPOINT])]),
    source: null,
  });
}

function element(tag, className, textContent) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (textContent !== undefined) node.textContent = textContent;
  return node;
}

export function mountGalleyStatus(root, model) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a galley status root is required");
  root.dataset.state = model.state;
  const nodes = [
    element("p", "panel-label", "GALLEY // STANDING"),
    element("h2", "galley-standing__headline", model.headline),
    element("p", "galley-standing__copy", model.standing),
  ];
  if (model.rows.length > 0) {
    const list = element("dl", "galley-standing__rows");
    for (const [term, detail] of model.rows) {
      const row = element("div");
      row.append(element("dt", "", term), element("dd", "", detail));
      list.append(row);
    }
    nodes.push(list);
  }
  if (model.source) nodes.push(element("small", "galley-standing__source", `Read from ${model.source}.`));
  root.replaceChildren(...nodes);
  return root;
}

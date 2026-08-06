import { boundedArray, bool, digest32, exactKeys, natural, refuse, text } from "./wire-shape.js";

/**
 * THE STATION — the communal ship instrument panel, and the salvage crate's
 * authored schedule.
 *
 * `GET /api/poa/station/{authority}/panel` serves a `POA-STATION-VIEW-1`
 * envelope wrapped around the exact `POA-STATION-DAILY-OUT-1` bytes native Lean
 * emitted (`Dregg2.Games.PathOfAngels.StationDailyRuntime`). This module parses
 * both layers and hands the page a render model. It computes no gauge, decides
 * no eligibility, and picks no period: every figure below came off the wire.
 *
 * ⚠ WHAT THIS ORGAN CANNOT ANSWER, and the page must not imply it can.
 *
 * There is no current-period pointer anywhere on this route, and that is a
 * type-level fact rather than an omission: `SalvageCrate.State` — which is where
 * `currentPeriod` lives — has a private constructor and no public producer, and
 * `SalvageCrate.openCrate` demands a `CurrentStateCapability` declared `opaque`
 * with no producer anywhere in the tree. So "what does the crate hold today" is
 * NOT a question this document answers, `rotation` is the whole authored
 * schedule rather than one day of it, and no copy here may say a day passed, a
 * draw happened, or a period is live.
 *
 * ⚠ AND THE ZEROS ARE THE CONTENT. Every gauge reads zero and will until a
 * judged opening exists. Lean asserts exactly that — `the_served_ship_has_not_
 * been_moved` pins one dial at zero with nothing observed and nothing admitted,
 * and goes red the day an opening can be folded in. A page that dressed this as
 * "loading" or filled a needle to look alive would be lying about a theorem.
 *
 * The panel route names no crew member (`crew: null` in the request Lean
 * accepts), so `crew` is null in every document this page reads. The crew route
 * exists and takes a 64-hex crew key; this terminal binds no crew identity, so
 * it does not ask.
 */

export const STATION_PANEL_ROUTE = "/api/poa/station/{authority}/panel";
export const STATION_CREW_ROUTE = "/api/poa/station/{authority}/crew/{crew}";
export const STATION_VIEW_FORMAT = "POA-STATION-VIEW-1";
export const STATION_DOCUMENT_FORMAT = "POA-STATION-DAILY-OUT-1";

/**
 * The exact key sets, EXPORTED so the gate can hold them against the Lean
 * encoders that emit them.
 *
 * They are exported rather than restated in a test on purpose: a test that
 * carried its own copy would be a third spelling, and the failure mode of three
 * spellings is that two of them get updated. `tests/station-panel.test.mjs`
 * compares THESE against `StationDailyRuntime.lean`, so there are exactly two
 * sources and they must agree.
 */
export const STATION_KEY_SETS = Object.freeze({
  envelope: Object.freeze(["format", "authority_id", "content_provenance", "write_path", "station", "consensus_finality"]),
  document: Object.freeze([
    "format", "federation_id", "content_session", "content_epoch", "gauges",
    "recovered_kinds", "observed", "admitted", "opens_at", "closes_at",
    "table_rows", "ticket_count", "crew",
  ]),
  gauge: Object.freeze(["gauge", "meter", "exact_total", "full_at", "shown", "at_full"]),
  crew: Object.freeze(["key", "eligible", "rotation"]),
  period: Object.freeze(["period", "beacon", "entry"]),
  entry: Object.freeze(["id", "prize", "supplies"]),
});

const { envelope: ENVELOPE_KEYS, document: DOCUMENT_KEYS, gauge: GAUGE_KEYS,
  crew: CREW_KEYS, period: PERIOD_KEYS, entry: ENTRY_KEYS } = STATION_KEY_SETS;

const MAX_GAUGES = 64;
const MAX_ROTATION = 512;

const SHAPE = Object.freeze({ shape: "station-shape", field: "station-field" });

/**
 * One gauge reading, with its own arithmetic re-derived rather than believed.
 *
 * The wire publishes `exact_total` (unclipped) and `shown` (the needle) as
 * separate fields on purpose, so the display scale can never quietly become the
 * bound. That separation is only worth anything if somebody CHECKS it: Lean's
 * `readingOf` sets `shown = min exactTotal fullAt` and `atFull = fullAt ≤
 * exactTotal`, and both are recomputed here. A node that clipped wrong, or that
 * parked a needle at full while the total says otherwise, is refused — it does
 * not get rendered with a footnote.
 */
function parseGauge(value, index) {
  exactKeys(value, GAUGE_KEYS, `station gauge ${index}`, SHAPE);
  const gauge = natural(value.gauge, `station gauge ${index} id`, "station-gauge");
  const meter = text(value.meter, `station gauge ${index} meter`, "station-gauge", 64);
  const exactTotal = natural(value.exact_total, `station gauge ${index} exact total`, "station-gauge");
  const fullAt = natural(value.full_at, `station gauge ${index} full mark`, "station-gauge");
  const shown = natural(value.shown, `station gauge ${index} needle`, "station-gauge");
  const atFull = bool(value.at_full, `station gauge ${index} at-full flag`, "station-gauge");
  refuse(
    shown === Math.min(exactTotal, fullAt),
    "station-gauge",
    `station gauge ${index} needle is not the clipped total; the display scale disagrees with the arithmetic`,
  );
  refuse(
    atFull === (fullAt <= exactTotal),
    "station-gauge",
    `station gauge ${index} at-full flag disagrees with its own total`,
  );
  return Object.freeze({ gauge, meter, exactTotal, fullAt, shown, atFull });
}

function parseEntry(value, at) {
  if (value === null) return null;
  exactKeys(value, ENTRY_KEYS, at, SHAPE);
  return Object.freeze({
    id: natural(value.id, `${at} id`, "station-rotation"),
    prize: text(value.prize, `${at} prize`, "station-rotation", 128),
    supplies: natural(value.supplies, `${at} supplies`, "station-rotation"),
  });
}

function parsePeriod(value, index) {
  const at = `station rotation period ${index}`;
  exactKeys(value, PERIOD_KEYS, at, SHAPE);
  return Object.freeze({
    period: natural(value.period, `${at} number`, "station-rotation"),
    beacon: digest32(value.beacon, `${at} beacon`, "station-rotation"),
    entry: parseEntry(value.entry, `${at} entry`),
  });
}

function parseCrew(value) {
  if (value === null) return null;
  exactKeys(value, CREW_KEYS, "station crew", SHAPE);
  const rotation = boundedArray(value.rotation, "station crew rotation", "station-rotation", MAX_ROTATION);
  return Object.freeze({
    key: digest32(value.key, "station crew key", "station-crew"),
    eligible: bool(value.eligible, "station crew eligibility", "station-crew"),
    rotation: Object.freeze(rotation.map(parsePeriod)),
  });
}

/** The Lean-emitted document, checked field by field. */
export function parseStationDocument(value) {
  exactKeys(value, DOCUMENT_KEYS, "station document", SHAPE);
  refuse(value.format === STATION_DOCUMENT_FORMAT, "station-format", `unsupported station document format: ${value.format}`);
  const gauges = boundedArray(value.gauges, "station gauges", "station-gauge", MAX_GAUGES);
  const opensAt = natural(value.opens_at, "station schedule opening period", "station-schedule");
  const closesAt = natural(value.closes_at, "station schedule closing period", "station-schedule");
  refuse(opensAt <= closesAt, "station-schedule", "the authored crate schedule closes before it opens");
  return Object.freeze({
    federationId: digest32(value.federation_id, "station federation id", "station-identity"),
    contentSession: digest32(value.content_session, "station content session", "station-identity"),
    contentEpoch: natural(value.content_epoch, "station content epoch", "station-identity"),
    gauges: Object.freeze(gauges.map(parseGauge)),
    recoveredKinds: natural(value.recovered_kinds, "station recovered kinds", "station-count"),
    observed: natural(value.observed, "station observed openings", "station-count"),
    admitted: natural(value.admitted, "station admitted openings", "station-count"),
    opensAt,
    closesAt,
    tableRows: natural(value.table_rows, "station loot table rows", "station-count"),
    ticketCount: natural(value.ticket_count, "station ticket count", "station-count"),
    crew: parseCrew(value.crew),
  });
}

/**
 * The serving envelope.
 *
 * ⚠ The envelope's `authority_id` is THIS NODE's federation; the document's
 * `federation_id` is the AUTHORED one, and the node's own docblock says they
 * need not be equal because the station is Lean-authored content and no station
 * genesis ceremony exists. So this does not require them to match — it records
 * whether they do, and the page says which, rather than either assuming equality
 * or hiding the difference.
 */
export function parseStationView(value, authorityId) {
  exactKeys(value, ENVELOPE_KEYS, "station publication", SHAPE);
  refuse(value.format === STATION_VIEW_FORMAT, "station-format", `unsupported station publication format: ${value.format}`);
  digest32(value.authority_id, "station authority id", "station-authority");
  refuse(value.authority_id === authorityId, "station-authority", "station publication is for another authority");
  const station = parseStationDocument(value.station);
  return Object.freeze({
    authorityId: value.authority_id,
    contentProvenance: text(value.content_provenance, "station content provenance", "station-claim"),
    writePath: text(value.write_path, "station write-path claim", "station-claim"),
    consensusFinality: text(value.consensus_finality, "station finality claim", "station-claim"),
    authoredHere: value.station.federation_id === value.authority_id,
    station,
  });
}

/**
 * Read the station panel for this authority.
 *
 * Never throws: every failure is a STATE, exactly as the slot read is. A station
 * this page cannot read must land as an absence with a reason, because the
 * alternative — a partial panel, or a zeroed one that looks like the real zeros
 * — is indistinguishable from the honest installed reading.
 */
export async function loadStationState({ authorityId, baseUrl, fetchImpl = globalThis.fetch, prefix = "/node" } = {}) {
  if (typeof authorityId !== "string" || !/^[0-9a-f]{64}$/.test(authorityId)) {
    return Object.freeze({ state: "unreachable", code: "station-authority", reason: "This terminal has no authority id to ask about" });
  }
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "station-fetch", reason: "No fetch is available in this environment" });
  }
  const url = new URL(
    `${prefix}${STATION_PANEL_ROUTE.replace("{authority}", authorityId)}`,
    baseUrl ?? globalThis.location?.href ?? "https://invalid.local/",
  );
  let body;
  let ok;
  let status;
  try {
    const response = await fetchImpl(url, { cache: "no-store", credentials: "same-origin" });
    ok = Boolean(response?.ok);
    status = response?.status ?? null;
    body = JSON.parse(await response.text());
  } catch {
    return Object.freeze({ state: "unreachable", code: "station-fetch", reason: "No station answered on this origin" });
  }
  if (!ok) {
    // The node's refusals are legible (`refused` + `detail`); say which one it
    // was rather than only the HTTP number, so "the station is rate-limited" and
    // "this node serves another federation" do not read the same.
    const refused = typeof body?.refused === "string" ? body.refused : null;
    return Object.freeze({
      state: "unreachable",
      code: refused ?? "station-status",
      reason: refused
        ? `The station refused this read (${refused})`
        : `The authority answered HTTP ${status ?? "nothing"}`,
    });
  }
  try {
    return Object.freeze({ state: "ready", view: parseStationView(body, authorityId) });
  } catch (error) {
    return Object.freeze({ state: "refused", code: error?.code ?? "station-shape", reason: error?.message ?? "the station publication was refused" });
  }
}

const METER_LABEL = Object.freeze({
  intel: "INTEL", supplies: "SUPPLIES", cohesion: "COHESION", influence: "INFLUENCE", score: "SCORE",
});

function meterLabel(meter) {
  return METER_LABEL[meter] ?? meter.toUpperCase();
}

function short(value) {
  return `${value.slice(0, 12)}…${value.slice(-4)}`;
}

/**
 * The one render model for the station.
 *
 * The headline is a reading of the gauges and the counts, never a mood: it says
 * "nothing has moved the ship" exactly when every needle is zero and nothing was
 * observed or admitted, and it says what did move otherwise.
 */
export function buildStationPanel(station) {
  if (!station || station.state === "pending") {
    return Object.freeze({
      state: "pending",
      eyebrow: "STATION // COMMUNAL INSTRUMENT",
      headline: "Reading the ship instruments",
      standing: "Asking the authority for the installed panel.",
      gauges: Object.freeze([]),
      counts: Object.freeze([]),
      crate: Object.freeze([]),
      provenance: Object.freeze([]),
    });
  }
  if (station.state !== "ready") {
    const refused = station.state === "refused";
    return Object.freeze({
      state: refused ? "refused" : "sealed",
      eyebrow: "STATION // COMMUNAL INSTRUMENT",
      headline: refused ? "The station panel was refused" : "No station answered",
      standing: refused
        ? `A panel was served and this terminal would not accept it (${station.code}): ${station.reason}. No figure from it is shown.`
        : `${station.reason} (${station.code}). No gauge, schedule, or count is shown, because none was read.`,
      gauges: Object.freeze([]),
      counts: Object.freeze([]),
      crate: Object.freeze([]),
      provenance: Object.freeze([]),
    });
  }

  const { view } = station;
  const { station: doc } = view;
  const still = doc.gauges.every((gauge) => gauge.exactTotal === 0) &&
    doc.observed === 0 && doc.admitted === 0 && doc.recoveredKinds === 0;

  return Object.freeze({
    state: "ready",
    eyebrow: "STATION // COMMUNAL INSTRUMENT",
    headline: still ? "Nothing has moved the ship" : "The ship has moved",
    standing: still
      ? "This is the station exactly as installed, not a station whose figures have not arrived. No crate opening has ever been accepted here — the opening demands a capability no Lean term in the tree builds — so every dial below reads its installed value, and Lean asserts that reading rather than this page assuming it."
      : "At least one gauge, observation, or admission is non-zero. Every figure below is the served reading; none of it is settled by quorum.",
    gauges: Object.freeze(doc.gauges.map((gauge) => Object.freeze({
      id: gauge.gauge,
      label: meterLabel(gauge.meter),
      reading: `${gauge.shown} of ${gauge.fullAt}`,
      exact: gauge.exactTotal === gauge.shown
        ? "exact total agrees with the needle"
        : `exact total ${gauge.exactTotal}, past the ${gauge.fullAt} mark`,
      atFull: gauge.atFull,
      shown: gauge.shown,
      fullAt: gauge.fullAt,
      exactTotal: gauge.exactTotal,
    }))),
    counts: Object.freeze([
      Object.freeze(["Salvage kinds recovered", String(doc.recoveredKinds)]),
      Object.freeze(["Openings observed", String(doc.observed)]),
      Object.freeze(["Openings admitted", String(doc.admitted)]),
    ]),
    crate: Object.freeze([
      Object.freeze(["Authored schedule", `periods ${doc.opensAt} through ${doc.closesAt}`]),
      Object.freeze(["Loot table", `${doc.tableRows} row${doc.tableRows === 1 ? "" : "s"}`]),
      Object.freeze(["Ticket entries", String(doc.ticketCount)]),
      Object.freeze([
        "Which period is live",
        "not published — this route carries no current-period pointer, so the schedule is the whole authored run of periods and not one day of it",
      ]),
      Object.freeze([
        "Your rotation",
        doc.crew === null
          ? "not requested — the communal panel names no crew member, and this terminal binds no crew key to ask the crew route with"
          : `${doc.crew.rotation.length} authored period${doc.crew.rotation.length === 1 ? "" : "s"} for ${short(doc.crew.key)}; ${doc.crew.eligible ? "on the authored roster" : "not on the authored roster"}`,
      ]),
    ]),
    provenance: Object.freeze([
      Object.freeze(["Content epoch", String(doc.contentEpoch)]),
      Object.freeze(["Content session", short(doc.contentSession)]),
      Object.freeze([
        "Authored federation",
        view.authoredHere
          ? `${short(doc.federationId)} — the same federation this node serves`
          : `${short(doc.federationId)} — NOT this node's authority ${short(view.authorityId)}; the station is authored content, not content a genesis ceremony installed here`,
      ]),
      Object.freeze(["Provenance", view.contentProvenance]),
      Object.freeze(["Write path", view.writePath]),
      Object.freeze(["Finality", view.consensusFinality]),
    ]),
  });
}

function element(tag, className, textContent) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (textContent !== undefined) node.textContent = textContent;
  return node;
}

function factList(rows, className) {
  const list = element("dl", className);
  for (const [term, detail] of rows) {
    const row = element("div");
    row.append(element("dt", "", term), element("dd", "", detail));
    list.append(row);
  }
  return list;
}

export function mountStationPanel(root, panel) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a station panel root is required");
  root.dataset.state = panel.state;
  const nodes = [
    element("p", "panel-label", panel.eyebrow),
    element("h2", "station-panel__headline", panel.headline),
    element("p", "station-panel__standing", panel.standing),
  ];
  if (panel.gauges.length > 0) {
    const dials = element("div", "station-panel__gauges");
    for (const gauge of panel.gauges) {
      const dial = element("article", "station-gauge");
      dial.dataset.gauge = String(gauge.id);
      dial.dataset.atFull = String(gauge.atFull);
      dial.append(
        element("b", "station-gauge__label", gauge.label),
        element("span", "station-gauge__reading", gauge.reading),
        element("small", "station-gauge__exact", gauge.exact),
      );
      dials.append(dial);
    }
    nodes.push(dials);
  }
  if (panel.counts.length > 0) nodes.push(factList(panel.counts, "station-panel__counts"));
  if (panel.crate.length > 0) {
    nodes.push(element("p", "panel-label", "SALVAGE CRATE // AUTHORED SCHEDULE"));
    nodes.push(factList(panel.crate, "station-panel__crate"));
  }
  if (panel.provenance.length > 0) {
    const fold = element("details", "verify-fold");
    fold.append(element("summary", "verify-fold__summary", "Provenance and standing claims"));
    fold.append(factList(panel.provenance, "verify-fold__rows"));
    nodes.push(fold);
  }
  root.replaceChildren(...nodes);
  return root;
}

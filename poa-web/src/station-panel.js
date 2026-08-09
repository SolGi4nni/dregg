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
 * ⚠ TWO CLAIMS THAT USED TO LIVE HERE ARE GONE, because they became FALSE.
 *
 * The first said `CurrentStateCapability` was "declared `opaque` with no
 * producer anywhere in the tree". The second said "No crate opening has ever
 * been accepted here — the opening demands a capability no Lean term in the tree
 * builds". Neither is true at HEAD: the capability is a sealed structure rooted
 * in `SalvageCrate.genesis`, a crew member opens the crate at
 * `POST /api/poa/station/{authority}/crate/open`, and the panel this page reads
 * is a FOLD OF THE NODE'S DURABLE OPEN LOG rather than the installed ship.
 *
 * So zeros here mean the log is EMPTY — nobody has opened the crate on this
 * node — and the copy says that, rather than saying openings are impossible.
 *
 * ⚠ WHAT THIS ORGAN STILL CANNOT ANSWER. There is no current-period pointer on
 * the READ document: `rotation` is the whole authored schedule rather than one
 * day of it, and no copy here may say a day passed or a period is live. The
 * crate-open reply DOES carry the period it opened, and the honest sentence
 * about it is the node's own `finality_gap`, which this page renders VERBATIM
 * rather than paraphrasing — see `buildCrateOpenAction`.
 *
 * ⚠ AND A REFUSAL IS NEVER A ZERO-MOVE. `opened: false` carries no `entry` and
 * no `panel` (Lean's `a_refused_open_publishes_no_gauge_and_no_entry`), so this
 * module draws NO NEEDLE on a refusal. A refusal rendered as "the ship moved by
 * zero" would be a different claim from the one the node made.
 *
 * The panel route names no crew member (`crew: null` in the request Lean
 * accepts), so `crew` is null in every document this page reads. The crew route
 * exists and takes a 64-hex crew key; this terminal binds no crew identity, so
 * it does not ask. THE BROWSER AUTHORS IDENTITY ONLY: the open request body is
 * one crew key, and no seed, beacon, date, ticket, entry, contribution, counter,
 * sequence, period or panel state is ever sent from here.
 */

export const STATION_PANEL_ROUTE = "/api/poa/station/{authority}/panel";
export const STATION_CREW_ROUTE = "/api/poa/station/{authority}/crew/{crew}";
export const CRATE_OPEN_ROUTE = "/api/poa/station/{authority}/crate/open";
export const STATION_VIEW_FORMAT = "POA-STATION-VIEW-1";
export const STATION_DOCUMENT_FORMAT = "POA-STATION-DAILY-OUT-1";
export const CRATE_OPEN_VIEW_FORMAT = "POA-CRATE-OPEN-VIEW-1";
export const CRATE_OPEN_DOCUMENT_FORMAT = "POA-CRATE-OPEN-OUT-1";

/**
 * The refusal tags `StationCrateOpenRuntime.Refusal.label` emits, and the words
 * this page says for each.
 *
 * ⚠ EXACT, and a tag not on this list is REFUSED rather than shown raw. The set
 * is `Refusal`'s constructors, and the day Lean grows one this page must be
 * taught what it means — a client that echoed an unknown tag would be inventing
 * copy for a state it has never seen.
 */
export const CRATE_REFUSALS = Object.freeze({
  "already-opened-this-period": "You have already opened the crate for this period. One crew key opens it once.",
  "ineligible-crew": "This crew key is not on the crew list the curator signed, so the crate will not open for it.",
  "crate-refused": "The crate declined this opening. Nothing was drawn and the ship did not move.",
  "history-refused": "This node's log of openings is not one this crate could have produced, so nothing was replayed and nothing was decided.",
  "panel-refused": "The crate accepted the opening and the ship's panel would not take the receipt, so nothing was added up.",
});

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
  envelope: Object.freeze(["format", "authority_id", "content_provenance", "write_path", "station", "log_rows_folded", "consensus_finality"]),
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

/**
 * The crate-open key sets, held against `StationCrateOpenRuntime.lean`'s
 * encoders by `tests/station-panel.test.mjs` exactly as the station sets are.
 *
 * ⚠ `gauge` and `entry` are the SAME sets as above and are not restated: Lean
 * spells them with `StationDailyRuntime.GaugeWire.toJson` / `EntryWire.toJson`
 * on both wires, and a second copy here would be a third spelling of a thing
 * that has one.
 */
export const CRATE_OPEN_KEY_SETS = Object.freeze({
  envelope: Object.freeze([
    "format", "authority_id", "content_provenance", "write_path", "finality_gap",
    "crate_open", "log_rows_replayed", "log_appended", "consensus_finality",
  ]),
  document: Object.freeze([
    "format", "federation_id", "content_session", "content_epoch", "opener",
    "period", "opened", "refusal", "entry", "panel",
  ]),
  panel: Object.freeze(["gauges", "recovered_kinds", "observed", "admitted"]),
});

const { envelope: ENVELOPE_KEYS, document: DOCUMENT_KEYS, gauge: GAUGE_KEYS,
  crew: CREW_KEYS, period: PERIOD_KEYS, entry: ENTRY_KEYS } = STATION_KEY_SETS;

const { envelope: OPEN_ENVELOPE_KEYS, document: OPEN_DOCUMENT_KEYS,
  panel: OPEN_PANEL_KEYS } = CRATE_OPEN_KEY_SETS;

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
    // How many rows of the node's durable open log produced these gauges. This
    // is what tells "nobody has opened the crate" apart from "this read is not
    // folding the log" — the pair that was indistinguishable for as long as the
    // second one was true.
    logRowsFolded: natural(value.log_rows_folded, "station folded log rows", "station-count"),
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

/* ─────────────────────────── THE SALVAGE CRATE, OPENED ─────────────────────────── */

const OPEN_SHAPE = Object.freeze({ shape: "crate-open-shape", field: "crate-open-field" });

/**
 * The communal ship as the OPEN reply publishes it.
 *
 * It is the same aggregate `/panel` serves — Lean spells both with one function —
 * so the gauges are parsed by the same `parseGauge`, arithmetic re-derived and
 * all. A node whose open reply clipped a needle differently from its panel read
 * is refused here rather than shown twice.
 */
function parseOpenPanel(value) {
  exactKeys(value, OPEN_PANEL_KEYS, "crate open panel", OPEN_SHAPE);
  const gauges = boundedArray(value.gauges, "crate open gauges", "crate-open-gauge", MAX_GAUGES);
  return Object.freeze({
    gauges: Object.freeze(gauges.map(parseGauge)),
    recoveredKinds: natural(value.recovered_kinds, "crate open recovered kinds", "crate-open-count"),
    observed: natural(value.observed, "crate open observed", "crate-open-count"),
    admitted: natural(value.admitted, "crate open admitted", "crate-open-count"),
  });
}

/**
 * The Lean-emitted open document, checked field by field.
 *
 * ⚠ LEAN'S OWN LAW IS RE-DERIVED HERE, not believed. `Verdict` is a SUM, so a
 * document cannot be both refused and carrying a panel — but that is a fact
 * about the Lean type, and what arrives here is JSON from a node. So:
 *
 *   * `opened: false` MUST carry a tag and MUST carry no entry and no panel
 *     (`a_refused_open_publishes_no_gauge_and_no_entry`);
 *   * `opened: true` MUST carry an entry, a panel and a period, and no tag.
 *
 * A document that violates either is REFUSED. It is not rendered with the parts
 * that did arrive, because a refusal carrying a panel and a move carrying none
 * are exactly the two readings a player must never be shown interchangeably.
 */
export function parseCrateOpenDocument(value) {
  exactKeys(value, OPEN_DOCUMENT_KEYS, "crate open document", OPEN_SHAPE);
  refuse(value.format === CRATE_OPEN_DOCUMENT_FORMAT, "crate-open-format",
    `unsupported crate open document format: ${value.format}`);
  const opened = bool(value.opened, "crate open verdict", "crate-open-verdict");

  if (!opened) {
    const refusal = text(value.refusal, "crate open refusal tag", "crate-open-verdict", 64);
    refuse(Object.hasOwn(CRATE_REFUSALS, refusal), "crate-open-verdict",
      `the crate refused with a tag this client has never been taught: ${refusal}`);
    refuse(value.entry === null && value.panel === null, "crate-open-verdict",
      "a refused opening carries a drawn row or a moved ship; Lean proves it carries neither, so this node's document is not one this page will render");
    return Object.freeze({
      opened: false,
      federationId: digest32(value.federation_id, "crate open federation id", "crate-open-identity"),
      contentSession: digest32(value.content_session, "crate open content session", "crate-open-identity"),
      contentEpoch: natural(value.content_epoch, "crate open content epoch", "crate-open-identity"),
      opener: digest32(value.opener, "crate open opener", "crate-open-identity"),
      // `null` exactly when the log did not replay, in which case there is no
      // crate state to read a period off and none is invented.
      period: value.period === null ? null : natural(value.period, "crate open period", "crate-open-period"),
      refusal,
      reason: CRATE_REFUSALS[refusal],
      entry: null,
      panel: null,
    });
  }

  refuse(value.refusal === null, "crate-open-verdict",
    "an accepted opening carries a refusal tag; this document claims both at once");
  refuse(value.entry !== null && value.panel !== null, "crate-open-verdict",
    "an accepted opening carries no drawn row or no moved ship");
  refuse(value.period !== null, "crate-open-verdict",
    "an accepted opening reports no period; the crate decides one on every acceptance");
  return Object.freeze({
    opened: true,
    federationId: digest32(value.federation_id, "crate open federation id", "crate-open-identity"),
    contentSession: digest32(value.content_session, "crate open content session", "crate-open-identity"),
    contentEpoch: natural(value.content_epoch, "crate open content epoch", "crate-open-identity"),
    opener: digest32(value.opener, "crate open opener", "crate-open-identity"),
    period: natural(value.period, "crate open period", "crate-open-period"),
    refusal: null,
    reason: null,
    entry: parseEntry(value.entry, "crate open entry"),
    panel: parseOpenPanel(value.panel),
  });
}

/** The serving envelope of the crate-open write. */
export function parseCrateOpenView(value, authorityId) {
  exactKeys(value, OPEN_ENVELOPE_KEYS, "crate open publication", OPEN_SHAPE);
  refuse(value.format === CRATE_OPEN_VIEW_FORMAT, "crate-open-format",
    `unsupported crate open publication format: ${value.format}`);
  digest32(value.authority_id, "crate open authority id", "crate-open-authority");
  refuse(value.authority_id === authorityId, "crate-open-authority",
    "crate open publication is for another authority");
  const document = parseCrateOpenDocument(value.crate_open);
  const logAppended = bool(value.log_appended, "crate open log append flag", "crate-open-verdict");
  // The node appends ONLY on an accepted open, and a failed append fails the
  // request. So an acceptance that did not stick is a document this page will
  // not render as a move: the row that defends the next replay is not there.
  refuse(logAppended === document.opened, "crate-open-verdict",
    "the node's append flag disagrees with the crate's verdict; an opening that was not logged is not in effect");
  return Object.freeze({
    authorityId: value.authority_id,
    contentProvenance: text(value.content_provenance, "crate open provenance", "crate-open-claim"),
    writePath: text(value.write_path, "crate open write-path claim", "crate-open-claim"),
    // ⚠ RENDERED VERBATIM, never paraphrased. This is the node's own sentence
    // about the crate being at the installed period and one crew key opening it
    // exactly once until a finality adapter lands. A paraphrase here would be
    // this page making a claim about `SalvageCrate.advancePeriod`.
    finalityGap: text(value.finality_gap, "crate open finality gap", "crate-open-claim"),
    consensusFinality: text(value.consensus_finality, "crate open finality claim", "crate-open-claim"),
    logRowsReplayed: natural(value.log_rows_replayed, "crate open replayed rows", "crate-open-count"),
    logAppended,
    document,
  });
}

/**
 * OPEN THE SALVAGE CRATE.
 *
 * ⚠ THE BODY IS ONE CREW KEY AND NOTHING ELSE. Not a seed, beacon, date, ticket,
 * entry, contribution, counter, sequence, period or panel state — Lean derives
 * every one of those from authored content and from positions in the node's own
 * durable log. The browser authors IDENTITY AND INTENT; it never publishes an
 * answer.
 *
 * Never throws: every failure is a STATE, exactly as `loadStationState` is. The
 * route is authenticated, so a terminal with no session lands as `unreachable`
 * with the node's own refusal word rather than as a thrown error.
 */
export async function openSalvageCrate({ authorityId, opener, baseUrl, fetchImpl = globalThis.fetch, prefix = "/node" } = {}) {
  if (typeof authorityId !== "string" || !/^[0-9a-f]{64}$/.test(authorityId)) {
    return Object.freeze({ state: "unreachable", code: "crate-open-authority", reason: "This terminal has no authority id to open a crate at" });
  }
  if (typeof opener !== "string" || !/^[0-9a-f]{64}$/.test(opener)) {
    return Object.freeze({ state: "unreachable", code: "crate-open-opener", reason: "This terminal binds no crew key to open the crate with" });
  }
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "crate-open-fetch", reason: "No fetch is available in this environment" });
  }
  const url = new URL(
    `${prefix}${CRATE_OPEN_ROUTE.replace("{authority}", authorityId)}`,
    baseUrl ?? globalThis.location?.href ?? "https://invalid.local/",
  );
  let body;
  let ok;
  let status;
  try {
    const response = await fetchImpl(url, {
      method: "POST",
      cache: "no-store",
      credentials: "same-origin",
      headers: { "content-type": "application/json" },
      // The whole request. `deny_unknown_fields` on the node's side refuses any
      // second key, so a page that grew one would be told rather than ignored.
      body: JSON.stringify({ opener }),
    });
    ok = Boolean(response?.ok);
    status = response?.status ?? null;
    body = JSON.parse(await response.text());
  } catch {
    return Object.freeze({ state: "unreachable", code: "crate-open-fetch", reason: "Nothing answered this opening at this address" });
  }
  if (!ok) {
    const refused = typeof body?.refused === "string" ? body.refused : null;
    return Object.freeze({
      state: "unreachable",
      code: refused ?? "crate-open-status",
      reason: refused
        ? `The authority refused this opening (${refused})`
        : `The authority answered HTTP ${status ?? "nothing"}`,
    });
  }
  try {
    const view = parseCrateOpenView(body, authorityId);
    // ⚠ TWO OUTCOMES, KEPT APART. `opened` is a move; `declined` is the CRATE
    // saying no, which is an ordinary answer and not a fault. Neither is
    // `refused`, which is this page declining the document itself.
    return Object.freeze({ state: view.document.opened ? "opened" : "declined", view });
  } catch (error) {
    return Object.freeze({ state: "refused", code: error?.code ?? "crate-open-shape", reason: error?.message ?? "the crate open publication was refused" });
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
      standing: "Asking the station for the panel it serves.",
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
      headline: refused ? "The panel did not check out" : "No station answered",
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
    // ⚠ The standing copy used to say "No crate opening has ever been accepted
    // here — the opening demands a capability no Lean term in the tree builds".
    // That was true when it was written and is false now: the crate opens. The
    // honest reading of zeros is that the node's open log is EMPTY, and the
    // served `log_rows_folded` is what says so.
    standing: still
      ? `This is the station exactly as installed. Every dial below is a fold of this node's durable open log, and the log is empty: ${doc.gauges.length === 1 ? "the dial reads" : "the dials read"} zero because nobody has opened the salvage crate here, not because opening is impossible. A crew member on the curator's roster can open it.`
      : `The dials below are the fold of ${view.logRowsFolded} opening${view.logRowsFolded === 1 ? "" : "s"} recorded in this node's durable log, replayed through the crate itself. Every figure is what the station served; none of it has been settled by a quorum.`,
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
        "Openings folded",
        `${view.logRowsFolded} row${view.logRowsFolded === 1 ? "" : "s"} of this node's durable open log`,
      ]),
      Object.freeze([
        "Your rotation",
        doc.crew === null
          ? "not requested — the communal panel names no crew member, and this terminal binds no crew key to ask the crew route with"
          : `${doc.crew.rotation.length} period${doc.crew.rotation.length === 1 ? "" : "s"} written for ${short(doc.crew.key)}; ${doc.crew.eligible ? "on the crew list" : "not on the crew list"}`,
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

/**
 * THE ONE ACTION: open the salvage crate.
 *
 * ⚠ WHAT IS DELIBERATELY ABSENT. No streak, no countdown, no attendance, no
 * "next crate in…", no per-player history. None of those states exist —
 * `ShipInstrumentPanel.State` has no per-player field at all and nothing
 * advances the crate's period — so simulating any of them client-side would be
 * this page inventing a game the node is not playing.
 *
 * `crew` is `{ key, eligible }` when this terminal has bound a crew identity and
 * read its eligibility off the wire, or `null` when it has not. Eligibility is
 * never DECIDED here: `eligible: false` came from the curator's authored roster
 * through `StationDailyRuntime.crewWireOver`, and an unknown eligibility leaves
 * the control enabled so the node — not this page — gets to answer.
 *
 * An ineligible or unbound crew member is DISABLED, with the reason said plainly.
 * They are not scolded, and no needle is drawn for them.
 */
export function buildCrateOpenAction({ crew = null, open = null } = {}) {
  const label = "Open the Salvage Crate";
  const base = { id: "crate-open", eyebrow: "SALVAGE CRATE // ONE KEY, ONE OPENING", label, gauges: Object.freeze([]), prize: null, finalityGap: null };

  if (open && open.state === "pending") {
    return Object.freeze({ ...base, state: "working", enabled: false, headline: "Opening the crate", standing: "The station is replaying its log of openings and asking the crate." });
  }

  if (open && (open.state === "opened" || open.state === "declined")) {
    const { view } = open;
    const doc = view.document;
    if (!doc.opened) {
      // ⚠ A REFUSAL, AND NOT A ZERO-MOVE. `entry` and `panel` are null, so there
      // is nothing to draw and nothing is drawn — no gauge, no prize, no needle.
      return Object.freeze({
        ...base,
        state: "declined",
        enabled: false,
        headline: "The crate did not open",
        standing: `${doc.reason} Nothing was drawn and the communal ship is unchanged — a refusal carries no gauge and no entry, so no reading below has moved.`,
        refusal: doc.refusal,
        finalityGap: view.finalityGap,
      });
    }
    return Object.freeze({
      ...base,
      state: "opened",
      enabled: false,
      headline: `You drew ${doc.entry.prize}`,
      standing: `The crate opened at period ${doc.period} and the communal ship moved. Your draw contributed ${doc.entry.supplies} suppl${doc.entry.supplies === 1 ? "y" : "ies"}; the dials below are the whole crew's, not yours.`,
      prize: Object.freeze({ id: doc.entry.id, prize: doc.entry.prize, supplies: doc.entry.supplies }),
      // ⚠ BOTH FIGURES, ALWAYS. `exact_total` is the unclipped arithmetic and
      // `shown` is the needle; publishing only the needle would let the display
      // scale quietly become the bound.
      gauges: Object.freeze(doc.panel.gauges.map((gauge) => Object.freeze({
        id: gauge.gauge,
        label: meterLabel(gauge.meter),
        reading: `${gauge.shown} of ${gauge.fullAt}`,
        exactTotal: gauge.exactTotal,
        shown: gauge.shown,
        fullAt: gauge.fullAt,
        atFull: gauge.atFull,
        exact: gauge.exactTotal === gauge.shown
          ? `exact total ${gauge.exactTotal}, which the needle shows`
          : `exact total ${gauge.exactTotal}, past the ${gauge.fullAt} mark the needle stops at`,
      }))),
      counts: Object.freeze([
        Object.freeze(["Salvage kinds recovered", String(doc.panel.recoveredKinds)]),
        Object.freeze(["Openings observed", String(doc.panel.observed)]),
        Object.freeze(["Openings admitted", String(doc.panel.admitted)]),
      ]),
      finalityGap: view.finalityGap,
    });
  }

  if (open && open.state !== "idle") {
    const refused = open.state === "refused";
    return Object.freeze({
      ...base,
      state: refused ? "refused" : "sealed",
      enabled: false,
      headline: refused ? "The opening was refused" : "Nobody answered",
      standing: refused
        ? `An opening was published and this terminal would not accept it (${open.code}): ${open.reason}. No prize and no gauge is shown, because none was read.`
        : `${open.reason} (${open.code}). Nothing was opened and nothing is claimed.`,
    });
  }

  if (!crew || typeof crew.key !== "string") {
    return Object.freeze({
      ...base,
      state: "unavailable",
      enabled: false,
      headline: "No crew key is bound here",
      standing: "Opening the crate is something you have to be allowed to do, and the crew list the curator signed is what allows it — so it needs a crew key. This terminal holds none, and it will not invent one.",
    });
  }
  if (crew.eligible === false) {
    return Object.freeze({
      ...base,
      state: "unavailable",
      enabled: false,
      headline: "This crew key is not on the roster",
      standing: `${short(crew.key)} is not on the crew list the curator signed for this crate, so the crate will not open for it. That is the list, not a penalty.`,
    });
  }
  return Object.freeze({
    ...base,
    state: "ready",
    enabled: true,
    headline: "The salvage crate is unopened for this key",
    standing: `Opening it sends one thing: the crew key ${short(crew.key)}. Which period it is, what you draw, what it contributes and where every needle lands are all decided by the station, out of the curator\u2019s signed content and its own log.`,
  });
}

export function mountCrateOpenAction(root, action) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a crate open root is required");
  root.dataset.state = action.state;
  const nodes = [
    element("p", "panel-label", action.eyebrow),
    element("h3", "crate-open__headline", action.headline),
    element("p", "crate-open__standing", action.standing),
  ];
  const button = element("button", "crate-open__button", action.label);
  button.type = "button";
  button.disabled = !action.enabled;
  nodes.push(button);

  if (action.prize) {
    nodes.push(factList([
      ["Drawn", action.prize.prize],
      ["Contributed", `${action.prize.supplies} to supplies`],
    ], "station-panel__counts crate-open__prize"));
  }
  if (action.gauges.length > 0) {
    const dials = element("div", "station-panel__gauges crate-open__gauges");
    for (const gauge of action.gauges) {
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
  if (action.counts) nodes.push(factList(action.counts, "station-panel__counts crate-open__counts"));
  // ⚠ VERBATIM. The node's own sentence about the installed period and one open
  // per crew key, rendered rather than paraphrased.
  if (action.finalityGap) nodes.push(element("p", "crate-open__finality", action.finalityGap));

  root.replaceChildren(...nodes);
  return root;
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

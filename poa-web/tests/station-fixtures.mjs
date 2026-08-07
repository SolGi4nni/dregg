/**
 * A specimen of the station document THIS DEPLOYMENT actually serves.
 *
 * Not an invention: every figure below is the one Lean emits for the installed
 * station, and `station-panel.test.mjs` pins the load-bearing ones against
 * `StationDailyRuntime.lean` / `SalvageCrateExamples.lean` rather than against
 * itself. The point is that the copy this page renders — "periods 31 through
 * 35", "4 loot rows", one dial reading zero of 64 — is the copy a player sees,
 * not a shape that merely parses.
 *
 * ⚠ IF THE CURATOR RE-AUTHORS THE CRATE this fixture goes stale and the pin
 * reds. RE-DERIVE it from the new Lean values. Do not delete the pin: a fixture
 * that no longer resembles the deployment is how a hostile test quietly stops
 * being about anything.
 */

const hex = (byte) => byte.toString(16).padStart(2, "0").repeat(32);

export const STATION_AUTHORITY = hex(0x2b);

/**
 * The station over an EMPTY open log: one dial, zero, nothing observed or admitted.
 *
 * ⚠ This used to cite `the_served_ship_has_not_been_moved`, which is RETIRED —
 * it asserted these zeros were unmovable, was advertised as "the assertion that
 * goes RED the day a judged opening can be folded in", and did not go red when
 * that day came, because it was about the request type rather than about
 * reachability. The zeros are now the fold of a log with no rows in it, and
 * `the_served_ship_moves_when_the_log_records_an_opening` is the pair that
 * actually fires. `MOVED_STATION_DOCUMENT` below is its second half.
 */
export const INSTALLED_STATION_DOCUMENT = Object.freeze({
  format: "POA-STATION-DAILY-OUT-1",
  federation_id: STATION_AUTHORITY,
  content_session: hex(0x16),
  content_epoch: 1,
  gauges: [{ gauge: 1, meter: "supplies", exact_total: 0, full_at: 64, shown: 0, at_full: false }],
  recovered_kinds: 0,
  observed: 0,
  admitted: 0,
  opens_at: 31,
  closes_at: 35,
  table_rows: 4,
  ticket_count: 14,
  crew: null,
});

/**
 * The station after ONE accepted opening — the ship crew 41's draw moved.
 *
 * Every figure is one Lean serves for the one-row log
 * (`the_served_ship_moves_when_the_log_records_an_opening`, second half) and one
 * the node served over HTTP in
 * `node/tests/poa_station_panel_serves_the_opened_ship.rs`. It is here so the
 * page's MOVED copy is exercised against the reading a player actually gets,
 * rather than against an invented non-zero.
 */
export const MOVED_STATION_DOCUMENT = Object.freeze({
  ...structuredClone(INSTALLED_STATION_DOCUMENT),
  gauges: [{ gauge: 1, meter: "supplies", exact_total: 1, full_at: 64, shown: 1, at_full: false }],
  recovered_kinds: 1,
  observed: 1,
  admitted: 1,
});

/** The exact `POA-CRATE-OPEN-OUT-1` document the node served for crew 41's accepted open. */
export const OPENER_KEY = hex(0x29);
export const STOWAWAY_KEY = hex(0x4d);

export const ACCEPTED_OPEN_DOCUMENT = Object.freeze({
  format: "POA-CRATE-OPEN-OUT-1",
  federation_id: STATION_AUTHORITY,
  content_session: hex(0x16),
  content_epoch: 1,
  opener: OPENER_KEY,
  period: 31,
  opened: true,
  refusal: null,
  entry: { id: 13, prize: "communal-salvage:55", supplies: 1 },
  panel: {
    gauges: [{ gauge: 1, meter: "supplies", exact_total: 1, full_at: 64, shown: 1, at_full: false }],
    recovered_kinds: 1,
    observed: 1,
    admitted: 1,
  },
});

/** ⚠ A refusal: a tag, and NO entry and NO panel. Lean proves it carries neither. */
export const REFUSED_OPEN_DOCUMENT = Object.freeze({
  ...structuredClone(ACCEPTED_OPEN_DOCUMENT),
  opened: false,
  refusal: "already-opened-this-period",
  entry: null,
  panel: null,
});

export const CRATE_FINALITY_GAP =
  "the crate is at the INSTALLED period (the first authored beacon) and stays there: " +
  "SalvageCrate.advancePeriod is capability-gated and no finality adapter calls it, so a " +
  "genesis-rooted replay never advances currentPeriod. One crew key therefore opens the crate " +
  "exactly ONCE. The period is never taken from the request — the wire has no field for it";

export function crateOpenEnvelope(overrides = {}, documentOverrides = null) {
  return {
    format: "POA-CRATE-OPEN-VIEW-1",
    authority_id: STATION_AUTHORITY,
    content_provenance: "lean-authored station content",
    write_path: "write: `crate_open` is the exact POA-CRATE-OPEN-OUT-1 document native Lean emitted",
    finality_gap: CRATE_FINALITY_GAP,
    crate_open: documentOverrides ?? structuredClone(ACCEPTED_OPEN_DOCUMENT),
    log_rows_replayed: 0,
    log_appended: true,
    consensus_finality: "the open is recorded in this node's durable open log; it is not a consensus turn",
    ...overrides,
  };
}

/** The envelope for a crate that DECLINED: nothing was appended. */
export function declinedOpenEnvelope(overrides = {}) {
  return crateOpenEnvelope({
    crate_open: structuredClone(REFUSED_OPEN_DOCUMENT),
    log_rows_replayed: 1,
    log_appended: false,
    ...overrides,
  });
}

export const STATION_PROVENANCE =
  "lean-authored station content (SalvageCrateExamples.config + StationDailyRuntime.stationPanel); " +
  "no station genesis ceremony exists, so the federation_id inside the document is the AUTHORED one " +
  "and need not equal authority_id";

/**
 * ⚠ REWRITTEN. This used to be the node's "no judged opening exists … declared
 * opaque with no producer anywhere" claim, which the node no longer serves
 * because it is false. The served claim now says the gauges ARE the fold of the
 * durable open log.
 */
export const STATION_WRITE_PATH =
  "read-only projection of the node's DURABLE OPEN LOG: every gauge is the fold of that log " +
  "through SalvageCrate.openCrate itself, replayed from genesis. Zeros therefore mean the log is " +
  "EMPTY — nobody has opened the crate on this node — and not that openings are impossible. " +
  "There is still NO CURRENT-PERIOD POINTER on this document: `rotation` is the whole authored " +
  "schedule rather than one day of it";

export function stationEnvelope(overrides = {}) {
  return {
    format: "POA-STATION-VIEW-1",
    authority_id: STATION_AUTHORITY,
    content_provenance: STATION_PROVENANCE,
    write_path: STATION_WRITE_PATH,
    station: structuredClone(INSTALLED_STATION_DOCUMENT),
    log_rows_folded: 0,
    consensus_finality: "the station panel is a projection of installed content on this node; no quorum-finality claim is made",
    ...overrides,
  };
}

/**
 * The state `loadStationState` returns.
 *
 * `logRowsFolded` defaults to the number of rows that could have produced these
 * figures — 0 for the installed ship, `admitted` otherwise — so a fixture cannot
 * accidentally claim an unmoved ship folded rows or a moved one folded none.
 */
export function readyStation(overrides = {}) {
  const document = structuredClone(INSTALLED_STATION_DOCUMENT);
  Object.assign(document, overrides);
  return {
    state: "ready",
    view: {
      authorityId: STATION_AUTHORITY,
      contentProvenance: STATION_PROVENANCE,
      writePath: STATION_WRITE_PATH,
      consensusFinality: "no quorum-finality claim is made",
      logRowsFolded: document.admitted,
      authoredHere: document.federation_id === STATION_AUTHORITY,
      station: {
        federationId: document.federation_id,
        contentSession: document.content_session,
        contentEpoch: document.content_epoch,
        gauges: document.gauges.map((gauge) => ({
          gauge: gauge.gauge,
          meter: gauge.meter,
          exactTotal: gauge.exact_total,
          fullAt: gauge.full_at,
          shown: gauge.shown,
          atFull: gauge.at_full,
        })),
        recoveredKinds: document.recovered_kinds,
        observed: document.observed,
        admitted: document.admitted,
        opensAt: document.opens_at,
        closesAt: document.closes_at,
        tableRows: document.table_rows,
        ticketCount: document.ticket_count,
        crew: document.crew,
      },
    },
  };
}

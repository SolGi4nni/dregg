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

/** `the_served_ship_has_not_been_moved`: one dial, zero, nothing observed or admitted. */
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

export const STATION_PROVENANCE =
  "lean-authored station content (SalvageCrateExamples.config + StationDailyRuntime.stationPanel); " +
  "no station genesis ceremony exists, so the federation_id inside the document is the AUTHORED one " +
  "and need not equal authority_id";

export const STATION_WRITE_PATH =
  "read-only: no judged opening exists, so every gauge reads its installed value. " +
  "SalvageCrate.openCrate requires a CurrentStateCapability, declared opaque with no producer anywhere, " +
  "so this is a type-level absence and not an unwired route. For the same reason there is no " +
  "SalvageCrate.State and therefore NO CURRENT-PERIOD POINTER: 'what does the crate hold today' is not " +
  "answerable here, and `rotation` is the whole authored schedule rather than one day of it";

export function stationEnvelope(overrides = {}) {
  return {
    format: "POA-STATION-VIEW-1",
    authority_id: STATION_AUTHORITY,
    content_provenance: STATION_PROVENANCE,
    write_path: STATION_WRITE_PATH,
    station: structuredClone(INSTALLED_STATION_DOCUMENT),
    consensus_finality: "the station panel is a projection of installed content on this node; no quorum-finality claim is made",
    ...overrides,
  };
}

/** The state `loadStationState` returns for the installed station. */
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

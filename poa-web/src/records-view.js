import { boundedArray, bool, digest32, exactKeys, natural, refuse, text } from "./wire-shape.js";

/**
 * FIELD RECORDS — where a finished run lands, read from the node that would
 * hold it.
 *
 * `GET /api/poa/records/{authority}` serves a `POA-RECORDS-VIEW-1` envelope
 * around the exact `POA-RECORDS-OUT-2` bytes native Lean emitted
 * (`Dregg2.Games.PathOfAngels.RecordsRuntime`), plus a replay verdict the node
 * actually ran. This module parses both and builds a render model.
 *
 * ⚠ AT ZERO RUNS THIS PAGE IS NOT EMPTY, and the empty-state string it replaces
 * was wrong about that. The page used to render a hand-written "no expedition
 * artifact has been settled" card and never called the route at all. But the
 * route is honest before any turn settles: with zero transitions it carries the
 * exact world identity, the world meters, the Canon revision and the playable
 * mission the genesis ceremony installed, with `stage: "awaiting-first-run"` and
 * `runs: []`. THAT IS THE CONTENT. It gets rendered as content — not apologised
 * for, not hidden behind a placeholder that says the same thing less truthfully.
 *
 * ⚠ AND THE REPLAY VERDICT IS CHECKED AGAINST A SECOND ROUTE, not restated. The
 * records read replays the durable history and reports the head it REBUILT;
 * `/api/poa/signal/{authority}/status` publishes the head the node SERVES. Those
 * are two independently computed answers to one question, so this page asks both
 * and says whether they agree. A pin against its own definition is decoration;
 * two sources that must agree is a gate, and this one can go red.
 *
 * What this module never does: score a run, decide a Canon status, or infer that
 * a record is private because a request succeeded. `PublicMissionWire` is
 * seedless BY TYPE — Lean's `publicMission_ignores_the_run_seed` proves
 * substituting any seed leaves the published value unchanged — so nothing here
 * needs to filter a secret out, and nothing here should behave as though it did.
 */

export const RECORDS_ROUTE = "/api/poa/records/{authority}";
export const SIGNAL_STATUS_ROUTE = "/api/poa/signal/{authority}/status";
export const RECORDS_VIEW_FORMAT = "POA-RECORDS-VIEW-1";
export const RECORDS_DOCUMENT_FORMAT = "POA-RECORDS-OUT-2";
export const SIGNAL_STATUS_FORMAT = "POA-SIGNAL-STATUS-1";

/**
 * The exact key sets, EXPORTED so the gate can hold them against the Lean
 * encoders and the Rust structs that emit them.
 *
 * Exported rather than restated in a test, because a test carrying its own copy
 * would be a third spelling and the failure mode of three spellings is that two
 * get updated. `tests/records-view.test.mjs` compares THESE against
 * `RecordsRuntime.lean` and `poa_records_api.rs`.
 */
export const RECORDS_KEY_SETS = Object.freeze({
  envelope: Object.freeze(["format", "authority_id", "federation_id", "installed", "replay", "records", "consensus_finality"]),
  replay: Object.freeze(["transitions_replayed", "retained_genesis_digest", "rebuilt_head_digest"]),
  document: Object.freeze([
    "format", "federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch", "curator_key", "stage", "mission", "reward", "world",
    "canon_revision", "catalog", "runs", "archive_entries", "locker_entries",
    "attendant_notices", "editorial_inbox", "consumed_runs", "players",
  ]),
  mission: Object.freeze([
    "mission_id", "artifact", "epoch", "federation_id", "content_root",
    "activation_digest", "content_session", "budget", "allowed_relics", "privacy", "ballot",
  ]),
  artifact: Object.freeze(["mission_id", "artifact_id", "source_digest", "content_digest"]),
  budget: Object.freeze(["intel", "supplies", "cohesion", "influence", "score", "relics"]),
  contribution: Object.freeze(["intel", "supplies", "cohesion", "influence", "score", "relics"]),
  world: Object.freeze(["intel", "supplies", "cohesion", "influence", "score", "discovered_relics", "beta_artifacts", "sequence"]),
  catalog: Object.freeze(["artifact", "status"]),
  run: Object.freeze(["status", "chain", "origin_key", "artifact", "contribution", "world_sequence"]),
  chain: Object.freeze(["commit_ordinal", "turn_hash", "receipt_hash", "signer", "actor_root"]),
  origin: Object.freeze(["federation_id", "content_session", "content_epoch", "player_key", "player_counter"]),
  statusEnvelope: Object.freeze(["format", "authority_id", "federation_id", "installed", "head", "consensus_finality"]),
  head: Object.freeze(["head_digest", "deployment_digest", "transition_count", "world_sequence", "canon_revision", "last_transition_digest"]),
});

const { envelope: ENVELOPE_KEYS, replay: REPLAY_KEYS, document: DOCUMENT_KEYS,
  mission: MISSION_KEYS, artifact: ARTIFACT_KEYS, budget: BUDGET_KEYS,
  contribution: CONTRIBUTION_KEYS, world: WORLD_KEYS, catalog: CATALOG_KEYS,
  run: RUN_KEYS, chain: CHAIN_KEYS, origin: ORIGIN_KEYS,
  statusEnvelope: STATUS_ENVELOPE_KEYS, head: HEAD_KEYS } = RECORDS_KEY_SETS;

/** `RunStatus.tag` — the exact five rungs, and no sixth. */
const RUN_STAGES = Object.freeze(["practice", "submitted", "judged", "finalized", "refused"]);
/** `WorldStage.tag` — the exact two. */
const WORLD_STAGES = Object.freeze(["awaiting-first-run", "active"]);

const MAX_CATALOG = 256;
const MAX_RUNS = 256;
const MAX_RELICS = 256;
const METERS = Object.freeze(["intel", "supplies", "cohesion", "influence", "score"]);

const SHAPE = Object.freeze({ shape: "records-shape", field: "records-field" });

function relicList(value, at) {
  const relics = boundedArray(value, at, "records-relics", MAX_RELICS);
  return Object.freeze(relics.map((relic, index) => natural(relic, `${at}[${index}]`, "records-relics")));
}

function meterBundle(value, keys, at) {
  exactKeys(value, keys, at, SHAPE);
  return Object.fromEntries(METERS.map((meter) => [meter, natural(value[meter], `${at} ${meter}`, "records-meter")]));
}

function parseArtifact(value, at) {
  exactKeys(value, ARTIFACT_KEYS, at, SHAPE);
  return Object.freeze({
    missionId: natural(value.mission_id, `${at} mission id`, "records-artifact"),
    artifactId: natural(value.artifact_id, `${at} artifact id`, "records-artifact"),
    sourceDigest: digest32(value.source_digest, `${at} source digest`, "records-artifact"),
    contentDigest: digest32(value.content_digest, `${at} content digest`, "records-artifact"),
  });
}

function parseBudget(value) {
  const meters = meterBundle(value, BUDGET_KEYS, "records mission budget");
  return Object.freeze({ ...meters, relics: natural(value.relics, "records mission budget relics", "records-meter") });
}

function parseContribution(value, at) {
  const meters = meterBundle(value, CONTRIBUTION_KEYS, at);
  return Object.freeze({ ...meters, relics: relicList(value.relics, `${at} relics`) });
}

function parseWorld(value) {
  const meters = meterBundle(value, WORLD_KEYS, "records world");
  const artifacts = boundedArray(value.beta_artifacts, "records world beta artifacts", "records-artifact", MAX_CATALOG);
  return Object.freeze({
    ...meters,
    discoveredRelics: relicList(value.discovered_relics, "records world discovered relics"),
    betaArtifacts: Object.freeze(artifacts.map((entry, index) => parseArtifact(entry, `records world beta artifact ${index}`))),
    sequence: natural(value.sequence, "records world sequence", "records-world"),
  });
}

function parseMission(value) {
  exactKeys(value, MISSION_KEYS, "records mission", SHAPE);
  return Object.freeze({
    missionId: natural(value.mission_id, "records mission id", "records-mission"),
    artifact: parseArtifact(value.artifact, "records mission artifact"),
    epoch: natural(value.epoch, "records mission epoch", "records-mission"),
    federationId: digest32(value.federation_id, "records mission federation id", "records-mission"),
    contentRoot: digest32(value.content_root, "records mission content root", "records-mission"),
    activationDigest: digest32(value.activation_digest, "records mission activation digest", "records-mission"),
    contentSession: digest32(value.content_session, "records mission content session", "records-mission"),
    budget: parseBudget(value.budget),
    allowedRelics: relicList(value.allowed_relics, "records mission allowed relics"),
    privacy: text(value.privacy, "records mission privacy grade", "records-mission", 64),
    ballot: text(value.ballot, "records mission ballot regime", "records-mission", 64),
  });
}

function parseChain(value, at) {
  if (value === null) return null;
  exactKeys(value, CHAIN_KEYS, at, SHAPE);
  return Object.freeze({
    commitOrdinal: natural(value.commit_ordinal, `${at} commit ordinal`, "records-chain"),
    turnHash: digest32(value.turn_hash, `${at} turn hash`, "records-chain"),
    receiptHash: digest32(value.receipt_hash, `${at} receipt hash`, "records-chain"),
    signer: digest32(value.signer, `${at} signer`, "records-chain"),
    actorRoot: digest32(value.actor_root, `${at} actor root`, "records-chain"),
  });
}

function parseOriginKey(value, at) {
  exactKeys(value, ORIGIN_KEYS, at, SHAPE);
  return Object.freeze({
    federationId: digest32(value.federation_id, `${at} federation id`, "records-origin"),
    contentSession: digest32(value.content_session, `${at} content session`, "records-origin"),
    contentEpoch: natural(value.content_epoch, `${at} content epoch`, "records-origin"),
    playerKey: digest32(value.player_key, `${at} player key`, "records-origin"),
    playerCounter: natural(value.player_counter, `${at} player counter`, "records-origin"),
  });
}

/**
 * One landed run.
 *
 * ⚠ The rung/coordinate agreement is RE-DERIVED, not read. Lean's
 * `RunWire.coherentB` says a chain coordinate is exactly the evidence
 * `finalized` claims: anything else carrying one is malformed, and a `finalized`
 * without one is too. A record that arrives incoherent is refused here rather
 * than rendered as a settled run whose chain link happens to be missing.
 */
function parseRun(value, index) {
  const at = `records run ${index}`;
  exactKeys(value, RUN_KEYS, at, SHAPE);
  const status = text(value.status, `${at} status`, "records-run", 32);
  refuse(RUN_STAGES.includes(status), "records-run", `${at} carries a rung this client does not know: ${status}`);
  const chain = parseChain(value.chain, `${at} chain coordinate`);
  refuse(
    (status === "finalized") === (chain !== null),
    "records-run",
    `${at} is ${status} and ${chain === null ? "carries no" : "carries a"} chain coordinate; only a finalized run has one`,
  );
  return Object.freeze({
    status,
    chain,
    originKey: parseOriginKey(value.origin_key, `${at} origin key`),
    artifact: parseArtifact(value.artifact, `${at} artifact`),
    contribution: parseContribution(value.contribution, `${at} contribution`),
    worldSequence: natural(value.world_sequence, `${at} world sequence`, "records-run"),
  });
}

/** The Lean-emitted records document. */
export function parseRecordsDocument(value) {
  exactKeys(value, DOCUMENT_KEYS, "records document", SHAPE);
  refuse(value.format === RECORDS_DOCUMENT_FORMAT, "records-format", `unsupported records document format: ${value.format}`);
  const stage = text(value.stage, "records world stage", "records-stage", 32);
  refuse(WORLD_STAGES.includes(stage), "records-stage", `records document carries an unknown world stage: ${stage}`);
  const runs = boundedArray(value.runs, "records runs", "records-run", MAX_RUNS);
  const catalog = boundedArray(value.catalog, "records catalog", "records-catalog", MAX_CATALOG);
  const parsedRuns = Object.freeze(runs.map(parseRun));
  // Lean's `stageOf_awaiting_iff_no_runs`: the stage is a READING of the rows, so
  // a document whose stage and rows disagree is one of the two lying.
  refuse(
    (stage === "awaiting-first-run") === (parsedRuns.length === 0),
    "records-stage",
    `records document says ${stage} with ${parsedRuns.length} runs; the stage must be a reading of the rows`,
  );
  return Object.freeze({
    federationId: digest32(value.federation_id, "records federation id", "records-identity"),
    contentRoot: digest32(value.content_root, "records content root", "records-identity"),
    activationDigest: digest32(value.activation_digest, "records activation digest", "records-identity"),
    contentSession: digest32(value.content_session, "records content session", "records-identity"),
    contentEpoch: natural(value.content_epoch, "records content epoch", "records-identity"),
    curatorKey: digest32(value.curator_key, "records curator key", "records-identity"),
    stage,
    mission: parseMission(value.mission),
    reward: parseContribution(value.reward, "records mission reward"),
    world: parseWorld(value.world),
    canonRevision: natural(value.canon_revision, "records canon revision", "records-canon"),
    catalog: Object.freeze(catalog.map((entry, index) => {
      exactKeys(entry, CATALOG_KEYS, `records catalog entry ${index}`, SHAPE);
      return Object.freeze({
        artifact: parseArtifact(entry.artifact, `records catalog entry ${index} artifact`),
        status: text(entry.status, `records catalog entry ${index} status`, "records-catalog", 64),
      });
    })),
    runs: parsedRuns,
    archiveEntries: natural(value.archive_entries, "records archive entries", "records-count"),
    lockerEntries: natural(value.locker_entries, "records locker entries", "records-count"),
    attendantNotices: natural(value.attendant_notices, "records attendant notices", "records-count"),
    editorialInbox: natural(value.editorial_inbox, "records editorial inbox", "records-count"),
    consumedRuns: natural(value.consumed_runs, "records consumed runs", "records-count"),
    players: natural(value.players, "records players", "records-count"),
  });
}

export function parseRecordsView(value, authorityId) {
  exactKeys(value, ENVELOPE_KEYS, "records publication", SHAPE);
  refuse(value.format === RECORDS_VIEW_FORMAT, "records-format", `unsupported records publication format: ${value.format}`);
  digest32(value.authority_id, "records authority id", "records-authority");
  refuse(value.authority_id === authorityId, "records-authority", "records publication is for another authority");
  digest32(value.federation_id, "records federation id", "records-authority");
  bool(value.installed, "records installed flag", "records-shape");
  text(value.consensus_finality, "records finality claim", "records-claim");
  if (!value.installed) {
    // An uninstalled authority has nothing to project, and says so with two
    // nulls rather than an empty document that would render like a real world.
    refuse(value.replay === null && value.records === null, "records-installed",
      "an uninstalled authority must publish no replay and no records");
    return Object.freeze({
      authorityId: value.authority_id,
      federationId: value.federation_id,
      installed: false,
      consensusFinality: value.consensus_finality,
      replay: null,
      records: null,
    });
  }
  refuse(value.replay !== null && value.records !== null, "records-installed",
    "an installed authority must publish both a replay verdict and a records document");
  exactKeys(value.replay, REPLAY_KEYS, "records replay verdict", SHAPE);
  return Object.freeze({
    authorityId: value.authority_id,
    federationId: value.federation_id,
    installed: true,
    consensusFinality: value.consensus_finality,
    replay: Object.freeze({
      transitionsReplayed: natural(value.replay.transitions_replayed, "records transitions replayed", "records-replay"),
      retainedGenesisDigest: digest32(value.replay.retained_genesis_digest, "records retained genesis digest", "records-replay"),
      rebuiltHeadDigest: digest32(value.replay.rebuilt_head_digest, "records rebuilt head digest", "records-replay"),
    }),
    records: parseRecordsDocument(value.records),
  });
}

/** The second, independent answer: the head this node publishes. */
export function parseSignalStatus(value, authorityId) {
  exactKeys(value, STATUS_ENVELOPE_KEYS, "signal status", SHAPE);
  refuse(value.format === SIGNAL_STATUS_FORMAT, "records-format", `unsupported signal status format: ${value.format}`);
  refuse(value.authority_id === authorityId, "records-authority", "signal status is for another authority");
  bool(value.installed, "signal status installed flag", "records-shape");
  if (value.head === null) {
    refuse(!value.installed, "records-status", "an installed authority must publish a head");
    return Object.freeze({ installed: false, head: null });
  }
  exactKeys(value.head, HEAD_KEYS, "signal status head", SHAPE);
  return Object.freeze({
    installed: value.installed,
    head: Object.freeze({
      headDigest: digest32(value.head.head_digest, "signal head digest", "records-status"),
      deploymentDigest: digest32(value.head.deployment_digest, "signal deployment digest", "records-status"),
      transitionCount: natural(value.head.transition_count, "signal transition count", "records-status"),
      worldSequence: natural(value.head.world_sequence, "signal world sequence", "records-status"),
      canonRevision: natural(value.head.canon_revision, "signal canon revision", "records-status"),
      lastTransitionDigest: digest32(value.head.last_transition_digest, "signal last transition digest", "records-status"),
    }),
  });
}

/**
 * Compare the head the records read REBUILT with the head the node SERVES.
 *
 * Three verdicts, and the middle one exists because the two reads are not
 * simultaneous: a turn can genuinely land between them, and calling that a
 * disagreement would be a gate that cries wolf until somebody turns it off.
 *
 *   agreed     — same head digest, same counts. Two computations, one answer.
 *   advanced   — different, and the served head is STRICTLY AHEAD. The node
 *                moved between the two requests; nothing is wrong, and nothing
 *                is claimed either.
 *   disagreed  — different, and the served head is NOT ahead. Two routes over
 *                one durable history cannot both be right. This is red.
 */
export function compareHeads(replay, status) {
  if (!replay || !status?.head) {
    return Object.freeze({ state: "unavailable", detail: "The head the network publishes was not read, so the rebuilt head was compared against nothing." });
  }
  const { head } = status;
  if (head.headDigest === replay.rebuiltHeadDigest && head.transitionCount === replay.transitionsReplayed) {
    return Object.freeze({
      state: "agreed",
      detail: `This read replayed ${replay.transitionsReplayed} transition${replay.transitionsReplayed === 1 ? "" : "s"} and rebuilt head ${replay.rebuiltHeadDigest.slice(0, 12)}…; the network publishes the same head at the same count. Two separate computations, one answer.`,
    });
  }
  if (head.transitionCount > replay.transitionsReplayed) {
    return Object.freeze({
      state: "advanced",
      detail: `The network is at ${head.transitionCount} transition${head.transitionCount === 1 ? "" : "s"} and this replay read ${replay.transitionsReplayed}: the node moved between the two requests. Nothing here disagrees, and nothing here is confirmed.`,
    });
  }
  return Object.freeze({
    state: "disagreed",
    detail: `This replay rebuilt head ${replay.rebuiltHeadDigest.slice(0, 12)}… at ${replay.transitionsReplayed} transitions, and the network publishes ${head.headDigest.slice(0, 12)}… at ${head.transitionCount}. Two reads of one history cannot both be right, and until they agree no figure on this page should be trusted.`,
  });
}

async function readJson(url, fetchImpl) {
  const response = await fetchImpl(url, { cache: "no-store", credentials: "same-origin" });
  return { ok: Boolean(response?.ok), status: response?.status ?? null, body: JSON.parse(await response.text()) };
}

/**
 * Read the records surface, and the head to check it against.
 *
 * Never throws. The cross-check is best-effort by design: a status route this
 * page cannot reach reports `unavailable`, which is not the same as agreement
 * and is not rendered as though it were.
 */
export async function loadRecordsState({ authorityId, baseUrl, fetchImpl = globalThis.fetch, prefix = "/node" } = {}) {
  if (typeof authorityId !== "string" || !/^[0-9a-f]{64}$/.test(authorityId)) {
    return Object.freeze({ state: "unreachable", code: "records-authority", reason: "This terminal has no authority id to ask about" });
  }
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "records-fetch", reason: "No fetch is available in this environment" });
  }
  const base = baseUrl ?? globalThis.location?.href ?? "https://invalid.local/";
  const recordsUrl = new URL(`${prefix}${RECORDS_ROUTE.replace("{authority}", authorityId)}`, base);
  let read;
  try {
    read = await readJson(recordsUrl, fetchImpl);
  } catch {
    return Object.freeze({ state: "unreachable", code: "records-fetch", reason: "No records surface answered on this origin" });
  }
  if (!read.ok) {
    const refused = typeof read.body?.refused === "string" ? read.body.refused : null;
    return Object.freeze({
      state: "unreachable",
      code: refused ?? "records-status",
      reason: refused ? `The records read was refused (${refused})` : `The authority answered HTTP ${read.status ?? "nothing"}`,
    });
  }
  let view;
  try {
    view = parseRecordsView(read.body, authorityId);
  } catch (error) {
    return Object.freeze({ state: "refused", code: error?.code ?? "records-shape", reason: error?.message ?? "the records publication was refused" });
  }
  let status = null;
  try {
    const head = await readJson(new URL(`${prefix}${SIGNAL_STATUS_ROUTE.replace("{authority}", authorityId)}`, base), fetchImpl);
    if (head.ok) status = parseSignalStatus(head.body, authorityId);
  } catch {
    status = null;
  }
  return Object.freeze({ state: "ready", view, crossCheck: compareHeads(view.replay, status) });
}

function short(value) {
  return `${value.slice(0, 12)}…${value.slice(-4)}`;
}

function meterRows(bundle) {
  return METERS.map((meter) => Object.freeze([meter.toUpperCase(), String(bundle[meter])]));
}

/**
 * The render model.
 *
 * The lead is a reading of `stage`, which Lean derives from the rows — so this
 * cannot say "awaiting the first run" over a page of runs, and cannot say a run
 * landed over an empty one.
 */
export function buildRecordsModel(records) {
  if (!records || records.state === "pending") {
    return Object.freeze({
      state: "pending",
      headline: "Reading the field records",
      standing: "Asking the network what has landed.",
      sections: Object.freeze([]),
      runs: Object.freeze([]),
      crossCheck: null,
    });
  }
  if (records.state !== "ready") {
    const refused = records.state === "refused";
    return Object.freeze({
      state: refused ? "refused" : "sealed",
      headline: refused ? "The records did not check out" : "No records answered",
      standing: refused
        ? `A records document was served and this terminal would not accept it (${records.code}): ${records.reason}. Nothing from it is shown, including the parts that parsed.`
        : `${records.reason} (${records.code}). This page holds no local copy of a world, so there is nothing to fall back to and nothing is claimed.`,
      sections: Object.freeze([]),
      runs: Object.freeze([]),
      crossCheck: null,
    });
  }
  const { view } = records;
  if (!view.installed) {
    return Object.freeze({
      state: "uninstalled",
      headline: "No world is installed here",
      standing: `The network answered, and says the Path of Angels founding ceremony has never been run here. There is no world, no mission, and no record to show — not an empty archive, an absent one. ${view.consensusFinality}`,
      sections: Object.freeze([]),
      runs: Object.freeze([]),
      crossCheck: null,
    });
  }

  const doc = view.records;
  const awaiting = doc.stage === "awaiting-first-run";
  return Object.freeze({
    state: "ready",
    stage: doc.stage,
    headline: awaiting
      ? "No run has landed yet"
      : `${doc.runs.length} run${doc.runs.length === 1 ? " has" : "s have"} landed`,
    standing: awaiting
      ? "This is not an empty page. Everything below is the world a run would write into — the identity the genesis ceremony installed, the meters it starts from, the mission that is playable, and the Canon revision a discovery would be promoted against — decoded from the bytes actually on disk and re-judged by the node for this request."
      : "Each record below was re-judged from its exact stored bytes for this request. A chain coordinate appears only on a finalized run; no other rung has one.",
    sections: Object.freeze([
      Object.freeze({
        id: "identity",
        title: "The world a run writes into",
        rows: Object.freeze([
          Object.freeze(["Federation", short(doc.federationId)]),
          Object.freeze(["Content session", short(doc.contentSession)]),
          Object.freeze(["Content root", short(doc.contentRoot)]),
          Object.freeze(["Activation digest", short(doc.activationDigest)]),
          Object.freeze(["Manifest revision", String(doc.contentEpoch)]),
          Object.freeze(["Curator key", short(doc.curatorKey)]),
          Object.freeze(["Stage", doc.stage]),
        ]),
      }),
      Object.freeze({
        id: "world",
        title: "World meters, as installed",
        rows: Object.freeze([
          ...meterRows(doc.world),
          Object.freeze(["World sequence", String(doc.world.sequence)]),
          Object.freeze(["Discovered relics", doc.world.discoveredRelics.length === 0 ? "none" : doc.world.discoveredRelics.join(", ")]),
          Object.freeze(["Beta artifacts", String(doc.world.betaArtifacts.length)]),
        ]),
      }),
      Object.freeze({
        id: "mission",
        title: "The playable mission",
        rows: Object.freeze([
          Object.freeze(["Mission", String(doc.mission.missionId)]),
          Object.freeze(["Artifact", `mission ${doc.mission.artifact.missionId} / artifact ${doc.mission.artifact.artifactId}`]),
          Object.freeze(["Content digest", short(doc.mission.artifact.contentDigest)]),
          Object.freeze(["Epoch", String(doc.mission.epoch)]),
          Object.freeze(["Privacy grade", doc.mission.privacy]),
          Object.freeze(["Ballot regime", doc.mission.ballot]),
          Object.freeze(["Allowed relics", doc.mission.allowedRelics.length === 0 ? "none" : doc.mission.allowedRelics.join(", ")]),
          Object.freeze(["Budget relics", String(doc.mission.budget.relics)]),
        ]),
      }),
      Object.freeze({
        id: "reward",
        title: "What one settled run would contribute",
        rows: Object.freeze([
          ...meterRows(doc.reward),
          Object.freeze(["Relics", doc.reward.relics.length === 0 ? "none" : doc.reward.relics.join(", ")]),
          Object.freeze(["Standing", "an unsettled preview, read off the signed rules: what one settled run would add. Nothing here has settled, so none of it has been added"]),
        ]),
      }),
      Object.freeze({
        id: "canon",
        title: "Canon and intake",
        rows: Object.freeze([
          Object.freeze(["Canon revision", String(doc.canonRevision)]),
          Object.freeze(["Catalog entries", String(doc.catalog.length)]),
          Object.freeze(["Archive entries", String(doc.archiveEntries)]),
          Object.freeze(["Locker entries", String(doc.lockerEntries)]),
          Object.freeze(["Attendant notices", String(doc.attendantNotices)]),
          Object.freeze(["Editorial inbox", String(doc.editorialInbox)]),
          Object.freeze(["Consumed runs", String(doc.consumedRuns)]),
          Object.freeze(["Players", String(doc.players)]),
        ]),
      }),
    ]),
    runs: Object.freeze(doc.runs.map((run, index) => Object.freeze({
      index: index + 1,
      status: run.status,
      worldSequence: run.worldSequence,
      artifact: `mission ${run.artifact.missionId} / artifact ${run.artifact.artifactId}`,
      chain: run.chain === null
        ? "no chain coordinate — only a finalized run carries one"
        : `commit ${run.chain.commitOrdinal}, turn ${short(run.chain.turnHash)}, receipt ${short(run.chain.receiptHash)}`,
      player: short(run.originKey.playerKey),
    }))),
    crossCheck: Object.freeze({
      state: records.crossCheck.state,
      title: Object.freeze({
        agreed: "The rebuilt head matches the one the authority publishes",
        advanced: "The network moved between the two reads",
        disagreed: "THE TWO READS DISAGREE",
        unavailable: "The rebuilt head was not cross-checked",
      })[records.crossCheck.state],
      detail: records.crossCheck.detail,
      genesis: `Retained genesis ${short(view.replay.retainedGenesisDigest)}; replay re-judged ${view.replay.transitionsReplayed} finalized transition${view.replay.transitionsReplayed === 1 ? "" : "s"} through native Lean for this request.`,
      finality: view.consensusFinality,
    }),
  });
}

function element(tag, className, textContent) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (textContent !== undefined) node.textContent = textContent;
  return node;
}

export function mountRecords(root, model) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a records root is required");
  root.dataset.state = model.state;
  const nodes = [
    element("p", "panel-label", "FIELD RECORDS // THIS NETWORK"),
    element("h2", "records-live__headline", model.headline),
    element("p", "records-live__standing", model.standing),
  ];
  for (const section of model.sections) {
    const panel = element("article", "records-section");
    panel.dataset.section = section.id;
    panel.append(element("h3", "records-section__title", section.title));
    const list = element("dl", "records-section__rows");
    for (const [term, detail] of section.rows) {
      const row = element("div");
      row.append(element("dt", "", term), element("dd", "", detail));
      list.append(row);
    }
    panel.append(list);
    nodes.push(panel);
  }
  if (model.state === "ready") {
    const log = element("div", "records-runs");
    log.append(element("h3", "records-section__title", "Landed runs"));
    if (model.runs.length === 0) {
      log.append(element("p", "records-runs__empty", "None. A run lands here when a node finalizes it; nothing on this page can put one here."));
    } else {
      for (const run of model.runs) {
        const row = element("article", "records-run");
        row.dataset.status = run.status;
        row.append(
          element("time", "", `#${run.index} · ${run.status}`),
          element("b", "", run.artifact),
          element("span", "", run.chain),
          element("small", "", `player ${run.player} · world sequence ${run.worldSequence}`),
        );
        log.append(row);
      }
    }
    nodes.push(log);
    const check = element("article", "records-crosscheck");
    check.dataset.crosscheck = model.crossCheck.state;
    check.append(
      element("h3", "records-section__title", model.crossCheck.title),
      element("p", "", model.crossCheck.detail),
      element("small", "", model.crossCheck.genesis),
      element("small", "", model.crossCheck.finality),
    );
    nodes.push(check);
  }
  root.replaceChildren(...nodes);
  return root;
}

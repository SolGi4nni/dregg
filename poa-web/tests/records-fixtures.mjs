/**
 * A `POA-RECORDS-VIEW-1` envelope at `latest_height` 0 — the state this
 * deployment is actually in.
 *
 * `stage: "awaiting-first-run"`, `runs: []`, and a world identity, a meter set,
 * a Canon revision and a playable mission that the genesis ceremony installed.
 * That combination is the whole point of the surface: it is honest BEFORE the
 * first turn settles, so a page at height 0 has something true to render rather
 * than a hand-written apology.
 */

const hex = (byte) => byte.toString(16).padStart(2, "0").repeat(32);

export const RECORDS_AUTHORITY = hex(0x2b);

export const GENESIS_ARTIFACT = Object.freeze({
  mission_id: 1,
  artifact_id: 7,
  source_digest: hex(0x31),
  content_digest: hex(0x32),
});

export function recordsDocument(overrides = {}) {
  return {
    format: "POA-RECORDS-OUT-2",
    federation_id: RECORDS_AUTHORITY,
    content_root: hex(0x11),
    activation_digest: hex(0x12),
    content_session: hex(0x13),
    content_epoch: 1,
    curator_key: hex(0x14),
    stage: "awaiting-first-run",
    mission: {
      mission_id: 1,
      artifact: structuredClone(GENESIS_ARTIFACT),
      epoch: 1,
      federation_id: RECORDS_AUTHORITY,
      content_root: hex(0x11),
      activation_digest: hex(0x12),
      content_session: hex(0x13),
      budget: { intel: 4, supplies: 3, cohesion: 2, influence: 1, score: 10, relics: 1 },
      allowed_relics: [8],
      privacy: "public",
      ballot: "none",
    },
    reward: { intel: 2, supplies: 1, cohesion: 0, influence: 0, score: 5, relics: [8] },
    world: {
      intel: 0, supplies: 0, cohesion: 0, influence: 0, score: 0,
      discovered_relics: [], beta_artifacts: [], sequence: 0,
    },
    canon_revision: 1,
    catalog: [{ artifact: structuredClone(GENESIS_ARTIFACT), status: "beta" }],
    runs: [],
    archive_entries: 0,
    locker_entries: 0,
    attendant_notices: 0,
    editorial_inbox: 0,
    consumed_runs: 0,
    players: 0,
    ...overrides,
  };
}

export const GENESIS_HEAD = hex(0x55);

export function recordsEnvelope(overrides = {}, documentOverrides = {}) {
  return {
    format: "POA-RECORDS-VIEW-1",
    authority_id: RECORDS_AUTHORITY,
    federation_id: RECORDS_AUTHORITY,
    installed: true,
    replay: {
      transitions_replayed: 0,
      retained_genesis_digest: hex(0x54),
      rebuilt_head_digest: GENESIS_HEAD,
    },
    records: recordsDocument(documentOverrides),
    consensus_finality: "records reflect this node's finalized commit history; no quorum-finality claim is made",
    ...overrides,
  };
}

export function signalStatus(overrides = {}, headOverrides = {}) {
  return {
    format: "POA-SIGNAL-STATUS-1",
    authority_id: RECORDS_AUTHORITY,
    federation_id: RECORDS_AUTHORITY,
    installed: true,
    head: {
      head_digest: GENESIS_HEAD,
      deployment_digest: hex(0x56),
      transition_count: 0,
      world_sequence: 0,
      canon_revision: 1,
      last_transition_digest: hex(0x57),
      ...headOverrides,
    },
    consensus_finality: "no quorum-finality claim is made",
    ...overrides,
  };
}

/** One finalized run, for the shape the page holds once something lands. */
export function finalizedRun(overrides = {}) {
  return {
    status: "finalized",
    chain: {
      commit_ordinal: 4,
      turn_hash: hex(0x61),
      receipt_hash: hex(0x62),
      signer: hex(0x63),
      actor_root: hex(0x64),
    },
    origin_key: {
      federation_id: RECORDS_AUTHORITY,
      content_session: hex(0x13),
      content_epoch: 1,
      player_key: hex(0x65),
      player_counter: 1,
    },
    artifact: structuredClone(GENESIS_ARTIFACT),
    contribution: { intel: 2, supplies: 1, cohesion: 0, influence: 0, score: 5, relics: [8] },
    world_sequence: 1,
    ...overrides,
  };
}

const hex = (pair) => pair.repeat(32);

const projection = ({ sequence, players, service }) => ({
  sequence,
  public_players: players,
  sponsors: [],
  spent_grant_nullifiers: [],
  public_play_count: players.length,
  sponsorship_count: 0,
  local_service_total: service,
  power_root: hex("10"),
  loot_root: hex("20"),
  canon_root: hex("30"),
  canon_revision: 18,
});

const payload = ({ actor, service }) => ({
  kind: "public-play",
  actor,
  beneficiary: actor,
  activity_id: hex("12"),
  grant_nullifier: hex("00"),
  authority_commitment: hex("13"),
  local_service: service,
});

/** Deterministic source for the current node's exact Galley wire specimen. */
export function buildGalleyWireFixture() {
  const receiptPostcardSha256 = "9f64a747e1b97f131fabb6b447296c9b6f0201e79fb3c5356e6c77e89b6a806a";
  const actor = hex("42");
  const earlierActor = hex("24");
  const dailyId = hex("33");
  const aggregateId = `galley:${dailyId}`;
  return {
    format: "POA-GALLEY-CROSS-WIRE-V1",
    prepare: {
      format: "POA-GALLEY-COMMAND-PREPARE-V1",
      action_token: hex("11"),
    },
    session: {
      format: "POA-GALLEY-SESSION-V1",
      federation_id: hex("55"),
      daily_id: dailyId,
      aggregate_id: aggregateId,
      schema_version: 1,
      sequence: 1,
      semantic_head: hex("66"),
      projection_digest: hex("77"),
      projection: projection({ sequence: 1, players: [earlierActor], service: 3 }),
      actions: [
        { kind: "perform", action_token: hex("11"), expires_after_sequence: 1 },
      ],
      replay: {
        audited: true,
        event_count: 1,
        total_event_count: 1,
        from_sequence: 1,
        through_sequence: 1,
        head_digest: hex("66"),
      },
    },
    unsigned_turn: {
      format: "POA-GALLEY-UNSIGNED-TURN-V1",
      intent_id: hex("dd"),
      federation_id: hex("55"),
      preparation_digest: "9f64a747e1b97f131fabb6b447296c9b6f0201e79fb3c5356e6c77e89b6a806a",
      turn_postcard_base64: "AQIDBA==",
      expires_after_sequence: 1,
    },
    status_before: {
      format: "POA-GALLEY-STATUS-V1",
      federation_id: hex("55"),
      daily_id: dailyId,
      aggregate_id: aggregateId,
      schema_version: 1,
      sequence: 1,
      semantic_head: hex("66"),
      projection_digest: hex("77"),
      projection: projection({ sequence: 1, players: [earlierActor], service: 3 }),
      actions: [
        { kind: "perform", action_token: hex("11"), expires_after_sequence: 1 },
      ],
      replay: {
        audited: true,
        event_count: 1,
        total_event_count: 1,
        from_sequence: 1,
        through_sequence: 1,
        head_digest: hex("66"),
      },
      events: [{
        sequence: 1,
        turn_hash: hex("44"),
        receipt_hash: hex("45"),
        event_digest: hex("66"),
        payload_digest: hex("46"),
        payload: payload({ actor: earlierActor, service: 3 }),
        receipt: { index: 1, postcard_base64: "AQIDBA==", sha256: receiptPostcardSha256 },
      }],
    },
    status: {
      format: "POA-GALLEY-STATUS-V1",
      federation_id: hex("55"),
      daily_id: dailyId,
      aggregate_id: aggregateId,
      schema_version: 1,
      sequence: 2,
      semantic_head: hex("aa"),
      projection_digest: hex("cc"),
      projection: projection({ sequence: 2, players: [earlierActor, actor], service: 6 }),
      actions: [],
      replay: {
        audited: true,
        event_count: 2,
        total_event_count: 2,
        from_sequence: 1,
        through_sequence: 2,
        head_digest: hex("aa"),
      },
      events: [{
        sequence: 1,
        turn_hash: hex("44"),
        receipt_hash: hex("45"),
        event_digest: hex("66"),
        payload_digest: hex("46"),
        payload: payload({ actor: earlierActor, service: 3 }),
        receipt: { index: 1, postcard_base64: "AQIDBA==", sha256: receiptPostcardSha256 },
      }, {
        sequence: 2,
        turn_hash: hex("88"),
        receipt_hash: hex("99"),
        event_digest: hex("aa"),
        payload_digest: hex("bb"),
        payload: payload({ actor, service: 3 }),
        receipt: { index: 2, postcard_base64: "AQIDBA==", sha256: receiptPostcardSha256 },
      }],
    },
  };
}

export function renderGalleyWireFixture() {
  return `${JSON.stringify(buildGalleyWireFixture(), null, 2)}\n`;
}

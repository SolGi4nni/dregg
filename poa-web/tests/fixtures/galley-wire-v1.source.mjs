const hex = (pair) => pair.repeat(32);

/** Deterministic source for the cross-client Galley wire specimen. */
export function buildGalleyWireFixture() {
  const receiptPostcardSha256 = "9f64a747e1b97f131fabb6b447296c9b6f0201e79fb3c5356e6c77e89b6a806a";
  return {
    format: "POA-GALLEY-CROSS-WIRE-V1",
    prepare: {
      format: "POA-GALLEY-COMMAND-PREPARE-V1",
      action_token: "perform:vat-pressure:third-watch",
    },
    session: {
      format: "POA-GALLEY-SESSION-V1",
      federation_id: hex("55"),
      daily_id: "daily-119-third-watch",
      aggregate_id: "galley:deck-119",
      schema_version: 1,
      sequence: 7,
      semantic_head: hex("66"),
      projection_digest: hex("77"),
      projection: {
        kind: "GalleyMaintenanceDaily",
        summary: "Reclamation vat pressure loss",
        note: "Opaque beta projection; presentation schema not frozen",
      },
      actions: [
        { kind: "perform", action_token: "perform:vat-pressure:third-watch", expires_after_sequence: 7 },
        { kind: "visit_commons", action_token: "commons:third-watch", expires_after_sequence: 7 },
        { kind: "public_vote", action_token: "vote:third-watch", expires_after_sequence: 7 },
      ],
      replay: {
        audited: true,
        event_count: 1,
        total_event_count: 7,
        from_sequence: 7,
        through_sequence: 7,
        head_digest: hex("66"),
      },
    },
    unsigned_turn: {
      format: "POA-GALLEY-UNSIGNED-TURN-V1",
      intent_id: "galley-intent-008",
      federation_id: hex("55"),
      turn_hash: hex("88"),
      turn_postcard_base64: "AQIDBA==",
      expires_after_sequence: 7,
    },
    status: {
      format: "POA-GALLEY-STATUS-V1",
      federation_id: hex("55"),
      daily_id: "daily-119-third-watch",
      aggregate_id: "galley:deck-119",
      schema_version: 1,
      sequence: 8,
      semantic_head: hex("aa"),
      projection_digest: hex("cc"),
      projection: {
        kind: "GalleyMaintenanceDaily",
        summary: "Reclamation vat pressure accepted",
        note: "Opaque beta projection; presentation schema not frozen",
      },
      actions: [
        { kind: "perform", action_token: "perform:intake-collar:third-watch", expires_after_sequence: 8 },
        { kind: "visit_commons", action_token: "commons:third-watch", expires_after_sequence: 8 },
      ],
      replay: {
        audited: true,
        event_count: 1,
        total_event_count: 8,
        from_sequence: 8,
        through_sequence: 8,
        head_digest: hex("aa"),
      },
      events: [{
        sequence: 8,
        turn_hash: hex("88"),
        receipt_hash: hex("99"),
        event_digest: hex("aa"),
        payload_digest: hex("bb"),
        payload: { kind: "maintenance_observation", visibility: "public" },
        receipt: { index: 8, postcard_base64: "AQIDBA==", sha256: receiptPostcardSha256 },
      }],
    },
  };
}

export function renderGalleyWireFixture() {
  return `${JSON.stringify(buildGalleyWireFixture(), null, 2)}\n`;
}

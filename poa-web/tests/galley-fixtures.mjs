import { readFileSync } from "node:fs";
import {
  normalizeGalleySession,
  normalizeGalleyStatus,
  normalizeGalleyUnsignedTurn,
} from "../src/galley-runtime.js";

export const GALLEY_FIXTURE_ORIGIN = "https://beta.pathofangels.network";
export const GALLEY_ACTOR_PUBLIC_KEY = "42".repeat(32);
export const GALLEY_WIRE_FIXTURE_URL = new URL("./fixtures/galley-wire-v1.json", import.meta.url);
export const GALLEY_WIRE_FIXTURE = Object.freeze(JSON.parse(readFileSync(GALLEY_WIRE_FIXTURE_URL, "utf8")));

export function galleySession() { return structuredClone(GALLEY_WIRE_FIXTURE.session); }
export function galleyUnsignedTurn() { return structuredClone(GALLEY_WIRE_FIXTURE.unsigned_turn); }
export function galleyStatus() { return structuredClone(GALLEY_WIRE_FIXTURE.status); }
export function pendingGalleyStatus() {
  const session = galleySession();
  return {
    ...session,
    format: "POA-GALLEY-STATUS-V1",
    events: [{
      sequence: 7,
      turn_hash: "44".repeat(32),
      receipt_hash: "45".repeat(32),
      event_digest: session.semantic_head,
      payload_digest: "46".repeat(32),
      payload: { kind: "earlier_journal_event" },
      receipt: {
        index: 7,
        postcard_base64: "AQIDBA==",
        sha256: "9f64a747e1b97f131fabb6b447296c9b6f0201e79fb3c5356e6c77e89b6a806a",
      },
    }],
  };
}

export function createFixtureGalleyTransport({
  pending = false,
  signingResult = {
    state: "submitted",
    turnHash: GALLEY_WIRE_FIXTURE.unsigned_turn.turn_hash,
    outboxId: null,
    error: null,
  },
} = {}) {
  const calls = [];
  return {
    calls,
    async openSession(actorPublicKeyHex) {
      calls.push({ method: "openSession", actorPublicKeyHex });
      return normalizeGalleySession(galleySession());
    },
    async requestCommand(view, token, actorPublicKeyHex) {
      calls.push({ method: "requestCommand", view, token, actorPublicKeyHex });
      return {
        kind: "signing",
        signingRequest: normalizeGalleyUnsignedTurn(galleyUnsignedTurn()),
        view,
      };
    },
    async sign(request, provider) {
      calls.push({ method: "sign", request, provider });
      return structuredClone(signingResult);
    },
    async status(request, actorPublicKeyHex) {
      calls.push({ method: "status", request, actorPublicKeyHex });
      const view = normalizeGalleyStatus(pending ? pendingGalleyStatus() : galleyStatus());
      return pending
        ? { state: "pending", event: null, receiptChecksumMatched: false, view }
        : { state: "settled", event: view.events[0], receiptChecksumMatched: true, view };
    },
  };
}

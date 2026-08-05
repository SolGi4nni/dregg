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
export function galleyStatusBefore() { return structuredClone(GALLEY_WIRE_FIXTURE.status_before); }
export function galleyStatus() { return structuredClone(GALLEY_WIRE_FIXTURE.status); }
export function pendingGalleyStatus() {
  return galleyStatusBefore();
}

export function createFixtureGalleyTransport({
  pending = false,
  signingResult = {
    state: "submitted",
    turnHash: GALLEY_WIRE_FIXTURE.status.events.at(-1).turn_hash,
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
    async openWatch(actorPublicKeyHex) {
      calls.push({ method: "openWatch", actorPublicKeyHex });
      return normalizeGalleyStatus(galleyStatusBefore());
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
      const event = view.events.find(({ turnHash }) => turnHash === request.finalTurnHash) ?? null;
      return pending
        ? { state: "pending", event: null, receiptChecksumMatched: false, view }
        : { state: "settled", event, receiptChecksumMatched: event !== null, view };
    },
  };
}

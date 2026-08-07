/** The deliberately tiny page-authored part of a PoA Signal claim. */
export const POA_SIGNAL_SCHEMA = "poa-signal-claim/v1" as const;
export const POA_SIGNAL_BETA_ORIGIN = "https://beta.pathofangels.network" as const;
export const POA_SIGNAL_NODE_URL = "https://node.pathofangels.network" as const;
/**
 * The federation every consented Signal claim is signed against and posted to.
 *
 * ⚠ FLAG DAY, 2026-08-06. This was
 * `4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a`, a
 * federation that no longer exists. The live deployment
 * (`poa/deployments/epoch-1/poa-devnet.json`) moved to the value below, and the
 * old id was still here — so the extension signed each claim under the wrong
 * federation domain and posted it to
 * `/api/poa/signal/4ea83e8e…/claims`, where the node's authority selector
 * answers 400 because the path does not name its configured federation. Every
 * judged Signal claim from the extension was refused before it reached the
 * judge, and nothing said so: the failure looked like an ordinary rejection.
 *
 * It is the SAME staleness found in three other places the same week (the
 * epoch-1 curator golden, the companion route fixture, the follower-package
 * test) — one deployment identity copied into four files with no source.
 * `poa-signal.test.mjs` now reads `poa-devnet.json` and fails if this constant
 * and the deployment disagree, so the next move breaks a test instead of a
 * player's turn.
 */
export const POA_SIGNAL_FEDERATION_HEX =
  "70b7fa4cfbc3921bef2e1ddb1a42869c8dcef27539179c9cbdf6a6e6b1d07c1b" as const;
export const POA_SIGNAL_MISSION_ID = 1 as const;

/** One three-band Signal code. */
export type PoASignalCode = [number, number, number];

/**
 * A judged run plays at most `SignalTriangulation.MAX_TURNS` bursts. Same number
 * as `dregg_sdk::poa_signal::SIGNAL_MAX_TRANSCRIPT_ROUNDS` and
 * `dregg_persist::POA_SIGNAL_SESSION_MAX_ROUNDS`; a longer transcript is one the
 * judge's `replay` refuses at the step, after the player paid a turn fee.
 */
export const POA_SIGNAL_MAX_ROUNDS = 5 as const;

export interface PoASignalClaimParams {
  schema: typeof POA_SIGNAL_SCHEMA;
  missionId: number;
  /**
   * ⚑ FLAG DAY, 2026-08-07 — THIS WAS `code`, ONE TRIPLE.
   *
   * A claim carries the TRANSCRIPT that was played, and the node refuses one
   * whose rounds it did not itself classify. A page that posts only the winning
   * code buys a rejected turn: `poa-signal-transcript-length-mismatch` if it
   * played more than one burst, `poa-signal-transcript-no-session` if it never
   * opened a session at all. Take this list verbatim from the judged session
   * document's `settlement.transcript`, in the order it was played.
   *
   * The old shape does not degrade quietly: `parsePoASignalClaim` pins the exact
   * key set, so a `code` claim is refused here, and the wasm builder's `Spec` is
   * `deny_unknown_fields`, so it would be refused there too.
   */
  transcript: readonly PoASignalCode[];
}

export type ParsedPoASignalClaim = {
  schema: typeof POA_SIGNAL_SCHEMA;
  missionId: typeof POA_SIGNAL_MISSION_ID;
  transcript: PoASignalCode[];
};

export type ParsePoASignalClaimResult =
  | { ok: true; claim: ParsedPoASignalClaim }
  | { ok: false; error: string };

/**
 * Validate and copy the complete page-facing claim. Exact keys are enforced so
 * caller-supplied authority, destination, reward, memo or effect fields cannot
 * hitch a ride to the extension background.
 */
export function parsePoASignalClaim(value: unknown): ParsePoASignalClaimResult {
  if (!value || typeof value !== "object" || Array.isArray(value)) {
    return { ok: false, error: "claim must be an object" };
  }
  const record = value as Record<string, unknown>;
  const keys = Object.keys(record).sort();
  if (keys.join(",") !== "missionId,schema,transcript") {
    return {
      ok: false,
      error: "claim must contain exactly schema, missionId, and transcript",
    };
  }
  if (record.schema !== POA_SIGNAL_SCHEMA) {
    return { ok: false, error: `schema must be ${POA_SIGNAL_SCHEMA}` };
  }
  if (record.missionId !== POA_SIGNAL_MISSION_ID) {
    return { ok: false, error: `missionId must be ${POA_SIGNAL_MISSION_ID}` };
  }
  if (
    !Array.isArray(record.transcript)
    || record.transcript.length < 1
    || record.transcript.length > POA_SIGNAL_MAX_ROUNDS
  ) {
    return {
      ok: false,
      error: `transcript must name 1 to ${POA_SIGNAL_MAX_ROUNDS} played rounds`,
    };
  }
  // A DEEP copy, round by round: the whole point of validating here is that the
  // page cannot mutate the claim after consent is painted, and a shallow copy of
  // an array of arrays leaves every round aliased to the caller's object.
  const transcript: PoASignalCode[] = [];
  for (let round = 0; round < record.transcript.length; round++) {
    const played = record.transcript[round];
    if (!Array.isArray(played) || played.length !== 3) {
      return {
        ok: false,
        error: `transcript[${round}] must contain exactly three Signal bands`,
      };
    }
    const code: PoASignalCode = [0, 0, 0];
    for (let i = 0; i < 3; i++) {
      const band = played[i];
      if (!Number.isSafeInteger(band) || (band as number) < 0 || (band as number) > 5) {
        return {
          ok: false,
          error: `transcript[${round}][${i}] must be an integer from 0 through 5`,
        };
      }
      code[i] = band as number;
    }
    transcript.push(code);
  }
  return {
    ok: true,
    claim: { schema: POA_SIGNAL_SCHEMA, missionId: POA_SIGNAL_MISSION_ID, transcript },
  };
}

export interface PoASignalConsentDetails {
  missionId: number;
  transcript: readonly PoASignalCode[];
  signerPublicKeyHex: string;
  agentCellId: string;
  nonce: number;
  previousReceiptHashHex: string | null;
  federationHex: string;
  fee: number;
  turnHash: string;
}

export interface PoASignalSubmitResult {
  turnId?: string;
  admission: "admitted" | "queued" | "refused";
  transition: "observed" | "not_observed";
  queued?: boolean;
  outboxId?: string;
  transitionSequence?: number;
  error?: string;
}

/** A faithful, deliberately non-economic reading for un-overlayable consent. */
export function explainPoASignalClaim(details: PoASignalConsentDetails): string {
  const predecessor = details.previousReceiptHashHex ?? "genesis (no previous receipt)";
  return [
    "PATH OF ANGELS — PUBLISH SIGNAL CLAIM",
    `Mission: ${details.missionId}`,
    // ⚠ THE CONSENT SHOWS THE WHOLE RUN, not just the answer. What is published
    // is every guess this player made, in order — a reader consenting to "publish
    // my solved code" while the turn carried five is being told the wrong thing
    // about what leaves their machine.
    `Signal transcript (${details.transcript.length} of ${POA_SIGNAL_MAX_ROUNDS} bursts): `
      + details.transcript.map((code) => code.join(" · ")).join("  →  "),
    `Solving code: ${details.transcript[details.transcript.length - 1]?.join(" · ") ?? "—"}`,
    "Public action: publish this solved run — every burst played, in order — to the PoA federation.",
    "Economic effect: none. This claim transfers no DREGG, mints no reward, and grants no capability.",
    `Player key: ${details.signerPublicKeyHex}`,
    `Player cell: ${details.agentCellId}`,
    `Turn nonce: ${details.nonce}`,
    `Previous receipt: ${predecessor}`,
    `Computron fee ceiling: ${details.fee}`,
    `PoA federation: ${details.federationHex}`,
    "The node may admit this turn before consensus records the PoA transition.",
    `[turn ${details.turnHash}]`,
  ].join("\n");
}

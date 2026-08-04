/** The deliberately tiny page-authored part of a PoA Signal claim. */
export const POA_SIGNAL_SCHEMA = "poa-signal-claim/v1" as const;
export const POA_SIGNAL_BETA_ORIGIN = "https://beta.pathofangels.network" as const;
export const POA_SIGNAL_NODE_URL = "https://node.pathofangels.network" as const;
export const POA_SIGNAL_FEDERATION_HEX =
  "4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a" as const;
export const POA_SIGNAL_MISSION_ID = 1 as const;

export interface PoASignalClaimParams {
  schema: typeof POA_SIGNAL_SCHEMA;
  missionId: number;
  code: readonly [number, number, number];
}

export type ParsedPoASignalClaim = {
  schema: typeof POA_SIGNAL_SCHEMA;
  missionId: typeof POA_SIGNAL_MISSION_ID;
  code: [number, number, number];
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
  if (keys.join(",") !== "code,missionId,schema") {
    return {
      ok: false,
      error: "claim must contain exactly schema, missionId, and code",
    };
  }
  if (record.schema !== POA_SIGNAL_SCHEMA) {
    return { ok: false, error: `schema must be ${POA_SIGNAL_SCHEMA}` };
  }
  if (record.missionId !== POA_SIGNAL_MISSION_ID) {
    return { ok: false, error: `missionId must be ${POA_SIGNAL_MISSION_ID}` };
  }
  if (!Array.isArray(record.code) || record.code.length !== 3) {
    return { ok: false, error: "code must contain exactly three Signal bands" };
  }
  const code: [number, number, number] = [0, 0, 0];
  for (let i = 0; i < 3; i++) {
    const band = record.code[i];
    if (!Number.isSafeInteger(band) || (band as number) < 0 || (band as number) > 5) {
      return { ok: false, error: `code[${i}] must be an integer from 0 through 5` };
    }
    code[i] = band as number;
  }
  return {
    ok: true,
    claim: { schema: POA_SIGNAL_SCHEMA, missionId: POA_SIGNAL_MISSION_ID, code },
  };
}

export interface PoASignalConsentDetails {
  missionId: number;
  code: readonly [number, number, number];
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
    `Signal code: ${details.code.join(" · ")}`,
    "Public action: publish this solved three-band code to the PoA federation.",
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

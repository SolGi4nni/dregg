import {
  POA_RECEIPT_CORE_PROTOCOL,
  type PoACompanionModel,
  type PoACompanionResponse,
  type PoAFieldRecordBinding,
} from "../../src/poa";
import {
  registerPoAElement,
  setPoAFieldRecordTransportFactory,
  setPoAPortFactory,
} from "../../src/elements/dregg-poa";

declare const window: any;

const VIDEO = "AbCdEfGhI01";
const POST = "1891234567890123456";
const RECEIPT = "33".repeat(32);
const MANIFEST = "44".repeat(32);
const FEDERATION = "55".repeat(32);
const TURN = "66".repeat(32);
const BLOCK = "77".repeat(32);
const AGENT = "88".repeat(32);

function signedModel(experienceId: string, platform: "youtube" | "x" = "youtube"): PoACompanionModel {
  const common = {
    trust: "signed_manifest" as const,
    contextId: platform === "youtube" ? VIDEO : POST,
    contentEpoch: 2,
    counter: 7,
    manifestDigest: MANIFEST,
    issuedAt: 1_800_000_000,
    expiresAt: 1_800_003_600,
    experienceId,
    title: "Crown wreckage debrief",
    episode: "Episode 2",
    dispatch: "The Crown returned three public bearings.",
    betaUrl: "https://beta.pathofangels.network/?episode=2",
    actions: {
      mission: { label: "Enter the deck survey", betaUrl: "https://beta.pathofangels.network/?view=missions&episode=2" },
      evidence: { label: '<img src=x onerror="window.HOST_AUTHORITY=true"> Inspect the bearings', betaUrl: "https://beta.pathofangels.network/?view=records&episode=2" },
      debrief: { label: "Read the crew debrief", betaUrl: "https://beta.pathofangels.network/?view=watch&episode=2" },
    },
    fieldRecord: { finalizedReceiptCoreId: RECEIPT, federationId: FEDERATION, turnHash: TURN },
    signer: "11".repeat(32),
  };
  return platform === "youtube"
    ? { ...common, platform, videoId: VIDEO, channelId: "UC_PathOfAngels" }
    : { ...common, platform, postId: POST };
}

const localModel: PoACompanionModel = {
  trust: "local_allowlist",
  platform: "youtube",
  contextId: VIDEO,
  videoId: VIDEO,
  experienceId: "local-shell",
  title: "Path of Angels field terminal",
  dispatch: "This exact video is locally recognized.",
  betaUrl: "https://beta.pathofangels.network/",
  availability: "authenticated_route_unavailable",
};

function success(model: PoACompanionModel): PoACompanionResponse {
  return model.trust === "signed_manifest"
    ? { ok: true, recognized: true, verified: true, tier: "extension", model }
    : { ok: true, recognized: true, verified: false, tier: "none", model };
}

let deferredRelease: ((value: unknown) => void) | null = null;

setPoAPortFactory(() => ({
  async request(req) {
    const href = req.context.href;
    if (href.includes("local")) return success(localModel);
    if (href.includes("x-route")) return success(signedModel("x-episode-debrief", "x"));
    if (href.includes("mismatch")) return success(signedModel("mismatch-record"));
    if (href.includes("deferred")) return success(signedModel("deferred-record"));
    return success(signedModel("no-transport-record"));
  },
}));

window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;
registerPoAElement();

function appendCompanion(id: string, pageUrl: string): HTMLElement {
  const element = document.createElement("dregg-poa");
  element.id = id;
  element.setAttribute("page-url", pageUrl);
  document.querySelector("#mount")?.appendChild(element);
  return element;
}

function canonicalFrc1(): string {
  const bytes = new Uint8Array(592);
  const view = new DataView(bytes.buffer);
  const putHex = (offset: number, hex: string) => {
    for (let index = 0; index < hex.length / 2; index += 1) {
      bytes[offset + index] = Number.parseInt(hex.slice(index * 2, index * 2 + 2), 16);
    }
  };
  bytes.set(new TextEncoder().encode("FRC1"), 0);
  view.setUint16(4, 1, true);
  bytes.set(new TextEncoder().encode("FEC1"), 8);
  view.setUint16(12, 1, true);
  putHex(16, BLOCK);
  view.setBigUint64(48, 19n, true);
  view.setBigInt64(56, 1_700_000_019n, true);
  view.setBigUint64(64, 3n, true);
  putHex(72, TURN);
  putHex(321, AGENT);
  putHex(353, FEDERATION);
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join("");
}

function record(_binding: PoAFieldRecordBinding): unknown {
  return {
    protocol: POA_RECEIPT_CORE_PROTOCOL,
    receipt_index: 12,
    core_id: RECEIPT,
    canonical_core: canonicalFrc1(),
    block_id: BLOCK,
    tau_round: 19,
    consensus_unix_seconds: 1_700_000_019,
    committee_epoch: 3,
    predecessor: { kind: "genesis" },
    turn_hash: TURN,
    agent: AGENT,
    federation_id: FEDERATION,
  };
}

// Construct this element while the deliberate production seam is absent.
appendCompanion("no-transport", "https://www.youtube.com/watch?v=no-transport");

setPoAFieldRecordTransportFactory(() => ({
  async readReceiptCoreObservation(binding) {
    if (binding.experienceId === "mismatch-record") {
      return { ...(record(binding) as Record<string, unknown>), core_id: "99".repeat(32) };
    }
    if (binding.experienceId === "deferred-record") {
      return new Promise((resolve) => { deferredRelease = resolve; });
    }
    return record(binding);
  },
}));

appendCompanion("active", "https://x.com/sentyr/status/x-route");
appendCompanion("mismatch", "https://www.youtube.com/watch?v=mismatch");
appendCompanion("deferred", "https://www.youtube.com/watch?v=deferred");
appendCompanion("local", "https://www.youtube.com/watch?v=local");

window.__poaActionsRoot = (id: string): ShadowRoot | null => {
  const element = document.querySelector(`#${id}`);
  return element ? window.__dreggPoARoots?.get(element) ?? null : null;
};
window.__poaReleaseDeferred = () => {
  const binding: PoAFieldRecordBinding = {
    platform: "youtube",
    contextId: VIDEO,
    experienceId: "deferred-record",
    manifestDigest: MANIFEST,
    finalizedReceiptCoreId: RECEIPT,
    federationId: FEDERATION,
    turnHash: TURN,
  };
  deferredRelease?.(record(binding));
  deferredRelease = null;
};
window.__POA_ACTIONS_READY = true;

import {
  DREGG_MINT,
  DREGG_TOKEN_PROGRAM,
  base64ToBytes,
  base58ToBytes,
  bytesToBase58,
  bytesToBase64,
  connectDreggWallet,
  discoverDreggWallets,
  normalizeSolanaPublicKey,
} from "./dregg-wallet.js";

export const DREGG_HOLDING_CHALLENGE_FORMAT = "poa-dregg-holding-challenge-v2";
export const DREGG_HOLDING_CAPABILITY_FORMAT = "poa-dregg-holding-capability-v2";
export const DREGG_HOLDING_STATUS_FORMAT = "poa-dregg-holding-status-v2";
export const DREGG_ADMISSION_SCOPE = "poa:beta:game-admission";
export const DREGG_ADMISSION_TRUST_GRADE = "rpcAttested";
export const DREGG_BACKEND_TRUST = "beta-rpc-attested";
export const DREGG_CLUSTER = "solana:mainnet-beta";
export const DREGG_HOLDING_WALLET_CONSENT_DOMAIN = "path-of-angels/dregg-holding/wallet-consent/v2";

/** Beta routes are proxied through `/node/*`; node-internal routes omit `/node`. */
export const DEFAULT_DREGG_ADMISSION_ENDPOINTS = Object.freeze({
  challenge: "/node/api/poa/holding/challenge",
  verify: "/node/api/poa/holding/verify",
  statusPrefix: "/node/api/poa/holding/status/",
});

const RECEIPT_STORAGE_KEY = "poa.dregg.beta-holding-receipt.v1";
const RECEIPT_STORAGE_FORMAT = "poa-dregg-holding-session-v2";
const MAX_CHALLENGE_LIFETIME_SECONDS = 300;
const MAX_CAPABILITY_LIFETIME_SECONDS = 120;
const CLOCK_SKEW_SECONDS = 30;
const DREGG_ADMISSION_ORIGIN = "https://beta.pathofangels.network";
const DREGG_ADMISSION_DOMAIN = "pathofangels.network";
const MAINNET_GENESIS = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const CAPABILITY_TTL_SECONDS = 120;
const decoder = new TextDecoder("utf-8", { fatal: true });

const CHALLENGE_KEYS = Object.freeze([
  "challenge_id", "cluster", "expires_at", "format", "issued_at", "min_context_slot",
  "minimum_raw_balance", "mint", "player", "player_cell", "signing_message_base64", "wallet",
]);
const CAPABILITY_KEYS = Object.freeze([
  "expires_at", "format", "governance_weight_bearing", "issued_at", "mint",
  "player", "player_cell", "receipt_id", "snapshot_slot", "trust", "wallet",
]);
const STATUS_KEYS = Object.freeze([
  "expires_at", "format", "governance_weight_bearing", "receipt_id", "state", "trust",
]);
const STORED_RECEIPT_KEYS = Object.freeze([
  "format", "player", "player_cell", "receipt_id", "wallet",
]);

class HoldingBackendError extends Error {
  constructor(status, code = null) {
    super(`holding backend refused request (${status})`);
    this.name = "HoldingBackendError";
    this.status = status;
    this.code = code;
  }
}

class InactiveReceiptError extends Error {
  constructor(state) {
    super(`receipt ${state}`);
    this.name = "InactiveReceiptError";
    this.state = state;
  }
}

function requiredText(name, value) {
  if (typeof value !== "string" || value.length === 0 || /\r|\n|[\u0000-\u001f]/u.test(value)) {
    throw new TypeError(`${name} must be non-empty text without control characters`);
  }
  return value;
}

function safeInteger(name, value) {
  if (!Number.isSafeInteger(value) || value < 0) throw new TypeError(`${name} must be a non-negative safe integer`);
  return value;
}

function safeNowSeconds(now) {
  const value = typeof now === "function" ? now() : now;
  return Math.floor(safeInteger("clock", value) / 1000);
}

function decimalRaw(name, value, { positive = false } = {}) {
  const text = requiredText(name, value);
  if (!/^(?:0|[1-9][0-9]*)$/u.test(text) || (positive && text === "0")) {
    throw new TypeError(`${name} must be canonical decimal atomic units`);
  }
  return text;
}

function base64Url32(name, value) {
  const text = requiredText(name, value);
  if (!/^[A-Za-z0-9_-]{43}$/u.test(text)) throw new TypeError(`${name} must be base64url-no-pad 32 bytes`);
  const standard = `${text.replace(/-/gu, "+").replace(/_/gu, "/")}=`;
  if (base64ToBytes(standard).length !== 32) throw new TypeError(`${name} must encode 32 bytes`);
  return text;
}

function exactKeys(name, payload, expected) {
  const actual = Object.keys(payload).sort();
  if (actual.length !== expected.length || actual.some((key, index) => key !== expected[index])) {
    throw new Error(`${name} has unexpected or missing fields`);
  }
}

function bytesEqual(left, right) {
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

function bytesToHex(bytes) {
  return [...bytes].map((value) => value.toString(16).padStart(2, "0")).join("");
}

function base64UrlToBytes(name, value) {
  const text = base64Url32(name, value);
  return base64ToBytes(`${text.replace(/-/gu, "+").replace(/_/gu, "/")}=`);
}

function framedFields(message, count) {
  const fields = [];
  let offset = 0;
  while (offset < message.length) {
    if (offset + 4 > message.length) throw new Error("wallet consent has a truncated field length");
    const length = new DataView(message.buffer, message.byteOffset + offset, 4).getUint32(0, false);
    offset += 4;
    if (offset + length > message.length) throw new Error("wallet consent has a truncated field");
    fields.push(message.slice(offset, offset + length));
    offset += length;
  }
  if (fields.length !== count) throw new Error("wallet consent has the wrong field count");
  return fields;
}

function utf8Field(name, bytes) {
  let text;
  try { text = decoder.decode(bytes); }
  catch { throw new Error(`${name} is not canonical UTF-8`); }
  return requiredText(name, text);
}

function u64Field(name, bytes) {
  if (bytes.length !== 8) throw new Error(`${name} must be an eight-byte integer`);
  const value = new DataView(bytes.buffer, bytes.byteOffset, 8).getBigUint64(0, false);
  if (value > BigInt(Number.MAX_SAFE_INTEGER)) throw new Error(`${name} exceeds browser-safe bounds`);
  return Number(value);
}

function nonzeroBytes32(name, bytes) {
  if (bytes.length !== 32 || bytes.every((value) => value === 0)) {
    throw new Error(`${name} must be a nonzero 32-byte value`);
  }
  return bytes;
}

function normalizePlayerBase58(name, value) {
  const normalized = normalizeSolanaPublicKey(name, value);
  return Object.freeze({ base58: normalized, hex: bytesToHex(base58ToBytes(normalized)) });
}

function normalizePlayerIdentity(value) {
  if (!value || typeof value !== "object" || Array.isArray(value)) {
    throw new TypeError("active Dregg identity is required");
  }
  const publicKeyHex = value.publicKeyHex ?? value.public_key_hex;
  const profileName = value.profileName ?? value.profile_name;
  if (typeof publicKeyHex !== "string" || !/^[0-9a-f]{64}$/u.test(publicKeyHex) || /^0+$/u.test(publicKeyHex)) {
    throw new TypeError("active Dregg identity must expose a lowercase nonzero Ed25519 public key");
  }
  if (typeof profileName !== "string" || profileName.length === 0 || profileName.length > 80 ||
      /[\u0000-\u001f\u007f]/u.test(profileName)) {
    throw new TypeError("active Dregg identity must expose a bounded profile name");
  }
  const identity = Object.freeze({ publicKeyHex, profileName });
  const bytes = Uint8Array.from(identity.publicKeyHex.match(/.{2}/gu), (pair) => Number.parseInt(pair, 16));
  return Object.freeze({ ...identity, base58: bytesToBase58(bytes) });
}

function validateWalletConsentMessage(message, challenge, expectedOrigin) {
  const fields = framedFields(message, 19);
  const expected = [
    [utf8Field("wallet consent domain", fields[0]), DREGG_HOLDING_WALLET_CONSENT_DOMAIN],
    [bytesToHex(fields[1]), bytesToHex(base64UrlToBytes("challenge_id", challenge.challengeId))],
    [utf8Field("wallet consent origin", fields[3]), expectedOrigin],
    [utf8Field("wallet consent domain name", fields[4]), DREGG_ADMISSION_DOMAIN],
    [utf8Field("wallet consent cluster", fields[5]), challenge.cluster],
    [bytesToHex(fields[6]), bytesToHex(base58ToBytes(MAINNET_GENESIS))],
    [bytesToHex(fields[8]), bytesToHex(base58ToBytes(challenge.mint))],
    [bytesToHex(fields[9]), bytesToHex(base58ToBytes(DREGG_TOKEN_PROGRAM))],
    [bytesToHex(fields[10]), bytesToHex(base58ToBytes(challenge.walletAddress))],
    [bytesToHex(fields[11]), bytesToHex(base58ToBytes(challenge.player.base58))],
    [bytesToHex(fields[12]), bytesToHex(base64UrlToBytes("player_cell", challenge.playerCell))],
    [u64Field("minimum_raw_balance", fields[14]), Number(challenge.minimumRawBalance)],
    [u64Field("min_context_slot", fields[15]), challenge.minContextSlot],
    [u64Field("issued_at", fields[16]), challenge.issuedAt],
    [u64Field("expires_at", fields[17]), challenge.expiresAt],
    [u64Field("capability_ttl", fields[18]), CAPABILITY_TTL_SECONDS],
  ];
  nonzeroBytes32("federation id", fields[2]);
  nonzeroBytes32("RPC endpoint id", fields[7]);
  nonzeroBytes32("challenge nonce", fields[13]);
  if (fields[1].length !== 32 || fields[6].length !== 32 || fields[8].length !== 32 ||
      fields[9].length !== 32 || fields[10].length !== 32 || fields[11].length !== 32 ||
      fields[12].length !== 32 || expected.some(([actual, wanted]) => actual !== wanted)) {
    throw new Error("node signing message is not the canonical wallet consent for this challenge and Dregg officer");
  }
}

function validateWindow(issuedAt, expiresAt, nowSeconds, maximumLifetimeSeconds) {
  if (expiresAt <= issuedAt || expiresAt - issuedAt > maximumLifetimeSeconds) {
    throw new Error("holding evidence is not short-lived");
  }
  if (issuedAt > nowSeconds + CLOCK_SKEW_SECONDS || expiresAt <= nowSeconds - CLOCK_SKEW_SECONDS) {
    throw new Error("holding evidence is outside its time window");
  }
}

/** Resolve a configured endpoint, refusing all cross-origin or credential-bearing URLs. */
export function resolveSameOriginAdmissionEndpoint(endpoint, origin) {
  const trustedOrigin = new URL(requiredText("origin", origin)).origin;
  const resolved = new URL(requiredText("endpoint", endpoint), `${trustedOrigin}/`);
  if (resolved.origin !== trustedOrigin || resolved.username || resolved.password) {
    throw new Error("Dregg admission endpoints must be same-origin");
  }
  return resolved.href;
}

export function normalizeHoldingChallenge(payload, expected, nowMs = Date.now()) {
  if (!payload || typeof payload !== "object") throw new TypeError("holding challenge is required");
  exactKeys("holding challenge", payload, CHALLENGE_KEYS);
  const challenge = {
    format: requiredText("format", payload.format),
    challengeId: base64Url32("challenge_id", payload.challenge_id),
    walletAddress: normalizeSolanaPublicKey("wallet", payload.wallet),
    player: normalizePlayerBase58("player", payload.player),
    playerCell: base64Url32("player_cell", payload.player_cell),
    signingMessage: base64ToBytes(requiredText("signing_message_base64", payload.signing_message_base64)),
    mint: normalizeSolanaPublicKey("mint", payload.mint),
    cluster: requiredText("cluster", payload.cluster),
    minimumRawBalance: decimalRaw("minimum_raw_balance", payload.minimum_raw_balance, { positive: true }),
    minContextSlot: safeInteger("min_context_slot", payload.min_context_slot),
    issuedAt: safeInteger("issued_at", payload.issued_at),
    expiresAt: safeInteger("expires_at", payload.expires_at),
  };
  if (challenge.format !== DREGG_HOLDING_CHALLENGE_FORMAT ||
      challenge.walletAddress !== expected.walletAddress ||
      challenge.player.hex !== expected.playerPublicKey) {
    throw new Error("holding challenge has the wrong format, wallet, or Dregg officer");
  }
  if (challenge.mint !== DREGG_MINT || challenge.cluster !== DREGG_CLUSTER || challenge.minimumRawBalance !== "1") {
    throw new Error("holding challenge has the wrong mint, cluster, or admission threshold");
  }
  if (challenge.signingMessage.length === 0) throw new Error("holding challenge has an empty signing message");
  validateWindow(
    challenge.issuedAt,
    challenge.expiresAt,
    safeNowSeconds(nowMs),
    MAX_CHALLENGE_LIFETIME_SECONDS,
  );
  validateWalletConsentMessage(
    challenge.signingMessage,
    challenge,
    expected.origin ? new URL(expected.origin).origin : DREGG_ADMISSION_ORIGIN,
  );
  return Object.freeze(challenge);
}

function admissionCredential({
  receiptId, walletAddress, playerPublicKey, playerBase58, playerCell,
  snapshotSlot = null, issuedAt = null, expiresAt,
}) {
  return Object.freeze({
    receiptId,
    walletAddress,
    playerPublicKey,
    playerBase58,
    playerCell,
    snapshotSlot,
    issuedAt,
    expiresAt,
    trustGrade: DREGG_ADMISSION_TRUST_GRADE,
    backendTrust: DREGG_BACKEND_TRUST,
    scope: DREGG_ADMISSION_SCOPE,
    credentialKind: "short-lived",
    governanceWeightBearing: false,
    balanceClaimBearing: false,
    accountsProofAnchored: false,
    sponsorshipBearing: false,
  });
}

/** Validate a privacy-preserving node capability; exact holdings never cross this wire. */
export function normalizeHoldingCapability(payload, expected, nowMs = Date.now()) {
  if (!payload || typeof payload !== "object") throw new TypeError("holding capability is required");
  exactKeys("holding capability", payload, CAPABILITY_KEYS);
  const format = requiredText("format", payload.format);
  const receiptId = base64Url32("receipt_id", payload.receipt_id);
  const trust = requiredText("trust", payload.trust);
  const walletAddress = normalizeSolanaPublicKey("wallet", payload.wallet);
  const player = normalizePlayerBase58("player", payload.player);
  const playerCell = base64Url32("player_cell", payload.player_cell);
  const mint = normalizeSolanaPublicKey("mint", payload.mint);
  const snapshotSlot = safeInteger("snapshot_slot", payload.snapshot_slot);
  const issuedAt = safeInteger("issued_at", payload.issued_at);
  const expiresAt = safeInteger("expires_at", payload.expires_at);
  if (format !== DREGG_HOLDING_CAPABILITY_FORMAT || trust !== DREGG_BACKEND_TRUST ||
      walletAddress !== expected.walletAddress || mint !== DREGG_MINT ||
      player.hex !== expected.playerPublicKey || playerCell !== expected.playerCell ||
      payload.governance_weight_bearing !== false) {
    throw new Error("holding capability has unsupported authority or bindings");
  }
  validateWindow(issuedAt, expiresAt, safeNowSeconds(nowMs), MAX_CAPABILITY_LIFETIME_SECONDS);
  return admissionCredential({
    receiptId, walletAddress, playerPublicKey: player.hex, playerBase58: player.base58,
    playerCell, snapshotSlot, issuedAt, expiresAt,
  });
}

/** Active status can restore beta admission; expired/consumed receipts cannot. */
export function normalizeHoldingStatus(payload, expected, nowMs = Date.now()) {
  if (!payload || typeof payload !== "object") throw new TypeError("holding status is required");
  exactKeys("holding status", payload, STATUS_KEYS);
  if (requiredText("format", payload.format) !== DREGG_HOLDING_STATUS_FORMAT ||
      base64Url32("receipt_id", payload.receipt_id) !== expected.receiptId ||
      requiredText("trust", payload.trust) !== DREGG_BACKEND_TRUST ||
      payload.governance_weight_bearing !== false) {
    throw new Error("holding status has the wrong format or receipt");
  }
  const state = requiredText("state", payload.state);
  if (!["active", "expired", "consumed"].includes(state)) throw new Error("holding status has an unknown state");
  if (state !== "active") return Object.freeze({ state, credential: null });
  const expiresAt = safeInteger("expires_at", payload.expires_at);
  const nowSeconds = safeNowSeconds(nowMs);
  if (expiresAt <= nowSeconds - CLOCK_SKEW_SECONDS ||
      expiresAt > nowSeconds + MAX_CAPABILITY_LIFETIME_SECONDS + CLOCK_SKEW_SECONDS) {
    throw new Error("holding status is outside its short-lived time window");
  }
  return Object.freeze({
    state,
    credential: admissionCredential({
      receiptId: expected.receiptId,
      walletAddress: expected.walletAddress,
      playerPublicKey: expected.playerPublicKey,
      playerBase58: expected.playerBase58,
      playerCell: expected.playerCell,
      expiresAt,
    }),
  });
}

function encodeStoredReceipt(receiptId, walletAddress, playerBase58, playerCell) {
  return JSON.stringify({
    format: RECEIPT_STORAGE_FORMAT,
    player: normalizePlayerBase58("player", playerBase58).base58,
    player_cell: base64Url32("player_cell", playerCell),
    receipt_id: base64Url32("receipt_id", receiptId),
    wallet: normalizeSolanaPublicKey("wallet", walletAddress),
  });
}

function decodeStoredReceipt(serialized) {
  const payload = JSON.parse(requiredText("saved receipt", serialized));
  if (!payload || typeof payload !== "object" || Array.isArray(payload)) {
    throw new TypeError("saved receipt must be an object");
  }
  exactKeys("saved receipt", payload, STORED_RECEIPT_KEYS);
  if (payload.format !== RECEIPT_STORAGE_FORMAT) throw new Error("saved receipt has the wrong format");
  return Object.freeze({
    receiptId: base64Url32("receipt_id", payload.receipt_id),
    walletAddress: normalizeSolanaPublicKey("wallet", payload.wallet),
    ...(() => {
      const player = normalizePlayerBase58("player", payload.player);
      return { playerBase58: player.base58, playerPublicKey: player.hex };
    })(),
    playerCell: base64Url32("player_cell", payload.player_cell),
  });
}

function el(documentRef, tag, className, text) {
  const node = documentRef.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function button(documentRef, className, text) {
  const node = el(documentRef, "button", className, text);
  node.type = "button";
  return node;
}

function abbreviated(address) {
  return `${address.slice(0, 5)}…${address.slice(-5)}`;
}

async function jsonRequest(fetchImpl, url, {
  method = "GET",
  body,
} = {}) {
  const response = await fetchImpl(url, {
    method,
    credentials: "same-origin",
    cache: "no-store",
    redirect: "error",
    headers: Object.freeze({ Accept: "application/json", "Content-Type": "application/json" }),
    ...(body === undefined ? {} : { body: JSON.stringify(body) }),
  });
  const contentType = response.headers?.get?.("content-type") ?? "";
  if (!response.ok) {
    let code = null;
    if (contentType.toLowerCase().includes("application/json")) {
      try {
        const payload = await response.json();
        if (payload && typeof payload === "object" && typeof payload.code === "string") code = payload.code;
      } catch { /* Caddy/Axum refusals need not have the node error shape. */ }
    }
    throw new HoldingBackendError(response.status, code);
  }
  if (!contentType.toLowerCase().includes("application/json")) throw new Error("holding backend did not return JSON");
  return response.json();
}

function isTransientBackendFailure(error) {
  if (!(error instanceof HoldingBackendError)) return true;
  return error.status === 429 || error.status >= 500;
}

function authenticationFailureMessage(error, savedReceiptRetained) {
  let message;
  if (error instanceof Error && /active Dregg|Dregg identity|Dregg expedition officer/iu.test(error.message)) {
    message = "Unlock or create an active Dregg expedition officer before binding a Solana wallet.";
  } else if (error instanceof HoldingBackendError && error.status === 401) {
    message = "The beta invitation session was refused. Re-enter the beta credentials and try again.";
  } else if (error instanceof HoldingBackendError && error.code === "insufficient_dregg") {
    message = "The finalized RPC check did not find the minimum $DREGG holding for this wallet.";
  } else if (error instanceof HoldingBackendError && error.status === 429) {
    message = "The holding service is rate-limited or busy. Wait briefly and try again.";
  } else if (error instanceof HoldingBackendError && error.status >= 500) {
    message = "The PoA node or finalized Solana RPC is temporarily unavailable. No access was granted.";
  } else if (error instanceof HoldingBackendError && error.status === 410) {
    message = "The wallet challenge expired before verification. Request a fresh challenge.";
  } else {
    message = "Wallet proof was cancelled, malformed, or refused. No access was granted.";
  }
  return savedReceiptRetained ? `${message} Your previously saved receipt was retained.` : message;
}

function receiptFailureMessage(error, retained) {
  if (retained) {
    if (error instanceof HoldingBackendError && error.status === 429) {
      return "The holding service is rate-limited. Your wallet-bound receipt was retained; retry shortly.";
    }
    return "The PoA node could not check the saved receipt. It remains wallet-bound in this tab; retry when the service returns.";
  }
  if (error instanceof HoldingBackendError && error.status === 401) {
    return "The beta invitation session was refused. The saved receipt was cleared and no access was granted.";
  }
  if (error instanceof InactiveReceiptError && error.state === "expired") {
    return "The saved PoA receipt expired. Request fresh beta game admission.";
  }
  if (error instanceof InactiveReceiptError && error.state === "consumed") {
    return "The saved PoA receipt was already consumed. Request fresh beta game admission.";
  }
  return "The saved PoA receipt was unknown or permanently refused. It was cleared and no access was granted.";
}

function safeStorage(storage) {
  return {
    get() { try { return storage?.getItem?.(RECEIPT_STORAGE_KEY) ?? null; } catch { return null; } },
    set(value) { try { storage?.setItem?.(RECEIPT_STORAGE_KEY, value); } catch { /* volatile session */ } },
    clear() { try { storage?.removeItem?.(RECEIPT_STORAGE_KEY); } catch { /* already volatile */ } },
  };
}

/** Mount optional RPC-attested game admission; no returned value carries governance weight. */
export function mountDreggAdmissionPanel(root, {
  walletsRegistry,
  origin = globalThis.location?.origin,
  endpoints = DEFAULT_DREGG_ADMISSION_ENDPOINTS,
  fetchImpl = globalThis.fetch,
  storage = globalThis.sessionStorage,
  now = () => Date.now(),
  setTimeoutImpl = globalThis.setTimeout,
  clearTimeoutImpl = globalThis.clearTimeout,
  classicProviderSource = [],
  getDreggIdentity = async () => {
    const provider = globalThis.window?.dregg;
    if (!provider || typeof provider.getActiveIdentity !== "function") {
      throw new Error("active Dregg expedition officer is unavailable");
    }
    return provider.getActiveIdentity();
  },
  onAdmissionChange = () => {},
} = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("panel root is required");
  if (!walletsRegistry || typeof walletsRegistry.get !== "function") throw new TypeError("Wallet Standard registry is required");
  if (typeof fetchImpl !== "function") throw new TypeError("fetch implementation is required");
  if (typeof setTimeoutImpl !== "function" || typeof clearTimeoutImpl !== "function") {
    throw new TypeError("credential expiry timers are required");
  }
  if (typeof getDreggIdentity !== "function") throw new TypeError("Dregg identity reader is required");
  const trustedOrigin = new URL(requiredText("origin", origin)).origin;
  const urls = Object.freeze({
    challenge: resolveSameOriginAdmissionEndpoint(endpoints.challenge, trustedOrigin),
    verify: resolveSameOriginAdmissionEndpoint(endpoints.verify, trustedOrigin),
    statusPrefix: resolveSameOriginAdmissionEndpoint(endpoints.statusPrefix, trustedOrigin),
  });
  const receiptStorage = safeStorage(storage);
  const documentRef = root.ownerDocument ?? globalThis.document;
  if (!documentRef?.createElement) throw new TypeError("DOM document is required");

  const panel = el(documentRef, "section", "dregg-admission");
  panel.setAttribute("aria-labelledby", "dregg-admission-title");
  const heading = el(documentRef, "div", "dregg-admission__heading");
  const headingCopy = el(documentRef, "div");
  const eyebrow = el(documentRef, "p", "dregg-admission__eyebrow", "OPTIONAL BETA ADMISSION // $DREGG");
  const title = el(documentRef, "h2", undefined, "Request expedition clearance");
  title.id = "dregg-admission-title";
  headingCopy.append(eyebrow, title);
  heading.append(headingCopy, el(documentRef, "span", "dregg-admission__grade", "RPC-ATTESTED"));
  const intro = el(documentRef, "p", "dregg-admission__intro",
    "Bind one Solana wallet to the active Dregg expedition officer, then sign the node's short-lived challenge. The node checks the exact Token-2022 mint at a finalized slot.");
  const boundary = el(documentRef, "div", "dregg-admission__boundary");
  boundary.setAttribute("role", "note");
  boundary.append(
    el(documentRef, "b", undefined, "GAME ADMISSION, NOT GOVERNANCE"),
    el(documentRef, "p", undefined,
      "This panel never displays or asserts a token balance and cannot create voting weight. Its local-node receipt is bound to one Dregg officer but is not federation-verifiable eligibility; Galley holder sponsorship remains closed."),
  );
  const trustList = el(documentRef, "dl", "dregg-admission__trust");
  for (const [term, detail] of [["Officer", "active Dregg identity"], ["Wallet", "Solana Ed25519 signature"], ["Admission", "short-lived"], ["Trust", "node RPC attestation"]]) {
    const item = el(documentRef, "div");
    item.append(el(documentRef, "dt", undefined, term), el(documentRef, "dd", undefined, detail));
    trustList.append(item);
  }
  const status = el(documentRef, "p", "dregg-admission__status", "Checking local PoA receipt…");
  status.setAttribute("role", "status");
  status.setAttribute("aria-live", "polite");
  status.setAttribute("aria-atomic", "true");
  const walletRegion = el(documentRef, "div", "dregg-admission__wallets");
  walletRegion.setAttribute("aria-labelledby", "dregg-wallet-list-title");
  const walletTitle = el(documentRef, "h3", undefined, "Compatible signing wallets");
  walletTitle.id = "dregg-wallet-list-title";
  const walletList = el(documentRef, "ul", "dregg-admission__wallet-list");
  const refreshButton = button(documentRef, "dregg-admission__secondary", "Refresh wallet list");
  const retryReceiptButton = button(documentRef, "dregg-admission__secondary", "Retry saved receipt");
  retryReceiptButton.hidden = true;
  const signingNote = el(documentRef, "p", "dregg-admission__signing-note",
    "Your wallet signs exact bytes supplied by the same-origin PoA node. This is a message signature, never a transaction.");
  signingNote.id = "dregg-admission-signing-note";
  walletRegion.append(walletTitle, walletList, refreshButton, retryReceiptButton, signingNote);
  const sessionRegion = el(documentRef, "div", "dregg-admission__session");
  sessionRegion.hidden = true;
  const sessionTitle = el(documentRef, "h3", undefined, "Beta game admission active");
  const sessionWallet = el(documentRef, "p", "dregg-admission__wallet");
  const sessionExpiry = el(documentRef, "p", "dregg-admission__expiry");
  const logoutButton = button(documentRef, "dregg-admission__secondary", "Forget PoA receipt");
  sessionRegion.append(sessionTitle, sessionWallet, sessionExpiry, logoutButton);
  panel.append(heading, intro, boundary, trustList, status, walletRegion, sessionRegion);
  root.replaceChildren(panel);

  let savedReceipt = null;
  const savedReceiptText = receiptStorage.get();
  if (savedReceiptText !== null) {
    try { savedReceipt = decodeStoredReceipt(savedReceiptText); }
    catch { receiptStorage.clear(); }
  }
  const state = {
    busy: false,
    credential: null,
    destroyed: false,
    wallets: [],
    savedReceipt,
    expiryTimer: null,
  };
  const unsubscriptions = [];
  function setStatus(kind, message) { status.dataset.state = kind; status.textContent = message; }
  function cancelCredentialExpiry() {
    if (state.expiryTimer !== null) clearTimeoutImpl(state.expiryTimer);
    state.expiryTimer = null;
  }
  function setBusy(value) {
    state.busy = value;
    panel.setAttribute("aria-busy", String(value));
    refreshButton.disabled = value;
    retryReceiptButton.disabled = value;
    logoutButton.disabled = value;
    for (const row of walletList.children ?? []) if (row.children?.[0]) row.children[0].disabled = value;
  }
  function showSignedOut({ notify = true } = {}) {
    cancelCredentialExpiry();
    state.credential = null;
    walletRegion.hidden = false;
    sessionRegion.hidden = true;
    if (notify) onAdmissionChange(null);
  }
  function credentialExpired(credential) {
    return safeInteger("clock", now()) >= credential.expiresAt * 1000;
  }
  function expireCredential(receiptId) {
    if (state.destroyed || state.credential?.receiptId !== receiptId) return false;
    if (!credentialExpired(state.credential)) {
      scheduleCredentialExpiry(state.credential);
      return false;
    }
    receiptStorage.clear();
    state.savedReceipt = null;
    showSignedOut();
    retryReceiptButton.hidden = true;
    renderWallets();
    setStatus("expired", "The short-lived PoA receipt expired. Request fresh beta game admission.");
    return true;
  }
  function scheduleCredentialExpiry(credential) {
    cancelCredentialExpiry();
    const delay = Math.max(0, credential.expiresAt * 1000 - safeInteger("clock", now()));
    state.expiryTimer = setTimeoutImpl(() => { expireCredential(credential.receiptId); }, delay);
    state.expiryTimer?.unref?.();
  }
  function showCredential(credential) {
    if (credentialExpired(credential)) {
      receiptStorage.clear();
      state.savedReceipt = null;
      showSignedOut();
      retryReceiptButton.hidden = true;
      setStatus("expired", "The short-lived PoA receipt expired. Request fresh beta game admission.");
      return false;
    }
    state.credential = credential;
    walletRegion.hidden = true;
    sessionRegion.hidden = false;
    sessionWallet.textContent = `Wallet ${abbreviated(credential.walletAddress)}`;
    sessionWallet.textContent += ` // officer ${credential.playerPublicKey.slice(0, 8)}…${credential.playerPublicKey.slice(-8)}`;
    sessionExpiry.textContent = `Short-lived access ends ${new Date(credential.expiresAt * 1000).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" })}.`;
    setStatus("admitted", "Your holding was checked against a finalized Solana read, and you are admitted. It grants no Galley sponsorship and no say in anything.");
    onAdmissionChange(credential);
    scheduleCredentialExpiry(credential);
    return true;
  }
  function renderWallets() {
    if (state.destroyed) return [];
    state.wallets = discoverDreggWallets(walletsRegistry, classicProviderSource);
    walletList.replaceChildren(...state.wallets.map((wallet, index) => {
      const row = el(documentRef, "li");
      const safeName = typeof wallet.name === "string" && wallet.name.length > 0 && wallet.name.length <= 80
        ? wallet.name : `Solana wallet ${index + 1}`;
      const connectButton = button(documentRef, "dregg-admission__wallet-button", `Connect ${safeName}`);
      connectButton.setAttribute("aria-describedby", signingNote.id);
      connectButton.addEventListener("click", () => { void authenticate(wallet); });
      row.append(connectButton);
      return row;
    }));
    if (!state.savedReceipt && state.wallets.length === 0) {
      setStatus("idle", "No compatible Solana message-signing wallet was discovered.");
    } else if (!state.savedReceipt && !state.credential && !state.busy) {
      setStatus("idle", "Choose a wallet to request optional beta game admission.");
    }
    return state.wallets;
  }

  async function refreshSession() {
    if (state.destroyed || state.busy) return null;
    const binding = state.savedReceipt;
    if (!binding) {
      showSignedOut({ notify: false });
      retryReceiptButton.hidden = true;
      setStatus("idle", state.wallets.length
        ? "Choose a wallet to request optional beta game admission."
        : "No compatible Solana message-signing wallet was discovered.");
      return null;
    }
    setBusy(true);
    setStatus("working", "Checking saved PoA receipt status…");
    try {
      const payload = await jsonRequest(
        fetchImpl,
        `${urls.statusPrefix}${encodeURIComponent(binding.receiptId)}`,
      );
      const result = normalizeHoldingStatus(payload, binding, safeInteger("clock", now()));
      if (!result.credential) throw new InactiveReceiptError(result.state);
      if (!showCredential(result.credential)) return null;
      retryReceiptButton.hidden = true;
      return result.credential;
    } catch (error) {
      const retained = isTransientBackendFailure(error) && !(error instanceof InactiveReceiptError);
      if (!retained) {
        receiptStorage.clear();
        state.savedReceipt = null;
      }
      showSignedOut();
      retryReceiptButton.hidden = !retained;
      setStatus(retained ? "deferred" : "refused", receiptFailureMessage(error, retained));
      return null;
    } finally { setBusy(false); }
  }

  async function authenticate(wallet) {
    if (state.destroyed || state.busy) return null;
    setBusy(true);
    retryReceiptButton.hidden = true;
    setStatus("working", "Reading the active Dregg expedition officer…");
    try {
      const player = normalizePlayerIdentity(await getDreggIdentity());
      setStatus("working", `Connecting a Solana wallet to officer ${player.profileName}…`);
      const session = await connectDreggWallet(wallet, { cluster: "solana:mainnet" });
      setStatus("working", "Requesting a short-lived node challenge…");
      const challengePayload = await jsonRequest(fetchImpl, urls.challenge, {
        method: "POST", body: Object.freeze({ wallet: session.address, player: player.base58 }),
      });
      const challenge = normalizeHoldingChallenge(
        challengePayload,
        { walletAddress: session.address, playerPublicKey: player.publicKeyHex, origin: trustedOrigin },
        safeInteger("clock", now()),
      );
      setStatus("working", "Confirm the non-transaction message signature in your wallet…");
      const signature = await session.signMessage(challenge.signingMessage);
      if (signature.length !== 64) throw new Error("wallet returned a malformed Ed25519 signature");
      setStatus("working", "Waiting for node RPC attestation…");
      const capabilityPayload = await jsonRequest(fetchImpl, urls.verify, {
        method: "POST",
        body: Object.freeze({ challenge_id: challenge.challengeId, signature_base64: bytesToBase64(signature) }),
      });
      const credential = normalizeHoldingCapability(
        capabilityPayload,
        {
          walletAddress: session.address,
          playerPublicKey: player.publicKeyHex,
          playerCell: challenge.playerCell,
        },
        safeInteger("clock", now()),
      );
      state.savedReceipt = Object.freeze({
        receiptId: credential.receiptId,
        walletAddress: credential.walletAddress,
        playerPublicKey: credential.playerPublicKey,
        playerBase58: credential.playerBase58,
        playerCell: credential.playerCell,
      });
      receiptStorage.set(encodeStoredReceipt(
        credential.receiptId,
        credential.walletAddress,
        credential.playerBase58,
        credential.playerCell,
      ));
      if (!showCredential(credential)) return null;
      return credential;
    } catch (error) {
      showSignedOut();
      retryReceiptButton.hidden = !state.savedReceipt;
      setStatus("refused", authenticationFailureMessage(error, Boolean(state.savedReceipt)));
      return null;
    } finally { setBusy(false); }
  }

  function logout() {
    receiptStorage.clear();
    state.savedReceipt = null;
    showSignedOut();
    renderWallets();
    setStatus("idle", "Local PoA receipt forgotten. The node capability was not revoked, and your wallet may remain connected.");
    return true;
  }

  refreshButton.addEventListener("click", renderWallets);
  retryReceiptButton.addEventListener("click", () => { void refreshSession(); });
  logoutButton.addEventListener("click", logout);
  if (typeof walletsRegistry.on === "function") {
    for (const eventName of ["register", "unregister"]) {
      const unsubscribe = walletsRegistry.on(eventName, renderWallets);
      if (typeof unsubscribe === "function") unsubscriptions.push(unsubscribe);
    }
  }
  renderWallets();
  const ready = refreshSession();
  return Object.freeze({
    ready, authenticate, logout, refreshSession, refreshWallets: renderWallets,
    getCredential: () => {
      if (state.credential && expireCredential(state.credential.receiptId)) return null;
      return state.credential;
    },
    getWallets: () => Object.freeze([...state.wallets]),
    destroy() {
      state.destroyed = true;
      cancelCredentialExpiry();
      for (const unsubscribe of unsubscriptions) unsubscribe();
      root.replaceChildren();
    },
  });
}

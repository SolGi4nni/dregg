import {
  DREGG_MINT,
  DREGG_OWNER_BIND_DOMAIN,
  base64ToBytes,
  base58ToBytes,
  bytesToBase64,
  connectDreggWallet,
  discoverDreggWallets,
  normalizeSolanaPublicKey,
} from "./dregg-wallet.js";

export const DREGG_HOLDING_CHALLENGE_FORMAT = "poa-dregg-holding-challenge-v1";
export const DREGG_HOLDING_CAPABILITY_FORMAT = "poa-dregg-holding-capability-v1";
export const DREGG_HOLDING_STATUS_FORMAT = "poa-dregg-holding-status-v1";
export const DREGG_ADMISSION_SCOPE = "poa:beta:game-admission";
export const DREGG_ADMISSION_TRUST_GRADE = "rpcAttested";
export const DREGG_BACKEND_TRUST = "beta-rpc-attested";
export const DREGG_CLUSTER = "solana:mainnet-beta";

/** Beta routes are proxied through `/node/*`; node-internal routes omit `/node`. */
export const DEFAULT_DREGG_ADMISSION_ENDPOINTS = Object.freeze({
  challenge: "/node/api/poa/holding/challenge",
  verify: "/node/api/poa/holding/verify",
  statusPrefix: "/node/api/poa/holding/status/",
});

const RECEIPT_STORAGE_KEY = "poa.dregg.beta-holding-receipt.v1";
const MAX_CHALLENGE_LIFETIME_SECONDS = 15 * 60;
const CLOCK_SKEW_SECONDS = 30;
const encoder = new TextEncoder();

const CHALLENGE_KEYS = Object.freeze([
  "challenge_id", "cluster", "expires_at", "format", "issued_at", "min_context_slot",
  "minimum_raw_balance", "mint", "signing_message_base64", "wallet",
]);
const CAPABILITY_KEYS = Object.freeze([
  "expires_at", "format", "governance_weight_bearing", "issued_at", "mint",
  "receipt_id", "snapshot_slot", "trust", "wallet",
]);
const STATUS_KEYS = Object.freeze([...CAPABILITY_KEYS, "state"].sort());

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

function validateOwnerBindingMessage(message, walletAddress) {
  const domain = encoder.encode(DREGG_OWNER_BIND_DOMAIN);
  const owner = base58ToBytes(walletAddress);
  if (message.length !== domain.length + 64 ||
      !bytesEqual(message.slice(0, domain.length), domain) ||
      !bytesEqual(message.slice(domain.length, domain.length + 32), owner)) {
    throw new Error("node signing message is not the canonical Dregg owner binding for this wallet");
  }
}

function validateWindow(issuedAt, expiresAt, nowSeconds) {
  if (expiresAt <= issuedAt || expiresAt - issuedAt > MAX_CHALLENGE_LIFETIME_SECONDS) {
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
    signingMessage: base64ToBytes(requiredText("signing_message_base64", payload.signing_message_base64)),
    mint: normalizeSolanaPublicKey("mint", payload.mint),
    cluster: requiredText("cluster", payload.cluster),
    minimumRawBalance: decimalRaw("minimum_raw_balance", payload.minimum_raw_balance, { positive: true }),
    minContextSlot: safeInteger("min_context_slot", payload.min_context_slot),
    issuedAt: safeInteger("issued_at", payload.issued_at),
    expiresAt: safeInteger("expires_at", payload.expires_at),
  };
  if (challenge.format !== DREGG_HOLDING_CHALLENGE_FORMAT || challenge.walletAddress !== expected.walletAddress) {
    throw new Error("holding challenge has the wrong format or wallet");
  }
  if (challenge.mint !== DREGG_MINT || challenge.cluster !== DREGG_CLUSTER || challenge.minimumRawBalance !== "1") {
    throw new Error("holding challenge has the wrong mint, cluster, or admission threshold");
  }
  if (challenge.signingMessage.length === 0) throw new Error("holding challenge has an empty signing message");
  validateOwnerBindingMessage(challenge.signingMessage, challenge.walletAddress);
  validateWindow(challenge.issuedAt, challenge.expiresAt, safeNowSeconds(nowMs));
  return Object.freeze(challenge);
}

function admissionCredential({ receiptId, walletAddress, snapshotSlot, issuedAt, expiresAt }) {
  return Object.freeze({
    receiptId,
    walletAddress,
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
  const mint = normalizeSolanaPublicKey("mint", payload.mint);
  const snapshotSlot = safeInteger("snapshot_slot", payload.snapshot_slot);
  const issuedAt = safeInteger("issued_at", payload.issued_at);
  const expiresAt = safeInteger("expires_at", payload.expires_at);
  if (format !== DREGG_HOLDING_CAPABILITY_FORMAT || trust !== DREGG_BACKEND_TRUST ||
      walletAddress !== expected.walletAddress || mint !== DREGG_MINT ||
      payload.governance_weight_bearing !== false) {
    throw new Error("holding capability has unsupported authority or bindings");
  }
  validateWindow(issuedAt, expiresAt, safeNowSeconds(nowMs));
  return admissionCredential({ receiptId, walletAddress, snapshotSlot, issuedAt, expiresAt });
}

/** Active status can restore beta admission; expired/consumed receipts cannot. */
export function normalizeHoldingStatus(payload, expected, nowMs = Date.now()) {
  if (!payload || typeof payload !== "object") throw new TypeError("holding status is required");
  exactKeys("holding status", payload, STATUS_KEYS);
  if (requiredText("format", payload.format) !== DREGG_HOLDING_STATUS_FORMAT ||
      base64Url32("receipt_id", payload.receipt_id) !== expected.receiptId) {
    throw new Error("holding status has the wrong format or receipt");
  }
  const state = requiredText("state", payload.state);
  if (!["active", "expired", "consumed"].includes(state)) throw new Error("holding status has an unknown state");
  if (state !== "active") return Object.freeze({ state, credential: null });
  const { state: _state, ...capabilityFields } = payload;
  const capabilityShape = { ...capabilityFields, format: DREGG_HOLDING_CAPABILITY_FORMAT };
  return Object.freeze({
    state,
    credential: normalizeHoldingCapability(capabilityShape, { walletAddress: payload.wallet }, nowMs),
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
  allowUnknownReceipt = false,
} = {}) {
  const response = await fetchImpl(url, {
    method,
    credentials: "same-origin",
    cache: "no-store",
    redirect: "error",
    headers: Object.freeze({ Accept: "application/json", "Content-Type": "application/json" }),
    ...(body === undefined ? {} : { body: JSON.stringify(body) }),
  });
  if (allowUnknownReceipt && response.status === 404) return null;
  if (!response.ok) throw new Error(`holding backend refused request (${response.status})`);
  const contentType = response.headers?.get?.("content-type") ?? "";
  if (!contentType.toLowerCase().includes("application/json")) throw new Error("holding backend did not return JSON");
  return response.json();
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
  onAdmissionChange = () => {},
} = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("panel root is required");
  if (!walletsRegistry || typeof walletsRegistry.get !== "function") throw new TypeError("Wallet Standard registry is required");
  if (typeof fetchImpl !== "function") throw new TypeError("fetch implementation is required");
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
    "Sign the node's short-lived challenge. The node checks the exact Token-2022 mint at a finalized slot and returns only a beta game receipt.");
  const boundary = el(documentRef, "div", "dregg-admission__boundary");
  boundary.setAttribute("role", "note");
  boundary.append(
    el(documentRef, "b", undefined, "GAME ADMISSION, NOT GOVERNANCE"),
    el(documentRef, "p", undefined,
      "This panel never displays or asserts a token balance and cannot create voting weight. Governance requires a Dregg-accepted anchored accounts proof."),
  );
  const trustList = el(documentRef, "dl", "dregg-admission__trust");
  for (const [term, detail] of [["Wallet", "Ed25519 signature"], ["Admission", "short-lived"], ["Trust", "node RPC attestation"]]) {
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
  const signingNote = el(documentRef, "p", "dregg-admission__signing-note",
    "Your wallet signs exact bytes supplied by the same-origin PoA node. This is a message signature, never a transaction.");
  signingNote.id = "dregg-admission-signing-note";
  walletRegion.append(walletTitle, walletList, refreshButton, signingNote);
  const sessionRegion = el(documentRef, "div", "dregg-admission__session");
  sessionRegion.hidden = true;
  const sessionTitle = el(documentRef, "h3", undefined, "Beta game admission active");
  const sessionWallet = el(documentRef, "p", "dregg-admission__wallet");
  const sessionExpiry = el(documentRef, "p", "dregg-admission__expiry");
  const logoutButton = button(documentRef, "dregg-admission__secondary", "Forget PoA receipt");
  sessionRegion.append(sessionTitle, sessionWallet, sessionExpiry, logoutButton);
  panel.append(heading, intro, boundary, trustList, status, walletRegion, sessionRegion);
  root.replaceChildren(panel);

  const state = { busy: false, credential: null, destroyed: false, wallets: [], receiptId: receiptStorage.get() };
  const unsubscriptions = [];
  function setStatus(kind, message) { status.dataset.state = kind; status.textContent = message; }
  function setBusy(value) {
    state.busy = value;
    panel.setAttribute("aria-busy", String(value));
    refreshButton.disabled = value;
    logoutButton.disabled = value;
    for (const row of walletList.children ?? []) if (row.children?.[0]) row.children[0].disabled = value;
  }
  function showSignedOut({ notify = true } = {}) {
    state.credential = null;
    walletRegion.hidden = false;
    sessionRegion.hidden = true;
    if (notify) onAdmissionChange(null);
  }
  function showCredential(credential) {
    state.credential = credential;
    state.receiptId = credential.receiptId;
    walletRegion.hidden = true;
    sessionRegion.hidden = false;
    sessionWallet.textContent = `Wallet ${abbreviated(credential.walletAddress)}`;
    sessionExpiry.textContent = `Short-lived access ends ${new Date(credential.expiresAt * 1000).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" })}.`;
    setStatus("admitted", "RPC-attested beta game receipt active. No governance authority granted.");
    onAdmissionChange(credential);
  }
  function renderWallets() {
    if (state.destroyed) return [];
    state.wallets = discoverDreggWallets(walletsRegistry);
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
    if (state.wallets.length === 0) setStatus("idle", "No compatible Solana message-signing wallet was discovered.");
    else if (!state.credential && !state.busy) setStatus("idle", "Choose a wallet to request optional beta game admission.");
    return state.wallets;
  }

  async function refreshSession() {
    if (state.destroyed || state.busy) return null;
    const receiptId = state.receiptId ?? receiptStorage.get();
    if (!receiptId) {
      showSignedOut({ notify: false });
      setStatus("idle", state.wallets.length
        ? "Choose a wallet to request optional beta game admission."
        : "No compatible Solana message-signing wallet was discovered.");
      return null;
    }
    setBusy(true);
    setStatus("working", "Checking saved PoA receipt status…");
    try {
      const validReceiptId = base64Url32("receipt_id", receiptId);
      const payload = await jsonRequest(fetchImpl, `${urls.statusPrefix}${encodeURIComponent(validReceiptId)}`, { allowUnknownReceipt: true });
      if (payload === null) throw new Error("unknown receipt");
      const result = normalizeHoldingStatus(payload, { receiptId: validReceiptId }, safeInteger("clock", now()));
      if (!result.credential) throw new Error(`receipt ${result.state}`);
      showCredential(result.credential);
      return result.credential;
    } catch {
      receiptStorage.clear();
      state.receiptId = null;
      showSignedOut();
      setStatus("refused", "Saved PoA receipt was unavailable, expired, or refused. No access was granted.");
      return null;
    } finally { setBusy(false); }
  }

  async function authenticate(wallet) {
    if (state.destroyed || state.busy) return null;
    setBusy(true);
    setStatus("working", "Connecting wallet…");
    try {
      const session = await connectDreggWallet(wallet, { cluster: "solana:mainnet" });
      setStatus("working", "Requesting a short-lived node challenge…");
      const challengePayload = await jsonRequest(fetchImpl, urls.challenge, {
        method: "POST", body: Object.freeze({ wallet: session.address }),
      });
      const challenge = normalizeHoldingChallenge(
        challengePayload,
        { walletAddress: session.address },
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
        { walletAddress: session.address },
        safeInteger("clock", now()),
      );
      state.receiptId = credential.receiptId;
      receiptStorage.set(credential.receiptId);
      showCredential(credential);
      return credential;
    } catch {
      receiptStorage.clear();
      state.receiptId = null;
      showSignedOut();
      setStatus("refused", "Wallet proof was cancelled, unavailable, or refused. No access was granted.");
      return null;
    } finally { setBusy(false); }
  }

  function logout() {
    receiptStorage.clear();
    state.receiptId = null;
    showSignedOut();
    renderWallets();
    setStatus("idle", "Local PoA receipt forgotten. The node capability was not revoked, and your wallet may remain connected.");
    return true;
  }

  refreshButton.addEventListener("click", renderWallets);
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
    getCredential: () => state.credential,
    getWallets: () => Object.freeze([...state.wallets]),
    destroy() {
      state.destroyed = true;
      for (const unsubscribe of unsubscriptions) unsubscribe();
      root.replaceChildren();
    },
  });
}

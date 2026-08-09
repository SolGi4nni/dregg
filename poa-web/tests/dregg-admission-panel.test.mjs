import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  DEFAULT_DREGG_ADMISSION_ENDPOINTS,
  DREGG_ADMISSION_SCOPE,
  DREGG_HOLDING_CAPABILITY_FORMAT,
  DREGG_HOLDING_CHALLENGE_FORMAT,
  DREGG_HOLDING_STATUS_FORMAT,
  mountDreggAdmissionPanel,
  normalizeHoldingCapability,
  normalizeHoldingChallenge,
  resolveSameOriginAdmissionEndpoint,
} from "../src/dregg-admission-panel.js";
import { DREGG_MINT, base64ToBytes, bytesToBase64 } from "../src/dregg-wallet.js";

const origin = "https://beta.pathofangels.network";
const nowMs = Date.parse("2026-08-04T15:42:00.000Z");
const nowSeconds = Math.floor(nowMs / 1000);
const crossWire = JSON.parse(readFileSync(new URL("./fixtures/dregg-holding-cross-wire-v2.json", import.meta.url), "utf8"));
const walletAddress = crossWire.challenge.wallet;
const playerPublicKey = "c050c5637a44fa8629fff3cccce2300cb362a63d99d95fc54145266f4332445a";
const playerBase58 = "DwiiKAQ7MXWDnCQiZcH81bF1pMyf6mYBLSKNKAxSEWzd";
const playerCell = "aRGH51etufHsmWISQhQnEfNzAi6UhfhyaM24efjhGTM";
const challengeId = crossWire.challenge.challenge_id;
const receiptId = crossWire.capability.receipt_id;
const signingBytes = base64ToBytes(crossWire.challenge.signing_message_base64);
const signatureBytes = new Uint8Array(64).fill(1);

function storedReceipt(wallet = walletAddress, receipt = receiptId) {
  return JSON.stringify({
    format: "poa-dregg-holding-session-v2",
    player: playerBase58,
    player_cell: playerCell,
    receipt_id: receipt,
    wallet,
  });
}

const challenge = Object.freeze(structuredClone(crossWire.challenge));

function capability(overrides = {}) {
  return { ...structuredClone(crossWire.capability), ...overrides };
}

function status(overrides = {}) {
  return { ...structuredClone(crossWire.status), ...overrides };
}

const getDreggIdentity = async () => ({ profileName: "marrow", publicKeyHex: playerPublicKey });

class FakeElement {
  constructor(tagName, ownerDocument) {
    this.tagName = tagName.toUpperCase();
    this.ownerDocument = ownerDocument;
    this.children = [];
    this.attributes = new Map();
    this.dataset = {};
    this.className = "";
    this.textContent = "";
    this.hidden = false;
    this.disabled = false;
    this.listeners = new Map();
    this.id = "";
    this.type = "";
  }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  addEventListener(name, callback) {
    this.listeners.set(name, [...(this.listeners.get(name) ?? []), callback]);
  }
  dispatch(name) {
    const event = { preventDefault() { this.defaultPrevented = true; } };
    for (const callback of this.listeners.get(name) ?? []) callback(event);
    return event;
  }
}

function fakeDom() {
  const documentRef = { createElement: (tag) => new FakeElement(tag, documentRef) };
  return { documentRef, root: new FakeElement("div", documentRef) };
}

function all(root) { return [root, ...root.children.flatMap(all)]; }

function response(statusCode, payload, contentType = "application/json; charset=utf-8") {
  return {
    status: statusCode,
    ok: statusCode >= 200 && statusCode < 300,
    headers: { get: (name) => name.toLowerCase() === "content-type" ? contentType : null },
    async json() { return payload; },
  };
}

function standardWallet(signatures = []) {
  const account = { address: walletAddress, chains: ["solana:mainnet"], features: ["solana:signMessage"] };
  return {
    name: "Fixture Standard",
    accounts: [account],
    features: {
      "standard:connect": { connect: async () => ({ accounts: [account] }) },
      "solana:signMessage": {
        signMessage: async ({ message }) => {
          signatures.push(message);
          return [{ signature: signatureBytes }];
        },
      },
    },
  };
}

function memoryStorage(initial = null) {
  let value = initial;
  return {
    getItem: () => value,
    setItem: (_key, next) => { value = next; },
    removeItem: () => { value = null; },
    value: () => value,
  };
}

test("configured holder endpoints are exact same-origin beta proxy routes", () => {
  assert.equal(DEFAULT_DREGG_ADMISSION_ENDPOINTS.challenge, "/node/api/poa/holding/challenge");
  assert.equal(DEFAULT_DREGG_ADMISSION_ENDPOINTS.verify, "/node/api/poa/holding/verify");
  assert.equal(DEFAULT_DREGG_ADMISSION_ENDPOINTS.statusPrefix, "/node/api/poa/holding/status/");
  assert.equal(resolveSameOriginAdmissionEndpoint(DEFAULT_DREGG_ADMISSION_ENDPOINTS.challenge, origin),
    `${origin}/node/api/poa/holding/challenge`);
  assert.throws(() => resolveSameOriginAdmissionEndpoint("https://evil.invalid/session", origin), /same-origin/u);
});

test("challenge validation binds exact wallet/mint/cluster/window and signing bytes", () => {
  const parsed = normalizeHoldingChallenge(challenge, { walletAddress, playerPublicKey }, nowMs);
  assert.deepEqual(parsed.signingMessage, signingBytes);
  assert.equal(parsed.challengeId, challengeId);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, wallet: DREGG_MINT }, { walletAddress, playerPublicKey }, nowMs), /wallet/u);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, mint: walletAddress }, { walletAddress, playerPublicKey }, nowMs), /mint/u);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, signing_message_base64: "***" }, { walletAddress, playerPublicKey }, nowMs), /base64/u);
  const wrongBinding = Uint8Array.from(signingBytes, (value, index) => index === signingBytes.length - 1 ? value ^ 1 : value);
  assert.throws(() => normalizeHoldingChallenge({
    ...challenge, signing_message_base64: bytesToBase64(wrongBinding),
  }, { walletAddress, playerPublicKey }, nowMs), /wallet consent/u);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, player: DREGG_MINT }, { walletAddress, playerPublicKey }, nowMs), /officer/u);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, expires_at: nowSeconds + 3600 }, { walletAddress, playerPublicKey }, nowMs), /short-lived/u);
  assert.throws(() => normalizeHoldingChallenge({
    ...challenge,
    issued_at: nowSeconds,
    expires_at: nowSeconds + 301,
  }, { walletAddress, playerPublicKey }, nowMs), /short-lived/u);
});

test("capability yields game admission without exposing returned raw balance", () => {
  const credential = normalizeHoldingCapability(capability(), { walletAddress, playerPublicKey, playerCell }, nowMs);
  assert.equal(credential.scope, DREGG_ADMISSION_SCOPE);
  assert.equal(credential.trustGrade, "rpcAttested");
  assert.equal(credential.backendTrust, "beta-rpc-attested");
  assert.equal(credential.governanceWeightBearing, false);
  assert.equal(credential.balanceClaimBearing, false);
  assert.equal(credential.sponsorshipBearing, false);
  assert.equal(credential.playerPublicKey, playerPublicKey);
  assert.equal("rawBalance" in credential, false);
  assert.equal("raw_balance" in credential, false);
  assert.throws(() => normalizeHoldingCapability({ ...capability(), raw_balance: "1" }, { walletAddress, playerPublicKey, playerCell }, nowMs), /unexpected/u);
  assert.throws(() => normalizeHoldingCapability(capability({ governance_weight_bearing: true }), { walletAddress, playerPublicKey, playerCell }, nowMs), /authority/u);
  assert.throws(() => normalizeHoldingCapability(capability({ trust: "consensus-proven" }), { walletAddress, playerPublicKey, playerCell }, nowMs), /authority/u);
  assert.throws(() => normalizeHoldingCapability(capability({ player: DREGG_MINT }), { walletAddress, playerPublicKey, playerCell }, nowMs), /bindings/u);
  assert.throws(() => normalizeHoldingCapability(capability({ player_cell: "A".repeat(43) }), { walletAddress, playerPublicKey, playerCell }, nowMs), /bindings/u);
  assert.throws(() => normalizeHoldingCapability(capability({
    issued_at: nowSeconds,
    expires_at: nowSeconds + 121,
  }), { walletAddress, playerPublicKey, playerCell }, nowMs), /short-lived/u);
});

test("active Dregg identity is required before wallet connection or network access", async () => {
  const { root } = fakeDom();
  const wallet = standardWallet();
  let walletConnections = 0;
  let fetches = 0;
  const originalConnect = wallet.features["standard:connect"].connect;
  wallet.features["standard:connect"].connect = async (...args) => {
    walletConnections += 1;
    return originalConnect(...args);
  };
  const controller = mountDreggAdmissionPanel(root, {
    walletsRegistry: { get: () => [wallet] }, origin, now: () => nowMs, storage: memoryStorage(),
    getDreggIdentity: async () => { throw new Error("active Dregg expedition officer is unavailable"); },
    fetchImpl: async () => { fetches += 1; throw new Error("must not fetch"); },
  });
  await controller.ready;
  assert.equal(await controller.authenticate(wallet), null);
  assert.equal(walletConnections, 0);
  assert.equal(fetches, 0);
  assert.match(all(root).find((node) => node.attributes.get("role") === "status").textContent,
    /Unlock or create an active Dregg expedition officer/u);
});

test("panel mounts an accessible Wallet Standard choice and truthful boundary", async () => {
  const { root } = fakeDom();
  const wallet = standardWallet();
  const controller = mountDreggAdmissionPanel(root, {
    walletsRegistry: { get: () => [wallet] }, origin, now: () => nowMs,
    fetchImpl: async () => { throw new Error("no fetch without receipt"); },
    storage: memoryStorage(),
  });
  await controller.ready;
  const nodes = all(root);
  const panel = nodes.find((node) => node.tagName === "SECTION");
  const live = nodes.find((node) => node.attributes.get("role") === "status");
  const connect = nodes.find((node) => node.tagName === "BUTTON" && /Connect Fixture Standard/u.test(node.textContent));
  const text = nodes.map((node) => node.textContent).join("\n");
  assert.equal(panel.attributes.get("aria-labelledby"), "dregg-admission-title");
  assert.equal(live.attributes.get("aria-live"), "polite");
  assert.equal(connect.type, "button");
  assert.match(connect.attributes.get("aria-describedby"), /signing-note/u);
  assert.match(text, /GAME ADMISSION, NOT GOVERNANCE/u);
  assert.match(text, /never displays or asserts a token balance/u);
  assert.match(live.textContent, /Choose a wallet/u);
});

test("exact node wire signs once, sends no balance fields, and stores only wallet-bound receipt metadata", async () => {
  const { root } = fakeDom();
  const signatures = [];
  const wallet = standardWallet(signatures);
  const storage = memoryStorage();
  const requests = [];
  const fetchImpl = async (url, options) => {
    requests.push({ url, options });
    const pathname = new URL(url).pathname;
    if (pathname.endsWith("/challenge")) {
      assert.deepEqual(JSON.parse(options.body), { wallet: walletAddress, player: playerBase58 });
      return response(201, challenge);
    }
    if (pathname.endsWith("/verify")) {
      assert.deepEqual(JSON.parse(options.body), {
        challenge_id: challengeId,
        signature_base64: bytesToBase64(signatureBytes),
      });
      return response(200, capability());
    }
    throw new Error("unexpected endpoint");
  };
  const controller = mountDreggAdmissionPanel(root, {
    walletsRegistry: { get: () => [wallet] }, origin, now: () => nowMs, fetchImpl, storage, getDreggIdentity,
  });
  await controller.ready;
  const admitted = await controller.authenticate(wallet);
  assert.equal(signatures.length, 1);
  assert.deepEqual(signatures[0], signingBytes);
  assert.equal(admitted.scope, DREGG_ADMISSION_SCOPE);
  assert.equal("rawBalance" in admitted, false);
  assert.deepEqual(JSON.parse(storage.value()), {
    format: "poa-dregg-holding-session-v2",
    player: playerBase58,
    player_cell: playerCell,
    receipt_id: receiptId,
    wallet: walletAddress,
  });
  assert.ok(requests.every(({ url }) => new URL(url).origin === origin));
  assert.ok(requests.every(({ options }) => options.credentials === "same-origin" && options.redirect === "error"));
  const surface = all(root).map((node) => node.textContent).join("\n");
  assert.doesNotMatch(surface, /raw balance|raw_balance/iu);
  // An admitted holder is admitted and nothing more: the surface must still
  // disclaim Galley sponsorship and any say in how anything is decided.
  assert.match(surface, /grants no Galley sponsorship and no say in anything/u);

  assert.equal(controller.logout(), true);
  assert.equal(controller.getCredential(), null);
  assert.equal(storage.value(), null);
  assert.match(all(root).find((node) => node.attributes.get("role") === "status").textContent, /not revoked/u);
});

test("saved receipt restores only through active status and unknown status fails closed", async () => {
  const { root } = fakeDom();
  const storage = memoryStorage(storedReceipt());
  let calls = 0;
  const controller = mountDreggAdmissionPanel(root, {
    walletsRegistry: { get: () => [standardWallet()] }, origin, now: () => nowMs, storage,
    fetchImpl: async (url) => {
      calls += 1;
      assert.equal(new URL(url).pathname, `/node/api/poa/holding/status/${receiptId}`);
      return response(200, status());
    },
  });
  const restored = await controller.ready;
  assert.equal(calls, 1);
  assert.equal(restored.receiptId, receiptId);
  assert.equal("rawBalance" in restored, false);

  controller.logout();
  storage.setItem("ignored", storedReceipt());
  const unavailable = mountDreggAdmissionPanel(fakeDom().root, {
    walletsRegistry: { get: () => [standardWallet()] }, origin, now: () => nowMs, storage,
    fetchImpl: async () => response(404, { code: "unknown_receipt", message: "unknown" }),
  });
  assert.equal(await unavailable.ready, null);
  assert.equal(unavailable.getCredential(), null);
  assert.equal(storage.value(), null);
});

test("legacy wallet-only receipt is cleared and can never restore sponsorship", async () => {
  const legacy = JSON.stringify({
    format: "poa-dregg-holding-session-v1",
    receipt_id: receiptId,
    wallet: walletAddress,
  });
  const storage = memoryStorage(legacy);
  let fetches = 0;
  const controller = mountDreggAdmissionPanel(fakeDom().root, {
    walletsRegistry: { get: () => [standardWallet()] }, origin, now: () => nowMs, storage,
    fetchImpl: async () => { fetches += 1; throw new Error("legacy receipt must not reach status"); },
  });
  assert.equal(await controller.ready, null);
  assert.equal(controller.getCredential(), null);
  assert.equal(storage.value(), null);
  assert.equal(fetches, 0);
});

test("saved receipt is independently wallet-bound and response substitution fails closed", async () => {
  const storage = memoryStorage(storedReceipt());
  const controller = mountDreggAdmissionPanel(fakeDom().root, {
    walletsRegistry: { get: () => [standardWallet()] }, origin, now: () => nowMs, storage,
    fetchImpl: async () => response(200, status({ wallet: DREGG_MINT })),
  });
  assert.equal(await controller.ready, null);
  assert.equal(controller.getCredential(), null);
  assert.equal(storage.value(), storedReceipt(), "protocol drift retains the independently bound receipt for retry");
});

test("transient status refusal retains the wallet-bound receipt but permanent 4xx clears it", async () => {
  const { root } = fakeDom();
  const storage = memoryStorage(storedReceipt());
  let nextResponse = response(429, { code: "rate_limited", message: "later" });
  const controller = mountDreggAdmissionPanel(root, {
    walletsRegistry: { get: () => [standardWallet()] }, origin, now: () => nowMs, storage,
    fetchImpl: async () => nextResponse,
  });
  assert.equal(await controller.ready, null);
  assert.equal(storage.value(), storedReceipt());
  const retry = all(root).find((node) => node.tagName === "BUTTON" && node.textContent === "Retry saved receipt");
  assert.equal(retry.hidden, false);
  assert.match(all(root).find((node) => node.attributes.get("role") === "status").textContent, /retained/u);

  nextResponse = response(502, { code: "rpc_refused", message: "later" });
  assert.equal(await controller.refreshSession(), null);
  assert.equal(storage.value(), storedReceipt());

  nextResponse = response(503, { code: "rpc_unavailable", message: "later" });
  assert.equal(await controller.refreshSession(), null);
  assert.equal(storage.value(), storedReceipt());

  nextResponse = response(410, { code: "expired", message: "gone" });
  assert.equal(await controller.refreshSession(), null);
  assert.equal(storage.value(), null);
  assert.match(all(root).find((node) => node.attributes.get("role") === "status").textContent, /cleared/u);
});

test("credential expiry timer and on-read guard close local admission and notify null", async () => {
  const { root } = fakeDom();
  const storage = memoryStorage();
  const notifications = [];
  let currentMs = nowMs;
  let scheduled = null;
  const timers = {
    setTimeoutImpl(callback, delay) {
      scheduled = { callback, delay, unref() {} };
      return scheduled;
    },
    clearTimeoutImpl(handle) { if (scheduled === handle) scheduled = null; },
  };
  const wallet = standardWallet();
  const controller = mountDreggAdmissionPanel(root, {
    walletsRegistry: { get: () => [wallet] }, origin, now: () => currentMs, storage,
    onAdmissionChange: (value) => notifications.push(value), getDreggIdentity,
    ...timers,
    fetchImpl: async (url) => new URL(url).pathname.endsWith("/challenge")
      ? response(201, challenge)
      : response(200, capability()),
  });
  await controller.ready;
  const admitted = await controller.authenticate(wallet);
  assert.equal(controller.getCredential(), admitted);
  assert.equal(scheduled.delay, admitted.expiresAt * 1000 - currentMs);

  currentMs = admitted.expiresAt * 1000;
  assert.equal(controller.getCredential(), null, "on-read guard closes before timer delivery");
  assert.equal(storage.value(), null);
  assert.equal(notifications.at(-1), null);
  assert.match(all(root).find((node) => node.attributes.get("role") === "status").textContent, /expired/u);

  const secondStorage = memoryStorage();
  const secondNotifications = [];
  currentMs = nowMs;
  scheduled = null;
  const second = mountDreggAdmissionPanel(fakeDom().root, {
    walletsRegistry: { get: () => [wallet] }, origin, now: () => currentMs, storage: secondStorage,
    onAdmissionChange: (value) => secondNotifications.push(value), getDreggIdentity,
    ...timers,
    fetchImpl: async (url) => new URL(url).pathname.endsWith("/challenge")
      ? response(201, challenge)
      : response(200, capability()),
  });
  await second.ready;
  const secondCredential = await second.authenticate(wallet);
  const expiryCallback = scheduled.callback;
  currentMs = secondCredential.expiresAt * 1000;
  expiryCallback();
  assert.equal(second.getCredential(), null, "timer delivery closes admission without a read");
  assert.equal(secondStorage.value(), null);
  assert.equal(secondNotifications.at(-1), null);
});

test("unavailable or over-claiming node response leaves admission closed", async () => {
  const { root } = fakeDom();
  const wallet = standardWallet();
  const fetchImpl = async (url) => {
    if (new URL(url).pathname.endsWith("/challenge")) return response(201, challenge);
    return response(200, capability({ governance_weight_bearing: true }));
  };
  const controller = mountDreggAdmissionPanel(root, {
    walletsRegistry: { get: () => [wallet] }, origin, now: () => nowMs, fetchImpl, storage: memoryStorage(), getDreggIdentity,
  });
  await controller.ready;
  assert.equal(await controller.authenticate(wallet), null);
  assert.equal(controller.getCredential(), null);
  const live = all(root).find((node) => node.attributes.get("role") === "status");
  assert.match(live.textContent, /No access was granted/u);
});

test("panel CSS preserves touch, focus, mobile, and reduced-motion accessibility", async () => {
  const css = await readFile(new URL("../dregg-admission-panel.css", import.meta.url), "utf8");
  assert.match(css, /min-height:\s*48px/u);
  assert.match(css, /touch-action:\s*manipulation/u);
  assert.match(css, /:focus-visible/u);
  assert.match(css, /@media\s*\(max-width:/u);
  assert.match(css, /prefers-reduced-motion/u);
});

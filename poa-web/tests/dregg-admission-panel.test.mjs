import assert from "node:assert/strict";
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
import { DREGG_MINT, buildDreggOwnerBindingMessage, bytesToBase64 } from "../src/dregg-wallet.js";

const origin = "https://beta.pathofangels.network";
const nowMs = Date.parse("2026-08-04T13:02:00.000Z");
const nowSeconds = Math.floor(nowMs / 1000);
const walletAddress = "11111111111111111111111111111111";
const challengeId = "A".repeat(43);
const receiptId = bytesToBase64(new Uint8Array(32).fill(1))
  .replace(/\+/gu, "-").replace(/\//gu, "_").replace(/=+$/u, "");
const signingBytes = buildDreggOwnerBindingMessage(walletAddress, DREGG_MINT);
const signatureBytes = new Uint8Array(64).fill(1);

const challenge = Object.freeze({
  format: DREGG_HOLDING_CHALLENGE_FORMAT,
  challenge_id: challengeId,
  wallet: walletAddress,
  signing_message_base64: bytesToBase64(signingBytes),
  mint: DREGG_MINT,
  cluster: "solana:mainnet-beta",
  minimum_raw_balance: "1",
  min_context_slot: 420000000,
  issued_at: nowSeconds - 30,
  expires_at: nowSeconds + 90,
});

function capability(overrides = {}) {
  return {
    format: DREGG_HOLDING_CAPABILITY_FORMAT,
    receipt_id: receiptId,
    trust: "beta-rpc-attested",
    wallet: walletAddress,
    mint: DREGG_MINT,
    snapshot_slot: 420000001,
    issued_at: nowSeconds - 10,
    expires_at: nowSeconds + 110,
    governance_weight_bearing: false,
    ...overrides,
  };
}

function status(overrides = {}) {
  return {
    ...capability(),
    format: DREGG_HOLDING_STATUS_FORMAT,
    state: "active",
    ...overrides,
  };
}

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
  const parsed = normalizeHoldingChallenge(challenge, { walletAddress }, nowMs);
  assert.deepEqual(parsed.signingMessage, signingBytes);
  assert.equal(parsed.challengeId, challengeId);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, wallet: DREGG_MINT }, { walletAddress }, nowMs), /wallet/u);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, mint: walletAddress }, { walletAddress }, nowMs), /mint/u);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, signing_message_base64: "AAAA=" }, { walletAddress }, nowMs), /base64/u);
  const wrongBinding = buildDreggOwnerBindingMessage(DREGG_MINT, walletAddress);
  assert.throws(() => normalizeHoldingChallenge({
    ...challenge, signing_message_base64: bytesToBase64(wrongBinding),
  }, { walletAddress }, nowMs), /owner binding/u);
  assert.throws(() => normalizeHoldingChallenge({ ...challenge, expires_at: nowSeconds + 3600 }, { walletAddress }, nowMs), /short-lived/u);
});

test("capability yields game admission without exposing returned raw balance", () => {
  const credential = normalizeHoldingCapability(capability(), { walletAddress }, nowMs);
  assert.equal(credential.scope, DREGG_ADMISSION_SCOPE);
  assert.equal(credential.trustGrade, "rpcAttested");
  assert.equal(credential.backendTrust, "beta-rpc-attested");
  assert.equal(credential.governanceWeightBearing, false);
  assert.equal(credential.balanceClaimBearing, false);
  assert.equal("rawBalance" in credential, false);
  assert.equal("raw_balance" in credential, false);
  assert.throws(() => normalizeHoldingCapability({ ...capability(), raw_balance: "1" }, { walletAddress }, nowMs), /unexpected/u);
  assert.throws(() => normalizeHoldingCapability(capability({ governance_weight_bearing: true }), { walletAddress }, nowMs), /authority/u);
  assert.throws(() => normalizeHoldingCapability(capability({ trust: "consensus-proven" }), { walletAddress }, nowMs), /authority/u);
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

test("exact node wire signs once, sends no browser balance fields, and stores only receipt id", async () => {
  const { root } = fakeDom();
  const signatures = [];
  const wallet = standardWallet(signatures);
  const storage = memoryStorage();
  const requests = [];
  const fetchImpl = async (url, options) => {
    requests.push({ url, options });
    const pathname = new URL(url).pathname;
    if (pathname.endsWith("/challenge")) {
      assert.deepEqual(JSON.parse(options.body), { wallet: walletAddress });
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
    walletsRegistry: { get: () => [wallet] }, origin, now: () => nowMs, fetchImpl, storage,
  });
  await controller.ready;
  const admitted = await controller.authenticate(wallet);
  assert.equal(signatures.length, 1);
  assert.deepEqual(signatures[0], signingBytes);
  assert.equal(admitted.scope, DREGG_ADMISSION_SCOPE);
  assert.equal("rawBalance" in admitted, false);
  assert.equal(storage.value(), receiptId);
  assert.ok(requests.every(({ url }) => new URL(url).origin === origin));
  assert.ok(requests.every(({ options }) => options.credentials === "same-origin" && options.redirect === "error"));
  const surface = all(root).map((node) => node.textContent).join("\n");
  assert.doesNotMatch(surface, /raw balance|raw_balance/iu);
  assert.match(surface, /No governance authority granted/u);

  assert.equal(controller.logout(), true);
  assert.equal(controller.getCredential(), null);
  assert.equal(storage.value(), null);
  assert.match(all(root).find((node) => node.attributes.get("role") === "status").textContent, /not revoked/u);
});

test("saved receipt restores only through active status and unknown status fails closed", async () => {
  const { root } = fakeDom();
  const storage = memoryStorage(receiptId);
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
  storage.setItem("ignored", receiptId);
  const unavailable = mountDreggAdmissionPanel(fakeDom().root, {
    walletsRegistry: { get: () => [standardWallet()] }, origin, now: () => nowMs, storage,
    fetchImpl: async () => response(404, { code: "unknown_receipt", message: "unknown" }),
  });
  assert.equal(await unavailable.ready, null);
  assert.equal(unavailable.getCredential(), null);
  assert.equal(storage.value(), null);
});

test("unavailable or over-claiming node response leaves admission closed", async () => {
  const { root } = fakeDom();
  const wallet = standardWallet();
  const fetchImpl = async (url) => {
    if (new URL(url).pathname.endsWith("/challenge")) return response(201, challenge);
    return response(200, capability({ governance_weight_bearing: true }));
  };
  const controller = mountDreggAdmissionPanel(root, {
    walletsRegistry: { get: () => [wallet] }, origin, now: () => nowMs, fetchImpl, storage: memoryStorage(),
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

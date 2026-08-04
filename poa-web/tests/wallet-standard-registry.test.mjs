import assert from "node:assert/strict";
import { test } from "node:test";
import { getWalletStandardRegistry } from "../src/wallet-standard-registry.js";

class FakeCustomEvent {
  constructor(type, init) { this.type = type; Object.assign(this, init); }
}

class FakeWindow {
  constructor() { this.CustomEvent = FakeCustomEvent; this.listeners = new Map(); this.dispatched = []; }
  addEventListener(name, callback) { this.listeners.set(name, [...(this.listeners.get(name) ?? []), callback]); }
  dispatchEvent(event) {
    this.dispatched.push(event);
    for (const callback of this.listeners.get(event.type) ?? []) callback(event);
    return true;
  }
}

test("local registry implements Wallet Standard app-ready/register protocol without vendor detection", () => {
  const windowRef = new FakeWindow();
  const wallet = { name: "Event wallet", features: {} };
  windowRef.addEventListener("wallet-standard:app-ready", ({ detail: { register } }) => register(wallet));
  const registry = getWalletStandardRegistry(windowRef);
  assert.deepEqual(registry.get(), [wallet]);
  assert.equal(windowRef.dispatched[0].type, "wallet-standard:app-ready");
  assert.equal(getWalletStandardRegistry(windowRef), registry);

  const later = { name: "Late wallet", features: {} };
  let registered = null;
  registry.on("register", (...wallets) => { registered = wallets; });
  windowRef.dispatchEvent(new FakeCustomEvent("wallet-standard:register-wallet", {
    detail: ({ register }) => register(later),
  }));
  assert.deepEqual(registered, [later]);
  assert.deepEqual(registry.get(), [wallet, later]);
});

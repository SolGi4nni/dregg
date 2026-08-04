/**
 * CSP-local Wallet Standard app registry.
 *
 * This is the small browser protocol implemented by `@wallet-standard/app`:
 * wallets register through `wallet-standard:register-wallet`, while the app
 * announces readiness through `wallet-standard:app-ready`. No provider names
 * or vendor globals are inspected.
 */

const registries = new WeakMap();

function guard(callback) {
  try { callback(); } catch (error) { console.error(error); }
}

export function getWalletStandardRegistry(windowRef = globalThis.window) {
  if (!windowRef || typeof windowRef.addEventListener !== "function" ||
      typeof windowRef.dispatchEvent !== "function") {
    throw new TypeError("browser window with Wallet Standard events is required");
  }
  const existing = registries.get(windowRef);
  if (existing) return existing;

  const registered = new Set();
  const listeners = { register: [], unregister: [] };
  let cached;
  function register(...wallets) {
    const added = wallets.filter((wallet) => wallet && typeof wallet === "object" && !registered.has(wallet));
    if (added.length === 0) return () => {};
    for (const wallet of added) registered.add(wallet);
    cached = undefined;
    for (const listener of listeners.register) guard(() => listener(...added));
    let active = true;
    return () => {
      if (!active) return;
      active = false;
      for (const wallet of added) registered.delete(wallet);
      cached = undefined;
      for (const listener of listeners.unregister) guard(() => listener(...added));
    };
  }
  function get() {
    cached ??= Object.freeze([...registered]);
    return cached;
  }
  function on(event, listener) {
    if (!(event in listeners) || typeof listener !== "function") throw new TypeError("invalid Wallet Standard listener");
    listeners[event].push(listener);
    return () => { listeners[event] = listeners[event].filter((candidate) => candidate !== listener); };
  }
  const api = Object.freeze({ register });
  const registry = Object.freeze({ register, get, on });
  registries.set(windowRef, registry);
  windowRef.addEventListener("wallet-standard:register-wallet", (event) => {
    if (typeof event?.detail === "function") guard(() => event.detail(api));
  });
  const EventConstructor = windowRef.CustomEvent ?? globalThis.CustomEvent;
  if (typeof EventConstructor !== "function") throw new TypeError("CustomEvent is required for Wallet Standard discovery");
  windowRef.dispatchEvent(new EventConstructor("wallet-standard:app-ready", {
    bubbles: false,
    cancelable: false,
    composed: false,
    detail: api,
  }));
  return registry;
}

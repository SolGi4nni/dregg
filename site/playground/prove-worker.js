// prove-worker.js — the in-browser proving Web Worker (WEB-FORWARD §(a)).
//
// `docs/WEB-FORWARD-EVERYWHERE.md §(a)`: recursive STARK proving in the tab is
// ~minutes of single-core wasm work; on the MAIN thread it FREEZES the page. This
// worker moves the heavy `light_client_demo` / `verify_history_against_anchor` /
// `prove_*` calls OFF the main thread so the UI stays responsive (a spinner
// animates, the work is cancellable by terminating the worker).
//
// The worker holds its OWN wasm instance + linear memory — workers cannot share a
// `WebAssembly.Module` instance with the page, only structured-cloned values — so
// it inits the wasm-bindgen `--target web` module itself (the same `pkg/` the page
// loads). The honest scope (per §(a)): a Worker fixes RESPONSIVENESS, not LATENCY;
// the prove is still minutes of FRI work, just a BACKGROUND cost now, not a frozen
// page. The latency levers (the proving-modality dial; threaded FRI behind
// COOP/COEP) are named elsewhere.
//
// Message protocol (structured-clone-safe; no functions cross the boundary):
//   page → worker:  { id, kind, args }      // kind ∈ the WHITELIST below
//   worker → page:  { id, ok: true, view }  // view = the binding's JS return
//                |  { id, ok: false, err }  // err  = a string (Error.message)
//                |  { ready: true }          // one-shot, after wasm init
//                |  { ready: false, err }    // wasm init failed
//
// `id` correlates a response to its request (the ProvingClient promise map). The
// worker serves requests sequentially (one wasm instance, one thread) — a second
// request queues behind the first; cancellation is "terminate + respawn" on the
// page side.

// wasm-bindgen `--target web` output: `export { initSync, __wbg_init as default }`.
// `import.meta.url` resolves relative to THIS module (served from /playground/),
// and the default init, called with no arg, fetches `dregg_wasm_bg.wasm` relative
// to `dregg_wasm.js` (its own `import.meta.url`) — so the .wasm loads correctly
// from /pkg/ without us hard-coding a path.
import init, * as wasm from '../pkg/dregg_wasm.js';

// The WHITELIST of heavy entry points this worker may invoke. Keeping it explicit
// (rather than `wasm[kind](...)` over arbitrary names) means the page cannot drive
// the worker to call an unexpected export — the message channel only reaches these.
const HANDLERS = {
  // The in-tab light client: fold a real k-turn chain + light-verify (self-anchored).
  // args: [k, step]
  light_client_demo: (a) => wasm.light_client_demo(a[0], BigInt(a[1])),
  // The config anchor for a window shape (cheap-ish fold; mostly for the demo's
  // "here is the anchor your config would ship" affordance). args: [k, step]
  genesis_vk_anchor: (a) => wasm.genesis_vk_anchor(a[0], BigInt(a[1])),
  // The config-not-artifact tooth: real verify_history against a CALLER anchor.
  // args: [k, step, anchorHex]
  verify_history_against_anchor: (a) =>
    wasm.verify_history_against_anchor(a[0], BigInt(a[1]), a[2]),
  // The external-envelope path (parse + anchor-discipline; byte-verify is the named
  // fork seam). args: [envelopeJson, configAnchorHex]
  verify_devnet_history: (a) => wasm.verify_devnet_history(a[0], a[1]),
  // The STARK / predicate toys (also heavy enough to want off-thread). args vary.
  generate_demo_stark_proof: (a) => wasm.generate_demo_stark_proof(a[0], a[1]),
  prove_committed_threshold: (a) => wasm.prove_committed_threshold(a[0], a[1], a[2]),
  generate_predicate_proof: (a) =>
    wasm.generate_predicate_proof(a[0], a[1], a[2], a[3], a[4]),
};

let ready = false;

// Init the worker's own wasm instance up front, then announce readiness. If init
// fails (e.g. the recursion-enabled build is not present), say so — the page falls
// back to its inline path and surfaces the reason rather than hanging.
init()
  .then(() => {
    ready = true;
    self.postMessage({ ready: true });
  })
  .catch((e) => {
    self.postMessage({ ready: false, err: String(e && e.message ? e.message : e) });
  });

self.onmessage = (ev) => {
  const msg = ev.data || {};
  const { id, kind, args } = msg;
  if (id == null) return; // not a request frame

  if (!ready) {
    self.postMessage({ id, ok: false, err: 'worker wasm not initialized yet' });
    return;
  }
  const handler = HANDLERS[kind];
  if (typeof handler !== 'function') {
    self.postMessage({ id, ok: false, err: `unknown proving kind: ${kind}` });
    return;
  }
  try {
    const view = handler(Array.isArray(args) ? args : []);
    self.postMessage({ id, ok: true, view });
  } catch (e) {
    self.postMessage({ id, ok: false, err: String(e && e.message ? e.message : e) });
  }
};

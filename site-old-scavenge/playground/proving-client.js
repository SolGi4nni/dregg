// proving-client.js — the page-side promise wrapper around the proving Worker.
//
// `docs/WEB-FORWARD-EVERYWHERE.md §(a)`. The page calls
// `await provingClient.lightClientDemo(2, 100n)` (or `.verifyHistoryAgainstAnchor`,
// etc.) and the heavy STARK fold runs OFF the main thread in `prove-worker.js`; the
// UI stays responsive while it works. Each call returns a Promise resolved with the
// binding's JS view (or rejected with the worker's error string).
//
// Cancellation is "terminate the worker": `cancel()` rejects all in-flight promises
// and respawns a fresh worker (a new wasm instance + linear memory) for the next
// call. That is the honest cancel for a single-core synchronous prove — there is no
// cooperative interrupt inside a FRI fold.

const WORKER_URL = new URL('./prove-worker.js', import.meta.url);

export class ProvingClient {
  constructor() {
    /** @type {Worker|null} */
    this._worker = null;
    /** @type {Map<number, {resolve: Function, reject: Function}>} */
    this._pending = new Map();
    this._nextId = 1;
    /** Resolves when the worker's wasm has initialized. */
    this._readyPromise = null;
    this._readyResolve = null;
    this._readyReject = null;
  }

  /** Lazily spawn the worker + wire its message pump. Idempotent. */
  _ensureWorker() {
    if (this._worker) return;
    // `{ type: 'module' }` so the worker can `import` the wasm-bindgen ESM module.
    const w = new Worker(WORKER_URL, { type: 'module' });
    this._worker = w;
    this._readyPromise = new Promise((resolve, reject) => {
      this._readyResolve = resolve;
      this._readyReject = reject;
    });
    // Swallow the unhandled-rejection if nobody awaits readiness before a call.
    this._readyPromise.catch(() => {});

    w.onmessage = (ev) => {
      const msg = ev.data || {};
      if (msg.ready === true) {
        this._readyResolve?.();
        return;
      }
      if (msg.ready === false) {
        this._readyReject?.(new Error(msg.err || 'worker wasm init failed'));
        return;
      }
      const entry = this._pending.get(msg.id);
      if (!entry) return;
      this._pending.delete(msg.id);
      if (msg.ok) entry.resolve(msg.view);
      else entry.reject(new Error(msg.err || 'proving failed'));
    };
    w.onerror = (ev) => {
      // A worker-level error (e.g. a module load failure) fails readiness AND any
      // in-flight requests, so callers don't hang.
      const err = new Error(ev.message || 'proving worker error');
      this._readyReject?.(err);
      for (const [, entry] of this._pending) entry.reject(err);
      this._pending.clear();
    };
  }

  /** Resolves once the worker's wasm is initialized (or rejects if init failed). */
  ready() {
    this._ensureWorker();
    return this._readyPromise;
  }

  /** Post a request and return a Promise for its response. */
  _call(kind, args) {
    this._ensureWorker();
    const id = this._nextId++;
    const p = new Promise((resolve, reject) => {
      this._pending.set(id, { resolve, reject });
    });
    // Wait for readiness before posting so the worker never replies "not
    // initialized yet" on a cold start; if readiness rejects, surface that.
    this._readyPromise.then(
      () => {
        // The worker may have been cancelled between ensure and ready.
        if (this._pending.has(id)) this._worker?.postMessage({ id, kind, args });
      },
      (e) => {
        const entry = this._pending.get(id);
        if (entry) {
          this._pending.delete(id);
          entry.reject(e);
        }
      },
    );
    return p;
  }

  // --- typed entry points (mirror the wasm bindings) -----------------------

  /** Fold a real k-turn chain + light-verify it in-tab (self-anchored). */
  lightClientDemo(k, step) {
    return this._call('light_client_demo', [k, Number(step)]);
  }

  /** The config anchor (root-circuit VK fingerprint, hex) for a window shape. */
  genesisVkAnchor(k, step) {
    return this._call('genesis_vk_anchor', [k, Number(step)]);
  }

  /** Real verify_history against a CONFIG-supplied anchor (config-not-artifact). */
  verifyHistoryAgainstAnchor(k, step, anchorHex) {
    return this._call('verify_history_against_anchor', [k, Number(step), anchorHex]);
  }

  /** Verify an external versioned envelope against a separate config anchor. */
  verifyDevnetHistory(envelopeJson, configAnchorHex) {
    return this._call('verify_devnet_history', [envelopeJson, configAnchorHex]);
  }

  /** A demo STARK proof (off-thread). */
  generateDemoStarkProof(leafValue, depth) {
    return this._call('generate_demo_stark_proof', [leafValue, depth]);
  }

  /**
   * Cancel ALL in-flight proving: reject every pending promise, terminate the
   * worker (killing the running FRI fold + its wasm memory), and drop it so the
   * next call respawns a fresh instance.
   */
  cancel(reason = 'cancelled') {
    if (this._worker) {
      this._worker.terminate();
      this._worker = null;
    }
    const err = new Error(reason);
    for (const [, entry] of this._pending) entry.reject(err);
    this._pending.clear();
    this._readyPromise = null;
    this._readyResolve = null;
    this._readyReject = null;
  }
}

/** A lazily-constructed shared client (most pages need only one). */
let _shared = null;
export function getProvingClient() {
  if (!_shared) _shared = new ProvingClient();
  return _shared;
}

/**
 * <dregg-app> — runtime context provider custom element.
 *
 * Usage:
 *   <dregg-app id="app"></dregg-app>
 *   <dregg-cell ref="dregg://cell/abc..."></dregg-cell>
 *
 * The cell element walks the DOM to find its nearest <dregg-app> ancestor and
 * reads `.runtime` from it. Set the runtime imperatively from page JS after
 * construction; inspectors that mount before the runtime is set wait for the
 * `dregg:runtime-ready` event.
 *
 * We don't use the (still-experimental) `<context-provider>` proposal yet —
 * the closest-ancestor walk is good enough and works in all browsers.
 */

class DreggApp extends HTMLElement {
  constructor() {
    super();
    this._runtime = null;
  }
  get runtime() { return this._runtime; }
  set runtime(rt) {
    this._runtime = rt;
    // Notify any inspectors that mounted before us.
    this.dispatchEvent(new CustomEvent('dregg:runtime-ready', { detail: rt, bubbles: false }));
  }
}
if (!customElements.get('dregg-app')) customElements.define('dregg-app', DreggApp);

/**
 * Walk up from `host` to find the enclosing <dregg-app>. If no runtime is
 * attached yet, wait for `dregg:runtime-ready`. Returns a Promise<Runtime>.
 */
export function findRuntime(host) {
  const app = host.closest('dregg-app');
  if (!app) return Promise.reject(new Error(`no <dregg-app> ancestor of <${host.localName}>`));
  if (app.runtime) return Promise.resolve(app.runtime);
  return new Promise(resolve => {
    app.addEventListener('dregg:runtime-ready', e => resolve(e.detail), { once: true });
  });
}

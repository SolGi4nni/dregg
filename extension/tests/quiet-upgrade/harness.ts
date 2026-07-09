/**
 * In-page test harness for the quiet-upgrade loop.
 *
 * It wires the REAL modules — the detector, the `<dregg-poll>` thin view (closed
 * shadow), the `PollEngine` over the REAL wasm `PollWorld` — behind a minimal
 * `chrome` shim so the element uses its REAL `chrome.runtime` message transport
 * and the detector uses its REAL per-origin storage gate. The ONLY things faked
 * are the message transport (routed in-page to the engine) and consent
 * (auto-approve, flippable via `window.__DREGG_CONSENT`). Everything security-
 * and correctness-relevant — closed shadow, engine-owns-wasm, self-verify,
 * one-ballot-one-vote, fail-closed — is the shipping code path.
 */
import { PollEngine, defaultResolveObject } from "../../src/port";
import { startDetector } from "../../src/detect";

declare const window: any;

(async () => {
  // Let the element register its closed root in a test registry (gated hook).
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;

  const wb = window.wasm_bindgen;
  await wb("/dregg_wasm_bg.wasm");
  const PollWorld = wb.PollWorld;

  const engine = new PollEngine({
    PollWorld,
    resolveObject: defaultResolveObject,
    // Consent stands in for the confirm-intent chrome; default approve.
    consent: async () => window.__DREGG_CONSENT !== false,
  });

  // The chrome shim: the element's real chromeMessagePort sends {type:"dregg:poll"}
  // here; we route to the engine and wrap as { id, result } exactly as the
  // background router does. The detector's real origin gate reads the allowlist.
  const allow: Record<string, boolean> = { [location.origin]: true };
  window.chrome = {
    runtime: {
      async sendMessage(msg: any) {
        if (msg && msg.type === "dregg:poll") {
          const result = await engine.handle(
            { op: msg.op, uri: msg.uri, turn: msg.turn, arg: msg.arg },
            location.origin,
          );
          return { id: msg.id, result };
        }
        return { id: msg?.id, error: "unknown message" };
      },
    },
    storage: {
      local: {
        async get(key: string) {
          return key === "dregg_upgrade_origins" ? { dregg_upgrade_origins: allow } : {};
        },
      },
    },
  };

  await startDetector();
  window.__DREGG_READY = true;
})().catch((e) => {
  window.__DREGG_ERROR = String((e && e.message) || e);
});

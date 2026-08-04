/**
 * `<dregg-poa>` — the opt-in Path of Angels YouTube companion.
 *
 * This is only a thin view. Recognition, manifest verification and routing are
 * performed by the background `PoAEngine`; game play is delegated to the
 * existing `<dregg-descent>` element/background engine. The page receives no
 * game state, signature oracle, key or writable shadow handle.
 */

import {
  POA_BETA_URL,
  type PoACompanionPort,
  type PoACompanionRequest,
  type PoACompanionResponse,
  type PoACompanionModel,
} from "../poa";

export type PoAPortFactory = () => PoACompanionPort;
let poaPortFactory: PoAPortFactory | null = null;

export function setPoAPortFactory(factory: PoAPortFactory): void {
  poaPortFactory = factory;
}

/** Production transport. The background disregards the supplied href and
 * derives the authoritative page URL from `sender.tab.url`. */
export function chromePoAPort(): PoACompanionPort {
  return {
    async request(req: PoACompanionRequest): Promise<PoACompanionResponse> {
      const response = await chrome.runtime.sendMessage({ type: "dregg:poa", ...req });
      if (response && typeof response === "object" && "result" in response) {
        return (response as { result: PoACompanionResponse }).result;
      }
      if (response && typeof response === "object" && "error" in response) {
        return {
          ok: false,
          recognized: false,
          verified: false,
          tier: "none",
          error: String((response as { error: unknown }).error),
        };
      }
      return {
        ok: false,
        recognized: false,
        verified: false,
        tier: "none",
        error: "empty companion response",
      };
    },
  };
}

function getPort(): PoACompanionPort {
  return (poaPortFactory ?? chromePoAPort)();
}

const CLOSED_ROOTS = new WeakMap<DreggPoA, ShadowRoot>();
const PRIMED_RESPONSES = new WeakMap<DreggPoA, PoACompanionResponse>();

/** Hand a just-recognized response from the detector to the element without
 * exposing it in page-readable attributes or performing a second node fetch. */
export function primePoAElement(element: DreggPoA, response: PoACompanionResponse): void {
  PRIMED_RESPONSES.set(element, response);
}

const STYLE = `
:host { display: block; font-family: system-ui, sans-serif; color: #eee9dc; margin: 12px 0; }
.terminal { position: relative; overflow: hidden; border: 1px solid #776f5c; border-radius: 10px; padding: 14px 15px; background: linear-gradient(145deg, #171915, #0d0f0d); box-shadow: 0 8px 28px rgba(0,0,0,.32); }
.terminal::before { content: ""; position: absolute; inset: 0; pointer-events: none; opacity: .12; background: repeating-linear-gradient(0deg, transparent 0 3px, #c8d5aa 4px); }
.eyebrow { position: relative; color: #a8b78b; font: 600 10px/1.2 ui-monospace, SFMono-Regular, Consolas, monospace; letter-spacing: .13em; text-transform: uppercase; }
.title { position: relative; margin: 6px 0 2px; color: #f1ead7; font-size: 17px; font-weight: 650; }
.episode { position: relative; color: #aaa38f; font-size: 12px; }
.epoch { position: relative; margin-top: 4px; color: #879776; font: 10px/1.3 ui-monospace, SFMono-Regular, Consolas, monospace; text-transform: uppercase; letter-spacing: .06em; }
.dispatch { position: relative; margin: 11px 0; color: #d2cbb9; font-size: 13px; line-height: 1.45; white-space: pre-wrap; }
.mission { position: relative; margin-top: 12px; }
.links { position: relative; display: flex; gap: 10px; align-items: center; margin-top: 11px; }
.links a { color: #cbdca7; font-size: 12px; text-decoration: underline; text-underline-offset: 2px; }
.badge { position: relative; margin-top: 9px; color: #8fb878; font: 10px/1.35 ui-monospace, SFMono-Regular, Consolas, monospace; }
`;

function validModel(value: unknown): value is PoACompanionModel {
  if (!value || typeof value !== "object" || Array.isArray(value)) return false;
  const m = value as PoACompanionModel;
  if (m.trust !== "signed_manifest" && m.trust !== "local_allowlist") return false;
  if (m.platform === "youtube") {
    if (typeof m.videoId !== "string" || !/^[A-Za-z0-9_-]{11}$/.test(m.videoId) || m.contextId !== m.videoId) return false;
  } else if (m.platform === "x") {
    if (m.trust !== "signed_manifest") return false;
    if (typeof m.postId !== "string" || !/^[1-9][0-9]{0,19}$/.test(m.postId) || m.contextId !== m.postId) return false;
  } else {
    return false;
  }
  if (typeof m.experienceId !== "string" || !m.experienceId || m.experienceId.length > 64) return false;
  if (typeof m.title !== "string" || !m.title || m.title.length > 160) return false;
  if (m.episode !== undefined && (typeof m.episode !== "string" || m.episode.length > 96)) return false;
  if (m.dispatch !== undefined && (typeof m.dispatch !== "string" || m.dispatch.length > 1200)) return false;
  try {
    if (new URL(m.betaUrl).origin !== "https://beta.pathofangels.network") return false;
  } catch {
    return false;
  }
  if (m.game) {
    if (m.trust !== "signed_manifest") return false;
    if (m.game.kind !== "descent" || !/^dregg:\/\/descent\/b3_[0-9a-f]{6,}$/i.test(m.game.src)) return false;
  }
  if (m.trust === "signed_manifest") {
    if (!Number.isSafeInteger(m.contentEpoch) || m.contentEpoch < 0) return false;
    if (!Number.isSafeInteger(m.counter) || m.counter < 0) return false;
    if (!/^[0-9a-f]{64}$/i.test(m.manifestDigest)) return false;
    if (!Number.isSafeInteger(m.issuedAt) || !Number.isSafeInteger(m.expiresAt) || m.expiresAt <= m.issuedAt) return false;
  }
  return true;
}

function makeDiv(className: string, text?: string): HTMLDivElement {
  const el = document.createElement("div");
  el.className = className;
  if (text !== undefined) el.textContent = text;
  return el;
}

export class DreggPoA extends HTMLElement {
  private readonly port = getPort();
  private booted = false;

  connectedCallback(): void {
    if (!this.booted) void this.boot();
  }

  private context(): { href: string; channelHint?: string } {
    const channelHint = this.getAttribute("channel-hint") || undefined;
    return { href: this.getAttribute("page-url") || location.href, ...(channelHint ? { channelHint } : {}) };
  }

  private async boot(): Promise<void> {
    this.booted = true;
    let response: PoACompanionResponse;
    try {
      response = PRIMED_RESPONSES.get(this) ?? await this.port.request({ op: "openContext", context: this.context() });
      PRIMED_RESPONSES.delete(this);
    } catch (error) {
      this.failClosed(String((error as Error)?.message ?? error));
      return;
    }
    if (!response.ok || !response.recognized || !validModel(response.model)) {
      this.failClosed(response.ok ? "invalid companion model" : response.error);
      return;
    }
    // Trust labels are structural: signed is the ONLY path that may be verified;
    // local allowlisting is recognition only and cannot attach a game.
    if (response.model.trust === "signed_manifest" && (!response.verified || response.tier !== "extension")) {
      this.failClosed("signed companion was not verified");
      return;
    }
    if (response.model.trust === "local_allowlist" && (response.verified || response.model.game)) {
      this.failClosed("local recognition cannot verify or attach a mission");
      return;
    }
    this.paint(response.model);
  }

  private paint(model: PoACompanionModel): void {
    const root = this.attachShadow({ mode: "closed" });
    CLOSED_ROOTS.set(this, root);
    const style = document.createElement("style");
    style.textContent = STYLE;
    const terminal = makeDiv("terminal");
    terminal.setAttribute("role", "complementary");
    terminal.setAttribute("aria-label", "Path of Angels companion");
    terminal.appendChild(makeDiv("eyebrow", "KHOVOKHI // FIELD TERMINAL"));
    terminal.appendChild(makeDiv("title", model.title));
    if (model.episode) terminal.appendChild(makeDiv("episode", model.episode));
    if (model.trust === "signed_manifest") {
      terminal.appendChild(makeDiv("epoch", `content epoch ${model.contentEpoch} · revision ${model.counter}`));
    }
    if (model.dispatch) terminal.appendChild(makeDiv("dispatch", model.dispatch));

    if (model.game?.kind === "descent") {
      const mission = makeDiv("mission");
      const descent = document.createElement("dregg-descent");
      descent.setAttribute("src", model.game.src);
      const fallback = document.createElement("a");
      fallback.href = model.betaUrl;
      fallback.textContent = "Open this expedition in the field terminal";
      fallback.target = "_blank";
      fallback.rel = "noopener noreferrer";
      descent.appendChild(fallback);
      mission.appendChild(descent);
      terminal.appendChild(mission);
    }

    const links = makeDiv("links");
    const beta = document.createElement("a");
    beta.href = model.betaUrl;
    beta.textContent = "Open beta.pathofangels.network";
    beta.target = "_blank";
    beta.rel = "noopener noreferrer";
    links.appendChild(beta);
    terminal.appendChild(links);
    terminal.appendChild(
      makeDiv(
        "badge",
        model.trust === "signed_manifest"
          ? "✓ curator manifest verified by your cipherclerk"
          : "• exact video locally recognized · not verified · no mission attached",
      ),
    );
    root.replaceChildren(style, terminal);

    this.setAttribute("recognized", "");
    this.setAttribute("experience", model.experienceId);
    this.setAttribute("platform", model.platform);
    this.setAttribute("context-id", model.contextId);
    if (model.platform === "youtube") {
      this.setAttribute("video-id", model.videoId);
      this.removeAttribute("post-id");
    } else {
      this.setAttribute("post-id", model.postId);
      this.removeAttribute("video-id");
    }
    if (model.trust === "signed_manifest") {
      this.setAttribute("trust", "extension");
      this.setAttribute("verified", "");
      this.setAttribute("manifest-signed", "");
      this.setAttribute("content-epoch", String(model.contentEpoch));
      this.setAttribute("manifest-counter", String(model.counter));
      this.setAttribute("manifest-digest", model.manifestDigest);
      this.setAttribute("expires-at", String(model.expiresAt));
    } else {
      this.setAttribute("trust", "local");
      this.removeAttribute("verified");
      this.removeAttribute("manifest-signed");
      this.removeAttribute("content-epoch");
      this.removeAttribute("manifest-counter");
      this.removeAttribute("manifest-digest");
      this.removeAttribute("expires-at");
    }
    this.removeAttribute("error");
    this.exposeRootForTest(root);
  }

  /** Fail closed to the beta link in light DOM. Never render a page-supplied
   * mission or claim recognition after a transport/verification failure. */
  private failClosed(reason: string): void {
    this.removeAttribute("verified");
    this.removeAttribute("manifest-signed");
    this.removeAttribute("content-epoch");
    this.removeAttribute("manifest-counter");
    this.removeAttribute("manifest-digest");
    this.removeAttribute("expires-at");
    this.removeAttribute("recognized");
    this.setAttribute("trust", "none");
    this.setAttribute("error", "");
    this.setAttribute("title", `Path of Angels companion unavailable: ${reason}`);
    let fallback = this.querySelector<HTMLAnchorElement>("a[data-poa-fallback]");
    if (!fallback) {
      fallback = document.createElement("a");
      fallback.dataset.poaFallback = "";
      fallback.href = POA_BETA_URL;
      fallback.textContent = "Open Path of Angels field terminal";
      fallback.target = "_blank";
      fallback.rel = "noopener noreferrer";
      this.appendChild(fallback);
    }
  }

  private exposeRootForTest(root: ShadowRoot): void {
    if ((globalThis as { __DREGG_EXPOSE_SHADOW_FOR_TEST__?: boolean }).__DREGG_EXPOSE_SHADOW_FOR_TEST__) {
      const globals = globalThis as { __dreggPoARoots?: WeakMap<Element, ShadowRoot> };
      const registry = (globals.__dreggPoARoots ??= new WeakMap());
      registry.set(this, root);
    }
  }
}

export function registerPoAElement(): void {
  if (typeof customElements === "undefined" || customElements === null) return;
  if (!customElements.get("dregg-poa")) customElements.define("dregg-poa", DreggPoA);
}

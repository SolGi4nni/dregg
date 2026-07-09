/**
 * `<dregg-poll>` — THE THIN VIEW (DREGG-QUIET-UPGRADE.md §3).
 *
 * This element lives in the page's DOM but its logic runs in the extension's
 * isolated content-script world. It is a *view*, not an engine: NO wasm, NO
 * keys, NO trust decisions. Every fact it shows comes back through the port
 * from the background engine; it never reads state from the page.
 *
 * Enforcing the split:
 *  - The render surface is a **closed** shadow root (`attachShadow({mode:"closed"})`).
 *    The handle is kept in a module-private `WeakMap`, never on the instance and
 *    never returned — a hostile page cannot read or rewrite what is inside it.
 *  - The click wire is bound to that closed root, so the page cannot inject
 *    affordances; only buttons the element itself rendered can fire.
 *  - The original link is preserved in the light DOM as a fail-closed fallback.
 *  - Trust tier + verified state are reflected as attributes AND shown as an
 *    honest badge; an unverifiable object renders NOTHING (fallback link only).
 */

import type { PollPort, ResolveResponse, RenderResponse, FireResponse, VerifyResponse, TrustTier } from "../port";

// The closed shadow roots — off-instance so nothing on the element (reachable
// by the page) exposes them. Keyed weakly by element.
const CLOSED_ROOTS = new WeakMap<DreggElement, ShadowRoot>();

/** The port factory the element uses to reach the engine. Overridable for tests. */
export type PollPortFactory = () => PollPort;
let portFactory: PollPortFactory | null = null;
export function setPollPortFactory(f: PollPortFactory): void {
  portFactory = f;
}

/** The default transport: chrome.runtime message hop to the background engine. */
function chromeMessagePort(): PollPort {
  return {
    async request(req) {
      const resp = await chrome.runtime.sendMessage({ type: "dregg:poll", ...req });
      // The router wraps handler results as { id, result } | { error }.
      if (resp && typeof resp === "object" && "result" in resp) {
        return (resp as { result: unknown }).result as never;
      }
      if (resp && typeof resp === "object" && "error" in resp) {
        return { ok: false, tier: "none", verified: false, error: String((resp as { error: unknown }).error) } as never;
      }
      return resp as never;
    },
  };
}

function getPort(): PollPort {
  return (portFactory ?? chromeMessagePort)();
}

const BADGE: Record<TrustTier, string> = {
  extension: "✓ verified by your cipherclerk",
  sdk: "✓ verified in this page",
  server: "✓ verified by dregg.net (trust the origin)",
  none: "⚠ unverified — original link shown",
};

const STYLE = `
:host { display: inline-block; font-family: system-ui, sans-serif; }
.wrap { border: 1px solid #7c6cf0; border-radius: 10px; padding: 10px 12px; min-width: 220px; background: #faf9ff; color: #1c1830; }
.title { font-weight: 600; font-size: 13px; margin-bottom: 6px; }
.live { font-size: 13px; }
.live table { border-collapse: collapse; }
.controls { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 8px; }
.controls button { font: inherit; font-size: 12px; padding: 3px 9px; border: 1px solid #7c6cf0; border-radius: 6px; background: #fff; color: #4030a0; cursor: pointer; }
.controls button:hover { background: #7c6cf0; color: #fff; }
.note { font-size: 12px; color: #b02a37; margin-top: 6px; min-height: 0; }
.note:empty { display: none; }
.badge { font-size: 11px; margin-top: 8px; color: #2f7d32; }
.badge.none { color: #b02a37; }
`;

/**
 * The shared base for every `<dregg-*>` thin view: it owns the port, the
 * lifecycle (resolve → closed shadow render OR fail-closed), and trust
 * reflection. Subclasses supply only how a resolved object renders + fires.
 */
export abstract class DreggElement extends HTMLElement {
  protected port: PollPort = getPort();
  protected booted = false;

  static get observedAttributes(): string[] {
    return ["src"];
  }

  get src(): string {
    return this.getAttribute("src") || "";
  }

  connectedCallback(): void {
    if (!this.booted) void this.boot();
  }

  /** Resolve through the port; on verified attach a CLOSED shadow + render;
   * otherwise fail closed (no shadow, keep the fallback link, warn). */
  protected async boot(): Promise<void> {
    this.booted = true;
    const uri = this.src;
    if (!uri) return this.failClosed("no source");
    let resolved: ResolveResponse;
    try {
      resolved = (await this.port.request({ op: "resolve", uri })) as ResolveResponse;
    } catch (e) {
      return this.failClosed(String((e as Error)?.message ?? e));
    }
    if (!resolved || !resolved.ok || !resolved.verified) {
      return this.failClosed(resolved?.error || "could not verify");
    }
    await this.renderVerified(uri, resolved);
  }

  /** Attach the closed shadow and paint the verified object. */
  protected abstract renderVerified(uri: string, resolved: ResolveResponse): Promise<void>;

  /** Attach (once) a closed shadow root, kept off-instance. */
  protected closedShadow(): ShadowRoot {
    let root = CLOSED_ROOTS.get(this);
    if (!root) {
      root = this.attachShadow({ mode: "closed" });
      CLOSED_ROOTS.set(this, root);
    }
    return root;
  }

  /** §5: reflect the tier + verified/error so the page and a11y tools can read
   * *who checked this*. These are public facts, never secret state. */
  protected reflectTrust(tier: TrustTier, verified: boolean): void {
    this.setAttribute("trust", tier);
    if (verified) this.setAttribute("verified", "");
    else this.removeAttribute("verified");
    this.removeAttribute("error");
  }

  /** Fail-closed (§4.4 / §6): render NOTHING; keep the light-DOM fallback link;
   * set [error]; show a warning next to the link. Never fake verification. */
  protected failClosed(reason: string): void {
    this.removeAttribute("verified");
    this.setAttribute("trust", "none");
    this.setAttribute("error", "");
    this.setAttribute("title", `dregg: could not verify (${reason}) — showing the original link`);
    // Add a small visible warning into the light DOM, once.
    if (!this.querySelector(".dregg-fallback-warning")) {
      const warn = document.createElement("span");
      warn.className = "dregg-fallback-warning";
      warn.setAttribute("role", "note");
      warn.style.cssText = "font-size:11px;color:#b02a37;margin-left:6px;";
      warn.textContent = "⚠ could not verify — showing the original link";
      this.appendChild(warn);
    }
  }
}

/** `<dregg-poll>` — a live, verified, votable poll. */
export class DreggPoll extends DreggElement {
  private uri = "";
  private optionCount = 0;

  protected async renderVerified(uri: string, resolved: ResolveResponse): Promise<void> {
    this.uri = uri;
    this.optionCount = resolved.object?.optionCount ?? 0;
    const render = (await this.port.request({ op: "render", uri })) as RenderResponse;
    if (!render.ok || !render.html) return this.failClosed(render.error || "render failed");

    const root = this.closedShadow();
    const style = document.createElement("style");
    style.textContent = STYLE;
    const wrap = document.createElement("div");
    wrap.className = "wrap";
    wrap.innerHTML =
      `<div class="title">Poll — ${escapeHtml(resolved.object?.addr || "")}</div>` +
      `<div class="live"></div>` +
      `<div class="controls"></div>` +
      `<div class="note" aria-live="polite"></div>` +
      `<div class="badge"></div>`;
    root.replaceChildren(style, wrap);

    // The live tally: engine-authored HTML (from the extension wasm, not the
    // page) — safe to inject; it is exactly what the background rendered.
    (wrap.querySelector(".live") as HTMLElement).innerHTML = render.html;

    // The affordances: one vote button per option, rendered BY US inside the
    // closed root so the page cannot add or alter them.
    const controls = wrap.querySelector(".controls") as HTMLElement;
    for (let i = 0; i < this.optionCount; i++) {
      const b = document.createElement("button");
      b.dataset.turn = "cast";
      b.dataset.arg = String(i);
      b.textContent = `Vote ${i}`;
      controls.appendChild(b);
    }

    // The click wire is bound to the CLOSED root — page-injected clicks on page
    // nodes never reach it, and only our buttons carry a turn.
    root.addEventListener("click", (ev) => void this.onShadowClick(ev));

    this.reflectTrust("extension", true);
    this.setAttribute("votes", String(resolved.receiptCount ?? 0));
    this.paintBadge(root, "extension", true);

    // Test hook (never populated in production): expose the closed root so the
    // harness can drive/read it. Gated on an explicit global flag.
    if ((globalThis as unknown as { __DREGG_EXPOSE_SHADOW_FOR_TEST__?: boolean }).__DREGG_EXPOSE_SHADOW_FOR_TEST__) {
      const reg = ((globalThis as unknown as { __dreggPollRoots?: WeakMap<Element, ShadowRoot> }).__dreggPollRoots ??=
        new WeakMap());
      reg.set(this, root);
    }
  }

  private async onShadowClick(ev: Event): Promise<void> {
    const target = ev.target as HTMLElement | null;
    const btn = target?.closest?.("button[data-turn]") as HTMLElement | null;
    if (!btn) return;
    const turn = btn.dataset.turn!;
    const arg = Number(btn.dataset.arg || "0");
    const root = CLOSED_ROOTS.get(this);
    if (!root) return;
    const note = root.querySelector(".note") as HTMLElement;
    note.textContent = "";
    // Disable while the turn (and its consent) is in flight.
    (root.querySelectorAll("button") as NodeListOf<HTMLButtonElement>).forEach((b) => (b.disabled = true));

    let resp: FireResponse;
    try {
      resp = (await this.port.request({ op: "fire", uri: this.uri, turn, arg })) as FireResponse;
    } catch (e) {
      note.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
      (root.querySelectorAll("button") as NodeListOf<HTMLButtonElement>).forEach((b) => (b.disabled = false));
      return;
    }

    if (resp.refused) {
      // Surface the refusal honestly (double-vote / below-quorum / denied).
      note.textContent = `⚠ vote refused: ${resp.reason || "refused"}`;
      this.setAttribute("vote-refused", "");
    } else if (resp.ok) {
      this.removeAttribute("vote-refused");
    }

    // Repaint from the engine (never from the page) + re-verify the badge.
    await this.repaint(root);
    (root.querySelectorAll("button") as NodeListOf<HTMLButtonElement>).forEach((b) => (b.disabled = false));
  }

  private async repaint(root: ShadowRoot): Promise<void> {
    const render = (await this.port.request({ op: "render", uri: this.uri })) as RenderResponse;
    if (render.ok && render.html) {
      (root.querySelector(".live") as HTMLElement).innerHTML = render.html;
    }
    const verify = (await this.port.request({ op: "verify", uri: this.uri })) as VerifyResponse;
    this.reflectTrust(verify.tier, verify.verified);
    if (verify.verified === false) this.removeAttribute("verified");
    if (typeof verify.total === "number") this.setAttribute("votes", String(verify.total));
    this.paintBadge(root, verify.tier, verify.verified);
    // Re-preserve [error] semantics: a poll that stops verifying must fail loud.
    if (!verify.verified) this.setAttribute("error", "");
  }

  private paintBadge(root: ShadowRoot, tier: TrustTier, verified: boolean): void {
    const badge = root.querySelector(".badge") as HTMLElement;
    if (!badge) return;
    const shown: TrustTier = verified ? tier : "none";
    badge.textContent = BADGE[shown];
    badge.classList.toggle("none", shown === "none");
  }
}

function escapeHtml(s: string): string {
  return s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}

/** Register the custom element (idempotent). Call from the content script. */
export function registerDreggElements(): void {
  if (typeof customElements === "undefined") return;
  if (!customElements.get("dregg-poll")) {
    customElements.define("dregg-poll", DreggPoll);
  }
}

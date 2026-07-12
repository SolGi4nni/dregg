/**
 * `<dregg-embed src="dregg://cell/…">` — a whole CHILD CELL embedded into a
 * parent surface (DOC-CELL-COMPOSITION.md §1/§2.3, DREGG-DOCUMENT-FOUNDATION.md
 * §1.3). This is `Op::Embed`: a nested cell renders as a nested `<dregg-*>`
 * element, and — because the child's rendered HTML may itself contain more
 * `<dregg-embed>` tags — the recursive fold through the membrane IS the browser
 * upgrading nested custom elements, each attaching its OWN closed shadow root.
 * A shadow root is the membrane boundary is the cell boundary.
 *
 * LIVE by default (`Pin::Live` — re-resolves to the child's tip) or pinned
 * (`pin="at:<receipt>"` — a frozen citation that never rots). It is a CELL, not
 * a value quote — independently owned, its own membrane, its own recursion.
 *
 * The five RESOLUTION STATES are all first-class — the renderer never forges,
 * never panics:
 *   rendered   — the child (recurses into grandchildren)
 *   darkened   — out-of-cap: render ONLY the citation; the ENGINE withheld the
 *                bytes (they never reached the page — the membrane projection)
 *   unresolved — unfetchable: a visible "unreachable" state + the dregg:// link
 *   cycle      — would loop: a "cycle" state (never a hang)
 *   unbound    — a Name binding to nothing: an "unbound" state; heals on rebind
 *
 * It REUSES `DreggElement` (closed shadow, trust reflection) but overrides the
 * boot flow to speak the composition port instead of the poll port.
 */

import { DreggElement } from "./dregg-poll";
import type { ResolveCellResponse, Provenance, CellPort } from "../port";
import { getCellPort, parsePin, ancestorChain, escapeHtml, exposeRootForTest, COMPOSE_STYLE } from "./cell-port";
import { DreggTransclude } from "./dregg-transclude";

export class DreggEmbed extends DreggElement {
  private cell: CellPort = getCellPort();

  static get observedAttributes(): string[] {
    return ["src", "pin"];
  }

  /** Re-resolve on a src/pin change — a `Name` rebind heals an `unbound` embed,
   * a re-pin re-freezes. (Only after the first boot; the initial set is the boot.) */
  attributeChangedCallback(name: string, prev: string | null, next: string | null): void {
    if (!this.booted || prev === next) return;
    if (name === "src" || name === "pin") void this.boot();
  }

  /** Public: force a re-resolve (the fixture uses it to show `unbound` healing). */
  refresh(): void {
    void this.boot();
  }

  /** Override the poll boot: resolve the child cell → one of the five states. */
  protected async boot(): Promise<void> {
    this.booted = true;
    const uri = this.src;
    // Stamp the canonical BEFORE we render, so nested embeds that upgrade inside
    // our shadow can read it while walking their ancestor chain.
    if (uri) this.setAttribute("data-canonical", uri);
    if (!uri) return this.paintState("unresolved", { cell: "" }, "no source", "");

    let resp: ResolveCellResponse;
    try {
      resp = (await this.cell.request({
        op: "resolveCell",
        uri,
        pin: parsePin(this),
        ancestors: ancestorChain(this),
      })) as ResolveCellResponse;
    } catch (e) {
      return this.paintState("unresolved", { cell: uri }, String((e as Error)?.message ?? e), uri);
    }

    const canonical = resp.canonical || uri;
    if (canonical) this.setAttribute("data-canonical", canonical);
    this.setAttribute("state", resp.state);
    this.setAttribute("trust", resp.tier);

    switch (resp.state) {
      case "rendered":
        return this.paintChild(canonical, resp);
      case "darkened":
        // The engine already WITHHELD the bytes (resp.html is undefined); we
        // render ONLY the citation. Never reach for bytes we were not given.
        return this.paintState("darkened", resp.provenance ?? { cell: canonical }, resp.reason ?? "out of cap", canonical);
      case "cycle":
        return this.paintState("cycle", resp.provenance ?? { cell: canonical }, resp.reason ?? "cycle", canonical);
      case "unbound":
        return this.paintState("unbound", resp.provenance ?? { cell: canonical }, resp.reason ?? "unbound", canonical);
      case "unresolved":
      default:
        return this.paintState("unresolved", resp.provenance ?? { cell: canonical }, resp.reason ?? resp.error ?? "unreachable", canonical);
    }
  }

  /** Abstract on the base (poll flow); the embed never uses it. */
  protected async renderVerified(): Promise<void> {
    /* unused — the embed overrides boot() and speaks the composition port. */
  }

  /** RENDERED: attach the closed shadow and inject the child's engine-authored
   * HTML. If that HTML contains nested `<dregg-*>` tags, the browser upgrades
   * them here and the fold recurses — each grandchild its own closed shadow. */
  private paintChild(canonical: string, resp: ResolveCellResponse): void {
    const root = this.closedShadow();
    const style = document.createElement("style");
    style.textContent = COMPOSE_STYLE;
    const wrap = document.createElement("div");
    wrap.className = "embed";
    wrap.setAttribute("role", "group");
    const child = document.createElement("div");
    child.className = "child";
    // Engine-authored HTML (from the extension side, not the page) — safe to
    // inject; nested `<dregg-embed>` tags in it upgrade recursively.
    child.innerHTML = resp.html ?? "";
    wrap.appendChild(child);
    wrap.appendChild(this.citation(resp.provenance, canonical, "embedded"));
    root.replaceChildren(style, wrap);

    this.reflectTrust(resp.tier, true);
    this.removeAttribute("error");
    exposeRootForTest(this, root);
  }

  /** A non-rendered state — darkened / unresolved / cycle / unbound. The bytes
   * are NEVER here (the engine withheld them); we render the state + citation. */
  private paintState(
    state: "darkened" | "unresolved" | "cycle" | "unbound",
    prov: Provenance,
    reason: string,
    canonical: string,
  ): void {
    const label: Record<string, string> = {
      darkened: "🌑 darkened — you are not in cap for this cell (its bytes are withheld)",
      unresolved: "⚠ unreachable — the child cell could not be fetched",
      cycle: "↻ cycle — embedding this cell here would loop",
      unbound: "○ unbound — this name binds to nothing (it will heal on rebind)",
    };
    const root = this.closedShadow();
    const style = document.createElement("style");
    style.textContent = COMPOSE_STYLE;
    const box = document.createElement("div");
    box.className = `state ${state}`;
    const cellUri = prov.cell || canonical;
    const linkHtml = cellUri
      ? `<span class="lnk"><a href="${escapeHtml(cellUri)}" rel="noopener">${escapeHtml(cellUri)}</a></span>`
      : "";
    box.innerHTML =
      `<span class="label">${escapeHtml(label[state])}</span>` +
      (reason ? ` <span class="why">(${escapeHtml(reason)})</span>` : "") +
      linkHtml;
    root.replaceChildren(style, box);

    // Reflect honestly: not verified; darkened/cycle/unbound are genuine engine
    // states (not errors); an unresolved child is a real failure ([error]).
    this.removeAttribute("verified");
    this.setAttribute("trust", state === "unresolved" ? "none" : "extension");
    if (state === "unresolved") this.setAttribute("error", "");
    else this.removeAttribute("error");
    exposeRootForTest(this, root);
  }

  /** The provenance/citation badge — ALWAYS shown (a darkened embed keeps it). */
  private citation(prov: Provenance | undefined, canonical: string, kind: string): HTMLElement {
    const cite = document.createElement("div");
    cite.className = "cite";
    const cellUri = prov?.cell || canonical;
    const pin = prov?.pin === "at" ? `📌 pinned${prov.receipt ? " @ " + prov.receipt : ""}` : "● live";
    cite.innerHTML =
      `<span>${escapeHtml(kind)} cell:</span> ` +
      `<a href="${escapeHtml(cellUri)}" rel="noopener">${escapeHtml(cellUri)}</a>` +
      (prov?.author ? ` <span class="who">by ${escapeHtml(prov.author)}</span>` : "") +
      ` <span class="pin">${escapeHtml(pin)}</span>`;
    return cite;
  }
}

/** Register the composition custom elements (idempotent). */
export function registerCompositionElements(): void {
  if (typeof customElements === "undefined" || customElements === null) return; // null in Chromium isolated worlds
  if (!customElements.get("dregg-embed")) customElements.define("dregg-embed", DreggEmbed);
  if (!customElements.get("dregg-transclude")) customElements.define("dregg-transclude", DreggTransclude);
}

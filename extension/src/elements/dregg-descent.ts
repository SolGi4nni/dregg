/**
 * `<dregg-descent src="dregg://descent/…">` — THE DESCENT, PLAYED IN THE TAB.
 * Today's beacon-seeded, provably-fair, permadeath roguelite runs privately in the
 * page: the moves never leave the device, and a stranger can replay the whole receipt
 * chain. docs/GAME-STRATEGY.md; wasm/src/bindings_descent.rs (`DescentWorld`).
 *
 * Modeled on `<dregg-story>` (its action sibling), with ONE load-bearing difference in
 * the trust tier:
 *  - PLAY + VERIFY are the FREE, trustless, PRIVATE tier — the room prose renders, a
 *    move press ADVANCES the run as a real cap-gated verified turn on the IN-TAB
 *    executor (the "cap-gate" is the scene's own gate: an HP floor, a `warden_hp<=0`
 *    stair), and a "✓ replay-verified" badge shows the whole run re-executes true.
 *    There is NO per-move custody prompt — the run is private and local, and a
 *    gated/invalid move FAILS CLOSED in-band (the permadeath trial's teeth).
 *  - SETTLE/PUBLISH is the ONLY custody write — an OPT-IN affordance that publishes the
 *    private run to the node's no-cheat leaderboard (via the background settle hook,
 *    `window.dregg.signTurnV3` + the node). Until published the run stays PRIVATE.
 *    Absent a settle provider it degrades to an honest "opt-in named hook" note.
 *
 * It is a THIN VIEW, exactly like `<dregg-story>` / `<dregg-doc>`: a **closed** shadow
 * root (the page cannot read or rewrite the render), NO wasm, NO keys, NO scene graph —
 * every fact comes back tiered through the port from the background `DescentEngine`. It
 * REUSES `DreggElement` (closed shadow, trust reflection, fail-closed) but overrides the
 * boot flow to speak the descent port. An unopenable/forged day renders NOTHING
 * (fallback link + warning). It NEVER hides its trust tier — a reflected `trust=…` + a
 * visible badge always say who checked.
 */

import { DreggElement } from "./dregg-poll";
import type {
  DescentPort,
  DescentPortRequest,
  DescentPortResponse,
  DescentOpenResponse,
  DescentRenderResponse,
  DescentAdvanceResponse,
  DescentVerifyResponse,
  DescentSettleResponse,
  DescentMove,
  DescentState,
  TrustTier,
} from "../port";

/** The port factory the element uses to reach the engine. Overridable for tests
 *  (the fixture routes it in-page to a `DescentEngine` over a stand-in DescentWorld). */
export type DescentPortFactory = () => DescentPort;
let descentPortFactory: DescentPortFactory | null = null;
export function setDescentPortFactory(f: DescentPortFactory): void {
  descentPortFactory = f;
}

/** The default transport: a `chrome.runtime` message hop to the background
 *  DescentEngine. The router wraps handler results as `{ id, result }` | `{ error }`. */
function chromeMessagePort(): DescentPort {
  return {
    async request(req: DescentPortRequest): Promise<DescentPortResponse> {
      const resp = await chrome.runtime.sendMessage({ type: "dregg:descent", ...req });
      if (resp && typeof resp === "object" && "result" in resp) {
        return (resp as { result: unknown }).result as DescentPortResponse;
      }
      if (resp && typeof resp === "object" && "error" in resp) {
        return { ok: false, tier: "none", verified: false, error: String((resp as { error: unknown }).error) } as DescentPortResponse;
      }
      return resp as DescentPortResponse;
    },
  };
}

function getDescentPort(): DescentPort {
  return (descentPortFactory ?? chromeMessagePort)();
}

// The badge surfaces BOTH the trust tier (who checked) AND the descent-specific
// semantic (the whole run re-executes). A tier is never hidden.
const BADGE: Record<TrustTier, string> = {
  extension: "✓ replay-verified by your cipherclerk",
  sdk: "✓ replay-verified in this page",
  server: "✓ replay-verified by dregg.net (trust the origin)",
  none: "⚠ unverified · original link shown",
};

const STYLE = `
:host { display: block; font-family: system-ui, sans-serif; }
.wrap { border: 1px solid #7c6cf0; border-radius: 10px; padding: 12px 14px; background: #faf9ff; color: #1c1830; max-width: 42em; }
.title { font-weight: 600; font-size: 13px; margin-bottom: 2px; color: #4030a0; }
.seed { font-size: 11px; color: #6a5acd; margin-bottom: 10px; font-variant-numeric: tabular-nums; word-break: break-all; }
.seed:empty { display: none; }
.prose { font-size: 15px; line-height: 1.55; white-space: pre-wrap; }
.stats { display: flex; flex-wrap: wrap; gap: 6px 14px; margin-top: 12px; font-size: 13px; }
.stat { display: inline-flex; gap: 5px; align-items: baseline; }
.stat .k { color: #6a5acd; font-size: 11px; text-transform: uppercase; letter-spacing: .04em; }
.stat .v { font-variant-numeric: tabular-nums; font-weight: 600; min-width: 1.5em; }
.status { font-size: 13px; margin-top: 8px; font-weight: 600; }
.status.won { color: #2f7d32; }
.status.dead { color: #b02a37; }
.moves { display: flex; flex-direction: column; gap: 8px; margin-top: 12px; }
.moves button { font: inherit; font-size: 14px; padding: 7px 12px; border: 1px solid #7c6cf0; border-radius: 8px; background: #fff; color: #4030a0; cursor: pointer; text-align: left; }
.moves button:hover:not(:disabled) { background: #7c6cf0; color: #fff; }
.moves button:disabled { opacity: .55; cursor: default; }
.moves button.gated::after { content: " 🔒"; }
.actions { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 12px; }
.actions button { font: inherit; font-size: 13px; padding: 5px 11px; border: 1px solid #7c6cf0; border-radius: 8px; background: #efeaff; color: #4030a0; cursor: pointer; }
.actions button:hover:not(:disabled) { background: #7c6cf0; color: #fff; }
.actions button:disabled { opacity: .5; cursor: default; }
.ending { font-size: 12px; color: #4030a0; margin-top: 12px; font-style: italic; }
.ending:empty { display: none; }
.settle-note { font-size: 12px; color: #6a5acd; margin-top: 8px; }
.settle-note:empty { display: none; }
.note { font-size: 12px; color: #b02a37; margin-top: 8px; }
.note:empty { display: none; }
.badge { font-size: 11px; margin-top: 12px; color: #2f7d32; }
.badge.none { color: #b02a37; }
:host([ended]) .moves { opacity: .8; }
:host([won]) .title::after { content: " · won"; color: #2f7d32; }
:host([dead]) .title::after { content: " · fallen"; color: #b02a37; }
`;

// The closed shadow roots — off-instance so nothing on the element (reachable by the
// page) exposes them. Keyed weakly by element.
const CLOSED_ROOTS = new WeakMap<DreggDescent, ShadowRoot>();

/** `<dregg-descent>` — The Descent, played in-tab, private, verifiable. */
export class DreggDescent extends DreggElement {
  private descent: DescentPort = getDescentPort();
  private uri = "";
  private wired = false;
  /** Whether an opt-in settle/publish provider is wired (the named hook). */
  private canSettle = false;

  /** Override the poll boot: open today's descent → render the room prose + the moves
   *  + the run state (the free, private, in-tab tier). */
  protected async boot(): Promise<void> {
    this.booted = true;
    const uri = this.src;
    if (!uri) return this.failClosed("no source");
    this.uri = uri;

    let open: DescentOpenResponse;
    try {
      open = (await this.descent.request({ op: "openDescent", uri })) as DescentOpenResponse;
    } catch (e) {
      return this.failClosed(String((e as Error)?.message ?? e));
    }
    if (!open || !open.ok || !open.verified) {
      return this.failClosed(open?.error || "could not open today's descent");
    }
    await this.paintInitial(open);
  }

  /** Abstract on the base (poll flow); the descent overrides boot(). */
  protected async renderVerified(): Promise<void> {
    /* unused — the descent overrides boot() and speaks the descent port. */
  }

  /** Build the shell, wire the (single, delegated) click handler on the closed root,
   *  and paint the opening room's prose + its moves + the run state. */
  private async paintInitial(open: DescentOpenResponse): Promise<void> {
    const render = (await this.descent.request({ op: "renderDescent", uri: this.uri })) as DescentRenderResponse;
    if (!render.ok) return this.failClosed(render.error || "render failed");

    this.canSettle = !!open.canSettle;

    const root = this.attachClosed();
    const style = document.createElement("style");
    style.textContent = STYLE;
    const wrap = document.createElement("div");
    wrap.className = "wrap";
    wrap.innerHTML =
      `<div class="title">The Descent — ${escapeHtml(open.object?.title || open.object?.addr || "")}</div>` +
      `<div class="seed"></div>` +
      `<div class="prose"></div>` +
      `<div class="stats" aria-label="run state"></div>` +
      `<div class="status" aria-live="polite"></div>` +
      `<div class="moves"></div>` +
      `<div class="ending" aria-live="polite"></div>` +
      `<div class="actions"></div>` +
      `<div class="settle-note" aria-live="polite"></div>` +
      `<div class="note" aria-live="polite"></div>` +
      `<div class="badge"></div>`;
    root.replaceChildren(style, wrap);

    (wrap.querySelector(".seed") as HTMLElement).textContent = open.object?.seedHex
      ? `today's seed ${open.object.seedHex.slice(0, 16)}…`
      : "";

    this.injectRoom(root, render.room ?? open.state?.room ?? "", render.prose ?? "", render.moves ?? []);
    if (open.state) this.injectState(root, open.state);

    // The action row: replay-verify (free, private) + the opt-in settle/publish hook.
    const actions = root.querySelector(".actions") as HTMLElement;
    const verifyBtn = document.createElement("button");
    verifyBtn.type = "button";
    verifyBtn.dataset.verify = "";
    verifyBtn.textContent = "Replay-verify this run";
    actions.appendChild(verifyBtn);
    const settleBtn = document.createElement("button");
    settleBtn.type = "button";
    settleBtn.dataset.settle = "";
    settleBtn.textContent = this.canSettle ? "Publish to the leaderboard" : "Publish (connect cipherclerk)";
    actions.appendChild(settleBtn);

    // The click wire is bound to the CLOSED root — the page cannot inject moves; only
    // the buttons this element rendered carry a turn.
    if (!this.wired) {
      root.addEventListener("click", (ev) => void this.onShadowClick(ev));
      this.wired = true;
    }

    this.reflectTrust(open.tier, true);
    this.setAttribute("turns", String(open.state?.turns ?? 0));
    if (open.commitment) this.setAttribute("commitment", open.commitment);
    this.paintBadge(root, open.tier, true);

    exposeRootForTest(this, root);
  }

  private async onShadowClick(ev: Event): Promise<void> {
    const target = ev.target as HTMLElement | null;
    const root = this.closed();
    if (!root) return;
    const moveBtn = target?.closest?.("button[data-move]") as HTMLButtonElement | null;
    if (moveBtn && !moveBtn.disabled) return void this.doMove(root, Number(moveBtn.getAttribute("data-move") || "0"));
    const verifyBtn = target?.closest?.("button[data-verify]") as HTMLButtonElement | null;
    if (verifyBtn && !verifyBtn.disabled) return void this.doVerify(root);
    const settleBtn = target?.closest?.("button[data-settle]") as HTMLButtonElement | null;
    if (settleBtn && !settleBtn.disabled) return void this.doSettle(root);
  }

  /** ADVANCE a move — ONE cap-gated verified turn, played IN-TAB and PRIVATE. A
   *  gated/invalid move is refused by the executor in-band (nothing commits) and
   *  surfaced honestly; a success re-renders the NEW room + state and re-verifies. */
  private async doMove(root: ShadowRoot, index: number): Promise<void> {
    const note = root.querySelector(".note") as HTMLElement;
    note.textContent = "";
    this.freeze(root, true);

    let resp: DescentAdvanceResponse;
    try {
      resp = (await this.descent.request({ op: "advanceMove", uri: this.uri, index })) as DescentAdvanceResponse;
    } catch (e) {
      note.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
      this.freeze(root, false);
      return;
    }

    if (resp.refused) {
      // Surface the gate's refusal honestly (a blow you could not survive, a warden
      // still standing) — nothing committed, the run did not move.
      note.textContent = `⚠ move refused: ${resp.reason || "refused by the gate"}`;
      this.setAttribute("move-refused", "");
    } else {
      this.removeAttribute("move-refused");
    }

    // Re-render the NEW room from the engine (never from the page) + re-verify the
    // badge. injectRoom rebuilds the move buttons with their correct takeable state.
    await this.repaint(root, resp.state);
  }

  /** Freeze/thaw the move row while a turn is in flight. On thaw a move is takeable
   *  iff it is available (not gated) — play is free (no custody needed). */
  private freeze(root: ShadowRoot, frozen: boolean): void {
    (root.querySelectorAll("button[data-move]") as NodeListOf<HTMLButtonElement>).forEach((b) => {
      b.disabled = frozen || b.classList.contains("gated");
    });
  }

  /** Re-render the room + state from the engine + re-verify the badge. */
  private async repaint(root: ShadowRoot, stateHint?: DescentState): Promise<void> {
    const render = (await this.descent.request({ op: "renderDescent", uri: this.uri })) as DescentRenderResponse;
    if (render.ok) {
      this.injectRoom(root, render.room ?? "", render.prose ?? "", render.moves ?? []);
      if (render.state) this.injectState(root, render.state);
    } else if (stateHint) {
      // A run may have ENDED (render still verifies; there are simply no moves) —
      // keep the last state visible so the win/loss stays on screen.
      this.injectState(root, stateHint);
    }

    const verify = (await this.descent.request({ op: "verifyDescent", uri: this.uri })) as DescentVerifyResponse;
    this.reflectTrust(verify.tier, verify.verified);
    if (!verify.verified) {
      this.removeAttribute("verified");
      this.setAttribute("error", "");
    }
    if (verify.commitment) this.setAttribute("commitment", verify.commitment);
    if (verify.state) this.injectState(root, verify.state);
    this.paintBadge(root, verify.tier, verify.verified);
  }

  /** THE STRANGER'S CHECK, on demand — replay the whole run against a fresh,
   *  identically-seeded day and surface the verdict (a WON and a LOST run both
   *  re-verify true; only a tampered chain fails). */
  private async doVerify(root: ShadowRoot): Promise<void> {
    const note = root.querySelector(".note") as HTMLElement;
    note.textContent = "replaying the run…";
    let verify: DescentVerifyResponse;
    try {
      verify = (await this.descent.request({ op: "verifyDescent", uri: this.uri })) as DescentVerifyResponse;
    } catch (e) {
      note.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
      return;
    }
    this.reflectTrust(verify.tier, verify.verified);
    if (!verify.verified) this.setAttribute("error", "");
    if (verify.commitment) this.setAttribute("commitment", verify.commitment);
    this.paintBadge(root, verify.tier, verify.verified);
    note.textContent = verify.verified
      ? "✓ replay verified — this run re-executes byte-identically against a fresh day"
      : "⚠ replay FAILED — the receipt chain does not re-execute";
  }

  /** SETTLE — the OPT-IN custody write (the named publish hook). Publishes the private
   *  run to the node's no-cheat leaderboard via the background settle provider. Absent
   *  a provider it degrades to an honest "opt-in named hook" note — the run stays private. */
  private async doSettle(root: ShadowRoot): Promise<void> {
    const note = root.querySelector(".note") as HTMLElement;
    const settleNote = root.querySelector(".settle-note") as HTMLElement;
    note.textContent = "";
    settleNote.textContent = "";

    let resp: DescentSettleResponse;
    try {
      resp = (await this.descent.request({ op: "settleDescent", uri: this.uri })) as DescentSettleResponse;
    } catch (e) {
      note.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
      return;
    }

    if (resp.published) {
      this.setAttribute("published", "");
      if (resp.commitment) this.setAttribute("commitment", resp.commitment);
      settleNote.textContent = "✓ published — this run is now a no-cheat leaderboard entry a stranger can replay";
    } else {
      // Honest degrade — the run stays PRIVATE (a named seam, never a fake).
      settleNote.textContent = `this run stays private — ${resp.reason || "settle unavailable"}`;
    }
  }

  /** Inject the current room: its prose, its moves as buttons (a gated move is shown
   *  but disabled), and the ending marker when the run is over. Reflects `[room]`. */
  private injectRoom(root: ShadowRoot, room: string, prose: string, moves: DescentMove[]): void {
    (root.querySelector(".prose") as HTMLElement).textContent = prose;
    if (room) this.setAttribute("room", room);

    const movesEl = root.querySelector(".moves") as HTMLElement;
    movesEl.replaceChildren();
    for (const m of moves) {
      const b = document.createElement("button");
      b.type = "button";
      b.dataset.move = String(m.index);
      b.textContent = m.text;
      // Every move is SHOWN; only an available (gate-passing) move is takeable. Play
      // is free/private (no custody) — a gated move is disabled, and pressing it would
      // be refused in-band regardless (the executor is the sole referee).
      b.disabled = !m.available;
      if (!m.available) b.classList.add("gated");
      movesEl.appendChild(b);
    }

    const ending = root.querySelector(".ending") as HTMLElement;
    ending.textContent = moves.length === 0 ? "— the run ends here —" : "";
  }

  /** Inject the run state: the stat row (hp / depth / warden / gold) + the status
   *  line (alive / won / fallen). Reflects `[hp] [depth] [turns] [won] [dead] [ended]`. */
  private injectState(root: ShadowRoot, s: DescentState): void {
    const stats = root.querySelector(".stats") as HTMLElement;
    const cell = (k: string, v: number): string =>
      `<span class="stat"><span class="k">${k}</span><span class="v">${v}</span></span>`;
    stats.innerHTML =
      cell("hp", s.hp) + cell("depth", s.depth) + cell("warden", s.wardenHp) + cell("gold", s.gold);

    const status = root.querySelector(".status") as HTMLElement;
    status.classList.remove("won", "dead");
    if (s.won) {
      status.textContent = "🏆 the hoard is seized — a won run";
      status.classList.add("won");
    } else if (s.dead) {
      status.textContent = "☠ fallen to the warden — a permadeath loss";
      status.classList.add("dead");
    } else if (s.ended) {
      status.textContent = "the run has ended";
    } else {
      status.textContent = "alive — press on";
    }

    this.setAttribute("hp", String(s.hp));
    this.setAttribute("depth", String(s.depth));
    this.setAttribute("turns", String(s.turns));
    this.toggleFlag("won", s.won);
    this.toggleFlag("dead", s.dead);
    this.toggleFlag("ended", s.ended);
    if (s.commitment) this.setAttribute("commitment", s.commitment);
  }

  private toggleFlag(name: string, on: boolean): void {
    if (on) this.setAttribute(name, "");
    else this.removeAttribute(name);
  }

  private paintBadge(root: ShadowRoot, tier: TrustTier, verified: boolean): void {
    const badge = root.querySelector(".badge") as HTMLElement;
    if (!badge) return;
    const shown: TrustTier = verified ? tier : "none";
    badge.textContent = BADGE[shown];
    badge.classList.toggle("none", shown === "none");
  }

  /** Attach (once) a closed shadow root, kept off-instance (the page can't reach it). */
  private attachClosed(): ShadowRoot {
    let root = CLOSED_ROOTS.get(this);
    if (!root) {
      root = this.attachShadow({ mode: "closed" });
      CLOSED_ROOTS.set(this, root);
    }
    return root;
  }

  private closed(): ShadowRoot | undefined {
    return CLOSED_ROOTS.get(this);
  }
}

function escapeHtml(s: string): string {
  return s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}

/** Test hook (never populated in production): expose the closed root so the harness
 *  can drive/read it. Gated on an explicit global flag, exactly like `<dregg-story>`'s
 *  `__dreggStoryRoots` and `<dregg-poll>`'s `__dreggPollRoots`. */
function exposeRootForTest(el: Element, root: ShadowRoot): void {
  if ((globalThis as unknown as { __DREGG_EXPOSE_SHADOW_FOR_TEST__?: boolean }).__DREGG_EXPOSE_SHADOW_FOR_TEST__) {
    const reg = ((globalThis as unknown as { __dreggDescentRoots?: WeakMap<Element, ShadowRoot> }).__dreggDescentRoots ??=
      new WeakMap());
    reg.set(el, root);
  }
}

/** Register the `<dregg-descent>` custom element (idempotent). Call from the content script. */
export function registerDescentElement(): void {
  if (typeof customElements === "undefined" || customElements === null) return; // null in Chromium isolated worlds
  if (!customElements.get("dregg-descent")) customElements.define("dregg-descent", DreggDescent);
}

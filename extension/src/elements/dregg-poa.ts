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
  parsePoAReceiptCoreObservation,
  type PoACompanionPort,
  type PoACompanionRequest,
  type PoACompanionResponse,
  type PoACompanionModel,
  type PoAEpisodeActions,
  type PoAFieldRecordBinding,
} from "../poa";
import {
  poAGalleyActionLabel,
  poAGalleyAvailableAtSequence,
  type PoAGalleyAction,
  type PoAGalleyBinding,
  type PoAGalleyPortRequest,
  type PoAGalleyPortResponse,
  type PoAGalleyStatus,
} from "../poa-galley";

export type PoAPortFactory = () => PoACompanionPort;
let poaPortFactory: PoAPortFactory | null = null;

export function setPoAPortFactory(factory: PoAPortFactory): void {
  poaPortFactory = factory;
}

/** Deliberate production seam: no implementation is installed until the
 * extension has a transport for a public FRC1 observation. The companion
 * renders that absence explicitly instead of fetching through the host page or
 * treating a local run as a network receipt. */
export interface PoAFieldRecordTransport {
  readReceiptCoreObservation(binding: PoAFieldRecordBinding): Promise<unknown>;
}

export type PoAFieldRecordTransportFactory = () => PoAFieldRecordTransport;
let poaFieldRecordTransportFactory: PoAFieldRecordTransportFactory | null = null;

export function setPoAFieldRecordTransportFactory(factory: PoAFieldRecordTransportFactory | null): void {
  poaFieldRecordTransportFactory = factory;
}

/** Background-only access to the versioned Galley projection.  The host page
 * never receives action tokens, receipt postcards, or a signing method. */
export interface PoAGalleyTransport {
  request(request: PoAGalleyPortRequest): Promise<PoAGalleyPortResponse>;
}

export type PoAGalleyTransportFactory = () => PoAGalleyTransport;
let poaGalleyTransportFactory: PoAGalleyTransportFactory | null = null;

export function setPoAGalleyTransportFactory(factory: PoAGalleyTransportFactory | null): void {
  poaGalleyTransportFactory = factory;
}

export function chromePoAGalleyTransport(): PoAGalleyTransport {
  return {
    async request(request): Promise<PoAGalleyPortResponse> {
      const response = await chrome.runtime.sendMessage({ type: "dregg:poaGalley", ...request });
      if (response && typeof response === "object" && "result" in response) {
        return (response as { result: PoAGalleyPortResponse }).result;
      }
      return {
        ok: false,
        op: request.op,
        error: response && typeof response === "object" && "error" in response
          ? String((response as { error: unknown }).error)
          : "empty Galley response",
      };
    },
  };
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
.actions { position: relative; display: grid; grid-template-columns: repeat(auto-fit, minmax(132px, 1fr)); gap: 7px; margin: 12px 0; }
.action { min-height: 44px; padding: 8px 9px; border: 1px solid #5f6950; border-radius: 6px; color: #e3edd1; background: rgba(104,120,79,.13); text-decoration: none; }
.action b, .action span { display: block; }
.action b { font: 9px/1.2 ui-monospace, SFMono-Regular, Consolas, monospace; color: #94a47a; letter-spacing: .1em; text-transform: uppercase; }
.action span { margin-top: 3px; font-size: 12px; line-height: 1.3; }
.unavailable, .protected, .record-status { position: relative; margin-top: 10px; padding: 8px 9px; border-left: 2px solid #8d7e5a; color: #bbb29d; background: rgba(75,64,43,.17); font-size: 11px; line-height: 1.45; }
.record { position: relative; margin-top: 11px; }
.record button { min-height: 44px; padding: 8px 10px; border: 1px solid #788c5d; border-radius: 6px; color: #e9f0d8; background: #242a20; cursor: pointer; font: 600 11px/1.3 system-ui, sans-serif; }
.record button:disabled { cursor: progress; opacity: .65; }
.record button:focus-visible, .action:focus-visible, .links a:focus-visible { outline: 2px solid #d9efac; outline-offset: 2px; }
.galley { position: relative; margin: 12px 0 2px; padding: 10px; border: 1px solid #4f5947; border-radius: 7px; background: rgba(26,35,25,.62); }
.galley h3 { margin: 0 0 7px; color: #dce7c6; font-size: 13px; }
.galley-status { color: #b9c4aa; font-size: 11px; line-height: 1.4; }
.galley dl { display: grid; grid-template-columns: max-content 1fr; gap: 3px 9px; margin: 8px 0; font: 10px/1.35 ui-monospace, SFMono-Regular, Consolas, monospace; }
.galley dt { color: #859575; }
.galley dd { margin: 0; min-width: 0; overflow-wrap: anywhere; color: #ced8bd; }
.galley-controls { display: flex; flex-wrap: wrap; gap: 7px; margin-top: 8px; }
.galley button { min-height: 44px; padding: 7px 9px; border: 1px solid #68785a; border-radius: 6px; color: #e8efd9; background: #222a20; cursor: pointer; font: 600 11px/1.25 system-ui, sans-serif; }
.galley button:disabled { cursor: not-allowed; opacity: .58; }
.galley button:focus-visible { outline: 2px solid #d9efac; outline-offset: 2px; }
.galley-result { margin-top: 9px; padding-top: 8px; border-top: 1px solid #3d4637; color: #bac7aa; font-size: 11px; line-height: 1.45; overflow-wrap: anywhere; }
.galley-result a { color: #cbdca7; }
.badge { position: relative; margin-top: 9px; color: #8fb878; font: 10px/1.35 ui-monospace, SFMono-Regular, Consolas, monospace; }
`;

const ACTION_ORDER = ["mission", "evidence", "debrief"] as const;

function trustedBetaUrl(value: string): boolean {
  try {
    const url = new URL(value);
    return url.protocol === "https:" && url.origin === "https://beta.pathofangels.network" && !url.username && !url.password;
  } catch {
    return false;
  }
}

function validEpisodeActions(value: unknown): value is PoAEpisodeActions {
  if (!value || typeof value !== "object" || Array.isArray(value)) return false;
  const actions = value as Record<string, unknown>;
  if (Object.keys(actions).length < 1 || Object.keys(actions).some((key) => !ACTION_ORDER.includes(key as typeof ACTION_ORDER[number]))) return false;
  return ACTION_ORDER.every((kind) => {
    const candidate = actions[kind];
    if (candidate === undefined) return true;
    if (!candidate || typeof candidate !== "object" || Array.isArray(candidate)) return false;
    const link = candidate as Record<string, unknown>;
    return Object.keys(link).sort().join(",") === "betaUrl,label" &&
      typeof link.label === "string" && link.label.length > 0 && link.label.length <= 80 &&
      typeof link.betaUrl === "string" && trustedBetaUrl(link.betaUrl);
  });
}

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
  if (typeof m.betaUrl !== "string" || !trustedBetaUrl(m.betaUrl)) return false;
  if (m.game) {
    if (m.trust !== "signed_manifest") return false;
    if (m.game.kind !== "descent" || !/^dregg:\/\/descent\/b3_[0-9a-f]{6,}$/i.test(m.game.src)) return false;
  }
  if (m.trust === "signed_manifest") {
    if (!Number.isSafeInteger(m.contentEpoch) || m.contentEpoch < 0) return false;
    if (!Number.isSafeInteger(m.counter) || m.counter < 0) return false;
    if (!/^[0-9a-f]{64}$/i.test(m.manifestDigest)) return false;
    if (!Number.isSafeInteger(m.issuedAt) || !Number.isSafeInteger(m.expiresAt) || m.expiresAt <= m.issuedAt) return false;
    if (m.actions !== undefined && (!m.episode || !validEpisodeActions(m.actions))) return false;
    if (m.fieldRecord !== undefined && (
      !m.episode || !m.fieldRecord || typeof m.fieldRecord !== "object" ||
      Object.keys(m.fieldRecord).sort().join(",") !== "federationId,finalizedReceiptCoreId,turnHash" ||
      !/^[0-9a-f]{64}$/.test(m.fieldRecord.finalizedReceiptCoreId) ||
      /^0{64}$/.test(m.fieldRecord.finalizedReceiptCoreId) ||
      !/^[0-9a-f]{64}$/.test(m.fieldRecord.federationId) ||
      !/^[0-9a-f]{64}$/.test(m.fieldRecord.turnHash)
    )) return false;
  } else {
    if (m.availability !== "authenticated_route_unavailable" || m.actions !== undefined || m.fieldRecord !== undefined) return false;
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
  private readonly fieldRecordTransport = poaFieldRecordTransportFactory?.() ?? null;
  private readonly galleyTransport = (poaGalleyTransportFactory ?? chromePoAGalleyTransport)();
  private booted = false;
  private lifecycle = 0;

  connectedCallback(): void {
    if (!this.booted) void this.boot(++this.lifecycle);
  }

  disconnectedCallback(): void {
    // A delayed manifest or receipt response must never repaint a detached
    // panel after YouTube/X replaces its SPA route.
    this.lifecycle += 1;
  }

  private context(): { href: string; channelHint?: string } {
    const channelHint = this.getAttribute("channel-hint") || undefined;
    return { href: this.getAttribute("page-url") || location.href, ...(channelHint ? { channelHint } : {}) };
  }

  private async boot(lifecycle: number): Promise<void> {
    this.booted = true;
    let response: PoACompanionResponse;
    try {
      response = PRIMED_RESPONSES.get(this) ?? await this.port.request({ op: "openContext", context: this.context() });
      PRIMED_RESPONSES.delete(this);
    } catch (error) {
      if (!this.isConnected || lifecycle !== this.lifecycle) return;
      this.failClosed(String((error as Error)?.message ?? error));
      return;
    }
    if (!this.isConnected || lifecycle !== this.lifecycle) return;
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
    this.paint(response.model, lifecycle);
  }

  private paint(model: PoACompanionModel, lifecycle: number): void {
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

    if (model.trust === "signed_manifest" && model.actions) {
      const actions = document.createElement("nav");
      actions.className = "actions";
      actions.setAttribute("aria-label", `${model.episode} episode actions`);
      for (const kind of ACTION_ORDER) {
        const route = model.actions[kind];
        if (!route) continue;
        const link = document.createElement("a");
        link.className = "action";
        link.href = route.betaUrl;
        link.target = "_blank";
        link.rel = "noopener noreferrer";
        const kindLabel = document.createElement("b");
        kindLabel.textContent = kind;
        const routeLabel = document.createElement("span");
        routeLabel.textContent = route.label;
        link.append(kindLabel, routeLabel);
        actions.appendChild(link);
      }
      terminal.appendChild(actions);
    }

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

    if (model.trust === "local_allowlist") {
      const unavailable = makeDiv(
        "unavailable",
        "Authenticated episode material is unavailable. This exact video is locally recognized only; no evidence, debrief, mission, or field record is verified.",
      );
      unavailable.setAttribute("role", "status");
      terminal.appendChild(unavailable);
    }

    if (model.trust === "signed_manifest" && model.fieldRecord) {
      terminal.appendChild(this.fieldRecordPanel(model, lifecycle));
    }

    if (model.trust === "signed_manifest") {
      terminal.appendChild(this.galleyPanel(model, lifecycle));
    }

    const links = makeDiv("links");
    const beta = document.createElement("a");
    beta.href = model.betaUrl;
    beta.textContent = "Open beta.pathofangels.network";
    beta.target = "_blank";
    beta.rel = "noopener noreferrer";
    links.appendChild(beta);
    terminal.appendChild(links);
    terminal.appendChild(makeDiv(
      "protected",
      "Protected beta route: your browser may ask for access. Cipherclerk stores no beta Basic Auth password.",
    ));
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

  private galleyPanel(
    model: Extract<PoACompanionModel, { trust: "signed_manifest" }>,
    lifecycle: number,
  ): HTMLElement {
    const panel = document.createElement("section");
    panel.className = "galley";
    panel.setAttribute("aria-label", "Live Khovokhi shift");
    const heading = document.createElement("h3");
    heading.textContent = "Live Khovokhi shift";
    const identityBoundary = makeDiv("galley-identity-boundary",
      "Cipherclerk's background attaches the permissioned active public key as a claimed preparation identity. That header authorizes nothing; the exact turn signature and finalized receipt identify the authoritative transition.");
    const statusLine = makeDiv("galley-status", "Contacting the versioned ship journal…");
    statusLine.setAttribute("role", "status");
    statusLine.setAttribute("aria-live", "polite");
    const facts = document.createElement("dl");
    const controls = makeDiv("galley-controls");
    const result = makeDiv("galley-result");
    result.hidden = true;
    panel.append(heading, identityBoundary, statusLine, facts, controls, result);

    const binding: PoAGalleyBinding = Object.freeze({
      platform: model.platform,
      contextId: model.contextId,
      experienceId: model.experienceId,
      manifestDigest: model.manifestDigest,
    });

    const refresh = async (): Promise<void> => {
      statusLine.textContent = "Refreshing the versioned ship journal…";
      controls.replaceChildren();
      try {
        const response = await this.galleyTransport.request({ op: "status", binding });
        if (!this.isConnected || lifecycle !== this.lifecycle) return;
        if (!response.ok || response.op !== "status") {
          facts.replaceChildren();
          statusLine.textContent = `Live Galley projection unavailable: ${response.error}. No local ship state is substituted.`;
          this.addRefreshButton(controls, refresh);
          return;
        }
        this.renderGalleyStatus(response.status, facts, statusLine);
        this.renderGalleyActions(response.status, binding, model, lifecycle, controls, result, refresh);
      } catch {
        if (!this.isConnected || lifecycle !== this.lifecycle) return;
        facts.replaceChildren();
        statusLine.textContent = "Live Galley projection unavailable. No local ship state is substituted.";
        this.addRefreshButton(controls, refresh);
      }
    };

    // Paint first; a delayed node response is lifecycle-bound and cannot
    // resurrect this panel after a YouTube/X SPA route replacement.
    queueMicrotask(() => {
      if (this.isConnected && lifecycle === this.lifecycle) void refresh();
    });
    return panel;
  }

  private addRefreshButton(container: HTMLElement, refresh: () => Promise<void>): void {
    const button = document.createElement("button");
    button.type = "button";
    button.textContent = "Refresh ship status";
    button.addEventListener("click", () => void refresh());
    container.appendChild(button);
  }

  private renderGalleyStatus(status: PoAGalleyStatus, facts: HTMLDListElement, statusLine: HTMLElement): void {
    statusLine.textContent = status.replay.audited
      ? `Journal replay audited through event ${status.replay.through_sequence}. The preparation identity remains a non-authoritative public claim.`
      : "Node projection returned without a successful replay audit; actions are unavailable.";
    const rows: Array<[string, string]> = [
      ["Shift", status.daily_id],
      ["Sequence", String(status.sequence)],
      ["Events", `${status.replay.event_count} shown / ${status.replay.total_event_count} total`],
      ["Semantic head", `${status.semantic_head.slice(0, 12)}…${status.semantic_head.slice(-8)}`],
    ];
    facts.replaceChildren(...rows.flatMap(([term, value]) => {
      const dt = document.createElement("dt");
      const dd = document.createElement("dd");
      dt.textContent = term;
      dd.textContent = value;
      return [dt, dd];
    }));
  }

  private renderGalleyActions(
    status: PoAGalleyStatus,
    binding: PoAGalleyBinding,
    model: Extract<PoACompanionModel, { trust: "signed_manifest" }>,
    lifecycle: number,
    controls: HTMLElement,
    result: HTMLElement,
    refresh: () => Promise<void>,
  ): void {
    controls.replaceChildren();
    for (const action of status.actions) {
      const button = document.createElement("button");
      button.type = "button";
      button.textContent = poAGalleyActionLabel(action.kind);
      const holderV1 = action.kind === "holder_sponsorship";
      const available = status.replay.audited &&
        poAGalleyAvailableAtSequence(action.expires_after_sequence, status.sequence) && !holderV1;
      button.disabled = !available;
      if (holderV1) {
        button.title = "Holder sponsorship waits for the V2 receipt that binds the active Dregg player key.";
        button.setAttribute("aria-description", button.title);
      } else if (!poAGalleyAvailableAtSequence(action.expires_after_sequence, status.sequence)) {
        button.title = "This server-issued action token expired at the current journal sequence.";
      } else if (!status.replay.audited) {
        button.title = "Actions require an audited server replay.";
      }
      if (available) {
        button.addEventListener("click", () => void this.runGalleyAction(action, binding, model, lifecycle, controls, result, refresh));
      }
      controls.appendChild(button);
    }
    this.addRefreshButton(controls, refresh);
  }

  private async runGalleyAction(
    action: PoAGalleyAction,
    binding: PoAGalleyBinding,
    model: Extract<PoACompanionModel, { trust: "signed_manifest" }>,
    lifecycle: number,
    controls: HTMLElement,
    result: HTMLElement,
    refresh: () => Promise<void>,
  ): Promise<void> {
    for (const button of controls.querySelectorAll("button")) button.disabled = true;
    result.hidden = false;
    result.textContent = "Preparing for the background-owned public identity claim. Cipherclerk will ask who actually signs the exact server-authored turn.";
    try {
      const response = await this.galleyTransport.request({ op: "command", binding, actionToken: action.action_token });
      if (!this.isConnected || lifecycle !== this.lifecycle) return;
      if (!response.ok || response.op !== "command") {
        result.textContent = `Shift action refused: ${!response.ok ? response.error : "unexpected Galley response"}`;
        await refresh();
        return;
      }
      if (response.observation !== "receipt_observed" || !response.event) {
        result.textContent = response.admission === "queued"
          ? `Turn ${response.turnHash} is queued; no journal receipt has been observed yet.`
          : `Turn ${response.turnHash} was submitted, but no exact matching journal receipt has been observed yet.`;
        await refresh();
        return;
      }
      const event = response.event;
      const intro = document.createElement("span");
      intro.textContent = `Journal event ${event.sequence} observed for exact turn ${event.turn_hash}. Receipt ${event.receipt_hash}; adjacent postcard SHA-256 checksum ${event.receipt.sha256} matched. The preparation actor header remains non-authoritative; canonical receipt verification is not yet installed. `;
      result.replaceChildren(intro);
      const signedRoute = model.actions?.evidence ?? model.actions?.debrief;
      if (signedRoute) {
        const link = document.createElement("a");
        link.href = signedRoute.betaUrl;
        link.target = "_blank";
        link.rel = "noopener noreferrer";
        link.textContent = "Open curator-signed evidence route";
        result.appendChild(link);
      }
      await refresh();
    } catch {
      if (!this.isConnected || lifecycle !== this.lifecycle) return;
      result.textContent = "Shift transport failed before an exact journal receipt was observed.";
      await refresh();
    }
  }

  private fieldRecordPanel(
    model: Extract<PoACompanionModel, { trust: "signed_manifest" }>,
    lifecycle: number,
  ): HTMLDivElement {
    const panel = makeDiv("record");
    const status = makeDiv("record-status");
    status.setAttribute("role", "status");
    status.setAttribute("aria-live", "polite");
    if (!model.fieldRecord || !this.fieldRecordTransport) {
      status.textContent = "Receipt-core observation transport is not connected in this extension build. No network receipt or quorum finality is claimed.";
      panel.appendChild(status);
      return panel;
    }

    const button = document.createElement("button");
    button.type = "button";
    button.textContent = "Check node receipt core";
    const binding: PoAFieldRecordBinding = Object.freeze({
      platform: model.platform,
      contextId: model.contextId,
      experienceId: model.experienceId,
      manifestDigest: model.manifestDigest,
      finalizedReceiptCoreId: model.fieldRecord.finalizedReceiptCoreId,
      federationId: model.fieldRecord.federationId,
      turnHash: model.fieldRecord.turnHash,
    });
    status.textContent = "A curator-signed receipt-core coordinate is attached. No node observation or quorum-finality certificate has been verified.";
    button.addEventListener("click", async () => {
      button.disabled = true;
      status.textContent = "Checking the node-reported FRC1 receipt core…";
      try {
        const value = await this.fieldRecordTransport?.readReceiptCoreObservation(binding);
        if (!this.isConnected || lifecycle !== this.lifecycle) return;
        const observation = parsePoAReceiptCoreObservation(value, binding);
        if (!observation) {
          status.textContent = "No exact matching FRC1 receipt-core observation was returned. No receipt or finality is claimed.";
          return;
        }
        status.textContent = `Node-reported FRC1 core ${observation.finalizedReceiptCoreId.slice(0, 10)}…${observation.finalizedReceiptCoreId.slice(-8)} matches the signed coordinates and canonical projection · tau round ${observation.tauRound}. This is a transport observation; quorum finality is not verified by Cipherclerk.`;
      } catch {
        if (!this.isConnected || lifecycle !== this.lifecycle) return;
        status.textContent = "Receipt-core transport is unavailable. No receipt or finality is claimed.";
      } finally {
        if (this.isConnected && lifecycle === this.lifecycle) button.disabled = false;
      }
    });
    panel.append(button, status);
    return panel;
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

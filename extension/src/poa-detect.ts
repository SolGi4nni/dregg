/**
 * SPA-safe, per-origin opt-in mounting for the Path of Angels YouTube companion.
 *
 * Detection is intentionally a HINT layer: it extracts the video id from the
 * URL and an optional channel id from YouTube's DOM, then asks the background
 * engine to recognize it. Nothing mounts until that background response is
 * verified. The browser-authenticated sender URL is authoritative there.
 */

import {
  POA_BETA_URL,
  parsePoAYouTubeUrl,
  type PoACompanionPort,
  type PoACompanionResponse,
} from "./poa";
import {
  DreggPoA,
  chromePoAPort,
  primePoAElement,
  registerPoAElement,
} from "./elements/dregg-poa";

const UPGRADE_ORIGINS_KEY = "dregg_upgrade_origins";
const MOUNT_ATTR = "data-dregg-poa-companion";

export interface DetectedPoAContext {
  href: string;
  videoId: string;
  channelHint?: string;
}

export interface PoADetectorOptions {
  isOriginAllowed?: () => Promise<boolean>;
  getContext?: () => DetectedPoAContext | null;
  getTarget?: () => Element | null;
  port?: PoACompanionPort;
  root?: Document | Element;
  debounceMs?: number;
}

async function defaultOriginAllowed(): Promise<boolean> {
  try {
    const stored = await chrome.storage.local.get(UPGRADE_ORIGINS_KEY);
    const allow = stored[UPGRADE_ORIGINS_KEY];
    if (!allow || typeof allow !== "object" || Array.isArray(allow)) return false;
    return (allow as Record<string, unknown>)[location.origin] === true;
  } catch {
    return false;
  }
}

function channelHintFromDocument(): string | undefined {
  const meta = document.querySelector<HTMLMetaElement>('meta[itemprop="channelId"][content]');
  const metaId = meta?.content?.trim();
  if (metaId && /^[A-Za-z0-9_-]{3,128}$/.test(metaId)) return metaId;
  const channelLink = document.querySelector<HTMLAnchorElement>(
    'ytd-watch-metadata a[href^="/channel/"], #owner a[href^="/channel/"]',
  );
  const match = channelLink?.getAttribute("href")?.match(/^\/channel\/([A-Za-z0-9_-]{3,128})(?:\/|$)/);
  return match?.[1];
}

export function currentPoAYouTubeContext(): DetectedPoAContext | null {
  const href = location.href;
  const parsed = parsePoAYouTubeUrl(href, channelHintFromDocument());
  if (!parsed) return null;
  return {
    href,
    videoId: parsed.videoId,
    ...(parsed.channelHint ? { channelHint: parsed.channelHint } : {}),
  };
}

function defaultTarget(): Element | null {
  // A dedicated marker is useful to PoA-owned pages and to fixtures. The other
  // selectors are stable YouTube layout regions, ordered from sidebar to below-player.
  return document.querySelector(
    "[data-dregg-poa-anchor], ytd-watch-flexy #secondary-inner, ytd-watch-flexy #below, ytd-watch-flexy #primary-inner",
  );
}

function allMounted(root: Document | Element): DreggPoA[] {
  return Array.from(root.querySelectorAll<DreggPoA>(`dregg-poa[${MOUNT_ATTR}]`));
}

function removeMounted(root: Document | Element): void {
  for (const element of allMounted(root)) element.remove();
}

function fallbackLink(betaUrl: string): HTMLAnchorElement {
  const link = document.createElement("a");
  link.dataset.poaFallback = "";
  link.href = betaUrl || POA_BETA_URL;
  link.textContent = "Open Path of Angels field terminal";
  link.target = "_blank";
  link.rel = "noopener noreferrer";
  return link;
}

/** Start the detector after the origin opt-in resolves. It is idempotent per
 * invocation, keeps exactly one companion mounted, and follows YouTube's
 * `yt-navigate-finish` SPA event as well as DOM replacement/popstate. */
export async function startPoACompanionDetector(options: PoADetectorOptions = {}): Promise<() => void> {
  registerPoAElement();
  const allowed = await (options.isOriginAllowed ?? defaultOriginAllowed)();
  if (!allowed) return () => {};

  // Do not install a document-wide observer on every site. Tests/host pages can
  // inject a context provider; production only runs on actual YouTube origins.
  if (!options.getContext) {
    const host = location.hostname.toLowerCase();
    if (host !== "www.youtube.com" && host !== "m.youtube.com" && host !== "youtube.com") return () => {};
  }

  const root = options.root ?? document;
  const getContext = options.getContext ?? currentPoAYouTubeContext;
  const getTarget = options.getTarget ?? defaultTarget;
  const port = options.port ?? chromePoAPort();
  const debounceMs = options.debounceMs ?? 80;
  let disposed = false;
  let timer: ReturnType<typeof setTimeout> | null = null;
  let generation = 0;
  let accepted: { context: DetectedPoAContext; response: Extract<PoACompanionResponse, { ok: true }> } | null = null;

  const mount = (context: DetectedPoAContext, response: Extract<PoACompanionResponse, { ok: true }>): boolean => {
    const target = getTarget();
    if (!target) return false;
    removeMounted(root);
    const element = document.createElement("dregg-poa") as DreggPoA;
    element.setAttribute(MOUNT_ATTR, context.videoId);
    element.setAttribute("page-url", context.href);
    element.setAttribute("video-id", context.videoId);
    if (context.channelHint) element.setAttribute("channel-hint", context.channelHint);
    element.appendChild(fallbackLink(response.model.betaUrl));
    // Prime before connection: the accepted model never crosses through a
    // page-readable attribute and the element does not repeat the node fetch.
    primePoAElement(element, response);
    target.prepend(element);
    return true;
  };

  const sync = async (): Promise<void> => {
    if (disposed) return;
    const context = getContext();
    if (!context) {
      accepted = null;
      removeMounted(root);
      return;
    }
    const existing = allMounted(root);
    if (existing.length === 1 && existing[0].getAttribute(MOUNT_ATTR) === context.videoId) return;
    if (accepted?.context.videoId === context.videoId) {
      mount(context, accepted.response);
      return;
    }

    const mine = ++generation;
    let response: PoACompanionResponse;
    try {
      response = await port.request({
        op: "openContext",
        context: { href: context.href, ...(context.channelHint ? { channelHint: context.channelHint } : {}) },
      });
    } catch {
      response = { ok: false, recognized: false, verified: false, tier: "none", error: "companion lookup failed" };
    }
    if (disposed || mine !== generation) return;
    // The response must bind the same URL-derived video. A stale SPA response
    // is discarded even if it was otherwise valid.
    if (!response.ok || !response.recognized || response.model.videoId !== context.videoId) {
      accepted = null;
      removeMounted(root);
      return;
    }
    accepted = { context, response };
    mount(context, response);
  };

  const schedule = (): void => {
    if (disposed || timer !== null) return;
    timer = setTimeout(() => {
      timer = null;
      void sync();
    }, debounceMs);
  };

  const observer = new MutationObserver(schedule);
  observer.observe(root, { childList: true, subtree: true });
  const navigation = (): void => {
    accepted = null;
    generation += 1;
    schedule();
  };
  window.addEventListener("popstate", navigation);
  window.addEventListener("yt-navigate-finish", navigation as EventListener);
  await sync();

  return () => {
    disposed = true;
    generation += 1;
    if (timer !== null) clearTimeout(timer);
    observer.disconnect();
    window.removeEventListener("popstate", navigation);
    window.removeEventListener("yt-navigate-finish", navigation as EventListener);
    removeMounted(root);
  };
}

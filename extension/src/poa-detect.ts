/**
 * SPA-safe, per-origin opt-in mounting for the Path of Angels media companion.
 *
 * Detection derives a YouTube video or X status id from the exact tab URL, then
 * asks the background engine to recognize it. Nothing mounts until that
 * background response is verified. The browser-authenticated sender URL is
 * authoritative there; page DOM is used only to choose a respectful mount.
 */

import {
  POA_BETA_URL,
  parsePoAContextUrl,
  parsePoAYouTubeUrl,
  poaContextId,
  type PoACompanionPort,
  type PoACompanionResponse,
  type PoAResolvedContext,
} from "./poa";
import {
  DreggPoA,
  chromePoAPort,
  primePoAElement,
  registerPoAElement,
} from "./elements/dregg-poa";

const UPGRADE_ORIGINS_KEY = "dregg_upgrade_origins";
const MOUNT_ATTR = "data-dregg-poa-companion";
const DEFAULT_REFRESH_MS = 5 * 60 * 1000;

export type DetectedPoAContext = PoAResolvedContext & { href: string };

export interface PoADetectorOptions {
  isOriginAllowed?: () => Promise<boolean>;
  getContext?: () => DetectedPoAContext | null;
  getTarget?: (context: DetectedPoAContext) => Element | null;
  port?: PoACompanionPort;
  root?: Document | Element;
  debounceMs?: number;
  /** Signed-manifest refresh cadence. Focus/visible transitions refresh sooner. */
  refreshMs?: number;
  /** Testable wall clock (unix seconds). */
  nowSeconds?: () => number;
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
    platform: "youtube",
    videoId: parsed.videoId,
    ...(parsed.channelHint ? { channelHint: parsed.channelHint } : {}),
  };
}

export function currentPoAContext(): DetectedPoAContext | null {
  const href = location.href;
  const parsed = parsePoAContextUrl(href, channelHintFromDocument());
  return parsed ? { href, ...parsed } : null;
}

export function findPoAXPostTarget(postId: string, root: ParentNode = document): Element | null {
  for (const anchor of root.querySelectorAll<HTMLAnchorElement>('article a[href*="/status/"]')) {
    let parsed: PoAResolvedContext | null = null;
    try {
      parsed = parsePoAContextUrl(new URL(anchor.getAttribute("href") || "", location.href).href);
    } catch {
      // A malformed page-owned href is not a mount target.
    }
    if (parsed?.platform === "x" && parsed.postId === postId) return anchor.closest("article");
  }
  return null;
}

function defaultTarget(context: DetectedPoAContext): Element | null {
  if (context.platform === "x") return findPoAXPostTarget(context.postId);
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
 * `yt-navigate-finish` SPA event as well as DOM replacement/popstate. A mounted
 * signed model is refreshed on focus/visibility and periodically before expiry,
 * so a higher route-free manifest revokes an already-mounted game. */
export async function startPoACompanionDetector(options: PoADetectorOptions = {}): Promise<() => void> {
  registerPoAElement();
  const allowed = await (options.isOriginAllowed ?? defaultOriginAllowed)();
  if (!allowed) return () => {};

  // Do not install a document-wide observer on every site. Tests/host pages can
  // inject a context provider; production only runs on supported media origins.
  if (!options.getContext) {
    const host = location.hostname.toLowerCase();
    if (!["www.youtube.com", "m.youtube.com", "youtube.com", "x.com", "www.x.com", "twitter.com", "www.twitter.com"].includes(host)) return () => {};
  }

  const root = options.root ?? document;
  const getContext = options.getContext ?? currentPoAContext;
  const getTarget = options.getTarget ?? defaultTarget;
  const port = options.port ?? chromePoAPort();
  const debounceMs = options.debounceMs ?? 80;
  const refreshMs = Math.max(1000, options.refreshMs ?? DEFAULT_REFRESH_MS);
  const nowSeconds = options.nowSeconds ?? (() => Math.floor(Date.now() / 1000));
  let disposed = false;
  let debounceTimer: ReturnType<typeof setTimeout> | null = null;
  let refreshTimer: ReturnType<typeof setTimeout> | null = null;
  let scheduledForce = false;
  let generation = 0;
  let accepted: { context: DetectedPoAContext; response: Extract<PoACompanionResponse, { ok: true }> } | null = null;

  const mount = (context: DetectedPoAContext, response: Extract<PoACompanionResponse, { ok: true }>): boolean => {
    const target = getTarget(context);
    if (!target) return false;
    removeMounted(root);
    const element = document.createElement("dregg-poa") as DreggPoA;
    const contextId = poaContextId(context);
    element.setAttribute(MOUNT_ATTR, `${context.platform}:${contextId}`);
    element.setAttribute("page-url", context.href);
    element.setAttribute("platform", context.platform);
    element.setAttribute("context-id", contextId);
    if (context.platform === "youtube") {
      element.setAttribute("video-id", context.videoId);
      if (context.channelHint) element.setAttribute("channel-hint", context.channelHint);
    } else {
      element.setAttribute("post-id", context.postId);
    }
    element.appendChild(fallbackLink(response.model.betaUrl));
    // Prime before connection: the accepted model never crosses through a
    // page-readable attribute and the element does not repeat the node fetch.
    primePoAElement(element, response);
    if (context.platform === "x") target.insertAdjacentElement("afterend", element);
    else target.prepend(element);
    return true;
  };

  const isExpired = (entry: typeof accepted): boolean =>
    !!entry && entry.response.model.trust === "signed_manifest" && entry.response.model.expiresAt <= nowSeconds();

  const responseIdentity = (response: Extract<PoACompanionResponse, { ok: true }>): string =>
    response.model.trust === "signed_manifest"
      ? `signed:${response.model.manifestDigest}`
      : `local:${response.model.contextId}`;

  const clearRefresh = (): void => {
    if (refreshTimer !== null) clearTimeout(refreshTimer);
    refreshTimer = null;
  };

  let schedule: (force?: boolean) => void;

  const armRefresh = (): void => {
    clearRefresh();
    if (disposed || !accepted) return;
    let delay = refreshMs;
    if (accepted.response.model.trust === "signed_manifest") {
      const untilExpiry = Math.max(0, (accepted.response.model.expiresAt - nowSeconds()) * 1000);
      delay = Math.min(delay, untilExpiry);
    }
    refreshTimer = setTimeout(() => {
      refreshTimer = null;
      schedule(true);
    }, delay);
  };

  const sync = async (force = false): Promise<void> => {
    if (disposed) return;
    const context = getContext();
    if (!context) {
      accepted = null;
      clearRefresh();
      removeMounted(root);
      return;
    }
    const existing = allMounted(root);
    const identity = `${context.platform}:${poaContextId(context)}`;
    let hasCurrentMount = existing.length === 1 && existing[0].getAttribute(MOUNT_ATTR) === identity;
    let previous = accepted && accepted.context.platform === context.platform &&
      poaContextId(accepted.context) === poaContextId(context) ? accepted : null;

    // Never display a panel beside the wrong SPA route while the new lookup is
    // in flight. X relies on DOM mutation to notice pushState navigation, so
    // this check is independent of platform-specific navigation events.
    if (existing.length > 0 && !hasCurrentMount) {
      removeMounted(root);
      hasCurrentMount = false;
    }

    // The signed lease is a display/authority boundary, not merely a deadline
    // for the next request. Remove an expired panel before transport begins so
    // a slow or hung worker cannot keep a nested game alive past expiresAt.
    if (previous?.response.model.trust === "signed_manifest" && isExpired(previous)) {
      accepted = null;
      clearRefresh();
      removeMounted(root);
      hasCurrentMount = false;
      previous = null;
    }
    if (!force && hasCurrentMount) {
      armRefresh();
      return;
    }
    if (!force && previous) {
      mount(context, previous.response);
      armRefresh();
      return;
    }

    const mine = ++generation;
    let response: PoACompanionResponse;
    try {
      response = await port.request({
        op: "openContext",
        context: {
          href: context.href,
          ...(context.platform === "youtube" && context.channelHint ? { channelHint: context.channelHint } : {}),
        },
      });
    } catch {
      response = { ok: false, recognized: false, verified: false, tier: "none", error: "companion lookup failed" };
    }
    if (disposed || mine !== generation) return;
    // The response must bind the same browser-authenticated media identity. A stale SPA response
    // is discarded even if it was otherwise valid.
    if (!response.ok || !response.recognized || response.model.platform !== context.platform ||
        response.model.contextId !== poaContextId(context)) {
      // A transport miss, 401 or stale rollback response must not erase an
      // already-verified route before its signed expiry. At expiry it fails
      // closed. A local shell carries no signed lease and may disappear.
      if (previous?.response.model.trust === "signed_manifest" && !isExpired(previous)) {
        accepted = previous;
        if (!hasCurrentMount) mount(context, previous.response);
        armRefresh();
        return;
      }
      accepted = null;
      clearRefresh();
      removeMounted(root);
      return;
    }

    // The background validates freshness before returning, but the signed
    // lease may expire while its response crosses a slow runtime-message or
    // network boundary. Never mount a response that is expired on arrival.
    if (response.model.trust === "signed_manifest" && response.model.expiresAt <= nowSeconds()) {
      accepted = null;
      clearRefresh();
      removeMounted(root);
      return;
    }

    // A transient unauthenticated/local response cannot downgrade a still-live
    // signed panel. A higher signed route-free response is accepted and mounted
    // below, removing any nested game immediately.
    if (previous?.response.model.trust === "signed_manifest" &&
        response.model.trust === "local_allowlist" && !isExpired(previous)) {
      accepted = previous;
      if (!hasCurrentMount) mount(context, previous.response);
      armRefresh();
      return;
    }

    const unchanged = previous && responseIdentity(previous.response) === responseIdentity(response);
    accepted = { context, response };
    if (!unchanged || !hasCurrentMount) mount(context, response);
    armRefresh();
  };

  schedule = (force = false): void => {
    if (disposed) return;
    scheduledForce ||= force;
    if (debounceTimer !== null) return;
    debounceTimer = setTimeout(() => {
      debounceTimer = null;
      const runForced = scheduledForce;
      scheduledForce = false;
      void sync(runForced);
    }, debounceMs);
  };

  const observer = new MutationObserver(() => schedule());
  observer.observe(root, { childList: true, subtree: true });
  const navigation = (): void => {
    accepted = null;
    clearRefresh();
    generation += 1;
    schedule();
  };
  const refreshOnFocus = (): void => schedule(true);
  const refreshOnVisible = (): void => {
    if (document.visibilityState === "visible") schedule(true);
  };
  window.addEventListener("popstate", navigation);
  window.addEventListener("yt-navigate-finish", navigation as EventListener);
  window.addEventListener("focus", refreshOnFocus);
  document.addEventListener("visibilitychange", refreshOnVisible);
  await sync();

  return () => {
    disposed = true;
    generation += 1;
    if (debounceTimer !== null) clearTimeout(debounceTimer);
    clearRefresh();
    observer.disconnect();
    window.removeEventListener("popstate", navigation);
    window.removeEventListener("yt-navigate-finish", navigation as EventListener);
    window.removeEventListener("focus", refreshOnFocus);
    document.removeEventListener("visibilitychange", refreshOnVisible);
    removeMounted(root);
  };
}

/**
 * THE DETECTOR (DREGG-QUIET-UPGRADE.md §2) — a single, platform-agnostic
 * content-script scanner that quietly upgrades a plaintext dregg-thing into a
 * live `<dregg-poll>`.
 *
 *  - A `MutationObserver` scans text nodes + anchor hrefs for BOTH the canonical
 *    `dregg://poll/<addr>` and the mirror `https://dregg.net/d/poll/<addr>`.
 *  - Idempotent: upgraded content is marked (`data-dregg-upgraded`, keyed by the
 *    canonical content-addr) and never double-upgraded; SPA re-mounts re-scan.
 *  - Respectful: only the matched node is replaced; surrounding prose is kept;
 *    the original link is moved into the element's light DOM as a fallback.
 *  - Per-origin opt-in (§6): default-deny unknown origins.
 *  - t.co adapter: when an anchor's href is a known shortener, prefer its visible
 *    text. This is the ONLY platform-specific code, and it is a DOM-quirk shim —
 *    no platform-specific trust logic (§2, §6).
 */

import { parseDreggUri, canonicalUri } from "./port";
import { registerDreggElements } from "./elements/dregg-poll";

// Loose token match (the engine validates the addr strictly + fails closed).
const THING_RE = /(?:dregg:\/\/poll\/[A-Za-z0-9_\-]+|https?:\/\/dregg\.net\/d\/poll\/[A-Za-z0-9_\-]+)/g;

// Known link shorteners whose href is rewritten but visible text is preserved.
const SHORTENERS = new Set(["t.co", "bit.ly", "tinyurl.com", "ow.ly", "buff.ly", "goo.gl", "t.ly", "lnkd.in"]);

export interface DetectorOptions {
  /** Override the per-origin opt-in gate (default: chrome.storage allowlist). */
  isOriginAllowed?: () => Promise<boolean>;
  /** Scan root (default: document). */
  root?: ParentNode & Node;
}

const processedTextNodes = new WeakSet<Text>();
const processedAnchors = new WeakSet<HTMLAnchorElement>();

/** Per-origin opt-in, default-deny. Reads `dregg_upgrade_origins` (object keyed
 * by origin) from extension storage; an unknown origin is denied. */
async function defaultOriginAllowed(): Promise<boolean> {
  try {
    const origin = location.origin;
    const stored = await chrome.storage.local.get("dregg_upgrade_origins");
    const allow = stored.dregg_upgrade_origins;
    if (!allow || typeof allow !== "object" || Array.isArray(allow)) return false;
    return allow[origin] === true;
  } catch {
    return false;
  }
}

function hostnameOf(href: string): string | null {
  try {
    return new URL(href).hostname.toLowerCase();
  } catch {
    return null;
  }
}

function isUpgraded(node: Node): boolean {
  let el: Node | null = node.nodeType === Node.ELEMENT_NODE ? node : node.parentNode;
  while (el) {
    if (el instanceof Element) {
      const tag = el.tagName.toLowerCase();
      if (tag === "dregg-poll" || el.hasAttribute?.("data-dregg-upgraded")) return true;
    }
    el = el.parentNode;
  }
  return false;
}

/** Build a `<dregg-poll>` for a canonical uri, with a fallback link (the mirror
 * form, always a working clickable) moved/created in its light DOM. */
function makePollElement(canonical: string, addr: string, fallback: HTMLAnchorElement | null, fallbackText: string): HTMLElement {
  const el = document.createElement("dregg-poll");
  el.setAttribute("src", canonical);
  el.setAttribute("data-dregg-upgraded", canonical);
  const link = fallback ?? document.createElement("a");
  if (!fallback) {
    link.textContent = fallbackText || canonical;
  }
  // The mirror form is the graceful-degradation target (a still-verifiable
  // server-rendered view for anyone without the extension).
  link.setAttribute("href", `https://dregg.net/d/poll/${addr}`);
  el.appendChild(link);
  return el;
}

/** Upgrade a text node: split around each match, insert an element per match. */
function upgradeTextNode(text: Text): void {
  if (processedTextNodes.has(text)) return;
  if (isUpgraded(text)) {
    processedTextNodes.add(text);
    return;
  }
  // A dregg reference used as an anchor's visible text is the ANCHOR path's job
  // (handles t.co unwrap) — never double-upgrade it from the text walker.
  if (text.parentElement?.closest("a")) {
    processedTextNodes.add(text);
    return;
  }
  const content = text.data;
  THING_RE.lastIndex = 0;
  const matches: Array<{ index: number; raw: string }> = [];
  let m: RegExpExecArray | null;
  while ((m = THING_RE.exec(content))) matches.push({ index: m.index, raw: m[0] });
  if (matches.length === 0) return;

  const parent = text.parentNode;
  if (!parent) return;
  processedTextNodes.add(text);

  const frag = document.createDocumentFragment();
  let cursor = 0;
  for (const { index, raw } of matches) {
    if (index > cursor) frag.appendChild(document.createTextNode(content.slice(cursor, index)));
    const parsed = parseDreggUri(raw);
    const canonical = canonicalUri(raw);
    if (parsed && canonical) {
      frag.appendChild(makePollElement(canonical, parsed.addr, null, raw));
    } else {
      frag.appendChild(document.createTextNode(raw));
    }
    cursor = index + raw.length;
  }
  if (cursor < content.length) frag.appendChild(document.createTextNode(content.slice(cursor)));
  parent.replaceChild(frag, text);
}

/** Upgrade an anchor: the href OR (for a shortener) the visible text. */
function upgradeAnchor(a: HTMLAnchorElement): void {
  if (processedAnchors.has(a)) return;
  if (isUpgraded(a)) {
    processedAnchors.add(a);
    return;
  }
  const href = a.getAttribute("href") || "";
  const host = hostnameOf(href);
  // t.co adapter: prefer the anchor's visible text when the href is a shortener.
  const candidate = host && SHORTENERS.has(host) ? a.textContent || "" : href;
  const parsed = parseDreggUri(candidate.trim());
  const canonical = canonicalUri(candidate.trim());
  if (!parsed || !canonical) return;

  processedAnchors.add(a);
  const parent = a.parentNode;
  if (!parent) return;
  // Move the original anchor into the element's light DOM as the fallback.
  const el = makePollElement(canonical, parsed.addr, a.cloneNode(true) as HTMLAnchorElement, a.textContent || "");
  parent.replaceChild(el, a);
}

function scan(root: ParentNode & Node): void {
  // Anchors FIRST (they own their inner text; t.co unwrap replaces them), then
  // free-standing text nodes (skipping any still inside an anchor).
  const anchors =
    root instanceof Element || root instanceof Document
      ? Array.from(root.querySelectorAll("a[href]"))
      : [];
  for (const a of anchors) upgradeAnchor(a as HTMLAnchorElement);

  const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
    acceptNode(node): number {
      const t = node as Text;
      if (!t.data || t.data.indexOf("dregg") === -1) return NodeFilter.FILTER_REJECT;
      return NodeFilter.FILTER_ACCEPT;
    },
  });
  const texts: Text[] = [];
  let n: Node | null;
  while ((n = walker.nextNode())) texts.push(n as Text);
  for (const t of texts) upgradeTextNode(t);
}

/**
 * Start the detector. Registers `<dregg-poll>`, does an initial scan, and
 * watches for mutations. Resolves the per-origin opt-in ONCE up front; if the
 * origin is not allowed, nothing is upgraded (the safe default). Returns a
 * disconnect function.
 */
export async function startDetector(opts: DetectorOptions = {}): Promise<() => void> {
  registerDreggElements();
  const allowed = await (opts.isOriginAllowed ?? defaultOriginAllowed)();
  if (!allowed) return () => {};

  const root = opts.root ?? document;
  scan(root);

  const observer = new MutationObserver((records) => {
    for (const rec of records) {
      if (rec.type === "characterData" && rec.target.nodeType === Node.TEXT_NODE) {
        // Text edited in place (SPA) — allow a re-scan of this node.
        processedTextNodes.delete(rec.target as Text);
        upgradeTextNode(rec.target as Text);
      }
      for (const added of Array.from(rec.addedNodes)) {
        if (added.nodeType === Node.TEXT_NODE) {
          upgradeTextNode(added as Text);
        } else if (added.nodeType === Node.ELEMENT_NODE) {
          scan(added as Element);
        }
      }
    }
  });
  observer.observe(root instanceof Document ? root.documentElement || root : (root as Node), {
    childList: true,
    subtree: true,
    characterData: true,
  });
  return () => observer.disconnect();
}

/**
 * Content script: bridges page.js (window.dregg) <-> background service worker.
 * Validates origins, checks allowlists, uses nonce-based event channels.
 */

import type { MessageType } from "./types";
import { startDetector } from "./detect";
import { registerCompositionElements } from "./elements/dregg-embed";
import { registerDocElement } from "./elements/dregg-doc";
import { registerStoryElement } from "./elements/dregg-story";
import { registerDescentElement } from "./elements/dregg-descent";
import { registerSpriteElement } from "./elements/dregg-sprite";

// Generate a random nonce for this injection session to prevent event spoofing.
const SESSION_NONCE = crypto.randomUUID();

// ── Quiet-upgrade detector (DREGG-QUIET-UPGRADE.md §2/§3) ───────────────────
// Runs in this isolated content-script world (NOT the page's main world): it
// registers <dregg-poll> and scans for plaintext dregg-things, upgrading each
// into a live, verified, votable thin view whose engine lives in the
// background. Per-origin opt-in (default-deny) gates whether anything upgrades.
void startDetector();

// Composition delivery layer (DOC-CELL-COMPOSITION §2.3, DREGG-WEB-SPEC pillar 5):
// register the `<dregg-embed>` (whole child cell, recursive) and
// `<dregg-transclude>` (value quote) custom elements so author-placed tags — and
// the nested `<dregg-*>` tags a resolved child renders — upgrade to closed-shadow
// thin views whose CellEngine lives in the background.
registerCompositionElements();

// The verifiable document surface (DREGG-DOCUMENT-FOUNDATION): register
// `<dregg-doc>` — the culminating authoring path. It renders a verifiable
// document, holds a first-class conflict as BOTH alternatives side by side, and
// PUBLISHES a resolution as a real verified turn through the background DocEngine.
registerDocElement();

// The verifiable choose-your-own-adventure (MEGASPEC §4): register `<dregg-story>`.
// READ + VERIFY are the free, trustless tier (a bare browser SEES the story + a
// replay-verified badge); CHOOSING a passage is a real custody-gated verified turn
// routed through the background StoryEngine, and a stranger can replay the receipt chain.
registerStoryElement();

// The Descent, played IN THE TAB (docs/GAME-STRATEGY.md): register `<dregg-descent>`.
// PLAY + VERIFY are the free, trustless, PRIVATE tier — a move press advances today's
// beacon-seeded permadeath run as a real cap-gated verified turn on the in-tab executor,
// and a stranger can replay the whole receipt chain. The ONLY custody write is the
// opt-in SETTLE/PUBLISH to the node's no-cheat leaderboard, routed through the background
// DescentEngine; until published the run stays private.
registerDescentElement();

// The in-house DETERMINISTIC sprite, painted in the tab (docs/CONTENT-AND-ASSET-SPEC.md):
// register `<dregg-sprite kind="gear|card" asset="<hex>">`. It asks the background SpriteEngine
// (which drives the wasm `spriteSvg`, wasm/src/bindings_sprite.rs) for the deterministic SVG
// of a content-addressed asset and paints it into a closed shadow root. Pure function of
// public data — same asset ⇒ the byte-identical sprite a stranger re-renders; no keys, no
// custody, no trust decision. A bad kind / non-hex / wrong-length id fails closed (no render).
registerSpriteElement();

// Methods that any page origin can call without prior approval.
const UNRESTRICTED_METHODS = new Set<MessageType>([
  "dregg:isConnected",
  "dregg:canAuthorize",
  "dregg:subscribe",
  "dregg:discoverServices",
  "dregg:resolvePath",
  "dregg:storageQuota",
  "dregg:federationStatus",
  "dregg:listKnownFederations",
]);

// Methods that require the origin to be in the user-approved allowlist.
const RESTRICTED_METHODS = new Set<MessageType>([
  "dregg:authorize",
  "dregg:provision",
  "dregg:postIntent",
  "dregg:signTurn",
  "dregg:signTurnV3",
  // Offering turn (G1 rung 2): a key-touching signature over a
  // dreggnet-offerings move — per-origin grant + the un-overlayable
  // confirm-intent consent, exactly like signTurnV3.
  "dregg:signOfferingTurn",
  "dregg:listOutbox",
  "dregg:flushOutbox",
  "dregg:dropOutboxEntry",
  "dregg:queryBalance",
  "dregg:shareCapability",
  "dregg:acceptCapability",
  "dregg:createHandoff",
  "dregg:mountService",
  "dregg:storageWrite",
  "dregg:storageRead",
  "dregg:proposeRoutes",
  "dregg:voteOnProposal",
  "dregg:registerFederation",
  "dregg:createCapTpDeliveredAuth",
  // Shielded proof composition (now sound: Poseidon2 membership) + the EVM
  // signing leg + the fhEgg sealed-bid ceremony + DrEX routed through the
  // extension — each is a key-touching operation, gated per-origin and behind
  // the un-overlayable confirm-intent consent.
  "dregg:composeProofs",
  "dregg:evmGetAddress",
  "dregg:evmPersonalSign",
  "dregg:evmSignTypedData",
  "dregg:sealedBidCommit",
  "dregg:sealedBidReveal",
  // The launchpad bidder leg: each turn seals or opens a bid with the wallet's
  // EVM key and escrows real value, so it is gated exactly like the rest.
  "dregg:launchpadCommit",
  "dregg:launchpadReveal",
  "dregg:launchpadStatus",
  "dregg:launchpadReclaimTx",
  "dregg:drexPlaceOrder",
]);

// Inject page.js with the session nonce as a data attribute.
const script = document.createElement("script");
script.src = chrome.runtime.getURL("dist/page.js");
script.dataset.dreggNonce = SESSION_NONCE;
(document.head || document.documentElement).appendChild(script);
script.onload = (): void => { script.remove(); };

/**
 * Check if the current page origin is allowed for a specific method.
 */
async function isOriginAllowed(origin: string, method: string): Promise<boolean> {
  try {
    const stored = await chrome.storage.local.get("dregg_allowed_origins");
    const allowlist = stored.dregg_allowed_origins || {};
    // P1-2: legacy array form is treated as no permission; user must re-prompt.
    if (Array.isArray(allowlist)) return false;
    const entry = allowlist[origin] as { methods: string[]; expires: number } | undefined;
    if (!entry) return false;
    if (entry.expires && entry.expires < Date.now()) return false;
    // No wildcard semantic — exact method match only.
    return entry.methods.includes(method);
  } catch {
    return false;
  }
}

/**
 * Request permission from the user for this origin to use restricted methods.
 */
async function requestOriginPermission(origin: string, method: string): Promise<boolean> {
  const response = await chrome.runtime.sendMessage({
    type: "dregg:requestOriginPermission",
    origin,
    method,
  });
  return response?.granted === true;
}

// Forward requests from page -> background (with security checks).
window.addEventListener(`dregg:request:${SESSION_NONCE}`, (async (event: Event): Promise<void> => {
  const customEvent = event as CustomEvent;
  // NOTE: no isTrusted check — script-dispatched CustomEvents are NEVER
  // trusted (isTrusted is true only for UA-generated events), so requiring it
  // would drop every page request, including page.js's own. The channel's
  // authentication is the per-injection SESSION_NONCE event name plus the
  // per-origin/per-method allowlist below.
  const detail = customEvent.detail;
  if (!detail || !detail.type) return;

  const origin = window.location.origin;
  const messageType = detail.type as MessageType;

  // Check if this method is allowed for this origin (per-method allowlist).
  if (RESTRICTED_METHODS.has(messageType)) {
    const allowed = await isOriginAllowed(origin, messageType);
    if (!allowed) {
      const granted = await requestOriginPermission(origin, messageType);
      if (!granted) {
        window.dispatchEvent(new CustomEvent(`dregg:response:${SESSION_NONCE}`, {
          detail: { id: detail.id, error: "Origin not authorized for this method. User denied permission." },
        }));
        return;
      }
    }
  } else if (!UNRESTRICTED_METHODS.has(messageType)) {
    // Unknown or removed method -- reject.
    window.dispatchEvent(new CustomEvent(`dregg:response:${SESSION_NONCE}`, {
      detail: { id: detail.id, error: `Method "${messageType}" is not available from page context.` },
    }));
    return;
  }

  // Forward to background with origin metadata.
  const response = await chrome.runtime.sendMessage({
    ...detail,
    _origin: origin,
  });
  window.dispatchEvent(new CustomEvent(`dregg:response:${SESSION_NONCE}`, { detail: response }));
}) as EventListener);

// Forward event notifications from background -> page.
// Also the entry point for a future content-script shadow-DOM passive debugger panel
// (Phase 1 §6): the listener already receives all "dregg:event" (incl. new "activity",
// "receipt", "root", "intent", "note_announcement", "federation" from STARBRIDGE-FOLLOWUP-06).
// A shadow panel can read chrome.runtime messages directly here (before or instead of
// forwarding) and mount <dregg-activity> using a shim runtime exposing getTraceEvents().
chrome.runtime.onMessage.addListener((
  message: { type: string; event?: string; payload?: unknown },
  _sender: chrome.runtime.MessageSender,
  sendResponse: (response: { ok: boolean }) => void,
): boolean => {
  if (message.type === "dregg:event") {
    window.dispatchEvent(new CustomEvent(`dregg:event:${SESSION_NONCE}`, {
      detail: { eventName: message.event, payload: message.payload },
    }));
    sendResponse({ ok: true });
  }
  return false;
});

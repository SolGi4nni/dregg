// Content script: bridges page.js (window.dregg) <-> background service worker.
// Security: validates origins, checks allowlists, uses nonce-based event channels.

// Generate a random nonce for this injection session to prevent event spoofing.
const SESSION_NONCE = crypto.randomUUID();

// Methods that any page origin can call without prior approval.
const UNRESTRICTED_METHODS = new Set([
  'dregg:isConnected',
  'dregg:canAuthorize',
  'dregg:subscribe',
  'dregg:discoverServices',
  'dregg:resolvePath',
  'dregg:storageQuota',
  'dregg:federationStatus',
]);

// Methods that require the origin to be in the user-approved allowlist.
const RESTRICTED_METHODS = new Set([
  'dregg:authorize',
  'dregg:provision',
  'dregg:postIntent',
  'dregg:offerCapability',
  'dregg:signTurn',
  'dregg:queryBalance',
  'dregg:shareCapability',
  'dregg:acceptCapability',
  'dregg:createHandoff',
  'dregg:mountService',
  'dregg:storageWrite',
  'dregg:storageRead',
  'dregg:proposeRoutes',
  'dregg:voteOnProposal',
]);

// Pending permission prompts: origin -> { resolve, reject }[]
const pendingPermissions = new Map();

// Inject page.js with the session nonce as a data attribute.
// Note: NOT set as type="module" for Firefox MV3 compatibility.
const script = document.createElement('script');
script.src = chrome.runtime.getURL('page.js');
script.dataset.dreggNonce = SESSION_NONCE;
(document.head || document.documentElement).appendChild(script);
script.onload = () => script.remove();

/**
 * Check if the current page origin is allowed for a specific method.
 */
async function isOriginAllowed(origin, method) {
  try {
    const stored = await chrome.storage.local.get('dregg_allowed_origins');
    const allowlist = stored.dregg_allowed_origins || {};
    // Handle legacy array format.
    if (Array.isArray(allowlist)) {
      return allowlist.includes(origin);
    }
    const entry = allowlist[origin];
    if (!entry) return false;
    // Check expiry.
    if (entry.expires && entry.expires < Date.now()) return false;
    // Check method.
    return entry.methods.includes('*') || entry.methods.includes(method);
  } catch {
    return false;
  }
}

/**
 * Request permission from the user for this origin to use restricted methods.
 * Opens a popup for the user to approve/deny.
 */
async function requestOriginPermission(origin, method) {
  // Send a permission request to the background, which will show the popup.
  const response = await chrome.runtime.sendMessage({
    type: 'dregg:requestOriginPermission',
    origin,
    method,
  });
  return response?.granted === true;
}

// Forward requests from page -> background (with security checks).
window.addEventListener(`dregg:request:${SESSION_NONCE}`, async (event) => {
  // Bug 3 fix: only accept trusted events (not synthetically dispatched).
  if (!event.isTrusted) return;

  const detail = event.detail;
  if (!detail || !detail.type) return;

  const origin = window.location.origin;
  const messageType = detail.type;

  // Check if this method is allowed for this origin (per-method allowlist).
  if (RESTRICTED_METHODS.has(messageType)) {
    const allowed = await isOriginAllowed(origin, messageType);
    if (!allowed) {
      // Request permission from the user for this specific method.
      const granted = await requestOriginPermission(origin, messageType);
      if (!granted) {
        window.dispatchEvent(new CustomEvent(`dregg:response:${SESSION_NONCE}`, {
          detail: { id: detail.id, error: 'Origin not authorized for this method. User denied permission.' },
        }));
        return;
      }
    }
  } else if (!UNRESTRICTED_METHODS.has(messageType)) {
    // Unknown or removed method — reject.
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
});

// Forward event notifications from background -> page.
chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  if (message.type === 'dregg:event') {
    window.dispatchEvent(new CustomEvent(`dregg:event:${SESSION_NONCE}`, {
      detail: { eventName: message.event, payload: message.payload },
    }));
    sendResponse({ ok: true });
  }
  return false;
});

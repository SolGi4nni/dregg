// Confirm-intent popup — nonce-bound.
// P0-1/P0-2: payload (action, spec, options, origin) fetched via background
// using the per-popup nonce. Decision message includes the nonce so the
// background can validate it came from this popup window.

function parseNonce() {
  const hash = window.location.hash || '';
  const m = hash.match(/(?:^#|&)nonce=([0-9a-f]+)/);
  return m ? m[1] : null;
}

const NONCE = parseNonce();

const actionEl = document.getElementById('action');
const specEl = document.getElementById('spec');
const optionsEl = document.getElementById('options');
const originEl = document.getElementById('origin');
const acceptBtn = document.getElementById('acceptBtn');
const rejectBtn = document.getElementById('rejectBtn');

let initialized = false;

// What this popup DISPLAYED, captured once at render time. The decision
// message echoes these so the background can refuse any accept whose
// displayed turn/domain differ from what it signed (post-confirmation
// substitution is treated as a decline).
let displayedTurnId = null;
let displayedFederationDomainHex = null;
// Offering-turn confirmations bind the SHA-256 of the exact canonical message
// about to be signed; the decision echoes it so the background refuses an
// accept for anything other than what this popup displayed.
let displayedOfferingBinding = null;

// Append one label/value row to the details panel (textContent only — the
// values are page-supplied strings and must never parse as markup).
function addDetailRow(label, value, mono) {
  const details = document.getElementById('details');
  if (!details) return;
  const row = document.createElement('div');
  row.className = 'detail-row';
  const labelEl = document.createElement('span');
  labelEl.className = 'detail-label';
  labelEl.textContent = label;
  const valueEl = document.createElement('span');
  valueEl.className = 'detail-value';
  valueEl.textContent = value;
  if (mono) valueEl.style.fontFamily = "'Courier New', monospace";
  row.appendChild(labelEl);
  row.appendChild(valueEl);
  details.appendChild(row);
}

async function init() {
  if (!NONCE) {
    actionEl.textContent = 'Error: no nonce — cannot display intent.';
    acceptBtn.disabled = true;
    return;
  }
  try {
    const resp = await chrome.runtime.sendMessage({
      type: 'dregg:getPendingDecision',
      nonce: NONCE,
    });
    if (resp && resp.result && resp.result.payload) {
      const p = resp.result.payload;
      actionEl.textContent = p.action || 'unknown';
      if (originEl) originEl.textContent = p.origin || 'unknown';
      if (p.action === 'signTurn' && typeof p.explanation === 'string') {
        // Turn-signing confirmation: show the cipherclerk's faithful reading
        // of the turn (the same human terms the SDK's explain renders, bound
        // to the canonical [turn <hash>]) instead of raw spec JSON.
        const titleEl = document.getElementById('title');
        const subtitleEl = document.getElementById('subtitle');
        if (titleEl) titleEl.textContent = 'Sign Turn';
        if (subtitleEl) subtitleEl.textContent =
          'A page asks your cipherclerk to sign this turn. This is exactly what it does:';
        const explanationEl = document.getElementById('explanation');
        if (explanationEl) {
          explanationEl.textContent = p.explanation;
          explanationEl.style.display = 'block';
        }
        if (p.hasUnknown) {
          const warningEl = document.getElementById('unknownWarning');
          if (warningEl) warningEl.style.display = 'block';
        }
        // Show the FULL federation domain the turn was signed under — all 64
        // lowercase hex characters, never truncated. Captured for the
        // decision echo below.
        displayedTurnId = typeof p.turnId === 'string' ? p.turnId : null;
        if (typeof p.federationDomainHex === 'string') {
          displayedFederationDomainHex = p.federationDomainHex;
          const federationRow = document.getElementById('federationRow');
          const federationEl = document.getElementById('federationDomain');
          if (federationRow && federationEl) {
            federationEl.textContent = p.federationDomainHex;
            federationRow.style.display = 'flex';
          }
        }
        const specRow = document.getElementById('specRow');
        const optionsRow = document.getElementById('optionsRow');
        if (specRow) specRow.style.display = 'none';
        if (optionsRow) optionsRow.style.display = 'none';
      } else if (p.action === 'signOfferingTurn') {
        // Offering-turn signing (G1 rung 2): render the human-readable intent
        // — offering, session, move, arg, text, replay counter, and the
        // signing identity — exactly the fields the canonical
        // dregg-offering-turn-v1 message binds.
        const titleEl = document.getElementById('title');
        const subtitleEl = document.getElementById('subtitle');
        if (titleEl) titleEl.textContent = 'Sign Offering Turn';
        if (subtitleEl) subtitleEl.textContent =
          'A page asks your cipherclerk to sign this offering move with your identity key. This is exactly what will be signed:';
        addDetailRow('Offering', String(p.offeringKey ?? ''));
        addDetailRow('Session', String(p.sessionId ?? ''));
        addDetailRow('Move', String(p.moveTurn ?? ''));
        addDetailRow('Argument', String(p.argDecimal ?? ''));
        if (typeof p.text === 'string') addDetailRow('Text', p.text, true);
        addDetailRow('Replay counter', String(p.counterDecimal ?? ''));
        addDetailRow(
          'Signing identity',
          (typeof p.signerProfile === 'string' && p.signerProfile ? p.signerProfile + ' — ' : '') +
            String(p.signerPubkeyHex ?? ''),
          true,
        );
        const explanationEl = document.getElementById('explanation');
        if (explanationEl) {
          explanationEl.textContent =
            'The replay counter must be strictly newer than the last move this identity made in this session. ' +
            'The server refuses stale counters, so this exact signature can land at most once.';
          explanationEl.style.display = 'block';
        }
        displayedOfferingBinding = typeof p.bindingHex === 'string' ? p.bindingHex : null;
        const specRow = document.getElementById('specRow');
        const optionsRow = document.getElementById('optionsRow');
        if (specRow) specRow.style.display = 'none';
        if (optionsRow) optionsRow.style.display = 'none';
      } else {
        specEl.textContent = JSON.stringify(p.matchSpec || {}, null, 2);
        optionsEl.textContent = JSON.stringify(p.options || {}, null, 2);
      }
      initialized = true;
    } else {
      actionEl.textContent = 'Error: pending decision not found.';
      acceptBtn.disabled = true;
    }
  } catch (_e) {
    actionEl.textContent = 'Error: failed to load intent.';
    acceptBtn.disabled = true;
  }
}

function sendDecision(confirmed) {
  if (!NONCE) return;
  const message = {
    type: 'dregg:intentConfirmation',
    nonce: NONCE,
    confirmed,
  };
  // Turn-signing decisions bind what was DISPLAYED: echo the turn id and
  // federation domain rendered above so the background refuses an accept for
  // anything other than exactly what the user saw.
  if (displayedTurnId !== null) message.turnId = displayedTurnId;
  if (displayedFederationDomainHex !== null) message.federationDomainHex = displayedFederationDomainHex;
  // Offering-turn decisions bind the displayed canonical-message digest.
  if (displayedOfferingBinding !== null) message.offeringBindingHex = displayedOfferingBinding;
  chrome.runtime.sendMessage(message);
}

acceptBtn.addEventListener('click', () => {
  sendDecision(true);
  window.close();
});

rejectBtn.addEventListener('click', () => {
  sendDecision(false);
  window.close();
});

window.addEventListener('beforeunload', () => {
  if (initialized) sendDecision(false);
});

init();

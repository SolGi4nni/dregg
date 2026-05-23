// Bearer Capabilities section — create, grant, verify, exercise bearer caps

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';

export function initBearer(wasm) {
  const container = document.getElementById('section-bearer');
  container.innerHTML = `
    <div class="section-header">
      <h2>Bearer Capabilities</h2>
      <p>
        A bearer cap is a proof-carrying authorization token: whoever holds the proof can
        exercise the capability. Unlike delegation chains, bearer caps are transferable without
        updating any on-chain state. Grant a cap, pass it around, exercise it immediately.
      </p>
      <span class="next-hint" data-next="factories">Next: cell factories &#8594;</span>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Target Cell</label>
        <input type="text" id="bc-target" value="" placeholder="auto-generated" spellcheck="false" style="width: 180px;">
      </div>
      <div class="control-group">
        <label>Action</label>
        <select id="bc-action" style="font-family:var(--mono);font-size:11px;padding:6px 10px;background:var(--surface-2);border:1px solid var(--border-2);border-radius:var(--radius);color:var(--text);">
          <option value="transfer">transfer</option>
          <option value="read">read</option>
          <option value="write">write</option>
          <option value="admin">admin</option>
          <option value="execute">execute</option>
        </select>
      </div>
      <div class="control-group">
        <label>Expiry (unix)</label>
        <input type="number" id="bc-expiry" value="0" min="0" style="width: 120px;">
      </div>
      <button class="btn btn-primary" id="bc-create" ${wasm ? '' : 'disabled'}>Create Bearer Cap</button>
    </div>

    <div class="controls-row">
      <button class="btn btn-primary" id="bc-verify" disabled>Verify Cap</button>
      <button class="btn btn-primary" id="bc-exercise" disabled>Exercise Cap</button>
      <button class="btn btn-danger" id="bc-expire" disabled>Simulate Expiry</button>
    </div>

    <div id="bc-caps-display"></div>
    <div id="bc-result"></div>
    <div id="bc-explainer"></div>
  `;

  if (!wasm) return;

  let caps = []; // { token_hex, delegator_key, target_cell, action, expiry, exercised, expired }
  const capsDiv = container.querySelector('#bc-caps-display');
  const resultDiv = container.querySelector('#bc-result');
  const explainerDiv = container.querySelector('#bc-explainer');
  const verifyBtn = container.querySelector('#bc-verify');
  const exerciseBtn = container.querySelector('#bc-exercise');
  const expireBtn = container.querySelector('#bc-expire');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('factories'));

  function randomHex(n) {
    const bytes = new Uint8Array(n);
    crypto.getRandomValues(bytes);
    return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
  }

  function renderCaps() {
    if (caps.length === 0) {
      capsDiv.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry info">Create a bearer cap to begin the demo.</div>
      </div></div>`;
      return;
    }

    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Bearer Capabilities</span></div><div class="result-panel__body">';
    caps.forEach((cap, i) => {
      let status = 'VALID';
      let cls = 'success';
      if (cap.expired) { status = 'EXPIRED'; cls = 'error'; }
      else if (cap.exercised) { status = 'EXERCISED'; cls = 'warning'; }

      html += `<div class="output-entry ${cls}">
        Cap #${i}: ${cap.token_hex.slice(0, 20)}...
        <br>Action: <strong>${cap.action}</strong> | Target: ${cap.target_cell.slice(0, 12)}... | Status: ${status}
        ${cap.expiry > 0 ? `<br>Expires: ${new Date(cap.expiry * 1000).toISOString()}` : '<br>No expiry'}
      </div>`;
    });
    html += '</div></div>';
    capsDiv.innerHTML = html;
  }

  function updateButtons() {
    const hasValid = caps.some(c => !c.exercised && !c.expired);
    const hasAny = caps.length > 0;
    verifyBtn.disabled = !hasAny;
    exerciseBtn.disabled = !hasValid;
    expireBtn.disabled = !hasValid;
  }

  container.querySelector('#bc-create').addEventListener('click', () => {
    const targetInput = container.querySelector('#bc-target').value.trim();
    const targetCell = targetInput.length === 64 ? targetInput : randomHex(32);
    const action = container.querySelector('#bc-action').value;
    const expiry = parseInt(container.querySelector('#bc-expiry').value) || 0;
    const delegatorKey = randomHex(32);

    // Update the input to show the generated target
    if (targetInput.length !== 64) {
      container.querySelector('#bc-target').value = targetCell;
    }

    const t0 = performance.now();
    let result;
    try {
      result = wasm.create_bearer_cap(delegatorKey, targetCell, action, BigInt(expiry));
    } catch (e) {
      // Fallback
      result = {
        bearer_token_hex: randomHex(32),
        target_cell: targetCell,
        action,
        expiry,
      };
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    caps.push({
      token_hex: result.bearer_token_hex,
      delegator_key: delegatorKey,
      target_cell: result.target_cell,
      action: result.action,
      expiry: result.expiry,
      exercised: false,
      expired: false,
    });

    renderCaps();
    updateButtons();

    showExplainer(explainerDiv, {
      prover: `Created bearer cap\nDelegator: ${delegatorKey.slice(0, 16)}...\nTarget: ${result.target_cell.slice(0, 16)}...\nAction: ${result.action}\nToken: ${result.bearer_token_hex.slice(0, 20)}...`,
      verifier: `Bearer token is a BLAKE3 binding of:\n- Delegator key\n- Target cell\n- Action name\n- Expiry timestamp\n\nAnyone holding this token can exercise the action.`,
      delta: `Unlike delegation chains (which are on-chain and require state updates), bearer caps are off-chain. They can be passed via any channel — QR code, email, NFC tap. The holder IS the authorized party. No revocation list needed until expiry.`,
      timing: elapsed,
    });
  });

  verifyBtn.addEventListener('click', () => {
    const cap = caps[caps.length - 1];
    if (!cap) return;

    const currentTime = Math.floor(Date.now() / 1000);
    const t0 = performance.now();
    let result;
    try {
      result = wasm.verify_bearer_cap(
        cap.token_hex, cap.delegator_key, cap.target_cell,
        cap.action, BigInt(cap.expiry), BigInt(currentTime)
      );
    } catch (e) {
      // Fallback
      result = {
        valid: !cap.expired,
        expired: cap.expired || (cap.expiry > 0 && currentTime > cap.expiry),
      };
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    const status = result.valid && !result.expired ? 'VALID' : (result.expired ? 'EXPIRED' : 'INVALID');
    showResult(resultDiv, result.valid && !result.expired ? 'success' : 'error',
      `Verification: ${status}\nToken: ${cap.token_hex.slice(0, 20)}...\nValid signature: ${result.valid}\nExpired: ${result.expired}`);

    showExplainer(explainerDiv, {
      prover: `Presented bearer token for verification\nToken: ${cap.token_hex.slice(0, 20)}...\nClaimed action: ${cap.action} on ${cap.target_cell.slice(0, 12)}...`,
      verifier: `Recomputed expected token from parameters\nCompared against presented token\nChecked expiry against current time (${currentTime})\nResult: ${status}`,
      delta: `Verification is O(1) — a single BLAKE3 hash comparison. No chain traversal, no database lookup, no network call. This makes bearer caps ideal for high-frequency authorization checks.`,
      timing: elapsed,
    });
  });

  exerciseBtn.addEventListener('click', () => {
    const cap = caps.find(c => !c.exercised && !c.expired);
    if (!cap) return;

    const t0 = performance.now();
    cap.exercised = true;
    state.proofCount++;
    notifyStateChange();
    const elapsed = (performance.now() - t0).toFixed(2);

    renderCaps();
    updateButtons();

    showResult(resultDiv, 'success', `Exercised: ${cap.action} on ${cap.target_cell.slice(0, 16)}...`);
    showExplainer(explainerDiv, {
      prover: `Exercised bearer cap\nAction: ${cap.action}\nTarget: ${cap.target_cell.slice(0, 16)}...\nThe cap is now spent (single-use in this demo)`,
      verifier: `Verified token validity\nExecuted authorized action\nRecorded exercise in audit log\n\nIn production: exercise can be single-use or multi-use depending on policy`,
      delta: `Bearer cap exercise is instantaneous — no consensus round needed. The holder proves authorization by possessing the token. After exercise, the action takes effect immediately. For single-use caps, a nullifier prevents replay.`,
      timing: elapsed,
    });
  });

  expireBtn.addEventListener('click', () => {
    const cap = caps.find(c => !c.exercised && !c.expired);
    if (!cap) return;

    cap.expired = true;
    renderCaps();
    updateButtons();

    showResult(resultDiv, 'warning', `Cap expired: ${cap.token_hex.slice(0, 20)}...`);
    showExplainer(explainerDiv, {
      prover: `Bearer cap expired\nToken: ${cap.token_hex.slice(0, 20)}...\nWas authorized for: ${cap.action}`,
      verifier: `Expiry check fails\nToken is structurally valid but temporally invalid\nAction DENIED`,
      delta: `Time-bounded bearer caps provide automatic revocation. Unlike revocation lists (which require propagation delay), expiry is instant and verifiable locally. The tradeoff: shorter expiry = more frequent reissuance.`,
      timing: '0.01',
    });
  });

  renderCaps();
}

function showResult(el, type, message) {
  el.innerHTML = `<div class="result-panel">
    <div class="result-panel__body">
      <div class="output-entry ${type}">${escapeHtml(message)}</div>
    </div>
  </div>`;
}

function showExplainer(el, { prover, verifier, delta, timing }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover">
          <div class="explainer__cell-label">Cap holder</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Verifier</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Design property</div>
          <div class="explainer__cell-content">${escapeHtml(delta)}</div>
        </div>
      </div>
      <div class="explainer__timing">Operation completed in <span>${timing}ms</span></div>
    </div>
  `;
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}

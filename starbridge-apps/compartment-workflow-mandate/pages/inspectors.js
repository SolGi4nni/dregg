// starbridge-apps/compartment-workflow-mandate/pages/inspectors.js
//
//   <dregg-cwm-mandate uri="dregg://cell/..."/>
//   <dregg-cwm-advance-form mandate-uri="dregg://cell/..."/>

const STEP_CURSOR_SLOT = 0;
const COMMITMENT_ANCHOR_SLOT = 1;
const CHARTER_TERMINAL_SLOT = 2;
const CLEARANCE_GRAPH_ROOT_SLOT = 3;
const SPEND_POLICY_SLOT = 4;

const PHASES = ['review', 'redact', 'sign'];
const POLL_MS = 5000;

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

function fieldToU64(bytes) {
  let v = 0n;
  for (let i = 24; i < 32; i += 1) {
    v = (v << 8n) | BigInt(bytes?.[i] ?? 0);
  }
  return Number(v);
}

class CwmMandateInspector extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._poll = null;
    this._state = null;
    this._error = null;
  }

  connectedCallback() {
    this.refresh();
    this._poll = setInterval(() => this.refresh(), POLL_MS);
  }

  disconnectedCallback() {
    if (this._poll) clearInterval(this._poll);
  }

  attributeChangedCallback() { this.refresh(); }

  async refresh() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.dregg?.readCell) return;
    try {
      const cell = await window.dregg.readCell(uri);
      this._state = cell?.state ?? null;
      this._error = null;
    } catch (e) {
      this._error = String(e);
    }
    this.render();
  }

  render() {
    const f = this._state?.fields;
    const cursor = f ? fieldToU64(f[STEP_CURSOR_SLOT]) : null;
    const anchor = f ? fieldToU64(f[COMMITMENT_ANCHOR_SLOT]) : null;
    const terminal = f ? fieldToU64(f[CHARTER_TERMINAL_SLOT]) : null;
    const spend = f ? fieldToU64(f[SPEND_POLICY_SLOT]) : null;
    const phase = cursor != null ? (PHASES[cursor] ?? 'complete') : '—';
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font: 14px/1.4 system-ui, sans-serif; }
        .card { border: 1px solid #ddd; border-radius: 8px; padding: 1rem; }
        dl { display: grid; grid-template-columns: 10rem 1fr; gap: 0.25rem 1rem; margin: 0; }
        dt { color: #666; }
        .err { color: #b00020; }
      </style>
      <div class="card">
        <h3>Workflow Mandate</h3>
        ${this._error ? `<p class="err">${escapeHtml(this._error)}</p>` : ''}
        <dl>
          <dt>Step cursor</dt><dd>${cursor ?? '—'} / ${terminal ?? '—'}</dd>
          <dt>Current phase</dt><dd><code>${escapeHtml(phase)}</code></dd>
          <dt>Commitment anchor</dt><dd>${anchor ?? '—'}</dd>
          <dt>Spend policy</dt><dd>${spend ?? '—'}</dd>
          <dt>Clearance root</dt><dd>slot ${CLEARANCE_GRAPH_ROOT_SLOT}</dd>
        </dl>
      </div>`;
  }
}

class CwmAdvanceForm extends HTMLElement {
  static get observedAttributes() { return ['mandate-uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._busy = false;
    this._msg = '';
  }

  connectedCallback() { this.render(); }

  async #cursor() {
    const uri = this.getAttribute('mandate-uri');
    if (!uri || !window.dregg?.readCell) return 0;
    const cell = await window.dregg.readCell(uri);
    return fieldToU64(cell?.state?.fields?.[STEP_CURSOR_SLOT]);
  }

  async advance() {
    const uri = this.getAttribute('mandate-uri');
    const b = window.dregg?.builders?.compartmentWorkflowMandate;
    if (!uri || !b?.advance_step) {
      this._msg = 'builders.compartmentWorkflowMandate.advance_step unavailable';
      this.render();
      return;
    }
    this._busy = true;
    this.render();
    try {
      const cur = await this.#cursor();
      await b.advance_step(uri, cur);
      this._msg = `Advanced ${cur} → ${cur + 1}`;
      this.closest('dregg-app')?.querySelector('dregg-cwm-mandate')?.refresh?.();
    } catch (e) {
      this._msg = String(e?.message || e);
    }
    this._busy = false;
    this.render();
  }

  render() {
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font: 14px/1.4 system-ui, sans-serif; }
        .card { border: 1px solid #ddd; border-radius: 8px; padding: 1rem; }
        button { padding: 0.5rem 1rem; cursor: pointer; }
        button:disabled { opacity: 0.5; }
        .msg { margin-top: 0.75rem; color: #444; font-size: 0.9rem; }
      </style>
      <div class="card">
        <h3>Advance Step</h3>
        <p>Commits <code>advance_step</code> — MonotonicSequence +1 with phase event.</p>
        <button id="go" ?disabled="${this._busy}">${this._busy ? 'Submitting…' : 'Advance workflow step'}</button>
        ${this._msg ? `<p class="msg">${escapeHtml(this._msg)}</p>` : ''}
      </div>`;
    this.shadowRoot.getElementById('go')?.addEventListener('click', () => this.advance());
  }
}

if (!customElements.get('dregg-cwm-mandate')) {
  customElements.define('dregg-cwm-mandate', CwmMandateInspector);
}
if (!customElements.get('dregg-cwm-advance-form')) {
  customElements.define('dregg-cwm-advance-form', CwmAdvanceForm);
}
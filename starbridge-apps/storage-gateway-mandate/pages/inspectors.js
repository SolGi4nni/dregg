// starbridge-apps/storage-gateway-mandate/pages/inspectors.js
//
//   <dregg-sgm-gateway uri="dregg://cell/..."/>
//   <dregg-sgm-storage-form mandate-uri="dregg://cell/..."/>

const OBJECT_KEY_SLOT = 0;
const LAST_OP_SLOT = 1;
const VOLUME_SPENT_SLOT = 2;
const COMMITMENT_ANCHOR_SLOT = 3;
const VOLUME_CEILING_SLOT = 4;

const OP_NAMES = ['GET', 'PUT', 'LIST'];
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

class SgmGatewayInspector extends HTMLElement {
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
    const spent = f ? fieldToU64(f[VOLUME_SPENT_SLOT]) : null;
    const ceiling = f ? fieldToU64(f[VOLUME_CEILING_SLOT]) : null;
    const lastOp = f ? fieldToU64(f[LAST_OP_SLOT]) : null;
    const anchor = f ? fieldToU64(f[COMMITMENT_ANCHOR_SLOT]) : null;
    const opName = lastOp != null ? (OP_NAMES[lastOp] ?? String(lastOp)) : '—';
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font: 14px/1.4 system-ui, sans-serif; }
        .card { border: 1px solid #ddd; border-radius: 8px; padding: 1rem; }
        dl { display: grid; grid-template-columns: 10rem 1fr; gap: 0.25rem 1rem; margin: 0; }
        dt { color: #666; }
        .bar { height: 8px; background: #eee; border-radius: 4px; overflow: hidden; margin-top: 0.25rem; }
        .fill { height: 100%; background: #3b82f6; }
        .err { color: #b00020; }
      </style>
      <div class="card">
        <h3>Storage Gateway</h3>
        ${this._error ? `<p class="err">${escapeHtml(this._error)}</p>` : ''}
        <dl>
          <dt>Volume spent</dt>
          <dd>${spent ?? '—'} / ${ceiling ?? '—'}
            ${spent != null && ceiling != null && ceiling > 0 ? `
              <div class="bar"><div class="fill" style="width:${Math.min(100, Math.round((spent / ceiling) * 100))}%"></div></div>` : ''}
          </dd>
          <dt>Last op</dt><dd><code>${escapeHtml(opName)}</code></dd>
          <dt>Commitment anchor</dt><dd>${anchor ?? '—'}</dd>
          <dt>Object key slot</dt><dd>${OBJECT_KEY_SLOT}</dd>
        </dl>
      </div>`;
  }
}

class SgmStorageForm extends HTMLElement {
  static get observedAttributes() { return ['mandate-uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._busy = false;
    this._msg = '';
  }

  connectedCallback() { this.render(); }

  async submit(op) {
    const uri = this.getAttribute('mandate-uri');
    const b = window.dregg?.builders?.storageGatewayMandate;
    const key = this.shadowRoot.getElementById('key')?.value || 'uploads/doc.txt';
    if (!uri || !b) {
      this._msg = 'builders.storageGatewayMandate unavailable';
      this.render();
      return;
    }
    this._busy = true;
    this.render();
    try {
      if (op === 'GET') await b.storage_get(uri, key);
      else if (op === 'PUT') await b.storage_put(uri, key, 3735928559);
      else await b.storage_list(uri, key);
      this._msg = `${op} committed for ${key}`;
      this.closest('dregg-app')?.querySelector('dregg-sgm-gateway')?.refresh?.();
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
        label { display: block; margin-bottom: 0.5rem; }
        input { width: 100%; padding: 0.4rem; box-sizing: border-box; }
        .ops { display: flex; gap: 0.5rem; margin-top: 0.75rem; flex-wrap: wrap; }
        button { padding: 0.5rem 1rem; cursor: pointer; }
        button:disabled { opacity: 0.5; }
        .msg { margin-top: 0.75rem; color: #444; font-size: 0.9rem; }
      </style>
      <div class="card">
        <h3>Storage Op</h3>
        <label>Object key / prefix
          <input id="key" type="text" value="uploads/doc.txt" />
        </label>
        <div class="ops">
          <button data-op="GET" ?disabled="${this._busy}">GET</button>
          <button data-op="PUT" ?disabled="${this._busy}">PUT</button>
          <button data-op="LIST" ?disabled="${this._busy}">LIST</button>
        </div>
        ${this._msg ? `<p class="msg">${escapeHtml(this._msg)}</p>` : ''}
      </div>`;
    for (const btn of this.shadowRoot.querySelectorAll('button[data-op]')) {
      btn.addEventListener('click', () => this.submit(btn.dataset.op));
    }
  }
}

if (!customElements.get('dregg-sgm-gateway')) {
  customElements.define('dregg-sgm-gateway', SgmGatewayInspector);
}
if (!customElements.get('dregg-sgm-storage-form')) {
  customElements.define('dregg-sgm-storage-form', SgmStorageForm);
}
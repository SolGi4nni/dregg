/**
 * Storage Gateway Mandate inspectors (Studio).
 *
 *   <dregg-sgm-gateway uri="dregg://cell/<id>"/>
 *   <dregg-sgm-storage-form mandate-uri="dregg://cell/<id>"/>
 *
 * Slot layout mirrors starbridge-apps/storage-gateway-mandate/src/lib.rs.
 */

import { parseRef } from '../uri.js';
import {
  InspectorBase,
  dreggCodeLink,
  emptyState,
  fieldU64,
  renderParseError,
  shortHex,
} from './_base.js';

const OBJECT_KEY_SLOT = 0;
const LAST_OP_SLOT = 1;
const VOLUME_SPENT_SLOT = 2;
const COMMITMENT_ANCHOR_SLOT = 3;
const VOLUME_CEILING_SLOT = 4;

const OP_NAMES = ['GET', 'PUT', 'LIST'];

function opName(code) {
  if (code == null) return '—';
  return OP_NAMES[code] ?? String(code);
}

function receiptHash(receipt) {
  return receipt?.id || receipt?.turnId || receipt?.turn_hash || receipt?.hash_hex || null;
}

function volumePct(spent, ceiling) {
  if (spent == null || ceiling == null || ceiling <= 0) return 0;
  return Math.min(100, Math.round((spent / ceiling) * 100));
}

// --- <dregg-sgm-gateway> ----------------------------------------------------

class DreggSgmGateway extends InspectorBase {
  constructor() {
    super();
    this._eventUnsub = null;
  }

  disconnectedCallback() {
    this._eventUnsub?.();
    this._eventUnsub = null;
    super.disconnectedCallback();
  }

  _bindEvents(parsed) {
    this._eventUnsub?.();
    const sub = this._runtime?.subscribeEvents;
    const uri = parsed ? `dregg://cell/${parsed.id}` : null;
    if (!uri || !sub) return;
    this._eventUnsub = sub(uri, 'storage-op-committed', () => this._render());
  }

  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'cell')) return;

    this._bindEvents(parsed);

    const cellSignal = this._runtime.getCell(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const cell = cellSignal.value;
      if (!cell) {
        return emptyState(html, 'Storage gateway unavailable', 'No runtime cell matches this gateway URI.');
      }

      const fields = cell.fields || [];
      const spent = fieldU64(fields, VOLUME_SPENT_SLOT);
      const ceiling = fieldU64(fields, VOLUME_CEILING_SLOT);
      const lastOp = fieldU64(fields, LAST_OP_SLOT);
      const anchor = fieldU64(fields, COMMITMENT_ANCHOR_SLOT);
      const keySlot = fields[OBJECT_KEY_SLOT];
      const id = cell.cell_id || parsed.id;
      const pct = volumePct(spent, ceiling);

      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            sgm ${spent ?? '—'}/${ceiling ?? '—'} · ${opName(lastOp)}
          </span>`;
      }

      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-storage-pattern sgm">
          <header class="dregg-storage-pattern__head">
            <div>
              <div class="dregg-storage-pattern__title">
                <span class="dregg-inspector__kind">storage-gateway</span>
                ${dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id)}
              </div>
              <div class="dregg-storage-pattern__subtitle">
                VFS gateway mandate with GET/PUT/LIST ops and Stingray volume budget.
              </div>
            </div>
            <div class="dregg-storage-pattern__badges">
              <span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">${opName(lastOp)}</span>
              <span class="dregg-storage-pattern__badge">${pct}% volume</span>
            </div>
          </header>

          <div class="dregg-storage-pattern__summary">
            <div><span>volume spent</span><strong>${spent ?? '—'} / ${ceiling ?? '—'}</strong></div>
            <div><span>last op</span><strong><code>${opName(lastOp)}</code></strong></div>
            <div><span>commitment anchor</span><strong>${anchor ?? '—'}</strong></div>
            <div><span>object key slot</span><strong>${OBJECT_KEY_SLOT}</strong></div>
          </div>

          ${spent != null && ceiling != null && ceiling > 0 ? html`
            <div class="dregg-inspector__panel">
              <span class="dregg-inspector__meta">volume budget</span>
              <span class="dregg-inspector__progress" style="display:block;margin-top:6px;width:100%;max-width:240px;">
                <span class="dregg-inspector__progress-fill" style=${`width:${pct}%`}></span>
              </span>
            </div>` : null}

          <dl class="dregg-inspector__kv">
            <dt>volume_spent</dt><dd>${spent ?? '—'}</dd>
            <dt>volume_ceiling</dt><dd>${ceiling ?? '—'}</dd>
            <dt>last_op</dt><dd><code>${opName(lastOp)}</code></dd>
            <dt>commitment_anchor</dt><dd>${anchor ?? '—'}</dd>
            <dt>object_key</dt><dd><code>${keySlot ? shortHex(String(keySlot), 18) : '—'}</code></dd>
          </dl>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-sgm-gateway')) {
  customElements.define('dregg-sgm-gateway', DreggSgmGateway);
}

// --- <dregg-sgm-storage-form> -----------------------------------------------

class DreggSgmStorageForm extends InspectorBase {
  static get observedAttributes() { return ['mandate-uri', 'mode']; }

  constructor() {
    super();
    this._busy = false;
    this._msg = '';
    this._receipt = null;
    this._key = 'uploads/doc.txt';
    this._eventUnsub = null;
  }

  disconnectedCallback() {
    this._eventUnsub?.();
    this._eventUnsub = null;
    super.disconnectedCallback();
  }

  attributeChangedCallback() {
    if (this._api) this._render();
  }

  _bindEvents(uri) {
    this._eventUnsub?.();
    const sub = this._runtime?.subscribeEvents || (typeof window !== 'undefined' ? window.dregg?.subscribeEvents : null);
    if (!uri || !sub) return;
    this._eventUnsub = sub(uri, 'storage-op-committed', () => this._render());
  }

  async _submit(uri, op) {
    const b = window.dregg?.builders?.storageGatewayMandate;
    if (!uri || !b) {
      this._msg = 'builders.storageGatewayMandate unavailable';
      this._render();
      return;
    }
    this._busy = true;
    this._msg = '';
    this._receipt = null;
    this._render();
    try {
      const key = this._key || 'uploads/doc.txt';
      let receipt;
      if (op === 'GET') receipt = await b.storage_get(uri, key);
      else if (op === 'PUT') receipt = await b.storage_put(uri, key, 0xdeadbeef);
      else receipt = await b.storage_list(uri, key);
      this._receipt = receipt;
      this._msg = `${op} committed for ${key}`;
      this.dispatchEvent(new CustomEvent('sgm-storage-op', {
        bubbles: true,
        detail: { uri, op, key, receipt },
      }));
    } catch (e) {
      this._msg = String(e?.message || e);
    }
    this._busy = false;
    this._render();
  }

  async _init(uri) {
    const b = window.dregg?.builders?.storageGatewayMandate;
    if (!uri || !b?.init_gateway) {
      this._msg = 'builders.storageGatewayMandate.init_gateway unavailable';
      this._render();
      return;
    }
    this._busy = true;
    this._msg = '';
    this._receipt = null;
    this._render();
    try {
      const receipt = await b.init_gateway(uri);
      this._receipt = receipt;
      this._msg = 'Gateway initialized';
      this.dispatchEvent(new CustomEvent('sgm-gateway-initialized', {
        bubbles: true,
        detail: { uri, receipt },
      }));
    } catch (e) {
      this._msg = String(e?.message || e);
    }
    this._busy = false;
    this._render();
  }

  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('mandate-uri');

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'cell')) return;

    this._bindEvents(refAttr);

    const cellSignal = parsed && this._runtime?.getCell
      ? this._runtime.getCell(parsed.id)
      : null;
    const root = document.createElement('div');
    this.appendChild(root);

    const self = this;
    const Component = () => {
      const cell = cellSignal ? cellSignal.value : null;
      const spent = fieldU64(cell?.fields, VOLUME_SPENT_SLOT);
      const ceiling = fieldU64(cell?.fields, VOLUME_CEILING_SLOT);
      const hash = receiptHash(self._receipt);
      const noticeClass = self._receipt
        ? 'dregg-inspector__notice dregg-inspector__notice--ok'
        : (self._msg && !self._busy ? 'dregg-inspector__notice dregg-inspector__notice--warn' : 'dregg-inspector__notice');

      return html`
        <div class="dregg-inspector dregg-inspector--panel sgm-storage">
          <header>
            <span class="dregg-inspector__kind">storage op</span>
            ${parsed ? dreggCodeLink(html, refAttr, shortHex(parsed.id, 14), refAttr) : null}
          </header>
          <p class="dregg-inspector__note">
            GET/PUT/LIST via <code>builders.storageGatewayMandate</code> with
            <code>storage-op-committed</code> events.
          </p>
          <div class="dregg-inspector__summary">
            <div><span>volume</span><strong>${spent ?? '—'} / ${ceiling ?? '—'}</strong></div>
            <div><span>status</span><strong>${self._busy ? 'submitting…' : (hash ? 'committed' : 'idle')}</strong></div>
          </div>
          <label class="dregg-inspector__meta" style="display:block;margin-top:8px;">
            Object key / prefix
            <input class="dregg-inspector__input" type="text" style="display:block;width:100%;margin-top:4px;"
              value=${self._key}
              onInput=${(e) => { self._key = e.target.value; }}
              disabled=${self._busy} />
          </label>
          <div class="dregg-inspector__controls">
            <button class="dregg-inspector__button" type="button" disabled=${self._busy}
              onClick=${() => self._init(refAttr)}>Initialize gateway</button>
            <button class="dregg-inspector__button" type="button" disabled=${self._busy}
              onClick=${() => self._submit(refAttr, 'GET')}>GET</button>
            <button class="dregg-inspector__button" type="button" disabled=${self._busy}
              onClick=${() => self._submit(refAttr, 'PUT')}>PUT</button>
            <button class="dregg-inspector__button" type="button" disabled=${self._busy}
              onClick=${() => self._submit(refAttr, 'LIST')}>LIST</button>
          </div>
          ${self._msg ? html`<div class=${noticeClass}>${self._msg}</div>` : null}
          ${hash ? html`
            <div class="dregg-inspector__controls">
              <span class="dregg-inspector__meta">receipt</span>
              ${dreggCodeLink(html, `dregg://receipt/${hash}`, shortHex(hash, 18), hash)}
            </div>` : null}
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-sgm-storage-form')) {
  customElements.define('dregg-sgm-storage-form', DreggSgmStorageForm);
}
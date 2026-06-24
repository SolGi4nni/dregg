/**
 * Compartment Workflow Mandate inspectors (Studio).
 *
 *   <dregg-cwm-mandate uri="dregg://cell/<id>"/>
 *   <dregg-cwm-advance-form mandate-uri="dregg://cell/<id>"/>
 *
 * Slot layout mirrors starbridge-apps/compartment-workflow-mandate/src/lib.rs.
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

const STEP_CURSOR_SLOT = 0;
const COMMITMENT_ANCHOR_SLOT = 1;
const CHARTER_TERMINAL_SLOT = 2;
const CLEARANCE_GRAPH_ROOT_SLOT = 3;
const SPEND_POLICY_SLOT = 4;

const PHASES = ['review', 'redact', 'sign'];

function phaseForCursor(cursor) {
  if (cursor == null) return '—';
  if (cursor >= PHASES.length) return 'complete';
  return PHASES[cursor] ?? String(cursor);
}

function receiptHash(receipt) {
  return receipt?.id || receipt?.turnId || receipt?.turn_hash || receipt?.hash_hex || null;
}

// --- <dregg-cwm-mandate> ----------------------------------------------------

class DreggCwmMandate extends InspectorBase {
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
    this._eventUnsub = sub(uri, 'workflow-step-advanced', () => this._render());
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
        return emptyState(html, 'Workflow mandate unavailable', 'No runtime cell matches this mandate URI.');
      }

      const fields = cell.fields || [];
      const cursor = fieldU64(fields, STEP_CURSOR_SLOT);
      const anchor = fieldU64(fields, COMMITMENT_ANCHOR_SLOT);
      const terminal = fieldU64(fields, CHARTER_TERMINAL_SLOT);
      const spend = fieldU64(fields, SPEND_POLICY_SLOT);
      const clearance = fields[CLEARANCE_GRAPH_ROOT_SLOT];
      const phase = phaseForCursor(cursor);
      const id = cell.cell_id || parsed.id;

      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            cwm step ${cursor ?? '—'}/${terminal ?? '—'} · ${phase}
          </span>`;
      }

      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-storage-pattern cwm">
          <header class="dregg-storage-pattern__head">
            <div>
              <div class="dregg-storage-pattern__title">
                <span class="dregg-inspector__kind">workflow-mandate</span>
                ${dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id)}
              </div>
              <div class="dregg-storage-pattern__subtitle">
                DAG charter mandate with MonotonicSequence step cursor and clearance admission.
              </div>
            </div>
            <div class="dregg-storage-pattern__badges">
              <span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">${phase}</span>
              <span class="dregg-storage-pattern__badge">slot ${CLEARANCE_GRAPH_ROOT_SLOT} clearance</span>
            </div>
          </header>

          <div class="dregg-storage-pattern__summary">
            <div><span>step cursor</span><strong>${cursor ?? '—'} / ${terminal ?? '—'}</strong></div>
            <div><span>phase</span><strong><code>${phase}</code></strong></div>
            <div><span>commitment anchor</span><strong>${anchor ?? '—'}</strong></div>
            <div><span>spend policy</span><strong>${spend ?? '—'}</strong></div>
          </div>

          <dl class="dregg-inspector__kv">
            <dt>step_cursor</dt><dd>${cursor ?? '—'}</dd>
            <dt>charter_terminal</dt><dd>${terminal ?? '—'}</dd>
            <dt>commitment_anchor</dt><dd>${anchor ?? '—'}</dd>
            <dt>spend_policy</dt><dd>${spend ?? '—'}</dd>
            <dt>clearance_graph_root</dt><dd><code>${clearance ? shortHex(String(clearance), 18) : '—'}</code></dd>
          </dl>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-cwm-mandate')) {
  customElements.define('dregg-cwm-mandate', DreggCwmMandate);
}

// --- <dregg-cwm-advance-form> -----------------------------------------------

class DreggCwmAdvanceForm extends InspectorBase {
  static get observedAttributes() { return ['mandate-uri', 'mode']; }

  constructor() {
    super();
    this._busy = false;
    this._msg = '';
    this._receipt = null;
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
    this._eventUnsub = sub(uri, 'workflow-step-advanced', () => this._render());
  }

  async _cursor(uri, parsed) {
    if (parsed && this._runtime?.getCell) {
      const cell = this._runtime.getCell(parsed.id).value;
      return fieldU64(cell?.fields, STEP_CURSOR_SLOT) ?? 0;
    }
    if (window.dregg?.readCell) {
      const cell = await window.dregg.readCell(uri);
      const fields = cell?.state?.fields || cell?.fields || [];
      return fieldU64(fields, STEP_CURSOR_SLOT) ?? 0;
    }
    return 0;
  }

  async _advance(uri) {
    const b = window.dregg?.builders?.compartmentWorkflowMandate;
    if (!uri || !b?.advance_step) {
      this._msg = 'builders.compartmentWorkflowMandate.advance_step unavailable';
      this._render();
      return;
    }
    this._busy = true;
    this._msg = '';
    this._receipt = null;
    this._render();
    try {
      let parsed = null;
      try { parsed = parseRef(uri); } catch {}
      const cur = await this._cursor(uri, parsed);
      const receipt = await b.advance_step(uri, cur);
      this._receipt = receipt;
      this._msg = `Advanced ${cur} → ${cur + 1}`;
      this.dispatchEvent(new CustomEvent('cwm-step-advanced', {
        bubbles: true,
        detail: { uri, from: cur, to: cur + 1, receipt },
      }));
    } catch (e) {
      this._msg = String(e?.message || e);
    }
    this._busy = false;
    this._render();
  }

  async _init(uri) {
    const b = window.dregg?.builders?.compartmentWorkflowMandate;
    if (!uri || !b?.init_mandate) {
      this._msg = 'builders.compartmentWorkflowMandate.init_mandate unavailable';
      this._render();
      return;
    }
    this._busy = true;
    this._msg = '';
    this._receipt = null;
    this._render();
    try {
      const receipt = await b.init_mandate(uri);
      this._receipt = receipt;
      this._msg = 'Mandate initialized';
      this.dispatchEvent(new CustomEvent('cwm-mandate-initialized', {
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
      const cursor = fieldU64(cell?.fields, STEP_CURSOR_SLOT);
      const terminal = fieldU64(cell?.fields, CHARTER_TERMINAL_SLOT);
      const hash = receiptHash(self._receipt);
      const noticeClass = self._receipt
        ? 'dregg-inspector__notice dregg-inspector__notice--ok'
        : (self._msg && !self._busy ? 'dregg-inspector__notice dregg-inspector__notice--warn' : 'dregg-inspector__notice');

      return html`
        <div class="dregg-inspector dregg-inspector--panel cwm-advance">
          <header>
            <span class="dregg-inspector__kind">advance step</span>
            ${parsed ? dreggCodeLink(html, refAttr, shortHex(parsed.id, 14), refAttr) : null}
          </header>
          <p class="dregg-inspector__note">
            Commits <code>advance_step</code> — MonotonicSequence +1 with
            <code>workflow-step-advanced</code> event.
          </p>
          <div class="dregg-inspector__summary">
            <div><span>cursor</span><strong>${cursor ?? '—'} / ${terminal ?? '—'}</strong></div>
            <div><span>phase</span><strong><code>${phaseForCursor(cursor)}</code></strong></div>
            <div><span>status</span><strong>${self._busy ? 'submitting…' : (hash ? 'committed' : 'idle')}</strong></div>
          </div>
          <div class="dregg-inspector__controls">
            <button class="dregg-inspector__button" type="button" disabled=${self._busy}
              onClick=${() => self._init(refAttr)}>Initialize mandate</button>
            <button class="dregg-inspector__button" type="button" disabled=${self._busy}
              onClick=${() => self._advance(refAttr)}>${self._busy ? 'Submitting…' : 'Advance workflow step'}</button>
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

if (!customElements.get('dregg-cwm-advance-form')) {
  customElements.define('dregg-cwm-advance-form', DreggCwmAdvanceForm);
}
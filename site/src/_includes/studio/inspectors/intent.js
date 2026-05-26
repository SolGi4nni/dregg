/**
 * <dregg-intent uri="dregg://intent/<id_or_index>"> — single intent.
 *
 * The wasm sim does NOT expose a getter to recover an intent's full spec by
 * id or index after creation. As a workaround, the JS runtime keeps a
 * `intentLedger` of every intent created through `runtime.createIntent(...)`
 * including its input spec; this inspector reads that.
 *
 * URI: the id segment may be either the hex intent_id (preferred) or a
 * numeric intent_index.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggIntent extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'intent')) return;

    const sig = this._runtime.getIntent(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const i = sig.value;
      if (!i) return html`<div class="dregg-inspector dregg-inspector--empty">intent not in JS ledger: <code>${shortHex(parsed.id, 16)}</code></div>`;
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code title=${i.intent_id}>${shortHex(i.intent_id)}</code>
            · ${i.kind}
            · ${i.actions.length} action${i.actions.length === 1 ? '' : 's'}
          </span>`;
      }
      const actionsRender = i.actions.length
        ? i.actions.map(a => html`<code>${a.action}@${a.resource}</code> `)
        : html`<span style="opacity:0.6">(none)</span>`;
      const constraintsRender = i.constraints.length
        ? i.constraints.map(c => html`<code>${JSON.stringify(c)}</code> `)
        : html`<span style="opacity:0.6">(none)</span>`;
      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">intent</span>
            <code class="dregg-inspector__id" title=${i.intent_id}>${shortHex(i.intent_id, 24)}</code>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>kind</dt><dd>${i.kind}</dd>
            <dt>intent id</dt><dd><code>${i.intent_id}</code></dd>
            <dt>index</dt><dd>${String(i.intent_index)}</dd>
            <dt>creator agent</dt><dd>#${String(i.agent_index)}</dd>
            <dt>actions</dt><dd>${actionsRender}</dd>
            <dt>constraints</dt><dd>${constraintsRender}</dd>
            <dt>resource pattern</dt><dd>${i.resource_pattern || html`<span style="opacity:0.6">(any)</span>`}</dd>
            <dt>expiry</dt><dd>${i.expiry ? String(i.expiry) : html`<span style="opacity:0.6">(none)</span>`}</dd>
          </dl>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-intent')) customElements.define('dregg-intent', DreggIntent);

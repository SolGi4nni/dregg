/**
 * <dregg-turn uri="dregg://turn/<hex32>"> — single turn.
 *
 * In the sim runtime a "turn" is identified by its turn_hash; its observable
 * state is the matching TurnReceipt (pre/post state, computrons, actions).
 * Backed by the same `get_receipt_chain` lookup as <dregg-receipt>, but
 * presented as a turn (with an embedded receipt for the effects view).
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggTurn extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'turn')) return;

    const sig = this._runtime.getTurn(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const t = sig.value;
      if (!t) return html`<div class="dregg-inspector dregg-inspector--empty">turn not found: <code>${shortHex(parsed.id, 16)}</code></div>`;
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code title=${parsed.id}>${shortHex(parsed.id)}</code>
            · ${String(t.action_count)} effects
          </span>`;
      }
      // Render per-action authorization badges if actions are available.
      const actions = Array.isArray(t.actions) ? t.actions : [];
      const actionList = actions.length
        ? html`
          <dt>actions</dt>
          <dd>
            <ul style="list-style:none;padding:0;margin:0;display:flex;flex-direction:column;gap:4px;">
              ${actions.map((a, i) => {
                const authJson = a.authorization ? JSON.stringify(a.authorization) : null;
                return html`
                  <li style="display:flex;align-items:center;gap:6px;">
                    <span style="color:var(--fg-dim);font-size:0.75rem;min-width:1.4em;">${String(i)}.</span>
                    <code style="font-size:0.78rem;" title=${a.target_cell || ''}>${shortHex(a.target_cell, 10)}</code>
                    <span style="color:var(--fg-dim);font-size:0.78rem;">${shortHex(a.method, 8)}</span>
                    ${authJson
                      ? html`<dregg-authorization data=${authJson} mode="compact"></dregg-authorization>`
                      : null}
                  </li>`;
              })}
            </ul>
          </dd>`
        : html`<dt>actions</dt><dd>${String(t.action_count)}</dd>`;

      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">turn</span>
            <code class="dregg-inspector__id" title=${parsed.id}>${shortHex(parsed.id, 24)}</code>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>turn hash</dt><dd><code>${t.turn_hash}</code></dd>
            <dt>effects</dt><dd>${String(t.action_count)}</dd>
            <dt>computrons</dt><dd>${String(t.computrons_used)}</dd>
            <dt>timestamp</dt><dd>${String(t.timestamp)}</dd>
            <dt>state transition</dt>
            <dd>
              <code title=${t.pre_state_hash}>${shortHex(t.pre_state_hash, 12)}</code>
              → <code title=${t.post_state_hash}>${shortHex(t.post_state_hash, 12)}</code>
            </dd>
            ${actionList}
            <dt>receipt</dt>
            <dd><dregg-receipt uri=${`dregg://receipt/${t.turn_hash}`} mode="compact"></dregg-receipt></dd>
          </dl>
          <details style="margin-top:var(--s3,8px);">
            <summary style="cursor:pointer;color:var(--fg-dim);font-size:0.82rem;user-select:none;">Trace</summary>
            <dregg-turn-debugger uri=${`dregg://turn/${t.turn_hash}`} mode="default"></dregg-turn-debugger>
          </details>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-turn')) customElements.define('dregg-turn', DreggTurn);

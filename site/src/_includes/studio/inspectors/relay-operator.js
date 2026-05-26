/**
 * <dregg-relay-operator uri="dregg://cell/<id>">
 * Uses DFA caveats for dispatch (Phase 5, after DFA lane). Cell program + <dregg-dfa> for routing rules.
 * RateLimitBySum + SenderAuthorized + FieldLte for quota.
 */
import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError } from './_base.js';

class DreggRelayOperator extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    let parsed = null; try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'cell')) return;
    const root = document.createElement('div'); this.appendChild(root);
    const Component = () => {
      const cell = parsed && this._runtime.getCell ? this._runtime.getCell(parsed.id).value : null;
      return html`
        <div class="dregg-inspector dregg-inspector--cell pro">
          <header><span class="dregg-inspector__kind">relay-operator</span> (DFA dispatch)</header>
          ${cell ? html`<dregg-cell uri=${`dregg://cell/${parsed.id}`} mode="compact"></dregg-cell><dregg-dfa mode="compact"></dregg-dfa>` : ''}
          <div style="font-size:0.7rem;">DFA caveat routing + quota cell-program. See STORAGE §3.5 + DFA-RATIONALIZATION.</div>
        </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-relay-operator')) customElements.define('dregg-relay-operator', DreggRelayOperator);

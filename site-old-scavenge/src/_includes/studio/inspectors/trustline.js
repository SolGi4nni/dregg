/**
 * <dregg-trustline uri="dregg://trustline/<cell>">
 *
 * THE ORGAN (docs/ORGANS.md §1): a bilateral line of credit. "Issuer A
 * extends holder B a line of N" is an ATTENUATED CAPABILITY whose exercise
 * debits a SHARED counter — granted ⊆ held made QUANTITATIVE. The enforcement
 * tooth is the executor-installed cell program the node re-evaluates on every
 * touch (`drawn ≤ line`, terms pinned, settlement monotone).
 *
 * This inspector surfaces the LIVE position from the node's operator-local
 * trustline service: `GET /trustline/status/{cell}` (node/src/trustline_service.rs,
 * the same route the @dregg/sdk TrustlineClient drives). It is a read of the
 * running system, so it needs a connected node (the remote runtime's
 * `nodeBase`); on the wasm sandbox runtime it says so plainly rather than
 * fabricate a credit line.
 */
import { parseRef } from '../uri.js';
import {
  InspectorBase,
  dreggCodeLink,
  emptyState,
  renderParseError,
  shortHex,
} from './_base.js';

function bar(html, drawn, line) {
  const pct = line > 0 ? Math.min(100, Math.round((drawn / line) * 100)) : 0;
  const hot = pct >= 90;
  return html`
    <div class="dregg-organ__bar" title=${`${drawn} drawn of ${line} (${pct}%)`}>
      <div class=${`dregg-organ__bar-fill ${hot ? 'dregg-organ__bar-fill--hot' : ''}`}
           style=${`width:${pct}%`}></div>
    </div>`;
}

class DreggTrustline extends InspectorBase {
  _render() {
    const { h, render, html, effect, signal } = this._api;
    const refAttr = this.getAttribute('uri');
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    let parsed = null; try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'trustline')) return;
    const root = document.createElement('div'); this.appendChild(root);

    const state = signal({ phase: 'idle', status: null, error: null });
    const nodeBase = this._runtime?.nodeBase || null;
    const nodeGet = this._runtime?.nodeGet || null;

    const load = async () => {
      if (!parsed) return;
      if (!nodeBase || !nodeGet) { state.value = { phase: 'no-node' }; return; }
      state.value = { phase: 'loading' };
      const status = await nodeGet(`/trustline/status/${parsed.id}`);
      if (!status) { state.value = { phase: 'unreachable' }; return; }
      state.value = { phase: 'ready', status };
    };
    load();

    const Component = () => {
      const s = state.value;
      const id = parsed?.id || '';
      const head = (badges) => html`
        <header class="dregg-organ__head">
          <div>
            <div class="dregg-organ__title">
              <span class="dregg-inspector__kind">trustline</span>
              ${id ? dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id) : null}
            </div>
            <div class="dregg-organ__subtitle">A bilateral line of credit — an attenuated
              capability whose draws debit a shared counter. ORGANS §1.</div>
          </div>
          <div class="dregg-organ__badges">${badges}</div>
        </header>`;

      if (s.phase === 'no-node') {
        return html`<div class="dregg-inspector dregg-organ">
          ${head(html`<span class="dregg-organ__badge dregg-organ__badge--warn">node-only</span>`)}
          ${emptyState(html, 'Connect a node to read the line',
            'Trustlines are a node-side organ (the operator is the issuer). Switch the runtime to a remote node to read this line’s live position.')}
        </div>`;
      }
      if (s.phase === 'loading' || s.phase === 'idle') {
        return html`<div class="dregg-inspector dregg-organ">${head(null)}
          <div class="dregg-organ__loading">reading <code>/trustline/status</code>…</div></div>`;
      }
      if (s.phase === 'unreachable') {
        return html`<div class="dregg-inspector dregg-organ">
          ${head(html`<span class="dregg-organ__badge dregg-organ__badge--warn">unreachable</span>`)}
          ${emptyState(html, 'No live trustline at this id',
            'The node returned nothing for this trustline (it may not be an open line on this operator, or the trustline service is not mounted / CORS-blocked).')}
        </div>`;
      }
      const t = s.status;
      const remaining = t.remaining ?? Math.max(0, (t.line || 0) - (t.drawn || 0));
      return html`<div class="dregg-inspector dregg-organ">
        ${head(html`
          <span class=${`dregg-organ__badge ${t.open ? 'dregg-organ__badge--ok' : 'dregg-organ__badge--warn'}`}>${t.open ? 'open' : 'closed'}</span>
          <span class="dregg-organ__badge">${t.collateral || 'fullReserve'}</span>`)}

        <div class="dregg-organ__credit">
          ${bar(html, t.drawn || 0, t.line || 0)}
          <div class="dregg-organ__credit-readout">
            <span><strong>${remaining}</strong> available</span>
            <span><strong>${t.drawn || 0}</strong> drawn of <strong>${t.line || 0}</strong></span>
          </div>
        </div>

        <div class="dregg-organ__parties">
          <div><span>issuer</span>${t.issuer ? dreggCodeLink(html, `dregg://cell/${t.issuer}`, shortHex(t.issuer, 14), t.issuer) : html`<code>—</code>`}</div>
          <div><span>holder</span>${t.holder ? dreggCodeLink(html, `dregg://cell/${t.holder}`, shortHex(t.holder, 14), t.holder) : html`<code>—</code>`}</div>
        </div>

        <div class="dregg-organ__grid">
          <div><span>escrow backing</span><strong>${t.escrow ?? '—'}</strong></div>
          <div><span>settled to holder</span><strong>${t.settled ?? 0}</strong></div>
          <div><span>coordinator headroom</span><strong>${t.coordinator_remaining == null ? '—' : t.coordinator_remaining}</strong></div>
          <div><span>coordinator version</span><strong>${t.coordinator_version == null ? '—' : t.coordinator_version}</strong></div>
        </div>

        <section class="dregg-organ__section">
          <h4>The enforcement tooth</h4>
          <p class="dregg-organ__note">Every draw is an ordinary turn the executor re-evaluates against
            the installed cell program: <code>drawn ≤ line</code> for life, terms pinned, settlement
            monotone. The Stingray budget coordinator and the cell counter
            <em>provably agree</em>. Inspect the cell program for the caveat shape.</p>
        </section>
      </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-trustline')) customElements.define('dregg-trustline', DreggTrustline);

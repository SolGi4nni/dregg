/**
 * <dregg-court uri="dregg://court/<strand-pubkey>">
 *
 * THE ORGAN (docs/ORGANS.md §3): the equivocation court. A strand author
 * posts a slashable BOND (a real bond cell, escrow == bond at every reachable
 * state) to be admitted. If anyone presents EVIDENCE of equivocation — two
 * conflicting signed blocks at the same sequence — the court slashes the bond
 * from the proof alone. Accountability without a trusted referee: the proof
 * IS the verdict.
 *
 * Surfaces `GET /court/status/{strand}` (node/src/equivocation_court_service.rs):
 * the registered bond, the bound bond cell + its live escrow, and the
 * admission verdict. The court routes live in the node's PROTECTED router
 * (bearer-token gate), so an unauthenticated browser read is refused — this
 * inspector says so plainly rather than fabricate a bond.
 */
import { parseRef } from '../uri.js';
import {
  InspectorBase,
  dreggCodeLink,
  emptyState,
  renderParseError,
  shortHex,
} from './_base.js';

class DreggCourt extends InspectorBase {
  _render() {
    const { h, render, html, effect, signal } = this._api;
    const refAttr = this.getAttribute('uri');
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    let parsed = null; try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'court')) return;
    const root = document.createElement('div'); this.appendChild(root);

    const state = signal({ phase: 'idle' });
    const nodeBase = this._runtime?.nodeBase || null;
    const nodeGet = this._runtime?.nodeGet || null;

    const load = async () => {
      if (!parsed) return;
      if (!nodeBase || !nodeGet) { state.value = { phase: 'no-node' }; return; }
      state.value = { phase: 'loading' };
      const status = await nodeGet(`/court/status/${parsed.id}`);
      if (!status) { state.value = { phase: 'gated' }; return; }
      state.value = { phase: 'ready', status };
    };
    load();

    const Component = () => {
      const s = state.value;
      const strand = parsed?.id || '';
      const head = (badges) => html`
        <header class="dregg-organ__head">
          <div>
            <div class="dregg-organ__title">
              <span class="dregg-inspector__kind">court</span>
              <code title=${strand}>${shortHex(strand, 18)}</code>
            </div>
            <div class="dregg-organ__subtitle">The equivocation court — a slashable bond admits a
              strand; a proof of two conflicting blocks slashes it. ORGANS §3.</div>
          </div>
          <div class="dregg-organ__badges">${badges}</div>
        </header>`;

      if (s.phase === 'no-node') {
        return html`<div class="dregg-inspector dregg-organ">
          ${head(html`<span class="dregg-organ__badge dregg-organ__badge--warn">node-only</span>`)}
          ${emptyState(html, 'Connect a node to read the court',
            'The court is a node-side organ. Switch the runtime to a remote node to read this strand’s bond + admission verdict.')}
        </div>`;
      }
      if (s.phase === 'loading' || s.phase === 'idle') {
        return html`<div class="dregg-inspector dregg-organ">${head(null)}
          <div class="dregg-organ__loading">reading <code>/court/status</code>…</div></div>`;
      }
      if (s.phase === 'gated') {
        return html`<div class="dregg-inspector dregg-organ">
          ${head(html`<span class="dregg-organ__badge dregg-organ__badge--warn">bearer-gated</span>`)}
          ${emptyState(html, 'Court status is operator-gated',
            'The /court/* routes live in the node’s protected router (a bearer-token gate). An unauthenticated browser read is refused. Query it from the operator console / SDK with the devnet key, or via `dregg court status`.')}
        </div>`;
      }
      const c = s.status;
      const slashed = (c.bond ?? 0) === 0;
      return html`<div class="dregg-inspector dregg-organ">
        ${head(html`
          <span class=${`dregg-organ__badge ${c.admitted ? 'dregg-organ__badge--ok' : 'dregg-organ__badge--warn'}`}>${c.admitted ? 'admitted' : 'not admitted'}</span>
          ${slashed ? html`<span class="dregg-organ__badge dregg-organ__badge--warn">no live bond</span>` : html`<span class="dregg-organ__badge dregg-organ__badge--ok">bonded</span>`}`)}

        <div class="dregg-organ__grid">
          <div><span>registered bond</span><strong>${c.bond ?? 0}</strong></div>
          <div><span>live escrow</span><strong>${c.escrow == null ? '—' : c.escrow}</strong></div>
          <div><span>admission verdict</span><strong>${c.admitted ? 'admitted' : 'refused'}</strong></div>
          <div><span>bond cell</span>${c.bond_cell ? dreggCodeLink(html, `dregg://cell/${c.bond_cell}`, shortHex(c.bond_cell, 12), c.bond_cell) : html`<strong>—</strong>`}</div>
        </div>

        <section class="dregg-organ__section">
          <h4>The proof is the verdict</h4>
          <p class="dregg-organ__note">Admission requires <code>escrow == bond</code> at every reachable
            state (the registry entry lands only after the funding turn commits). A presented
            <code>EquivocationProof</code> — two conflicting signed blocks at one sequence — slashes the
            bond from the proof alone, no trusted referee. A registered bond of 0 here means there is no
            live stake (never posted, or already slashed).</p>
        </section>
      </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-court')) customElements.define('dregg-court', DreggCourt);

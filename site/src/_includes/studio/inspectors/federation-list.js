/**
 * <dregg-federation-list> — lists KnownFederations registry + sim-created federations.
 *
 * Per STARBRIDGE-PLAN §4.5 + §5.7: needs list_known_federations wasm binding.
 * Today: falls back to runtime-created federations (via listBlocks / getFederation).
 * Renders each as <dregg-federation> + block-dag affordance.
 *
 * Reuses platform vocab: <dregg-federation>, <dregg-block-dag>.
 *
 * Supports register affordance (placeholder until extension cclerk + binding).
 */

import { InspectorBase, shortHex } from './_base.js';

class DreggFederationList extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      // In real: const list = this._runtime.listKnownFederations().value || [];
      // Today we synthesize from blocks signal if present (coarse).
      let feds = [];
      try {
        const blocksSig = this._runtime.listBlocks ? this._runtime.listBlocks() : null;
        // Heuristic: collect unique fed indices seen in blocks (weak but works for sim)
        const seen = new Set();
        // Fallback: the federation inspector test fixtures create via createFederation.
        // For production, this list will come from wasm.get_known_federations or equivalent.
        if (this._runtime._wasm && typeof this._runtime._wasm.list_federation_blocks === 'function') {
          // best-effort scan 0..4
          for (let i = 0; i < 8; i++) {
            try {
              const bl = this._runtime._wasm.list_federation_blocks(this._runtime._handle, i);
              if (bl && bl.length) seen.add(i);
            } catch {}
          }
        }
        feds = Array.from(seen).map(i => ({ fed_index: i, name: `fed-${i}` }));
      } catch (e) { /* silent */ }

      if (mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">federations: ${feds.length}</span>`;
      }

      return html`
        <div class="dregg-inspector dregg-inspector--cell pfl">
          <header>
            <span class="dregg-inspector__kind">federation-list</span>
            <span class="pfl__count">${feds.length} known</span>
          </header>
          ${feds.length === 0
            ? html`<div class="pfl__empty" style="color:var(--fg-dim);font-size:0.82rem;">no federations in this runtime (create via runtime.createFederation or register_federation binding)</div>`
            : html`<ul class="pfl__list" style="margin:6px 0;padding-left:0;list-style:none;">
                ${feds.map(f => html`
                  <li style="margin:4px 0;padding:4px 8px;border:1px solid var(--line);border-radius:3px;">
                    <dregg-federation uri=${`dregg://federation/${f.fed_index}`} mode="compact"></dregg-federation>
                    <dregg-block-dag uri=${`dregg://federation/${f.fed_index}`} mode="compact" style="margin-left:8px;"></dregg-block-dag>
                    <!-- Cluster B integration (FOLLOWUP-15): real blocklace DAG via block-dag (dregg-blocklace + dregg_federation);
                         educational sim + config (constitution threshold/timeout/routes_commitment DFA) via blocklace-sim;
                         delegation graph, merkle (for receipts/ARs), DFA routing (constitution.routes_commitment), factory descriptors for cell minting in fed. -->
                    <div style="margin-top:4px;font-size:0.65rem;color:var(--fg-dim);">
                      <dregg-delegation-graph mode="compact" style="margin-right:6px;"></dregg-delegation-graph>
                      <dregg-dfa mode="compact" data-dfa=${JSON.stringify({name:'route-sample', states:[{id:0,dead:true},{id:1}], transitions:[{from:0,to:1,byte:47}]})} style="margin-right:6px;"></dregg-dfa>
                      <span title="blocklace constitution + dfa routes + factories govern cell creation & routing in this fed (see blocklace/src/constitution.rs, dfa/src/router.rs, cell/src/factory.rs)">+ blocklace/DFA/factory config</span>
                    </div>
                  </li>`)}
              </ul>`}
          <div class="pfl__note" style="font-size:0.7rem;color:var(--fg-dim);margin-top:6px;">
            KnownFederations registry (node + extension) + sim list. Add via <code>registerFederation</code> (Task #28 / §4.3).
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-federation-list')) {
  customElements.define('dregg-federation-list', DreggFederationList);
}

(function injectStyles() {
  if (document.getElementById('dregg-federation-list-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-federation-list-styles';
  s.textContent = `.pfl__list li { background: var(--bg-raised); } .pfl__count { font-size:0.8rem; }`;
  document.head.appendChild(s);
})();

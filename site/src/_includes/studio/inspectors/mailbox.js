/**
 * <dregg-mailbox uri="dregg://mailbox/<owner-pubkey>">
 *
 * THE ORGAN (docs/ORGANS.md §2): a hosted inbox over the relay. The relay is
 * a store-and-forward service — senders enqueue SEALED bodies to your inbox;
 * you drain them with a CUSTODY PROOF (a dequeue proof: old/new roots +
 * remaining leaves + the entry's content_hash). The relay sees only
 * ciphertext.
 *
 * Unlike the trustline / channels organs (operator-local on the node), the
 * relay is a SEPARATE network-facing service on its own port (default :3100,
 * node/src/relay_service.rs). So this inspector reads `GET /relay/status` and
 * `GET /relay/inbox/{owner}/status` against a RELAY base URL — derived from
 * the node host (port → 3100) and overridable. Cross-port / cross-origin
 * reads are CORS-gated in the browser; when blocked it says so rather than
 * fabricate a queue depth.
 */
import { parseRef } from '../uri.js';
import {
  InspectorBase,
  dreggCodeLink,
  emptyState,
  renderParseError,
  shortHex,
} from './_base.js';

const RELAY_KEY = 'dregg.relay.baseUrl';

/** Derive a default relay base from the node base: same host, port 3100. */
function defaultRelayBase(nodeBase) {
  try {
    const saved = localStorage.getItem(RELAY_KEY);
    if (saved) return saved.replace(/\/+$/, '');
  } catch {}
  if (!nodeBase) return '';
  try {
    const u = new URL(nodeBase);
    u.port = '3100';
    return u.toString().replace(/\/+$/, '');
  } catch { return ''; }
}

async function relayGet(base, path) {
  if (!base) return null;
  try {
    const res = await fetch(`${base}${path}`, { headers: { Accept: 'application/json' } });
    if (!res.ok) return null;
    return await res.json();
  } catch { return null; }
}

class DreggMailbox extends InspectorBase {
  _render() {
    const { h, render, html, effect, signal } = this._api;
    const refAttr = this.getAttribute('uri');
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    let parsed = null; try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'mailbox')) return;
    const root = document.createElement('div'); this.appendChild(root);

    const nodeBase = this._runtime?.nodeBase || null;
    const relayBase = signal(this.getAttribute('relay') || defaultRelayBase(nodeBase));
    const state = signal({ phase: 'idle' });

    const load = async () => {
      const base = relayBase.value;
      const owner = parsed?.id || '';
      if (!base) { state.value = { phase: 'no-relay' }; return; }
      state.value = { phase: 'loading' };
      const [relay, inbox] = await Promise.all([
        relayGet(base, '/relay/status'),
        owner ? relayGet(base, `/relay/inbox/${owner}/status`) : Promise.resolve(null),
      ]);
      if (!relay && !inbox) { state.value = { phase: 'unreachable' }; return; }
      state.value = { phase: 'ready', relay, inbox };
    };
    load();

    const Component = () => {
      const s = state.value;
      const owner = parsed?.id || '';
      const head = (badges) => html`
        <header class="dregg-organ__head">
          <div>
            <div class="dregg-organ__title">
              <span class="dregg-inspector__kind">mailbox</span>
              <code title=${owner}>${shortHex(owner, 18)}</code>
            </div>
            <div class="dregg-organ__subtitle">A hosted inbox over the store-and-forward relay —
              sealed bodies in, drained with a custody proof. ORGANS §2.</div>
          </div>
          <div class="dregg-organ__badges">${badges}</div>
        </header>`;

      const relayBar = () => html`
        <div class="dregg-organ__relaybar">
          <span>relay</span>
          <input class="dregg-organ__relay-input" type="url" value=${relayBase.value || ''}
                 placeholder="https://host:3100" spellcheck="false"
                 onChange=${(e) => {
                   const v = e.target.value.trim().replace(/\/+$/, '');
                   relayBase.value = v;
                   try { localStorage.setItem(RELAY_KEY, v); } catch {}
                   load();
                 }} />
          <button type="button" class="dregg-organ__relay-go" onClick=${() => load()}>reload</button>
        </div>`;

      if (s.phase === 'no-relay') {
        return html`<div class="dregg-inspector dregg-organ">
          ${head(html`<span class="dregg-organ__badge dregg-organ__badge--warn">relay base unset</span>`)}
          ${relayBar()}
          ${emptyState(html, 'Point at a relay',
            'The relay is a separate service (default port :3100). Set its base URL above to read this inbox’s live depth + root.')}
        </div>`;
      }
      if (s.phase === 'loading' || s.phase === 'idle') {
        return html`<div class="dregg-inspector dregg-organ">${head(null)}${relayBar()}
          <div class="dregg-organ__loading">reading <code>/relay/inbox/${shortHex(owner, 8)}/status</code>…</div></div>`;
      }
      if (s.phase === 'unreachable') {
        return html`<div class="dregg-inspector dregg-organ">
          ${head(html`<span class="dregg-organ__badge dregg-organ__badge--warn">unreachable</span>`)}
          ${relayBar()}
          ${emptyState(html, 'Relay not reachable',
            'No response from the relay (it may be down, not running on this base, or the browser cross-origin read is CORS-blocked — the relay is a separate-port service).')}
        </div>`;
      }
      const r = s.relay;
      const i = s.inbox;
      return html`<div class="dregg-inspector dregg-organ">
        ${head(html`
          ${i ? html`<span class=${`dregg-organ__badge ${i.evicted ? 'dregg-organ__badge--warn' : 'dregg-organ__badge--ok'}`}>${i.evicted ? 'evicted' : 'hosted'}</span>` : html`<span class="dregg-organ__badge dregg-organ__badge--warn">no inbox</span>`}
          ${r ? html`<span class="dregg-organ__badge">bond ${r.bond ?? '—'}</span>` : null}`)}
        ${relayBar()}

        ${i ? html`
          <div class="dregg-organ__grid">
            <div><span>pending messages</span><strong>${i.pending_messages ?? 0}</strong></div>
            <div><span>committed capacity</span><strong>${i.committed_capacity ?? '—'}</strong></div>
            <div><span>last drain height</span><strong>${i.last_drain_height ?? '—'}</strong></div>
            <div><span>evicted</span><strong>${i.evicted ? 'yes' : 'no'}</strong></div>
          </div>
          <div class="dregg-organ__roots">
            <div><span>queue root</span><code title=${i.queue_root || ''}>${shortHex(i.queue_root || '', 14)}</code></div>
          </div>`
        : html`<div class="dregg-organ__notice">No hosted inbox for this owner on this relay (they have not subscribed here).</div>`}

        ${r ? html`
          <div class="dregg-organ__parties">
            <div><span>relay operator</span>${r.operator_id ? dreggCodeLink(html, `dregg://cell/${r.operator_id}`, shortHex(r.operator_id, 14), r.operator_id) : html`<code>—</code>`}</div>
          </div>` : null}

        <section class="dregg-organ__section">
          <h4>Custody, not trust</h4>
          <p class="dregg-organ__note">The relay moves opaque ciphertext. Every drained message arrives
            with its full <code>DequeueProof</code> (old/new roots + remaining leaves + the entry’s
            <code>content_hash</code>); a recipient recomputes the body’s content hash and verifies the
            proof against the queue’s own verifier before trusting it. Sealing and opening are
            client-side — the relay never sees a key.</p>
        </section>
      </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-mailbox')) customElements.define('dregg-mailbox', DreggMailbox);

/**
 * <dregg-channel uri="dregg://channel/<cell>">
 *
 * THE ORGAN (docs/ORGANS.md §4): a group is a CELL — the membership
 * commitment, the key-epoch counter, and the epoch-key commitment live
 * on-cell; joins / removals / rekeys are ordinary turns. Message BODIES never
 * touch the chain (control plane on-cell, data plane ciphertext over any
 * transport).
 *
 * THE KEYSTONE — epoch unification. The group's key epoch and the capability
 * freshness epoch are THE SAME counter, so `remove(m)` ends, in ONE atomic
 * turn, BOTH m's forward-read ability (they never receive the epoch-e+1 key)
 * AND m's group-held capabilities (staled by the freshness check). The
 * `epochs_unified` flag is that invariant — this inspector surfaces it as the
 * headline tooth, loud when it is ever false.
 *
 * Reads the LIVE room from `GET /channels/status/{cell}`
 * (node/src/channels_service.rs, the route @dregg/sdk ChannelsClient drives).
 */
import { parseRef } from '../uri.js';
import {
  InspectorBase,
  dreggCodeLink,
  emptyState,
  renderParseError,
  shortHex,
} from './_base.js';

class DreggChannel extends InspectorBase {
  _render() {
    const { h, render, html, effect, signal } = this._api;
    const refAttr = this.getAttribute('uri');
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    let parsed = null; try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'channel')) return;
    const root = document.createElement('div'); this.appendChild(root);

    const state = signal({ phase: 'idle' });
    const nodeBase = this._runtime?.nodeBase || null;
    const nodeGet = this._runtime?.nodeGet || null;

    const load = async () => {
      if (!parsed) return;
      if (!nodeBase || !nodeGet) { state.value = { phase: 'no-node' }; return; }
      state.value = { phase: 'loading' };
      const status = await nodeGet(`/channels/status/${parsed.id}`);
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
              <span class="dregg-inspector__kind">channel</span>
              ${id ? dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id) : null}
            </div>
            <div class="dregg-organ__subtitle">An encrypted group as a cell — membership root,
              key epoch, and epoch-key commitment on-cell; bodies off-chain. ORGANS §4.</div>
          </div>
          <div class="dregg-organ__badges">${badges}</div>
        </header>`;

      if (s.phase === 'no-node') {
        return html`<div class="dregg-inspector dregg-organ">
          ${head(html`<span class="dregg-organ__badge dregg-organ__badge--warn">node-only</span>`)}
          ${emptyState(html, 'Connect a node to read the room',
            'Channels are a node-side organ (the node seals the epoch-key fan-out). Switch the runtime to a remote node to read this room’s live epoch + membership.')}
        </div>`;
      }
      if (s.phase === 'loading' || s.phase === 'idle') {
        return html`<div class="dregg-inspector dregg-organ">${head(null)}
          <div class="dregg-organ__loading">reading <code>/channels/status</code>…</div></div>`;
      }
      if (s.phase === 'unreachable') {
        return html`<div class="dregg-inspector dregg-organ">
          ${head(html`<span class="dregg-organ__badge dregg-organ__badge--warn">unreachable</span>`)}
          ${emptyState(html, 'No live channel at this id',
            'The node returned nothing for this group (it may not be an open room on this operator, or the channels service is not mounted / CORS-blocked).')}
        </div>`;
      }
      const c = s.status;
      const unified = c.epochs_unified === true;
      return html`<div class="dregg-inspector dregg-organ">
        ${head(html`
          <span class=${`dregg-organ__badge ${c.open ? 'dregg-organ__badge--ok' : 'dregg-organ__badge--warn'}`}>${c.open ? 'open' : 'closed'}</span>
          <span class="dregg-organ__badge">tag ${c.tag ?? '—'}</span>`)}

        <div class=${`dregg-organ__keystone ${unified ? 'dregg-organ__keystone--ok' : 'dregg-organ__keystone--bad'}`}>
          <div class="dregg-organ__keystone-mark">${unified ? '✓' : '✗'}</div>
          <div>
            <strong>${unified ? 'Epochs unified' : 'EPOCH DIVERGENCE'}</strong>
            <span>${unified
              ? `key epoch = freshness epoch = ${c.epoch}. remove(m) darkens m’s forward-read AND m’s group-held capabilities in ONE turn.`
              : `key epoch ${c.epoch} ≠ delegation epoch ${c.delegation_epoch} — the keystone invariant is broken; removals would not stale capabilities.`}</span>
          </div>
        </div>

        <div class="dregg-organ__grid">
          <div><span>key epoch</span><strong>${c.epoch ?? '—'}</strong></div>
          <div><span>freshness (delegation) epoch</span><strong>${c.delegation_epoch ?? '—'}</strong></div>
          <div><span>members</span><strong>${c.members == null ? '—' : c.members}</strong></div>
          <div><span>messages held</span><strong>${c.messages_held == null ? '—' : c.messages_held}</strong></div>
        </div>

        <div class="dregg-organ__parties">
          <div><span>admin</span>${c.admin ? dreggCodeLink(html, `dregg://cell/${c.admin}`, shortHex(c.admin, 14), c.admin) : html`<code>—</code>`}</div>
        </div>

        <div class="dregg-organ__roots">
          <div><span>membership root</span><code title=${c.member_root || ''}>${shortHex(c.member_root || '', 14)}</code></div>
          <div><span>epoch-key commit</span><code title=${c.key_commit || ''}>${shortHex(c.key_commit || '', 14)}</code></div>
        </div>

        <section class="dregg-organ__section">
          <h4>Control plane on-cell, data plane off-chain</h4>
          <p class="dregg-organ__note">Joins / removals / rekeys are ordinary turns that bump the
            membership root, the epoch, the epoch-key commitment, AND the cell’s
            <code>delegation_epoch</code> together. Message bodies are ciphertext posted to the relay
            (<code>/channels/post</code>) and never touch the chain — only the sealed epoch-key
            fan-out delivers a key, one sealed key per current member.</p>
        </section>
      </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-channel')) customElements.define('dregg-channel', DreggChannel);

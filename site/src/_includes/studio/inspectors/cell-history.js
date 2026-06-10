/**
 * <dregg-cell-history uri="dregg://cell-history/<cell-id>"> — RECEIPT
 * TIME-TRAVEL for one cell.
 *
 * Walks the cell's receipt chain BACKWARD (each receipt links its predecessor
 * via `previous_receipt_hash`; the list is ordered by `chain_index`) and lets
 * the user scrub along it. At every step it shows what the node actually
 * serves about that point in history:
 *
 *   * the pre → post STATE COMMITMENTS (the receipt binds the whole
 *     post-state — guarantee C; the commitment chain IS the cell's state
 *     evolution as the protocol witnesses it),
 *   * the turn (hash, agent, #actions, computrons, time, finality),
 *   * proof / witness status (executor-signed · has_proof · DWR1 witnesses),
 *   * a deep link into the witnessed-receipt inspector for full detail.
 *
 * HONESTY: the node serves historical COMMITMENTS + effects, not historical
 * slot values (cells are not versioned key-value stores; the commitment is
 * the canonical historical object). The CURRENT slot values are shown at the
 * head only, clearly labeled. Nothing is interpolated or fabricated.
 *
 * Runtime surface: prefers `runtime.listCellReceipts(id)` (RemoteRuntime —
 * server-side ?cell= filter over /api/starbridge/receipts). Falls back to
 * client-side filtering of `runtime.listReceipts()` by agent / touched cells
 * (works on the in-memory wasm runtime too).
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex, dreggCodeLink, emptyState, whatIsThisLink } from './_base.js';

function tsLabel(ts) {
  const n = Number(ts);
  if (!Number.isFinite(n) || n <= 0) return '';
  try {
    const d = new Date(n > 1e12 ? n : n * 1000);
    return d.toISOString().replace('T', ' ').replace(/\.\d+Z$/, 'Z');
  } catch { return String(ts); }
}

/** Order receipts newest-first: chain_index desc, then previous-hash links. */
function orderChain(receipts) {
  const list = [...receipts];
  list.sort((a, b) => {
    const ai = Number(a.chain_index ?? -1);
    const bi = Number(b.chain_index ?? -1);
    if (ai !== bi) return bi - ai;
    return Number(b.timestamp ?? 0) - Number(a.timestamp ?? 0);
  });
  // Verify backward links where present (purely informational — broken links
  // are surfaced, not hidden).
  for (let i = 0; i < list.length - 1; i++) {
    const prevHash = list[i].previous_receipt_hash;
    if (!prevHash) continue;
    const next = list[i + 1];
    const nextHash = next.receipt_hash || next.turn_hash;
    list[i]._link_ok = String(prevHash).toLowerCase() === String(nextHash || '').toLowerCase();
  }
  return list;
}

function cellMatches(r, id) {
  const want = String(id || '').toLowerCase();
  const fields = [r.agent, r.cell, r.cell_id, r.target];
  if (fields.some((f) => String(f || '').toLowerCase() === want)) return true;
  const touched = r.touched_cells || r.cells || [];
  return Array.isArray(touched) && touched.some((c) => String(c || '').toLowerCase() === want);
}

class DreggCellHistory extends InspectorBase {
  _render() {
    const { h, render, html, effect, signal } = this._api;
    const refAttr = this.getAttribute('uri');
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'cell-history')) return;
    const cellId = parsed.id;

    const runtime = this._runtime;
    const chainSig = typeof runtime.listCellReceipts === 'function'
      ? runtime.listCellReceipts(cellId)
      : null;
    const allSig = typeof runtime.listReceipts === 'function' ? runtime.listReceipts() : null;
    const cellSig = typeof runtime.getCell === 'function' ? runtime.getCell(cellId) : null;

    const root = document.createElement('div');
    this.appendChild(root);

    // Scrub position as a signal (0 = head / newest) — the render effect
    // tracks it, so setPos re-renders without hooks.
    const posSig = signal(0);

    const Component = () => {
      // Resolve the chain: server-filtered if available (null = still loading),
      // else client-filtered from the full receipt list.
      let receipts = chainSig ? chainSig.value : null;
      let filteredClientSide = false;
      if (!Array.isArray(receipts) || receipts.length === 0) {
        const all = (allSig && allSig.value) || [];
        const fallback = all.filter((r) => cellMatches(r, cellId));
        if (fallback.length || receipts === null) {
          if (fallback.length) { receipts = fallback; filteredClientSide = true; }
        }
      }
      const loading = chainSig && chainSig.value === null && !filteredClientSide;
      const chain = orderChain(receipts || []);
      const cell = cellSig ? cellSig.value : null;

      const pos = Math.min(posSig.value, Math.max(chain.length - 1, 0));
      const setPos = (p) => { posSig.value = Math.max(0, Math.min(p, chain.length - 1)); };
      const at = chain[pos] || null;

      if (loading) {
        return html`<div class="dregg-inspector dregg-inspector--empty">walking the receipt chain for <code>${shortHex(cellId, 12)}</code>…</div>`;
      }
      if (!chain.length) {
        return emptyState(html, 'No receipts for this cell',
          html`The runtime has no receipt whose agent / touched cells include <code>${shortHex(cellId, 16)}</code>.
          A cell with no turns yet has no history — its whole state is its genesis.`);
      }

      const headBadge = pos === 0
        ? html`<span class="dregg-ch__pill dregg-ch__pill--head">HEAD (newest)</span>`
        : html`<span class="dregg-ch__pill">${pos} turn${pos === 1 ? '' : 's'} before head</span>`;

      const proofBits = at ? [
        at.executor_signed ? 'executor-signed' : null,
        at.has_proof ? 'proof' : null,
        at.has_witness ? `${at.witness_count || ''} witness${(at.witness_count || 0) === 1 ? '' : 'es'}`.trim() : null,
        at.finality && at.finality !== 'unknown' ? `finality: ${at.finality}` : null,
      ].filter(Boolean) : [];

      const receiptUri = at ? `dregg://receipt/${at.turn_hash || at.receipt_hash}` : null;

      return html`
        <div class="dregg-inspector dregg-ch">
          <header class="dregg-ch__head">
            <span class="dregg-inspector__kind">cell-history</span>
            ${dreggCodeLink(html, `dregg://cell/${cellId}`, shortHex(cellId, 16), 'open the cell')}
            <span class="dregg-inspector__meta">${chain.length} receipt${chain.length === 1 ? '' : 's'} in chain${filteredClientSide ? ' (client-filtered)' : ''}</span>
            ${whatIsThisLink(html, 'cell-history')}
          </header>

          <div class="dregg-ch__scrub">
            <button class="dregg-inspector__button" disabled=${pos >= chain.length - 1}
              onClick=${() => setPos(Math.min(pos + 1, chain.length - 1))}>◀ older</button>
            <input type="range" class="dregg-ch__slider" min="0" max=${chain.length - 1} step="1"
              value=${chain.length - 1 - pos}
              onInput=${(e) => setPos(chain.length - 1 - Number(e.target.value))} />
            <button class="dregg-inspector__button" disabled=${pos <= 0}
              onClick=${() => setPos(Math.max(pos - 1, 0))}>newer ▶</button>
            ${headBadge}
          </div>

          ${at && html`
            <div class="dregg-ch__at">
              <div class="dregg-ch__commits" title="the receipt binds the WHOLE post-state (guarantee C): this commitment pair IS the protocol's witnessed state evolution at this step">
                <div class="dregg-ch__commit"><span>pre-state</span><code title=${at.pre_state_hash}>${shortHex(at.pre_state_hash, 18) || '(unavailable)'}</code></div>
                <div class="dregg-ch__arrow">→</div>
                <div class="dregg-ch__commit dregg-ch__commit--post"><span>post-state</span><code title=${at.post_state_hash}>${shortHex(at.post_state_hash, 18) || '(unavailable)'}</code></div>
              </div>
              <dl class="dregg-inspector__kv">
                <dt>turn</dt><dd>${dreggCodeLink(html, receiptUri, shortHex(at.turn_hash || at.receipt_hash, 20), 'open the witnessed receipt')}</dd>
                <dt>agent</dt><dd>${at.agent ? dreggCodeLink(html, `dregg://cell/${at.agent}`, shortHex(at.agent, 14)) : html`<em>—</em>`}</dd>
                ${at.chain_index != null && html`<dt>chain index</dt><dd>${String(at.chain_index)}</dd>`}
                <dt>time</dt><dd>${tsLabel(at.timestamp) || html`<em>—</em>`}</dd>
                <dt>actions</dt><dd>${String(at.action_count ?? 0)} · ${String(at.computrons_used ?? 0)} computrons</dd>
                ${Array.isArray(at.effect_kinds) && at.effect_kinds.length
                  ? html`<dt>effects</dt><dd>${at.effect_kinds.map((k) => html`<span class="dregg-ch__pill">${k}</span> `)}</dd>` : null}
                <dt>attestation</dt>
                <dd>${proofBits.length
                  ? proofBits.map((b) => html`<span class="dregg-ch__pill dregg-ch__pill--proof">${b}</span> `)
                  : html`<em>none recorded</em>`}</dd>
              </dl>
              ${at._link_ok === false && html`
                <div class="dregg-inspector__notice dregg-inspector__notice--warn">
                  chain-link mismatch: this receipt's <code>previous_receipt_hash</code> does not match
                  the next-older receipt the node returned. Shown as served — not repaired.
                </div>`}
            </div>`}

          <details class="dregg-inspector__section" open=${pos === 0}>
            <summary>current state at HEAD ${cell && cell.found === false ? '(cell not found on this runtime)' : ''}</summary>
            <div class="dregg-inspector__section-body">
              ${cell ? html`
                <dl class="dregg-inspector__kv">
                  <dt>balance</dt><dd>${String(cell.balance ?? '—')}</dd>
                  <dt>nonce</dt><dd>${String(cell.nonce ?? '—')}</dd>
                  ${cell.state_commitment ? html`<dt>state commitment</dt><dd><code title=${cell.state_commitment}>${shortHex(cell.state_commitment, 20)}</code></dd>` : null}
                  ${Array.isArray(cell.fields) && cell.fields.length
                    ? html`<dt>slots</dt><dd>${cell.fields.map((f, i) => html`<span class="dregg-ch__pill" title=${String(f)}>[${i}] ${shortHex(String(f), 10)}</span> `)}</dd>` : null}
                </dl>` : html`<div class="dregg-inspector__note">cell detail unavailable on this runtime.</div>`}
              <div class="dregg-inspector__note">
                Honest scope: the node serves historical state <strong>commitments</strong> (above, per receipt)
                plus per-turn effects — not historical slot values. The slots here are the cell <strong>now</strong>;
                each receipt's post-state commitment is the canonical historical object a verifier checks.
              </div>
            </div>
          </details>

          <details class="dregg-inspector__section">
            <summary>full chain (${chain.length}, newest first)</summary>
            <div class="dregg-inspector__section-body">
              <table class="dregg-inspector__table">
                <thead><tr><th></th><th>turn</th><th>post-state</th><th>time</th><th>attest</th></tr></thead>
                <tbody>
                  ${chain.map((r, i) => html`
                    <tr class=${i === pos ? 'dregg-ch__row--at' : ''} style="cursor:pointer" onClick=${() => setPos(i)}>
                      <td>${i === 0 ? 'head' : `−${i}`}</td>
                      <td><code title=${r.turn_hash}>${shortHex(r.turn_hash || r.receipt_hash, 14)}</code></td>
                      <td><code title=${r.post_state_hash}>${shortHex(r.post_state_hash, 14)}</code></td>
                      <td>${tsLabel(r.timestamp)}</td>
                      <td>${[r.executor_signed && 'sig', r.has_proof && 'proof', r.has_witness && 'wit'].filter(Boolean).join('·') || '—'}</td>
                    </tr>`)}
                </tbody>
              </table>
            </div>
          </details>
        </div>`;
    };

    this._dispose = effect(() => {
      // subscribe to the live signals so the timeline re-renders on poll/scrub
      if (chainSig) chainSig.value;
      if (allSig) allSig.value;
      if (cellSig) cellSig.value;
      posSig.value;
      render(h(Component, {}), root);
    });
  }
}

if (!customElements.get('dregg-cell-history')) {
  customElements.define('dregg-cell-history', DreggCellHistory);
}

(function injectStyles() {
  if (document.getElementById('dregg-cell-history-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-cell-history-styles';
  s.textContent = `
.dregg-ch__head { display:flex; align-items:center; gap:10px; flex-wrap:wrap; border-bottom:1px solid var(--line,#30363d); padding-bottom:6px; margin-bottom:8px; }
.dregg-ch__scrub { display:flex; align-items:center; gap:10px; flex-wrap:wrap; margin:10px 0; }
.dregg-ch__slider { flex:1; min-width:160px; accent-color: var(--accent, #5b8a5a); }
.dregg-ch__pill { display:inline-block; border:1px solid var(--line,#30363d); border-radius:999px; padding:1px 8px; font-size:0.68rem; color:var(--fg-dim,#9aa0a6); }
.dregg-ch__pill--head { border-color:#62c47a; color:#8ee6a2; text-transform:uppercase; }
.dregg-ch__pill--proof { border-color:#62c47a; color:#8ee6a2; }
.dregg-ch__at { border:1px solid var(--line,#30363d); border-radius:6px; background:var(--bg-raised,#161b22); padding:10px; }
.dregg-ch__commits { display:flex; align-items:center; gap:10px; flex-wrap:wrap; margin-bottom:8px; cursor:help; }
.dregg-ch__commit { border:1px solid var(--line,#30363d); border-radius:5px; background:var(--bg,#0d1117); padding:6px 9px; min-width:0; }
.dregg-ch__commit span { display:block; font-size:0.64rem; text-transform:uppercase; color:var(--fg-dim,#9aa0a6); }
.dregg-ch__commit code { font-size:0.78rem; color:var(--fg,#e8f0e8); word-break:break-all; }
.dregg-ch__commit--post { border-color: var(--accent,#5b8a5a); }
.dregg-ch__arrow { color:var(--fg-dim,#9aa0a6); }
.dregg-ch__row--at td { background: color-mix(in srgb, var(--accent,#5b8a5a) 14%, transparent); }
`;
  document.head.appendChild(s);
})();

// Ring Trades — intent graph editor + cycle search + REAL atomic settle.
//
// The cycle math is a greedy DFS (real). The SETTLEMENT is no longer a DOM
// string flip: each leg of the found cycle is submitted as a REAL transfer
// turn through the in-browser wasm `execute_turn` (the canonical dregg-turn
// TurnExecutor). Atomicity is enforced the way dregg actually enforces it:
// all legs run against a FRESH runtime; the ring "commits" only if EVERY leg's
// receipt is `committed`. If any leg is rejected by the executor (e.g. a party
// can't cover its leg — conservation/balance fails), we discard the runtime so
// NOTHING persists — a real all-or-nothing rollback, with the executor's real
// rejection reason surfaced.

import { mountSection } from './_newworld.js';
import { renderRingTradeSvg } from '../visualizers/ring-trade.js';

// Greedy cycle search: find any cycle reachable from `start` via DFS.
function findCycle(nodes, edges) {
  const adj = new Map(nodes.map(n => [n.id, []]));
  for (const e of edges) adj.get(e.from)?.push(e.to);
  for (const start of nodes.map(n => n.id)) {
    const stack = [{ id: start, path: [start] }];
    const seen = new Set();
    while (stack.length) {
      const { id, path } = stack.pop();
      for (const next of adj.get(id) || []) {
        if (next === start && path.length >= 2) {
          return [...path, next];
        }
        const key = `${id}->${next}|${path.join(',')}`;
        if (seen.has(key)) continue;
        seen.add(key);
        if (!path.includes(next)) {
          stack.push({ id: next, path: [...path, next] });
        }
      }
    }
  }
  return null;
}

export function initRingTrades(wasm) {
  mountSection('ring-trades', (api) => {
    const { html, signal } = api;

    const nodes = signal([
      { id: 'A', label: 'A wants apples', has: 'pears' },
      { id: 'B', label: 'B wants pears',  has: 'oranges' },
      { id: 'C', label: 'C wants oranges',has: 'apples' },
    ]);
    const edges = signal([
      { from: 'A', to: 'B' },
      { from: 'B', to: 'C' },
      { from: 'C', to: 'A' },
    ]);
    const cycle = signal([]);
    const settled = signal(null);   // null | 'committed' | 'rolled-back'
    const log = signal([]);
    const receipts = signal([]);    // [{ leg, from, to, status, turn_hash, error }]
    const busy = signal(false);

    function pushLog(msg, kind = 'info') {
      log.value = [...log.value, { t: Date.now(), msg, kind }].slice(-30);
    }

    function addNode() {
      const idChar = String.fromCharCode(65 + nodes.value.length);
      nodes.value = [...nodes.value, { id: idChar, label: idChar, has: '?' }];
      pushLog(`added party ${idChar}`);
    }
    function removeNode(id) {
      nodes.value = nodes.value.filter(n => n.id !== id);
      edges.value = edges.value.filter(e => e.from !== id && e.to !== id);
      pushLog(`removed party ${id}`, 'warn');
      cycle.value = []; settled.value = null; receipts.value = [];
    }
    function addEdge(from, to) {
      if (!from || !to || from === to) return;
      edges.value = [...edges.value, { from, to }];
      pushLog(`leg: ${from} → ${to}`);
      cycle.value = []; settled.value = null; receipts.value = [];
    }
    function search() {
      const c = findCycle(nodes.value, edges.value);
      if (c) {
        cycle.value = c.slice(0, -1);  // drop the closing dup
        pushLog(`cycle found: ${c.join(' → ')}`, 'ok');
        settled.value = null; receipts.value = [];
      } else {
        cycle.value = [];
        pushLog('no cycle in graph', 'warn');
      }
    }

    // The shared good-as-token amount each leg moves. Under the EPOCH
    // "fees-as-moves" model the signing cell's balance must also cover the turn
    // FEE (which doubles as the computron budget AND is debited), so each party
    // is funded with the leg amount PLUS a fee reserve. A balanced, fully-funded
    // ring settles; a starved party (funded 0) can neither pay its leg nor its
    // fee, so the executor rejects that leg and the whole ring rolls back.
    const LEG_AMOUNT = 100;
    const LEG_FEE = 3000; // covers a single-transfer turn's computrons comfortably.

    // Run the whole ring as real transfer turns against a fresh runtime.
    // `starveLeg` (index into the cycle) optionally under-funds one party so
    // its outbound leg is rejected by the executor — driving the real rollback.
    async function settleRing(starveLeg) {
      if (!wasm || busy.value) return;
      const ring = cycle.value;
      if (ring.length < 2) { pushLog('no cycle to settle', 'err'); return; }
      busy.value = true;
      settled.value = null;
      receipts.value = [];

      let handle = null;
      try {
        // Fresh, isolated runtime — discarded on rollback so nothing persists.
        handle = wasm.create_runtime();
        // Genesis (agent 0) funds everyone else; give it ample headroom.
        const genesis = wasm.create_agent(handle, 'clearing-house', 1_000_000n);
        const genesisCell = cellIdOf(genesis);

        // One real agent-cell per party. The starved party gets nothing, so
        // its outbound transfer will overdraw and the executor rejects it.
        const cellOf = new Map();
        for (let i = 0; i < ring.length; i++) {
          const id = ring[i];
          const fund = (starveLeg === i) ? 0n : BigInt(LEG_AMOUNT + LEG_FEE);
          const a = wasm.create_agent(handle, `party-${id}`, fund);
          cellOf.set(id, { idx: a.agent_index ?? a.agentIndex, cell: cellIdOf(a) });
          pushLog(`minted party ${id}${starveLeg === i ? ' (UNFUNDED — will fail its leg)' : ` (funded ${LEG_AMOUNT} + ${LEG_FEE} fee reserve)`}`, starveLeg === i ? 'warn' : 'info');
        }

        // Submit each leg as a REAL transfer turn: party[i] → party[i+1].
        // The cycle closes (last → first), so the ring is balanced when every
        // party is funded.
        const legResults = [];
        let allCommitted = true;
        for (let i = 0; i < ring.length; i++) {
          const fromId = ring[i];
          const toId = ring[(i + 1) % ring.length];
          const from = cellOf.get(fromId);
          const to = cellOf.get(toId);
          const actions = [{ type: 'transfer', to: to.cell, amount: LEG_AMOUNT }];

          let res;
          try {
            res = wasm.execute_turn(handle, from.idx, JSON.stringify(actions), BigInt(LEG_FEE));
          } catch (e) {
            res = { status: 'error', error: String(e && e.message || e) };
          }
          const status = res.status || 'unknown';
          const entry = {
            leg: `${fromId} → ${toId}`,
            status,
            turn_hash: res.turn_hash || null,
            error: res.error || null,
          };
          legResults.push(entry);
          receipts.value = [...legResults];

          if (status === 'committed') {
            pushLog(`leg ${fromId} → ${toId}: committed · ${String(res.turn_hash).slice(0, 12)}…`, 'ok');
          } else {
            allCommitted = false;
            pushLog(`leg ${fromId} → ${toId}: ${status}${res.error ? ' · ' + res.error : ''}`, 'err');
            // Real atomic rollback: a rejected leg fails the WHOLE ring. Stop
            // submitting further legs and discard the runtime below.
            pushLog('a leg failed → ATOMIC ROLLBACK: discarding the entire settlement (nothing persists)', 'err');
            break;
          }
        }

        if (allCommitted) {
          settled.value = 'committed';
          pushLog(`ring settled atomically: ${ring.join(' → ')} → ${ring[0]} (${ring.length} real transfer turns committed)`, 'ok');
        } else {
          settled.value = 'rolled-back';
        }
      } catch (e) {
        settled.value = 'rolled-back';
        pushLog(`settlement error → rollback: ${String(e && e.message || e)}`, 'err');
      } finally {
        // Whether committed or rolled back, this throwaway runtime is done.
        // On rollback, destroying it is the rollback: no partial state escapes.
        try { if (handle != null) wasm.destroy_runtime(handle); } catch {}
        busy.value = false;
      }
    }

    function reset() {
      cycle.value = []; settled.value = null; receipts.value = [];
      pushLog('reset settlement state');
    }

    function cellIdOf(r) {
      if (!r || typeof r !== 'object') return '';
      return r.cell_id || r.cellId || r.id || '';
    }

    // Local UI state for the edge picker
    const newFrom = signal('A');
    const newTo = signal('B');

    const App = api.reactive(() => html`
      <section class="vizzer" aria-label="Ring trade demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">Ring-trade solver</h3>
          <p class="vizzer__sub">${cycle.value.length ? `cycle: ${cycle.value.join(' → ')}` : 'no cycle yet'}</p>
          <div class="vizzer__controls">
            <button class="inline" onClick=${search} disabled=${busy.value}>find cycle</button>
            <button class="inline" onClick=${() => settleRing(-1)} disabled=${!cycle.value.length || busy.value || !wasm}>settle (real turns)</button>
            <button class="inline" data-tone="warm" onClick=${() => settleRing(0)} disabled=${!cycle.value.length || busy.value || !wasm}>starve a leg → rollback</button>
            <button class="inline" onClick=${reset} disabled=${busy.value}>reset</button>
          </div>
        </header>
        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">

          ${renderRingTradeSvg(html, nodes.value, edges.value, cycle.value, settled.value)}

          ${!wasm ? html`<div style="color:var(--danger);font-family:var(--font-mono);font-size:11px;">wasm runtime unavailable — real settlement disabled.</div>` : ''}

          ${receipts.value.length ? html`
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">
                settlement legs — real ${api.text ? '' : ''}execute_turn receipts
                ${settled.value === 'committed' ? html` · <span style="color:var(--ok,#62c47a);">RING COMMITTED</span>` : ''}
                ${settled.value === 'rolled-back' ? html` · <span style="color:var(--danger,#d4685c);">ROLLED BACK (nothing settled)</span>` : ''}
              </h3>
              <div style="display:flex;flex-direction:column;gap:3px;">
                ${receipts.value.map((r, i) => html`
                  <div key=${i} style="display:flex;gap:8px;align-items:center;font-family:var(--font-mono);font-size:11px;">
                    <span class="chip">${r.leg}</span>
                    <span style="color:${r.status === 'committed' ? 'var(--ok,#62c47a)' : 'var(--danger,#d4685c)'};">${r.status}</span>
                    ${r.turn_hash ? html`<span style="color:var(--fg-dim);">${String(r.turn_hash).slice(0, 14)}…</span>` : ''}
                    ${r.error ? html`<span style="color:var(--danger,#d4685c);flex:1;">${r.error}</span>` : ''}
                  </div>
                `)}
              </div>
            </div>
          ` : ''}

          <div class="grid-2">
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">parties</h3>
              <div style="display:flex;flex-direction:column;gap:4px;">
                ${nodes.value.map(n => html`
                  <div key=${n.id} style="display:flex;gap:6px;align-items:center;font-family:var(--font-mono);font-size:11px;">
                    <span class="chip">${n.id}</span>
                    <span style="color:var(--fg-dim);flex:1;">${n.label}</span>
                    <button class="inline" data-tone="danger" onClick=${() => removeNode(n.id)} disabled=${busy.value}>×</button>
                  </div>
                `)}
              </div>
              <button class="inline" style="margin-top:6px;" onClick=${addNode} disabled=${busy.value}>+ party</button>
            </div>
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">add leg</h3>
              <div style="display:flex;gap:6px;align-items:center;">
                <select value=${newFrom.value} onChange=${e => newFrom.value = e.target.value}
                        style="background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:4px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;">
                  ${nodes.value.map(n => html`<option key=${n.id} value=${n.id}>${n.id}</option>`)}
                </select>
                <span style="color:var(--fg-dim);font-family:var(--font-mono);">→</span>
                <select value=${newTo.value} onChange=${e => newTo.value = e.target.value}
                        style="background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:4px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;">
                  ${nodes.value.map(n => html`<option key=${n.id} value=${n.id}>${n.id}</option>`)}
                </select>
                <button class="inline" onClick=${() => addEdge(newFrom.value, newTo.value)} disabled=${busy.value}>add</button>
              </div>
              <div style="margin-top:10px;font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);">
                ${edges.value.length} leg(s) · each leg moves ${LEG_AMOUNT} tokens as a real transfer turn
              </div>
            </div>
          </div>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">log</h3>
            <div class="log" role="log" aria-live="polite">
              ${log.value.length === 0
                ? html`<div style="color:var(--fg-muted);">no events.</div>`
                : log.value.slice().reverse().map((e, i) => html`<div key=${i} class="log__entry" data-kind=${e.kind}>${e.msg}</div>`)}
            </div>
          </div>
        </div>
      </section>
    `);
    return html`<${App} />`;
  }, {
    title: 'Ring trades',
    lede: 'When N parties each want what the next has, the intent solver finds the cycle and settles all N legs as REAL transfer turns through the in-browser executor — atomically (every leg commits) or it rolls the whole ring back (any leg the executor rejects discards the entire settlement).',
    fallback: 'Interactive ring-trade graph editor + cycle solver.',
  });
}

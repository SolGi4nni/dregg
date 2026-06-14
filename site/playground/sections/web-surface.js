// Web Surface — the killer demo (N13): "TWO TABS, ONE SURFACE, the share that REFUSES".
//
// `docs/design-frontiers/WEB-FORWARD.md §4` (the web killer demo) + the §4 web cut
// of `docs/FRONTIER-ROADMAP.md`. The single copy-paste end-to-end web evaluation
// artifact: a browser surface IS a dregg cell's surface capability, carried to a
// `<canvas>` pane, with the no-amplification law firing at the PIXEL LAYER.
//
// Everything here drives the REAL `dregg-cell`/`dregg-turn` crates in wasm32 (the
// `DreggRuntime` + the N10 surface bindings) through the N11 compositor — NOT a
// mock. The honest scope (advertised, per the project law): the in-tab world is
// "the REAL dregg-cell/dregg-turn crates in wasm, differential-anchored," NOT
// "verified-in-browser" (the Lean executor in wasm is research R3).

import { navigateTo } from '../playground.js';
import { deepLinkBanner } from '../studio-embed.js';
import { Compositor, Layout } from '../compositor.js';

export function initWebSurface(wasm) {
  const container = document.getElementById('section-web-surface');
  container.innerHTML = `
    <div class="section-header">
      <h2>Web Surface — two tabs, one surface, the share that refuses</h2>
      ${deepLinkBanner([
        { label: '<dregg-cell>', uri: 'dregg://cell/alice' },
        { label: '<dregg-capability>', uri: 'dregg://capability/0/0' },
      ])}
      <p>
        A dregg window is a <code>Capability{ target: Surface(cell), rights }</code>
        rendered to a <code>&lt;canvas&gt;</code> — the firmament's one handle, carried
        out past seL4, past the native shell, into a browser tab. Alice opens her cell
        as a surface; the title bar (<code>cell … · live · root …</code>) is drawn by the
        COMPOSITOR from the live ledger, <em>never</em> by the pane (the anti-spoof T2
        badge). She shares it read-only with Bob — a real <code>GrantCapability</code>
        turn. Bob tries to share it onward as <strong>writable</strong>: the executor
        <strong>REJECTS</strong> with <code>DelegationDenied</code> — no-amplification
        firing at the pixel layer. Alice revokes Bob's pane: dark THIS frame (n=1).
      </p>
      <p class="muted" style="font-size:12px;color:var(--text-muted,#8795a1);">
        This runs the REAL <code>dregg-cell</code>/<code>dregg-turn</code> crates in
        wasm32 (differential-anchored), the same <code>granted ⊆ held</code> lattice and
        the same <code>TurnExecutor</code> the node runs — not a mock. (The verified Lean
        executor in wasm is a separate research frontier; this is the Rust executor.)
      </p>
      <span class="next-hint" data-next="capabilities">Next: capabilities &#8594;</span>
    </div>

    <div class="controls-row">
      <button class="btn btn-primary" id="ws-step" ${wasm ? '' : 'disabled'}>▶ Run the next step</button>
      <button class="btn" id="ws-reset" ${wasm ? '' : 'disabled'}>Reset</button>
      <span style="margin-left:auto;display:flex;gap:6px;align-items:center;">
        <label style="font-size:12px;color:var(--text-muted,#8795a1);">layout</label>
        <select id="ws-layout" style="background:#222934;color:#cfd8e3;border:1px solid #2d3540;border-radius:4px;padding:2px 6px;">
          <option value="float">float</option>
          <option value="tile">tile</option>
          <option value="stack">stack</option>
        </select>
      </span>
    </div>

    <div style="display:grid;grid-template-columns:1fr 1fr;gap:12px;margin-top:10px;">
      <div>
        <div style="font:12px ui-monospace,monospace;color:#8795a1;margin-bottom:4px;">ALICE'S TAB (the owner)</div>
        <div id="ws-tab-alice"></div>
      </div>
      <div>
        <div style="font:12px ui-monospace,monospace;color:#8795a1;margin-bottom:4px;">BOB'S TAB (the recipient)</div>
        <div id="ws-tab-bob"></div>
      </div>
    </div>

    <div id="ws-banner" style="margin-top:10px;"></div>
    <div id="ws-log" style="margin-top:8px;font:12px ui-monospace,monospace;background:#161b22;border:1px solid #2d3540;border-radius:6px;padding:8px;max-height:200px;overflow:auto;"></div>

    <div style="margin-top:12px;">
      <button class="btn" id="ws-verify" ${wasm ? '' : 'disabled'}>🔎 Verify a whole history yourself (light client, in-tab)</button>
      <span id="ws-verify-out" style="margin-left:8px;font:12px ui-monospace,monospace;color:#8795a1;"></span>
      <div style="margin-top:4px;font-size:11px;color:var(--text-muted,#8795a1);">
        Folds a small real turn-chain into ONE recursive aggregate and light-verifies it
        re-witnessing nothing — the anti-pale-ghost tooth, running in wasm. ⚠ Recursive STARK
        proving in the browser is SLOW (this can take a couple of MINUTES and will block the
        tab); it proves the pipeline runs in-tab. (Verifying a pre-produced devnet proof would
        be instant — that path needs a fork-side serialization of the recursion proof, a named
        follow-up; see N12.)
      </div>
    </div>
  `;

  if (!wasm) return;

  const log = container.querySelector('#ws-log');
  const banner = container.querySelector('#ws-banner');
  const stepBtn = container.querySelector('#ws-step');
  const resetBtn = container.querySelector('#ws-reset');
  const layoutSel = container.querySelector('#ws-layout');

  container.querySelector('.next-hint')?.addEventListener('click', () => navigateTo('capabilities'));

  // --- the demo state machine ----------------------------------------------
  // One shared DreggRuntime is the "single source of truth" both tabs read; each
  // tab is its OWN compositor over that ledger (the two tabs really do composite
  // the SAME surface — re-reading the same cell, drawing the same verified badge).
  let runtime = null;
  let aliceCmp = null;
  let bobCmp = null;
  let aliceIdx = 0; // genesis (alice)
  let bobIdx = 1;   // bob, minted from genesis
  let alicePane = null;
  let bobPane = null;
  let step = 0;

  const STEPS = [
    'Create the shared world (alice = genesis, bob minted from genesis).',
    'Alice opens her cell as a WRITABLE surface — a canvas pane, badge drawn from the ledger.',
    'Alice shares it READ-ONLY with Bob — a real GrantCapability turn. Bob composites the SAME surface.',
    'Bob tries to share it ONWARD as WRITABLE — the executor REFUSES (⚠ over-share at the pixel layer).',
    'Alice REVOKES Bob’s pane — dark THIS frame (n=1, synchronous).',
    'Done. Run the light client below, or Reset.',
  ];

  function logLine(kind, msg) {
    const colors = { ok: '#38c172', err: '#e3342f', info: '#7795f8', warn: '#f6993f' };
    const row = document.createElement('div');
    row.style.color = colors[kind] || '#cfd8e3';
    row.textContent = msg;
    log.appendChild(row);
    log.scrollTop = log.scrollHeight;
  }

  function showBanner(kind, html) {
    const bg = kind === 'warn' ? '#3a2a12' : kind === 'ok' ? '#13301f' : '#1b222c';
    const bd = kind === 'warn' ? '#f6993f' : kind === 'ok' ? '#38c172' : '#2d3540';
    banner.innerHTML = `<div style="background:${bg};border:1px solid ${bd};border-radius:6px;padding:8px 12px;color:#e6edf3;font-size:13px;">${html}</div>`;
  }

  function setStepLabel() {
    stepBtn.textContent = step < STEPS.length ? `▶ ${STEPS[step]}` : '▶ (done — Reset)';
    stepBtn.disabled = step >= STEPS.length;
  }

  // A tiny content painter so each pane shows the live balance + a fill keyed to
  // the cell's source-state-root (visual proof the panes read the SAME cell).
  function paneContent(label) {
    return (ctx, surface) => {
      const id = surface.identity || {};
      // A deterministic swatch from the state root (so both tabs draw it identically).
      const seed = parseInt((id.source_state_root || '0').slice(0, 6) || '0', 16) || 0;
      ctx.fillStyle = `hsl(${seed % 360}, 40%, 22%)`;
      ctx.fillRect(0, 0, ctx.canvas.width, ctx.canvas.height);
      ctx.fillStyle = '#cfd8e3';
      ctx.font = '13px ui-monospace, monospace';
      ctx.fillText(`${label}`, 12, 26);
      ctx.fillStyle = '#9fb0c3';
      ctx.font = '11px ui-monospace, monospace';
      ctx.fillText(`balance ${id.balance}`, 12, 46);
      ctx.fillText(`lifecycle ${id.lifecycle}`, 12, 62);
      ctx.fillStyle = '#7e8a99';
      ctx.fillText(`root ${(id.source_state_root || '').slice(0, 12)}…`, 12, 78);
    };
  }

  function reset() {
    if (runtime != null) {
      try { wasm.destroy_runtime(runtime); } catch (_) {}
    }
    runtime = wasm.create_runtime();
    // Alice (genesis) needs headroom to mint bob + pay the share fee. Bob is
    // funded too, so when HE attempts the onward-widening share the refusal is
    // the GENUINE DelegationDenied (no-amplification) and not a fee-balance
    // failure that would precede it — the teaching moment stays honest. The
    // create_agent binding returns { agent_index, name, cell_id, public_key }.
    aliceIdx = wasm.create_agent(runtime, 'alice', 30000n).agent_index ?? 0;
    bobIdx = wasm.create_agent(runtime, 'bob', 5000n).agent_index ?? 1;
    aliceCmp = new Compositor({ wasm, runtime, mount: container.querySelector('#ws-tab-alice'), area: { w: 360, h: 320 } });
    bobCmp = new Compositor({ wasm, runtime, mount: container.querySelector('#ws-tab-bob'), area: { w: 360, h: 320 } });
    aliceCmp.openConsole('alice', aliceIdx, 'alice console');
    bobCmp.openConsole('bob', bobIdx, 'bob console');
    alicePane = null;
    bobPane = null;
    // reset() performs STEP 0 (create the world) itself; the next "Run next
    // step" click is STEP 1 (open the surface).
    step = 1;
    log.innerHTML = '';
    banner.innerHTML = '';
    container.querySelector('#ws-verify-out').textContent = '';
    logLine('info', 'world created: alice = genesis, bob minted from genesis (real CreateCellFromFactory turn).');
    setStepLabel();
  }

  function applyLayout() {
    const l = layoutSel.value;
    aliceCmp?.setLayout(l);
    bobCmp?.setLayout(l);
  }

  function runStep() {
    banner.innerHTML = '';
    if (step === 1) {
      // Alice opens her cell as a WRITABLE surface (None = widest authority).
      const id = wasm.open_surface(runtime, aliceIdx, 'none');
      alicePane = aliceCmp.openSurface('alice', aliceIdx, 'alice’s document', paneContent('alice’s document'));
      aliceCmp.present(alicePane, 1);
      logLine('ok', `open_surface(alice, writable) → badge from ledger: cell ${id.owning_cell_id.slice(0,8)}… · ${id.lifecycle} · root ${id.source_state_root.slice(0,8)}…`);
      showBanner('ok', 'Alice opened her cell as a <b>writable</b> surface. The title bar is drawn by the compositor from the live ledger — not the pane.');
    } else if (step === 2) {
      // Alice shares READ-ONLY with Bob — a real GrantCapability turn.
      const out = wasm.share_surface(runtime, aliceIdx, bobIdx, aliceIdx, 'signature');
      if (out.ok) {
        logLine('ok', `share_surface(alice → bob, read-only) committed: ${out.reason}`);
        // Bob now composites the SAME surface (his own compositor, same cell).
        bobPane = bobCmp.openSurface('bob', aliceIdx, 'alice’s document (shared, read-only)', paneContent('shared (read-only)'));
        bobCmp.present(bobPane, 1);
        showBanner('ok', 'Alice shared the pane <b>read-only</b> with Bob (a real <code>GrantCapability</code> turn). Bob’s tab now composites the <b>same</b> surface — same cell, same verified badge.');
      } else {
        logLine('err', `share refused: ${out.reason}`);
      }
    } else if (step === 3) {
      // Bob tries to share it ONWARD as WRITABLE (a widening) — REFUSED.
      const out = wasm.share_surface(runtime, bobIdx, aliceIdx, aliceIdx, 'none');
      if (!out.ok) {
        logLine('warn', `THE REFUSAL → ${out.reason}`);
        // The ⚠ over-share teaching banner — at the pixel layer.
        showBanner('warn', '⚠ <b>over-share refused.</b> Bob tried to share the read-only pane ONWARD as <b>writable</b> — the executor rejected it with <code>DelegationDenied</code> (<code>granted ⊄ held</code>). No-amplification fired <b>at the pixel layer</b>, the same law a light client checks at the wire.');
        // Bob's pane flashes (re-read identity; it's unchanged — the widening
        // never produced a verified turn, so nothing changed on-ledger).
        bobCmp.refreshIdentities();
      } else {
        logLine('err', `BUG: the widening onward share unexpectedly COMMITTED: ${out.reason}`);
      }
    } else if (step === 4) {
      // Alice revokes Bob's pane — dark THIS frame (n=1, synchronous).
      const removed = wasm.revoke_surface(runtime, bobIdx, aliceIdx);
      logLine(removed ? 'ok' : 'warn', `revoke_surface(bob) → ${removed ? 'cap removed — synchronous at n=1' : 'no cap held'}`);
      // Bob can no longer present — the glass goes dark this frame.
      const pres = wasm.present_surface(runtime, bobIdx, aliceIdx, 'signature');
      logLine(pres.ok ? 'err' : 'ok', `bob present after revoke → ${pres.ok ? 'STILL PAINTS (bug)' : 'refused — the glass is dark'}`);
      if (bobPane != null) bobCmp.closeSurface(bobPane);
      showBanner('ok', 'Alice <b>revoked</b> Bob’s pane. At n=1 (the local tab) it goes dark THIS frame — a subsequent <code>present</code> finds nothing held. Synchronous revocation, the firmament’s n=1 collapse.');
    }
    step += 1;
    setStepLabel();
  }

  stepBtn.addEventListener('click', runStep);
  resetBtn.addEventListener('click', () => { reset(); });
  layoutSel.addEventListener('change', applyLayout);

  // The light-client button (N12): fold a small real chain IN THE TAB and
  // light-verify it, re-witnessing nothing — the anti-pale-ghost tooth. Recursive
  // proving is heavy, so this runs a tiny k=2 chain; it may take a moment.
  container.querySelector('#ws-verify').addEventListener('click', () => {
    const out = container.querySelector('#ws-verify-out');
    if (typeof wasm.light_client_demo !== 'function') {
      out.textContent = 'light client (verify_history-in-wasm) ships in the recursion-enabled wasm build — see N12.';
      out.style.color = '#f6993f';
      return;
    }
    out.textContent = 'folding + verifying a real chain in the tab (recursive proving — a moment)…';
    out.style.color = '#7795f8';
    // Defer so the "working…" message paints before the (synchronous, heavy) prove.
    setTimeout(() => {
      try {
        const t0 = performance.now();
        const v = wasm.light_client_demo(2, 100n); // k=2 (the chain-binding needs ≥2 turns)
        const ms = Math.round(performance.now() - t0);
        if (v && v.attested) {
          out.innerHTML = `<span style="color:#38c172;">AttestedHistory ✓</span> — ${v.num_turns} turns, genesis→final folded, re-witnessed nothing (${ms} ms). <span style="color:#7e8a99;">${v.named_floor}</span>`;
        } else {
          out.textContent = `not attested: ${v && v.named_floor ? v.named_floor : 'unknown'}`;
          out.style.color = '#e3342f';
        }
      } catch (e) {
        out.textContent = `verify failed: ${e.message || e}`;
        out.style.color = '#e3342f';
      }
    }, 30);
  });

  // Boot into the first state so the panes are visible immediately.
  reset();
}

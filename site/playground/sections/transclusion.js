// Transclusion — Xanadu made HONEST, and you can TOUCH it: "transclude a span,
// amend the source, the quote follows live — then forge it, and it REFUSES."
//
// Ted Nelson's Xanadu promised TRANSCLUSION: include-by-reference where the quoted
// material keeps its identity + provenance, joined by two-way links that cannot
// break. The open web could never make it honest — a "transcluded" quote was just a
// copy: nothing forced it to equal the source, nothing stopped it rotting, the
// back-link was a hand-maintained index. dregg ships the missing piece: the VERIFIED
// cross-cell finalized read (the `dregg://` attested fetch). This section NAMES that
// as transclusion and lets a visitor drive it end-to-end.
//
// Everything here drives the REAL `starbridge-web-surface::transclusion` path in
// wasm32 (`TranscludedField::include` over a genuine `WebOfCells` — a real
// `dregg_cell::Ledger` + the real `dregg_types::AttestedRoot` receipt-stream
// verifier) — NOT a mock, NOT a re-implementation. Only the RESOLVE/RENDER path
// reaches the browser (a separate minimal wasm entry, `bindings_transclusion`); the
// circuit prover + the recursion path are untouched.

import { navigateTo } from '../playground.js';
import { deepLinkBanner } from '../studio-embed.js';

// The demo's named source document (the "constitution" everyone quotes).
const DOC = 'constitution';
const DOC_URL = 'dregg://constitution';

// The successive committed values the source amends through (Nelson's unbreakable
// link: the dregg:// ref never changes, but it re-resolves to each new value).
const VERSIONS = [
  '<h1>The Charter</h1><p>Quorum threshold = <b>3</b>.</p>',
  '<h1>The Charter</h1><p>Quorum threshold = <b>5</b>. <i>(amended)</i></p>',
  '<h1>The Charter</h1><p>Quorum threshold = <b>7</b>, ratified by the council. <i>(amended again)</i></p>',
];

export function initTransclusion(wasm) {
  const container = document.getElementById('section-transclusion');
  container.innerHTML = `
    <div class="section-header">
      <h2>Transclusion — touch a live honest-quote (Xanadu that shipped)</h2>
      ${deepLinkBanner([
        { label: '<dregg-cell>', uri: 'dregg://cell/constitution' },
        { label: '<dregg://constitution>', uri: 'dregg://constitution' },
      ])}
      <p>
        Ted Nelson's Xanadu promised <b>transclusion</b>: quote-by-reference, where the
        quoted span keeps its identity and provenance, joined by two-way links that
        cannot break. The open web could never make it honest — a "transcluded" quote is
        just a <em>copy</em>: nothing forces it to equal the source, nothing stops it
        rotting, the back-link is a hand-maintained index. dregg ships the missing piece:
        a <code>dregg://</code> link is a <b>capability into a cell</b>, and resolving it
        is a <b>verified cross-cell finalized read</b> that returns <em>attested</em>
        content (content-addressed + a receipt + a quorum-signed <code>AttestedRoot</code>).
        So a quote <b>IS</b> the value the source committed, at a cited immutable receipt.
      </p>
      <p>
        Drive it yourself: <b>transclude</b> the source span (the displayed bytes ARE the
        source's committed bytes), <b>amend</b> the source (the <code>dregg://</code> ref
        is unchanged, but the <b>live</b> quote follows it while a <b>snapshot</b> stays
        pinned — I-confluence), then <b>forge</b> it — a lying node swaps the bytes and
        the client <b>REFUSES</b> with <code>ContentHashMismatch</code>. A forged quote
        cannot be opened.
      </p>
      <p class="muted" style="font-size:12px;color:var(--text-muted,#8795a1);">
        This runs the REAL <code>starbridge-web-surface::transclusion</code> path in
        wasm32 — <code>TranscludedField::include</code> over a genuine
        <code>WebOfCells</code> (a real <code>dregg_cell::Ledger</code> + the real
        <code>dregg_types::AttestedRoot</code> receipt-stream verifier), the same
        attestation chain the node runs — not a mock. Only the resolve/render path is
        compiled to wasm; the circuit prover is untouched.
      </p>
      <span class="next-hint" data-next="web-surface">Next: web surface &#8594;</span>
    </div>

    <div class="controls-row">
      <button class="btn btn-primary" id="tx-step" ${wasm ? '' : 'disabled'}>▶ Run the next step</button>
      <button class="btn" id="tx-reset" ${wasm ? '' : 'disabled'}>Reset</button>
      <span id="tx-height" style="margin-left:auto;font:12px ui-monospace,monospace;color:#7e8a99;"></span>
    </div>

    <div style="display:grid;grid-template-columns:1fr 1fr;gap:12px;margin-top:10px;">
      <div>
        <div style="font:12px ui-monospace,monospace;color:#8795a1;margin-bottom:4px;">
          THE SOURCE — <code>${DOC_URL}</code> (a real cell; edit + amend it)
        </div>
        <textarea id="tx-source" spellcheck="false" style="width:100%;box-sizing:border-box;height:96px;background:#161b22;color:#cfd8e3;border:1px solid #2d3540;border-radius:6px;padding:8px;font:12px ui-monospace,monospace;resize:vertical;" ${wasm ? '' : 'disabled'}></textarea>
        <div class="controls-row" style="gap:8px;margin-top:6px;">
          <button class="btn" id="tx-amend" ${wasm ? '' : 'disabled'}>✎ Amend the source (commit a new finalized value)</button>
        </div>
        <div id="tx-source-badge" style="margin-top:6px;font:11px ui-monospace,monospace;color:#7e8a99;"></div>
      </div>
      <div>
        <div style="font:12px ui-monospace,monospace;color:#8795a1;margin-bottom:4px;">
          THE TRANSCLUDED QUOTE — what your document shows (verified)
        </div>
        <div id="tx-quote-live" style="min-height:96px;background:#13301f1a;border:1px solid #2d3540;border-radius:6px;padding:8px;color:#e6edf3;font-size:13px;">
          <span style="color:#7e8a99;font:12px ui-monospace,monospace;">(not transcluded yet — run step 1, or click "Transclude")</span>
        </div>
        <div class="controls-row" style="gap:8px;margin-top:6px;flex-wrap:wrap;">
          <button class="btn" id="tx-include" ${wasm ? '' : 'disabled'}>⧉ Transclude the span (verified finalized read)</button>
          <button class="btn" id="tx-snapshot" ${wasm ? '' : 'disabled'}>📌 Pin a snapshot (I-confluent)</button>
        </div>
        <div id="tx-quote-prov" style="margin-top:6px;font:11px ui-monospace,monospace;color:#7e8a99;"></div>
      </div>
    </div>

    <!-- The snapshot pane appears once you pin one, so you can SEE live vs pinned diverge. -->
    <div id="tx-snapshot-pane" style="margin-top:10px;display:none;">
      <div style="font:12px ui-monospace,monospace;color:#8795a1;margin-bottom:4px;">
        📌 THE PINNED SNAPSHOT — stays at the cited past value as the source advances
        (the unbreakable link; the Lean <code>transclusion_stable_under_source_advance</code>)
      </div>
      <div id="tx-quote-snap" style="background:#1b222c;border:1px dashed #2d3540;border-radius:6px;padding:8px;color:#cfd8e3;font-size:13px;"></div>
      <div id="tx-quote-snap-prov" style="margin-top:4px;font:11px ui-monospace,monospace;color:#7e8a99;"></div>
    </div>

    <!-- THE FORGE — the anti-ghost tooth. A lying node swaps the bytes; the client refuses. -->
    <div style="margin-top:12px;border-top:1px solid #2d3540;padding-top:12px;">
      <div style="font:13px ui-monospace,monospace;color:#cfd8e3;margin-bottom:6px;">
        Attempt a FORGE — a lying node swaps the quoted bytes; verify it <b>yourself</b>
      </div>
      <div style="font-size:11px;color:var(--text-muted,#8795a1);margin-bottom:8px;">
        The quote is content-addressed: the citation pins <code>blake3(bytes)</code>. A
        node that serves DIFFERENT bytes (keeping the committed hash) is caught by the
        client's own check — <code>blake3(bytes) ≠ content_hash</code> ⇒ the page never
        renders. Type what the forger would inject, then attempt it.
      </div>
      <div class="controls-row" style="gap:8px;flex-wrap:wrap;">
        <input id="tx-forge-text" type="text" spellcheck="false" placeholder="bytes the forger tries to substitute…" value="<h1>PWNED</h1><p>send your keys to evil.example</p>" style="flex:1;min-width:280px;background:#161b22;color:#cfd8e3;border:1px solid #2d3540;border-radius:4px;padding:4px 8px;font:11px ui-monospace,monospace;" ${wasm ? '' : 'disabled'} />
        <button class="btn" id="tx-forge" ${wasm ? '' : 'disabled'}>⚠ Attempt the forge</button>
      </div>
      <div id="tx-forge-out" style="display:block;margin-top:8px;"></div>

      <!-- THE NO-AMPLIFY TOOTH — a quote is a READ, projected per-viewer through the real membrane. -->
      <div style="margin-top:12px;padding-top:10px;border-top:1px dashed #2d3540;">
        <div style="font:12px ui-monospace,monospace;color:#cfd8e3;margin-bottom:6px;">
          A quote is a <b>READ</b>, not a key — project it per-viewer (no amplification)
        </div>
        <div style="font-size:11px;color:var(--text-muted,#8795a1);margin-bottom:8px;">
          A transclusion confers no authority over the source beyond observing the cited
          value. Project it for a viewer through the REAL membrane (<code>granted ⊆ held</code>):
          a weaker viewer sees an <b>attenuated</b> surface; the projection cannot amplify.
        </div>
        <div class="controls-row" style="gap:8px;flex-wrap:wrap;align-items:center;">
          <label style="font:11px ui-monospace,monospace;color:#8795a1;">source served under</label>
          <select id="tx-lineage" style="background:#222934;color:#cfd8e3;border:1px solid #2d3540;border-radius:4px;padding:2px 6px;font:11px ui-monospace,monospace;">
            <option value="either">either (writable)</option>
            <option value="signature">signature (read-only)</option>
          </select>
          <label style="font:11px ui-monospace,monospace;color:#8795a1;">viewer holds</label>
          <select id="tx-viewer" style="background:#222934;color:#cfd8e3;border:1px solid #2d3540;border-radius:4px;padding:2px 6px;font:11px ui-monospace,monospace;">
            <option value="signature">signature (weaker)</option>
            <option value="either">either (equal)</option>
            <option value="none">none (widest — must NOT amplify)</option>
          </select>
          <button class="btn" id="tx-project" ${wasm ? '' : 'disabled'}>🔎 Project for the viewer</button>
        </div>
        <div id="tx-project-out" style="display:block;margin-top:6px;font:12px ui-monospace,monospace;color:#8795a1;"></div>
      </div>
    </div>

    <div id="tx-log" style="margin-top:12px;font:12px ui-monospace,monospace;background:#161b22;border:1px solid #2d3540;border-radius:6px;padding:8px;max-height:180px;overflow:auto;"></div>
  `;

  container.querySelector('.next-hint')?.addEventListener('click', () => navigateTo('web-surface'));

  if (!wasm) return;

  // The transclusion-demo wasm entry must be present (the resolve/render path).
  if (typeof wasm.transclusion_create !== 'function') {
    container.querySelector('#tx-log').innerHTML =
      '<span style="color:#f6993f;">the transclusion path ships in the wasm build with bindings_transclusion — rebuild wasm/pkg.</span>';
    return;
  }

  const log = container.querySelector('#tx-log');
  const stepBtn = container.querySelector('#tx-step');
  const resetBtn = container.querySelector('#tx-reset');
  const heightEl = container.querySelector('#tx-height');
  const sourceTa = container.querySelector('#tx-source');
  const sourceBadge = container.querySelector('#tx-source-badge');
  const quoteLive = container.querySelector('#tx-quote-live');
  const quoteProv = container.querySelector('#tx-quote-prov');
  const snapPane = container.querySelector('#tx-snapshot-pane');
  const quoteSnap = container.querySelector('#tx-quote-snap');
  const quoteSnapProv = container.querySelector('#tx-quote-snap-prov');
  const includeBtn = container.querySelector('#tx-include');
  const snapshotBtn = container.querySelector('#tx-snapshot');
  const amendBtn = container.querySelector('#tx-amend');
  const forgeBtn = container.querySelector('#tx-forge');
  const forgeText = container.querySelector('#tx-forge-text');
  const forgeOut = container.querySelector('#tx-forge-out');
  const projectBtn = container.querySelector('#tx-project');
  const lineageSel = container.querySelector('#tx-lineage');
  const viewerSel = container.querySelector('#tx-viewer');
  const projectOut = container.querySelector('#tx-project-out');

  // --- demo state -----------------------------------------------------------
  let demo = null;        // the wasm transclusion-demo handle
  let amendCount = 0;     // how many times the source has been amended (picks VERSIONS)
  // The pinned snapshot is a CLIENT-side capture of a verified quote at a height;
  // we keep its rendered view so it can stay visibly pinned while the live quote moves.
  let pinned = null;      // { view, height } | null
  let step = 0;

  const STEPS = [
    'Transclude the span — a verified finalized read; the displayed bytes ARE the source’s committed bytes.',
    'Pin a SNAPSHOT of the current value (I-confluent — it will stay put as the source advances).',
    'Amend the source — commit a NEW finalized value (the dregg:// ref is unchanged).',
    'Re-read LIVE — the live quote FOLLOWS the amend; the snapshot stays pinned.',
    'Attempt a FORGE — a lying node swaps the bytes; the client REFUSES (ContentHashMismatch).',
    'Done. Project per-viewer (no amplification), or Reset.',
  ];

  function logLine(kind, msg) {
    const colors = { ok: '#38c172', err: '#e3342f', info: '#7795f8', warn: '#f6993f' };
    const row = document.createElement('div');
    row.style.color = colors[kind] || '#cfd8e3';
    row.textContent = msg;
    log.appendChild(row);
    log.scrollTop = log.scrollHeight;
  }

  function setStepLabel() {
    stepBtn.textContent = step < STEPS.length ? `▶ ${STEPS[step]}` : '▶ (done — Reset)';
    stepBtn.disabled = step >= STEPS.length;
  }

  function setHeight(h) {
    heightEl.textContent = `federation height: ${h}`;
  }

  // Render a quote view (from the wasm binding) into a target pane + its provenance line.
  function renderQuote(paneEl, provEl, view, label) {
    // The quoted bytes are the source's committed value — we render them as the
    // document would show them (it's the source's own HTML), inside a sandboxed-ish
    // container. (Demo content is trusted authored HTML; the security property being
    // shown is the VERIFICATION, not script isolation.)
    paneEl.innerHTML = `<div>${view.text}</div>`;
    const fin = view.finalized ? 'finalized ✓' : 'UNATTESTED';
    const verified = view.verifies
      ? '<span style="color:#38c172;">verifies ✓</span>'
      : '<span style="color:#e3342f;">DOES NOT VERIFY</span>';
    provEl.innerHTML =
      `${label} ${verified} · ${fin} · cite ${view.source_uri.slice(0, 16)}…` +
      ` · content ${view.content_hash.slice(0, 12)}… · receipt ${view.receipt_hash.slice(0, 12)}…` +
      ` · @h${view.at_height}`;
  }

  function refreshSourceBadge() {
    sourceBadge.textContent = `committed url ${DOC_URL} · the dregg:// ref is content-addressed (it never changes across amends)`;
  }

  // (re)publish the source at VERSIONS[0] into a fresh demo world.
  function reset() {
    if (demo != null) {
      try { wasm.transclusion_destroy(demo); } catch (_) {}
    }
    demo = wasm.transclusion_create();
    amendCount = 0;
    pinned = null;
    step = 0;
    snapPane.style.display = 'none';
    quoteSnap.innerHTML = '';
    quoteSnapProv.textContent = '';
    quoteLive.innerHTML = '<span style="color:#7e8a99;font:12px ui-monospace,monospace;">(not transcluded yet — run step 1, or click "Transclude")</span>';
    quoteProv.textContent = '';
    forgeOut.innerHTML = '';
    projectOut.textContent = '';
    log.innerHTML = '';
    sourceTa.value = VERSIONS[0];

    const pub = wasm.transclusion_publish(demo, DOC, VERSIONS[0], DOC_URL);
    setHeight(pub.at_height);
    refreshSourceBadge();
    logLine('info', `published ${DOC_URL} (a real origin cell; content committed in slot 0, 3-of-3 quorum) @h${pub.at_height}.`);
    setStepLabel();
  }

  // Transclude (the verified finalized read) and render into the LIVE pane.
  function doInclude() {
    try {
      const view = wasm.transclusion_include(demo, DOC);
      renderQuote(quoteLive, quoteProv, view, 'live');
      logLine('ok', `transcluded: a verified finalized read — displayed bytes ARE the source's committed value (content ${view.content_hash.slice(0, 12)}…, ${view.verifies ? 'verifies' : 'FAILS'}).`);
      return view;
    } catch (e) {
      logLine('err', `transclude failed: ${e && e.message ? e.message : e}`);
      return null;
    }
  }

  // Pin a snapshot — capture the CURRENT live read and freeze it in the snapshot pane.
  function doSnapshot() {
    try {
      const view = wasm.transclusion_include(demo, DOC); // resolve the current value now
      pinned = { view, height: view.at_height };
      snapPane.style.display = '';
      renderQuote(quoteSnap, quoteSnapProv, view, 'pinned');
      logLine('info', `pinned a SNAPSHOT @h${view.at_height} (content ${view.content_hash.slice(0, 12)}…) — it will stay PUT as the source advances (I-confluence).`);
    } catch (e) {
      logLine('err', `snapshot failed: ${e && e.message ? e.message : e}`);
    }
  }

  // Amend the source to the next committed value (or to the textarea's current text
  // if the user edited it).
  function doAmend() {
    try {
      // Prefer the user's edited text; otherwise walk the scripted VERSIONS.
      let next = sourceTa.value;
      const scripted = VERSIONS[Math.min(amendCount + 1, VERSIONS.length - 1)];
      if (next === VERSIONS[amendCount]) {
        // User didn't edit — advance the scripted narrative.
        next = scripted;
        sourceTa.value = next;
      }
      const newHeight = wasm.transclusion_amend(demo, DOC, next);
      amendCount += 1;
      setHeight(newHeight);
      logLine('warn', `amended ${DOC_URL} → a NEW finalized value @h${newHeight}. The dregg:// ref is UNCHANGED — same citation, advanced source.`);
      // The live quote, if shown, now FOLLOWS the new value; re-resolve it.
      let liveHash = null;
      if (quoteProv.textContent) {
        const live = wasm.transclusion_read_live(demo, DOC);
        liveHash = live.content_hash;
        renderQuote(quoteLive, quoteProv, live, 'live');
        logLine('ok', `the LIVE quote followed the amend → now shows the new value (receipt ${live.receipt_hash.slice(0, 12)}… advanced).`);
      }
      // The pinned snapshot, if any, STAYS at its captured value (re-render it from
      // the cached view — it does NOT re-fetch). If the live quote moved, the pin
      // did not: the divergence is the unbreakable link, both directions.
      if (pinned) {
        renderQuote(quoteSnap, quoteSnapProv, pinned.view, 'pinned');
        if (liveHash && liveHash !== pinned.view.content_hash) {
          logLine('info', `the SNAPSHOT stayed PINNED @h${pinned.height} (content ${pinned.view.content_hash.slice(0, 12)}…) — the live quote moved, the pin did not. The unbreakable link, both directions.`);
        }
      }
    } catch (e) {
      logLine('err', `amend failed: ${e && e.message ? e.message : e}`);
    }
  }

  // The FORGE — the headline refusal.
  function doForge() {
    const forged = forgeText.value || '<h1>forged</h1>';
    try {
      const out = wasm.transclusion_forge_attempt(demo, DOC, forged);
      if (out.refused) {
        forgeOut.innerHTML =
          `<div style="background:#3a2a12;border:1px solid #f6993f;border-radius:6px;padding:8px 12px;color:#e6edf3;font-size:13px;">` +
          `⛔ <b>FORGE REFUSED</b> — the client rejected it with <code>${out.reason}</code>. ` +
          `The forger tried to serve <code style="color:#f6993f;">${escapeHtml(out.forged_text.slice(0, 48))}${out.forged_text.length > 48 ? '…' : ''}</code>, ` +
          `but the citation pins <code>content ${out.committed_content_hash.slice(0, 12)}…</code> = <code>blake3</code> of the source's REAL bytes. ` +
          `<code>blake3(forged) ≠ content_hash</code> ⇒ the page never renders. A forged quote cannot be opened.` +
          `</div>`;
        logLine('warn', `THE REFUSAL → ${out.reason}: blake3(forged bytes) ≠ the committed content hash. The quote stayed bound to the SOURCE, not the forger.`);
      } else {
        forgeOut.innerHTML =
          `<div style="background:#3a1212;border:1px solid #e3342f;border-radius:6px;padding:8px 12px;color:#e6edf3;font-size:13px;">` +
          `BUG: the forge was NOT refused (${out.reason}).</div>`;
        logLine('err', `BUG: the forge slipped through (${out.reason}).`);
      }
    } catch (e) {
      logLine('err', `forge attempt errored: ${e && e.message ? e.message : e}`);
    }
  }

  // The no-amplify projection.
  function doProject() {
    try {
      const out = wasm.transclusion_project_for(demo, DOC, viewerSel.value, lineageSel.value);
      if (out.projected) {
        const amp = out.no_amplify
          ? '<span style="color:#38c172;">no amplification ✓ (projected ⊆ lineage)</span>'
          : '<span style="color:#e3342f;">AMPLIFIED (bug)</span>';
        projectOut.innerHTML =
          `projected: viewer sees rights <b>${out.viewer_rights}</b> (lineage served under <b>${out.lineage_rights}</b>) — ${amp}. ` +
          `A weaker viewer is attenuated to its own ceiling; the quote never handed it the source's authority.`;
        logLine('ok', `project(viewer=${viewerSel.value}, lineage=${lineageSel.value}) → rights ${out.viewer_rights}, no-amplify=${out.no_amplify}.`);
      } else {
        projectOut.innerHTML =
          `<span style="color:#f6993f;">projection REFUSED</span> — ${out.reason}. ` +
          `(An incomparable / over-broad viewer cannot project the quote — the membrane refuses to amplify.)`;
        logLine('warn', `projection refused: ${out.reason}.`);
      }
    } catch (e) {
      logLine('err', `project failed: ${e && e.message ? e.message : e}`);
    }
  }

  // The scripted step machine (a guided tour through the same buttons).
  function runStep() {
    if (step === 0) { doInclude(); }
    else if (step === 1) { doSnapshot(); }
    else if (step === 2) { doAmend(); }
    else if (step === 3) {
      const live = wasm.transclusion_include(demo, DOC);
      renderQuote(quoteLive, quoteProv, live, 'live');
      if (pinned) renderQuote(quoteSnap, quoteSnapProv, pinned.view, 'pinned');
      const diverged = pinned && pinned.view.content_hash !== live.content_hash;
      logLine(diverged ? 'ok' : 'info',
        diverged
          ? `LIVE vs PINNED have DIVERGED: live=content ${live.content_hash.slice(0, 12)}… (h${live.at_height}), pinned=content ${pinned.view.content_hash.slice(0, 12)}… (h${pinned.height}). The live quote followed the source; the snapshot did not.`
          : `re-read live (content ${live.content_hash.slice(0, 12)}…).`);
    }
    else if (step === 4) { doForge(); }
    step += 1;
    setStepLabel();
  }

  stepBtn.addEventListener('click', runStep);
  resetBtn.addEventListener('click', () => reset());
  includeBtn.addEventListener('click', () => doInclude());
  snapshotBtn.addEventListener('click', () => doSnapshot());
  amendBtn.addEventListener('click', () => doAmend());
  forgeBtn.addEventListener('click', () => doForge());
  projectBtn.addEventListener('click', () => doProject());

  // Boot into the published state so the source pane is live immediately.
  reset();
}

// Minimal HTML-escape for rendering the forged bytes as INERT text (we show what
// the forger tried, we never execute it).
function escapeHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

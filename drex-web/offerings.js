// offerings.js — the DreggFi Offerings menu client.
//
// Fetches the manifest from the offerings server (offerings.mjs), renders one card
// per offering, and — for the wired ones — POSTs to the per-offering endpoint to
// RUN the real fhegg-solver engine and render the returned clearing + certificate.
// The linked offerings (ring DrEX, launchpad) open their own surfaces. No mock: the
// numbers a card shows are the runner bin's certificate, fetched from the server.

const $ = (t, c, txt) => { const e = document.createElement(t); if (c) e.className = c; if (txt != null) e.textContent = txt; return e; };

// Per-offering parameter presets — small, honest inputs that drive the real bin.
const PARAMS = {
  derivatives: {
    controls: [
      { name: 'kind', type: 'select', options: ['american', 'european'], label: 'family' },
      { name: 'steps', type: 'number', value: 256, label: 'steps (American)' },
      { name: 'strike', type: 'number', value: 100, label: 'strike (American)' },
      { name: 'scenarios', type: 'number', value: 64, label: 'scenarios (European)' },
    ],
    body: (v) => v.kind === 'european'
      ? { kind: 'european', scenarios: +v.scenarios || 64, instruments: 16, seed: 48813 }
      : { kind: 'american', spot: 100, strike: +v.strike || 100, rate: 0.05, vol: 0.2, expiry: 1.0, steps: +v.steps || 256, isPut: true },
  },
  package: {
    controls: [
      { name: 'mode', type: 'select', options: ['sample', 'random'], label: 'instance' },
      { name: 'items', type: 'number', value: 20, label: 'items (random)' },
      { name: 'bids', type: 'number', value: 80, label: 'bids (random)' },
      { name: 'seed', type: 'number', value: 1, label: 'seed (random)' },
    ],
    body: (v) => v.mode === 'random'
      ? { random: { items: +v.items || 20, bids: +v.bids || 80, seed: +v.seed || 0 } }
      : {},
  },
  'drex-shielded': { controls: [], body: () => sampleOrders() },
};

// A tiny revealed-orders batch for the shielded clearing demo (same shape fhegg_clear reads).
function sampleOrders() {
  return [
    { trader: 'alice', offerAsset: 'DREGG', offerAmount: 100, wantAsset: 'USDC', wantMin: 90, priority: 2 },
    { trader: 'bob', offerAsset: 'USDC', offerAmount: 120, wantAsset: 'ETH', wantMin: 1, priority: 1 },
    { trader: 'carol', offerAsset: 'ETH', offerAmount: 2, wantAsset: 'DREGG', wantMin: 150, priority: 3 },
  ];
}

function stageClass(stage) {
  if (/deployable-now/.test(stage)) return 'now';
  if (/spec|not compiled|not yet/.test(stage)) return 'spec';
  return 'linked';
}

function renderCert(cert) {
  const wrap = $('div', 'cert');
  for (const [k, val] of Object.entries(cert)) {
    if (typeof val !== 'boolean') continue;
    const chip = $('span', 'chip ' + (val ? 'pass' : 'fail'), (val ? '✓ ' : '✗ ') + k);
    wrap.appendChild(chip);
  }
  return wrap;
}

// Pull the human-relevant scalars out of a runner result for the KV grid.
function scalars(r) {
  const pick = {};
  for (const k of ['kind', 'family', 'source', 'certifiedValue', 'certifiedPrice', 'dualityGap',
    'certifiedRatio', 'welfare', 'upperBound', 'items', 'bidCount', 'nodes', 'clearedVolume']) {
    if (r[k] !== undefined) pick[k] = r[k];
  }
  // fhegg_clear (shielded) nests its top-line under certificate.clearedVolume.
  if (r.certificate && r.certificate.clearedVolume !== undefined && pick.clearedVolume === undefined)
    pick.clearedVolume = r.certificate.clearedVolume;
  return pick;
}

function renderOut(container, r) {
  container.innerHTML = '';
  container.classList.add('show');
  const cert = r.certificate || {};
  const valid = cert.valid !== undefined ? cert.valid : (r.certificate && r.certificate.valid);
  const head = $('div', 'head');
  head.appendChild($('span', '', r.mechanism ? '' : ''));
  const verdict = $('span', 'verdict ' + (valid ? 'valid' : 'invalid'),
    valid ? 'certificate VALID' : 'certificate INVALID');
  head.appendChild($('span', '', r.tier ? r.tier.split('—')[0].trim() : ''));
  head.appendChild(verdict);
  container.appendChild(head);

  const kv = $('div', 'kv');
  for (const [k, val] of Object.entries(scalars(r))) {
    kv.appendChild($('span', 'k', k));
    kv.appendChild($('span', 'v', String(val)));
  }
  container.appendChild(kv);

  if (Object.keys(cert).length) container.appendChild(renderCert(cert));

  // Negative polarity (the honest reject), if the bin reports one.
  if (r.negativePolarity) {
    const np = $('div', 'note');
    np.style.padding = '2px 12px 8px';
    np.innerHTML = `<b>negative polarity:</b> ${r.negativePolarity.what} → ` +
      (r.negativePolarity.rejected ? '<span style="color:var(--ok)">REJECTED ✓</span>' : '<span style="color:var(--bad)">accepted ✗</span>');
    container.appendChild(np);
  }
  if (r.tamper) {
    const tp = $('div', 'note');
    tp.style.padding = '2px 12px 8px';
    tp.innerHTML = `<b>tamper:</b> ${r.tamper.what} → ` +
      (r.tamper.accept ? '<span style="color:var(--bad)">accepted ✗</span>' : '<span style="color:var(--ok)">REJECTED ✓</span>');
    container.appendChild(tp);
  }

  const det = document.createElement('details'); det.className = 'raw';
  det.appendChild($('summary', '', 'raw certificate JSON'));
  const pre = $('pre', 'raw', JSON.stringify(r, null, 2));
  det.appendChild(pre);
  container.appendChild(det);
}

function card(off) {
  const c = $('div', 'card');
  c.appendChild($('h2', '', off.name));
  c.appendChild($('div', 'mech', off.mechanism));
  const st = $('div', 'stage ' + stageClass(off.stage), off.stage);
  c.appendChild(st);
  c.appendChild($('div', 'tier', off.tier));
  c.appendChild($('div', 'note', off.note));

  const row = $('div', 'row');
  const out = $('div', 'out');
  const preset = PARAMS[off.id];
  const inputs = {};

  if (off.run && preset) {
    // Parameter controls.
    const pbox = $('div', 'params');
    for (const ctl of preset.controls) {
      const lab = $('label', '', ctl.label);
      let inp;
      if (ctl.type === 'select') {
        inp = document.createElement('select');
        for (const o of ctl.options) { const opt = $('option', '', o); opt.value = o; inp.appendChild(opt); }
      } else {
        inp = document.createElement('input'); inp.type = 'number'; inp.value = ctl.value; inp.style.width = '84px';
      }
      inputs[ctl.name] = inp;
      lab.appendChild(inp);
      pbox.appendChild(lab);
    }
    if (preset.controls.length) { pbox.classList.add('show'); c.appendChild(pbox); }

    const btn = $('button', 'run', 'Run the real engine');
    btn.onclick = async () => {
      btn.disabled = true; btn.textContent = 'clearing…';
      const vals = {}; for (const [k, el] of Object.entries(inputs)) vals[k] = el.value;
      try {
        const res = await fetch(off.run, { method: 'POST', headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify(preset.body(vals)) }).then((r) => r.json());
        if (!res.ok) { out.classList.add('show'); out.innerHTML = ''; out.appendChild($('pre', 'raw', 'error: ' + (res.error || 'run failed') + (res.stderr ? '\n' + res.stderr : ''))); }
        else renderOut(out, res.result);
      } catch (e) {
        out.classList.add('show'); out.innerHTML = ''; out.appendChild($('pre', 'raw', 'network error: ' + e.message));
      }
      btn.disabled = false; btn.textContent = 'Run the real engine';
    };
    row.appendChild(btn);
  }

  if (off.link) {
    const a = $('a', 'btn', 'Open surface ↗');
    a.href = off.link; a.target = '_blank'; a.rel = 'noopener';
    row.appendChild(a);
  }
  if (!off.run && !off.link) {
    const s = $('span', 'note', 'spec\'d — wire needed');
    row.appendChild(s);
  }
  c.appendChild(row);
  c.appendChild(out);
  return c;
}

async function main() {
  let m;
  try { m = await fetch('/offerings').then((r) => r.json()); }
  catch (e) { document.getElementById('scope').textContent = 'offerings server unreachable: ' + e.message; return; }
  document.getElementById('scope').textContent = m.scope;
  const grid = document.getElementById('grid');
  for (const off of m.offerings) grid.appendChild(card(off));
  document.getElementById('foot').innerHTML =
    'Each wired offering runs the REAL <code>fhegg-solver</code> engine locally and shows its verified certificate. ' +
    'This is a devnet-DEMO surface — public devnet broadcast + live tokens are the ember-gated step. ' +
    'See <code>docs/deos/DREGGFI-DEVNET-OFFERINGS.md</code> for the stage-per-offering assessment + the deploy path.';
}
main();

// drex-viz.js — the DrEX legibility layer. Turns the fhEgg engine's JSON into
// SVG you can SEE: the cleared circulation ring, the uniform-price crossing, the
// Cert-F certificate as a checkable object, and the privacy-tier reveal-diff.
//
// Every renderer is DRIVEN BY REAL ENGINE OUTPUT — the shapes match fhegg_clear
// (the circulation + Cert-F + verified AIR) and fhegg_uniform (the fold + one
// crossing). No fabricated numbers: the flows, the certificate scalars, the AIR
// accept/reject, and the curves all come from the binaries (live via
// /clear-shielded, or the baked real snapshot in drex-viz-data.js).
//
// Self-contained: inline SVG + vanilla JS, no deps. Theme-aware: reads the current
// light/dark mode and re-renders on toggle (call DrexViz.onThemeChange).
//
// The privacy-tier semantics are HONEST, not decorative:
//   OPEN     (Tier 2): everyone sees every order + every cleared flow.
//   SHIELDED (Tier 1): the descriptor (topology A, weights w, caps c) is PUBLIC;
//                      the flows f — who cleared how much — live only in the STARK
//                      witness. The world's one witness-derived scalar is wᵀf.
//                      What is blurred here is exactly what the STARK provably hides.
//   DARK     (Tier 0): inputs stay ENCRYPTED — nobody (no solver, no committee)
//                      sees an order; only the public result decrypts.
// (Per docs/deos/DREGGFI-PRIVACY-TIERS.md and fhegg_clear's own `hides`/tiers.)

// ── palette (validated dataviz categorical set, light + dark steps) ──
const PAL = {
  light: { cat: ['#2a78d6', '#1baf7a', '#eda100', '#4a3aa7', '#e34948', '#e87ba4', '#eb6834', '#008300'],
    good: '#0ca30c', critical: '#d03b3b', warn: '#b8860b',
    surface: '#fcfcfb', plane: '#f4f3ef', ink: '#0b0b0b', ink2: '#52514e', muted: '#898781',
    grid: '#e1e0d9', axis: '#c3c2b7', ring: 'rgba(11,11,11,0.10)' },
  dark: { cat: ['#3987e5', '#199e70', '#c98500', '#9085e9', '#e66767', '#d55181', '#d95926', '#008300'],
    good: '#0ca30c', critical: '#d03b3b', warn: '#e0a92e',
    surface: '#0d1a14', plane: '#08120d', ink: '#eaf6ef', ink2: '#a9c4b7', muted: '#7f948a',
    grid: '#183226', axis: '#26463a', ring: 'rgba(220,255,240,0.10)' },
};

export function currentMode() {
  const t = document.documentElement.getAttribute('data-theme');
  if (t === 'light' || t === 'dark') return t;
  return matchMedia('(prefers-color-scheme: light)').matches ? 'light' : 'dark';
}
const P = () => PAL[currentMode()];

// Stable asset→hue: fixed order of the assets array (never cycled). ≤5 assets →
// distinct categorical slots; a 6th+ folds to slot 6+ (still fixed, never generated).
function assetColors(assets) {
  const c = P().cat;
  const m = {};
  assets.forEach((a, i) => { m[a] = c[i % c.length]; });
  return m;
}

const esc = (s) => String(s).replace(/[&<>"]/g, (m) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[m]));
const svgOpen = (w, h) => `<svg viewBox="0 0 ${w} ${h}" width="100%" preserveAspectRatio="xMidYMid meet" role="img" style="max-width:100%;height:auto;display:block">`;

// ════════════════════════════════════════════════════════════════════════════
// 1a. THE CIRCULATION RING GRAPH — nodes = assets, edges = orders, cleared
//     circulation highlighted, the binding (bottleneck) edge marked. Driven by
//     the Cert-F (edges, w, c, f, s) + the per-order clearedFlow.
//     `reveal`: 'open' | 'shielded' | 'dark' controls what each viewer learns.
// ════════════════════════════════════════════════════════════════════════════
export function ringGraph(ring, reveal = 'open') {
  const p = P();
  const cert = ring.solverCert;
  const assets = ring.assets;
  const ac = assetColors(assets);
  const W = 540, H = 420, cx = W / 2, cy = H / 2 - 6, R = 138, nodeR = 30;
  // node positions on a circle
  const pos = assets.map((_, i) => {
    const th = -Math.PI / 2 + (i / assets.length) * 2 * Math.PI;
    return { x: cx + R * Math.cos(th), y: cy + R * Math.sin(th) };
  });
  const dark = reveal === 'dark';
  const shielded = reveal === 'shielded';

  let s = svgOpen(W, H);
  s += `<title>DrEX cleared circulation — ${esc(reveal)} view</title>`;
  // arrow markers (cleared / rested)
  s += `<defs>
    <marker id="arw-${reveal}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M0 0L10 5L0 10z" fill="${p.ink2}"/></marker>
    <marker id="arwc-${reveal}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
      <path d="M0 0L10 5L0 10z" fill="${p.good}"/></marker>
  </defs>`;

  // edges: quadratic bezier bowed outward from the chord, arrowhead at head
  cert.edges.forEach((e, i) => {
    const [tail, head] = e;
    const a = pos[tail], b = pos[head];
    const flow = cert.f[i], cap = cert.c[i];
    const cleared = flow > 1e-6;
    const binding = cleared && Math.abs(flow - cap) < 1e-6; // at capacity ⇒ bottleneck
    // trim endpoints to node radius
    const dx = b.x - a.x, dy = b.y - a.y, L = Math.hypot(dx, dy) || 1;
    const ux = dx / L, uy = dy / L;
    const ax = a.x + ux * nodeR, ay = a.y + uy * nodeR;
    const bx = b.x - ux * (nodeR + 8), by = b.y - uy * (nodeR + 8);
    // bow the control point perpendicular (consistent side) for readability
    const mx = (ax + bx) / 2, my = (ay + by) / 2;
    const bow = 34;
    const qx = mx - uy * bow, qy = my + ux * bow;
    const ord = ring.orders[i];
    const dashed = cleared ? '' : 'stroke-dasharray="4 5"';
    const stroke = dark ? p.muted : cleared ? p.good : p.axis;
    const wdt = binding ? 5.5 : cleared ? 3.5 : 2;
    const op = dark ? 0.5 : cleared ? 0.95 : 0.5;
    const mk = dark ? '' : cleared ? `marker-end="url(#arwc-${reveal})"` : `marker-end="url(#arw-${reveal})"`;
    s += `<path d="M${ax.toFixed(1)} ${ay.toFixed(1)} Q${qx.toFixed(1)} ${qy.toFixed(1)} ${bx.toFixed(1)} ${by.toFixed(1)}" fill="none" stroke="${stroke}" stroke-width="${wdt}" stroke-linecap="round" opacity="${op}" ${dashed} ${mk}>`;
    s += `<title>${dark ? 'encrypted order (Tier 0 — no viewer)' : esc(orderTitle(ord, flow, cap, binding, cleared, reveal))}</title></path>`;
    // edge label at the bow apex
    const lx = mx - uy * (bow + 14), ly = my + ux * (bow + 14);
    let lab;
    if (dark) lab = '🔒';
    else if (shielded) lab = cleared ? `${esc(ord.offerAsset)}→${esc(ord.wantAsset)}` : 'rested';
    else lab = cleared ? `${esc(ord.offerAsset)}→${esc(ord.wantAsset)} · ${flow}` : `${esc(ord.offerAsset)}→${esc(ord.wantAsset)} · rests`;
    const labFill = cleared && !dark ? p.ink : p.muted;
    s += `<g font-size="11.5" text-anchor="middle" font-family="system-ui,sans-serif">`;
    s += `<rect x="${lx - measure(lab) / 2 - 5}" y="${ly - 10}" width="${measure(lab) + 10}" height="17" rx="5" fill="${p.surface}" opacity="0.82"/>`;
    if (shielded && cleared) {
      // the flow number is redacted — in the STARK witness, not public
      s += `<text x="${lx}" y="${ly + 2.5}" fill="${labFill}">${lab} · <tspan fill="${p.muted}" style="filter:blur(2.5px)">██</tspan></text>`;
    } else {
      s += `<text x="${lx}" y="${ly + 2.5}" fill="${labFill}" ${binding ? `font-weight="700"` : ''}>${lab}</text>`;
    }
    if (binding && !dark) s += `<text x="${lx}" y="${ly + 16}" fill="${p.warn}" font-size="9.5" font-weight="700">◆ binding · cap ${cap}</text>`;
    s += `</g>`;
  });

  // nodes (assets)
  assets.forEach((asset, i) => {
    const { x, y } = pos[i];
    const col = dark ? p.muted : ac[asset];
    s += `<circle cx="${x}" cy="${y}" r="${nodeR}" fill="${p.surface}" stroke="${col}" stroke-width="3"/>`;
    s += `<circle cx="${x}" cy="${y}" r="${nodeR - 7}" fill="${col}" opacity="${dark ? 0.12 : 0.16}"/>`;
    s += `<text x="${x}" y="${y + 4}" text-anchor="middle" font-size="12.5" font-weight="700" font-family="system-ui,sans-serif" fill="${dark ? p.muted : p.ink}">${dark ? '🔒' : esc(asset)}</text>`;
  });

  s += `</svg>`;
  return s;
}
function orderTitle(o, flow, cap, binding, cleared, reveal) {
  if (reveal === 'shielded') return `order (topology public): ${o.offerAsset}→${o.wantAsset}, cap ${cap} — cleared flow HIDDEN in the STARK witness`;
  if (!cleared) return `${o.trader}: offers ${o.offerAmount} ${o.offerAsset}, wants ≥${o.wantMin} ${o.wantAsset} — RESTS (no ring closed through it)`;
  return `${o.trader}: ${o.offerAsset}→${o.wantAsset}, cleared ${flow} of ${cap}${binding ? ' — BINDING (at capacity; the ring bottleneck)' : ''}`;
}
// crude text width estimate for label backing rects (avoids DOM measurement)
function measure(str) { return String(str).replace(/<[^>]+>/g, '').length * 6.2; }

// ════════════════════════════════════════════════════════════════════════════
// 1b. THE UNIFORM-PRICE CROSSING CURVES — demand (suffix scan, non-increasing) +
//     supply (prefix scan, non-decreasing) step curves, the crossing p*/V* at the
//     argmax of min(D,S), filled vs rested bids. Driven by fhegg_uniform's fold.
// ════════════════════════════════════════════════════════════════════════════
export function crossingCurves(u) {
  const p = P();
  const c = P().cat;
  const cDemand = c[0], cSupply = c[1]; // blue / aqua — validated pair
  const K = u.k;
  const peak = Math.max(...u.curves.demand, ...u.curves.supply, 1);
  const maxV = peak * 1.06; // headroom so the flat top isn't on the frame edge
  const W = 560, H = 360, mL = 44, mR = 16, mT = 20, mB = 78;
  const pw = W - mL - mR, ph = H - mT - mB;
  const X = (j) => mL + (K <= 1 ? 0 : (j / (K - 1)) * pw);
  const Y = (v) => mT + ph - (v / maxV) * ph;

  let s = svgOpen(W, H);
  s += `<title>Uniform-price crossing — ${esc(u.pair)}, p*=${esc(u.clearingPriceLabel)}, V*=${u.clearedVolume}</title>`;
  // gridlines + y ticks
  const ticks = 4;
  for (let t = 0; t <= ticks; t++) {
    const v = (peak * t) / ticks, y = Y(v);
    s += `<line x1="${mL}" y1="${y.toFixed(1)}" x2="${W - mR}" y2="${y.toFixed(1)}" stroke="${p.grid}" stroke-width="1"/>`;
    s += `<text x="${mL - 6}" y="${(y + 3).toFixed(1)}" text-anchor="end" font-size="10" fill="${p.muted}" font-family="system-ui">${Math.round(v)}</text>`;
  }
  // x labels (price grid) + clearing band
  const px = X(u.clearingPriceIndex);
  s += `<rect x="${(px - 1).toFixed(1)}" y="${mT}" width="2" height="${ph}" fill="${p.warn}" opacity="0.55"/>`;
  u.priceGrid.forEach((lab, j) => {
    const active = j === u.clearingPriceIndex;
    s += `<text x="${X(j).toFixed(1)}" y="${H - mB + 16}" text-anchor="middle" font-size="9.5" fill="${active ? p.ink : p.muted}" font-weight="${active ? 700 : 400}" font-family="system-ui">${esc(lab)}</text>`;
  });
  s += `<text x="${(mL + pw / 2).toFixed(1)}" y="${H - mB + 34}" text-anchor="middle" font-size="10.5" fill="${p.ink2}" font-family="system-ui">price (GOLD per ART) →  clearing price p* highlighted</text>`;

  // step-path builder (value constant across each level, stepped at midpoints)
  const stepPath = (arr) => {
    let d = '';
    for (let j = 0; j < K; j++) {
      const x0 = j === 0 ? mL : X(j) - (pw / (K - 1)) / 2;
      const x1 = j === K - 1 ? W - mR : X(j) + (pw / (K - 1)) / 2;
      const y = Y(arr[j]);
      d += (j === 0 ? `M${x0.toFixed(1)} ${y.toFixed(1)}` : `L${x0.toFixed(1)} ${y.toFixed(1)}`) + ` L${x1.toFixed(1)} ${y.toFixed(1)}`;
    }
    return d;
  };
  // supply fill (light), demand fill (light), then lines on top
  s += `<path d="${stepPath(u.curves.supply)}" fill="none" stroke="${cSupply}" stroke-width="2.5" stroke-linejoin="round"/>`;
  s += `<path d="${stepPath(u.curves.demand)}" fill="none" stroke="${cDemand}" stroke-width="2.5" stroke-linejoin="round"/>`;
  // per-level markers with tooltips (matchable = min)
  for (let j = 0; j < K; j++) {
    s += `<circle cx="${X(j).toFixed(1)}" cy="${Y(u.curves.demand[j]).toFixed(1)}" r="3" fill="${cDemand}"><title>${esc(u.priceGrid[j])}: demand D=${u.curves.demand[j]}</title></circle>`;
    s += `<circle cx="${X(j).toFixed(1)}" cy="${Y(u.curves.supply[j]).toFixed(1)}" r="3" fill="${cSupply}"><title>${esc(u.priceGrid[j])}: supply S=${u.curves.supply[j]}</title></circle>`;
  }
  // the crossing point: V* at p*
  const vy = Y(u.clearedVolume);
  s += `<circle cx="${px.toFixed(1)}" cy="${vy.toFixed(1)}" r="6.5" fill="${p.warn}" stroke="${p.surface}" stroke-width="2"><title>clearing: p*=${esc(u.clearingPriceLabel)}, V*=${u.clearedVolume} = argmax min(D,S)</title></circle>`;
  s += `<text x="${(px + 10).toFixed(1)}" y="${(vy - 8).toFixed(1)}" font-size="11.5" font-weight="700" fill="${p.ink}" font-family="system-ui">p*=${esc(u.clearingPriceLabel)} · V*=${u.clearedVolume}</text>`;

  // legend (both series direct-labeled)
  s += `<g font-family="system-ui" font-size="11">`;
  s += `<line x1="${mL}" y1="${H - 8}" x2="${mL + 16}" y2="${H - 8}" stroke="${cDemand}" stroke-width="2.5"/><text x="${mL + 22}" y="${H - 4}" fill="${p.ink2}">demand D(j) — bids at price ≤ limit</text>`;
  s += `<line x1="${mL + 250}" y1="${H - 8}" x2="${mL + 266}" y2="${H - 8}" stroke="${cSupply}" stroke-width="2.5"/><text x="${mL + 272}" y="${H - 4}" fill="${p.ink2}">supply S(j) — asks at price ≥ limit</text>`;
  s += `</g>`;
  s += `</svg>`;
  return s;
}

// The per-order fill bars beneath the crossing (filled vs rested), direct-labeled.
export function fillBars(u) {
  const p = P();
  const rows = u.orders.map((o) => {
    const w = Math.round((o.fill / Math.max(1, o.qty)) * 100);
    const col = o.side === 'bid' ? P().cat[0] : P().cat[1];
    const status = o.filled ? (o.fill === o.qty ? 'filled' : 'partial (pro-rata)') : 'rests';
    const sc = o.filled ? p.good : p.muted;
    return `<div class="dvz-bar">
      <span class="dvz-bl"><b>${esc(o.trader)}</b> <span class="dvz-mut">${o.side} ${o.qty} @≤/≥ ${esc(o.limitLabel)}</span></span>
      <span class="dvz-track"><span class="dvz-fill" style="width:${o.filled ? Math.max(6, w) : 0}%;background:${col}"></span></span>
      <span class="dvz-br" style="color:${sc}">${o.fill}/${o.qty} · ${status}</span>
    </div>`;
  }).join('');
  return `<div class="dvz-bars">${rows}</div>`;
}

// ════════════════════════════════════════════════════════════════════════════
// 2. THE CERTIFICATE, VISUALIZED — weak duality closes (wᵀf = cᵀs, gap≈0),
//    conservation = 0, and the AIR accept (honest) vs the TAMPER reject. The
//    checkable object: "the buyer verifies this themselves." Driven by RING.
// ════════════════════════════════════════════════════════════════════════════
export function certificateViz(ring) {
  const p = P();
  const c = ring.certificate, air = ring.air, tam = ring.tamper;
  const prim = c.clearedVolume, dual = c.dualObjective;
  const maxV = Math.max(prim, dual, 1);
  const W = 540, H = 150, mL = 128, barMax = W - mL - 90;
  const Y1 = 46, Y2 = 92, bh = 26;
  let s = svgOpen(W, H);
  s += `<title>Cert-F: weak duality closes (wᵀf=${prim}=cᵀs), gap≈0</title>`;
  const bar = (y, label, val, col, note) => {
    let g = `<text x="${mL - 10}" y="${y + bh / 2 + 4}" text-anchor="end" font-size="12" font-family="system-ui" fill="${p.ink2}">${label}</text>`;
    g += `<rect x="${mL}" y="${y}" width="${barMax}" height="${bh}" rx="5" fill="${p.grid}"/>`;
    g += `<rect x="${mL}" y="${y}" width="${((val / maxV) * barMax).toFixed(1)}" height="${bh}" rx="5" fill="${col}"><title>${esc(note)}</title></rect>`;
    g += `<text x="${mL + barMax + 8}" y="${y + bh / 2 + 4}" font-size="12.5" font-weight="700" font-family="system-ui" fill="${p.ink}">${val}</text>`;
    return g;
  };
  s += bar(Y1, 'primal  wᵀf', prim, P().cat[0], `cleared weighted volume wᵀf = ${prim}`);
  s += bar(Y2, 'dual  cᵀs', dual, P().cat[1], `dual objective cᵀs = ${dual}`);
  // the closing brace between them
  s += `<text x="${mL + barMax + 46}" y="${(Y1 + Y2) / 2 + bh / 2 + 4}" font-size="12" font-family="system-ui" fill="${p.good}" font-weight="700">gap ${c.dualityGap}</text>`;
  s += `<text x="8" y="18" font-size="11.5" font-family="system-ui" fill="${p.ink2}">weak duality: wᵀf ≤ cᵀs always — here they MEET (gap≈0) ⇒ provably optimal</text>`;
  s += `</svg>`;

  // the checkable-checks grid (the buyer re-runs each; a linear certificate)
  const check = (ok, label, val) =>
    `<div class="dvz-chk ${ok ? 'ok' : 'no'}"><span class="dvz-ci">${ok ? '✓' : '✕'}</span><span class="dvz-cl">${esc(label)}</span><span class="dvz-cv">${esc(val)}</span></div>`;
  const checks = `<div class="dvz-checks">
    ${check(c.conserves, 'conservation ‖Af‖∞ = 0', c.conservationResidual)}
    ${check(c.gapOk, 'duality gap ≤ ε', c.dualityGap)}
    ${check(c.primalBoxed, 'primal boxed 0≤f≤c', c.primalBoxed ? 'yes' : 'no')}
    ${check(c.sNonneg, 'dual slack s ≥ 0', c.sNonneg ? 'yes' : 'no')}
    ${check(c.dualFeasible, 'dual feasible', c.dualFeasible ? 'yes' : 'no')}
    ${check(c.valid, 'certificate valid', c.valid ? 'PROVED-sound' : 'no')}
  </div>`;

  // the verified AIR gate: honest ACCEPT vs tampered REJECT (side by side)
  const gate = `<div class="dvz-gate">
    <div class="dvz-gcol ok">
      <div class="dvz-gh"><span class="dvz-gi">✓</span> honest certificate</div>
      <div class="dvz-gb">the verified AIR (${air.constraints} constraints · ${air.terms} terms · ${air.witnessCells} witness cells) <b class="dvz-acc">ACCEPTS</b></div>
      <div class="dvz-gm">the exact n+4m+1 rows <span class="dvz-mono">Market/CertF.lean</span> proves sound</div>
    </div>
    <div class="dvz-gcol no">
      <div class="dvz-gh"><span class="dvz-gi">✕</span> tampered certificate</div>
      <div class="dvz-gb">${esc(tam.what)} → the AIR <b class="dvz-rej">REJECTS</b></div>
      <div class="dvz-gm">violated: <span class="dvz-mono">${(tam.violated || []).join(', ') || '—'}</span> — a cheat can't even be built</div>
    </div>
  </div>`;

  return `<div class="dvz-cert">${s}${checks}${gate}</div>`;
}

// ════════════════════════════════════════════════════════════════════════════
// 3. THE PRIVACY-TIER REVEAL-DIFF (the killer viz) — the SAME clearing shown
//    three ways: OPEN / SHIELDED / DARK, viewer-by-viewer, what each learns.
//    Honest: SHIELDED blurs exactly what the STARK hides (the flows f); DARK
//    encrypts the inputs (Tier-0 FHE, no viewer). Driven by RING.
// ════════════════════════════════════════════════════════════════════════════
const TIERS = [
  { id: 'open', name: 'OPEN', sub: 'Tier 2 · public', carrier: 'STARK of correctness over a public book',
    learns: ['every order — trader, offer, want', 'every cleared flow (who cleared how much)', 'the binding bottleneck edge', 'the clearing is fair + conserving'],
    hidden: [], badge: 'public' },
  { id: 'shielded', name: 'SHIELDED', sub: 'Tier 1 · private-from-the-world', carrier: 'STARK-ZK (Poseidon2/FRI, hiding PCS) + PQ',
    learns: ['the descriptor: topology A, weights w, caps c (public constants)', 'a fair batch cleared · conservation held', 'the one public scalar: cleared volume wᵀf = 300'],
    hidden: ['the flows f — who cleared how much', 'the dual prices π and slacks s', 'trader identities (shielded-pool note commitments)'], badge: 'solver sees · world does not' },
  { id: 'dark', name: 'DARK', sub: 'Tier 0 · no viewer', carrier: 'FHE (lattice/LWE) + threshold-decrypt only the result',
    learns: ['only the public result decrypts (e.g. the clearing price)', 'a valid batch cleared'],
    hidden: ['every order — inputs stay ENCRYPTED end-to-end', 'no solver, committee, or enclave ever sees an order', 'the flows, the topology, the amounts — all sealed'], badge: 'nobody sees an order' },
];

export function tierReveal(ring) {
  const cols = TIERS.map((t) => {
    const learns = t.learns.map((l) => `<li class="dvz-see">${esc(l)}</li>`).join('');
    const hidden = t.hidden.map((h) => `<li class="dvz-hide">${esc(h)}</li>`).join('');
    return `<div class="dvz-tier dvz-t-${t.id}">
      <div class="dvz-th">
        <div class="dvz-tn">${esc(t.name)}</div>
        <div class="dvz-ts">${esc(t.sub)}</div>
        <div class="dvz-tbadge">${esc(t.badge)}</div>
      </div>
      <div class="dvz-tgraph">${ringGraph(ring, t.id)}</div>
      <div class="dvz-tcarrier"><span class="dvz-clab">carrier</span> ${esc(t.carrier)}</div>
      <div class="dvz-tlists">
        <div class="dvz-tll"><div class="dvz-tlh dvz-tlh-see">this viewer sees</div><ul>${learns}</ul></div>
        ${t.hidden.length ? `<div class="dvz-tll"><div class="dvz-tlh dvz-tlh-hide">hidden from this viewer</div><ul>${hidden}</ul></div>` : ''}
      </div>
    </div>`;
  }).join('');
  return `<div class="dvz-tiers">${cols}</div>
    <div class="dvz-tfoot">One clearing, one verified kernel — <b>fair, conserving, no-mint, proven is identical at every tier</b>; only what the world <i>sees</i> moves along the dial. The blur on SHIELDED is exactly what the STARK provably hides (the flows f); DARK keeps the inputs encrypted (no viewer). <span class="dvz-mono">docs/deos/DREGGFI-PRIVACY-TIERS.md</span></div>`;
}

// ── the stylesheet the viz needs (scoped to .dvz-* ; theme-aware) ──
export function styles() {
  return `
  .dvz-mono{font-family:ui-monospace,'SF Mono',Menlo,monospace;font-size:.9em}
  .dvz-bars{display:flex;flex-direction:column;gap:6px;margin-top:10px}
  .dvz-bar{display:grid;grid-template-columns:190px 1fr auto;align-items:center;gap:10px;font-size:12px}
  .dvz-bl b{font-weight:700}.dvz-mut,.dvz-tier .dvz-mut{opacity:.62}
  .dvz-track{height:12px;border-radius:6px;background:var(--dvz-grid);overflow:hidden}
  .dvz-fill{display:block;height:100%;border-radius:6px;transition:width .5s cubic-bezier(.2,.7,.2,1)}
  .dvz-br{font-variant-numeric:tabular-nums;white-space:nowrap;font-weight:600}
  .dvz-cert{display:flex;flex-direction:column;gap:12px}
  .dvz-checks{display:grid;grid-template-columns:repeat(auto-fit,minmax(215px,1fr));gap:6px}
  .dvz-chk{display:flex;align-items:center;gap:8px;padding:7px 10px;border-radius:8px;font-size:12px;border:1px solid var(--dvz-ring)}
  .dvz-chk.ok{background:color-mix(in srgb,var(--dvz-good) 12%,transparent)}
  .dvz-chk.no{background:color-mix(in srgb,var(--dvz-crit) 14%,transparent)}
  .dvz-ci{font-weight:800}.dvz-chk.ok .dvz-ci{color:var(--dvz-good)}.dvz-chk.no .dvz-ci{color:var(--dvz-crit)}
  .dvz-cl{flex:1}.dvz-cv{font-variant-numeric:tabular-nums;opacity:.8;font-weight:600}
  .dvz-gate{display:grid;grid-template-columns:1fr 1fr;gap:10px}
  .dvz-gcol{padding:11px 13px;border-radius:10px;border:1px solid var(--dvz-ring)}
  .dvz-gcol.ok{background:color-mix(in srgb,var(--dvz-good) 10%,transparent);border-color:color-mix(in srgb,var(--dvz-good) 40%,transparent)}
  .dvz-gcol.no{background:color-mix(in srgb,var(--dvz-crit) 10%,transparent);border-color:color-mix(in srgb,var(--dvz-crit) 40%,transparent)}
  .dvz-gh{font-weight:700;font-size:13px;margin-bottom:5px;display:flex;align-items:center;gap:7px}
  .dvz-gcol.ok .dvz-gi{color:var(--dvz-good)}.dvz-gcol.no .dvz-gi{color:var(--dvz-crit)}
  .dvz-gb{font-size:12.5px;line-height:1.4}.dvz-gm{font-size:11px;opacity:.66;margin-top:5px}
  .dvz-acc{color:var(--dvz-good)}.dvz-rej{color:var(--dvz-crit)}
  .dvz-tiers{display:grid;grid-template-columns:repeat(3,1fr);gap:12px}
  .dvz-tier{border:1px solid var(--dvz-ring);border-radius:12px;padding:12px;background:var(--dvz-surface);display:flex;flex-direction:column;gap:9px}
  .dvz-t-shielded{border-color:color-mix(in srgb,var(--dvz-c1) 45%,var(--dvz-ring))}
  .dvz-t-dark{border-color:color-mix(in srgb,var(--dvz-muted) 45%,var(--dvz-ring))}
  .dvz-th{text-align:center}
  .dvz-tn{font-weight:800;font-size:15px;letter-spacing:.06em}
  .dvz-ts{font-size:11px;opacity:.7;margin-top:1px}
  .dvz-tbadge{display:inline-block;margin-top:5px;font-size:10.5px;padding:2px 9px;border-radius:20px;background:color-mix(in srgb,var(--dvz-c1) 16%,transparent);opacity:.92}
  .dvz-tgraph{background:var(--dvz-plane);border-radius:9px;padding:4px}
  .dvz-tcarrier{font-size:11px;line-height:1.35}.dvz-clab{font-weight:700;opacity:.6;text-transform:uppercase;letter-spacing:.05em;font-size:9.5px}
  .dvz-tlists{display:flex;flex-direction:column;gap:8px}
  .dvz-tlh{font-size:10px;text-transform:uppercase;letter-spacing:.05em;font-weight:700;margin-bottom:3px}
  .dvz-tlh-see{color:var(--dvz-good)}.dvz-tlh-hide{color:var(--dvz-muted)}
  .dvz-tll ul{list-style:none;margin:0;padding:0;display:flex;flex-direction:column;gap:3px}
  .dvz-tll li{font-size:11.5px;line-height:1.35;padding-left:16px;position:relative}
  .dvz-see::before{content:'✓';position:absolute;left:0;color:var(--dvz-good);font-weight:700}
  .dvz-hide{opacity:.72}.dvz-hide::before{content:'🔒';position:absolute;left:0;font-size:10px}
  .dvz-tfoot{margin-top:12px;font-size:12px;line-height:1.5;opacity:.85;padding:11px 13px;border-radius:10px;background:var(--dvz-plane)}
  @media (max-width:820px){.dvz-tiers{grid-template-columns:1fr}.dvz-gate{grid-template-columns:1fr}.dvz-bar{grid-template-columns:150px 1fr auto}}
  `;
}

// Inject the theme CSS variables the viz styles reference (call once; re-call on toggle).
export function applyThemeVars(el) {
  const p = P();
  const root = el || document.documentElement;
  const set = (k, v) => root.style.setProperty(k, v);
  set('--dvz-grid', p.grid); set('--dvz-good', p.good); set('--dvz-crit', p.critical);
  set('--dvz-ring', p.ring); set('--dvz-surface', p.surface); set('--dvz-plane', p.plane);
  set('--dvz-muted', p.muted); set('--dvz-c1', p.cat[0]);
}

// Convenience: re-render on theme change. Pass a callback that redraws all viz.
export function onThemeChange(redraw) {
  const obs = new MutationObserver(() => { applyThemeVars(); redraw(); });
  obs.observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
  matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { applyThemeVars(); redraw(); });
}

export const DrexViz = { ringGraph, crossingCurves, fillBars, certificateViz, tierReveal, styles, applyThemeVars, onThemeChange, currentMode };
export default DrexViz;

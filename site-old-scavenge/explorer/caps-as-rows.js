/**
 * caps-as-rows — the browser twin of the pg-dregg cap-gated query cookbook.
 *
 * "Your capabilities, expressed as the rows you may read." Present a capability
 * (its caveats) and the cell rows narrow exactly as the node's Row-Level-Security
 * gate narrows a `SELECT * FROM dregg.cells`. The decision logic here FAITHFULLY
 * mirrors `dregg_cap_admits` / `dregg-auth::credential::Credential::verify`:
 *
 *   admit(action, resource, now) :=  action caveat (AttrEq)
 *                                AND resource caveat (AttrPrefix)
 *                                AND temporal caveat (NotAfter)
 *                                AND not revoked
 *
 * fail-closed: any unmet caveat ⇒ refused (and the reason names the first
 * violated requirement, exactly as the Refusal Display does in dregg-auth and as
 * `dregg_cap_explain` surfaces it).
 *
 * The DATA is a labeled static snapshot of the live `pg_dregg_mirror` schema:
 * the six seeded cells + the delegation graph from `sql/cookbook-seed.sql`, so
 * this glass and the SQL glass render the identical world. Nothing here bypasses
 * the gate — a filtered row's value is redacted, never shown.
 */

// ---- the snapshot: the live mirror's seeded rows (sql/cookbook-seed.sql) ----
// cell_id (64-hex), balance, lifecycle. These are the exact rows dregg.cells holds.
const CELLS = [
  { id: '5eff91e344090c47234eeceb0f684b2dbc1ffdafc0d5b69fb2427add7020cd86', balance: 20,   lifecycle: 'Live' },
  { id: '5c94568eff15b01d2580e2cce5b739612d9672f0248645fe973c0595847c319e', balance: 15,   lifecycle: 'Live' },
  { id: 'aa00000000000000000000000000000000000000000000000000000000000000', balance: 1000, lifecycle: 'Live' },
  { id: 'bb00000000000000000000000000000000000000000000000000000000000000', balance: 500,  lifecycle: 'Live' },
  { id: 'cc00000000000000000000000000000000000000000000000000000000000000', balance: 250,  lifecycle: 'Live' },
  { id: 'dd00000000000000000000000000000000000000000000000000000000000000', balance: 100,  lifecycle: 'Live' },
];

// the delegation graph (dregg.capabilities → dregg.cap_edges). `amplifies` marks
// the deliberate over-grant the seed plants for recipe 2's audit to catch.
const CAP_EDGES = [
  { holder: 'aa00', target: 'bb00', slot: 0, effects: ['read', 'transfer', 'grant', 'admin'], genesisRoot: true,  amplifies: false },
  { holder: 'bb00', target: 'cc00', slot: 0, effects: ['read', 'transfer'],                   genesisRoot: false, amplifies: false },
  { holder: 'cc00', target: 'dd00', slot: 0, effects: ['read'],                               genesisRoot: false, amplifies: false },
  { holder: 'cc00', target: 'bb00', slot: 1, effects: ['admin'],                              genesisRoot: false, amplifies: true  },
];

// ---- the capability decision (mirrors dregg_cap_admits, fail-closed) --------
// Returns { admitted: bool, reason: string } for one (cap, action, resource).
function capAdmits(cap, action, resourceHex) {
  // revocation (the dregg_cap_not_revoked / dregg_revoke tier): denied outright.
  if (cap.revoked) {
    return { admitted: false, reason: 'refused: credential is revoked' };
  }
  // action caveat (AttrEq on `action`).
  if (cap.action && cap.action !== action) {
    return { admitted: false, reason: `refused: block 0 requires attribute \`action\` = \`${cap.action}\`` };
  }
  // resource caveat (AttrPrefix on `resource`) — the confinement to a namespace.
  if (cap.prefix && !resourceHex.startsWith(cap.prefix)) {
    return { admitted: false, reason: `refused: block 0 requires attribute \`resource\` starts with \`${cap.prefix}\`` };
  }
  // temporal caveat (NotAfter) — present only if the cap carries an expiry.
  if (cap.notAfter != null && nowSeconds() > cap.notAfter) {
    return { admitted: false, reason: `refused: block 0 requires clock <= ${cap.notAfter} (NotAfter)` };
  }
  return { admitted: true, reason: 'allowed' };
}

function nowSeconds() { return Math.floor(Date.now() / 1000); }

// ---- the live cap being presented (read from the form) ----------------------
function readCap() {
  return {
    action: document.getElementById('car-action').value,
    prefix: document.getElementById('car-prefix').value.trim().toLowerCase(),
    revoked: document.getElementById('car-revoked').checked,
    notAfter: null,
  };
}

// ---- render: the caveat readout --------------------------------------------
function renderCaveats(cap) {
  const el = document.getElementById('car-caveats');
  const parts = [
    `<span class="k">action</span> = <span class="v">${esc(cap.action)}</span>`,
    cap.prefix
      ? `<span class="k">resource</span> startsWith <span class="v">${esc(cap.prefix)}</span>`
      : `<span class="k">resource</span> = <span class="v">∗ (no prefix — all)</span>`,
  ];
  if (cap.revoked) parts.push(`<span class="k" style="color:var(--danger)">revoked</span>`);
  el.innerHTML =
    `token caveats &nbsp; { ${parts.join(' &nbsp;∧&nbsp; ')} }<br>` +
    `<span style="color:var(--text-muted)">decision := dregg_cap_admits(token, 'read', cell_id, now) — fail-closed</span>`;
}

// ---- render: the rows (caps-as-rows), gate respected ------------------------
let currentTab = 'admitted';

function renderRows(cap) {
  const action = cap.action;
  const verdicts = CELLS.map((c) => ({ cell: c, ...capAdmits(cap, action, c.id) }));
  const admitted = verdicts.filter((v) => v.admitted);

  // summary
  const sum = document.getElementById('car-summary');
  sum.innerHTML = `
    <div class="car-stat"><span class="big">${admitted.length}</span><span class="lbl">rows admitted</span></div>
    <div class="car-stat filtered"><span class="big">${verdicts.length - admitted.length}</span><span class="lbl">rows filtered (vanished)</span></div>
    <div class="car-stat"><span class="big">${verdicts.length}</span><span class="lbl">rows in dregg.cells</span></div>`;

  // table — in "admitted" tab show only admitted rows (the SELECT a reader sees);
  // in "explain" tab show all rows with the per-row verdict + reason, but a
  // filtered row's VALUE is redacted (the gate is honored visually, never bypassed).
  const show = currentTab === 'admitted' ? admitted : verdicts;
  const body = document.getElementById('car-rows-body');
  document.querySelectorAll('.explain-col').forEach((e) => { e.style.display = currentTab === 'explain' ? '' : 'none'; });

  body.innerHTML = show.map((v) => {
    const cls = v.admitted ? 'admitted' : 'filtered';
    const idShort = v.cell.id.slice(0, 10) + '…';
    const balCell = v.admitted ? v.cell.balance : '— redacted —';
    const lifeCell = v.admitted ? v.cell.lifecycle : '—';
    const pill = v.admitted
      ? '<span class="car-verdict-pill ok">admitted</span>'
      : '<span class="car-verdict-pill no">filtered</span>';
    const reason = currentTab === 'explain'
      ? `<td class="car-reason explain-col">${esc(v.reason)}</td>` : '';
    return `<tr class="${cls}">
      <td title="${v.cell.id}">${idShort}</td>
      <td class="cell-val">${balCell}</td>
      <td class="cell-val">${lifeCell}</td>
      <td class="verdict">${pill}</td>
      ${reason}
    </tr>`;
  }).join('');

  if (show.length === 0) {
    body.innerHTML = `<tr><td colspan="5" style="color:var(--text-muted);padding:1rem .7rem">
      No rows admitted — this capability is confined to a namespace that matches no cell (fail-closed).
    </td></tr>`;
  }
}

// ---- render: the delegation tree (recipe 1) --------------------------------
function renderTree() {
  // walk cap-edges from the genesis root (aa00), cycle-guarded, like the recursive CTE.
  const roots = CAP_EDGES.filter((e) => e.genesisRoot).map((e) => e.holder);
  const out = [];
  const seen = new Set(); // (holder|target|slot) edges the tree walk reached
  function walk(node, depth, path) {
    if (depth > 32) return;
    for (const e of CAP_EDGES) {
      if (e.holder !== node) continue;
      if (path.includes(e.target)) continue; // cycle guard (NOT dst = ANY(path))
      out.push({ depth, ...e, chain: [...path, e.target], inTree: true });
      seen.add(`${e.holder}|${e.target}|${e.slot}`);
      walk(e.target, depth + 1, [...path, e.target]);
    }
  }
  for (const r of roots) walk(r, 1, [r]);

  // append the cap-edges the tree walk did NOT reach (back-edges the cycle guard
  // excluded — exactly where an amplification hides). Recipe 1's tree never
  // follows them; recipe 2's audit is what catches them, so we surface them here
  // flagged, not on the tree path.
  for (const e of CAP_EDGES) {
    const key = `${e.holder}|${e.target}|${e.slot}`;
    if (!seen.has(key)) {
      out.push({ depth: '—', ...e, chain: [`${e.holder} ⤳ ${e.target}`], inTree: false });
    }
  }

  const body = document.getElementById('car-tree-body');
  body.innerHTML = out.map((e) => {
    const eff = e.effects.map((f) => e.amplifies ? `<span style="color:var(--danger)">${f}</span>` : f).join(', ');
    const chain = e.chain.join(' → ');
    const note = e.amplifies
      ? ' <span style="color:var(--danger);font-size:.7rem">⚠ amplifies (back-edge, not on the tree)</span>'
      : (!e.inTree ? ' <span style="color:var(--text-muted);font-size:.7rem">(back-edge)</span>' : '');
    return `<tr class="${e.amplifies ? 'filtered' : 'admitted'}">
      <td>${e.depth}</td><td>${e.holder}</td><td>${e.target}${note}</td>
      <td>${eff}</td><td>${chain}</td></tr>`;
  }).join('');
}

// ---- wiring -----------------------------------------------------------------
function esc(s) { return String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c])); }

function refresh() {
  const cap = readCap();
  renderCaveats(cap);
  renderRows(cap);
}

function syncPresetHighlight() {
  const cap = readCap();
  document.querySelectorAll('.car-preset').forEach((b) => {
    const match = b.dataset.action === cap.action
      && (b.dataset.prefix || '') === cap.prefix
      && Boolean(b.dataset.revoked) === cap.revoked;
    b.classList.toggle('active', match);
  });
}

function boot() {
  // presets
  document.getElementById('car-presets').addEventListener('click', (ev) => {
    const b = ev.target.closest('.car-preset');
    if (!b) return;
    document.getElementById('car-action').value = b.dataset.action;
    document.getElementById('car-prefix').value = b.dataset.prefix || '';
    document.getElementById('car-revoked').checked = Boolean(b.dataset.revoked);
    refresh(); syncPresetHighlight();
  });
  // live form
  ['car-action', 'car-prefix', 'car-revoked'].forEach((id) => {
    const el = document.getElementById(id);
    el.addEventListener('input', () => { refresh(); syncPresetHighlight(); });
    el.addEventListener('change', () => { refresh(); syncPresetHighlight(); });
  });
  // tabs
  document.getElementById('car-tabs').addEventListener('click', (ev) => {
    const b = ev.target.closest('button'); if (!b) return;
    currentTab = b.dataset.tab;
    document.querySelectorAll('#car-tabs button').forEach((x) => x.classList.toggle('active', x === b));
    refresh();
  });

  refresh();
  renderTree();
  syncPresetHighlight();
}

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', boot);
} else {
  boot();
}

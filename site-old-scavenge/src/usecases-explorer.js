// usecases/explorer.js — the real-usecase explorer controller.
//
// Owned by the site-overhaul surface (page-level HTML + usecase explorer).
// It does NOT touch the Studio authoring widgets (_includes/studio/*).
//
// What it does, grounded in the real system:
//   1. Loads each app's manifest.json (the Rust-derived source of truth copied
//      to /starbridge-apps/<id>/manifest.json by build.js).
//   2. Renders slots, state constraints, turn-builders, and host actions.
//   3. "Try it" probes a live node's honest verified-execution surface
//      (/api/node/producer, /api/node/identity) and resolves the seeded cell
//      for the app (/api/cell/{id}). Strictly read-only and strictly honest:
//      it reports exactly what the node returns, or that the node is offline.
//
// No fabricated results. If the node is unreachable, the panel says so.

'use strict';

// ---- node base resolution (mirrors explorer/app.js) ------------------------
const NODE_URL_KEY = 'dregg_node_url';
const DEFAULT_NODE_URL = 'http://localhost:8420';

function defaultNodeUrl() {
  if (typeof window !== 'undefined' && window.location) {
    const { protocol, hostname, origin } = window.location;
    const isLocal = hostname === 'localhost' || hostname === '127.0.0.1' || hostname === '[::1]';
    // On a real deployed host (e.g. devnet behind Caddy) the node API is fronted
    // on the SAME origin under /api, /status. Use it to avoid CORS/mixed-content.
    if (protocol.startsWith('http') && !isLocal) return origin;
  }
  return DEFAULT_NODE_URL;
}
function nodeBase() {
  try { return localStorage.getItem(NODE_URL_KEY) || defaultNodeUrl(); }
  catch { return defaultNodeUrl(); }
}
function setNodeBase(url) {
  try { localStorage.setItem(NODE_URL_KEY, String(url || '').trim()); } catch {}
}

// fetch with a hard timeout — the deployed node can hang; never spin forever.
async function fetchJson(url, { timeout = 9000 } = {}) {
  const ctrl = new AbortController();
  const t = setTimeout(() => ctrl.abort(), timeout);
  try {
    const res = await fetch(url, { headers: { Accept: 'application/json' }, signal: ctrl.signal });
    const text = await res.text();
    let json = null;
    try { json = text ? JSON.parse(text) : null; } catch { /* non-json (e.g. static fallback html) */ }
    return { ok: res.ok, status: res.status, json, text };
  } finally {
    clearTimeout(t);
  }
}

// ---- the apps (ids drive manifest fetch; order drives the catalog) ---------
const APP_IDS = [
  'nameservice',
  'identity',
  'subscription',
  'privacy-voting',
  'bounty-board',
  'governed-namespace',
  'compartment-workflow-mandate',
  'storage-gateway-mandate',
];

// Plain-language "what it does" + the guarantee story per app. Kept here (not in
// the manifest) because it is editorial narrative; the structural facts (slots,
// constraints, builders, actions) all come from the manifest itself.
const NARRATIVE = {
  'nameservice': {
    tagline: 'A federation name directory built from dregg-native primitives.',
    what: 'Register a name, point it at a target cell, renew it before it expires, transfer it, or revoke it. Names live in factory-born cells; the registry is just another cell.',
    guarantee: 'The name hash is WriteOnce so a name binds exactly once and cannot be silently rebound; expiry is Monotonic so renewal can only extend, never shorten; the revoked flag is WriteOnce so revocation is final. A turn that violates any of these is rejected by the executor.',
  },
  'identity': {
    tagline: 'Credential issuance and selective-disclosure presentation.',
    what: 'An issuer issues credentials; a holder presents chosen facts; a verifier checks the presentation; the issuer can revoke. Presentation is a local action — the holder proves "age ≥ 18" without revealing the exact value.',
    guarantee: 'The schema commitment is Immutable, issuance is a MonotonicSequence (no replay), the revocation root only grows, and SenderAuthorized(PublicRoot(...)) means only the registered issuer key may write issuer state.',
  },
  'subscription': {
    tagline: 'A capability-gated bounded ring buffer (pub/sub topic).',
    what: 'The owner grants publisher and consumer capabilities. Publishers push messages; consumers drain them. Capacity is fixed at birth.',
    guarantee: 'Capacity and owner are Immutable; the invariant tail ≤ head is enforced by FieldLteField on every turn; publishing advances the head as a MonotonicSequence and consuming advances the tail, so neither pointer can be rewound to replay or drop messages.',
  },
  'privacy-voting': {
    tagline: 'Factory-born polls with one-vote-per-ballot enforced by the substrate.',
    what: 'Open a poll (a public tally board), mint a ballot cell per voter, cast a vote, close the poll. Ballot cells are minted from a caller-chosen blinding token so a ballot id need not link to the voter’s primary cell.',
    guarantee: 'The question hash and closed flag are WriteOnce; tallies are Monotonic so a vote can never be erased by rewriting a tally downward; each ballot’s vote slot is WriteOnce — a second cast_vote on the same ballot is rejected with a WriteOnce violation. The anti-double-vote rule is the executor’s, not the app’s.',
  },
  'bounty-board': {
    tagline: 'A bounty lifecycle that is a substrate-enforced state machine.',
    what: 'Post a bounty, claim it, submit work, get paid. One factory-born cell carries the whole lifecycle.',
    guarantee: 'State runs OPEN(1) → CLAIMED(2) → SUBMITTED(3) → PAID(4) as a StrictMonotonic slot: you cannot skip backward, cannot re-enter a state, and cannot double-claim. The claimant hash is WriteOnce so the first claimer wins; title and reward are WriteOnce so a reward cannot be silently lowered after a worker commits.',
  },
  'governed-namespace': {
    tagline: 'A DAO-controlled route table and capability service mesh.',
    what: 'Propose a route-table update, vote on it (threshold), commit the update, register services into the table. The table drives DFA-style routing.',
    guarantee: 'The governance committee root and the threshold are Immutable — you cannot quietly change who governs or how many votes are needed. The table version is Monotonic, and committing an update advances the version as a MonotonicSequence so history is append-only.',
  },
  'compartment-workflow-mandate': {
    tagline: 'A DAG workflow under a bounded, clearance-gated mandate.',
    what: 'Initialize a mandate, then advance the workflow one step at a time. Each step is admitted only if the actor’s clearance label dominates the step’s requirement and the spend policy permits it.',
    guarantee: 'The step cursor is a MonotonicSequence that can never pass the charter terminal (FieldLteField(cursor, terminal)); the commitment anchor is Immutable. These slot caveats are the Rust image of the Lean CompartmentWorkflowMandate theorems.',
  },
  'storage-gateway-mandate': {
    tagline: 'A storage gateway operating under a volume ceiling.',
    what: 'Initialize a gateway, then GET / PUT / LIST objects under an authorized key prefix and clearance label. Every operation accrues against a volume budget.',
    guarantee: 'Volume spent is Monotonic and can never exceed the ceiling (FieldLteField(spent, ceiling)); the commitment anchor is Immutable. These caveats are the Rust image of the Lean StorageGatewayMandate theorems.',
  },
};

// Human labels + one-line meanings for the StateConstraint vocabulary, so a
// reader who has never seen dregg can decode a manifest. Pure presentation.
const CONSTRAINT_HELP = [
  ['WriteOnce',         'a slot may be written once, then is frozen forever'],
  ['Immutable',         'a slot is fixed at birth and may never be written'],
  ['Monotonic',         'a slot’s value may only ever increase'],
  ['StrictMonotonic',   'a slot must strictly increase on each write (no re-entry)'],
  ['MonotonicSequence', 'a counter that advances by exactly one, in order'],
  ['FieldLteField',     'one slot must always stay ≤ another (an invariant pair)'],
  ['SenderAuthorized',  'only a sender authorized by a public root may write'],
  ['MethodIs',          'a guard scoping a constraint to one turn method'],
];

function tagFor(constraint) {
  const head = constraint.split('(')[0].split(' ')[0];
  return head;
}

// ---- rendering -------------------------------------------------------------
function el(tag, attrs = {}, ...kids) {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') e.className = v;
    else if (k === 'html') e.innerHTML = v;
    else if (k.startsWith('on') && typeof v === 'function') e.addEventListener(k.slice(2), v);
    else if (v != null) e.setAttribute(k, v);
  }
  for (const kid of kids) {
    if (kid == null) continue;
    e.append(kid.nodeType ? kid : document.createTextNode(String(kid)));
  }
  return e;
}

function renderSlots(manifest) {
  const layout = manifest.slot_layout || {};
  const entries = Object.entries(layout).sort((a, b) => a[1] - b[1]);
  if (!entries.length) return el('p', { class: 'uc-muted' }, 'No fixed slot layout (composite cells).');
  const rows = entries.map(([name, idx]) =>
    el('tr', {},
      el('td', { class: 'uc-slot-idx' }, `#${idx}`),
      el('td', { class: 'uc-mono' }, name),
    ),
  );
  return el('table', { class: 'uc-table' },
    el('thead', {}, el('tr', {}, el('th', {}, 'slot'), el('th', {}, 'name'))),
    el('tbody', {}, ...rows),
  );
}

function renderConstraints(manifest) {
  const cs = manifest.state_constraints || [];
  if (!cs.length) return el('p', { class: 'uc-muted' }, 'No declared slot constraints.');
  return el('ul', { class: 'uc-constraints' },
    ...cs.map((c) => el('li', {},
      el('span', { class: 'uc-pill' }, tagFor(c)),
      el('code', { class: 'uc-mono' }, c),
    )),
  );
}

function renderActions(manifest) {
  const acts = manifest.host_actions || [];
  const builders = manifest.turn_builders || [];
  const list = acts.length
    ? acts.map((a) => el('li', {},
        el('span', { class: `uc-kind uc-kind--${a.kind || 'turn'}` }, a.kind || 'turn'),
        el('span', { class: 'uc-action-label' }, a.label || a.id),
        a.builder ? el('code', { class: 'uc-mono uc-dim' }, a.builder) : null,
      ))
    : builders.map((b) => el('li', {},
        el('span', { class: 'uc-kind uc-kind--turn' }, 'turn'),
        el('code', { class: 'uc-mono' }, b),
      ));
  return el('ul', { class: 'uc-actions' }, ...list);
}

function renderApp(id, manifest) {
  const n = NARRATIVE[id] || {};
  const health = manifest.manifest_health || {};
  const ready = health.status === 'ready' || health.status === 'starbridge-native';
  const sot = health.source_of_truth || (`starbridge-apps/${id}/src/lib.rs`);

  const card = el('article', { class: 'uc-app', id });

  // header
  card.append(el('div', { class: 'uc-app__head' },
    el('div', {},
      el('h2', { class: 'uc-app__title' }, manifest.name || id),
      el('p', { class: 'uc-app__tagline' }, n.tagline || manifest.description || ''),
    ),
    el('span', { class: `uc-status uc-status--${ready ? 'ready' : 'stub'}` },
      ready ? 'real · tested' : (health.status || 'stub')),
  ));

  // what + guarantee
  const body = el('div', { class: 'uc-app__body' });
  if (n.what) body.append(el('p', { class: 'uc-app__what' }, n.what));
  if (n.guarantee) {
    body.append(el('p', { class: 'uc-guarantee' },
      el('strong', {}, 'Substrate-enforced: '),
      n.guarantee));
  }
  card.append(body);

  // grid: slots | constraints | flow
  const grid = el('div', { class: 'uc-grid' });
  grid.append(el('section', { class: 'uc-panel' }, el('h3', {}, 'Cell slots'), renderSlots(manifest)));
  grid.append(el('section', { class: 'uc-panel' }, el('h3', {}, 'State constraints'), renderConstraints(manifest)));
  grid.append(el('section', { class: 'uc-panel' }, el('h3', {}, 'Turns & actions'), renderActions(manifest)));
  card.append(grid);

  // try-it
  const seedCell = (manifest.host_actions || []).find((a) => a.kind === 'inspect' && a.uri)?.uri
    || (manifest.host_controls || []).find((c) => c.type === 'uri')?.default
    || null;
  card.append(renderTryIt(id, manifest, seedCell));

  // footer: source of truth + page link
  const foot = el('div', { class: 'uc-app__foot' });
  foot.append(el('span', { class: 'uc-dim' }, 'source of truth: '), el('code', { class: 'uc-mono' }, sot));
  if (manifest.page) {
    foot.append(el('a', { class: 'uc-applink', href: manifest.page }, 'open app surface →'));
  }
  card.append(foot);

  return card;
}

// ---- live try-it -----------------------------------------------------------
function uriToCellId(uri) {
  // dregg://cell/<id> — pass <id> straight to /api/cell/{id}. The seeded
  // default ids are symbolic (e.g. "registry-default"); the node resolves them.
  if (!uri) return null;
  const m = /^dregg:\/\/cell\/(.+)$/.exec(uri.trim());
  return m ? m[1] : null;
}

function renderTryIt(id, manifest, seedCellUri) {
  const wrap = el('details', { class: 'uc-tryit' });
  wrap.append(el('summary', {}, 'Try it against a node'));

  const cellId = uriToCellId(seedCellUri);
  const intro = el('p', { class: 'uc-dim uc-tryit__intro' },
    'Read-only. Probes the node’s verified-execution surface and resolves this app’s seeded cell. ',
    'It reports exactly what the node returns — nothing is faked.');
  wrap.append(intro);

  const out = el('div', { class: 'uc-tryit__out' });
  const btn = el('button', { class: 'uc-btn', type: 'button' }, 'Probe ' + (cellId ? `cell ${cellId}` : 'node'));
  btn.addEventListener('click', () => runProbe(out, btn, cellId));
  wrap.append(el('div', { class: 'uc-tryit__bar' }, btn,
    el('span', { class: 'uc-dim uc-mono uc-tryit__node' }, '→ ' + nodeBase())));
  wrap.append(out);
  return wrap;
}

function statusLine(label, kind, text) {
  return el('div', { class: `uc-line uc-line--${kind}` },
    el('span', { class: 'uc-line__dot' }), el('strong', {}, label + ': '), text);
}

async function runProbe(out, btn, cellId) {
  out.replaceChildren();
  btn.disabled = true;
  const base = nodeBase();
  out.append(el('p', { class: 'uc-dim' }, `Querying ${base} …`));

  // 1) producer status — the honest verified-execution surface.
  let producerOk = false;
  try {
    const r = await fetchJson(`${base}/api/node/producer`);
    out.replaceChildren();
    if (r.ok && r.json && typeof r.json.state_producer === 'string') {
      producerOk = true;
      const p = r.json;
      out.append(statusLine('producer', p.lean_producer_enabled ? 'ok' : 'warn',
        `${p.state_producer} (${p.covered_effects?.length ?? '?'} verified-covered effect kinds of ${p.total_effect_kinds ?? '?'}; full-turn proving ${p.full_turn_proving ? 'ON' : 'off'})`));
      if (p.summary) out.append(el('p', { class: 'uc-dim uc-summary' }, p.summary));
    } else {
      out.append(statusLine('node', 'err',
        `reachable but no verified-execution JSON (HTTP ${r.status}). The node API may be down behind the proxy.`));
    }
  } catch (e) {
    out.replaceChildren();
    out.append(statusLine('node', 'err',
      `unreachable: ${e?.name === 'AbortError' ? 'timed out' : (e?.message || e)}. ` +
      `Set a node URL below, or run one locally (cargo run -p dregg-node -- run).`));
  }

  // 2) seeded cell resolution (only meaningful if the node answered).
  if (producerOk && cellId) {
    try {
      const r = await fetchJson(`${base}/api/cell/${encodeURIComponent(cellId)}`);
      if (r.ok && r.json) {
        const j = r.json;
        const bits = [];
        if (j.balance != null) bits.push(`balance ${j.balance}`);
        if (j.nonce != null) bits.push(`nonce ${j.nonce}`);
        const idShown = j.id || j.cell_id || cellId;
        out.append(statusLine('seed cell', 'ok',
          `${idShown}${bits.length ? ' — ' + bits.join(', ') : ' resolved'}`));
      } else {
        const why = r.status === 0
          ? 'the node did not answer the cell lookup (it may only resolve hex cell ids, or the route is down)'
          : `the node returned no cell JSON (HTTP ${r.status})`;
        out.append(statusLine('seed cell', 'warn', `${cellId}: ${why}.`));
      }
    } catch (e) {
      out.append(statusLine('seed cell', 'warn', `${cellId}: ${e?.message || e}`));
    }
  }

  // node URL control
  out.append(renderNodeControl(out, btn, cellId));
  btn.disabled = false;
}

function renderNodeControl(out, btn, cellId) {
  const row = el('div', { class: 'uc-nodectl' });
  const input = el('input', { type: 'text', class: 'uc-input uc-mono',
    value: nodeBase(), placeholder: 'http://localhost:8420' });
  const save = el('button', { class: 'uc-btn uc-btn--ghost', type: 'button' }, 'use this node');
  save.addEventListener('click', () => { setNodeBase(input.value); runProbe(out, btn, cellId); });
  row.append(el('label', { class: 'uc-dim' }, 'node URL'), input, save);
  return row;
}

// ---- boot ------------------------------------------------------------------
async function loadManifest(id) {
  try {
    const r = await fetchJson(`/starbridge-apps/${id}/manifest.json`, { timeout: 6000 });
    if (r.ok && r.json) return r.json;
  } catch { /* fall through */ }
  return null;
}

async function boot() {
  const root = document.getElementById('uc-apps');
  if (!root) return;
  root.replaceChildren(el('p', { class: 'uc-dim' }, 'Loading app manifests …'));

  const manifests = await Promise.all(APP_IDS.map(loadManifest));
  root.replaceChildren();

  let rendered = 0;
  APP_IDS.forEach((id, i) => {
    const m = manifests[i];
    if (!m) {
      root.append(el('article', { class: 'uc-app uc-app--missing', id },
        el('h2', { class: 'uc-app__title' }, id),
        el('p', { class: 'uc-muted' }, `manifest not found at /starbridge-apps/${id}/manifest.json`)));
      return;
    }
    root.append(renderApp(id, m));
    rendered += 1;
  });

  // honest global node-status banner
  const banner = document.getElementById('uc-node-banner');
  if (banner) {
    fetchJson(`${nodeBase()}/api/node/producer`).then((r) => {
      if (r.ok && r.json && r.json.state_producer) {
        banner.className = 'uc-banner uc-banner--ok';
        banner.textContent = `Node reachable at ${nodeBase()} — producer: ${r.json.state_producer}, ${r.json.covered_effects?.length ?? '?'} verified-covered effects.`;
      } else {
        banner.className = 'uc-banner uc-banner--warn';
        banner.textContent = `Node API at ${nodeBase()} did not return verified-execution JSON. Try-it panels will report it offline; the structural views below are static and always work.`;
      }
    }).catch(() => {
      banner.className = 'uc-banner uc-banner--warn';
      banner.textContent = `No node reachable at ${nodeBase()}. The try-it panels will say so; everything else on this page is static and works offline.`;
    });
  }

  // deep-link: if the URL has a #fragment, scroll to it after render
  if (location.hash) {
    const t = document.getElementById(location.hash.slice(1));
    if (t) t.scrollIntoView({ behavior: 'smooth', block: 'start' });
  }
}

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', boot);
} else {
  boot();
}

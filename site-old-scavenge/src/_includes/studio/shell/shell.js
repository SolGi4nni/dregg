/**
 * shell.js — the Starbridge shell: boot into your polis.
 *
 * ONE persistent frame (the left rail: identity · places · your cells · the
 * receipt stream) around ONE mount. Places render inside the frame — same
 * identity, same stream, no full-page resets:
 *
 *   #/home                  your cells + recent receipts + the places
 *   #/place/<app-id>        an app place (embedded starbridge-app frame)
 *   #/inspect/<dregg-uri>   any object, mounted on the shared inspectors
 *
 * Boot sequence: connect (node probe) → identity (create / import / guest)
 * → home. Deep links: ?at=<dregg-uri> opens the inspect mount (the URL shape
 * the app surfaces emit).
 *
 * Object data flows through the shared remote runtime (runtime-remote.js);
 * the live receipt stream through node-link.js (SSE with poll fallback).
 * Identity is identity.js; the command affordance is palette.js (⌘K).
 */

import { parseRef, isRef } from '../uri.js';
import '../context.js';
import '../inspectors.js';
import { createRemoteRuntime } from '../runtime-remote.js';
import { PLACES, EXPERIMENTS, TOOLS, placeById } from './places.js';
import {
  loadProfiles, activeProfile, setActiveProfile, createProfile, generatePhrase, claimFaucet,
} from './identity.js';
import { createNodeLink, resolveNodeUrl, saveNodeUrl, DEFAULT_NODE } from './node-link.js';
import { createPalette } from './palette.js';

function whenDregg() {
  return new Promise((resolve) => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', (e) => resolve(e.detail), { once: true });
  });
}

const $ = (id) => document.getElementById(id);

function esc(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

function shortHex(s, n = 8) {
  const v = String(s || '');
  return v.length > n * 2 + 1 ? `${v.slice(0, n)}…${v.slice(-4)}` : v;
}

/**
 * The operational ORGANS (docs/ORGANS.md) — the live cell surfaces the node
 * serves. Each is a dregg:// kind with a registered inspector that reads its
 * node-side status route. The rail offers them as entry points: you supply
 * the organ's id (the cell / strand / owner key) and the shell mounts the
 * organ inspector on the shared inspect surface.
 */
const ORGANS = [
  { kind: 'trustline', label: 'Trustlines', prompt: 'trustline cell id (hex)',
    what: 'a bilateral line of credit — draws debit a shared counter (ORGANS §1)' },
  { kind: 'channel', label: 'Channels', prompt: 'channel (group) cell id (hex)',
    what: 'an encrypted group as a cell — the epochs-unified keystone (ORGANS §4)' },
  { kind: 'mailbox', label: 'Mailboxes', prompt: 'inbox owner public key (hex)',
    what: 'a hosted inbox over the relay, drained with a custody proof (ORGANS §2)' },
  { kind: 'court', label: 'Court', prompt: 'strand public key (hex)',
    what: 'the equivocation court — a bond admits, a proof slashes (ORGANS §3)' },
];

(async function main() {
  const ui = await whenDregg();

  const bootEl = $('shl-boot');
  const bootBody = $('shl-boot-body');
  const railIdentity = $('shl-identity');
  const railPlaces = $('shl-places');
  const railCells = $('shl-cells');
  const railStream = $('shl-stream');
  const railNode = $('shl-node');
  const mount = $('shl-mount');
  const appEl = $('shl-app');
  const shellRoot = document.querySelector('.shl');

  // ---------------------------------------------------------------------------
  // Node link + shared runtime.
  // ---------------------------------------------------------------------------
  const nodeUrl = resolveNodeUrl();
  const link = createNodeLink(nodeUrl);
  let runtime = null;
  let profile = activeProfile();

  // An explicit "continue as guest" persists; otherwise a keyless visitor
  // meets the identity stage on every boot.
  const GUEST_KEY = 'starbridge.shell.guest.v1';
  const guestChosen = () => {
    try { return localStorage.getItem(GUEST_KEY) === '1'; } catch { return false; }
  };
  const setGuestChosen = (v) => {
    try {
      if (v) localStorage.setItem(GUEST_KEY, '1');
      else localStorage.removeItem(GUEST_KEY);
    } catch {}
  };

  function watchedCells() {
    try {
      const list = JSON.parse(localStorage.getItem('starbridge.shell.watched.v1') || '[]');
      return Array.isArray(list) ? list.filter((c) => /^[0-9a-f]{64}$/i.test(c)) : [];
    } catch { return []; }
  }
  function watchCell(id) {
    const list = watchedCells();
    if (!list.includes(id)) list.unshift(id);
    try { localStorage.setItem('starbridge.shell.watched.v1', JSON.stringify(list.slice(0, 12))); } catch {}
    renderCells();
  }
  function unwatchCell(id) {
    try {
      localStorage.setItem('starbridge.shell.watched.v1', JSON.stringify(watchedCells().filter((c) => c !== id)));
    } catch {}
    renderCells();
  }

  function myCellIds() {
    const ids = [];
    if (profile?.cellId) ids.push(profile.cellId);
    for (const c of watchedCells()) if (!ids.includes(c)) ids.push(c);
    return ids;
  }

  // ---------------------------------------------------------------------------
  // Rail: identity card.
  // ---------------------------------------------------------------------------
  function renderIdentity() {
    if (!railIdentity) return;
    if (!profile) {
      railIdentity.innerHTML = `
        <div class="shl-id shl-id--guest">
          <span class="shl-id__name">guest</span>
          <span class="shl-id__detail">read-only — no key in this browser</span>
          <button type="button" class="shl-btn" data-act="identity">Create identity</button>
        </div>`;
    } else {
      railIdentity.innerHTML = `
        <div class="shl-id">
          <span class="shl-id__name">${esc(profile.name)}</span>
          <span class="shl-id__detail" title="${esc(profile.publicKeyHex)}">key ${esc(shortHex(profile.publicKeyHex))}</span>
          <span class="shl-id__detail">
            <a href="#/inspect/${encodeURIComponent(`dregg://cell/${profile.cellId}`)}"
               title="${esc(profile.cellId)}">cell ${esc(shortHex(profile.cellId))}</a>
            <button type="button" class="shl-mini" data-act="copy-cell" title="Copy cell id">copy</button>
          </span>
          <div class="shl-id__actions">
            <button type="button" class="shl-mini" data-act="faucet">claim faucet</button>
            <button type="button" class="shl-mini" data-act="identity">switch</button>
          </div>
          <span class="shl-id__note" data-id-note hidden></span>
        </div>`;
    }
    railIdentity.querySelector('[data-act="identity"]')?.addEventListener('click', () => showBoot('identity'));
    railIdentity.querySelector('[data-act="copy-cell"]')?.addEventListener('click', () => ui.copy(profile.cellId));
    railIdentity.querySelector('[data-act="faucet"]')?.addEventListener('click', () => runFaucet());
  }

  async function runFaucet() {
    if (!profile) return showBoot('identity');
    const note = railIdentity.querySelector('[data-id-note]');
    if (note) { note.hidden = false; note.textContent = 'asking the faucet…'; }
    const res = await claimFaucet(link.base, profile, 1000);
    if (note) {
      note.textContent = res.ok
        ? `faucet sent ${res.amount} computrons (turn ${shortHex(res.turnHash || '', 6)})`
        : res.error;
    }
    if (res.ok) ui.toast(`faucet: +${res.amount} computrons`, 'info');
  }

  // ---------------------------------------------------------------------------
  // Rail: places nav.
  // ---------------------------------------------------------------------------
  function navRow(href, label, hint, current) {
    return `<a class="shl-nav__row${current ? ' is-current' : ''}" href="${esc(href)}"
              ${current ? 'aria-current="page"' : ''} title="${esc(hint || '')}">${esc(label)}</a>`;
  }

  function renderPlaces() {
    if (!railPlaces) return;
    const route = currentRoute();
    const placeRows = PLACES.map((p) =>
      navRow(`#/place/${p.id}`, p.label, p.what, route.kind === 'place' && route.id === p.id)).join('');
    const expRows = EXPERIMENTS.map((p) =>
      navRow(`#/place/${p.id}`, p.label, p.what, route.kind === 'place' && route.id === p.id)).join('');
    const toolRows = TOOLS.map((t) =>
      `<a class="shl-nav__row" href="${esc(t.href)}" title="${esc(t.what)}">${esc(t.label)} <span class="shl-nav__ext">↗</span></a>`).join('');
    const organRows = ORGANS.map((o) =>
      `<button type="button" class="shl-nav__row shl-nav__row--btn" data-organ="${esc(o.kind)}"
               title="${esc(o.what)}">${esc(o.label)}</button>`).join('');
    railPlaces.innerHTML = `
      ${navRow('#/home', 'Home', 'your cells, your receipts, the places', route.kind === 'home')}
      <div class="shl-nav__group">Places</div>
      ${placeRows}
      <details class="shl-nav__drawer">
        <summary>Experiments</summary>
        ${expRows}
      </details>
      <div class="shl-nav__group" title="The operational organs of your polis — the live cell surfaces the node serves.">Organs</div>
      ${organRows}
      <div class="shl-nav__group">Tools</div>
      ${toolRows}
      <button type="button" class="shl-nav__row shl-nav__row--btn" data-act="palette"
              title="Jump anywhere (⌘K / ctrl-K)">Command palette <kbd>⌘K</kbd></button>`;
    railPlaces.querySelector('[data-act="palette"]')?.addEventListener('click', () => palette.open());
    for (const btn of railPlaces.querySelectorAll('[data-organ]')) {
      btn.addEventListener('click', () => openOrgan(btn.dataset.organ));
    }
  }

  // ---------------------------------------------------------------------------
  // Rail: your cells (live balances via the shared runtime's cell signals).
  // ---------------------------------------------------------------------------
  let cellsEffectDispose = null;
  function renderCells() {
    if (!railCells) return;
    if (cellsEffectDispose) { cellsEffectDispose(); cellsEffectDispose = null; }
    const ids = myCellIds();
    if (!ids.length) {
      railCells.innerHTML = '<div class="shl-empty">no cells yet — create an identity</div>';
      return;
    }
    if (!runtime) {
      railCells.innerHTML = '<div class="shl-empty">node not connected</div>';
      return;
    }
    const signals = ids.map((id) => runtime.getCell(id));
    cellsEffectDispose = ui.effect(() => {
      const rows = ids.map((id, i) => {
        const c = signals[i].value;
        const mine = profile && id === profile.cellId;
        const meta = c
          ? `${String(c.balance ?? '—')} · nonce ${String(c.nonce ?? '—')}${(c.has_program || (c.program && c.program.kind !== 'None')) ? ' · program' : ''}`
          : 'not in the ledger yet';
        return `
          <a class="shl-cell" href="#/inspect/${encodeURIComponent(`dregg://cell/${id}`)}" title="${esc(id)}">
            <span class="shl-cell__id">${mine ? '● ' : ''}${esc(shortHex(id))}</span>
            <span class="shl-cell__meta">${esc(meta)}</span>
          </a>
          ${mine ? '' : `<button type="button" class="shl-mini shl-cell__unwatch" data-unwatch="${esc(id)}" title="Stop watching">×</button>`}`;
      }).join('');
      railCells.innerHTML = rows;
      for (const btn of railCells.querySelectorAll('[data-unwatch]')) {
        btn.addEventListener('click', () => unwatchCell(btn.dataset.unwatch));
      }
    });
    disposers.push(cellsEffectDispose);
  }

  // ---------------------------------------------------------------------------
  // Rail: the receipt stream (live region).
  // ---------------------------------------------------------------------------
  function renderStream() {
    if (!railStream) return;
    const { events, streamMode } = link.state;
    const mode = streamMode === 'sse' ? 'live · sse'
      : streamMode === 'poll' ? 'polling'
        : 'no events reachable';
    const rows = events.slice(0, 18).map((ev) => {
      const kind = ev.kinds[0] || (ev.finality ? `commit · ${ev.finality}` : 'commit');
      const when = ev.timestamp ? new Date(ev.timestamp * 1000).toLocaleTimeString() : '';
      return `
        <a class="shl-ev" href="#/inspect/${encodeURIComponent(`dregg://receipt/${ev.turnHash}`)}" title="${esc(ev.turnHash)}">
          <span class="shl-ev__kind">${esc(kind)}</span>
          <span class="shl-ev__meta">h${ev.height}${ev.hasProof ? ' · proof' : ''} ${esc(when)}</span>
        </a>`;
    }).join('');
    railStream.innerHTML = `
      <div class="shl-stream__mode" data-mode="${esc(streamMode)}">${esc(mode)}</div>
      ${rows || '<div class="shl-empty">no receipts seen yet</div>'}`;
  }

  function renderNode() {
    if (!railNode) return;
    const { ok, height, error } = link.state;
    const host = (() => { try { return new URL(link.base).host; } catch { return link.base; } })();
    railNode.innerHTML = `
      <span class="shl-node__dot" data-ok="${ok ? 'true' : 'false'}"></span>
      <span class="shl-node__host" title="${esc(link.base)}${error ? ` — ${esc(error)}` : ''}">${esc(host)}</span>
      <span class="shl-node__height">${ok ? `h${height}` : 'offline'}</span>
      <button type="button" class="shl-mini" data-act="node" title="Change node">change</button>`;
    railNode.querySelector('[data-act="node"]')?.addEventListener('click', () => showBoot('connect'));
  }

  link.onChange(() => { renderStream(); renderNode(); });

  // ---------------------------------------------------------------------------
  // Routes + mounts.
  // ---------------------------------------------------------------------------
  function currentRoute() {
    const h = window.location.hash || '#/home';
    let m = /^#\/place\/([a-z0-9-]+)$/i.exec(h);
    if (m) return { kind: 'place', id: m[1] };
    m = /^#\/inspect\/(.+)$/.exec(h);
    if (m) return { kind: 'inspect', uri: decodeURIComponent(m[1]) };
    return { kind: 'home' };
  }

  function goInspect(uri) {
    window.location.hash = `#/inspect/${encodeURIComponent(uri)}`;
  }

  // Open an organ inspector by id. Organs are keyed by a cell/strand/owner
  // hex id you supply; the shell mounts the registered organ inspector, which
  // reads the live node-side status. (A profile's own cell is offered as the
  // default for a trustline holder; otherwise prompt.)
  function openOrgan(kind) {
    const organ = ORGANS.find((o) => o.kind === kind);
    if (!organ) return;
    const id = (window.prompt(`Open ${organ.label} — ${organ.prompt}:`, '') || '').trim().toLowerCase();
    if (!id) return;
    if (!/^[0-9a-f]{64}$/.test(id)) {
      ui.toast('expected a 64-char hex id', 'warn');
      return;
    }
    goInspect(`dregg://${kind}/${id}`);
  }

  function mountHome() {
    const placeCards = PLACES.map((p) => `
      <a class="shl-card" href="#/place/${p.id}">
        <span class="shl-card__glyph">${esc(p.glyph)}</span>
        <strong>${esc(p.label)}</strong>
        <span>${esc(p.what)}</span>
      </a>`).join('');
    const toolCards = TOOLS.map((t) => `
      <a class="shl-card shl-card--tool" href="${esc(t.href)}">
        <strong>${esc(t.label)} ↗</strong>
        <span>${esc(t.what)}</span>
      </a>`).join('');
    const identityBlock = profile
      ? `<p class="shl-home__lede">You are <strong>${esc(profile.name)}</strong> on
           <code>${esc((() => { try { return new URL(link.base).host; } catch { return link.base; } })())}</code>.
           Your hosted cell is
           <a href="#/inspect/${encodeURIComponent(`dregg://cell/${profile.cellId}`)}"><code>${esc(shortHex(profile.cellId, 10))}</code></a>.</p>`
      : `<p class="shl-home__lede">You are browsing as a <strong>guest</strong> — every place is
           read-only until an identity exists in this browser.
           <button type="button" class="shl-btn" data-act="identity">Create identity</button></p>`;
    const organCards = ORGANS.map((o) => `
      <button type="button" class="shl-card shl-card--organ" data-organ="${esc(o.kind)}">
        <strong>${esc(o.label)}</strong>
        <span>${esc(o.what)}</span>
      </button>`).join('');
    mount.innerHTML = `
      <div class="shl-home">
        ${identityBlock}
        <h2 class="shl-home__h">Places</h2>
        <div class="shl-home__grid">${placeCards}</div>
        <h2 class="shl-home__h" title="The operational organs of your polis — live cell surfaces the node serves.">Organs</h2>
        <p class="shl-home__sub">The cell/agent/receipt machinery your polis runs on. Open one by its
          id to read its live node-side status.</p>
        <div class="shl-home__grid shl-home__grid--organs">${organCards}</div>
        <h2 class="shl-home__h">Tools</h2>
        <div class="shl-home__grid shl-home__grid--tools">${toolCards}</div>
        <p class="shl-home__note">The receipt stream on the left is this node's commit feed;
          every entry is a receipt you can open. ⌘K jumps anywhere.</p>
      </div>`;
    mount.querySelector('[data-act="identity"]')?.addEventListener('click', () => showBoot('identity'));
    for (const btn of mount.querySelectorAll('[data-organ]')) {
      btn.addEventListener('click', () => openOrgan(btn.dataset.organ));
    }
  }

  function mountPlace(id) {
    const place = placeById(id);
    if (!place) { mountHome(); return; }
    const src = `${place.page}?embedded=1&runtime=in-memory`;
    mount.innerHTML = `
      <div class="shl-place">
        <header class="shl-place__head">
          <div>
            <strong>${esc(place.label)}</strong>
            <span>${esc(place.what)}</span>
          </div>
          <div class="shl-place__actions">
            <span class="shl-place__runtime" title="The app frame runs its own in-browser wasm runtime; turns it executes are real but local to the frame unless submitted through a signer.">in-frame sandbox runtime</span>
            <a class="shl-mini" href="${esc(place.page)}" target="_blank" rel="noopener">pop out ↗</a>
          </div>
        </header>
        <iframe class="shl-place__frame" title="${esc(place.label)}" src="${esc(src)}"></iframe>
      </div>`;
  }

  const INSPECTOR_ALIASES = { token: 'attenuated-token', queue: 'programmable-queue' };

  function mountInspect(uri) {
    let parsed = null;
    try { parsed = parseRef(uri); } catch {}
    if (!parsed) {
      mount.innerHTML = `<div class="shl-empty shl-empty--pad">not a dregg:// ref: <code>${esc(uri)}</code></div>`;
      return;
    }
    const kind = INSPECTOR_ALIASES[parsed.kind] || parsed.kind;
    const tag = `dregg-${kind}`;
    mount.innerHTML = `
      <div class="shl-inspect">
        <header class="shl-inspect__head">
          <code title="${esc(uri)}">${esc(uri)}</code>
          <div>
            <button type="button" class="shl-mini" data-act="copy">copy uri</button>
            ${parsed.kind === 'cell' && (!profile || parsed.id !== profile.cellId)
              ? '<button type="button" class="shl-mini" data-act="watch">add to my cells</button>' : ''}
            <a class="shl-mini" href="/explorer/?at=${encodeURIComponent(uri)}">explorer ↗</a>
          </div>
        </header>
        <div class="shl-inspect__body"></div>
      </div>`;
    mount.querySelector('[data-act="copy"]')?.addEventListener('click', () => ui.copy(uri));
    mount.querySelector('[data-act="watch"]')?.addEventListener('click', () => watchCell(parsed.id.toLowerCase()));
    const body = mount.querySelector('.shl-inspect__body');
    if (!customElements.get(tag)) {
      body.innerHTML = `<div class="shl-empty shl-empty--pad">no inspector registered for kind “${esc(parsed.kind)}” —
        open it in the <a href="/starbridge/workbench.html?at=${encodeURIComponent(uri)}">workbench</a>.</div>`;
      return;
    }
    const el = document.createElement(tag);
    el.setAttribute('uri', kind === parsed.kind ? uri : `dregg://${kind}/${parsed.id}`);
    body.appendChild(el);
  }

  function route() {
    const r = currentRoute();
    if (r.kind === 'place') mountPlace(r.id);
    else if (r.kind === 'inspect') mountInspect(r.uri);
    else mountHome();
    renderPlaces();
  }
  window.addEventListener('hashchange', route);

  // In-page dregg:navigate (inspector link clicks) stays inside the shell.
  document.addEventListener('dregg:navigate', (e) => {
    const uri = e.detail?.uri;
    if (!uri || !isRef(uri)) return;
    e.preventDefault();
    goInspect(uri);
  });

  // ---------------------------------------------------------------------------
  // Command palette.
  // ---------------------------------------------------------------------------
  const palette = createPalette({
    root: document.body,
    onRun: (cmd) => { if (cmd.kind === 'inspect') goInspect(cmd.uri); },
    getItems: () => {
      const items = [];
      items.push({ label: 'Home', hint: 'your cells + the places', run: () => { window.location.hash = '#/home'; } });
      for (const p of [...PLACES, ...EXPERIMENTS]) {
        items.push({ label: p.label, hint: p.what, keywords: `place app ${p.id}`, run: () => { window.location.hash = `#/place/${p.id}`; } });
      }
      for (const t of TOOLS) {
        items.push({ label: t.label, hint: t.what, keywords: 'tool', run: () => { window.location.href = t.href; } });
      }
      for (const o of ORGANS) {
        items.push({ label: `Open ${o.label}`, hint: o.what, keywords: `organ ${o.kind}`, run: () => openOrgan(o.kind) });
      }
      if (profile) {
        items.push({ label: 'Copy my cell id', hint: shortHex(profile.cellId), run: () => ui.copy(profile.cellId) });
        items.push({ label: 'Copy my public key', hint: shortHex(profile.publicKeyHex), run: () => ui.copy(profile.publicKeyHex) });
        items.push({ label: 'Claim faucet', hint: 'devnet computrons for your cell', run: () => runFaucet() });
        items.push({ label: 'My cell', hint: 'inspect your hosted cell', run: () => goInspect(`dregg://cell/${profile.cellId}`) });
      }
      items.push({ label: profile ? 'Switch identity' : 'Create identity', hint: 'profiles in this browser', run: () => showBoot('identity') });
      items.push({ label: 'Change node', hint: link.base, run: () => showBoot('connect') });
      for (const id of watchedCells()) {
        items.push({ label: `cell ${shortHex(id)}`, hint: 'watched cell', keywords: id, run: () => goInspect(`dregg://cell/${id}`) });
      }
      for (const ev of link.state.events.slice(0, 8)) {
        items.push({
          label: `receipt ${shortHex(ev.turnHash, 6)}`,
          hint: `${ev.kinds[0] || 'commit'} · h${ev.height}`,
          keywords: ev.turnHash,
          run: () => goInspect(`dregg://receipt/${ev.turnHash}`),
        });
      }
      return items;
    },
  });

  // ---------------------------------------------------------------------------
  // Boot overlay: connect → identity → home.
  // ---------------------------------------------------------------------------
  function hideBoot() {
    if (bootEl) bootEl.hidden = true;
    if (shellRoot) shellRoot.dataset.booted = 'true';
  }

  function showBoot(stage) {
    if (!bootEl || !bootBody) return;
    bootEl.hidden = false;
    if (stage === 'connect') renderConnectStage();
    else renderIdentityStage();
  }

  function renderConnectStage() {
    const { ok, height, error } = link.state;
    bootBody.innerHTML = `
      <h2>Connect</h2>
      <p class="shl-boot__what">The shell is a frame over one node — your polis. Status, cells,
        and the receipt stream all come from it.</p>
      <label class="shl-boot__field">node URL
        <input type="url" id="shl-boot-node" value="${esc(link.base)}" spellcheck="false" autocomplete="off">
      </label>
      <div class="shl-boot__status" data-ok="${ok ? 'true' : 'false'}">
        ${ok ? `reachable — height ${height}` : `unreachable${error ? ` (${esc(error)})` : ''}`}
      </div>
      <div class="shl-boot__actions">
        <button type="button" class="shl-btn" data-act="use">Use this node</button>
        <button type="button" class="shl-mini" data-act="devnet">devnet default</button>
        <button type="button" class="shl-mini" data-act="skip">continue anyway</button>
      </div>`;
    bootBody.querySelector('[data-act="use"]')?.addEventListener('click', () => {
      const url = bootBody.querySelector('#shl-boot-node')?.value.trim();
      if (url && url !== link.base) {
        saveNodeUrl(url);
        const q = new URLSearchParams(window.location.search);
        q.delete('node');
        window.location.search = q.toString(); // full reload onto the new node
        return;
      }
      afterConnect();
    });
    bootBody.querySelector('[data-act="devnet"]')?.addEventListener('click', () => {
      const input = bootBody.querySelector('#shl-boot-node');
      if (input) input.value = DEFAULT_NODE;
    });
    bootBody.querySelector('[data-act="skip"]')?.addEventListener('click', () => afterConnect());
  }

  function afterConnect() {
    if (!profile && !guestChosen()) renderIdentityStage();
    else { hideBoot(); route(); renderAllRail(); }
  }

  function renderIdentityStage() {
    const profiles = loadProfiles();
    const existing = profiles.map((p) => `
      <button type="button" class="shl-boot__profile" data-profile="${esc(p.id)}">
        <strong>${esc(p.name)}</strong>
        <span>cell ${esc(shortHex(p.cellId))}</span>
      </button>`).join('');
    bootBody.innerHTML = `
      <h2>Identity</h2>
      <p class="shl-boot__what">A profile is a keypair in this browser: a 24-word phrase derives
        an Ed25519 key, and the key derives your hosted cell id. The phrase is stored
        <strong>unencrypted in localStorage</strong> — devnet custody, not real custody
        (real custody is the Cipherclerk extension).</p>
      ${existing ? `<div class="shl-boot__profiles">${existing}</div>` : ''}
      <div class="shl-boot__actions">
        <button type="button" class="shl-btn" data-act="create">New identity</button>
        <button type="button" class="shl-mini" data-act="import">import phrase</button>
        <button type="button" class="shl-mini" data-act="guest">continue as guest</button>
      </div>
      <form class="shl-boot__form" data-form hidden>
        <label class="shl-boot__field">name
          <input type="text" name="name" placeholder="ember" autocomplete="off" spellcheck="false">
        </label>
        <label class="shl-boot__field" data-phrase-field>recovery phrase
          <textarea name="phrase" rows="3" spellcheck="false" autocomplete="off"></textarea>
        </label>
        <p class="shl-boot__warn" data-phrase-warn hidden>Write the phrase down — it IS the key.
          Anyone holding it holds the cell.</p>
        <div class="shl-boot__actions">
          <button type="submit" class="shl-btn">Enter the polis</button>
          <span class="shl-boot__err" data-err></span>
        </div>
      </form>`;
    const form = bootBody.querySelector('[data-form]');
    const phraseEl = form.querySelector('[name="phrase"]');
    const errEl = form.querySelector('[data-err]');
    for (const btn of bootBody.querySelectorAll('[data-profile]')) {
      btn.addEventListener('click', () => {
        setActiveProfile(btn.dataset.profile);
        profile = activeProfile();
        setGuestChosen(false);
        hideBoot(); route(); renderAllRail();
      });
    }
    bootBody.querySelector('[data-act="create"]')?.addEventListener('click', () => {
      form.hidden = false;
      phraseEl.value = generatePhrase();
      phraseEl.readOnly = true;
      form.querySelector('[data-phrase-warn]').hidden = false;
      form.querySelector('[name="name"]')?.focus();
    });
    bootBody.querySelector('[data-act="import"]')?.addEventListener('click', () => {
      form.hidden = false;
      phraseEl.value = '';
      phraseEl.readOnly = false;
      form.querySelector('[data-phrase-warn]').hidden = true;
      phraseEl.focus();
    });
    bootBody.querySelector('[data-act="guest"]')?.addEventListener('click', () => {
      setActiveProfile(null);
      profile = null;
      setGuestChosen(true);
      hideBoot(); route(); renderAllRail();
    });
    form.addEventListener('submit', async (e) => {
      e.preventDefault();
      errEl.textContent = '';
      try {
        const wasm = await import('/pkg/dregg_wasm.js');
        await wasm.default();
        profile = createProfile(wasm, {
          name: new FormData(form).get('name'),
          phrase: phraseEl.value,
        });
        setGuestChosen(false);
        hideBoot(); route(); renderAllRail();
        // Best-effort materialization: a fresh identity claims a small faucet
        // grant so the cell exists in the ledger under its real key.
        runFaucet();
      } catch (err) {
        errEl.textContent = String(err?.message || err);
      }
    });
  }

  function renderAllRail() {
    renderIdentity();
    renderPlaces();
    renderCells();
    renderStream();
    renderNode();
  }

  // ---------------------------------------------------------------------------
  // Boot.
  // ---------------------------------------------------------------------------
  if (bootEl) bootEl.hidden = false;
  if (bootBody) bootBody.innerHTML = '<h2>Booting</h2><p class="shl-boot__what">probing the node…</p>';
  link.start();
  await link.probe();

  runtime = await createRemoteRuntime({ signals: ui, baseUrl: link.base });
  if (appEl) appEl.runtime = runtime;

  // Deep link: ?at=<dregg-uri> → the inspect mount (the shape app surfaces emit).
  try {
    const at = new URLSearchParams(window.location.search).get('at');
    if (at && isRef(at)) {
      const q = new URLSearchParams(window.location.search);
      q.delete('at');
      window.history.replaceState(null, '',
        `${window.location.pathname}${q.toString() ? `?${q}` : ''}#/inspect/${encodeURIComponent(at)}`);
    }
  } catch {}

  if (!link.state.ok) {
    showBoot('connect');
  } else if (!profile && !guestChosen()) {
    showBoot('identity');
  } else {
    hideBoot();
  }
  route();
  renderAllRail();
})();

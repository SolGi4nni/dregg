/**
 * image-shell.js — the coherence layer that makes the four surfaces
 * (explorer / playground / studio / learn) feel like tabs of ONE image.
 *
 * Three affordances, all routed through the shared resolver (resolver.js):
 *
 *   1. <dregg-image-nav current="explorer"> — the persistent surface
 *      switcher. The same four tabs everywhere; the current surface is lit.
 *
 *   2. GLOBAL "inspect anything": any element with `data-dregg-uri`, on ANY
 *      page, becomes clickable. Pages that host live inspectors handle the
 *      `dregg:navigate` event themselves (in-page mount); everywhere else —
 *      and for refs whose inspector lives on another surface — this shell
 *      routes the click to the owning surface via the resolver. Docs pages
 *      get the affordance for free by loading this module.
 *
 *   3. <dregg-live-strip> — the docs→live bridge: a concept rung embeds a
 *      strip that probes the same-origin node for a real object (e.g. the
 *      newest receipt) and links it into the explorer. HONEST: when no node
 *      is reachable from the page it says exactly that — nothing fabricated.
 */

import { resolveRef, siteBase as resolverBase } from './resolver.js';

function siteBase() {
  try {
    const p = new URL(import.meta.url).pathname;
    const i = p.indexOf('/_includes/studio/image-shell.js');
    if (i > 0) return p.slice(0, i);
  } catch { /* ignore */ }
  return resolverBase();
}

// --- 1. the surface switcher -------------------------------------------------

const SURFACES = [
  { id: 'home', label: 'π', href: '/', title: 'Dragon\'s Egg — home' },
  { id: 'learn', label: 'Learn', href: '/learn.html', title: 'the concept ladder — what each object IS' },
  { id: 'studio', label: 'Studio', href: '/studio.html', title: 'author turns, predicates, factories' },
  { id: 'explorer', label: 'Explorer', href: '/explorer/', title: 'live objects on a node — inspect anything' },
  { id: 'playground', label: 'Playground', href: '/playground/', title: 'drive the eight verbs against the wasm runtime' },
];

function detectSurface() {
  try {
    const p = window.location.pathname.replace(siteBase(), '');
    if (p.startsWith('/explorer')) return 'explorer';
    if (p.startsWith('/playground')) return 'playground';
    if (p.startsWith('/studio')) return 'studio';
    if (p.startsWith('/learn') || p.startsWith('/docs')) return 'learn';
    if (p === '/' || p === '/index.html') return 'home';
  } catch { /* non-browser */ }
  return '';
}

class DreggImageNav extends HTMLElement {
  connectedCallback() {
    const current = this.getAttribute('current') || detectSurface();
    const base = siteBase();
    this.innerHTML = SURFACES.map((s) =>
      `<a class="dregg-image-nav__tab${s.id === current ? ' is-current' : ''}${s.id === 'home' ? ' dregg-image-nav__tab--home' : ''}"
         href="${base}${s.href}" title="${s.title}"${s.id === current ? ' aria-current="page"' : ''}>${s.label}</a>`
    ).join('');
    ensureShellStyles();
  }
}
if (!customElements.get('dregg-image-nav')) customElements.define('dregg-image-nav', DreggImageNav);

// --- 2. global inspect-anything ------------------------------------------------

// Cross-surface routing for dregg:navigate events nobody handled in-page.
// Explorer/studio pages that DO handle them call preventDefault(), so this
// only fires for refs with no local home (e.g. a verb chip in the playground,
// a cell id in the docs).
document.addEventListener('dregg:navigate', (e) => {
  if (e.defaultPrevented) return;
  const uri = e.detail?.uri;
  if (!uri) return;
  const href = safeHref(uri);
  if (href) { e.preventDefault(); window.location.href = href; }
});

// Plain pages (docs, playground chrome) have no InspectorBase to translate
// clicks into dregg:navigate — do it here for any [data-dregg-uri] click that
// reaches the document unhandled.
document.addEventListener('click', (e) => {
  if (e.defaultPrevented) return;
  const el = e.target?.closest?.('[data-dregg-uri]');
  if (!el) return;
  // Inside a live inspector the InspectorBase click handler owns it.
  if (el.closest('dregg-app')) return;
  const href = safeHref(el.getAttribute('data-dregg-uri'));
  if (href) { e.preventDefault(); window.location.href = href; }
});

function safeHref(uri) {
  try {
    const r = resolveRef(uri);
    return r ? siteBase() + r.href : null;
  } catch { return null; }
}

// --- 3. docs → live strips -------------------------------------------------------

/**
 * <dregg-live-strip kind="receipt"> — embed one REAL object from the node
 * this page is served beside (same-origin; the devnet serves /api/* on the
 * site origin). Honest empty state otherwise.
 */
class DreggLiveStrip extends HTMLElement {
  async connectedCallback() {
    ensureShellStyles();
    const kind = this.getAttribute('kind') || 'receipt';
    this.innerHTML = `<div class="dregg-live-strip"><span class="dregg-live-strip__tag">live</span> probing this origin for a node…</div>`;
    const { protocol, hostname, origin } = window.location;
    const isHttp = protocol === 'http:' || protocol === 'https:';
    const isLocalFile = !isHttp;
    const base = isLocalFile ? 'http://localhost:8420' : origin;
    try {
      if (kind === 'receipt') {
        const res = await fetchTimeout(`${base}/api/starbridge/receipts?limit=1`, 5000);
        const data = await res.json();
        const list = Array.isArray(data) ? data : data.receipts || [];
        const r = list[0]?.receipt || list[0];
        if (r) {
          const hash = r.turn_hash || r.receipt_hash || r.hash;
          const post = r.post_state_hash || r.post_state || '';
          this.renderLive(`a real receipt this node serves right now`, [
            ['turn', hash, `dregg://receipt/${hash}`],
            ['post-state commitment', post, null],
          ]);
          return;
        }
      } else if (kind === 'cell') {
        const res = await fetchTimeout(`${base}/api/cells`, 5000);
        const data = await res.json();
        const list = Array.isArray(data) ? data : data.cells || [];
        const c = list[0];
        if (c) {
          const id = c.cell_id || c.id;
          this.renderLive(`a real cell this node serves right now`, [
            ['cell', id, `dregg://cell/${id}`],
            ['balance', String(c.balance ?? c.state?.balance ?? '—'), null],
          ]);
          return;
        }
      }
      this.renderEmpty('node reachable, but it serves no objects of this kind yet');
    } catch {
      this.renderEmpty(isLocalFile
        ? 'no node at localhost:8420 from this page'
        : 'no node reachable on this page\'s origin');
    }
  }
  renderLive(lede, rows) {
    const cells = rows.map(([k, v, uri]) => {
      const short = String(v || '').slice(0, 18) + (String(v || '').length > 18 ? '…' : '');
      return uri
        ? `<span>${k}: <a class="dregg-live-strip__link" data-dregg-uri="${uri}" href="${safeHref(uri) || '#'}"><code title="${v}">${short}</code></a></span>`
        : `<span>${k}: <code title="${v}">${short}</code></span>`;
    }).join(' · ');
    this.innerHTML = `<div class="dregg-live-strip is-live"><span class="dregg-live-strip__tag is-live">live</span> ${lede} — ${cells}</div>`;
  }
  renderEmpty(why) {
    this.innerHTML = `<div class="dregg-live-strip"><span class="dregg-live-strip__tag">live</span> ` +
      `no live instance to show: ${why}. <a class="dregg-live-strip__link" href="${siteBase()}/explorer/">open the explorer</a> against a node to see real ones.</div>`;
  }
}
if (!customElements.get('dregg-live-strip')) customElements.define('dregg-live-strip', DreggLiveStrip);

function fetchTimeout(url, ms) {
  const ctl = new AbortController();
  const t = setTimeout(() => ctl.abort(), ms);
  return fetch(url, { headers: { Accept: 'application/json' }, signal: ctl.signal })
    .then((r) => { if (!r.ok) throw new Error(String(r.status)); return r; })
    .finally(() => clearTimeout(t));
}

// --- styles -----------------------------------------------------------------------

function ensureShellStyles() {
  if (document.getElementById('dregg-image-shell-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-image-shell-styles';
  s.textContent = `
dregg-image-nav { display:inline-flex; align-items:center; gap:2px; border:1px solid var(--line,#2a3530); border-radius:999px; padding:2px; background:var(--bg-raised,#141a17); }
.dregg-image-nav__tab { color:var(--fg-dim,#9aa0a6); text-decoration:none; font-size:0.78rem; padding:3px 11px; border-radius:999px; white-space:nowrap; }
.dregg-image-nav__tab:hover { color:var(--fg,#e8f0e8); }
.dregg-image-nav__tab.is-current { color:var(--bg,#0d1117); background:var(--accent,#5b8a5a); font-weight:650; }
.dregg-image-nav__tab--home { font-family:var(--mono,ui-monospace,monospace); }
.dregg-live-strip { border:1px solid var(--line,#30363d); border-left:3px solid var(--line,#30363d); border-radius:6px; background:var(--bg-raised,#161b22); padding:8px 11px; font-size:0.82rem; color:var(--fg-dim,#9aa0a6); line-height:1.5; margin:10px 0; }
.dregg-live-strip.is-live { border-left-color:#62c47a; }
.dregg-live-strip__tag { display:inline-block; border:1px solid var(--line,#30363d); border-radius:999px; padding:0 8px; font-size:0.64rem; text-transform:uppercase; letter-spacing:0.06em; margin-right:6px; }
.dregg-live-strip__tag.is-live { border-color:#62c47a; color:#8ee6a2; }
.dregg-live-strip__link { color:var(--accent-bright,#8fddff); text-decoration:none; border-bottom:1px dotted currentColor; }
[data-dregg-uri] { cursor:pointer; }
`;
  document.head.appendChild(s);
}

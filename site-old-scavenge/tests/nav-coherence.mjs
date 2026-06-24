// Nav coherence: the site's authored pages must form ONE connected tree.
//
//   1. Every internal link on every authored page resolves to a real file in
//      dist/ (directory links resolve via index.html).
//   2. No orphans: every authored top-level page is reachable by crawling
//      from index.html (redirect stubs count as reachable via their target).
//
// Authored pages = HTML built from site/src (dist minus the copy-through
// dirs, whose internals are app surfaces with their own tests). Links INTO
// copy-through dirs are still checked for existence.
//
// BASE_PATH-aware: if dist was built with BASE_PATH=/dregg, hrefs carry the
// prefix; we detect it from the nav brand link and strip it before resolving.
//
// Run: node site/tests/nav-coherence.mjs   (after node build.js)

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const DIST = path.join(SITE, 'dist');

if (!fs.existsSync(path.join(DIST, 'index.html'))) {
  console.error('nav-coherence: dist/index.html missing — run node build.js first');
  process.exit(1);
}

// Copy-through dirs: link targets inside them must exist, but we do not
// crawl their internals.
const COPY_DIRS = new Set([
  'playground', 'explorer', 'sandbox', 'extension', 'examples', 'demos',
  'pkg', 'old-site', 'starbridge-apps', '_includes', 'assets', 'paper',
  // the self-built interactive atlas (bundled by pages.yml at /dregg/atlas/) —
  // a self-contained app surface with its own structure, not authored pages.
  'atlas',
  // the live web cockpit (the verified executor in wasm, /dregg/cockpit/).
  'cockpit',
]);

// Detect BASE_PATH from the built nav brand link (href="{BASE}/").
function detectBasePath() {
  if (process.env.BASE_PATH) return process.env.BASE_PATH.replace(/\/$/, '');
  const html = fs.readFileSync(path.join(DIST, 'index.html'), 'utf8');
  const m = html.match(/class="nav__brand"/) && html.match(/<a href="([^"]*)\/" class="nav__brand"/);
  return m ? m[1] : '';
}
const BASE = detectBasePath();

let failures = 0;
const fail = (msg) => { console.error(`FAIL: ${msg}`); failures++; };

// href → dist-relative file path, or null for external/non-checkable links.
function resolveHref(fromRel, href) {
  if (!href) return null;
  if (/^(https?:|mailto:|data:|javascript:|#|dregg:)/.test(href)) return null;
  let clean = href.split('#')[0].split('?')[0];
  if (!clean) return null;
  if (BASE && clean.startsWith(BASE + '/')) clean = clean.slice(BASE.length);
  let rel;
  if (clean.startsWith('/')) {
    rel = clean.slice(1);
  } else {
    rel = path.posix.normalize(path.posix.join(path.posix.dirname(fromRel), clean));
  }
  if (rel === '' || rel.endsWith('/')) rel = path.posix.join(rel, 'index.html');
  return rel;
}

function isAuthored(rel) {
  const top = rel.split('/')[0];
  return rel.endsWith('.html') && !COPY_DIRS.has(top);
}

const LINK_RE = /\b(?:href|src)="([^"]+)"/g;

// BFS from index.html over authored pages.
const visited = new Set();
const queue = ['index.html'];
while (queue.length) {
  const rel = queue.shift();
  if (visited.has(rel)) continue;
  visited.add(rel);
  const file = path.join(DIST, rel);
  if (!fs.existsSync(file)) { fail(`${rel}: page in crawl but missing from dist`); continue; }
  const html = fs.readFileSync(file, 'utf8');

  // Redirect stubs: follow the meta-refresh target, skip link checking.
  const stub = html.match(/http-equiv="refresh"\s+content="\d+;\s*url=([^"]+)"/i);
  if (stub) {
    const target = resolveHref(rel, stub[1]);
    if (!target) { fail(`${rel}: redirect stub with unresolvable target ${stub[1]}`); continue; }
    if (!fs.existsSync(path.join(DIST, target))) fail(`${rel}: redirect target missing: ${target}`);
    else if (isAuthored(target) && !visited.has(target)) queue.push(target);
    continue;
  }

  for (const m of html.matchAll(LINK_RE)) {
    const target = resolveHref(rel, m[1]);
    if (!target) continue;
    if (!fs.existsSync(path.join(DIST, target))) {
      fail(`${rel}: broken link ${m[1]} → ${target}`);
      continue;
    }
    if (isAuthored(target) && !visited.has(target)) queue.push(target);
  }
}

// Orphan check: every authored .html in dist must be reachable. Redirect
// stubs are entry points (kept-working old URLs), so a stub being unvisited
// is fine ONLY if its target is in the graph — verify by following it.
function* walkAuthored(dir = '', out = []) {
  for (const e of fs.readdirSync(path.join(DIST, dir), { withFileTypes: true })) {
    const rel = path.posix.join(dir, e.name);
    if (e.isDirectory()) {
      if (!COPY_DIRS.has(rel.split('/')[0])) yield* walkAuthored(rel);
    } else if (rel.endsWith('.html')) {
      yield rel;
    }
  }
}
for (const rel of walkAuthored()) {
  if (visited.has(rel)) continue;
  const html = fs.readFileSync(path.join(DIST, rel), 'utf8');
  const stub = html.match(/http-equiv="refresh"/i);
  if (stub) {
    const target = html.match(/url=([^"]+)"/i);
    const t = target && resolveHref(rel, target[1]);
    if (!t || !(visited.has(t) || fs.existsSync(path.join(DIST, t)))) {
      fail(`${rel}: redirect stub whose target is outside the site graph`);
    }
    continue;
  }
  fail(`${rel}: orphan page — not reachable from index.html`);
}

if (failures) {
  console.error(`\nnav-coherence: ${failures} failure(s).`);
  process.exit(1);
}
console.log(`nav-coherence: OK (${visited.size} pages crawled from index.html, no broken links, no orphans${BASE ? `, base ${BASE}` : ''})`);

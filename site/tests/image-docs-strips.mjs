// Image coherence in the BUILT site: the docs↔live strips render, the
// dregg:// anchor targets exist on the rungs the resolver points at, and the
// four surfaces carry the shared switcher. Run AFTER `node build.js`.
//
// Run: node site/tests/image-docs-strips.mjs

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const DIST = path.join(SITE, 'dist');
const CATALOGS = path.join(SITE, 'src', '_includes', 'studio');

const cat = (name) => JSON.parse(fs.readFileSync(path.join(CATALOGS, name), 'utf8'));
const page = (rel) => fs.readFileSync(path.join(DIST, rel), 'utf8');

let failures = 0;
function expect(html, rel, needle, what) {
  if (!html.includes(needle)) {
    console.error(`FAIL ${rel}: missing ${what}: ${JSON.stringify(needle)}`);
    failures++;
  }
}

// --- anchors: every resolver target exists on its rung -----------------------
{
  const v = cat('verb-catalog.generated.json');
  const html = page('learn/concepts/substances.html');
  for (const verb of v.verbs) {
    expect(html, 'learn/concepts/substances.html', `id="verb-${verb.name}"`, 'verb anchor (dregg://verb)');
  }
}
{
  const p = cat('predicate-catalog.generated.json');
  const html = page('learn/concepts/guards.html');
  for (const c of p.constraints) {
    expect(html, 'learn/concepts/guards.html', `id="constraint-${c.name}"`, 'constraint anchor');
  }
}
{
  const a = cat('assurance-catalog.generated.json');
  const html = page('learn/concepts/trust-boundary.html');
  for (const g of a.guarantees) {
    expect(html, 'learn/concepts/trust-boundary.html', `id="guarantee-${g.letter}"`, 'guarantee anchor (dregg://guarantee)');
  }
}

// --- the userspace rung's live-instances strip (generated factory samples) ---
{
  const s = cat('factory-samples.generated.json');
  const html = page('learn/concepts/userspace.html');
  expect(html, 'learn/concepts/userspace.html', 'data-catalog="factory-instances"', 'factory-instances strip');
  for (const k of ['escrow', 'obligation', 'council', 'constitution']) {
    expect(html, 'learn/concepts/userspace.html', s[k].title, `${k} sample title`);
    expect(html, 'learn/concepts/userspace.html', String(s[k].descriptor_hash).slice(0, 16), `${k} descriptor hash`);
    expect(html, 'learn/concepts/userspace.html', `dregg://factory/${k}`, `${k} factory deep link`);
  }
}

// --- the docs→live probes are embedded -----------------------------------------
expect(page('learn/concepts/receipts.html'), 'learn/concepts/receipts.html',
  '<dregg-live-strip kind="receipt">', 'live receipt strip');
expect(page('learn/concepts/substances.html'), 'learn/concepts/substances.html',
  '<dregg-live-strip kind="cell">', 'live cell strip');

// --- the switcher + shell on all four surfaces ---------------------------------
expect(page('explorer/index.html'), 'explorer/index.html', '<dregg-image-nav', 'switcher (explorer)');
expect(page('explorer/index.html'), 'explorer/index.html', 'id="page-polis"', 'polis page (explorer)');
expect(page('playground/index.html'), 'playground/index.html', '<dregg-image-nav', 'switcher (playground)');
expect(page('studio.html'), 'studio.html', '<dregg-image-nav', 'switcher (studio, via nav include)');
expect(page('studio.html'), 'studio.html', 'runtime-bootstrap.js', 'inspector bootstrap (studio compose-then-inspect)');
expect(page('learn/concepts/turn.html'), 'learn/concepts/turn.html', 'image-shell.js', 'image-shell on docs pages');

// --- the polis inspectors ship in the studio bundle ------------------------------
expect(fs.readFileSync(path.join(DIST, '_includes', 'studio', 'inspectors.js'), 'utf8'),
  '_includes/studio/inspectors.js', "./inspectors/polis.js", 'polis inspectors registered');
for (const f of ['polis-decode.js', 'resolver.js', 'image-shell.js']) {
  if (!fs.existsSync(path.join(DIST, '_includes', 'studio', f))) {
    console.error(`FAIL dist/_includes/studio/${f} missing`);
    failures++;
  }
}

if (failures) { console.error(`\n${failures} failure(s)`); process.exit(1); }
console.log('all image-docs-strips checks passed');

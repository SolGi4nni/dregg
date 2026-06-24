// Living-docs drift check: the built docs pages embed facts from the
// generated catalogs (build.js <catalog view="..."> → CATALOG_VIEWS). This
// test mirrors the gen-ontology-catalog --check discipline one layer up: it
// re-reads the catalogs and asserts every checkable fact they carry actually
// appears in the built HTML — so a page that stops embedding (or a view that
// silently drops rows) fails CI, the same way a stale catalog fails the build.
//
// Run: node site/tests/docs-living-content.mjs   (after node build.js)

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

// --- the verb roster: every verb + its substance on the substances rung ----
{
  const v = cat('verb-catalog.generated.json');
  const html = page('learn/concepts/substances.html');
  for (const verb of v.verbs) {
    expect(html, 'learn/concepts/substances.html', `<code>${verb.name}</code>`, 'verb');
    expect(html, 'learn/concepts/substances.html', `<code>${verb.substance}</code>`, 'substance');
  }
  for (const t of v.minimality_theorems.concat(v.completeness_theorems)) {
    expect(html, 'learn/concepts/substances.html', t, 'registry theorem');
  }
}

// --- the factory patterns + proof modules on the userspace rung ------------
{
  const v = cat('verb-catalog.generated.json');
  const html = page('learn/concepts/userspace.html');
  for (const f of v.factory_patterns) {
    expect(html, 'learn/concepts/userspace.html', `<code>${f.pattern}</code>`, 'factory pattern');
    if (f.module) expect(html, 'learn/concepts/userspace.html', f.module, 'factory module');
  }
}

// --- the guarantee list: every letter/title/apex on trust-boundary + index -
{
  const a = cat('assurance-catalog.generated.json');
  for (const rel of ['learn/concepts/trust-boundary.html', 'index.html']) {
    const html = page(rel);
    for (const g of a.guarantees) {
      expect(html, rel, `${g.title}`, `guarantee ${g.letter} title`);
      if (g.apex_theorem) expect(html, rel, g.apex_theorem, `guarantee ${g.letter} apex`);
    }
    for (const ax of a.kernel_axiom_triple) expect(html, rel, ax, 'kernel axiom');
  }
}

// --- the assumption floor: every carrier on light-client + trust-boundary --
{
  const a = cat('assurance-catalog.generated.json');
  for (const rel of ['learn/concepts/light-client.html', 'learn/concepts/trust-boundary.html']) {
    const html = page(rel);
    for (const f of a.assumption_floor) {
      expect(html, rel, f.name, 'floor carrier');
    }
  }
}

// --- the constraint kinds: every kind on the guards rung -------------------
{
  const p = cat('predicate-catalog.generated.json');
  const html = page('learn/concepts/guards.html');
  for (const c of p.constraints) {
    expect(html, 'learn/concepts/guards.html', `<code>${c.name}</code>`, 'constraint kind');
  }
}

if (failures) {
  console.error(`\ndocs-living-content: ${failures} missing fact(s). ` +
    'A docs page has drifted from the generated catalogs — re-run node build.js ' +
    'and check the <catalog view="..."> embeds.');
  process.exit(1);
}
console.log('docs-living-content: OK (all catalog facts present in built docs)');

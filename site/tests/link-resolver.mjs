// The image's link resolver: every dregg:// form must (a) round-trip through
// the shared uri.js parser and (b) resolve to the surface that owns it.
//
// Run: node site/tests/link-resolver.mjs

import path from 'node:path';
import { fileURLToPath } from 'node:url';

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const STUDIO = path.join(SITE, 'src', '_includes', 'studio');

const { resolveRef, isResolvable, rungRef, RUNG_FOR_KIND } = await import(path.join(STUDIO, 'resolver.js'));
const { parseRef, makeRef, isRef } = await import(path.join(STUDIO, 'uri.js'));

let failures = 0;
function check(cond, what) {
  if (!cond) { console.error(`FAIL: ${what}`); failures++; }
  else console.log(`ok: ${what}`);
}

const HASH = 'a'.repeat(64);

// kind → [ref, expected surface, substring the href must contain]
const CASES = [
  // live objects → explorer (?at= deep link, the explorer's existing scheme)
  [`dregg://cell/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://cell-history/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://receipt/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://turn/${HASH}`, 'explorer', '/explorer/?at='],
  ['dregg://block/0/42', 'explorer', '/explorer/?at='],
  ['dregg://block-dag/0', 'explorer', '/explorer/?at='],
  [`dregg://capability/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://token/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://intent/${HASH}`, 'explorer', '/explorer/?at='],
  ['dregg://federation/all', 'explorer', '/explorer/?at='],
  ['dregg://activity/feed', 'explorer', '/explorer/?at='],
  // the polis organ
  [`dregg://council/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://constitution/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://mandate/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://amendment-ceremony/${HASH}`, 'explorer', '/explorer/?at='],
  [`dregg://amendment-ceremony/${HASH}/old/${HASH}/new/${HASH}`, 'explorer', '/explorer/?at='],
  // vocabulary → docs/studio
  ['dregg://verb/move', 'learn', '/learn/concepts/substances.html#verb-move'],
  ['dregg://verb/shieldUnshield', 'learn', '#verb-shieldUnshield'],
  ['dregg://constraint/WriteOnce', 'studio', '/studio.html?constraint=WriteOnce#predicates'],
  ['dregg://constraint/AffineLe', 'studio', '?constraint=AffineLe'],
  ['dregg://guarantee/A', 'learn', '/learn/concepts/trust-boundary.html#guarantee-A'],
  ['dregg://factory/council', 'studio', '/studio.html?factory=council#factory'],
  [`dregg://factory/${'6582dc71'}`, 'studio', '?factory=6582dc71'],
  ['dregg://effect/transfer', 'studio', '/studio.html?effect=transfer#catalog'],
  // concept rungs (the "what is this?" backbone)
  ['dregg://concept/turn', 'learn', '/learn/concepts/turn.html'],
  ['dregg://concept/substances', 'learn', '/learn/concepts/substances.html'],
  ['dregg://concept/guards', 'learn', '/learn/concepts/guards.html'],
  ['dregg://concept/receipts', 'learn', '/learn/concepts/receipts.html'],
  ['dregg://concept/light-client', 'learn', '/learn/concepts/light-client.html'],
  ['dregg://concept/userspace', 'learn', '/learn/concepts/userspace.html'],
  ['dregg://concept/trust-boundary', 'learn', '/learn/concepts/trust-boundary.html'],
];

for (const [ref, surface, fragment] of CASES) {
  const r = resolveRef(ref);
  check(r && r.surface === surface && r.href.includes(fragment),
    `${ref} → ${surface} (${r ? r.href : 'null'})`);
  // every resolvable explorer/studio object form must also parse with uri.js
  if (surface === 'explorer') {
    const parsed = parseRef(ref);
    check(isRef(ref) && parsed.kind && parsed.id, `${ref} parses with uri.js (kind=${parsed.kind})`);
    check(makeRef(parsed.kind, parsed.id, { sub: parsed.sub }).startsWith(`dregg://${parsed.kind}/${parsed.id}`),
      `${ref} round-trips through makeRef`);
  }
  // ?at= refs must decode back to the original (the explorer reads them back)
  if (fragment === '/explorer/?at=') {
    const at = decodeURIComponent(r.href.split('?at=')[1]);
    check(at === ref, `${ref} survives the ?at= round trip`);
  }
}

// junk handling
check(!isResolvable('not-a-ref'), 'junk is not resolvable');
check(resolveRef('dregg://nonsense/xyz') === null, 'unknown kinds resolve to null, not a wrong surface');
check(resolveRef('dregg://concept/nope') === null, 'unknown concept rungs resolve to null');

// every inspector kind with a docs rung resolves to a real rung ref
for (const kind of Object.keys(RUNG_FOR_KIND)) {
  const rr = rungRef(kind);
  check(rr != null && resolveRef(rr) != null, `RUNG_FOR_KIND[${kind}] → ${rr} resolves`);
}

if (failures) { console.error(`\n${failures} failure(s)`); process.exit(1); }
console.log('\nall link-resolver checks passed');

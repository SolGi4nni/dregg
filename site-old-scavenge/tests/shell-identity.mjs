// Shell identity invariants: the embedded wordlist is exactly 256 unique
// words (8 bits/word ⇒ a 24-word phrase carries 192 bits), and generatePhrase
// emits 24 of them. The keypair/cell derivation itself is covered by
// shell-blake3.mjs (cell id) and the wasm module (Ed25519).
//
// Run: node site/tests/shell-identity.mjs

import path from 'node:path';
import { fileURLToPath } from 'node:url';

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const SHELL = path.join(SITE, 'src', '_includes', 'studio', 'shell');

const { WORDLIST, generatePhrase } = await import(path.join(SHELL, 'identity.js'));

let failures = 0;
function check(cond, what) {
  if (!cond) { console.error(`FAIL: ${what}`); failures++; }
  else console.log(`ok: ${what}`);
}

check(WORDLIST.length === 256, `wordlist has 256 words (got ${WORDLIST.length})`);
check(new Set(WORDLIST).size === 256, 'wordlist words are unique');
check(WORDLIST.every((w) => /^[a-z]+$/.test(w)), 'words are lowercase ascii');

for (let i = 0; i < 8; i += 1) {
  const phrase = generatePhrase();
  const words = phrase.split(' ');
  check(words.length === 24, `phrase ${i} has 24 words`);
  check(words.every((w) => WORDLIST.includes(w)), `phrase ${i} draws from the wordlist`);
}

check(generatePhrase() !== generatePhrase(), 'two phrases differ');

if (failures) process.exit(1);
console.log('shell identity invariants hold');

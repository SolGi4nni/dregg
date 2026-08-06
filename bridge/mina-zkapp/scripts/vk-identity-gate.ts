import { existsSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  KNOWN_VK_NOTIONS,
  explainVkMismatch,
  identifyVkHash,
  leanEmissionEpoch,
  resolveVkNotions,
  vkNotion,
} from '../src/VerificationKeyIdentity.js';

// ---------------------------------------------------------------------------
// THE VK IDENTITY GATE — every key notion in this tree resolved to the CIRCUIT
// it keys, every pin recomputed from its PRODUCER, and both polarities of the
// refusal exercised.
//
// ⚑ WHAT WENT WRONG WITHOUT IT. `DreggHeadGate.advanceHead` pins an o1js
// `.compile()` hash; dregg's key on Mina devnet is derived from Lean-emitted
// `KimchiWrapMain` gates. They differ, `advanceHead` refuses the registered one,
// and the refusal said only "the proof was made under a key this gate does not
// name" — a number against a number. In that shape a CATEGORY ERROR (two
// circuits) and a REAL DRIFT (one circuit, two epochs) are indistinguishable,
// and this tree has had both.
//
// This gate is out of circuit, reads JSON, and finishes in milliseconds. It is
// tier 0 for exactly the reason `src/tier.ts` gives: the arc's actual defects
// were found by cheap exhaustive out-of-circuit checks, not by compiles.
//
// ⚑ NO SKIPS. An absent producer artifact is REPORTED as absent and named, and
// notions whose artifacts a clean checkout does not carry do not fail the gate —
// but a pin that DISAGREES with a producer that IS present is RED, and an
// identification that cannot go red is RED.
//
//   npm run vk-identity
//   npm run vk-identity -- --self-test    # prove the identification can go red
// ---------------------------------------------------------------------------

// ⚑ `../..`, because this runs as `dist/scripts/vk-identity-gate.js`. The same
// base every other leg in this directory uses; `../..` from `<app>/dist/scripts`
// is `<app>`. Not `process.cwd()` — a leg whose paths depend on where it was
// invoked from is a leg that reads nothing when invoked from elsewhere, and the
// floor in [1] exists because that failure is silent.
const APP = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const REPO = process.env.DREGG_REPO_ROOT ?? resolve(APP, '..', '..');
const SELF_TEST = process.argv.includes('--self-test');

let failures = 0;
const ok = (m: string) => console.log(`  ✓ ${m}`);
const bad = (m: string) => {
  failures++;
  console.log(`  ✗ ${m}`);
};
const check = (c: boolean, good: string, wrong: string) => (c ? ok(good) : bad(wrong));

const resolved = resolveVkNotions(APP);

// ── [1] THE ROSTER ─────────────────────────────────────────────────────────
// Say what each key is the key OF. This is the half that was nowhere.
console.log('\n=== [1] THE KEY NOTIONS IN THIS TREE, AND THE CIRCUIT EACH KEYS ===\n');
for (const r of resolved) {
  const n = r.notion;
  console.log(`  ${n.id}`);
  console.log(`     circuit    ${n.circuit}`);
  console.log(`     produced   ${n.producedBy}`);
  console.log(`     side       ${n.side}`);
  console.log(`     consumer   ${n.consumer}`);
  console.log(`     value      ${r.hash === null ? `ABSENT — ${r.absent}` : r.hash}`);
  console.log(
    `     from       ${
      r.source === 'mirror-only' ? `${n.mirrorPath} (pin only)` : n.valuePath
    }`,
  );
  if (r.unverified) console.log(`     ⚠ UNCHECKED ${r.unverified}`);
  if (n.caveat) console.log(`     ⚠ ${n.caveat}`);
  console.log('');
}

// ⚑ THE FLOOR. A roster that read nothing would print a clean sweep.
check(
  KNOWN_VK_NOTIONS.length >= 4,
  `${KNOWN_VK_NOTIONS.length} notions declared`,
  `only ${KNOWN_VK_NOTIONS.length} notions declared — the registry is not being read`,
);
const present = resolved.filter((r) => r.hash !== null);
check(
  present.length >= 2,
  `${present.length} of ${resolved.length} notions resolve to a value in this checkout`,
  `only ${present.length} notion(s) resolved — the artifacts are not being read, and a gate that ` +
    'reads nothing agrees with everything',
);

// ── [1b] EVERY NOTION'S CREDITED PRODUCER EXISTS ───────────────────────────
// ⚑ AN ABSENT VALUE AND A PATH NOTHING WRITES LOOK IDENTICAL. Three of four
// notions resolve to ABSENT in a clean checkout, so "the artifact is not there
// yet" is the normal state and a `valuePath` naming a file no producer emits
// would sit in it forever. This tree already has that exact rot one level up:
// the `mina-shrink-head` npm script runs `dist/scripts/mina-shrink-head.js`, for
// which `scripts/mina-shrink-head.ts` has never existed.
console.log('=== [1b] THE CREDITED PRODUCER OF EACH NOTION EXISTS ===\n');
for (const r of resolved) {
  const src = r.notion.producerSource;
  if (src === null) {
    console.log(
      `  ⚠  ${r.notion.id}: NO SCRIPT WRITES ${r.notion.valuePath} — it is a hand-maintained ` +
        'record. Its numbers are as good as the last edit, and its prose goes stale silently.',
    );
    continue;
  }
  check(
    existsSync(resolve(APP, src)),
    `${r.notion.id}: credited producer ${src} exists`,
    `${r.notion.id}: credited producer ${src} DOES NOT EXIST — the notion names an emitter ` +
      'this tree does not have, so its value could never appear',
  );
}
console.log('');

// ── [2] EVERY PIN RECOMPUTED FROM ITS PRODUCER ─────────────────────────────
// The sibling pattern: `check_subproof_program_pin` recomputes the dispatched
// sub-proof's fingerprint at verify time rather than trusting a literal. A pin
// file is a literal; its producer is the key ring. Compare them.
console.log('=== [2] EVERY PIN RECOMPUTED FROM ITS PRODUCER (not trusted as a literal) ===\n');
for (const r of resolved) {
  if (r.notion.mirrorPath === null) {
    console.log(`  ·  ${r.notion.id}: single-source (${r.notion.valuePath}); nothing to cross-check`);
    continue;
  }
  if (r.hash === null) {
    console.log(`  ·  ${r.notion.id}: neither side present — ${r.absent}`);
    continue;
  }
  if (r.source === 'mirror-only') {
    // ⚑ NOT A FAILURE, AND NOT A SILENCE. `.fullchain/` is gitignored, so this is
    // the state of every clone that did not compile the chain itself. Reddening
    // here would make the leg a machine-detector rather than a drift-detector —
    // the vacuous-red class. Saying what went unchecked is the whole obligation.
    console.log(`  ⚠  ${r.notion.id}: ${r.unverified}`);
    continue;
  }
  check(
    r.drift === '',
    `${r.notion.id}: ${r.notion.mirrorPath} agrees with its producer ${r.notion.valuePath}`,
    `${r.notion.id}: ${r.drift}`,
  );
}
console.log('');

// ── [3] THE LEAN WRAP EMISSION'S EPOCH, MEASURED ───────────────────────────
// The registered key is the key of ONE emission. Saying "it is stale" is only
// informative with the two epochs named.
console.log('=== [3] THE REGISTERED KEY\'S EPOCH vs HEAD\'S LEAN EMISSION ===\n');
const ep = leanEmissionEpoch(APP, REPO);
console.log(`  registered emission  ${ep.registeredSha256 ?? 'UNREADABLE'}`);
console.log(`     its circuit       ${ep.registeredShape ?? 'UNREADABLE'}`);
console.log(`  HEAD emission        ${ep.currentSha256 ?? 'ABSENT'}`);
console.log(`     its circuit       ${ep.currentShape ?? 'ABSENT'}`);
if (ep.registeredSha256 === null || ep.currentSha256 === null) {
  bad('one of the two emission identities could not be read — the epoch comparison is blind');
} else if (ep.chainHoldsCurrent) {
  ok('the devnet account holds the key of HEAD\'s emission');
} else {
  console.log(
    '\n  ⚑ THE DEVNET ACCOUNT HOLDS AN OLDER CIRCUIT. This is not a drift OF the chain: the\n' +
      '    chain holds exactly what was registered. The Lean assembly moved underneath it.\n' +
      '    Re-registering is a fresh account + a keypair + 1 MINA on a signed devnet\n' +
      '    transaction — THE OPERATOR\'S CALL, and nothing here attempts it.\n',
  );
  ok('the two emission epochs are NAMED rather than collapsed into "the hash differs"');
}
console.log('');

// ── [4] BOTH POLARITIES OF THE REFUSAL ─────────────────────────────────────
console.log('=== [4] BOTH POLARITIES — the right key accepted, the wrong key refused BY NAME ===\n');

const WANT = 'o1js-rootfriuniform-terminal-babybear';
const want = resolved.find((r) => r.notion.id === WANT)!;

if (want.hash === null) {
  bad(
    `the key ${WANT} is absent in this checkout, so neither polarity can be exercised — ` +
      `${want.absent}`,
  );
} else {
  // ACCEPT — the key `advanceHead` pins identifies as the circuit it names.
  const self = identifyVkHash(want.hash, resolved);
  check(
    self !== null && self.notion.id === WANT,
    `ACCEPT: ${want.hash} identifies as ${WANT} — the o1js terminal advanceHead pins`,
    `the pinned key does not identify as its own notion (the lookup is broken, not the tree)`,
  );

  // REFUSE (different object) — the key registered on Mina devnet.
  const reg = resolved.find((r) => r.notion.id === 'lean-kimchi-wrapmain-w4bind')!;
  if (reg.hash === null) {
    bad(`the registered devnet key is unreadable — ${reg.absent}`);
  } else {
    check(
      reg.hash !== want.hash,
      'the registered devnet key and the pinned terminal key are DIFFERENT numbers',
      'the registered devnet key equals the pinned terminal key — this gate is comparing a value ' +
        'with itself and proves nothing',
    );
    const msg = explainVkMismatch(WANT, reg.hash, resolved);
    console.log('\n  --- what advanceHead now says when handed the REGISTERED key ---');
    console.log(
      msg
        .split('\n')
        .map((l) => `  | ${l}`)
        .join('\n'),
    );
    console.log('');
    check(
      msg.includes(WANT) && msg.includes('lean-kimchi-wrapmain-w4bind'),
      'REFUSE: the refusal names BOTH keys by notion, not by anonymous number',
      'the refusal does not name both keys — this is the shape the wound hid in',
    );
    check(
      msg.includes('TWO DIFFERENT CIRCUITS'),
      'REFUSE: the refusal says these are two circuits, not two epochs of one',
      'the refusal does not distinguish a category error from a drift',
    );
    check(
      msg.includes('OPPOSITE ENDS OF THE BRIDGE'),
      'REFUSE: the refusal states the layering (prover-side pin vs Mina ledger account state)',
      'the refusal does not state the layering',
    );
  }

  // REFUSE (unknown) — a number no notion holds. Constructed, never fabricated
  // as a key: `pin + 1` is not a verification key and is not presented as one.
  const stranger = want.hash + 1n;
  check(
    identifyVkHash(stranger, resolved) === null,
    'a number no notion holds is identified as UNKNOWN',
    'an unknown number was identified as a known key — the lookup accepts anything',
  );
  const unknownMsg = explainVkMismatch(WANT, stranger, resolved);
  check(
    unknownMsg.includes('NOT a key this tree knows') && unknownMsg.includes(WANT),
    'REFUSE: an unknown key is refused with the WANTED key named and the roster printed',
    'the unknown-key refusal does not name what was wanted',
  );
}

// ── [5] SELF-TEST — prove the identification can go red ────────────────────
if (SELF_TEST) {
  console.log('\n=== [5] SELF-TEST — the identification must be able to go RED ===\n');
  // (a) a notion whose value is swapped for another notion's must be reported as
  //     the OTHER notion. If identification were a rubber stamp this would pass
  //     it off as the wanted key.
  const reg = resolved.find((r) => r.notion.id === 'lean-kimchi-wrapmain-w4bind')!;
  if (reg.hash === null) {
    bad('self-test: the registered key is unreadable, so the swap probe cannot run');
  } else {
    const hit = identifyVkHash(reg.hash, resolved);
    check(
      hit !== null && hit.notion.id === 'lean-kimchi-wrapmain-w4bind',
      'self-test: the registered key identifies as ITSELF and not as the wanted one',
      'self-test: the registered key was mis-identified — the lookup is not discriminating',
    );
  }
  // (b) ⚑ THE DRIFT CHECK MUST GO RED. On a healthy tree [2] is always green,
  //     which is precisely the state in which nobody has shown it CAN fail. Feed
  //     the resolver a pin file whose `terminalVkHash` is one off its producer,
  //     in memory — no tracked file is touched, because this working tree is
  //     shared with other lanes.
  const w = resolved.find((r) => r.notion.id === WANT)!;
  if (w.hash === null) {
    bad('self-test: the wanted key is absent, so the drift probe cannot run');
  } else if (w.source !== 'producer') {
    // ⚑ SAY IT LOUDLY RATHER THAN PASS QUIETLY. Drift is only observable where
    // BOTH the pin and its producing key ring exist, and `.fullchain/` is
    // gitignored — so on any checkout that did not compile the chain, [2]'s red
    // path is UNPROVEN here. That is a fact about this machine, not a defect,
    // and a transcript must not read as if the red-proof had run.
    console.log(
      '  ⚠  self-test: [2]\'s DRIFT CHECK IS UNPROVEN ON THIS MACHINE. It needs the key ring\n' +
        `     (${w.notion.valuePath}) beside the pin, and \`.fullchain/\` is gitignored. Run\n` +
        `     \`${w.notion.producer}\` on a box that has the chain, then re-run --self-test.\n` +
        '     Everything else below did run.',
    );
  } else {
    const perturbed = resolveVkNotions(APP, {
      perturb: (rel, j) =>
        rel === 'dregg-chain-pins.json'
          ? { ...j, terminalVkHash: (BigInt(j.terminalVkHash) + 1n).toString() }
          : j,
    });
    const d = perturbed.find((r) => r.notion.id === WANT)!;
    check(
      d.drift !== '',
      'self-test: a pin one off its producer is REPORTED as drift — [2] can go red',
      'self-test: a pin one off its producer was accepted — [2] cannot go red and proves nothing',
    );
    check(
      d.drift.includes('ONE OBJECT, DRIFTED') &&
        d.drift.includes('dregg-chain-pins.json') &&
        d.drift.includes('.fullchain/uniform-claim/key-block42.json'),
      'self-test: the drift report names the PIN, the PRODUCER, and that it is one object',
      'self-test: the drift report does not name both sides — it would read like a category error',
    );
    // And the unchanged resolution must still be clean, so the red above is
    // attributable to the perturbation rather than to the probe running at all.
    check(
      w.drift === '',
      'self-test: CONTROL — the unperturbed pin is clean, so the red is attributable',
      'self-test: the unperturbed pin already reported drift; the probe attributes nothing',
    );
    const m = explainVkMismatch(WANT, w.hash + 1n, resolved);
    check(
      m.includes('NOT a key this tree knows'),
      'self-test: a hash one off the pin is refused rather than waved through',
      'self-test: a drifted hash was accepted',
    );
  }
  // (c) an unknown notion id must THROW rather than silently name nothing.
  let threw = false;
  try {
    vkNotion('no-such-notion');
  } catch {
    threw = true;
  }
  check(
    threw,
    'self-test: asking for an unknown notion throws (no silent empty answer)',
    'self-test: an unknown notion resolved to something',
  );
}

console.log(
  failures === 0
    ? `\nPASS — vk-identity: ${KNOWN_VK_NOTIONS.length} notions named to the circuit each keys, ` +
        `${present.length} resolved from producers, both refusal polarities exercised` +
        (SELF_TEST ? ' (+ self-test)' : '')
    : `\nFAIL — ${failures} check(s) failed`,
);
process.exit(failures === 0 ? 0 : 1);

// STEP_MAIN SHAPE DIFF — the Lean-assembled `verify_one` against Mina's own compiled step circuit,
// by GATE-TYPE CENSUS and RUN-LENGTH PROFILE. ⚑ GREEN-OR-BUST since 2026-08-03.
//
// ## ⚑ WHAT THIS FILE WAS UNTIL TODAY, MEASURED
//
// It PRINTED TWO TABLES AND EXITED 0. No comparison, no failure counter, no verdict, and it was
// wired into no gate script — `grep -rn stepmain-shape-diff` found it in `HORIZONLOG.md` and in
// another script's docblock, nowhere else. So
//
//   HORIZONLOG:350  "all five run-length families INTACT: EndoMul 32×77 exactly Mina's …"
//   HORIZONLOG:878  "SHAPE-DIFFED against Mina's own compiled circuit … four of six families match"
//
// were A HUMAN READING TWO PRINTED TABLES. Nothing in this repository could have gone red if a
// family had stopped matching; the claim and its evidence were the same act. It is now a machine
// verdict with a red path, and it runs in `pickles-synthesis-oracles.sh`.
//
// ## THE FOUR VERDICTS, AND WHY THESE FOUR
//
// A run length is a cheap, early signal that a GADGET was mis-assembled: a Poseidon permutation is
// 11 rows, a 128-bit `Scalar_challenge.endo` is 32 `EndoMul` rows, a `var_base_mul` chunk is a lone
// `VarBaseMul` row followed by its `Zero`, a 128-bit `to_field_checked` is 8 `EndoMulScalar` rows.
// The COUNTS move with every sub-circuit the assembly gains and so are a scope statement, not a
// defect — which is exactly why "the counts matched when I looked" was never a gate. What IS
// gateable is stated below, and every reference value is read off MINA'S BLOB, never written here:
//
//   V1  RUN-LENGTH SETS.  The set of run lengths WE emit for a family ⊆ the set MINA emits for it.
//       A length upstream never produces is a gadget we assembled wrong — a Poseidon "permutation"
//       of 7 rows, a `to_field_checked` of 5. Count-free, so assembly growth cannot move it.
//   V2  SUBSET DIRECTION.  Per gadget family, our instance count ≤ Mina's. Being SHORT is scope
//       (sub-circuits not yet assembled, named in `KimchiStepMain.lean`); being LONG is not — it
//       means we emit more of a gadget than the circuit upstream contains. ⚠ `Zero` and `Generic`
//       are deliberately EXCLUDED and the exclusion is itself an entry: our σ-only probe rows are
//       standalone `Zero`s Mina has none of, and our per-site `packHalves` spends Generic rows a
//       global `pending_generic_gate` would not.
//   V3  TYPE ALPHABET.  Both sides' gate types ⊆ the seven kimchi types Mina uses, and OURS ⊆
//       MINA'S. A lookup / foreign-field / range-check gate appearing here would be a gate no Mina
//       circuit contains.
//   V4  POSEIDON PERMUTATION LENGTH.  Every Poseidon run on both sides is a multiple of 11. This is
//       the one gadget whose row count is fixed by the gate itself, and a non-multiple means two
//       permutations merged or one was truncated.
//
// ⚠ WHAT THIS STILL CANNOT SEE, so that its green is not read as more than it is: a run length
// cannot see a wrong coefficient, a wrong wire, a right-shaped gadget in the wrong place, or a
// region emitted in the wrong order. `stepmain-region-conformance.mjs` sees all four, per gate.
// This file is the cheap early signal, gated; that one is the conformance verdict.
//
// ## BOTH SIDES ARE PROVENANCE-CHECKED
//
// The MINA side is `loadCircuit('step-zkapp-proved')`, which refuses any blob whose kimchi digest is
// not the md5 o1-labs put in its own release-asset FILENAME — content-addressed, so a truncated or
// substituted blob is REFUSED, not read. (`--dump`-file arguments are gone: the argument was a
// scratch path anybody could point anywhere, and the oracle already owns a verified loader.)
//
// The LEAN side is the live `DREGG_SM=step` emission when one exists, else the COMMITTED gz fixture,
// and either way it passes `emit-provenance.mjs`'s floor: the stamped source cone must equal the
// cone of the tree right now, the artifact's own sha256 must be the one the stamp recorded, and the
// emit cone must have been COMMITTED at the stamped HEAD. A stale or unreproducible input REFUSES
// (exit 3); nothing here warns. `step-zkapp-proved` is step branch 4 — the branch that RUNS
// `verify_one`. `step-transaction` (branch 0) is instantiated with N_PREVIOUS = 0 and contains NO
// `verify_one` call at all (mina-rust `transaction.rs:4286`), so it is the wrong reference.
//
// USAGE — ⚠ every invocation is green-or-bust.
//   node scripts/stepmain-shape-diff.mjs                  # grade
//   node scripts/stepmain-shape-diff.mjs --self-test      # the red path: 4 bites + an honest anchor
//   node scripts/stepmain-shape-diff.mjs --lean <path>    # a specific rung emission
//
// EXIT: 0 conform · 1 a verdict is red · 2 usage · 3 the Lean input is stale/unreproducible.
import { existsSync, readFileSync } from 'node:fs';
import { gunzipSync } from 'node:zlib';
import { isStale, leanConeDigest, requireFreshArtifact, requireFreshFixture } from './emit-provenance.mjs';
import { loadCircuit } from './mina-canonical-circuit-oracle.mjs';

const EMIT_DRIVER = 'Dregg2/Circuit/Emit/EmitStepMainJson.lean';
const EMIT_CMD = '(cd metatheory && DREGG_SM=step lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean)';
const REFRESH_CMD = 'node scripts/stepmain-region-conformance.mjs --emit --refresh-fixture';
const LEAN_DEFAULT = '/tmp/pickles-stepmain/stepmain_step_r8_finalize.json';
// ⚑ THE SAME committed snapshot the region-conformance gate grades. Named here rather than imported
// because importing that module RUNS it (it is a gate, not a library) — the two paths are pinned by
// this comment and by `check-doc-refs.sh`, and a rename that misses one reds this file's fixture leg.
const LEAN_FIXTURE = new URL('../fixtures/stepmain-step-r8-finalize-gates.json.gz', import.meta.url);
const LEAN_FIXTURE_PROV = new URL('../fixtures/stepmain-step-r8-finalize-gates.provenance.json', import.meta.url);

// GateType declaration order == the BCS variant index (kimchi `circuits/gate.rs`). Only these seven
// appear in ANY Mina step or wrap circuit — no lookup, no foreign-field, no range-check.
const NAMES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];
// The five families whose RUN LENGTH is a gadget signature. `Zero` and `Generic` have no run-length
// meaning (a `Zero` is a ladder's second row, a probe row, or padding) and are censused only.
const GADGETS = ['Poseidon', 'EndoMul', 'EndoMulScalar', 'VarBaseMul', 'CompleteAdd'];

/** The Lean emitter's shape: `gates[i].typ` is the ORDINAL. Refused unless its emission is stamped,
 *  the stamp matches the source cone as the tree stands right now, and that cone was committed. */
function loadLean(explicit, cone) {
  const live = explicit ?? LEAN_DEFAULT;
  const haveLive = existsSync(live);
  const haveFix = existsSync(LEAN_FIXTURE);
  if (!haveLive && !haveFix)
    throw new Error(`no Lean emission: neither ${live} nor the committed fixture. Produce it with\n   ${EMIT_CMD}`);
  let j, src;
  if (haveLive) {
    requireFreshArtifact({ artifact: live, cone, emitCmd: EMIT_CMD });
    j = JSON.parse(readFileSync(live, 'utf8')); src = live;
  } else {
    requireFreshFixture({ fixture: LEAN_FIXTURE, sidecar: LEAN_FIXTURE_PROV, cone, emitCmd: EMIT_CMD, refreshCmd: REFRESH_CMD });
    j = JSON.parse(gunzipSync(readFileSync(LEAN_FIXTURE)).toString('utf8')); src = 'committed fixture';
  }
  return { name: j.name, pub: j.public_input_size, gates: j.gates.map((g) => NAMES[g.typ]), src };
}

const histogram = (gs) => gs.reduce((h, g) => ((h[g] = (h[g] ?? 0) + 1), h), {});

/** Maximal runs of one gate type, as a `length -> count` map. This is the fidelity signal. */
function runLengths(gs, kind) {
  const c = new Map();
  let n = 0;
  for (const g of gs) {
    if (g === kind) n++;
    else if (n) { c.set(n, (c.get(n) ?? 0) + 1); n = 0; }
  }
  if (n) c.set(n, (c.get(n) ?? 0) + 1);
  return c;
}
const fmtRuns = (c) => [...c.entries()].sort((a, b) => b[1] - a[1]).map(([k, v]) => `${k}x${v}`).join(' ') || '—';

// ── the verdict ───────────────────────────────────────────────────────────────────────────────────
/** Returns `{ pass:[], fail:[] }`. Every reference value is read off MINA'S gate list. */
export function grade(mina, lean) {
  const pass = [], fail = [];
  const check = (name, ok, detail) => (ok ? pass : fail).push({ name, detail });

  const hm = histogram(mina.gates), hl = histogram(lean.gates);

  // V3 — the type alphabet, both directions.
  const tm = [...new Set(mina.gates)].sort(), tl = [...new Set(lean.gates)].sort();
  check('V3 types/mina-are-the-seven', tm.every((t) => NAMES.includes(t)),
    `mina emits {${tm.join(',')}}`);
  check('V3 types/lean-are-the-seven', tl.every((t) => NAMES.includes(t)),
    `lean emits {${tl.join(',')}}`);
  check('V3 types/lean-subset-of-mina', tl.every((t) => tm.includes(t)),
    `${tl.filter((t) => !tm.includes(t)).join(',') || 'none'} outside Mina's alphabet`);

  for (const k of GADGETS) {
    const rm = runLengths(mina.gates, k), rl = runLengths(lean.gates, k);
    // V1 — a run length upstream never emits is a mis-assembled gadget. Count-free.
    const alien = [...rl.keys()].filter((n) => !rm.has(n)).sort((a, b) => a - b);
    check(`V1 runlen/${k}/lengths-mina-also-emits`, alien.length === 0,
      alien.length ? `⚑ lengths Mina NEVER emits: ${alien.map((n) => `${n}x${rl.get(n)}`).join(' ')}   (mina emits {${[...rm.keys()].sort((a, b) => a - b).join(',')}})`
                   : `{${[...rl.keys()].sort((a, b) => a - b).join(',') || '—'}} ⊆ {${[...rm.keys()].sort((a, b) => a - b).join(',') || '—'}}`);
    // V2 — short is scope, long is a defect.
    const cm = hm[k] ?? 0, cl = hl[k] ?? 0;
    check(`V2 census/${k}/lean-does-not-exceed-mina`, cl <= cm,
      `lean ${cl} rows ${cl <= cm ? '≤' : '⚑ >'} mina ${cm}${cl < cm ? `   (short by ${cm - cl} — SCOPE, see KimchiStepMain.lean's named simplifications)` : ''}`);
  }

  // V4 — a Poseidon run that is not a multiple of 11 is not a permutation.
  for (const [side, c] of [['mina', mina], ['lean', lean]]) {
    const bad = [...runLengths(c.gates, 'Poseidon').keys()].filter((n) => n % 11 !== 0);
    check(`V4 poseidon/${side}/runs-are-whole-permutations`, bad.length === 0,
      bad.length ? `⚑ run lengths ${bad.join(',')} are not multiples of 11` : 'every run is a multiple of 11');
  }

  return { pass, fail };
}

function report(c, label) {
  const h = histogram(c.gates);
  const tot = c.gates.length;
  console.log(`\n=== ${label}: ${c.name} — ${tot} gates, public_input_size ${c.pub} ===`);
  for (const k of NAMES) {
    if (!h[k]) continue;
    console.log(`   ${k.padEnd(14)} ${String(h[k]).padStart(6)}  ${(100 * h[k] / tot).toFixed(1)}%`);
  }
  console.log(`   ${'non-Generic'.padEnd(14)} ${String(tot - (h.Generic ?? 0)).padStart(6)}`);
  for (const k of GADGETS) if (h[k]) console.log(`   runlen ${k.padEnd(14)} ${fmtRuns(runLengths(c.gates, k))}`);
}

// ── ⚑ THE RED PATH ────────────────────────────────────────────────────────────────────────────────
/**
 * Each bite must make a NAMED verdict go red, and the ANCHOR must stay green — a gate that reds on
 * everything proves nothing, and a gate whose green survives a bent gadget is the thing this file
 * was. It needs NO Lean emission: the honest candidate is MINA'S OWN gate list, which conforms to
 * itself by construction, so the bites measure the verdicts and not the assembly.
 */
function selfTest(mina) {
  const asLean = (gates) => ({ name: 'self-test', pub: mina.pub, gates });
  let bad = 0;
  const leg = (label, gates, expectRed) => {
    const { fail } = grade(mina, asLean(gates));
    const red = fail.length > 0;
    const ok = red === expectRed;
    if (!ok) bad++;
    console.log(`   ${ok ? 'ok  ' : 'RED '} ${label.padEnd(58)} ${red ? `RED (${fail.map((f) => f.name).join(', ')})` : 'green'}`);
  };
  console.log('── stepmain-shape-diff --self-test (the four verdicts must bite) ──');
  // (A0) THE ANCHOR — Mina's own gate list graded as the candidate must be GREEN.
  leg('A0 anchor: Mina\'s own gate list as the candidate', [...mina.gates], false);
  // (B1) V1: split a Poseidon permutation in the middle → runs of 4 and 6, lengths Mina never emits.
  leg('B1 a Poseidon permutation split by a retyped row', (() => {
    const g = [...mina.gates]; const i = g.indexOf('Poseidon'); g[i + 4] = 'Zero'; return g;
  })(), true);
  // (B2) V2: duplicate every EndoMul row → our count exceeds the circuit's.
  leg('B2 more EndoMul rows than the circuit contains', (() => {
    const g = []; for (const x of mina.gates) { g.push(x); if (x === 'EndoMul') g.push(x); } return g;
  })(), true);
  // (B3) V3: a gate type no Mina circuit has.
  leg('B3 a gate type outside the seven (a lookup gate)', (() => {
    const g = [...mina.gates]; g[g.length - 1] = 'Lookup'; return g;
  })(), true);
  // (B4) V4: one Poseidon row deleted → a 10-row "permutation".
  leg('B4 one Poseidon row deleted → a 10-row permutation', (() => {
    const g = [...mina.gates]; g.splice(g.indexOf('Poseidon'), 1); return g;
  })(), true);
  console.log();
  if (bad) { console.log(`stepmain-shape-diff --self-test: ${bad} LEG(S) FAILED`); process.exit(1); }
  console.log('stepmain-shape-diff --self-test: 5 legs green (1 anchor + 4 bites, each reddening a named verdict)');
}

// ── main ──────────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const arg = (f) => { const i = argv.indexOf(f); return i >= 0 ? argv[i + 1] : undefined; };
if (argv.some((a) => a.endsWith('.json') && !argv.includes('--lean')))
  console.error('note: positional dump paths are gone — the Mina side is loaded (and md5-verified) by '
    + 'mina-canonical-circuit-oracle.mjs, and the Lean side by --lean <path> or the provenance floor.');

const { spec, publicInputSize, gates: minaGates } = await loadCircuit('step-zkapp-proved');
const mina = { name: spec.stem.slice(0, 44), pub: publicInputSize, gates: minaGates.map((g) => g.typ) };

if (argv.includes('--self-test')) { selfTest(mina); if (argv.length === 1) process.exit(0); }

let lean;
try {
  const cone = leanConeDigest(EMIT_DRIVER);
  lean = loadLean(arg('--lean'), cone);
} catch (e) {
  // REFUSE, DO NOT WARN — a stale run-length table is how "five families match" becomes a claim
  // about a circuit nobody emitted.
  console.error(`\n${e.message}\n`);
  process.exit(isStale(e) ? 3 : 1);
}

report(mina, 'MINA');
report(lean, `LEAN (${lean.src})`);

const { pass, fail } = grade(mina, lean);
console.log('\n── VERDICTS (every reference value read off Mina\'s blob) ──');
for (const p of pass) console.log(`   ok   ${p.name.padEnd(46)} ${p.detail}`);
for (const f of fail) console.log(`   RED  ${f.name.padEnd(46)} ${f.detail}`);
if (fail.length) {
  console.log(`\nstepmain-shape-diff: ${fail.length} VERDICT(S) RED over ${pass.length + fail.length}`);
  console.log('A run-length divergence is a MIS-ASSEMBLED GADGET; a count shortfall is a scope statement and');
  console.log('is not graded as one. Read KimchiStepMain.lean\'s named-simplifications list before calling a');
  console.log('SHORTFALL a bug — but a length Mina never emits, or a count that EXCEEDS Mina\'s, is not that.');
  process.exit(1);
}
console.log(`\nstepmain-shape-diff: ${pass.length}/${pass.length} verdicts conform `
  + `(${GADGETS.length} run-length families ⊆ Mina's, ${GADGETS.length} counts ≤ Mina's, the type alphabet, and whole Poseidon permutations)`);

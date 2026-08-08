// WRAP_MAIN SHAPE DIFF — the Lean-assembled `wrap_main` against Mina's own compiled
// `wrap-transaction`, by GATE-TYPE CENSUS and RUN-LENGTH FAMILY, as a RATCHET.
//
// ## ⚑ WHAT THIS FILE REPLACES, AND WHY IT IS A GATE AND NOT A TABLE
//
// This census — "what percentage of Mina's wrap circuit do we emit?" — is the project's actual
// scoreboard for the Pickles-in-Lean epoch, and until this file existed it was a `census.py` in a
// scratchpad directory, re-typed by hand each session. Two figures got quoted through 2026-08-04
// in a way the numbers do not support, and both are the shape a hand-read table produces:
//
//   * "`EndoMul 32×77`, exactly Mina's" quoted about the WRAP. ⚑ VERIFIED AT SOURCE: `32×77` is a
//     true and correctly-scoped result about the STEP circuit — `KimchiStepMain.lean:203` measures
//     ours at 2464 = `32×77` against Mina's step `32×77 + 1×1` — and every occurrence in the tree
//     sits in a step context. It is a CROSS-CIRCUIT error, not a false step claim. Mina's
//     `wrap-transaction` carries **79** runs of 32 `EndoMul` rows, and this assembly carried
//     **ZERO** of them until W-COMBINE and W-BULLET landed. 77 is a number about a different
//     circuit and it never belonged in a wrap sentence.
//   * "Poseidon 89/89, 100%" quoted as COVERAGE. 89 was the count of 11-row Poseidon blocks the
//     assembly emitted at `w9_prev`; `89/89` was PER-INSTANCE internal-row identity of the blocks
//     we do emit — a different measurement with a different denominator. Mina's wrap has **261**
//     permutations, so coverage was 34%. `KimchiWrapMain.lean`'s §1 header already carries this
//     correction in prose; this file makes it mechanical, which prose cannot be.
//
// So every line here that could be read as coverage NAMES BOTH SIDES and names the denominator, and
// both figures are printed with their correction attached. A number without a denominator, or a
// number from the neighbouring circuit, is how each of those went wrong.
//
// ## ⚑ THERE IS NO SINGLE ARTIFACT THAT HOLDS ALL 15 RUNGS — THE ASSEMBLY IS BUILT HERE
//
// `KimchiWrapMain.lean`'s `rungsUpto` is a TREE, not a chain: three branches hang off `w9_prev`.
//
//     w9_prev ─┬─ w10_finalize ── w11_finsponge         (finalize_other_proof, wrap_main.ml:329)
//              ├─ w11_wraphack ── w12_close             (hash_messages_for_next_wrap_proof, :340)
//              └─ w10_combine  ── w11_bullet            (Split_commitments.combine + bullet_reduce)
//
// so `wrapmain_wrap_w11_bullet.json` is NOT the whole circuit — it is `w9_prev + combine + bullet`
// and contains none of finalize/finsponge/wraphack/close. Censusing any ONE emitted file against
// Mina's blob UNDERSTATES the assembly, and censusing the sum of the files DOUBLE-COUNTS `w9_prev`
// six times.
//
// This file assembles the union by PREFIX-STRIPPING and VERIFIES the prefix relation on the emitted
// bytes — `(typ, coeffs)` per row, not on the `rfl` theorem that motivates it. A branch whose body
// is not its base's body plus a suffix is a BLOCKED run (exit 3), because it means the seven files
// on disk are not one emission.
//
// ⚠ THE ASSEMBLY ORDER ACROSS BRANCHES IS DECLARED, NOT DERIVED — `wrap_main.ml` runs the branches
// but nothing in the emission fixes their relative order. It matters only where two segments would
// MERGE a run at the seam, so the gate MEASURES the seams and prints them: every cross-branch seam
// is `Zero → Generic` (distinct), which makes the run-length multiset order-independent. If a future
// assembly ever seams two like types, that line says so and the families become order-dependent.
//
// ## THE RATCHET
//
// R1  GATE-TYPE DELTA.  Per kimchi gate type, `|ours − mina|` against the baseline. It may SHRINK,
//     never GROW. A shrink is a STALE ROW and is also red — that is what makes the census MONOTONE
//     rather than merely non-increasing, and it is the only thing that forces a win to be RECORDED.
// R2  RUN-LENGTH FAMILY DELTA.  Same, per `typ × length` family. A family with a nonzero delta and
//     NO baseline row is a NEW DIVERGENT FAMILY and is red — that is the gadget-mis-assembly signal
//     (a Poseidon "permutation" of 7 rows, a `CompleteAdd` batch of 18 where Mina batches 2 and 3).
// R3  OVERSHOOT.  `ours > mina` on any family is printed in its own section every run. Being SHORT
//     is scope; being LONG means we emit more of a gadget than the circuit upstream contains.
//
// ⚠ FAIL-CLOSED, AND `3` IS NOT `1`. A missing rung, an emission whose provenance stamp does not
// match the source cone as the tree stands right now, a broken prefix relation, or a census that
// observed too little to be a census, all exit **3 (BLOCKED)** — the diff DID NOT RUN. A ratchet
// violation exits **1 (RED)**. Collapsing those into one line is what makes an unactionable red that
// readers learn to skip; `local-gates.sh` and `pickles-synthesis-oracles.sh` both name them apart.
//
// USAGE — every invocation is green-or-bust.
//   node scripts/wrapmain-shape-diff.mjs                     # grade against the committed baseline
//   node scripts/wrapmain-shape-diff.mjs --self-test         # the red path; needs NO Lean emission
//   node scripts/wrapmain-shape-diff.mjs --report            # print the census, grade, still exits
//   node scripts/wrapmain-shape-diff.mjs --update-baseline   # record a WIN (refuses on growth)
//   node scripts/wrapmain-shape-diff.mjs --update-baseline --accept-growth
//
// EXIT: 0 conform · 1 a ratchet row is red · 2 usage · 3 BLOCKED (input absent/stale/inconsistent).
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { isStale, leanConeDigest, requireFreshArtifact } from './emit-provenance.mjs';
import { loadCircuit } from './mina-canonical-circuit-oracle.mjs';

const EMIT_DRIVER = 'Dregg2/Circuit/Emit/EmitWrapMainJson.lean';
const EMIT_CMD = '(cd metatheory && DREGG_WM=wrap lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean)';
const EMIT_DIR = process.env.DREGG_WM_OUT ?? '/tmp/pickles-wrapmain';
const BASELINE = new URL('../fixtures/wrapmain-wrap-census-baseline.json', import.meta.url);
const BASELINE_SCHEMA = 'wrapmain-wrap-census/1';

// GateType declaration order == the BCS variant index (kimchi `circuits/gate.rs`). Only these seven
// appear in ANY Mina step or wrap circuit.
const NAMES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];
const ORDER = ['Poseidon', 'EndoMul', 'EndoMulScalar', 'VarBaseMul', 'CompleteAdd', 'Generic', 'Zero'];

// ⚑ ALL FIFTEEN. The freshness floor runs over every one of them, so an emission that stopped at
// rung 9 BLOCKS instead of grading a nine-rung assembly as though it were the circuit.
// ⚑ `w11_finsponge` (2026-08-05) is the fifteenth: `finalize_other_proof`'s SPONGE half, which hangs
// off `w10_finalize` and carries the two `finalize` sponges — the largest single Poseidon family
// left. It is a `Rung` constructor with a `rungOwn` arm AND an emitted artifact; before it existed
// this list had fourteen entries and a census that omitted it read 122 Poseidon blocks short.
const RUNGS = ['w1_transcript', 'w2_challenges', 'w3_branch', 'w4_bind', 'w5_key', 'w6_xhat',
  'w7_split', 'w8_ftcomm', 'w9_prev', 'w10_finalize', 'w11_finsponge', 'w11_wraphack', 'w12_close',
  'w10_combine', 'w11_bullet'];
// The union, as `rungsUpto` defines it. `base` is the rung whose body must be a PREFIX of this one's;
// the difference is this rung's own row-set, and the union is the base plus every own-set exactly once.
const TRUNK = 'w9_prev';
const BRANCHES = [
  { tag: 'w10_finalize', base: TRUNK },
  { tag: 'w11_finsponge', base: 'w10_finalize' },
  { tag: 'w11_wraphack', base: TRUNK },
  { tag: 'w12_close', base: 'w11_wraphack' },
  { tag: 'w10_combine', base: TRUNK },
  { tag: 'w11_bullet', base: 'w10_combine' },
];

class Blocked extends Error { constructor(m) { super(m); this.blocked = true; } }
const block = (m) => { throw new Blocked(m); };

/**
 * ⚑ THE PI DENOMINATOR IS READ, NOT RE-TYPED. `24` written here would be a constant beside its own
 * definition. This counts the slots in `KimchiWrapMain.lean`'s `WRAP_PINNED_SLOTS` — which is itself
 * annotated slot-by-slot with the `wrap_verifier.ml` / `wrap_main.ml` line that pins each one — and
 * REFUSES on any list form it does not understand rather than falling back to a number.
 */
function pinnedWordsFromLean() {
  const src = new URL('../../../metatheory/Dregg2/Circuit/Emit/KimchiWrapMain.lean', import.meta.url);
  if (!existsSync(src)) block(`cannot read ${fileURLToPath(src)} — the PI denominator has no source.`);
  const text = readFileSync(src, 'utf8');
  const i = text.indexOf('def WRAP_PINNED_SLOTS');
  if (i < 0) block('KimchiWrapMain.lean no longer defines WRAP_PINNED_SLOTS — the PI denominator moved.');
  const body = text.slice(text.indexOf(':=', i) + 2, text.indexOf('\ndef ', i));
  let n = 0;
  for (const raw of body.split('++')) {
    const term = raw.replace(/--[^\n]*/g, '').trim();
    if (!term) continue;
    let m = /^\[\s*([0-9]+(?:\s*,\s*[0-9]+)*)\s*\]$/.exec(term);
    if (m) { n += m[1].split(',').length; continue; }
    m = /^\(List\.range\s+([0-9]+)\)\.map/.exec(term);
    if (m) { n += Number(m[1]); continue; }
    block(`WRAP_PINNED_SLOTS carries a term this gate cannot count: ${term.slice(0, 60)}… — refusing rather than guessing the PI denominator.`);
  }
  if (n < 1) block('WRAP_PINNED_SLOTS counted 0 slots — a blinded read must not become a PI denominator.');
  return n;
}

// ── loading ───────────────────────────────────────────────────────────────────────────────────────
/** One emitted rung as `{pub, rows}` where a row is `typ|coeffs` — enough to verify the prefix
 *  relation on CONTENT and not merely on length. */
function loadRung(tag) {
  const p = `${EMIT_DIR}/wrapmain_wrap_${tag}.json`;
  if (!existsSync(p)) block(`no ${p} — the wrap emission is absent or incomplete.\n   emit it:  ${EMIT_CMD}`);
  const j = JSON.parse(readFileSync(p, 'utf8'));
  if (j.name !== `wrapmain_wrap_${tag}`)
    block(`${p} names itself "${j.name}" but this gate asked for wrapmain_wrap_${tag} — a file from a `
      + `different shape or rung is sitting under this name.`);
  // ⚑⚑ THE σ-ONLY PROBE ROWS ARE THIS ASSEMBLY'S INSTRUMENT AND ARE SPLICED OUT BEFORE ANY COUNT.
  // ⚠ 2026-08-04, MEASURED AND FIXED. Until now this mapped `j.gates` straight through, so every
  // number this file produced — the coverage headline, `gate_type_delta`, `run_length_delta`, and
  // the committed `wrapmain-wrap-census-baseline.json` — counted 323 rows that `KimchiWrapMain.lean`
  // declares are OURS and that `wrap_main` has none of (`:714`, "A σ-ONLY PROBE: a standalone `Zero`
  // row"). The instrument was measuring itself.
  // The loudest consequence was a divergence that did not exist. This file reported 137 consecutive-
  // `Zero` runs of length >= 2 against Mina's 0 and called it the largest structural gap left, under
  // a line (`:320`) that ALREADY said "ours are the sigma-only probe rows". Splice them and the
  // count is {} — EXACTLY Mina's. Every one of the 137 was a probe row landing beside a gadget's
  // closing `Zero`; not one was an extra `Zero` the assembly emits.
  // The sibling gate `wrapmain-region-conformance.mjs` has always spliced them (`normalizeLean`),
  // so the two files disagreed about what a row IS. They agree now.
  const probe = new Set(j.probe_rows ?? []);
  if ([...probe].some((i) => i < j.public_input_size))
    block(`${p}: a probe row sits inside the public block — splicing would move the PI width.`);
  const rows = j.gates
    .filter((_, i) => !probe.has(i))
    .map((g) => `${typeof g.typ === 'number' ? NAMES[g.typ] : g.typ}|${(g.coeffs ?? []).join(',')}`);
  return { pub: j.public_input_size, rows, path: p, probes: probe.size };
}

const typeOf = (row) => row.slice(0, row.indexOf('|'));

/**
 * ⚑ THE UNION. Returns `{ gates, pub, segments, seams }`, or BLOCKS.
 *
 * Each branch body must be its base's body plus a suffix, verified row by row on `(typ, coeffs)`.
 * The public rows are taken from the rung that pins the MOST statement words — that rung's emitted
 * file already carries them contiguously ahead of the same trunk body, so the assembly is a
 * rearrangement of measured segments and never a synthesised row.
 */
function assemble(rungs) {
  const body = (tag) => rungs[tag].rows.slice(rungs[tag].pub);
  const own = {};
  for (const { tag, base } of BRANCHES) {
    const b = body(base), t = body(tag);
    if (t.length < b.length || b.some((r, i) => r !== t[i]))
      block(`⚑ ASSEMBLY REFUSED: ${tag}'s body is not ${base}'s body plus a suffix. `
        + `${base} ${b.length} rows, ${tag} ${t.length}; first divergence at row `
        + `${b.findIndex((r, i) => r !== t[i])}. These files are not one emission — re-emit all `
        + `fourteen rungs in one run:\n   ${EMIT_CMD}`);
    own[tag] = t.slice(b.length);
  }
  // The rung pinning the MOST statement words, taking the LAST such in schedule order so the public
  // block is named by the deepest rung that carries it.
  const pubTag = RUNGS.reduce((a, t) => (rungs[t].pub >= rungs[a].pub ? t : a), TRUNK);
  const segments = [
    { name: 'pub', rows: rungs[pubTag].rows.slice(0, rungs[pubTag].pub) },
    { name: TRUNK, rows: body(TRUNK) },
    ...BRANCHES.map(({ tag }) => ({ name: `${tag}/own`, rows: own[tag] })),
  ];
  for (const s of segments) if (!s.rows.length) block(`⚑ ASSEMBLY REFUSED: segment ${s.name} is EMPTY — a census over it would report a shape nothing emits.`);
  // ⚠ THE SEAMS ARE MEASURED, NOT ASSUMED, AND HALF OF THEM ARE NOT SEAMS AT ALL. A junction is REAL
  // when some single emitted rung already carries those two segments adjacent — `w12_close` IS
  // `pub ++ w9_prev ++ wraphack/own ++ close/own` on disk. Only a SYNTHETIC junction (one this file
  // creates by choosing an order across branches) could make the family table order-dependent, and
  // only if its two sides carry the SAME gate type, which would MERGE two runs into one.
  const chains = { [TRUNK]: ['pub', TRUNK] };
  for (const { tag, base } of BRANCHES) chains[tag] = [...chains[base], `${tag}/own`];
  const realPairs = new Set(Object.values(chains).flatMap((c) => c.slice(1).map((x, i) => `${c[i]}→${x}`)));
  const seams = [];
  for (let i = 0; i + 1 < segments.length; i++) {
    const a = typeOf(segments[i].rows.at(-1)), b = typeOf(segments[i + 1].rows[0]);
    seams.push({
      from: segments[i].name, to: segments[i + 1].name, a, b, merges: a === b,
      real: realPairs.has(`${segments[i].name}→${segments[i + 1].name}`),
    });
  }
  return { gates: segments.flatMap((s) => s.rows).map(typeOf), pub: rungs[pubTag].pub, segments, seams, pubTag };
}

// ── census ────────────────────────────────────────────────────────────────────────────────────────
const histogram = (gs) => gs.reduce((h, g) => ((h[g] = (h[g] ?? 0) + 1), h), {});

/** Maximal runs as `"typ x len" -> count`. The family table; a gadget signature. */
function families(gs) {
  const f = new Map();
  let cur = null, n = 0;
  const flush = () => { if (cur !== null) f.set(`${cur} x ${n}`, (f.get(`${cur} x ${n}`) ?? 0) + 1); };
  for (const g of gs) { if (g === cur) n++; else { flush(); cur = g; n = 1; } }
  flush();
  return f;
}

/** `key -> ours - mina`, restricted to the keys where they DISAGREE. This is the ratchet's subject. */
function deltas(ours, mina) {
  const d = {};
  for (const k of new Set([...ours.keys(), ...mina.keys()])) {
    const v = (ours.get(k) ?? 0) - (mina.get(k) ?? 0);
    if (v !== 0) d[k] = v;
  }
  return d;
}

// ── the ratchet ───────────────────────────────────────────────────────────────────────────────────
/**
 * Grade `now` (a `{gate_type_delta, run_length_delta}` pair) against `base`. Returns
 * `{ grew, stale, novel, ok }` — each a list of `{key, was, is}` — and NEVER prints. A row may
 * SHRINK toward zero (that is the whole point) but the baseline must then RECORD it, so a shrink is
 * `stale` and red: a census that ratchets in one direction only is a census whose numbers are
 * always the last measurement, not the best one somebody once saw.
 */
export function ratchet(now, base) {
  const grew = [], stale = [], novel = [], ok = [];
  for (const bucket of ['gate_type_delta', 'run_length_delta']) {
    const n = now[bucket] ?? {}, b = base[bucket] ?? {};
    for (const k of Object.keys(n)) {
      const key = `${bucket === 'gate_type_delta' ? 'type' : 'family'}/${k}`;
      if (!(k in b)) { novel.push({ key, was: 0, is: n[k] }); continue; }
      if (Math.abs(n[k]) > Math.abs(b[k])) grew.push({ key, was: b[k], is: n[k] });
      else if (Math.abs(n[k]) < Math.abs(b[k])) stale.push({ key, was: b[k], is: n[k] });
      else ok.push({ key, was: b[k], is: n[k] });
    }
    for (const k of Object.keys(b)) {
      if (k in n) continue;
      const key = `${bucket === 'gate_type_delta' ? 'type' : 'family'}/${k}`;
      // The row went to ZERO — it CONFORMS now. Still stale: the baseline must say so.
      stale.push({ key, was: b[k], is: 0 });
    }
  }
  return { grew, stale, novel, ok };
}

// ── reporting ─────────────────────────────────────────────────────────────────────────────────────
function pct(a, b) { return b ? `${(100 * a / b).toFixed(1)}%` : '--'; }

function report(ours, mina, asm, WRAP_PINNED_WORDS) {
  const ho = histogram(ours.gates), hm = histogram(mina.gates);
  console.log(`\n╔═ WRAP_MAIN SHAPE DIFF — the 14-rung Lean assembly vs Mina's compiled wrap-transaction`);
  console.log(`║  OURS   ${asm.segments.map((s) => `${s.name} ${s.rows.length}`).join(' + ')}`);
  console.log(`║         = ${ours.gates.length} gates, public_input_size ${ours.pub}   (from ${EMIT_DIR}, all 14 rungs provenance-checked)`);
  console.log(`║  MINA   ${mina.name} — ${mina.gates.length} gates, public_input_size ${mina.pub}`);
  console.log(`╚═ ⚠ byte-equality with THIS blob is unreachable even complete: wrap_main.ml:215-219 bakes the`);
  console.log(`   per-branch step VK commitments as \`Inner_curve.constant\`, so the Generic stream is per-zkApp.`);
  console.log(`   The reachable target is the NON-GENERIC stream, identical across both compiled wrap blobs.\n`);

  const row = (label, o, m) => console.log(label.padEnd(16) + String(o).padStart(8) + String(m).padStart(8)
    + `${o - m >= 0 ? '+' : ''}${o - m}`.padStart(9) + pct(o, m).padStart(11));
  console.log('GATE-TYPE CENSUS   ⚑ "% of mina" is OUR count over MINA\'S — a coverage figure, both sides named.');
  console.log('gate type'.padEnd(16) + 'ours'.padStart(8) + 'mina'.padStart(8) + 'delta'.padStart(9) + '% of mina'.padStart(11));
  console.log('-'.repeat(52));
  for (const g of ORDER) row(g, ho[g] ?? 0, hm[g] ?? 0);
  for (const g of [...new Set([...Object.keys(ho), ...Object.keys(hm)])].sort())
    if (!ORDER.includes(g)) console.log(`${g.padEnd(16)}${String(ho[g] ?? 0).padStart(8)}${String(hm[g] ?? 0).padStart(8)}   ⚑ OUTSIDE MINA'S SEVEN`);
  console.log('-'.repeat(52));
  row('TOTAL', ours.gates.length, mina.gates.length);
  row('non-Generic', ours.gates.length - (ho.Generic ?? 0), mina.gates.length - (hm.Generic ?? 0));
  row('non-Generic/Zero', ours.gates.length - (ho.Generic ?? 0) - (ho.Zero ?? 0),
    mina.gates.length - (hm.Generic ?? 0) - (hm.Zero ?? 0));
  // ⚑ PI AGAINST THE RIGHT DENOMINATOR, AND THERE ARE TWO OF THEM. `WRAP_PRIMARY_LEN = 40` is the
  // statement WIDTH; upstream's `wrap_main` pins only 24 of those slots and the other sixteen are
  // deferred values it passes through unchecked (0–4, 9), `Spec.T.Constant` padding (30–37) and the
  // dead lookup `Opt` (38–39) — all sixteen ZERO in a real devnet wrap proof. The in-tree slot-by-slot
  // census is `KimchiWrapMain.lean`'s `WRAP_PINNED_SLOTS` / `WRAP_UNPINNED`, read at source there.
  // ⚠ "PI 23 of 40" read the width as the target and made sixteen unpinnable slots look like a to-do list.
  row('PI (pinned)', ours.pub, WRAP_PINNED_WORDS);
  console.log(`${'PI (width)'.padEnd(16)}${String(ours.pub).padStart(8)}${String(mina.pub).padStart(8)}`
    + `${(ours.pub - mina.pub).toString().padStart(9)}      ⚠ ${mina.pub - WRAP_PINNED_WORDS} of Mina's ${mina.pub} slots are pinned by NOTHING upstream`);

  const fo = families(ours.gates), fm = families(mina.gates);
  const keys = [...new Set([...fo.keys(), ...fm.keys()])].sort((x, y) => {
    const [tx, lx] = x.split(' x '), [ty, ly] = y.split(' x ');
    return (ORDER.indexOf(tx) - ORDER.indexOf(ty)) || (+ly - +lx);
  });
  console.log(`\nRUN-LENGTH FAMILIES   ⚑ each row is OURS against MINA'S. Neither column alone is a result.`);
  console.log(`${'family (typ x len)'.padEnd(28)}${'ours'.padStart(8)}${'mina'.padStart(8)}${'delta'.padStart(9)}`);
  console.log('-'.repeat(53));
  for (const k of keys) {
    const o = fo.get(k) ?? 0, m = fm.get(k) ?? 0;
    console.log(`${k.padEnd(28)}${String(o).padStart(8)}${String(m).padStart(8)}${((o - m >= 0 ? '+' : '') + (o - m)).padStart(9)}`);
  }

  // ── the three lines that exist because a hand-read table got them wrong ──────────────────────
  const g = (f, k) => f.get(k) ?? 0;
  console.log('\n⚑ THE FIGURES THAT WERE MISQUOTED — printed with BOTH sides so they cannot be read as one:');
  console.log(`   EndoMul x 32   ours ${g(fo, 'EndoMul x 32')}  ·  mina ${g(fm, 'EndoMul x 32')}   `
    + `${g(fo, 'EndoMul x 32') === g(fm, 'EndoMul x 32') ? 'CONFORMS' : `DIVERGES by ${g(fo, 'EndoMul x 32') - g(fm, 'EndoMul x 32')}`}`);
  console.log(`     ⚠ THE WRAP NUMBER IS ${g(fm, 'EndoMul x 32')}, NOT 77. "EndoMul 32x77 exactly Mina's" is a true STEP result`);
  console.log('       (KimchiStepMain.lean:203 — ours 2464 = 32x77 vs Mina\'s step 32x77 + 1x1) and quoting it about');
  console.log('       the wrap crosses circuits. This assembly emitted ZERO 32-blocks until W-COMBINE and W-BULLET.');
  const po = g(fo, 'Poseidon x 11'), pm = g(fm, 'Poseidon x 11');
  console.log(`   Poseidon permutations (11-row blocks)   ours ${po}  ·  mina ${pm}   COVERAGE ${pct(po, pm)}`);
  console.log('     ⚠ NOT "89/89, 100%". That figure was PER-INSTANCE internal-row identity of the blocks we do');
  console.log('       emit — a different measurement, with a different denominator, and never coverage.');
  const zo = [...fo.entries()].filter(([k]) => k.startsWith('Zero x ') && +k.split(' x ')[1] >= 2);
  const zm = [...fm.entries()].filter(([k]) => k.startsWith('Zero x ') && +k.split(' x ')[1] >= 2);
  console.log(`   consecutive-Zero runs (len >= 2)   ours ${zo.reduce((s, [, v]) => s + v, 0)} runs `
    + `[${zo.map(([k, v]) => `${k}: ${v}`).join(', ') || 'none'}]  ·  mina ${zm.reduce((s, [, v]) => s + v, 0)} runs `
    + `[${zm.map(([k, v]) => `${k}: ${v}`).join(', ') || 'none'}]`);
  console.log('     Mina\'s wrap has NO two consecutive Zero rows anywhere, and neither do we — the 137 runs');
  console.log('     this line used to report were the sigma-only probe rows, which are now spliced in loadRung.');

  // R3 — OVERSHOOT, its own section every run.
  const over = keys.map((k) => [k, (fo.get(k) ?? 0) - (fm.get(k) ?? 0)]).filter(([, d]) => d > 0);
  console.log(`\nR3 OVERSHOOT (ours > mina) — being SHORT is scope; being LONG is not:`);
  console.log(`   ${over.map(([k, d]) => `${k} +${d}`).join(' · ') || 'none'}`);

  console.log('\nSEAMS across the assembled segments. A REAL junction is one some emitted rung already carries');
  console.log('adjacent; only a SYNTHETIC one that MERGES (both sides the same type) makes the family table');
  console.log('order-dependent, and that combination is the one to watch for:');
  for (const s of asm.seams)
    console.log(`   ${s.from.padEnd(16)} …${s.a.padEnd(14)} | ${s.b.padEnd(14)} ${s.to.padEnd(16)} `
      + `${s.real ? 'REAL     ' : 'SYNTHETIC'} ${s.merges ? 'MERGE' : 'distinct'}`
      + `${!s.real && s.merges ? '   ⚠ ORDER-DEPENDENT' : ''}`);
  const dep = asm.seams.filter((s) => !s.real && s.merges).length;
  console.log(`   => ${dep === 0 ? 'no synthetic seam merges: the run-length multiset is ORDER-INDEPENDENT across the branches.'
    : `⚠ ${dep} synthetic seam(s) merge — the family table depends on the declared branch order.`}`);
  return { gate_type_delta: deltas(new Map(Object.entries(ho)), new Map(Object.entries(hm))), run_length_delta: deltas(fo, fm) };
}

// ── ⚑ THE RED PATH ────────────────────────────────────────────────────────────────────────────────
/**
 * Needs NO Lean emission and touches no file: the honest candidate is MINA'S OWN gate list, which
 * conforms to itself by construction, so each bite measures the RATCHET and not the assembly.
 */
function selfTest(mina) {
  let bad = 0;
  const leg = (label, ok, detail) => { if (!ok) bad++; console.log(`   ${ok ? 'ok  ' : 'RED '} ${label.padEnd(60)} ${detail}`); };
  console.log('── wrapmain-shape-diff --self-test (the ratchet and the assembly floor must bite) ──');

  const census = (gates) => ({
    gate_type_delta: deltas(new Map(Object.entries(histogram(gates))), new Map(Object.entries(histogram(mina.gates)))),
    run_length_delta: deltas(families(gates), families(mina.gates)),
  });
  const anchor = census(mina.gates);                       // conforms to itself: every delta is 0
  const short = census(mina.gates.slice(0, -400));         // a real, divergent candidate
  const shortBase = census(mina.gates.slice(0, -400));

  // (A0) THE ANCHOR — a candidate at its own baseline is GREEN, or the gate reds on everything.
  let r = ratchet(anchor, anchor);
  leg('A0 anchor: a census graded against ITSELF', r.grew.length + r.stale.length + r.novel.length === 0, 'green');
  r = ratchet(short, shortBase);
  leg('A1 anchor: a DIVERGENT census at its own baseline', r.grew.length + r.stale.length + r.novel.length === 0,
    `${Object.keys(short.gate_type_delta).length} type rows + ${Object.keys(short.run_length_delta).length} family rows, all at baseline`);

  // (B1) GROWTH — a divergence that got worse.
  const grown = { ...shortBase, gate_type_delta: { ...shortBase.gate_type_delta } };
  const gk = Object.keys(grown.gate_type_delta)[0];
  const worse = { ...short, gate_type_delta: { ...short.gate_type_delta, [gk]: short.gate_type_delta[gk] * 2 } };
  r = ratchet(worse, shortBase);
  leg('B1 a gate-type delta that GREW', r.grew.length === 1 && r.grew[0].key === `type/${gk}`, `grew: ${r.grew.map((x) => x.key).join(',')}`);

  // (B2) A NEW DIVERGENT RUN-LENGTH FAMILY — the gadget-mis-assembly signal.
  const novelCand = { ...short, run_length_delta: { ...short.run_length_delta, 'CompleteAdd x 18': 1 } };
  r = ratchet(novelCand, shortBase);
  leg('B2 a NEW divergent run-length family (CompleteAdd x 18)',
    r.novel.length === 1 && r.novel[0].key === 'family/CompleteAdd x 18', `novel: ${r.novel.map((x) => x.key).join(',')}`);

  // (B3) A STALE ROW — the win nobody recorded. Red, or the census is not monotone.
  const better = { ...short, gate_type_delta: { ...short.gate_type_delta, [gk]: 0 } };
  delete better.gate_type_delta[gk];
  r = ratchet(better, shortBase);
  leg('B3 a row that SHRANK and was not recorded (stale baseline)',
    r.stale.some((x) => x.key === `type/${gk}`), `stale: ${r.stale.map((x) => x.key).join(',').slice(0, 40)}`);

  // (B4) THE ASSEMBLY FLOOR — a branch that is not its base plus a suffix must BLOCK, not grade.
  const mk = (body) => ({ pub: 1, rows: ['Generic|PUB', ...body], path: 'synthetic' });
  const trunkRows = ['Generic|1', 'Poseidon|', 'Zero|'];
  const good = {}; for (const t of RUNGS) good[t] = mk([...trunkRows, `Generic|${t}`]);
  good[TRUNK] = mk(trunkRows);
  good.w12_close = mk([...trunkRows, 'Generic|w11_wraphack', 'Generic|w12_close']);
  good.w11_bullet = mk([...trunkRows, 'Generic|w10_combine', 'Generic|w11_bullet']);
  good.w11_finsponge = mk([...trunkRows, 'Generic|w10_finalize', 'Generic|w11_finsponge']);
  let blocked = false; try { assemble(good); } catch (e) { blocked = !!e.blocked; }
  leg('B4 control: a consistent synthetic emission ASSEMBLES', !blocked, blocked ? 'BLOCKED (wrong)' : 'assembled');
  const bent = JSON.parse(JSON.stringify(good));
  bent.w11_bullet.rows[1] = 'Generic|BENT';   // trunk row rewritten under a branch
  blocked = false; try { assemble(bent); } catch (e) { blocked = !!e.blocked; }
  leg('B4 a branch whose body is NOT its base plus a suffix BLOCKS', blocked, blocked ? 'BLOCKED (exit 3)' : 'graded anyway (wrong)');
  const empty = JSON.parse(JSON.stringify(good));
  empty.w12_close = mk([...trunkRows, 'Generic|w11_wraphack'], 0);   // close contributes nothing
  blocked = false; try { assemble(empty); } catch (e) { blocked = !!e.blocked; }
  leg('B5 a rung that contributes ZERO own rows BLOCKS (a blinded census)', blocked, blocked ? 'BLOCKED (exit 3)' : 'graded anyway (wrong)');

  console.log();
  if (bad) { console.log(`wrapmain-shape-diff --self-test: ${bad} LEG(S) FAILED`); process.exit(1); }
  console.log('wrapmain-shape-diff --self-test: 8 legs green (2 anchors + 3 ratchet bites + 3 assembly-floor legs)');
}

// ── main ──────────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const known = new Set(['--self-test', '--report', '--update-baseline', '--accept-growth']);
for (const a of argv) if (!known.has(a)) { console.error(`usage: wrapmain-shape-diff.mjs [${[...known].join('] [')}]`); process.exit(2); }

// ── SCOPE ─ this pair is the ONLY copy; it prints on every run, pass or fail, because the
// misreads this convention exists to stop happened to people reading RESULTS, not source. ──
const SCOPE_ANSWERS =
  'for each of the seven kimchi gate types and each `typ x runlength` family, is |ours - mina| EXACTLY the '
  + 'number recorded in fixtures/wrapmain-wrap-census-baseline.json — measured over the union of 15 '
  + '/tmp/pickles-wrapmain rungs, each provenance-checked against the current source cone, probe rows spliced '
  + 'out, every branch verified on emitted rows to be its base plus a suffix?';
const SCOPE_DOES_NOT_ANSWER =
  'whether the gates we emit ARE Mina wrap gates. It reads COUNTS of gate types and COUNTS of run lengths and '
  + 'nothing else — never a coefficient, a wire, a row position or an ordering — so a circuit with the right '
  + 'run-length multiset in the wrong order with wrong coefficients sits at baseline; and because it is a '
  + 'RATCHET, at baseline means no worse than the recorded divergence, never conforms.';
const SCOPE_ANSWERS_SELFTEST =
  'given MINA OWN gate list as the synthetic candidate, do ratchet() and assemble() bite — a gate-type delta '
  + 'that grew, a new divergent run-length family, a shrink the baseline does not record, a branch that is not '
  + 'its base plus a suffix, and a rung contributing zero own rows?';
const SCOPE_DOES_NOT_ANSWER_SELFTEST =
  'anything about the wrap assembly on disk. It reads no emission and no baseline file at all; the bare census '
  + 'refuses (exit 3) without one, so a green here is the instrument firing, not a census.';
{
  const st = argv.includes('--self-test') && argv.length === 1;
  console.log(`ANSWERS:         ${st ? SCOPE_ANSWERS_SELFTEST : SCOPE_ANSWERS}`);
  console.log(`DOES NOT ANSWER: ${st ? SCOPE_DOES_NOT_ANSWER_SELFTEST : SCOPE_DOES_NOT_ANSWER}`);
}

const { spec, publicInputSize, gates: minaGates } = await loadCircuit('wrap-transaction');
const mina = { name: spec.stem.slice(0, 48), pub: publicInputSize, gates: minaGates.map((g) => g.typ) };

if (argv.includes('--self-test')) { selfTest(mina); if (argv.length === 1) process.exit(0); }

let asm, ours, pinned, prov;
try {
  pinned = pinnedWordsFromLean();
  const cone = leanConeDigest(EMIT_DRIVER);
  const rungs = {};
  for (const t of RUNGS) {
    rungs[t] = loadRung(t);
    prov = requireFreshArtifact({ artifact: rungs[t].path, cone, emitCmd: EMIT_CMD });
  }
  asm = assemble(rungs);
  ours = { gates: asm.gates, pub: asm.pub };
  // THE NON-VACUITY FLOOR. A reader that lost the gate list reads as "conforms" otherwise.
  const seen = new Set(ours.gates);
  if (ours.gates.length < 1000 || seen.size < 6)
    block(`the assembled census observed ${ours.gates.length} gates over ${seen.size} type(s) — too little to BE a census. `
      + `A blinded reader must not read as conformance.`);
} catch (e) {
  console.error(`\n${e.message}\n`);
  // ⚠ 3 IS NOT 1. A prerequisite that is absent or stale means THE DIFF DID NOT RUN.
  process.exit(e.blocked || isStale(e) ? 3 : 1);
}

const now = report(ours, mina, asm, pinned);

const UPDATING = argv.includes('--update-baseline');
if (!existsSync(BASELINE) && !UPDATING) {
  // ⚠ AN ABSENT BASELINE IS BLOCKED, NEVER GREEN. A ratchet with nothing to ratchet against is not
  // a conforming run; it is a run that measured nothing.
  console.error(`\n⚑ BLOCKED — no baseline at ${fileURLToPath(BASELINE)}. Record this measurement with --update-baseline.\n`);
  process.exit(3);
}
const base = existsSync(BASELINE) ? JSON.parse(readFileSync(BASELINE, 'utf8')) : { gate_type_delta: {}, run_length_delta: {}, schema: BASELINE_SCHEMA };
if (base.schema !== BASELINE_SCHEMA) { console.error(`\n⚑ BLOCKED — baseline schema ${base.schema} != ${BASELINE_SCHEMA}.\n`); process.exit(3); }

const r = ratchet(now, base);

if (UPDATING) {
  // ⚠ THE EASY PATH MUST BE THE SAFE ONE. `--update-baseline` after a red is the reflex, and a
  // reflex that silently accepts a regression turns the ratchet into a rubber stamp. Growth and a
  // NEW divergent family both refuse; only a first-ever baseline (no file) is written unconditionally.
  const regressed = [...r.grew, ...r.novel];
  if (existsSync(BASELINE) && regressed.length && !argv.includes('--accept-growth')) {
    console.error(`\n⚑ REFUSING TO RECORD A REGRESSION — ${r.grew.length} row(s) GREW, ${r.novel.length} NEW divergent family(ies):`);
    for (const x of regressed) console.error(`   ${x.key}  ${x.was} -> ${x.is}`);
    console.error('   Fix the assembly, or pass --accept-growth and SAY IN THE COMMIT what regressed and why.\n');
    process.exit(1);
  }
  const out = {
    schema: BASELINE_SCHEMA,
    what: 'The 14-rung Lean wrap_main assembly against Mina\'s compiled wrap-transaction. Every row is '
      + 'OURS - MINA. It may shrink; a GROWTH and a NEW divergent family are both red, and a shrink that '
      + 'is not recorded here is red too (that is what makes the census monotone).',
    measured_at: new Date().toISOString(),
    mina: { circuit: 'wrap-transaction', md5: spec.md5, gates: mina.gates.length, primary: mina.pub },
    ours: { gates: ours.gates.length, public_input_size: ours.pub, rungs: RUNGS.length, emit_dir: EMIT_DIR },
    // ⚑ WHICH EMISSION THIS SCOREBOARD IS OF. A census row without a commit behind it is a number
    // nobody can re-derive — the same defect the provenance floor exists to refuse one level down.
    emitted_from: { git_head: prov?.git?.head, cone_digest: prov?.cone?.digest, emitted_at: prov?.emitted_at },
    coverage: {
      total: pct(ours.gates.length, mina.gates.length),
      non_generic: pct(ours.gates.length - (histogram(ours.gates).Generic ?? 0),
        mina.gates.length - (histogram(mina.gates).Generic ?? 0)),
      pinned_statement_words: `${ours.pub}/${pinned}`,
    },
    gate_type_delta: now.gate_type_delta,
    run_length_delta: now.run_length_delta,
  };
  writeFileSync(fileURLToPath(BASELINE), `${JSON.stringify(out, null, 2)}\n`);
  console.log(`\nwrapmain-shape-diff: baseline WRITTEN to ${fileURLToPath(BASELINE)} `
    + `(${Object.keys(now.gate_type_delta).length} type rows, ${Object.keys(now.run_length_delta).length} family rows)`);
  process.exit(0);
}

console.log(`\n── RATCHET vs ${fileURLToPath(BASELINE).replace(/.*\/bridge\//, 'bridge/')} `
  + `(measured ${base.measured_at}, ours ${base.ours?.gates} of mina ${base.mina?.gates}) ──`);
for (const x of r.grew) console.log(`   RED    GREW    ${x.key.padEnd(34)} ${x.was} -> ${x.is}`);
for (const x of r.novel) console.log(`   RED    NEW     ${x.key.padEnd(34)} no baseline row, delta ${x.is}`);
for (const x of r.stale) console.log(`   RED    STALE   ${x.key.padEnd(34)} ${x.was} -> ${x.is}   (a WIN nobody recorded)`);
console.log(`   ok     ${r.ok.length} row(s) at baseline`);

if (r.grew.length || r.novel.length || r.stale.length) {
  console.log(`\nwrapmain-shape-diff: ${r.grew.length} GREW · ${r.novel.length} NEW · ${r.stale.length} STALE `
    + `over ${r.ok.length + r.grew.length + r.novel.length + r.stale.length} rows`);
  console.log('   GREW / NEW  = the assembly diverged further from Mina\'s wrap circuit. Read the row.');
  console.log('   STALE       = it diverged LESS and the scoreboard does not say so. Record it:');
  console.log('                   node scripts/wrapmain-shape-diff.mjs --update-baseline');
  process.exit(1);
}
console.log(`\nwrapmain-shape-diff: at baseline — ${ours.gates.length}/${mina.gates.length} gates `
  + `= ${pct(ours.gates.length, mina.gates.length)} of Mina's wrap-transaction, MEASURED over 14 provenance-checked rungs.`);

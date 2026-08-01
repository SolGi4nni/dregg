// diff-oracle.mjs — ONE differential-oracle harness the Pickles-synthesis byte-diffs share.
//
// WHY. The Pickles-in-Lean epoch grew ~6 near-identical o1js differential oracles
// (custom-gate-diff, pickles-placement, pickles-r3-branchdata, pickles-statement,
// curve-gate, pickles-step-statement). Every one does the SAME four things:
//   (a) a REFERENCE producer  — o1js `Provable.constraintSystem(f).gates`, or a statement's
//       packed public input, or a field of a real kimchi-verified devnet block;
//   (b) a CANDIDATE producer  — the Lean-emitted value (from a Lean-source extraction, a
//       committed fixture, or a recomputation of the Lean `to_data`/pack);
//   (c) a byte/field DIFF     — canonicalize both to an ordered vector of {name,value} and
//       walk them, citing the FIRST diverging offset/field;
//   (d) exit RED on divergence, GREEN on byte-exact.
// This harness is that shape, once. An oracle becomes a thin module that supplies (a) and (b)
// and calls `runOracle`; the DIFF + exit-code + RED-PATH SELF-TEST live here.
//
// ⚑ THE POINT OF THE SELF-TEST. A diff that cannot go RED is documented-not-detected. `runOracle`
// (and the standalone `--self-test`) take the live vector, CORRUPT one entry, and PROVE the engine
// reports RED at the right offset — so every migrated oracle carries a machine-checked demonstration
// that its red path bites, not a prose claim that it would.
//
// ⚑ THE tsc WRINKLE. The old oracles carried literal falsification controls (`67 === 66`) that `tsc`
// rejects as TS2367. Here the falsification is a RUNTIME corruption of a producer's output, never a
// literal-vs-literal comparison — so the harness is plain `.mjs` (tsc never sees it) and a migrated
// `.ts` oracle that routes its diff through `runOracle` no longer trips TS2367 either.
//
// LIBRARY FORM (what migrated oracles use):
//   import { runOracle } from './diff-oracle.mjs';
//   await runOracle({ shape, label, reference, candidate, extra });   // reads --self-test from argv
// where reference()/candidate() each return a Vector: Array<{ name, value }> (value bigint|number|
// string; a bare array of primitives is auto-named by index). `extra()` is optional shape-specific
// provenance (falsifiers, bytecode code-path greps) that runs after the vector diff.
//
// CLI FORM:
//   node diff-oracle.mjs --reference <mod.mjs#export> --candidate <mod.mjs#export> --shape <gates|statement|field> [--self-test]
//   node diff-oracle.mjs --self-test        # standalone: prove the engine's RED path bites for all three shapes
//
// Run: node scripts/diff-oracle.mjs --self-test
import { pathToFileURL, fileURLToPath } from 'node:url';
import { resolve } from 'node:path';

// ── canonicalization: every value becomes a byte-comparable string ────────────────────────────────
export function canon(v) {
  if (typeof v === 'bigint') return v.toString();
  if (typeof v === 'number') return Number.isFinite(v) ? String(v) : `NaN(${v})`;
  if (typeof v === 'string') return v;
  if (v && typeof v === 'object') {
    // {row,col} placement cells and the like → stable string
    if ('row' in v && 'col' in v) return `${v.row},${v.col}`;
    if (Array.isArray(v)) return v.map(canon).join('|');
    return JSON.stringify(v);
  }
  return String(v);
}

// Coerce a producer's output into a normalized Vector: Array<{ name, value }>.
export function normalize(out, tag = 'entry') {
  if (!Array.isArray(out)) throw new Error(`${tag}: producer did not return an array`);
  return out.map((e, i) => {
    if (e && typeof e === 'object' && 'value' in e)
      return { name: String(e.name ?? `${tag}[${i}]`), value: e.value };
    return { name: `${tag}[${i}]`, value: e };
  });
}

// ── the DIFF engine: walk two ordered vectors, cite the FIRST divergence ──────────────────────────
export function diffVectors(ref, cand) {
  const n = Math.min(ref.length, cand.length);
  for (let i = 0; i < n; i++) {
    if (ref[i].name !== cand[i].name)
      return { ok: false, kind: 'name', index: i, name: ref[i].name, ref: ref[i].name, cand: cand[i].name };
    const rv = canon(ref[i].value);
    const cv = canon(cand[i].value);
    if (rv !== cv)
      return { ok: false, kind: 'value', index: i, name: ref[i].name, ref: rv, cand: cv };
  }
  if (ref.length !== cand.length)
    return { ok: false, kind: 'length', index: n, name: '<length>', ref: String(ref.length), cand: String(cand.length) };
  return { ok: true, matched: n };
}

// ── RED-PATH self-test: corrupt a KNOWN-GREEN copy of the vector, prove the engine reports RED ────
// Built on the reference-vs-itself baseline (guaranteed GREEN), so it is independent of whatever the
// real candidate did — it proves the ENGINE's red path on the EXACT data shapes in play.
export function selfTestBite(ref) {
  if (ref.length === 0) return { ok: false, detail: 'reference vector empty — nothing to corrupt' };
  const clean = ref.map((e) => ({ ...e }));
  const base = diffVectors(ref, clean);
  if (!base.ok) return { ok: false, detail: 'baseline (ref vs identical copy) did NOT diff GREEN — engine broken' };
  // (1) value corruption at index 0 → must RED with kind 'value' at offset 0
  const cv = clean.map((e) => ({ ...e }));
  cv[0] = { ...cv[0], value: canon(cv[0].value) + '#CORRUPT' };
  const r1 = diffVectors(ref, cv);
  if (r1.ok) return { ok: false, detail: 'value-corrupted candidate still diffed GREEN — RED PATH DEAD' };
  if (!(r1.kind === 'value' && r1.index === 0))
    return { ok: false, detail: `value corruption surfaced as ${r1.kind}@${r1.index}, expected value@0` };
  // (2) length corruption (drop last) → must RED with kind 'length'
  const cl = clean.slice(0, clean.length - 1);
  const r2 = diffVectors(ref, cl);
  if (r2.ok) return { ok: false, detail: 'length-corrupted candidate still diffed GREEN' };
  return { ok: true, detail: `baseline GREEN; flip value@0 → RED(${r1.kind}); drop tail → RED(${r2.kind}); n=${ref.length}` };
}

function hasSelfTestFlag() {
  return process.argv.slice(2).some((a) => a === '--self-test' || a === '--selftest');
}

function printDiff(label, shape, ref, cand, res) {
  console.log(`── diff-oracle [${shape}] ${label} ─────────────────────`);
  console.log(`  reference: ${ref.length} entr${ref.length === 1 ? 'y' : 'ies'}   candidate: ${cand.length}`);
  if (res.ok) {
    console.log(`  ok   ALL ${res.matched} entr${res.matched === 1 ? 'y' : 'ies'} BYTE-EXACT: reference == candidate`);
  } else if (res.kind === 'length') {
    console.log(`  RED  length mismatch: reference has ${res.ref} entries, candidate has ${res.cand}`);
  } else if (res.kind === 'name') {
    console.log(`  RED  entry #${res.index}: reference names '${res.ref}', candidate names '${res.cand}'`);
  } else {
    console.log(`  RED  DIVERGE at entry #${res.index} (${res.name}): reference=${res.ref}  candidate=${res.cand}`);
  }
}

// ── the library entry every migrated oracle calls ─────────────────────────────────────────────────
export async function runOracle({ shape, label, reference, candidate, extra, selfTest } = {}) {
  if (!['gates', 'statement', 'field'].includes(shape))
    throw new Error(`runOracle: --shape must be gates|statement|field, got ${shape}`);
  const wantSelfTest = selfTest ?? hasSelfTestFlag();

  const ref = normalize(await reference(), 'ref');
  const cand = normalize(await candidate(), 'cand');
  const res = diffVectors(ref, cand);
  printDiff(label, shape, ref, cand, res);

  // shape-specific provenance / falsifiers that are not a plain vector diff (kept as-is by the oracle)
  if (typeof extra === 'function') {
    try {
      await extra({ ref, cand, result: res });
    } catch (e) {
      console.log(`  RED  extra provenance check threw: ${(e && e.message) || e}`);
      process.exit(1);
    }
  }

  // RED-PATH self-test — a diff that cannot go RED is documented-not-detected.
  if (wantSelfTest) {
    const st = selfTestBite(ref);
    if (!st.ok) {
      console.log(`  SELF-TEST FAILED (red path does not bite): ${st.detail}`);
      process.exit(1);
    }
    console.log(`  self-test: RED path bites — ${st.detail}`);
  }

  console.log(res.ok ? `=== GREEN — ${label} byte-exact ===` : `=== RED — ${label}: first divergence cited above ===`);
  process.exit(res.ok ? 0 : 1);
}

// ── CLI ───────────────────────────────────────────────────────────────────────────────────────────
function parseArgs(argv) {
  const o = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--self-test' || a === '--selftest') o.selfTest = true;
    else if (a === '--reference') o.reference = argv[++i];
    else if (a === '--candidate') o.candidate = argv[++i];
    else if (a === '--shape') o.shape = argv[++i];
    else if (a === '--label') o.label = argv[++i];
  }
  return o;
}

// resolve a CLI spec `path/to/mod.mjs#exportName` → an async producer function
async function loadProducer(spec) {
  const [p, exp] = spec.split('#');
  const url = pathToFileURL(resolve(process.cwd(), p)).href;
  const mod = await import(url);
  const fn = mod[exp || 'produce'] || mod.default;
  if (typeof fn !== 'function')
    throw new Error(`producer ${spec}: no callable export '${exp || 'produce'}' (or default)`);
  return fn;
}

// standalone red-path proof: exercise the engine on a synthetic vector of EACH shape
function standaloneSelfTest() {
  console.log('=== diff-oracle --self-test: proving the RED path bites for every shape ===');
  const synth = {
    gates: [
      { name: 'gate[0].coeff[0]', value: 123n },
      { name: 'gate[0].coeff[1]', value: 456n },
      { name: 'gate[1].wire[0]', value: { row: 2, col: 3 } },
    ],
    statement: Array.from({ length: 6 }, (_, i) => ({ name: `slot[${i}]`, value: BigInt(i * 7 + 1) })),
    field: [{ name: 'wrap_public_input[29]', value: 67 }],
  };
  let bad = 0;
  for (const shape of ['gates', 'statement', 'field']) {
    const st = selfTestBite(normalize(synth[shape], shape));
    if (st.ok) console.log(`  ok   [${shape}] ${st.detail}`);
    else { console.log(`  RED  [${shape}] ${st.detail}`); bad++; }
  }
  console.log(bad ? `=== RED — ${bad} shape(s) failed to bite ===` : '=== GREEN — the diff engine reports RED on corruption for all three shapes ===');
  process.exit(bad ? 1 : 0);
}

async function cliMain() {
  const o = parseArgs(process.argv.slice(2));
  if (!o.reference && !o.candidate && o.selfTest) return standaloneSelfTest();
  if (!o.reference || !o.candidate || !o.shape) {
    console.error('usage: diff-oracle --reference <mod.mjs#export> --candidate <mod.mjs#export> --shape <gates|statement|field> [--self-test]');
    console.error('       diff-oracle --self-test    (standalone engine red-path proof)');
    process.exit(2);
  }
  const [reference, candidate] = await Promise.all([loadProducer(o.reference), loadProducer(o.candidate)]);
  await runOracle({ shape: o.shape, label: o.label ?? `${o.reference} vs ${o.candidate}`, reference, candidate, selfTest: o.selfTest });
}

// run the CLI only when invoked directly (not when imported by an oracle module or the CLI)
const isMain = process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1]);
if (isMain) cliMain();

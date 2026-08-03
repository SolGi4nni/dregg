// CURVE-GATE ORACLE — the scalar-mul custom gates are COEFF-FREE, in o1js AND in what Lean emits.
//
// ## ⚑ WHAT THIS FILE CLAIMED, AND WHAT IT MEASURED, UNTIL 2026-08-03
//
// It printed `ok VarBaseMul: o1js-emitted, ALL rows coeff-free (coeffs=[] — MATCH Lean)` while
// reading o1js AND NOTHING ELSE. "MATCH Lean" was a parenthesis in a `console.log`: the Lean side
// was never opened, so the oracle was green for any Lean emitter whatsoever, including one that put
// fifteen coefficients on every `VarBaseMul` row. It was also in NO gate script — `grep -rn
// curve-gate-oracle` found it in no `.sh`, no workflow, and no docs. A one-sided oracle that
// self-certifies its second source is exactly the "identity carrier" shape: the conclusion names a
// comparison the code never performs.
//
// ## WHAT IT IS NOW: TWO SOURCES, AND THE SECOND ONE IS THE EMITTED OBJECT
//
//   source A  o1js 2.15.0 `Provable.constraintSystem(...).gates` — the OCaml/wasm bindings' own
//             emission, compiled from `Group.scale(Scalar)`.
//   source B  OUR emitted step circuit (`stepmain_step_r8_finalize.json`, live or the committed gz
//             fixture) — not the Lean SOURCE and not a `#guard`, the gate list that actually ships.
//
// The comparison is per gate type: the SET of coefficient-vector lengths each side puts on rows of
// that type. For `VarBaseMul` and `CompleteAdd`, which `Group.scale` reaches, both sides must be
// exactly `{0}` and the two must agree. For `EndoMul` and `EndoMulScalar`, which are reachable only
// from Pickles' in-circuit recursive verifier and NOT from a plain `Group.scale`, o1js has nothing
// to say — so their coeff-freeness is asserted against OUR EMISSION alone, and the upstream leg is
// `proof-systems`' own constructors (`create_endomul` / EndoMulScalar use `vec![]`) plus the shared
// `GateType` #[repr(C)] discriminants. That asymmetry is a named boundary here, not a silence: the
// entries say which legs each type has.
//
// ⚠ WHAT IS NOT CLAIMED. Coefficient-freeness is a shape fact. That these gates' SUBSTANCE matches
// kimchi's is measured elsewhere (the pure-Rust harness: `verify() = true` + tamper rejected against
// proof-systems 0.3.0), and their wires by `pickles-placement-oracle.mjs`.
//
// USAGE — ⚠ green-or-bust.
//   node scripts/curve-gate-oracle.mjs                # grade
//   node scripts/curve-gate-oracle.mjs --self-test    # the red path: 4 bites + two anchors
//   node scripts/curve-gate-oracle.mjs --lean <path>  # a specific emission (its stamp is still checked)
// EXIT: 0 conform · 1 a check is red · 3 the Lean emission is stale/unreproducible.
import { existsSync, readFileSync } from 'node:fs';
import { gunzipSync } from 'node:zlib';
import { Scalar, Group, Provable } from 'o1js';
import { isStale, leanConeDigest, requireFreshArtifact, requireFreshFixture } from './emit-provenance.mjs';

const EMIT_DRIVER = 'Dregg2/Circuit/Emit/EmitStepMainJson.lean';
const EMIT_CMD = '(cd metatheory && DREGG_SM=step DREGG_SM_RUNGS=r8_finalize lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean)';
const REFRESH_CMD = 'node scripts/stepmain-region-conformance.mjs --emit --refresh-fixture';
const DEFAULT_LEAN_PATH = '/tmp/pickles-stepmain/stepmain_step_r8_finalize.json';
const LEAN_FIXTURE = new URL('../fixtures/stepmain-step-r8-finalize-gates.json.gz', import.meta.url);
const LEAN_FIXTURE_PROV = new URL('../fixtures/stepmain-step-r8-finalize-gates.provenance.json', import.meta.url);
// GateType declaration order == the BCS variant index (kimchi `circuits/gate.rs`).
const NAMES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];
/** The two o1js reaches from `Group.scale`, and the two it does not. */
const TWO_SOURCE = ['VarBaseMul', 'CompleteAdd'];
const LEAN_ONLY = ['EndoMul', 'EndoMulScalar'];

/** `{ type -> { count, coeffLens:Set } }` over one gate list. */
function byType(gates, typeOf, coeffsOf) {
  const m = new Map();
  for (const g of gates) {
    const t = typeOf(g);
    if (!m.has(t)) m.set(t, { count: 0, coeffLens: new Set() });
    const e = m.get(t);
    e.count++;
    e.coeffLens.add(coeffsOf(g).length);
  }
  return m;
}
const lens = (e) => (e ? [...e.coeffLens].sort((a, b) => a - b) : []);

async function o1jsCurveGates() {
  const cs = await Provable.constraintSystem(() => {
    const g = Provable.witness(Group, () => Group.generator);
    const s = Provable.witness(Scalar, () => Scalar.from(12345n));
    g.scale(s).x.seal();
  });
  return { rows: cs.rows, byType: byType(cs.gates, (g) => g.type, (g) => g.coeffs) };
}

/** OUR emitted step circuit — live when present, else the committed fixture, both under the floor. */
function leanCurveGates(cone, explicit) {
  const LEAN_DEFAULT = explicit ?? DEFAULT_LEAN_PATH;
  const haveLive = existsSync(LEAN_DEFAULT);
  const haveFix = existsSync(LEAN_FIXTURE);
  if (!haveLive && !haveFix)
    throw new Error(`no Lean emission: neither ${LEAN_DEFAULT} nor the committed fixture. Produce it with\n   ${EMIT_CMD}`);
  let j, src;
  if (haveLive) {
    requireFreshArtifact({ artifact: LEAN_DEFAULT, cone, emitCmd: EMIT_CMD });
    j = JSON.parse(readFileSync(LEAN_DEFAULT, 'utf8')); src = LEAN_DEFAULT;
  } else {
    requireFreshFixture({ fixture: LEAN_FIXTURE, sidecar: LEAN_FIXTURE_PROV, cone, emitCmd: EMIT_CMD, refreshCmd: REFRESH_CMD });
    j = JSON.parse(gunzipSync(readFileSync(LEAN_FIXTURE)).toString('utf8')); src = 'committed fixture';
  }
  return { src, gates: j.gates };
}

/** The graded vector. `leanGates` is the raw emitted list so a self-test can bend it. */
export function grade(o1, leanGates) {
  const L = byType(leanGates, (g) => NAMES[g.typ], (g) => g.coeffs);
  const out = [];
  const check = (name, ok, detail) => out.push({ name, ok, detail });

  for (const t of TWO_SOURCE) {
    const a = o1.byType.get(t), b = L.get(t);
    check(`${t}/o1js-emits-it`, !!a, a ? `${a.count} rows from Group.scale` : '⚑ o1js did not emit it at all');
    check(`${t}/lean-emits-it`, !!b && b.count > 0, b ? `${b.count} rows in our step circuit` : '⚑ our emission has none');
    check(`${t}/o1js-coeff-free`, !!a && a.coeffLens.size === 1 && a.coeffLens.has(0), `o1js coeffLens {${lens(a).join(',')}}`);
    check(`${t}/lean-coeff-free`, !!b && b.coeffLens.size === 1 && b.coeffLens.has(0), `lean coeffLens {${lens(b).join(',')}}`);
    // ⚑ THE CROSS-SOURCE ENTRY — the one the old file printed and never computed.
    check(`${t}/o1js-and-lean-agree`, !!a && !!b && lens(a).join(',') === lens(b).join(','),
      `o1js {${lens(a).join(',')}} vs lean {${lens(b).join(',')}}`);
  }
  for (const t of LEAN_ONLY) {
    const b = L.get(t);
    // ⚠ A BOUNDARY, STATED. o1js `Group.scale` cannot reach these, so there is no second source here;
    // the leg that remains is our emitted object against proof-systems' own `vec![]` constructors.
    check(`${t}/not-reachable-from-o1js-Group.scale`, !o1.byType.get(t),
      o1.byType.get(t) ? `⚑ o1js emitted it after all — the boundary comment is wrong` : 'as documented (Pickles-recursion-internal)');
    check(`${t}/lean-coeff-free`, !!b && b.coeffLens.size === 1 && b.coeffLens.has(0),
      b ? `lean coeffLens {${lens(b).join(',')}} over ${b.count} rows (single-source: proof-systems' vec![])`
        : '⚑ our emission has no rows of this type — nothing was measured');
  }
  return out;
}

// ── main ──────────────────────────────────────────────────────────────────────────────────────────
const argv = process.argv.slice(2);
const arg = (f) => { const i = argv.indexOf(f); return i >= 0 ? argv[i + 1] : undefined; };
const o1 = await o1jsCurveGates();
console.log(`── o1js Group.scale(Scalar): ${o1.rows} rows`);
for (const [t, e] of o1.byType) console.log(`   ${t.padEnd(16)} count=${String(e.count).padStart(4)}  coeffLens={${lens(e).join(',')}}`);

// ⚑ THE RED PATH, and it needs NEITHER Lean nor an emission — deliberately, so the instrument's own
// red path is answerable in a tree whose Lean cone has moved (the same split `wrapmain-region-
// conformance.mjs --self-test` uses). The honest anchor is a SYNTHETIC coeff-free gate list, which
// is what a conforming emission looks like for these four types; each bite puts a coefficient on one
// row of one type and must redden that type's entry. The OLD file could not have gone red for ANY of
// these, because it never opened a second source at all.
if (argv.includes('--self-test')) {
  const ordOf = (n) => NAMES.indexOf(n);
  const honest = [...TWO_SOURCE, ...LEAN_ONLY].flatMap((t) => [
    { typ: ordOf(t), coeffs: [] }, { typ: ordOf(t), coeffs: [] },
  ]);
  let bad = 0;
  const leg = (label, gates, expectRed) => {
    const red = grade(o1, gates).some((c) => !c.ok);
    const ok = red === expectRed; if (!ok) bad++;
    console.log(`   ${ok ? 'ok  ' : 'RED '} ${label.padEnd(56)} ${red ? 'RED' : 'green'}`);
  };
  const bend = (typ) => honest.map((x, i) =>
    (x.typ === ordOf(typ) && i === honest.findIndex((y) => y.typ === ordOf(typ)) ? { typ: x.typ, coeffs: ['7'] } : x));
  console.log('\n── curve-gate-oracle --self-test (the Lean side must be READ, so bending it must bite) ──');
  leg('A0 anchor: a coeff-free gate list of all four types', honest, false);
  leg('B1 one VarBaseMul row given a coefficient', bend('VarBaseMul'), true);
  leg('B2 one CompleteAdd row given a coefficient', bend('CompleteAdd'), true);
  leg('B3 one EndoMulScalar row given a coefficient', bend('EndoMulScalar'), true);
  leg('B4 one EndoMul row given a coefficient', bend('EndoMul'), true);
  // ⚠ AND THE ANCHOR THAT MATTERS MOST: a candidate with NO rows of a type must NOT pass. An oracle
  // that is green over an empty set is the identity-carrier shape this file used to be.
  leg('B5 an emission with no curve-gate rows at all', [], true);
  console.log();
  if (bad) { console.log(`curve-gate-oracle --self-test: ${bad} LEG(S) FAILED`); process.exit(1); }
  console.log('curve-gate-oracle --self-test: 6 legs green (1 anchor + 4 coefficient bites + the empty-set anchor)\n');
  if (argv.length === 1) process.exit(0);
}

let lean;
try {
  lean = leanCurveGates(leanConeDigest(EMIT_DRIVER), arg('--lean'));
} catch (e) {
  console.error(`\n${e.message}\n`);
  process.exit(isStale(e) ? 3 : 1);
}
console.log(`── lean emission: ${lean.src} (${lean.gates.length} rows)`);

const checks = grade(o1, lean.gates);
console.log();
for (const c of checks) console.log(`   ${c.ok ? 'ok  ' : 'RED '} ${c.name.padEnd(48)} ${c.detail}`);
const fails = checks.filter((c) => !c.ok).length;
console.log('\n=== ' + (fails
  ? `RED — ${fails} check(s) failed over ${checks.length}`
  : `GREEN — ${checks.length} checks: VarBaseMul + CompleteAdd coeff-free in o1js AND in our emitted step circuit and the two AGREE; `
    + 'EndoMul + EndoMulScalar coeff-free in our emission (single-source by construction)') + ' ===');
process.exit(fails ? 1 : 0);

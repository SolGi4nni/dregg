// Curve-gate oracle — confirm o1js emits the scalar-mul custom gates with the typ (name) + coeffs the
// Lean curve-gate emitters use (all coeff-free, coeffs = []). READ-ONLY oracle; o1js is the byte target.
//
// FINDING (measured): o1js `Group.scale(Scalar)` compiles to the VARIABLE-BASE path — it emits
// `VarBaseMul` + `CompleteAdd` (both coeff-free), NOT the endomorphism gates. `EndoMul`/`EndoMulScalar`
// are used only inside Pickles' in-circuit recursive verifier (the ScalarChallenge endo-multiplication)
// and are not reachable from a plain o1js `Group.scale`. So this oracle byte-confirms VarBaseMul +
// CompleteAdd against o1js directly; EndoMul/EndoMulScalar coeff-freeness rests on proof-systems' own
// gate constructors (`create_endomul`/EndoMulScalar use `vec![]`) + the shared `GateType` #[repr(C)]
// discriminants (o1js and kimchi share the enum). Their SUBSTANCE is measured in the pure-Rust harness
// (verify()=true + tamper rejected) against proof-systems 0.3.0.
import { Scalar, Group, Provable } from 'o1js';

async function gateSummary(label, f) {
  const cs = await Provable.constraintSystem(f);
  const byType = new Map();
  for (const g of cs.gates) {
    const key = g.type;
    if (!byType.has(key)) byType.set(key, { count: 0, coeffLens: new Set() });
    const e = byType.get(key);
    e.count++;
    e.coeffLens.add(g.coeffs.length);
  }
  console.log(`\n===== ${label} =====  (rows=${cs.rows})`);
  for (const [type, e] of byType) {
    console.log(`  ${type.padEnd(16)} count=${String(e.count).padStart(4)}  coeffLens={${[...e.coeffLens].join(',')}}`);
  }
  return byType;
}

const bt = await gateSummary('Group.scale(Scalar)  (variable-base scalar mul)', () => {
  const g = Provable.witness(Group, () => Group.generator);
  const s = Provable.witness(Scalar, () => Scalar.from(12345n));
  g.scale(s).x.seal();
});

let fails = 0;
// The two curve gates o1js `Group.scale` actually emits — byte-confirmed coeff-free vs the Lean emitters.
for (const gate of ['VarBaseMul', 'CompleteAdd']) {
  const e = bt.get(gate);
  if (!e) {
    console.log(`  RED  ${gate}: expected but NOT emitted by o1js Group.scale`);
    fails++;
  } else if (!(e.coeffLens.size === 1 && e.coeffLens.has(0))) {
    console.log(`  RED  ${gate}: coeff lengths ${[...e.coeffLens]} != {0} (Lean emits coeffs=[])`);
    fails++;
  } else {
    console.log(`  ok   ${gate}: o1js-emitted, ALL rows coeff-free (coeffs=[] — MATCH Lean)`);
  }
}
// Documented boundary (not a gate): the endo gates are not reachable via Group.scale.
for (const gate of ['EndoMul', 'EndoMulScalar']) {
  if (bt.get(gate)) {
    console.log(`  note ${gate}: unexpectedly emitted here — coeff-free? ${[...bt.get(gate).coeffLens]}`);
  } else {
    console.log(`  note ${gate}: not emitted by Group.scale (Pickles-recursion-internal); coeff-freeness from proof-systems`);
  }
}
console.log('\n=== ' + (fails ? `RED — ${fails} check(s) failed` : 'GREEN — VarBaseMul + CompleteAdd are o1js-emitted and coeff-free, matching the Lean emitters') + ' ===');
process.exit(fails ? 1 : 0);

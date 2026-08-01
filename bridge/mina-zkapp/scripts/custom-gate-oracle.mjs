// R1 custom-gate oracle — dump o1js's emitted gate rows (typ/wires/coeffs) for
// tiny circuits that each use ONE custom kimchi gate, so a Lean emitter can be
// byte-diffed against them. READ-ONLY oracle; o1js is the byte target.
import { Field, Poseidon, Group, Provable } from 'o1js';

async function dumpGates(label, f) {
  const cs = await Provable.constraintSystem(f);
  console.log(`\n===== ${label} =====`);
  console.log(`rows=${cs.rows}  publicInputSize=${cs.publicInputSize}`);
  console.log('summary:', JSON.stringify(cs.summary()));
  // Only show gates that are NOT plain Generic/Zero, plus a couple of context rows.
  cs.gates.forEach((g, i) => {
    console.log(
      `[${i}] typ=${g.type} nWires=${g.wires.length} nCoeffs=${g.coeffs.length}`
    );
    if (g.type !== 'Generic' && g.type !== 'Zero') {
      console.log('     wires =', JSON.stringify(g.wires));
      console.log('     coeffs=', JSON.stringify(g.coeffs));
    }
  });
}

// (1) complete_add — one EC point addition on the Pallas curve.
await dumpGates('complete_add: Group g1 + g2', () => {
  const g1 = Provable.witness(Group, () => Group.generator);
  const g2 = Provable.witness(Group, () => Group.generator.add(Group.generator));
  const s = g1.add(g2);
  Provable.asProver(() => {});
  s.x.seal();
});

// (2) poseidon — one hash of two field elements.
await dumpGates('poseidon: Poseidon.hash([1,2])', () => {
  const a = Provable.witness(Field, () => Field(1));
  const b = Provable.witness(Field, () => Field(2));
  Poseidon.hash([a, b]).seal();
});

// STAGE 1 measurement: does Provable.switch emit an exclusivity (Sigma mask == 1) gate?
// Independent reproduction. o1js 2.15.0.
import { Field, Bool, Provable } from 'o1js';

function summarize(label, cs) {
  console.log(`\n### ${label}`);
  console.log(`rows: ${cs.rows}`);
  console.log(`digest: ${cs.digest}`);
  const kinds = {};
  for (const g of cs.gates) kinds[g.type] = (kinds[g.type] ?? 0) + 1;
  console.log(`gate kinds: ${JSON.stringify(kinds)}`);
  // dump the Generic coefficient halves so we can read what is actually constrained
  let half = 0;
  for (const g of cs.gates) {
    if (g.type === 'Generic') {
      const c = g.coeffs;
      // Generic gates pack TWO halves of 5 coeffs: l*w0 + r*w1 + o*w2 + m*w0*w1 + c
      for (let k = 0; k < c.length; k += 5) {
        const [l, r, o, m, cc] = c.slice(k, k + 5);
        console.log(`  half[${half++}] l=${l} r=${r} o=${o} m=${m} c=${cc}`);
      }
    }
  }
  return cs;
}

// 1. Three WITNESSED Bools (non-constant mask) -> switch over 3 field values.
const csSwitch = await Provable.constraintSystem(() => {
  const m0 = Provable.witness(Bool, () => Bool(true));
  const m1 = Provable.witness(Bool, () => Bool(false));
  const m2 = Provable.witness(Bool, () => Bool(false));
  const out = Provable.switch([m0, m1, m2], Field, [Field(10), Field(20), Field(30)]);
  // consume the output so it is not dead-code eliminated
  out.mul(Field(1)).assertEquals(out);
});
summarize('switch([w,w,w], Field, [10,20,30])  -- default (exclusive expected)', csSwitch);

// 2. IDENTICAL but with allowNonExclusive: true -> if digests match, the option
//    emits NO constraints, i.e. the "check" is purely off-circuit.
const csLax = await Provable.constraintSystem(() => {
  const m0 = Provable.witness(Bool, () => Bool(true));
  const m1 = Provable.witness(Bool, () => Bool(false));
  const m2 = Provable.witness(Bool, () => Bool(false));
  const out = Provable.switch([m0, m1, m2], Field, [Field(10), Field(20), Field(30)], {
    allowNonExclusive: true,
  });
  out.mul(Field(1)).assertEquals(out);
});
summarize('switch(..., {allowNonExclusive:true})', csLax);

// 3. CONTROL: what an exclusivity gate would COST, to show it is absent above.
const csWithSum = await Provable.constraintSystem(() => {
  const m0 = Provable.witness(Bool, () => Bool(true));
  const m1 = Provable.witness(Bool, () => Bool(false));
  const m2 = Provable.witness(Bool, () => Bool(false));
  const out = Provable.switch([m0, m1, m2], Field, [Field(10), Field(20), Field(30)]);
  // the gate the gadget does NOT emit:
  m0.toField().add(m1.toField()).add(m2.toField()).assertEquals(Field(1));
  out.mul(Field(1)).assertEquals(out);
});
summarize('switch + EXPLICIT Sigma mask == 1 (control)', csWithSum);

console.log('\n=== VERDICT LINES ===');
console.log(`SENTINEL digest_default=${csSwitch.digest}`);
console.log(`SENTINEL digest_allowNonExclusive=${csLax.digest}`);
console.log(`SENTINEL digest_with_sum_gate=${csWithSum.digest}`);
console.log(
  `SENTINEL default_equals_lax=${csSwitch.digest === csLax.digest ? 'IDENTICAL' : 'DIFFERENT'}`
);
console.log(
  `SENTINEL sumgate_changes_cs=${csSwitch.digest !== csWithSum.digest ? 'YES' : 'NO'}`
);
console.log(`SENTINEL rows_default=${csSwitch.rows} rows_with_sum=${csWithSum.rows}`);

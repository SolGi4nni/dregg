// What would it cost o1js to close this in-circuit?
// Note the documented semantics: an ALL-FALSE mask legitimately returns 0
// (o1js tests that at provable.test.ts:54). So the correct in-circuit gate is
// "at most one", i.e. Sigma mask <= 1 -- NOT Sigma mask == 1.
import { Field, Bool, Provable } from 'o1js';

const N_CASES = [2, 3, 4, 8, 16];

function maskAndValues(n) {
  const mask = Array.from({ length: n }, (_, i) =>
    Provable.witness(Bool, () => Bool(i === 0))
  );
  const values = Array.from({ length: n }, (_, i) =>
    Provable.witness(Field, () => Field(10 * (i + 1)))
  );
  return { mask, values };
}

console.log('n\tbase\teq\tle\tchain\td_eq\t\td_le\t\td_chain');
for (const n of N_CASES) {
  const base = await Provable.constraintSystem(() => {
    const { mask, values } = maskAndValues(n);
    Provable.switch(mask, Field, values, { allowNonExclusive: true }).assertEquals(
      Provable.witness(Field, () => Field(10))
    );
  });

  const eq = await Provable.constraintSystem(() => {
    const { mask, values } = maskAndValues(n);
    const out = Provable.switch(mask, Field, values, { allowNonExclusive: true });
    mask
      .reduce((a, b) => a.add(b.toField()), Field(0))
      .assertEquals(Field(1)); // exactly-one: BREAKS the documented all-false case
    out.assertEquals(Provable.witness(Field, () => Field(10)));
  });

  const le = await Provable.constraintSystem(() => {
    const { mask, values } = maskAndValues(n);
    const out = Provable.switch(mask, Field, values, { allowNonExclusive: true });
    // at-most-one: PRESERVES all-false -> 0
    mask
      .reduce((a, b) => a.add(b.toField()), Field(0))
      .assertLessThanOrEqual(Field(1));
    out.assertEquals(Provable.witness(Field, () => Field(10)));
  });

  // the cheap standard at-most-one for bits already known boolean:
  // keep a running OR of the bits seen, and forbid a bit that follows a set bit.
  const chain = await Provable.constraintSystem(() => {
    const { mask, values } = maskAndValues(n);
    const out = Provable.switch(mask, Field, values, { allowNonExclusive: true });
    let seen = Bool(false);
    for (const b of mask) {
      b.and(seen).assertFalse(); // no second true
      seen = seen.or(b);
    }
    out.assertEquals(Provable.witness(Field, () => Field(10)));
  });

  console.log(
    `${n}\t${base.rows}\t${eq.rows}\t${le.rows}\t${chain.rows}\t+${eq.rows - base.rows}\t\t+${
      le.rows - base.rows
    }\t\t+${chain.rows - base.rows}`
  );
}
console.log('\nSENTINEL fix_cost_measured=yes');

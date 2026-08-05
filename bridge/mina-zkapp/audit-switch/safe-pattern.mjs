// Verify the SAFE-PATTERN criterion used to triage real callers.
// Claim under test: a mask built as [idx.equals(0), idx.equals(1), idx.equals(2)]
// over ONE constrained Field is at-most-one-hot IN-CIRCUIT, so `Provable.switch`
// is safe there even though switch itself pins nothing.
// If that claim is wrong, every "SAFE" verdict in the survey is wrong too.
import { Field, Bool, Provable, ZkProgram } from 'o1js';

// A: can a prover force the DERIVED mask to sum to 2? It must be unsatisfiable.
const Derived = ZkProgram({
  name: 'derived-mask-sums-to-two',
  publicOutput: Field,
  methods: {
    tryIt: {
      privateInputs: [Field],
      async method(idx) {
        const mask = [0, 1, 2].map((i) => idx.equals(Field(i)));
        const sum = mask[0].toField().add(mask[1].toField()).add(mask[2].toField());
        sum.assertEquals(Field(2)); // demand a NON-exclusive derived mask
        const out = Provable.switch(mask, Field, [Field(10), Field(20), Field(30)], {
          allowNonExclusive: true,
        });
        return { publicOutput: out };
      },
    },
  },
});

await Derived.compile({ forceRecompile: true });
let a = 'PROVED_MASK_SUM_2_UNSAFE';
try {
  for (const cand of [0n, 1n, 2n, 3n, 7n]) {
    await Derived.tryIt(Field(cand));
    a = `PROVED with idx=${cand} -- CRITERION IS WRONG`;
    break;
  }
} catch (e) {
  a = `refused: ${String(e.message).split('\n')[0].slice(0, 80)}`;
}
console.log(`SENTINEL derived_mask_can_sum_to_2=${a}`);

// B: the equals-derived mask still lets the prover pick WHICH branch (that is fine
// and intended), but the output is always exactly one branch value or 0.
const Honest = ZkProgram({
  name: 'derived-mask-honest',
  publicOutput: Field,
  methods: {
    pick: {
      privateInputs: [Field],
      async method(idx) {
        const mask = [0, 1, 2].map((i) => idx.equals(Field(i)));
        const out = Provable.switch(mask, Field, [Field(10), Field(20), Field(30)], {
          allowNonExclusive: true,
        });
        return { publicOutput: out };
      },
    },
  },
});
await Honest.compile({ forceRecompile: true });
for (const cand of [0n, 1n, 2n, 5n]) {
  const p = (await Honest.pick(Field(cand))).proof;
  console.log(`SENTINEL derived_idx=${cand} output=${p.publicOutput.toString()}`);
}

// C: CONTRAST -- an INDEPENDENTLY WITNESSED mask (the unsafe pattern) CAN sum to 2.
const Witnessed = ZkProgram({
  name: 'witnessed-mask-sums-to-two',
  publicOutput: Field,
  methods: {
    tryIt: {
      privateInputs: [Bool, Bool, Bool],
      async method(m0, m1, m2) {
        const sum = m0.toField().add(m1.toField()).add(m2.toField());
        sum.assertEquals(Field(2));
        const out = Provable.switch([m0, m1, m2], Field, [Field(10), Field(20), Field(30)], {
          allowNonExclusive: true,
        });
        return { publicOutput: out };
      },
    },
  },
});
await Witnessed.compile({ forceRecompile: true });
let c;
try {
  const p = (await Witnessed.tryIt(Bool(true), Bool(true), Bool(false))).proof;
  c = `PROVED output=${p.publicOutput.toString()}`;
} catch (e) {
  c = `refused: ${String(e.message).split('\n')[0].slice(0, 80)}`;
}
console.log(`SENTINEL witnessed_mask_can_sum_to_2=${c}`);
console.log('\n=== DONE ===');

// SEVERITY PROBE: is the mask constrained to {0,1}?
// If booleanity is NOT enforced, the attack is not "sum of branches" but
// "arbitrary SCALAR MULTIPLE of a branch", which is far worse.
// If it IS enforced, the reachable set is exactly the subset-sums of the branches.
import { Field, Bool, UInt64, Provable, ZkProgram, verify } from 'o1js';

const TIER_AMOUNTS = [UInt64.from(100), UInt64.from(250), UInt64.from(500)];
const VAULT_BALANCE = UInt64.from(1_000_000);

// --- A: mask arrives as a ZkProgram PRIVATE INPUT of declared type Bool
const ViaInput = ZkProgram({
  name: 'bool-input-check',
  publicOutput: UInt64,
  methods: {
    withdraw: {
      privateInputs: [Bool, Bool, Bool],
      async method(m0, m1, m2) {
        const amount = Provable.switch([m0, m1, m2], UInt64, TIER_AMOUNTS, {
          allowNonExclusive: true,
        });
        amount.assertLessThanOrEqual(VAULT_BALANCE);
        return { publicOutput: amount };
      },
    },
  },
});

const vk = (await ViaInput.compile({ forceRecompile: true })).verificationKey;
console.log(`SENTINEL vk=${vk.hash.toString()}`);

// honest sanity check
const good = (await ViaInput.withdraw(Bool(false), Bool(true), Bool(false))).proof;
console.log(`SENTINEL honest_amount=${good.publicOutput.toString()}`);
console.log(`SENTINEL honest_verifies=${await verify(good.toJSON(), vk)}`);

// non-exclusive but still boolean
const nonExcl = (await ViaInput.withdraw(Bool(true), Bool(true), Bool(false))).proof;
console.log(`SENTINEL nonexclusive_amount=${nonExcl.publicOutput.toString()}`);
console.log(`SENTINEL nonexclusive_verifies=${await verify(nonExcl.toJSON(), vk)}`);

// NOW: a "Bool" whose underlying field is 7, smuggled in via the unsafe constructor.
// This models a prover who hands the circuit a non-boolean where a Bool is declared.
const seven = Bool.Unsafe.fromField(Field(7));
let ampAmount = null;
let ampVerifies = null;
try {
  const amp = (await ViaInput.withdraw(seven, Bool(false), Bool(false))).proof;
  ampAmount = amp.publicOutput.toString();
  ampVerifies = await verify(amp.toJSON(), vk);
} catch (e) {
  ampAmount = `REFUSED: ${String(e.message).split('\n')[0].slice(0, 120)}`;
}
console.log(`SENTINEL amplified_amount=${ampAmount}   (tier0 = 100)`);
console.log(`SENTINEL amplified_verifies=${ampVerifies}`);

// --- B: what does the constraint system say? count booleanity gates on ZkProgram inputs
const cs = await ViaInput.analyzeMethods();
const g = cs.withdraw.gates;
let boolHalves = 0;
const NEG1 = 28948022309329048855892746252171976963363056481941560715954676764349967630336n;
for (const gate of g) {
  if (gate.type !== 'Generic') continue;
  for (let k = 0; k < gate.coeffs.length; k += 5) {
    const [l, r, o, m, c] = gate.coeffs.slice(k, k + 5).map(BigInt);
    // booleanity has the shape  -w + w*w = 0  =>  l = -1, m = 1, r = o = c = 0
    if (l === NEG1 && m === 1n && r === 0n && o === 0n && c === 0n) boolHalves++;
  }
}
console.log(`SENTINEL booleanity_halves_in_zkprogram=${boolHalves}  (expect 3 if inputs are checked)`);
console.log(`SENTINEL total_rows=${cs.withdraw.rows}`);
console.log('\n=== DONE ===');

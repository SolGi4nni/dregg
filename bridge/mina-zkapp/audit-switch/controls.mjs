// NEGATIVE CONTROLS for the falsifier.
// "verifies=true" is worthless unless this verify path CAN return false.
// Three things must go red here, or the falsifier proves nothing:
//   C1. a tampered proof must FAIL
//   C2. a proof must FAIL against a DIFFERENT circuit's VK
//   C3. adding the missing `Sigma mask == 1` gate must CHANGE the VK *and*
//       make the non-exclusive witness UNPROVABLE (constraint unsatisfied)
import { Bool, UInt64, Field, Provable, ZkProgram, verify } from 'o1js';

let LAX = false;
let ADD_SUM_GATE = false;

const VAULT_BALANCE = UInt64.from(1_000_000);
const TIER_AMOUNTS = [UInt64.from(100), UInt64.from(250), UInt64.from(500)];

const Vault = ZkProgram({
  name: 'switch-vault-control',
  publicOutput: UInt64,
  methods: {
    withdraw: {
      privateInputs: [Bool, Bool, Bool],
      async method(m0, m1, m2) {
        const amount = Provable.switch([m0, m1, m2], UInt64, TIER_AMOUNTS, {
          allowNonExclusive: LAX,
        });
        if (ADD_SUM_GATE) {
          // THE FIX: constrain the mask to be one-hot, in-circuit.
          m0.toField().add(m1.toField()).add(m2.toField()).assertEquals(Field(1));
        }
        amount.assertLessThanOrEqual(VAULT_BALANCE);
        return { publicOutput: amount };
      },
    },
  },
});

// unrelated circuit, to supply a foreign VK for C2
const Other = ZkProgram({
  name: 'switch-vault-control-other',
  publicOutput: UInt64,
  methods: {
    withdraw: {
      privateInputs: [Bool, Bool, Bool],
      async method(m0, m1, m2) {
        const amount = Provable.switch([m0, m1, m2], UInt64, TIER_AMOUNTS, {
          allowNonExclusive: true,
        });
        amount.assertLessThanOrEqual(UInt64.from(999_999));
        amount.assertGreaterThan(UInt64.from(0));
        return { publicOutput: amount };
      },
    },
  },
});

// ---------------------------------------------------------------- vulnerable build
LAX = false;
ADD_SUM_GATE = false;
const vulnVk = (await Vault.compile({ forceRecompile: true })).verificationKey;
console.log(`SENTINEL vuln_vk=${vulnVk.hash.toString()}`);

LAX = true;
const badProof = (await Vault.withdraw(Bool(true), Bool(true), Bool(false))).proof;
console.log(`SENTINEL badproof_amount=${badProof.publicOutput.toString()}`);
console.log(`SENTINEL C0_baseline_verifies=${await verify(badProof.toJSON(), vulnVk)}`);

// ---------------------------------------------------------------- C1: tampered proof
const json = badProof.toJSON();
const tampered = JSON.parse(JSON.stringify(json));
tampered.publicOutput[0] = '999';
let c1;
try {
  c1 = await verify(tampered, vulnVk);
} catch (e) {
  c1 = `threw: ${String(e.message).split('\n')[0]}`;
}
console.log(`SENTINEL C1_tampered_verifies=${c1}`);

// ---------------------------------------------------------------- C2: foreign VK
const otherVk = (await Other.compile({ forceRecompile: true })).verificationKey;
console.log(`SENTINEL other_vk=${otherVk.hash.toString()}`);
let c2;
try {
  c2 = await verify(badProof.toJSON(), otherVk);
} catch (e) {
  c2 = `threw: ${String(e.message).split('\n')[0]}`;
}
console.log(`SENTINEL C2_foreign_vk_verifies=${c2}`);

// ---------------------------------------------------------------- C3: the fix
LAX = false;
ADD_SUM_GATE = true;
const fixedVk = (await Vault.compile({ forceRecompile: true })).verificationKey;
console.log(`SENTINEL fixed_vk=${fixedVk.hash.toString()}`);
console.log(
  `SENTINEL C3a_fix_changes_vk=${fixedVk.hash.toString() !== vulnVk.hash.toString()}`
);
// the old bad proof must not verify against the fixed VK
let c3b;
try {
  c3b = await verify(badProof.toJSON(), fixedVk);
} catch (e) {
  c3b = `threw: ${String(e.message).split('\n')[0]}`;
}
console.log(`SENTINEL C3b_badproof_vs_fixed_vk=${c3b}`);

// and with the fix in place, the non-exclusive mask must be UNPROVABLE even lax
LAX = true;
ADD_SUM_GATE = true;
let c3c;
try {
  await Vault.withdraw(Bool(true), Bool(true), Bool(false));
  c3c = 'PROVED_ANYWAY_BAD';
} catch (e) {
  c3c = `refused: ${String(e.message).split('\n')[0].slice(0, 90)}`;
}
console.log(`SENTINEL C3c_fixed_circuit_refuses_nonexclusive=${c3c}`);

// sanity: with the fix, an HONEST one-hot mask still proves and verifies
LAX = false;
ADD_SUM_GATE = true;
const goodProof = (await Vault.withdraw(Bool(false), Bool(true), Bool(false))).proof;
console.log(`SENTINEL C3d_fixed_honest_amount=${goodProof.publicOutput.toString()}`);
console.log(
  `SENTINEL C3d_fixed_honest_verifies=${await verify(goodProof.toJSON(), fixedVk)}`
);
console.log('\n=== CONTROLS DONE ===');

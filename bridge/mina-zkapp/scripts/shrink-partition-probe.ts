import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { shrinkShapeOf, shrinkValues } from '../src/MinaShrinkVerify.js';
import { rootClaim, rootValues } from '../src/RootConsume.js';
import { verifyPlan, makeDreggProofClaim } from '../src/DreggProofVerify.js';
import { NUM_CHAIN_CLAIMS } from '../src/RootClaim.js';

// PROBE — settle the claim-binding question against the REAL fixture:
//   * what is `air.numPublicValues` for the shrink shape?
//   * what does `claim.publicValues` hold, and are the 41 claim lanes in it?
//   * plan.derive / plan.nBatches for the derive:true (partition step0) shape.
function main() {
  const p =
    process.env.MINA_SHRINK_FIXTURE ??
    resolve(process.cwd(), '.fullchain', 'mina-shrink-fixture.json');
  const fx = JSON.parse(readFileSync(p, 'utf8'));
  const sh = shrinkShapeOf(fx);
  const v = shrinkValues(fx);

  console.log('=== SHAPE ===');
  console.log('air.numPublicValues     :', sh.air.numPublicValues);
  console.log('air.degreeBits          :', sh.air.degreeBits);
  console.log('air.baseDegreeBits      :', sh.air.baseDegreeBits);
  console.log('air.preprocessedWidth   :', sh.air.preprocessedWidth);
  console.log('batches.length          :', sh.batches.length);
  console.log('knobs                   :', JSON.stringify(sh.knobs));
  console.log('deriveChallenges(sh)    :', (sh as any).deriveChallenges);
  console.log('constraints present     :', !!sh.constraints);

  const planCarry = verifyPlan(sh);
  console.log('\n=== PLAN (as MinaShrinkVerify uses it) ===');
  console.log('plan.derive             :', planCarry.derive);
  console.log('plan.nBatches           :', planCarry.nBatches);
  console.log('plan.nOpenedTrace       :', planCarry.nOpenedTrace);
  console.log('plan.nQuotientVals      :', planCarry.nQuotientVals);

  const shHead = { ...sh, deriveChallenges: true } as any;
  const planHead = verifyPlan(shHead);
  console.log('\n=== PLAN (derive:true, partition step0) ===');
  console.log('planHead.derive         :', planHead.derive);
  console.log('planHead.nBatches       :', planHead.nBatches);

  const Claim = makeDreggProofClaim(sh);
  const claim = rootClaim(sh, v, Claim);
  const pv = (claim as any).publicValues.map((f: any) => f.toBigInt?.() ?? BigInt(f.toString()));
  console.log('\n=== CLAIM ===');
  console.log('claim.publicValues len  :', pv.length);
  console.log('claim.publicValues[0..8]:', pv.slice(0, 8).map(String));

  const cl = (fx.claimLanes as number[]).slice(0, NUM_CHAIN_CLAIMS).map((x) => BigInt(x));
  console.log('\n=== BINDING CHECK ===');
  console.log('claimLanes (25) [0..4]  :', cl.slice(0, 5).map(String));
  const pvSet = new Set(pv.map(String));
  const inPv = cl.filter((x) => pvSet.has(String(x)));
  console.log(`claim lanes present in claim.publicValues: ${inPv.length}/${NUM_CHAIN_CLAIMS}`);
  console.log('rootValues.publicValues len:', (v as any).publicValues?.length);
  console.log(
    'rootValues.publicValues[0..8]:',
    ((v as any).publicValues ?? []).slice(0, 8).map(String),
  );
}
main();

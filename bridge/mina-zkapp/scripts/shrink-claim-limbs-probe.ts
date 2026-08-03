import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { shrinkShapeOf, shrinkValues } from '../src/MinaShrinkVerify.js';
import { rootWitness } from '../src/RootConsume.js';
import { EXT_D } from '../src/FriQueryStep.js';
import { NUM_CHAIN_CLAIMS } from '../src/RootClaim.js';
import { claimTraceOffset as offOf } from '../src/MinaShrinkPartition.js';

// Are the claim columns base-only (limbs 1..3 == 0) in the FLAT openedTrace the
// circuit sees? readSealedClaim asserts that; if false, the assert bites.
const P = 2n ** 31n - 1n;
function main() {
  const p =
    process.env.MINA_SHRINK_FIXTURE ??
    resolve(process.cwd(), '.fullchain', 'mina-shrink-fixture.json');
  const fx = JSON.parse(readFileSync(p, 'utf8'));
  const sh = shrinkShapeOf(fx);
  const v = shrinkValues(fx);
  const w = rootWitness(sh, v);
  const oT = w[0] as any[]; // BbExt[] openedTrace
  const off = offOf(sh, fx.claimInstance);
  console.log('offset:', off, 'openedTrace len:', oT.length);
  let nonzero = 0;
  let outOfRange = 0;
  for (let i = 0; i < NUM_CHAIN_CLAIMS; i++) {
    const e = oT[off + EXT_D * i];
    const limbs = e.limbs.map((f: any) => f.toBigInt());
    if (limbs[1] !== 0n || limbs[2] !== 0n || limbs[3] !== 0n) {
      if (nonzero < 6) console.log(`  col ${EXT_D * i}: limbs = [${limbs.join(', ')}]  (limbs 1..3 NOT zero)`);
      nonzero++;
    }
    if (limbs[0] > P) outOfRange++;
  }
  console.log(`\nlanes with nonzero limbs 1..3: ${nonzero}/${NUM_CHAIN_CLAIMS}`);
  console.log(`lanes with base > 2^31-1     : ${outOfRange}/${NUM_CHAIN_CLAIMS}`);
  console.log('lane0 base:', oT[off].limbs[0].toBigInt(), 'lane16 base:', oT[off + EXT_D * 16].limbs[0].toBigInt());
}
main();

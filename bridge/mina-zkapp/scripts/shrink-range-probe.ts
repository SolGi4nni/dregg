import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { shrinkShapeOf, shrinkValues } from '../src/MinaShrinkVerify.js';
import { rootWitness, rootClaim } from '../src/RootConsume.js';

// Are all opened-value limbs (and claim digest limbs) canonical (< 2^31)? A
// range-check lookup miss during prove says one is not.
const P = 2n ** 31n - 1n;
function main() {
  const p =
    process.env.MINA_SHRINK_FIXTURE ??
    resolve(process.cwd(), '.fullchain', 'mina-shrink-fixture.json');
  const fx = JSON.parse(readFileSync(p, 'utf8'));
  const sh = shrinkShapeOf(fx);
  const v = shrinkValues(fx);
  const w = rootWitness(sh, v);
  const [oT, oQ] = w;
  let bad = 0;
  const checkArr = (arr: any[], name: string) => {
    let n = 0;
    arr.forEach((e: any, i: number) => {
      e.limbs.forEach((l: any, j: number) => {
        const val = l.toBigInt();
        if (val > P) {
          if (n < 6) console.log(`  ${name}[${i}].limb[${j}] = ${val} > 2^31-1`);
          n++;
          bad++;
        }
      });
    });
    console.log(`${name}: ${arr.length} ext values, ${n} out-of-range limbs`);
  };
  checkArr(oT, 'openedTrace');
  checkArr(oQ, 'openedQuotient');

  // claim digest limbs (Pasta) — informational: these are 254-bit, expected big.
  const Claim = (sh as any);
  console.log('\nsuite:', (sh.suite as any)?.label ?? '(unnamed)');
  console.log('inputCommits raw[0]:', JSON.stringify(fx.commits?.[0] ?? fx.inputRounds?.[0]?.commit ?? '(n/a)').slice(0, 120));
  console.log(`\nTOTAL out-of-range opened limbs: ${bad}`);
}
main();

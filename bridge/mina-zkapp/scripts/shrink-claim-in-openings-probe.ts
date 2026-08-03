import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { shrinkShapeOf, shrinkValues } from '../src/MinaShrinkVerify.js';
import { NUM_CHAIN_CLAIMS } from '../src/RootClaim.js';

// Is the exposed claim SEALABLE? Instance `claimInstance` (expose_claim,
// degreeBits=0 → constant trace) evaluates at ζ to its trace cell = the claim
// lane. Those opened trace values are authenticated by the walk. So if the 41
// claim lanes appear among `v.opened[round0][claimInstance]`, the claim can be
// bound to the committed trace rather than riding as a free witness.
function main() {
  const p =
    process.env.MINA_SHRINK_FIXTURE ??
    resolve(process.cwd(), '.fullchain', 'mina-shrink-fixture.json');
  const fx = JSON.parse(readFileSync(p, 'utf8'));
  const sh = shrinkShapeOf(fx);
  const v = shrinkValues(fx);
  const ci = fx.claimInstance as number;
  const cl = (fx.claimLanes as number[]).map((x) => BigInt(x));

  console.log('claimInstance:', ci, ' degreeBits:', fx.degreeBits);
  console.log('nBatches (rounds):', sh.batches.length);
  for (let ri = 0; ri < sh.batches.length; ri++) {
    console.log(
      `  round ${ri}: ${sh.batches[ri].matrices.length} matrices, ` +
        `numPoints/cols: ${sh.batches[ri].matrices
          .map((m: any) => `${m.numPoints}x${m.numCols}`)
          .join(', ')}`,
    );
  }

  // v.opened[round][matrix][point] = array of (numCols * EXT_D) base lanes.
  // Round 0 = main trace. Find the matrix whose opened value at point 0 matches
  // the claim lanes (base components; ext limbs should be 0 for a base value).
  const r0 = v.opened[0];
  console.log('\nround0 matrices:', r0.length);
  for (let mi = 0; mi < r0.length; mi++) {
    const pt0 = r0[mi][0] as number[]; // point 0 flat base lanes
    const numCols = sh.batches[0].matrices[mi].numCols;
    // Extract base component of each column (every EXT_D-th lane).
    const EXT_D = 4;
    const bases: bigint[] = [];
    for (let c = 0; c < numCols; c++) bases.push(BigInt(pt0[c * EXT_D]));
    // Does the sequence of column-base values match the claim lanes?
    const matchFirst25 = cl.slice(0, NUM_CHAIN_CLAIMS).every((x, i) => bases[i] === x);
    const match41 = cl.every((x, i) => bases[i] === x);
    console.log(
      `  matrix ${mi}: numCols=${numCols} pt0.len=${pt0.length} ` +
        `bases[0..4]=${bases.slice(0, 5).map(String)} ` +
        `match25=${matchFirst25} match41=${match41}`,
    );
  }

  // Also: for the claim matrix specifically, print alignment detail.
  console.log('\nclaim lanes[0..4]:', cl.slice(0, 5).map(String));
}
main();

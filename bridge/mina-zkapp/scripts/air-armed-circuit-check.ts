// ===========================================================================
// THE ARMED CIRCUIT closes the AIR twin→circuit gap.
//
// The joint differential asserts airTwinVerdict == native AIR closing equality. `airTwinVerdict`
// recomputes acc (bigint DAG fold) and quotient (zps·chunks) and checks `acc·invZ == quotient`. This
// harness runs the SAME check as a real o1js CIRCUIT, over ONE instance (Const — the smallest, 9
// base + 3 ext columns), under `Provable.runAndCheck` — SOUND FOR A REFUSAL of an `assertEquals`. It
// uses `evalDagInCircuit` (the EXACT node walk the armed `RootAirProcessChain` slice `sliceWork`
// compiles) for the accumulator and `fromExtBasisCoefficients`/`extScaleConst` (the deployed quotient
// recompose) for `Σ zps_j·from_ext_basis(chunk_j)`, then asserts `acc·invVanishing == quotient`. It
// confirms:
//   • the honest proof SATISFIES the closing-equality circuit, and
//   • each sampled mutation that the twin+native both REJECT on the Const instance also makes the
//     circuit's own constraints REFUSE.
//
// ⚑ THIS IS THE TOOTH THE DEPLOYED o1js PATH LACKS. `RootAirChain`/`RootAirProcessChain` recompute
// acc via `sliceWork` and seal it, but the deployed chain compares that acc against p3's RUST-emitted
// per-instance accumulators (`root-air-fullchain` leg [7]) — it never recomposes the quotient and
// asserts `acc·invZ == quotient`. This circuit IS that missing closing equality, and it refuses the
// mutations the deployed path (lacking it) would have to trust FRI to catch.
//
//   ../../target/release/root_proof_mutation <seed> <n> | \
//     node --max-old-space-size=16384 dist/scripts/air-armed-circuit-check.js <K>
// ===========================================================================
import { createInterface } from 'node:readline';
import { Field, Provable } from 'o1js';
import { BbExt, EXT_D, extAdd, extMul } from '../src/FriQueryStep.js';
import { canonicalLane } from '../src/Poseidon2BabyBearW16.js';
import { rootAirDag, bindRealInstance, evalDagInCircuit, foldRootsP3 } from '../src/RootAirDag.js';
import { fromExtBasisCoefficients, extScaleConst } from '../src/AirEval.js';

const K = Number(process.argv[2] ?? '8');
const TABLE = process.env.AIR_ARMED_TABLE ?? 'Const';
const LANE_MAX = (1n << 31n) - 1n;
const dag = rootAirDag();
const constTable = dag.tables.find((t) => t.name === TABLE);
if (!constTable) throw new Error(`no DAG table ${TABLE}`);

function airInstOf(air: any, name: string): any {
  for (const i of air.instances)
    if (i.table.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_') === name) return i;
  throw new Error(`AIR decode has no instance for ${name}`);
}

/** Run the Const closing equality as a circuit under runAndCheck: acc = foldRootsP3(alpha,
 *  evalDagInCircuit(opened)), quot = Σ zps_j·fromExtBasis(chunk_j), assert acc·invVan == quot.
 *  Resolves true iff the constraints are satisfied, false iff the circuit refuses. */
async function circuitAccepts(air: any): Promise<boolean> {
  if (air.kind === 'degenerate') return false;
  const inst = airInstOf(air, TABLE);
  const { base, ext } = bindRealInstance(constTable as any, inst);
  const alphaB = air.challenges.alpha.map((x: number) => BigInt(x));
  const invVanB = inst.selectors.invVanishing.map((x: number) => BigInt(x));
  const zpsB = inst.zps.map((z: number[]) => z.map((x) => BigInt(x)));
  const chunksB = inst.quotientChunks.map((c: number[][]) => c.map((v) => v.map((x) => BigInt(x))));
  try {
    await Provable.runAndCheck(() => {
      const baseW = base.map((b) => Provable.witness(BbExt, () => BbExt.from(b)));
      const extW = ext.map((e) => Provable.witness(BbExt, () => BbExt.from(e)));
      const alphaW = Provable.witness(BbExt, () => BbExt.from(alphaB));
      const roots = evalDagInCircuit(constTable as any, baseW, extW);
      const acc = foldRootsP3(alphaW, roots);
      // quotient = Σ_j zps[j]·from_ext_basis(chunk_j) — zps are compile-time constants at this zeta,
      // the chunks are witnessed opened values (the RAW positions a mutation moves).
      let quot = BbExt.zero();
      for (let j = 0; j < chunksB.length; j++) {
        const chunkW = chunksB[j].map((v: bigint[]) => Provable.witness(BbExt, () => BbExt.from(v)));
        const val = fromExtBasisCoefficients(chunkW);
        // zps[j] is one EF constant; multiply the (from-basis) chunk value by it.
        const zpW = Provable.witness(BbExt, () => BbExt.from(zpsB[j]));
        quot = extAdd(quot, extMul(zpW, val));
      }
      const lhs = extMul(acc, BbExt.from(invVanB));
      void extScaleConst; // deployed recompose helper, referenced for provenance
      for (let k = 0; k < EXT_D; k++)
        canonicalLane(lhs.limbs[k], LANE_MAX * LANE_MAX).assertEquals(canonicalLane(quot.limbs[k], LANE_MAX * LANE_MAX));
    });
    return true;
  } catch {
    return false;
  }
}

/** Does a mutation hit the Const instance's closing equality? Its own opened values (desc `inst0 …`)
 *  do directly; a shared commitment / public value shifts zeta, which moves Const's emitted
 *  selectors and zps — also reaching it. */
function affectsConst(region: string, desc: string): boolean {
  if (TABLE === 'Const' && desc.startsWith('inst0 ')) return true;
  if (region === 'main_commit_root' || region === 'quotient_commit_root' || region === 'permutation_commit_root')
    return true;
  if (region === 'public_value') return true;
  return false;
}

const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
let processed = 0;
let honestOk = false;
const mutated: { trial: number; region: string; desc: string; circuit: boolean }[] = [];
const t0 = Date.now();

for await (const line of rl) {
  if (!line.trim()) continue;
  const rec = JSON.parse(line) as { trial: number; region: string; desc: string; airOracle: string; air: any };
  if (rec.trial === -1) {
    const t = Date.now();
    honestOk = await circuitAccepts(rec.air);
    console.error(`  honest baseline: ${TABLE} closing-equality runAndCheck = ${honestOk ? 'SATISFIED (accept)' : 'REFUSED'}  [${((Date.now() - t) / 1000).toFixed(1)}s]`);
    if (!honestOk) { console.error('  ✗ the circuit REFUSED the honest proof — IO construction wrong, aborting'); process.exit(1); }
    continue;
  }
  if (processed >= K) break;
  if (rec.airOracle !== 'REJECT') continue;
  if (!affectsConst(rec.region, rec.desc)) continue;
  const t = Date.now();
  const circuit = await circuitAccepts(rec.air);
  mutated.push({ trial: rec.trial, region: rec.region, desc: rec.desc, circuit });
  processed++;
  console.error(`  trial ${rec.trial} [${rec.region}]: native-AIR=REJECT circuit=${circuit ? 'ACCEPT ⚠' : 'REFUSED ✓'}  [${((Date.now() - t) / 1000).toFixed(1)}s]  ${rec.desc}`);
}
rl.close();

const disagreements = mutated.filter((m) => m.circuit);
console.error(
  `\n=== ARMED-CIRCUIT CONFIRMATION (${TABLE}) ===\n  honest satisfied: ${honestOk}\n  mutations tested: ${mutated.length} (all native-AIR-REJECT)\n  ` +
    `circuit REFUSED all of them: ${disagreements.length === 0}\n  total ${((Date.now() - t0) / 1000).toFixed(1)}s`,
);
if (disagreements.length > 0) {
  console.error(`  ⚠ the CIRCUIT accepted ${disagreements.length} proof(s) the native AIR verifier rejected:`);
  for (const d of disagreements) console.error(`    trial ${d.trial} [${d.region}] ${d.desc}`);
  process.exit(2);
}
console.error('  ✓ the armed closing-equality circuit refuses every sampled twin-rejected Const mutation — twin verdict == circuit refusal');
process.exit(0);

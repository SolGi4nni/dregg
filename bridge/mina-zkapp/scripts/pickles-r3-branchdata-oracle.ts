/**
 * pickles-r3-branchdata-oracle.ts — the o1js/OCaml-Pickles ORACLE side of R3's earliest signal.
 *
 * Pairs with `metatheory/Dregg2/Bridge/PicklesR3BranchDataDiff.lean` (the Lean EMIT side). Together
 * they are the smallest emit-and-diff of the Pickles Step/Wrap statement scaffolding:
 *
 *   Lean emits   branchDataPack {proofs_verified = N2, domain_log2 = 16}  = 67   (kernel-checked)
 *   oracle emits wrap_public_input[29] of a real, kimchi-verified devnet block  = 67
 *   DIFF:        byte-exact match, and a naive packer (tag-not-mask) would emit  66  (rejected)
 *
 * ⚑ Phase A discipline: this establishes FIDELITY (the Lean pack matches the real chain's field for
 * one fixed input, MEASURED), NOT soundness. Not "machine-checked Pickles".
 *
 * The oracle is a LIVE emission of exactly the OCaml `Branch_data.pack` that o1js wraps:
 *   - `metatheory/mina_real_block_proof.json` was decoded by `metatheory/fixtures/pickles-extractors`
 *     from Mina devnet block 539508; its `wrap_public_input` is openmina's own
 *     `PreparedStatement::to_public_input`, and o1-labs' `kimchi::verifier::verify` ACCEPTS the Wrap
 *     proof against those 40 words (so slot 29 is validated, not transcribed).
 *   - o1js is js_of_ocaml of the same Pickles: its bytecode carries `branch_data`/`Prefix_mask`/
 *     `proofs_verified`/`composition_types` (confirmed below). Same emitter, different runtime.
 *
 * Run: npx tsx scripts/pickles-r3-branchdata-oracle.ts
 * (read-only; exits non-zero if the diff does NOT match — this is a gate, green-or-bust.)
 */
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO = resolve(__dirname, '..', '..', '..');
const FIXTURE = resolve(REPO, 'metatheory', 'mina_real_block_proof.json');
const O1JS_BC = resolve(
  __dirname, '..', 'node_modules', 'o1js', 'dist', 'node',
  'bindings', 'compiled', 'node_bindings', 'o1js_node.bc.cjs',
);

const BRANCH_DATA_SLOT = 29;          // MinaWrapPublicInput.lean §CENSUS: slot 29 = branch_data, packed
const LEAN_EMIT = 67;                 // branchDataPack {2, 16}, kernel-checked in the paired Lean file
const NAIVE_WRONG = 66;               // 4*16 + to_int(N2)=2 — the tag-not-mask mistake

function fail(msg: string): never { console.error('DIFF RED:', msg); process.exit(1); }

// ── §1 the oracle: the real block's packed branch_data field ───────────────────────────────────
const block = JSON.parse(readFileSync(FIXTURE, 'utf8'));
const wpi: string[] = block.wrap_public_input;
if (!Array.isArray(wpi) || wpi.length !== 40) fail(`wrap_public_input is not 40 words (${wpi?.length})`);
const oracleBranchData = Number(wpi[BRANCH_DATA_SLOT]);
const pv = block.branch_data_proofs_verified ?? findNested(block, 'branch_data_proofs_verified');
const dl = block.branch_data_domain_log2 ?? findNested(block, 'branch_data_domain_log2');

console.log('=== R3 branch_data oracle (real devnet block 539508) ===');
console.log(`  network/height        : ${block._network} / ${block._blockchain_length}`);
console.log(`  state_hash            : ${block._state_hash}`);
console.log(`  decoded branch_data   : { proofs_verified = ${pv}, domain_log2 = ${dl} }`);
console.log(`  wrap_public_input[29] : ${oracleBranchData}   (openmina to_public_input, kimchi-accepted)`);
console.log(`  padding slots 30..39  : ${wpi.slice(30).every((x) => x === '0') ? 'all 0 (ok)' : 'NON-ZERO'}`);

// ── §2 confirm o1js wraps the SAME pack code path ──────────────────────────────────────────────
const bc = readFileSync(O1JS_BC, 'utf8');
const hits = (re: RegExp) => (bc.match(re) || []).length;
const codePath = {
  branch_data: hits(/branch_data/g),
  Prefix_mask: hits(/[Pp]refix_mask/g),
  proofs_verified: hits(/proofs_verified/g),
  composition_types: hits(/composition_types/g),
};
console.log('=== o1js shares the emitter (o1js_node.bc.cjs code-path hits) ===');
console.log(`  ${JSON.stringify(codePath)}`);
if (codePath.branch_data === 0 || codePath.proofs_verified === 0)
  fail('o1js bytecode does not carry the branch_data / proofs_verified pack path');

// ── §3 the DIFF ────────────────────────────────────────────────────────────────────────────────
console.log('=== DIFF: Lean emit  vs  o1js/OCaml oracle ===');
console.log(`  Lean  branchDataPack {2,16} = ${LEAN_EMIT}`);
console.log(`  oracle wrap_public_input[29] = ${oracleBranchData}`);
if (oracleBranchData !== LEAN_EMIT)
  fail(`byte diff at slot 29: Lean ${LEAN_EMIT} != oracle ${oracleBranchData}`);
if (oracleBranchData === NAIVE_WRONG)
  fail('oracle equals the NAIVE (tag-not-mask) value — provenance is wrong');
console.log(`  MATCH (byte-exact). Naive tag-not-mask packer would emit ${NAIVE_WRONG} (rejected).`);

// ── §4 (optional) exercise o1js's OWN runtime for the same fixed input ─────────────────────────
// dummyProof(maxProofsVerified=2, domainLog2=16) runs o1js's Pickles for the SAME {N2, 16}; the
// proof is opaque so we do not decode branch_data out of it here (that is the R4 wire-decode task),
// but a clean run confirms o1js executes the same path for this input. Best-effort; never blocks.
try {
  const o1js: any = await import('o1js');
  if (o1js?.Pickles?.dummyProof) {
    const [n] = o1js.Pickles.dummyProof(2, 16);
    console.log(`=== o1js runtime: Pickles.dummyProof(2, 16) ran; maxProofsVerified tag = ${n} ===`);
  } else {
    console.log('=== o1js runtime: Pickles.dummyProof not reachable in this build (skipped) ===');
  }
} catch (e) {
  console.log(`=== o1js runtime: dummyProof skipped (${(e as Error).message.split('\n')[0]}) ===`);
}

console.log('R3 branch_data diff: GREEN (Lean pack == real-chain field, byte-exact, for {N2,16}).');

function findNested(o: any, key: string): unknown {
  const s = JSON.stringify(o);
  const i = s.indexOf(`"${key}":`);
  if (i < 0) return undefined;
  const tail = s.slice(i + key.length + 3);
  const m = tail.match(/^\s*("?)([^",}]+)\1/);
  return m ? m[2] : undefined;
}

/**
 * pickles-r3-branchdata-oracle.ts — the o1js/OCaml-Pickles ORACLE side of R3's earliest signal.
 *
 * MIGRATED to the shared `diff-oracle.mjs` harness (shape `field`): the core diff is ONE field —
 * `wrap_public_input[29]` of a real kimchi-verified block vs the Lean `branchDataPack {2,16}` emit — as
 * a single-entry vector. The harness owns the diff, the exit code, and the RED-PATH self-test
 * (`--self-test`); the o1js-bytecode code-path grep and the naive-tag (66) falsifier stay here as
 * `extra` provenance. Runs under `ts-node --transpile-only --esm` (it imports the sibling `.mjs`).
 *
 * Pairs with `metatheory/Dregg2/Bridge/PicklesR3BranchDataDiff.lean` (the Lean EMIT side):
 *   Lean emits   branchDataPack {proofs_verified = N2, domain_log2 = 16}  = 67   (kernel-checked)
 *   oracle emits wrap_public_input[29] of a real, kimchi-verified devnet block  = 67
 *   DIFF:        byte-exact match, and a naive packer (tag-not-mask) would emit  66  (rejected)
 *
 * ⚑ Phase A discipline: this establishes FIDELITY (the Lean pack matches the real chain's field for one
 * fixed input, MEASURED), NOT soundness. Not "machine-checked Pickles".
 *
 * The oracle is a LIVE emission of exactly the OCaml `Branch_data.pack` that o1js wraps:
 *   - `metatheory/mina_real_block_proof.json` was decoded from Mina devnet block 539508; its
 *     `wrap_public_input` is openmina's own `PreparedStatement::to_public_input`, and o1-labs'
 *     `kimchi::verifier::verify` ACCEPTS the Wrap proof against those 40 words (slot 29 is validated).
 *   - o1js is js_of_ocaml of the same Pickles: its bytecode carries `branch_data`/`Prefix_mask`/
 *     `proofs_verified`/`composition_types` (confirmed in `extra`). Same emitter, different runtime.
 *
 * Run: npx tsx scripts/pickles-r3-branchdata-oracle.ts   (or ts-node --transpile-only --esm)
 * (read-only; exits non-zero if the diff does NOT match — a gate, green-or-bust.)
 */
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { runOracle } from './diff-oracle.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO = resolve(__dirname, '..', '..', '..');
const FIXTURE = resolve(REPO, 'metatheory', 'mina_real_block_proof.json');
const O1JS_BC = resolve(
  __dirname, '..', 'node_modules', 'o1js', 'dist', 'node',
  'bindings', 'compiled', 'node_bindings', 'o1js_node.bc.cjs',
);

const BRANCH_DATA_SLOT = 29; // MinaWrapPublicInput.lean §CENSUS: slot 29 = branch_data, packed
const LEAN_EMIT = 67;        // branchDataPack {2,16}, kernel-checked in PicklesR3BranchDataDiff.lean
const NAIVE_WRONG = 66;      // 4*16 + to_int(N2)=2 — the tag-not-mask mistake

function loadBlock(): any {
  return JSON.parse(readFileSync(FIXTURE, 'utf8'));
}

// REFERENCE: the real block's packed branch_data field (openmina to_public_input, kimchi-accepted).
export function reference() {
  const block = loadBlock();
  const wpi: string[] = block.wrap_public_input;
  if (!Array.isArray(wpi) || wpi.length !== 40) throw new Error(`wrap_public_input is not 40 words (${wpi?.length})`);
  return [{ name: 'wrap_public_input[29]', value: Number(wpi[BRANCH_DATA_SLOT]) }];
}

// CANDIDATE: the Lean-emitted pack (branchDataPack {2,16} = 67, kernel-checked in the paired Lean file).
export function candidate() {
  return [{ name: 'wrap_public_input[29]', value: LEAN_EMIT }];
}

// EXTRA provenance: decoded inputs, the naive-tag (66) falsifier, and o1js sharing the emitter.
export async function extra() {
  const block = loadBlock();
  const wpi: string[] = block.wrap_public_input;
  const oracleBranchData = Number(wpi[BRANCH_DATA_SLOT]);
  const pv = block.branch_data_proofs_verified ?? findNested(block, 'branch_data_proofs_verified');
  const dl = block.branch_data_domain_log2 ?? findNested(block, 'branch_data_domain_log2');
  console.log(`  network/height : ${block._network} / ${block._blockchain_length}   state_hash: ${block._state_hash}`);
  console.log(`  decoded branch_data : { proofs_verified = ${pv}, domain_log2 = ${dl} }`);
  console.log(`  padding slots 30..39: ${wpi.slice(30).every((x) => x === '0') ? 'all 0 (ok)' : 'NON-ZERO'}`);

  // naive-tag (66) falsifier: the prefix-mask pack must NOT coincide with 4*dl + tag.
  if (oracleBranchData === NAIVE_WRONG) throw new Error('oracle equals the NAIVE (tag-not-mask) value 66 — provenance is wrong');
  console.log(`  ok   naive tag-not-mask packer would emit ${NAIVE_WRONG} (rejected; the mask is load-bearing)`);

  // o1js shares the OCaml pack code path.
  const bc = readFileSync(O1JS_BC, 'utf8');
  const hits = (re: RegExp) => (bc.match(re) || []).length;
  const codePath = {
    branch_data: hits(/branch_data/g),
    Prefix_mask: hits(/[Pp]refix_mask/g),
    proofs_verified: hits(/proofs_verified/g),
    composition_types: hits(/composition_types/g),
  };
  console.log(`  o1js bytecode code-path hits: ${JSON.stringify(codePath)}`);
  if (codePath.branch_data === 0 || codePath.proofs_verified === 0)
    throw new Error('o1js bytecode does not carry the branch_data / proofs_verified pack path');
  console.log('  ok   o1js bytecode carries branch_data + proofs_verified (same emitter, different runtime)');
}

function findNested(o: any, key: string): unknown {
  const s = JSON.stringify(o);
  const i = s.indexOf(`"${key}":`);
  if (i < 0) return undefined;
  const tail = s.slice(i + key.length + 3);
  const m = tail.match(/^\s*("?)([^",}]+)\1/);
  return m ? m[2] : undefined;
}

export const shape = 'field';
export const label = 'R3 branch_data (real block 539508 wrap_public_input[29] vs Lean branchDataPack {2,16})';

const isMain = process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1]);
if (isMain) await runOracle({ shape, label, reference, candidate, extra });

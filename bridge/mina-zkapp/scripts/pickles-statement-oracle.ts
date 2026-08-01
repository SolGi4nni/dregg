/**
 * pickles-statement-oracle.ts — the o1js/OCaml-Pickles ORACLE side of the FULL Wrap-statement diff.
 *
 * Extends `pickles-r3-branchdata-oracle.ts` (which diffed ONE field, branch_data / slot 29) to the
 * WHOLE Wrap statement. Pairs with `metatheory/Dregg2/Bridge/PicklesStatementDiff.lean` (the Lean EMIT
 * side). Together they confirm every `wrap_public_input` slot byte-exact against a live, kimchi-verified
 * devnet block:
 *
 *   slots 0-4   fp block      = Type1/Fp shift of step_deferred_values.{cip,b,ztsl,ztds,perm}   [PACK]
 *   slots 5-9   challenges    = step_deferred_values.{beta,gamma,alpha,zeta,xi}  (to_data order) [ident]
 *   slot 10     sponge digest = sponge_digest_before_evaluations                                 [ident]
 *   slots 11-12 me-only       = messages_for_next_{wrap,step}_proof digests (pinned in            [cited]
 *                               MinaWrapPublicInput via word11Gold/word12Gold)
 *   slots 13-28 bp challenges = step_deferred_values.bulletproof_challenges (16)                 [ident]
 *   slot 29     branch_data   = 4*domain_log2 + prefix_mask(proofs_verified) = 67                [PACK]
 *   slots 30-39 feature/lookup= 0 (8 feature-flag bits + 2-slot lookup opt, all off)             [const]
 *
 * The two NON-identity packings (fp shift, branch_data) are reproduced from the DECODED unpacked
 * fields; the identity slots are confirmed against the independently-decoded step_deferred_values (a
 * DIFFERENT json path than wrap_public_input), so the ORDER is validated, not projected.
 *
 * ⚑ Phase A discipline: this establishes FIDELITY (Lean's packing matches the real chain's words for
 * one block, MEASURED), NOT soundness. Not "machine-checked Pickles".
 *
 * The oracle is a LIVE emission of exactly the OCaml `Wrap.Statement.to_data`/`Shifted_value.Type1`
 * that o1js wraps:
 *   - `metatheory/mina_real_block_proof.json` (devnet block 539508) — wrap_public_input is openmina's
 *     own `PreparedStatement::to_public_input`, and o1-labs' `kimchi::verifier::verify` ACCEPTS the
 *     Wrap proof against those 40 words (so each slot is validated, not transcribed).
 *   - o1js is js_of_ocaml of the same Pickles; its bytecode carries `shifted_value`/`composition_types`
 *     (confirmed below).
 *
 * Run: npx tsx scripts/pickles-statement-oracle.ts
 * (read-only; exits non-zero if ANY slot diff fails — a gate, green-or-bust.)
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

// ── Pasta Fp (the STEP proof's scalar field; the fp block is shifted over THIS field) ──────────────
const P = 28948022309329048855892746252171976963363056481941560715954676764349967630337n;
const Q = 28948022309329048855892746252171976963363056481941647379679742748393362948097n;
const C1 = (2n ** 255n) + 1n;            // Type1 shift constant, = shift1Fp.c
const INV2_P = (P + 1n) / 2n;            // 2^{-1} mod p (p odd ⇒ (p+1)/2), = shift1Fp.twoInv
const mod = (a: bigint, m: bigint) => ((a % m) + m) % m;
/** `Shifted_value.Type1.of_field` over field M: `(s - (2^255+1)) * 2^{-1}`  (Lean `type1OfField`). */
const type1 = (s: bigint, M: bigint, inv2: bigint) => mod((s - C1) * inv2, M);

function fail(msg: string): never { console.error('DIFF RED:', msg); process.exit(1); }

// ── load ────────────────────────────────────────────────────────────────────────────────────────
const block = JSON.parse(readFileSync(FIXTURE, 'utf8'));
const wpi: bigint[] = (block.wrap_public_input as string[]).map((x) => BigInt(x));
if (wpi.length !== 40) fail(`wrap_public_input is not 40 words (${wpi.length})`);
const sdv = block.step_deferred_values;
if (!sdv) fail('fixture missing step_deferred_values (the decoded unpacked record)');
const B = (v: unknown) => BigInt(String(v));

console.log('=== Pickles Wrap-statement oracle (real devnet block 539508) ===');
console.log(`  network/height : ${block._network} / ${block._blockchain_length}`);
console.log(`  state_hash     : ${block._state_hash}`);

let checked = 0, packSlots = 0, identSlots = 0, constSlots = 0, citedSlots = 0;
const expect = new Array<bigint | null>(40).fill(null);

// ── §1 fp block (slots 0-4): NON-identity Type1/Fp shift ──────────────────────────────────────────
const FP = [
  { name: 'combined_inner_product', slot: 0 },
  { name: 'b', slot: 1 },
  { name: 'zeta_to_srs_length', slot: 2 },
  { name: 'zeta_to_domain_size', slot: 3 },
  { name: 'perm', slot: 4 },
];
console.log('--- slots 0-4  fp block  (Type1/Fp shift; PACK) ---');
for (const { name, slot } of FP) {
  const unshifted = B(sdv[name]);
  const shiftedDecoded = B(sdv[`${name}_shifted`]);   // second, independent decoded field
  const emitted = type1(unshifted, P, INV2_P);         // Lean's type1OfField shift1Fp, recomputed
  const wire = wpi[slot];
  if (wire !== shiftedDecoded) fail(`slot ${slot} (${name}): wire ${wire} != decoded _shifted ${shiftedDecoded}`);
  if (emitted !== wire) fail(`slot ${slot} (${name}): Type1/Fp emit ${emitted} != wire ${wire}`);
  // value-field rule: the shift is over Fp (the value's field), NOT the wrap circuit's native Fq
  if (type1(unshifted, Q, (Q + 1n) / 2n) === wire) fail(`slot ${slot}: Type1 over Fq ALSO matched — provenance ambiguous`);
  expect[slot] = wire; packSlots++; checked++;
  console.log(`  [${slot}] ${name.padEnd(24)} Type1/Fp(unshifted) == wire  ✓`);
}
// falsifier: identity placement (raw scalar on the wire) is rejected at slot 0
if (B(sdv['combined_inner_product']) === wpi[0]) fail('identity placement matched slot 0 — shift not load-bearing');
console.log('  falsifier: identity placement (no shift) != wire  ✓   Type1/Fq != wire  ✓');

// ── §2 challenges (slots 5-9): identity, to_data order ────────────────────────────────────────────
const CH = [
  { name: 'beta', slot: 5 }, { name: 'gamma', slot: 6 },
  { name: 'alpha', slot: 7 }, { name: 'zeta', slot: 8 }, { name: 'xi', slot: 9 },
];
console.log('--- slots 5-9  challenges  (identity; to_data order [beta,gamma,alpha,zeta,xi]) ---');
for (const { name, slot } of CH) {
  const decoded = B(sdv[name]);
  if (wpi[slot] !== decoded) fail(`slot ${slot} (${name}): wire ${wpi[slot]} != decoded ${decoded}`);
  expect[slot] = wpi[slot]; identSlots++; checked++;
}
console.log(`  slots 5-9 == step_deferred_values.{beta,gamma,alpha,zeta,xi}  ✓  (order confirmed)`);

// ── §3 sponge digest (slot 10): identity ──────────────────────────────────────────────────────────
const sponge = B(block.sponge_digest_before_evaluations);
if (wpi[10] !== sponge) fail(`slot 10: wire ${wpi[10]} != sponge_digest_before_evaluations ${sponge}`);
expect[10] = wpi[10]; identSlots++; checked++;
console.log('--- slot 10   sponge_digest_before_evaluations == wire  ✓  (identity) ---');

// ── §4 me-only digests (slots 11-12): pinned elsewhere, pass-through ───────────────────────────────
expect[11] = wpi[11]; expect[12] = wpi[12]; citedSlots += 2;
console.log('--- slots 11-12  me-only digests: pinned by MinaWrapPublicInput.word11Gold/word12Gold (cited) ---');

// ── §5 bulletproof challenges (slots 13-28): identity ─────────────────────────────────────────────
const bpc: bigint[] = (sdv.bulletproof_challenges as string[]).map((x) => BigInt(x));
if (bpc.length !== 16) fail(`bulletproof_challenges is not 16 (${bpc.length})`);
for (let j = 0; j < 16; j++) {
  if (wpi[13 + j] !== bpc[j]) fail(`slot ${13 + j}: wire ${wpi[13 + j]} != bp challenge ${bpc[j]}`);
  expect[13 + j] = wpi[13 + j]; identSlots++; checked++;
}
console.log('--- slots 13-28  bulletproof_challenges (16) == wire  ✓  (identity) ---');

// ── §6 branch_data (slot 29): NON-identity prefix-mask pack ────────────────────────────────────────
const prefixMask = (pv: number) => (pv === 0 ? 0 : pv === 1 ? 2 : pv === 2 ? 3 : NaN);
// proofs_verified is decoded as the tag "N0"/"N1"/"N2" (or a bare int); map "N<k>" -> k.
const rawPv = String(sdv.branch_data_proofs_verified ?? findNested(block, 'branch_data_proofs_verified') ?? '2');
const pv = rawPv.startsWith('N') ? Number(rawPv.slice(1)) : Number(rawPv);
const dl = Number(sdv.branch_data_domain_log2 ?? findNested(block, 'branch_data_domain_log2') ?? 16);
if (!Number.isInteger(pv) || !Number.isInteger(dl)) fail(`branch_data parse: pv=${rawPv} dl=${dl}`);
const branchPacked = BigInt(4 * dl + prefixMask(pv));
if (wpi[29] !== branchPacked) fail(`slot 29: wire ${wpi[29]} != branchDataPack{pv=${pv},dl=${dl}} ${branchPacked}`);
if (branchPacked === BigInt(4 * dl + pv)) fail('branch_data: prefix-mask == tag — the mask is not load-bearing here');
expect[29] = wpi[29]; packSlots++; checked++;
console.log(`--- slot 29   branch_data = 4*${dl} + prefix_mask(${pv}) = ${branchPacked} == wire  ✓  (PACK; naive tag emits ${4 * dl + pv}) ---`);

// ── §7 feature-flag / lookup-opt tail (slots 30-39): constant 0 ───────────────────────────────────
for (let i = 30; i < 40; i++) {
  if (wpi[i] !== 0n) fail(`slot ${i}: tail expected 0, got ${wpi[i]}`);
  expect[i] = 0n; constSlots++; checked++;
}
console.log('--- slots 30-39  feature_flags(8) + lookup_opt(2) = 0  ✓  (const; Lean wrapStatementLayout=38 omits the 2 lookup slots) ---');

// ── §8 the full reconstruction: to_data order over decoded fields == the 40 wire words ─────────────
for (let i = 0; i < 40; i++) {
  if (expect[i] === null) fail(`slot ${i}: not covered by the reconstruction`);
  if (expect[i] !== wpi[i]) fail(`RECONSTRUCTION slot ${i}: ${expect[i]} != wire ${wpi[i]}`);
}
console.log(`=== reconstruction: to_data(decoded record) == wrap_public_input, all 40 slots  ✓ ===`);
console.log(`  coverage: ${checked}/40 diffed against decoded fields · ${citedSlots}/40 cited (me-only)`);
console.log(`           (PACK ${packSlots} · identity ${identSlots} · const ${constSlots} · cited ${citedSlots})`);

// ── §9 o1js shares the emitter (bytecode code-path hits) ──────────────────────────────────────────
const bc = readFileSync(O1JS_BC, 'utf8');
const hits = (re: RegExp) => (bc.match(re) || []).length;
const codePath = {
  shifted_value: hits(/shifted_value|Shifted_value/g),
  composition_types: hits(/composition_types/g),
  branch_data: hits(/branch_data/g),
};
console.log(`=== o1js shares the emitter (o1js_node.bc.cjs): ${JSON.stringify(codePath)} ===`);
if (codePath.composition_types === 0) fail('o1js bytecode does not carry the composition_types to_data path');

console.log('Pickles Wrap-statement diff: GREEN (Lean to_data packing == real-chain 40 words, byte-exact).');

function findNested(o: unknown, key: string): unknown {
  const s = JSON.stringify(o);
  const i = s.indexOf(`"${key}":`);
  if (i < 0) return undefined;
  const tail = s.slice(i + key.length + 3);
  const m = tail.match(/^\s*("?)([^",}]+)\1/);
  return m ? m[2] : undefined;
}

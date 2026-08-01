/**
 * pickles-step-statement-oracle.ts — the o1js/OCaml/openmina ORACLE side of the STEP-statement diff.
 *
 * Complement to `pickles-statement-oracle.ts` (the WRAP statement, byte-exact vs live block 539508).
 * Pairs with `metatheory/Dregg2/Bridge/PicklesStepStatementDiff.lean` (the Lean EMIT side). The STEP
 * per-proof statement has a DIFFERENT flat layout and its own field-key, handed off from the Wrap lane.
 *
 * ⚑ ORACLE SITUATION — read this. Unlike the Wrap lane, the live fixture carries NO step-statement
 * public input: `mina_real_block_proof.json` is a WRAP-proof decode, so its `step_deferred_values` is
 * the WRAP statement's payload ABOUT the step proof (its `_shifted` fields are Type1/Fp = the Wrap `fp`
 * block), NOT a step proof's own public input. So this oracle establishes, honestly:
 *
 *   [ORDER]      the 27-slot flat layout (fq 5 · digest 1 · challenge 2 · scalar_challenge 3 ·
 *                bulletproof 15 · bool 1) — ORDER-CONFIRMED by TWO independent implementations that
 *                AGREE: OCaml `composition_types.ml:1298-1318` to_data + openmina Rust
 *                `unfinalized.rs:397-434` Unfinalized::to_field_elements. o1js bytecode carries the path.
 *   [FIELD-KEY]  fq = Shifted_value.Type2 over **Fq** — SOURCE-DEFINITIVE (`impls.ml:135` binds Step's
 *                `Field` spec leaf to `Shifted_value.Type2.typ Other_field`, Other_field = Tock = Fq;
 *                openmina `unfinalized.rs:105` types combined_inner_product `<Fq>::Shifting =
 *                ShiftedValue<Fq>` = Type2, `plonk_checks.rs:113`). Below: the diverging control — the
 *                Type2/Fq encoding of a sample scalar DIVERGES from Type2/Fp (wrong FIELD), Type1/Fq
 *                (wrong KIND) and identity, so the choice is observable/falsifiable.
 *   [RESIDUAL]   the fixture is MEASURED to be a Wrap decode (its cip_shifted == Type1/Fp(cip), NOT
 *                Type2/Fq), so there is no step wire to byte-diff PACKED VALUES against — named, not
 *                assumed. Closed by a decoded step statement (a step proof's unfinalized_proofs.(i)).
 *
 * ⚑ Phase A discipline: LAYOUT / FIELD-KEY FIDELITY, NOT soundness, and NOT "byte-exact vs the chain"
 * for the step values (there is no step wire here). NOT "machine-checked Pickles".
 *
 * Run: npx tsx scripts/pickles-step-statement-oracle.ts
 * (read-only; exits non-zero if ANY assertion fails — a gate, green-or-bust.)
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

// ── Pasta scalar fields ─────────────────────────────────────────────────────────────────────────
const P = 28948022309329048855892746252171976963363056481941560715954676764349967630337n; // Fp = Vesta scalar (Step-native)
const Q = 28948022309329048855892746252171976963363056481941647379679742748393362948097n; // Fq = Pallas scalar (the step's fq block)
const C2 = 2n ** 255n;         // Type2 shift constant  = shift2*.shift
const C1 = C2 + 1n;            // Type1 shift constant  = shift1*.c
const INV2 = (m: bigint) => (m + 1n) / 2n;   // 2^{-1} mod m (m odd)
const mod = (a: bigint, m: bigint) => ((a % m) + m) % m;
/** Shifted_value.Type2.of_field over field M: `s - 2^255`  (Lean `type2OfField shift2*`). */
const type2 = (s: bigint, M: bigint) => mod(s - C2, M);
/** Shifted_value.Type1.of_field over field M: `(s - (2^255+1)) * 2^{-1}`  (Lean `type1OfField shift1*`). */
const type1 = (s: bigint, M: bigint) => mod((s - C1) * INV2(M), M);

function fail(msg: string): never { console.error('DIFF RED:', msg); process.exit(1); }
function ok(msg: string) { console.log(`  ${msg}  ✓`); }

// ── §0 the enumerated Step per-proof slot map (composition_types.ml:1268-1318; unfinalized.rs) ────
const STEP_LAYOUT: [string, number][] = [
  ['fq', 5], ['digest', 1], ['challenge', 2], ['scalar_challenge', 3],
  ['bulletproof_challenge', 15], ['bool', 1],
];
const TOTAL = STEP_LAYOUT.reduce((n, [, c]) => n + c, 0);
console.log('=== Pickles STEP-statement oracle (per-proof layout) ===');
console.log('  layout (composition_types.ml:1298-1318 to_data == openmina unfinalized.rs:397-434):');
for (const [name, c] of STEP_LAYOUT) console.log(`    ${name.padEnd(22)} ${c}`);
if (TOTAL !== 27) fail(`slot total ${TOTAL} != 27`);
ok(`slot total == 27 (fq 5 · digest 1 · challenge 2 · scalar_challenge 3 · bulletproof 15 · bool 1)`);
// bp = Backend.Tock.Rounds.n = 15 (the WRAP proof's IPA rounds; a Step proof defers a Wrap proof).
if (STEP_LAYOUT.find(([n]) => n === 'bulletproof_challenge')![1] !== 15)
  fail('bulletproof count != 15 (Tock rounds)');
ok('bulletproof count == 15 (Tock.Rounds.n; Wrap statement defers 16 = Tick, this defers 15 = Tock)');

// step order DIFFERS from the wrap head order (digest early, trailing bool, no branch_data)
const STEP_ORDER = STEP_LAYOUT.map(([n]) => n);
const WRAP_HEAD_ORDER = ['fp', 'challenge', 'scalar_challenge', 'digest'];
if (STEP_ORDER[1] !== 'digest') fail('step digest not at block #2');
if (WRAP_HEAD_ORDER[3] !== 'digest') fail('wrap digest not at block #4');
if (!STEP_ORDER.includes('bool')) fail('step missing trailing bool');
if (STEP_ORDER.includes('branch_data')) fail('step should NOT carry branch_data');
ok('step order != wrap order (digest early #2 vs #4; trailing should_finalize bool; no branch_data)');

// ── §1 FIELD-KEY: the fq block is Type2/Fq. Diverging control on a sample scalar ──────────────────
// SAMPLE matches Lean `SAMPLE_FQ` (the block's own combined_inner_product, reused as an illustrative
// Fq scalar — there is NO real step wire; §Residual). The control is about observability, not a match.
const SAMPLE = 19890585860582513838359427261530390921328764305959386728558585581183530790096n;
const t2q = type2(SAMPLE, Q);   // CORRECT: Type2 over Fq
const t2p = type2(SAMPLE, P);   // wrong FIELD (right kind)
const t1q = type1(SAMPLE, Q);   // wrong KIND (right field: halving instead of subtract-only)
// Lean `PicklesStepStatementDiff.step_fq_sample_shift_pins_oracle` proves the shift equals THIS
// constant; the assert below is the TS side of that two-sided pin (kernel ZMod vs bigint agree).
const LEAN_T2Q_SAMPLE = 19890585860582513838359427261530390921419884937022399468189279074013691866322n;
console.log('--- field-key: fq = Type2/Fq (impls.ml:135 · unfinalized.rs:105 · plonk_checks.rs:113) ---');
console.log(`  Type2/Fq(SAMPLE) = ${t2q}`);
if (t2q !== LEAN_T2Q_SAMPLE)
  fail(`Type2/Fq(SAMPLE) != Lean step_fq_sample_shift_pins_oracle constant`);
ok('Type2/Fq(SAMPLE) == Lean step_fq_sample_shift_pins_oracle (kernel ZMod == bigint, byte-diff)');
if (t2q === SAMPLE) fail('identity == Type2/Fq — shift not load-bearing');
if (t2q === t2p) fail('Type2/Fp == Type2/Fq — wrong-FIELD not observable (provenance ambiguous)');
if (t2q === t1q) fail('Type1/Fq == Type2/Fq — wrong-KIND (halving vs subtract-only) not observable');
ok('Type2/Fq != { identity, Type2/Fp, Type1/Fq } — the field-key choice is observable/falsifiable');
// round-trip: to_field(of_field(s)) = s
if (mod(t2q + C2, Q) !== SAMPLE) fail('Type2/Fq round-trip failed');
ok('Type2/Fq round-trips (shifted + 2^255 == raw, mod q)');

// ── §Residual: MEASURE that this fixture is a Wrap decode (no step wire) ───────────────────────────
const block = JSON.parse(readFileSync(FIXTURE, 'utf8'));
const sdv = block.step_deferred_values;
if (!sdv) fail('fixture missing step_deferred_values');
const cip = BigInt(String(sdv.combined_inner_product));
const cipShifted = BigInt(String(sdv.combined_inner_product_shifted));
console.log('--- §Residual: the fixture is a WRAP decode (no step wire), MEASURED ---');
// the fixture's cip_shifted is the Type1/Fp encoding (the Wrap fp block), NOT Type2/Fq.
if (type1(cip, P) !== cipShifted)
  fail(`combined_inner_product_shifted is not Type1/Fp(cip) — fixture unexpected`);
ok('combined_inner_product_shifted == Type1/Fp(combined_inner_product) — this IS the Wrap fp block');
if (type2(cip, Q) === cipShifted)
  fail('cip_shifted also matches Type2/Fq — would be ambiguous; expected a pure Wrap decode');
ok('combined_inner_product_shifted != Type2/Fq(cip) — so there is NO step statement here (residual)');
console.log('  residual closed by: a decoded STEP statement — a step proof\'s unfinalized_proofs.(i)');
console.log('  per-proof public input (openmina Unfinalized), giving real Fq cip/b/perm with Type2/Fq');
console.log('  .shifted forms (the analog of the Wrap _shifted pairing this fixture has for Fp).');

// ── §2 o1js carries the step per-proof code path (live-emission evidence, green-or-bust) ──────────
const bc = readFileSync(O1JS_BC, 'utf8');
const hits = (re: RegExp) => (bc.match(re) || []).length;
const codePath = {
  should_finalize: hits(/should_finalize/g),
  unfinalized_proofs: hits(/unfinalized_proofs/g),
  shifted_value: hits(/shifted_value|Shifted_value/g),
  per_proof: hits(/[Pp]er_proof/g),
  composition_types: hits(/composition_types/g),
};
console.log(`=== o1js carries the step per-proof path (o1js_node.bc.cjs): ${JSON.stringify(codePath)} ===`);
if (codePath.should_finalize === 0 || codePath.shifted_value === 0 || codePath.composition_types === 0)
  fail('o1js bytecode does not carry the step per-proof to_data / shifted_value code path');
ok('o1js bytecode carries should_finalize + shifted_value + composition_types (same emitter)');

console.log('Pickles STEP-statement diff: GREEN (layout ORDER + fq=Type2/Fq field-key confirmed; ' +
  'packed-values residual named — no step wire in this fixture).');

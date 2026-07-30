import { Bool, Field, Poseidon, Provable } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { resolve } from 'node:path';
import {
  LANES_PER_PERM,
  LIMBS_PER_SLOT,
  P_BB,
  P_PASTA,
  PastaDigest,
  compressPasta,
  compressPastaBigInt,
  condSwapPasta,
  foldOpeningPasta,
  foldPathPastaBigInt,
  packSlot,
  packSlotBigInt,
  spongePasta,
  spongePastaBigInt,
} from '../src/PastaMmcs.js';
import {
  PASTA_MINUS_ONE_DIGITS,
  P_POW,
  SPLIT_REM_BITS,
  SQUEEZE_NUM_F_ELMS,
  reducePackedBigInt,
  pinSplitHint,
  splitPastaBigInt,
  splitToFieldOrderLimbs,
} from '../src/PastaChallenger.js';

// ---------------------------------------------------------------------------
// THE DIFFERENTIAL, AND IT RUNS BEFORE ANY CIRCUIT IS COMPILED.
//
// ⚑ WHY THIS SCRIPT EXISTS AT ALL, AND IT IS NOT DILIGENCE. Every previous rung
// of this arc paid for the same lesson: a cheap EXHAUSTIVE out-of-circuit
// differential against the real Rust objects found four defects that would each
// have compiled, proved and verified cleanly — a full output buffer on entry,
// `sample_bits` taking the wrong bits, `alpha_pow` starting at one, an undefined
// path direction. None of them is visible in a row count and none of them makes
// a circuit fail to build. And partial agreement is NOT agreement: one mapping
// in this arc matched 216 of 512 cases by coincidence.
//
// So: every shape, not a sample of shapes. Row widths 1..48 covers every
// partial-slot and partial-block position the sponge has, three times over.
//
// THE REFERENT IS THE DEPLOYED RUST, not a transcription of it:
// `dregg-p3-pasta`'s `pasta-mmcs-emit` calls the REAL
// `MultiField32PaddingFreeSponge<BabyBear, PastaFp, MinaPoseidonPerm, 3, 2, 1>`
// and the REAL `TruncatedPermutation<MinaPoseidonPerm, 2, 1, 3>` — the same
// types `dregg_mina_config::MinaHash` / `MinaCompress` alias.
//
//   npm run pasta-differential
// ---------------------------------------------------------------------------

let failures = 0;
function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  failures++;
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
function check(cond: boolean, msg: string) {
  if (cond) ok(msg);
  else fail(msg);
}

const REPO = resolve(process.cwd(), '../..');

function emit(args: string[]): any {
  const out = execFileSync(
    'cargo',
    ['run', '--release', '--quiet', '--offline', '-p', 'dregg-p3-pasta', '--bin', 'pasta-mmcs-emit', '--', ...args],
    { cwd: REPO, encoding: 'utf8', maxBuffer: 1 << 26 },
  );
  return JSON.parse(out);
}

const hexToBig = (s: string) => BigInt(s);

/** Lanes the Rust side cannot have precomputed: this tree's HEAD, a millisecond
 *  timestamp and 128 fresh bits, folded into BabyBear. A differential against a
 *  constant the emitter also produced is not a differential. */
function freshLanes(n: number): bigint[] {
  const head = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: REPO, encoding: 'utf8' }).trim();
  let acc = BigInt('0x' + head.slice(0, 32));
  acc = (acc * 65537n + BigInt(Date.now())) % P_BB;
  acc = (acc * 65537n + BigInt('0x' + randomBytes(16).toString('hex'))) % P_BB;
  const out: bigint[] = [];
  for (let i = 0; i < n; i++) {
    acc = (acc * 1000003n + BigInt(i) + 7n) % P_BB;
    out.push(acc);
  }
  return out;
}

/** The wrapped decomposition — built in [4], required to be REFUSED in [5]. */
let FORBIDDEN_HINT: bigint[] = [];

console.log('=== THE PASTA HASH DIFFERENTIAL — o1js vs the REAL p3 objects ===\n');

// ---------------------------------------------------------------------------
console.log('[1] the MMCS leaf sponge, EVERY row width 1..48');
// Widths 1..48 are three full 16-lane blocks with every partial position in
// between — the two boundaries that matter are a partial SLOT (row length not a
// multiple of 8, so the Horner is short) and a partial BLOCK (one rate slot
// written, the other KEEPING its previous value rather than being zeroed).
{
  const WIDTHS = Array.from({ length: 48 }, (_, i) => i + 1);
  const N_ROWS = 2;
  let mismatched = 0;
  let slotChecks = 0;
  for (const w of WIDTHS) {
    const lanes = freshLanes(w * N_ROWS);
    const em = emit(['leaf', String(w), String(N_ROWS), ...lanes.map(String)]);
    if (em.limbsPerSlot !== LIMBS_PER_SLOT || em.radixBits !== 31 || em.lanesPerPermutation !== LANES_PER_PERM)
      fail('the p3 packing constants moved — this script describes the wrong sponge');
    for (let r = 0; r < N_ROWS; r++) {
      const row = lanes.slice(r * w, (r + 1) * w);
      // the packed rate slots, on their own — so a Horner bug is not hidden
      // behind a permutation
      for (let c = 0, k = 0; c < w; c += LIMBS_PER_SLOT, k++) {
        const mine = packSlotBigInt(row.slice(c, c + LIMBS_PER_SLOT));
        if (mine !== hexToBig(em.packedSlots[r][k])) mismatched++;
        slotChecks++;
      }
      if (spongePastaBigInt(row) !== hexToBig(em.leafDigests[r])) mismatched++;
    }
  }
  check(mismatched === 0, `${WIDTHS.length} widths x ${N_ROWS} rows: ${slotChecks} packed slots and ${WIDTHS.length * N_ROWS} leaf digests all agree with p3`);
}

// ---------------------------------------------------------------------------
console.log('\n[2] the packing is INJECTIVE where p3 says it is, and the +1 shift is what does it');
{
  // `reduce_packed_shifted` reserves 0 as "no digit", so a SHORTER row and a
  // longer row that agrees on its prefix do NOT collide. That is the property
  // the whole leaf hash rests on and it is one line away from being lost:
  // `reduce_packed` (no shift) is what the CHALLENGER uses, and the two live ten
  // lines apart.
  const a = packSlotBigInt([1n, 2n]);
  const b = packSlotBigInt([1n, 2n, 0n]);
  check(a !== b, `shifted pack: [1,2] and [1,2,0] are DISTINCT (${a % 1000000n}... vs ${b % 1000000n}...)`);
  const ua = reducePackedBigInt([1n, 2n]);
  const ub = reducePackedBigInt([1n, 2n, 0n]);
  check(ua === ub, 'unshifted pack: [1,2] and [1,2,0] COLLIDE — which is why the challenger pairs it with a LENGTH TAG');
  check(packSlotBigInt([0n]) !== reducePackedBigInt([0n]), 'the two packs are genuinely different functions');
}

// ---------------------------------------------------------------------------
console.log('\n[3] the Merkle compression and a full path, against p3');
{
  const DEPTH = 12;
  const N_LEAVES = 1 << 5;
  const leaves = freshLanes(N_LEAVES).map((v) => (v * 7919n) % P_PASTA);
  let bad = 0;
  for (const idx of [0, 1, 2, 7, N_LEAVES - 1]) {
    const em = emit(['path', String(DEPTH), String(idx), ...leaves.map((v) => '0x' + v.toString(16).padStart(64, '0'))]);
    const sibs = em.siblings.map(hexToBig);
    const nodes = foldPathPastaBigInt(leaves[idx], sibs, em.isRight);
    for (let h = 0; h < DEPTH; h++) if (nodes[h] !== hexToBig(em.nodes[h])) bad++;
    if (nodes[DEPTH - 1] !== hexToBig(em.root)) bad++;
  }
  check(bad === 0, `5 leaf indices x depth ${DEPTH}: every node and every root agrees with p3's TruncatedPermutation`);
  // and the compression is ORDER-SENSITIVE, or a prover swaps siblings freely
  check(
    compressPastaBigInt(3n, 5n) !== compressPastaBigInt(5n, 3n),
    'compress(l,r) != compress(r,l) — sibling order is bound',
  );
}

// ---------------------------------------------------------------------------
console.log('\n[4] the base-|F| SPLIT, out of circuit — the challenger squeeze');
{
  // `split_pf_to_field_order_limbs(v, 7)` is a pure integer decomposition, so it
  // can be checked EXHAUSTIVELY in the only sense available: the recomposition
  // is an identity over the integers for every value tried, including the two
  // that matter (0 and p_Pasta - 1, the lexicographic bound's own witness).
  const vals: bigint[] = [0n, 1n, P_PASTA - 1n, P_PASTA - 2n, P_BB, P_BB - 1n, P_POW[7], P_POW[7] - 1n];
  for (let i = 0; i < 64; i++) vals.push(BigInt('0x' + randomBytes(32).toString('hex')) % P_PASTA);
  let bad = 0;
  for (const v of vals) {
    const { limbs, rem } = splitPastaBigInt(v);
    if (limbs.length !== SQUEEZE_NUM_F_ELMS) bad++;
    if (limbs.some((l) => l >= P_BB)) bad++;
    if (rem >= 1n << BigInt(SPLIT_REM_BITS)) bad++;
    let acc = rem * P_POW[SQUEEZE_NUM_F_ELMS];
    for (let i = 0; i < SQUEEZE_NUM_F_ELMS; i++) acc += limbs[i] * P_POW[i];
    if (acc !== v) bad++;
  }
  check(bad === 0, `${vals.length} values: 7 canonical limbs + a 38-bit remainder, recomposing EXACTLY over the integers`);

  // The lexicographic bound is the part that is not obviously needed, so its
  // witness is checked directly: the digits of p_Pasta - 1 are exactly what the
  // split of p_Pasta - 1 produces, i.e. the bound is TIGHT and admits the
  // largest honest value rather than being a loose over-approximation.
  const top = splitPastaBigInt(P_PASTA - 1n);
  check(
    top.limbs.every((l, i) => l === PASTA_MINUS_ONE_DIGITS[i]) &&
      top.rem === PASTA_MINUS_ONE_DIGITS[SQUEEZE_NUM_F_ELMS],
    'the lex bound IS the split of p_Pasta - 1 — exact, no completeness gap',
  );
  // ...and the wrap it forbids is REAL: v + p_Pasta has a decomposition with
  // limbs still canonical, which satisfies (a)(b)(c) and is a DIFFERENT set of
  // challenges.
  {
    // ⚑ THE WRAP MUST BE BUILT OVER THE INTEGERS. `splitPastaBigInt` reduces its
    // argument mod p_Pasta first — it is the HONEST prover's routine — so asking
    // it for the decomposition of `v + p_Pasta` gives back the decomposition of
    // `v`. The attack is a decomposition p3 would never produce, so it has to be
    // constructed here.
    const v = 12345n;
    const wrapped = v + P_PASTA;
    let rest = wrapped;
    const wl: bigint[] = [];
    for (let i = 0; i < SQUEEZE_NUM_F_ELMS; i++) {
      wl.push(rest % P_BB);
      rest /= P_BB;
    }
    const wrem = rest;
    const honest = splitPastaBigInt(v);
    const differs = wl.some((l, i) => l !== honest.limbs[i]);
    const canonical = wl.every((l) => l < P_BB);
    const remInRange = wrem < 1n << BigInt(SPLIT_REM_BITS);
    let acc = wrem * P_POW[SQUEEZE_NUM_F_ELMS];
    for (let i = 0; i < SQUEEZE_NUM_F_ELMS; i++) acc += wl[i] * P_POW[i];
    const satisfiesLinear = acc % P_PASTA === v;
    check(
      differs && canonical && remInRange && satisfiesLinear,
      'the FORBIDDEN decomposition exists: 7 canonical limbs, a 38-bit remainder, the linear relation SATISFIED, and DIFFERENT challenges — so (a)(b)(c) alone let a prover pick its own query indices',
    );
    // (d) is what catches it, and the reason is that the digit tuple is ordered
    // exactly like the integer: `wrapped > p_Pasta - 1`, so `(rem, c6..c0)` is
    // lexicographically greater than the digits of `p_Pasta - 1`.
    const lexGreater = (() => {
      const a = [wrem, ...wl.slice().reverse()];
      const b = [PASTA_MINUS_ONE_DIGITS[SQUEEZE_NUM_F_ELMS], ...PASTA_MINUS_ONE_DIGITS.slice(0, SQUEEZE_NUM_F_ELMS).reverse()];
      for (let i = 0; i < a.length; i++) {
        if (a[i] > b[i]) return true;
        if (a[i] < b[i]) return false;
      }
      return false;
    })();
    check(lexGreater, 'and (d) catches it: its digit tuple is lexicographically ABOVE the digits of p_Pasta - 1');
    FORBIDDEN_HINT = [...wl, wrem];
  }
}



// ---------------------------------------------------------------------------
console.log('\n[5] IN CIRCUIT vs the twins — and the refusals');
async function inCircuit() {
  // -- the leaf sponge, at the widths that exercise both boundaries
  for (const w of [1, 7, 8, 9, 15, 16, 17, 31, 32, 33]) {
    const row = freshLanes(w);
    const want = spongePastaBigInt(row);
    let got = 0n;
    await Provable.runAndCheck(() => {
      const r = Provable.witness(Provable.Array(Field, w), () => row.map((v) => Field(v)));
      const d = spongePasta(r);
      Provable.asProver(() => {
        got = d.limbs[0].toBigInt();
      });
    });
    if (got !== want) fail(`in-circuit leaf sponge disagrees with its twin at width ${w}`);
  }
  ok('the CIRCUIT leaf sponge == the twin == p3, at widths 1,7,8,9,15,16,17,31,32,33');

  // -- REFUSAL: a lane >= 2^31 must be refused, or the injectivity bound is
  //    about nothing.
  let held = false;
  try {
    await Provable.runAndCheck(() => {
      const r = Provable.witness(Provable.Array(Field, 3), () => [Field(1n << 31n), Field(0), Field(0)]);
      spongePasta(r);
    });
    held = true;
  } catch {
    /* expected */
  }
  check(!held, 'the circuit REFUSES a lane >= 2^31 (the packing bound is enforced, not decorative)');

  // -- the Merkle fold, in circuit, against the twin
  {
    const DEPTH = 8;
    const leaf = (freshLanes(1)[0] * 7919n) % P_PASTA;
    const sibs = freshLanes(DEPTH).map((v) => (v * 104729n) % P_PASTA);
    const dirs = sibs.map((_, i) => i % 3 === 0);
    const want = foldPathPastaBigInt(leaf, sibs, dirs)[DEPTH - 1];
    let got = 0n;
    await Provable.runAndCheck(() => {
      const l = PastaDigest.from([Provable.witness(Field, () => Field(leaf))]);
      const ss = Provable.witness(Provable.Array(Field, DEPTH), () =>
        sibs.map((v) => Field(v)),
      ).map((f) => PastaDigest.from([f]));
      const bs = Provable.witness(Provable.Array(Bool, DEPTH), () => dirs.map((d) => Bool(d)));
      const root = foldOpeningPasta(l, ss, bs);
      Provable.asProver(() => {
        got = root.limbs[0].toBigInt();
      });
    });
    check(got === want, `the CIRCUIT depth-${DEPTH} fold == the twin == p3`);

    // and the DIRECTION bit is real: flipping one must move the root. (An
    // undefined path direction is one of the four defects this discipline caught
    // in an earlier rung, and it compiled and proved cleanly.)
    const flipped = dirs.slice();
    flipped[3] = !flipped[3];
    check(
      foldPathPastaBigInt(leaf, sibs, flipped)[DEPTH - 1] !== want,
      'flipping ONE path direction moves the root — the direction bits are not decorative',
    );
  }

  // -- the base-|F| split, in circuit, against the twin, plus its refusal
  {
    let bad = 0;
    for (let i = 0; i < 8; i++) {
      const v = BigInt('0x' + randomBytes(32).toString('hex')) % P_PASTA;
      const want = splitPastaBigInt(v).limbs;
      const got: bigint[] = [];
      await Provable.runAndCheck(() => {
        const f = Provable.witness(Field, () => Field(v));
        const limbs = splitToFieldOrderLimbs(f);
        Provable.asProver(() => {
          for (const l of limbs) got.push(l.toBigInt());
        });
      });
      if (want.some((w, j) => w !== got[j])) bad++;
    }
    check(bad === 0, 'the CIRCUIT split == `split_pf_to_field_order_limbs(v, 7)`, 8 random Pasta cells');

    // ⚑ AND THE CIRCUIT IS WATCHED REFUSING IT. `pinSplitHint` takes the hint as
    // an argument precisely so this can be run: the wrapped decomposition built
    // above satisfies (a), (b) and (c), so if (d) were absent or wrong this
    // would be ACCEPTED and a prover would choose its own FRI query indices out
    // of a perfectly honest sponge. A documented soundness argument that nothing
    // can be seen enforcing is not a detected one.
    let held = false;
    try {
      await Provable.runAndCheck(() => {
        const f = Provable.witness(Field, () => Field(12345n));
        const hint = Provable.witness(Provable.Array(Field, SQUEEZE_NUM_F_ELMS + 1), () =>
          FORBIDDEN_HINT.map((x) => Field(x)),
        );
        pinSplitHint(f, hint);
      });
      held = true;
    } catch {
      /* expected */
    }
    check(!held, 'the circuit REFUSES the wrapped decomposition — (d) is ENFORCED, not documented');

    // ...and it ACCEPTS the honest one for the same value, so the refusal is
    // about the wrap and not about the shape.
    const honestHint = (() => {
      const { limbs, rem } = splitPastaBigInt(12345n);
      return [...limbs, rem];
    })();
    await Provable.runAndCheck(() => {
      const f = Provable.witness(Field, () => Field(12345n));
      const hint = Provable.witness(Provable.Array(Field, SQUEEZE_NUM_F_ELMS + 1), () =>
        honestHint.map((x) => Field(x)),
      );
      pinSplitHint(f, hint);
    });
    ok('and ACCEPTS the honest decomposition of the SAME value — the refusal is the wrap, not the shape');
  }
}

// ---------------------------------------------------------------------------
inCircuit()
  .then(() => {
    if (failures > 0) {
      console.error(`\n${failures} DIFFERENTIAL FAILURES\n`);
      process.exit(1);
    }
    console.log('\n=== the o1js Pasta hash agrees with p3 on every shape tried ===\n');
  })
  .catch((e) => {
    console.error('\nDIFFERENTIAL FAILED:', e?.message ?? e, '\n');
    process.exit(1);
  });

// Keep `Poseidon` and `condSwapPasta` referenced so a refactor that drops the
// import is a build error rather than a silently narrower differential.
void Poseidon;
void condSwapPasta;
void compressPasta;
void packSlot;

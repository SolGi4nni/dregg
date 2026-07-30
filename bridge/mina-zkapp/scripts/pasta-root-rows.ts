import { Bool, Field, Poseidon, Provable } from 'o1js';
import {
  PastaDigest,
  compressPasta,
  condSwapPasta,
  spongePasta,
} from '../src/PastaMmcs.js';
import { PastaChallenger } from '../src/PastaChallenger.js';
import { BbExt } from '../src/FriQueryStep.js';
import { PICKLES } from '../src/CostModel.js';

// ---------------------------------------------------------------------------
// THE MINA-SIDE ROW COUNT, MEASURED AT THE ROOT'S REAL GEOMETRY.
//
// ⚑ WHAT THIS REPLACES. `mina-poseidon-merkle-rows.ts` measured three Pasta UNIT
// prices and then SCALED `MINA-VERIFIES-DREGG-FRI-SIZE` §3's deployed
// decomposition by them, landing on 2.85 x 10^6 rows = 53 slices. That is a
// model with measured inputs, and it says so. This script does not scale
// anything: it BUILDS the root's hash work — every Merkle level, every leaf
// lane, every transcript absorb and every squeeze, at the counts §2.2/§2.3
// derive from the vendored verifier — and asks o1js how many rows it is.
//
// ⚑ THE GEOMETRY, and where each number comes from (§2.2, structurally
// re-derived from `vendor/plonky3-fri-82cfad73/src/verifier.rs`):
//
//   INPUT phase, per query — FOUR rounds, all at depth 22:
//     main          940 lanes   quotient  56 lanes
//     preprocessed  175 lanes   permutation 28 lanes
//   COMMIT phase, per query — 16 rounds at tree depths 21..6 (216 levels),
//     each leaf an arity-2 extension row = 8 base lanes.
//
//   ⚑ AND THIS IS WHERE THE PROJECTION WAS THIN. The 53-slice model's Merkle
//   cross-check used `22 + 216 = 238` levels a query — ONE input round. The
//   structural census has FOUR, i.e. `4*22 + 216 = 304`, 27.7% more. It barely
//   moves the answer, and the reason it barely moves it is the point of the
//   whole exercise: after the hash swap the Merkle term is a rounding error.
//
// ⚑ WHAT IS STILL MODELLED AND IS SAID SO. The DEEP quotient and the AIR
// evaluation at zeta are BabyBear extension arithmetic — no hash choice touches
// them — and their measured values (§3) are carried across unchanged. They are
// now the whole budget, which is the headline.
//
//   npm run pasta-root-rows
// ---------------------------------------------------------------------------

const fmt = (n: number) => Math.round(n).toLocaleString('en-US');

async function rows(f: () => void): Promise<number> {
  const cs = await Provable.constraintSystem(f);
  return cs.rows;
}
const wit = <T>(t: any, f: () => T): T => Provable.witness(t, f) as T;
const witField = (v: bigint) => wit(Field, () => Field(v));
const witDigest = (v: bigint) => PastaDigest.from([witField(v)]);
const witLanes = (n: number, seed = 3n) =>
  Array.from({ length: n }, (_, i) => witField((seed * BigInt(i + 1) * 1000003n) % 2013265921n));

// -- the root's geometry, §2.2 ---------------------------------------------
const NUM_QUERIES = 19;
const INPUT_DEPTH = 22;
const COMMIT_LAYERS = 16;
const COMMIT_DEPTHS = Array.from({ length: COMMIT_LAYERS }, (_, i) => 21 - i); // 21..6
const INPUT_ROUNDS = [
  { name: 'main', lanes: 940 },
  { name: 'quotient', lanes: 56 },
  { name: 'preprocessed', lanes: 175 },
  { name: 'permutation', lanes: 28 },
];
const COMMIT_LEAF_LANES = 8; // arity-2 extension row = 8 base elements

const levelsPerQuery =
  INPUT_ROUNDS.length * INPUT_DEPTH + COMMIT_DEPTHS.reduce((a, b) => a + b, 0);
const lanesPerQuery =
  INPUT_ROUNDS.reduce((a, r) => a + r.lanes, 0) + COMMIT_LAYERS * COMMIT_LEAF_LANES;

// -- the root's transcript schedule, §2.3 ----------------------------------
// Absorb sites, with the DIGEST absorbs pulled out: under `DreggMinaConfig` a
// commitment is ONE native Pasta word absorbed natively (one permutation, no
// repack), where the deployed challenger absorbed 8 BabyBear lanes.
const TRANSCRIPT = {
  babyBearObserves:
    28 + //     instance bindings
    25 + //     public values (33 in §2.3, less the 8 digest lanes)
    7 + //      preprocessed round (15 less 8)
    28 + //     permutation round (36 less 8)
    0 + //      quotient round (8, all digest)
    4 + //      the final polynomial
    16 + //     the 16 arity tags
    9368, //    ⚑ THE DOMINANT TERM: every opened value at zeta, ~2,342
  //            extension values = 9,368 base elements
  digestObserves: INPUT_ROUNDS.length + COMMIT_LAYERS, //  4 input + 16 commit-phase roots
  // alpha, zeta, fri alpha, 16 betas: 19 extension challenges = 76 samples;
  // plus 19 query indices, each one sample + a 22-bit split.
  extSamples: 19,
  indexSamples: NUM_QUERIES,
  indexBits: 22,
};

console.log('=== THE MINA-SIDE ROW COUNT, MEASURED AT THE ROOT GEOMETRY ===\n');
console.log(
  `geometry: ${NUM_QUERIES} queries, ${INPUT_ROUNDS.length} input rounds at depth ${INPUT_DEPTH}, ` +
    `${COMMIT_LAYERS} commit layers at depths 21..6`,
);
console.log(
  `          ${levelsPerQuery} Merkle levels/query, ${fmt(lanesPerQuery)} leaf lanes/query\n`,
);

async function main() {
  // -------------------------------------------------------------------------
  console.log('[1] UNIT PRICES, re-measured here so this script stands alone');

  const perm1 = await rows(() => {
    const a = witField(11n);
    const b = witField(22n);
    Poseidon.hash([a, b]).seal();
  });
  const perm8 = await rows(() => {
    let x = witField(11n);
    const b = witField(22n);
    for (let i = 0; i < 8; i++) x = Poseidon.hash([x, b]);
    x.seal();
  });
  const permMarginal = (perm8 - perm1) / 7;
  console.log(`    one native Poseidon permutation   ${permMarginal.toFixed(2)} rows  (vs 2,600.5 emulated BabyBear)`);

  const lvl = async (n: number) =>
    rows(() => {
      let cur = witDigest(7n);
      for (let h = 0; h < n; h++) {
        const sib = witDigest(BigInt(h + 13));
        const bit = wit(Bool, () => Bool(h % 2 === 0));
        const [l, r] = condSwapPasta(cur, sib, bit);
        cur = compressPasta(l, r);
      }
      cur.limbs[0].seal();
    });
  const l1 = await lvl(1);
  const l17 = await lvl(17);
  const levelMarginal = (l17 - l1) / 16;
  console.log(`    one Merkle level (swap + hash)    ${levelMarginal.toFixed(2)} rows  (vs 2,677)`);

  const spg = async (w: number) => rows(() => spongePasta(witLanes(w)).limbs[0].seal());
  const s16 = await spg(16);
  const s48 = await spg(48);
  const laneMarginal = (s48 - s16) / 32;
  console.log(`    one leaf-sponge BabyBear lane     ${laneMarginal.toFixed(2)} rows  (vs 329)`);

  const obs = async (n: number) =>
    rows(() => {
      const c = new PastaChallenger();
      c.observeSlice(witLanes(n));
      c.sample().seal();
    });
  const o16 = await obs(16);
  const o80 = await obs(80);
  const observeMarginal = (o80 - o16) / 64;
  console.log(`    one challenger BabyBear observe   ${observeMarginal.toFixed(2)} rows`);

  const smp = async (n: number) =>
    rows(() => {
      const c = new PastaChallenger();
      c.observeSlice(witLanes(16));
      for (let i = 0; i < n; i++) c.sample().seal();
    });
  const q1 = await smp(1);
  const q29 = await smp(29);
  const sampleMarginal = (q29 - q1) / 28;
  console.log(`    one challenger sample             ${sampleMarginal.toFixed(2)} rows  (the base-|F| SPLIT amortised over 7 limbs a cell)`);

  const dgo = async (n: number) =>
    rows(() => {
      const c = new PastaChallenger();
      for (let i = 0; i < n; i++) c.observeDigest(witDigest(BigInt(i + 5)));
      c.sample().seal();
    });
  const d1 = await dgo(1);
  const d17 = await dgo(17);
  const digestMarginal = (d17 - d1) / 16;
  console.log(`    one NATIVE digest observe         ${digestMarginal.toFixed(2)} rows  (one Pasta word, one permutation — the deployed one absorbed 8 BabyBear lanes)`);

  // -------------------------------------------------------------------------
  console.log('\n[2] THE PER-QUERY HASH WALK, BUILT AT THE ROOT GEOMETRY');
  // Not a product of unit prices: the whole per-query hash work as ONE circuit.
  const perQuery = await rows(() => {
    // input phase — four rounds, each a leaf sponge then a depth-22 fold
    for (const r of INPUT_ROUNDS) {
      let cur = spongePasta(witLanes(r.lanes));
      for (let h = 0; h < INPUT_DEPTH; h++) {
        const sib = witDigest(BigInt(h + 3));
        const bit = wit(Bool, () => Bool(h % 2 === 0));
        const [l, rr] = condSwapPasta(cur, sib, bit);
        cur = compressPasta(l, rr);
      }
      cur.limbs[0].seal();
    }
    // commit phase — 16 rounds, an 8-lane leaf then a fold at that round's depth
    for (let rd = 0; rd < COMMIT_LAYERS; rd++) {
      let cur = spongePasta(witLanes(COMMIT_LEAF_LANES), true);
      for (let h = 0; h < COMMIT_DEPTHS[rd]; h++) {
        const sib = witDigest(BigInt(h + 3));
        const bit = wit(Bool, () => Bool(h % 2 === 1));
        const [l, rr] = condSwapPasta(cur, sib, bit);
        cur = compressPasta(l, rr);
      }
      cur.limbs[0].seal();
    }
  });
  console.log(`    one query's Merkle + leaf hashing : ${fmt(perQuery)} rows`);
  const modelled = levelsPerQuery * levelMarginal + lanesPerQuery * laneMarginal;
  const drift = Math.abs(perQuery - modelled) / modelled;
  console.log(
    `    the unit-price model says            ${fmt(modelled)} — ${(drift * 100).toFixed(1)}% apart`,
  );
  if (drift > 0.1)
    throw new Error(
      'the built walk and the unit-price model disagree by more than 10%: one of them is ' +
        'not describing the root geometry',
    );
  const hashAllQueries = perQuery * NUM_QUERIES;
  console.log(`    x ${NUM_QUERIES} queries                        : ${fmt(hashAllQueries)} rows`);

  // -------------------------------------------------------------------------
  console.log('\n[3] THE TRANSCRIPT, BUILT AT THE ROOT SCHEDULE');
  const transcript = await rows(() => {
    const c = new PastaChallenger();
    c.observeSlice(witLanes(TRANSCRIPT.babyBearObserves));
    for (let i = 0; i < TRANSCRIPT.digestObserves; i++) c.observeDigest(witDigest(BigInt(i + 11)));
    for (let i = 0; i < TRANSCRIPT.extSamples; i++) c.sampleExt().limbs[0].seal();
    for (let i = 0; i < TRANSCRIPT.indexSamples; i++) c.sampleBitsAsBits(TRANSCRIPT.indexBits);
  });
  console.log(
    `    ${fmt(TRANSCRIPT.babyBearObserves)} BabyBear observes + ${TRANSCRIPT.digestObserves} native ` +
      `digest observes + ${TRANSCRIPT.extSamples} ext challenges + ${TRANSCRIPT.indexSamples} query indices`,
  );
  console.log(`    transcript                        : ${fmt(transcript)} rows`);

  // -------------------------------------------------------------------------
  console.log('\n[4] THE TOTAL, against the 2.85e6 / 53 PROJECTION');
  // The hash-independent halves, MEASURED in §3 and unchanged by any hash
  // choice: BabyBear extension arithmetic all the way down.
  //  ⚠ RETIRED, AND KEPT ONLY SO THE MOVE IS VISIBLE. `2.5e6` was the DEEP
  //  quotient priced over the RETIRED FLAT CENSUS of 2,342 opened values —
  //  2,286 plus the 56 quotient openings counted twice, the model
  //  `CostModel.RETIRED_FLAT_MODEL` already documents as wrong. Re-derived from
  //  `ARITH_PRICE` at the measured census of 2,630, the term is 3,902,258 rows
  //  and the per-opened-value price is 1,484, not 1,067. `npm run deep-columns`
  //  owns that derivation and prices the levers; this leg keeps the retired pair
  //  so its own headline can still be read against §0.1's, and says so.
  const DEEP_RETIRED = 2.5e6;
  const DEEP_CENSUS_RETIRED = 2342;
  const DEEP = 3_902_258;
  const AIR = 1.9e5;
  const measuredHash = hashAllQueries + transcript;
  const total = measuredHash + DEEP + AIR;

  const USABLE = PICKLES.usableRowsMpv1; //  leg 16 — OWNED by src/CostModel.ts
  const slices = Math.ceil(total / USABLE);

  const table: [string, number, string][] = [
    ['Merkle paths + leaf hashing (19 queries)', hashAllQueries, 'MEASURED here'],
    ['transcript (absorbs + squeezes)', transcript, 'MEASURED here'],
    ['DEEP quotient (BabyBear ext. arith)', DEEP, '§3, hash-independent'],
    ['AIR constraint evaluation at zeta', AIR, '§3, hash-independent'],
  ];
  console.log('    term                                          rows      share   source');
  for (const [n, v, src] of table)
    console.log(
      `    ${n.padEnd(42)} ${v.toExponential(2).padStart(9)}  ${((v / total) * 100).toFixed(1).padStart(6)}%   ${src}`,
    );
  console.log(`    ${'TOTAL'.padEnd(42)} ${total.toExponential(3).padStart(9)}`);
  console.log('');

  const PROJ_TOTAL = 2.85e6;
  const PROJ_SLICES = 53;
  const d = (total - PROJ_TOTAL) / PROJ_TOTAL;
  console.log(
    `    ⚑ MEASURED ${total.toExponential(3)} rows = ${slices} slices @ ${fmt(USABLE)}, against the ` +
      `PROJECTED ${PROJ_TOTAL.toExponential(3)} / ${PROJ_SLICES} (${d >= 0 ? '+' : ''}${(d * 100).toFixed(1)}%)`,
  );
  console.log(
    `    ⚑ deployed (Poseidon2-BabyBear) was 2.46e7 / 453 slices — a ${(2.46e7 / total).toFixed(1)}x collapse`,
  );

  // -------------------------------------------------------------------------
  console.log('\n[5] THE SHAPE, WHICH IS THE POINT');
  const hashShare = (measuredHash / total) * 100;
  const deepShare = (DEEP / total) * 100;
  console.log(
    `    hashing is ${hashShare.toFixed(1)}% of the budget (it was 89% deployed); the DEEP quotient is ` +
      `${deepShare.toFixed(1)}% (it was 10%)`,
  );
  console.log(
    `    a 3x error in EVERY measured Pasta hash price moves the total to ` +
      `${((measuredHash * 3 + DEEP + AIR) / USABLE).toFixed(0)} slices — the answer is no longer sensitive to the hash`,
  );
  console.log(
    `    ⚑ THE NEXT LEVER IS COLUMN NARROWING, with a number: the DEEP quotient is ` +
      `${fmt(DEEP)} rows over 2,630 opened values at zeta = ${(DEEP / 2630).toFixed(0)} rows ` +
      `per opened value. Halving the root's committed column count halves it, i.e. ` +
      `${Math.ceil((measuredHash + DEEP / 2 + AIR) / USABLE)} slices.\n` +
      `      ⚠ THIS LEG USED TO SAY ${(DEEP_RETIRED / DEEP_CENSUS_RETIRED).toFixed(0)} ROWS PER OPENED VALUE ` +
      `(${fmt(DEEP_RETIRED)} / ${fmt(DEEP_CENSUS_RETIRED)}) and both literals were the retired flat model's.\n` +
      `      \`npm run deep-columns\` re-derives the term from \`ARITH_PRICE\` at the measured census and\n` +
      `      prices six levers with exact opened-value deltas — the lever is 39% BIGGER than this\n` +
      `      leg advertised, and it is ONE table (\`poseidon2_perm/baby_bear_d4_w24\`, 40.8%).`,
  );
  console.log('');
}

main().catch((e) => {
  console.error('\nMEASUREMENT FAILED:', e?.message ?? e, '\n');
  process.exit(1);
});

void BbExt;

// ---------------------------------------------------------------------------
// THE COST MODEL — one owner for every number the Mina-facing size projections
// ride on, and one mechanism that makes a second owner fail loudly.
//
// ⚑ WHY THIS FILE EXISTS, in the words of the review that asked for it:
//
//   "The lanes did not duplicate EFFORT, they duplicated CONSTANTS — and
//    constants that disagree are worse than effort that overlaps, because they
//    are silent."
//
// Four disagreements were live when this was written, and every one of them
// compiled, type-checked and produced a plausible number:
//
//   1. `deployedShapeOf` forced `logHeight: 22` on every matrix and priced a
//      2,286-term census, while the SAME document's §3.28 measured the root at
//      FIVE heights (22, 21, 16, 9, 6) and a census of 2,630.
//   2. `PartitionSchedule`'s chunk grouping (`misc, fold, open*`) and
//      `DreggProofSchedule`'s (`input, fold, pub, open*, pow`) both feed
//      `rootCommitDigest = Poseidon(digests)` and the only assertion checked the
//      lane TOTAL, so a divergent grouping repriced silently.
//   3. Three prices for "witness and range-check one BabyBear lane", reconciled
//      in a comment in exactly one file.
//   4. `stepBoundary` had an identical signature AND body in two families, so a
//      wrong import was numerically right today and undetectable.
//
// ⚑ EVERY FIGURE BELOW CARRIES ITS PROVENANCE, and the three words are not
// decoration:
//   * MEASURED  — a `getRows()`/`analyzeMethods` reading, or a value read off a
//                 real committed proof. The § or leg says which run.
//   * DERIVED   — arithmetic over MEASURED inputs, with the arithmetic shown.
//   * PROJECTED — a MEASURED unit multiplied by a structural count that has not
//                 itself been emitted. Never quoted in a measurement's voice.
//
// ⚑ AND THE REGISTRY AT THE BOTTOM IS THE POINT. A comment reconciling two
// constants is not a mechanism. `register()` throws when the same named quantity
// is registered twice with different values, and `scripts/cost-model-gate.ts`
// imports every module that registers plus scans the tree for unregistered
// literals. A second owner therefore fails a gate instead of drifting.
// ---------------------------------------------------------------------------

import { Field, Poseidon } from 'o1js';

// ===========================================================================
// 0. THE REGISTRY — the mechanism against recurrence.
// ===========================================================================

export type Provenance = 'MEASURED' | 'DERIVED' | 'PROJECTED';

export type Registration = {
  /** The QUANTITY, not the variable. Two modules pricing the same physical
   *  thing must choose the same key — that is what makes the clash detectable. */
  key: string;
  value: number;
  /** Where the number is defined, as `Module.EXPORT`. */
  site: string;
  provenance: Provenance;
  /** The run, §, or arithmetic that produced it. A registration without this is
   *  a number nobody can re-derive. */
  source: string;
  /** Fractional disagreement tolerated before `register` throws. Defaults to 0
   *  — exact agreement — because a cost constant that two modules "roughly"
   *  agree on is the defect this registry exists to catch. */
  tolerance?: number;
};

const REGISTRY = new Map<string, Registration>();

/**
 * Declare a cost constant. Throws when the same key is already registered with
 * a different value.
 *
 * ⚑ THIS RUNS AT MODULE LOAD, so a clash is a crash at import rather than a
 * wrong number in a report. `scripts/cost-model-gate.ts` imports every module
 * that registers, which is what turns "two lanes disagreed" into a red gate.
 */
export function register(r: Registration): number {
  const prev = REGISTRY.get(r.key);
  if (prev) {
    const tol = Math.max(prev.tolerance ?? 0, r.tolerance ?? 0);
    const drift = prev.value === 0 ? (r.value === 0 ? 0 : 1) : Math.abs(r.value - prev.value) / Math.abs(prev.value);
    if (drift > tol)
      throw new Error(
        `COST CONSTANT CLASH on \`${r.key}\`:\n` +
          `  ${prev.site} = ${prev.value}  (${prev.provenance}: ${prev.source})\n` +
          `  ${r.site} = ${r.value}  (${r.provenance}: ${r.source})\n` +
          `  ${(drift * 100).toFixed(2)}% apart, tolerance ${(tol * 100).toFixed(2)}%.\n` +
          '  One quantity, one home. Import it from `src/CostModel.ts` rather than ' +
          're-deriving it — and if the two really are different quantities, they need ' +
          'different keys and the difference needs stating.',
      );
    return prev.value;
  }
  REGISTRY.set(r.key, r);
  return r.value;
}

export const registry = (): Registration[] => [...REGISTRY.values()].sort((a, b) => a.key.localeCompare(b.key));

/** Registered under this key, or `undefined`. For the gate's reporting. */
export const registered = (key: string): Registration | undefined => REGISTRY.get(key);

// ===========================================================================
// 1. THE HASH PRICES — one row per (hash, operation), each MEASURED.
// ===========================================================================

/**
 * What one hashing operation costs in emitted Kimchi rows.
 *
 * ⚑ THE HASH IS A PARAMETER, and that is the whole subject of
 * `docs/MINA-FACING-TERMINAL-OPTIONS.md`. The deployed root commits with
 * Poseidon2-over-BabyBear, which a Pasta circuit must EMULATE; a Mina-facing
 * proof minted under `DreggMinaConfig` commits with Mina's own Poseidon, which
 * the circuit runs NATIVELY. Same verifier, same segment list, ~200x the price
 * per permutation.
 */
export type HashPrice = {
  name: string;
  /** One sponge permutation. */
  perm: number;
  /** One Merkle level: conditional swap + compress + the sibling's range checks. */
  merkleLevel: number;
  /** A mixed-height INJECTION: `compress(root, digestOfRowsAtThisHeight)`. No
   *  `condSwap` and no witnessed sibling — both operands are computed, so it is
   *  one bare permutation. */
  merkleInject: number;
  /** BabyBear lanes absorbed per permutation by the leaf sponge. ⚑ NOT the same
   *  for the two hashes: the deployed sponge takes 8, the Pasta MMCS packs 16
   *  (8 shifted radix-2^31 limbs x rate 2), so the swap halves the permutation
   *  COUNT as well as the permutation PRICE. */
  spongeRate: number;
};

export const BABYBEAR_HASH: HashPrice = {
  name: 'Poseidon2-BabyBear-w16 (foreign, emulated)',
  perm: register({
    key: 'rows/permutation@babybear',
    value: 2601,
    site: 'CostModel.BABYBEAR_HASH.perm',
    provenance: 'MEASURED',
    source: '§3.8, measured 2,600.5 by `npm run poseidon2-rows`; carried as 2601 by the walk',
    // 2,600.5 and 2,601 are the same measurement read to different precision.
    tolerance: 0.001,
  }),
  merkleLevel: register({
    key: 'rows/merkle-level@babybear',
    value: 2677,
    site: 'CostModel.BABYBEAR_HASH.merkleLevel',
    provenance: 'MEASURED',
    source: '§3.9, `npm run poseidon2-merkle`: condSwap + compress + 8 sibling range checks',
  }),
  merkleInject: 2601,
  spongeRate: register({
    key: 'lanes/sponge-permutation@babybear',
    value: 8,
    site: 'CostModel.BABYBEAR_HASH.spongeRate',
    provenance: 'MEASURED',
    source: '§3.9: one 8-lane block costs 2,632 rows; `RootFriWalk.CHAL_RATE`',
  }),
};

export const PASTA_HASH: HashPrice = {
  name: 'Mina-Poseidon over Pasta (NATIVE)',
  perm: register({
    key: 'rows/permutation@pasta',
    value: 13,
    site: 'CostModel.PASTA_HASH.perm',
    provenance: 'MEASURED',
    source:
      'o1js 2.15.0, `npm run mina-merkle` 2026-07-30. ⚠ NOT kimchi`s cited 11 — that is the ' +
      'Poseidon GATE chain alone; o1js charges 2 more for the generic rows around it',
  }),
  merkleLevel: register({
    key: 'rows/merkle-level@pasta',
    value: 15.5,
    site: 'CostModel.PASTA_HASH.merkleLevel',
    provenance: 'MEASURED',
    source:
      'o1js 2.15.0, `npm run mina-merkle` 2026-07-30. The DERIVED ~15 was right to 3% for the ' +
      'wrong reason: the conditional swap is ~2.5 rows, not ~4',
  }),
  merkleInject: 13,
  spongeRate: register({
    key: 'lanes/sponge-permutation@pasta',
    value: 16,
    site: 'CostModel.PASTA_HASH.spongeRate',
    provenance: 'MEASURED',
    source:
      '`npm run mina-merkle`: the Pasta MMCS packs 8 shifted radix-2^31 limbs x rate 2. ' +
      'Half the permutations of the deployed sponge AND each ~200x cheaper',
  }),
};

// ===========================================================================
// 2. THE CARRY PRICE — ONE quantity, ONE home.
// ===========================================================================
//
// ⚑ THE REVIEW SAID "THREE PRICES FOR ONE QUANTITY, 6.9x APART". The 6.9x is a
// UNITS ARTIFACT and the real disagreement is smaller and more interesting, so
// the reconciliation is done here once, in arithmetic, instead of in a comment
// in one file:
//
//   §3.20 MEASURED, bulk re-witness of a flat lane list:
//     rebind (witness + range-check + pack + hash) 34,566 / 9,198 = 3.757 rows/LANE
//     pack + hash alone (`probeNoRc`)              11,571 / 9,198 = 1.258 rows/LANE
//     => range check alone, DERIVED as the difference      2.499 rows/LANE
//
//   leg 13 MEASURED, the AIR chain witnessing its own carried values:
//     41,659 / 1,602 = 26.0 rows per 4-lane EXTENSION VALUE = 6.5 rows/LANE
//
// 26 against 3.757 is 6.9x and compares rows-per-EXTENSION-VALUE against
// rows-per-LANE. In the SAME unit it is 6.5 against 3.757 — **1.73x** — and the
// gap is real rather than an error: §3.20's probe amortises one pack over 9,198
// lanes, and leg 13's carry is a few dozen extension values where it does not
// amortise at all. `RootFriWalk.PRICE.witnessLane` already takes the higher of
// the two, which is the right call in the right direction (a cut that fits at
// 6.5 also fits at 3.757, and the failure mode of the other direction is a
// circuit that does not compile). What was missing is that the call was made in
// one file and nothing enforced it anywhere else.

export const LANE_COST = {
  /** §3.20 MEASURED: re-witness + range-check + pack + hash, one lane, over a
   *  100x range (203..9,198 lanes, two independent slopes agreeing within 5%). */
  rebindPerLane: register({
    key: 'rows/lane/rebind@bulk',
    value: 34_566 / 9_198,
    site: 'CostModel.LANE_COST.rebindPerLane',
    provenance: 'MEASURED',
    source: '§3.20, 34,566 rows at 9,198 lanes',
  }),
  /** §3.20 MEASURED: the same circuit with the range checks removed — what a
   *  lane the step ALREADY holds costs to fold into a digest. */
  hashPerLane: register({
    key: 'rows/lane/pack-and-hash@bulk',
    value: 11_571 / 9_198,
    site: 'CostModel.LANE_COST.hashPerLane',
    provenance: 'MEASURED',
    source: '§3.20 `probeNoRc`, 11,571 rows at 9,198 lanes',
  }),
  /** leg 13 MEASURED: witness and range-check one carried EXTENSION VALUE. */
  witnessPerExtValue: register({
    key: 'rows/ext-value/witness@air-chain',
    value: 26,
    site: 'CostModel.LANE_COST.witnessPerExtValue',
    provenance: 'MEASURED',
    source: 'leg 13 EMITTED, 41,659 rows / 1,602 extension values = 26.0',
  }),
  /** The same, per lane — what `RootFriWalk.PRICE.witnessLane` carries. */
  witnessPerLane: 26 / 4,
} as const;

/** DERIVED: the range check alone, as the difference of §3.20's two measured
 *  slopes. Named because it is the term that does NOT move when the hash does. */
export const RANGE_CHECK_PER_LANE = LANE_COST.rebindPerLane - LANE_COST.hashPerLane;

/**
 * ⚑ The reconciliation, as an assertion rather than a paragraph. If a future
 * measurement moves either slope far enough that the two lane prices stop being
 * the same order, the comment above has stopped being true and this throws
 * instead of letting the comment lie.
 */
export function assertLaneCostCoherent(): void {
  const ratio = LANE_COST.witnessPerLane / LANE_COST.rebindPerLane;
  if (!(ratio > 1 && ratio < 3))
    throw new Error(
      `the AIR chain's per-lane carry (${LANE_COST.witnessPerLane.toFixed(3)}) and §3.20's bulk ` +
        `rebind slope (${LANE_COST.rebindPerLane.toFixed(3)}) are ${ratio.toFixed(2)}x apart. ` +
        'The reconciliation in CostModel §2 says 1.73x and explains it by pack amortisation; ' +
        'at this ratio that explanation no longer covers the gap and one of the two is measuring ' +
        'something else.',
    );
  //  The range check is the hash-INDEPENDENT part, and the Pasta leaf sponge
  //  measured it end to end at 3.69 rows/lane all-in. Its implied range-check
  //  residual is `3.69 - perm/spongeRate`; if that has drifted far from §3.20's
  //  derived 2.499 then "the range check does not shrink" has stopped holding.
  const pastaImplied = PASTA_SPONGE_ALL_IN_PER_LANE - PASTA_HASH.perm / PASTA_HASH.spongeRate;
  const drift = Math.abs(pastaImplied - RANGE_CHECK_PER_LANE) / RANGE_CHECK_PER_LANE;
  if (drift > 0.5)
    throw new Error(
      `the Pasta leaf sponge implies ${pastaImplied.toFixed(3)} rows/lane of range check and ` +
        `§3.20 derives ${RANGE_CHECK_PER_LANE.toFixed(3)} — ${(drift * 100).toFixed(0)}% apart. ` +
        '`MINA-FACING-TERMINAL-OPTIONS` §0.1 rests on the range check being hash-independent.',
    );
}

/** MEASURED (`npm run mina-merkle`): the Pasta leaf sponge, all-in per BabyBear
 *  lane — permutation share plus the per-lane range check. Against the deployed
 *  sponge's 329 rows/lane (§3.9, 2,632 per 8-lane block) this is the 89x. */
export const PASTA_SPONGE_ALL_IN_PER_LANE = register({
  key: 'rows/lane/leaf-sponge-all-in@pasta',
  value: 3.69,
  site: 'CostModel.PASTA_SPONGE_ALL_IN_PER_LANE',
  provenance: 'MEASURED',
  source: 'o1js 2.15.0, `npm run mina-merkle` 2026-07-30',
});

// ===========================================================================
// 3. THE ROOT'S GEOMETRY — MEASURED off the committed proof, not derived from
//    a table of widths.
// ===========================================================================

/**
 * ⚑ THE CENSUS AND THE HEIGHTS, AS THE PROOF HAS THEM.
 *
 * `deployedShapeOf` used to force `logHeight: 22` and `pathDepth: 22` on EVERY
 * matrix and price `940 + 175` columns at two opening points each. §3.28
 * measured the real object and it is wrong in two directions that do not
 * cancel:
 *
 *   * it OMITS the permutation round — 64 extension columns x 4 x 2 = 512 terms;
 *   * it ASSUMES two opening points everywhere, which the proof refuses. `Const`,
 *     `Public`, `recompose` and `expose_claim` reference no next-row main or
 *     preprocessed value, so those matrices are opened at ζ alone — 168 terms
 *     §3.15 charges and the proof does not have.
 *
 * A census that multiplies every width by two gets 2,798; the proof says 2,630.
 *
 * ⚑ AND THE HEIGHTS ARE NOT FLAT. The root's committed matrices sit at FIVE
 * distinct heights, so `MerkleTreeMmcs::verify_batch` compresses a shorter
 * matrix's own row digest into the running root at the level its height names.
 * A flat-22 model pays four full-depth paths per query where the proof pays one
 * path per round with injections.
 */
export const MEASURED_ROOT_GEOMETRY = {
  /** DEEP terms — `(matrix, point, column)` triples — in ONE query's
   *  `open_input`. MEASURED off `.fullchain/real-root-fri.json`. */
  censusPerQuery: register({
    key: 'deep-terms/query@root',
    value: 2630,
    site: 'CostModel.MEASURED_ROOT_GEOMETRY.censusPerQuery',
    provenance: 'MEASURED',
    source:
      '§3.28, read off `.fullchain/real-root-fri.json` by `RootFriWalk.deepTermCensus`: ' +
      'main 1,768 + quotient_chunk 56 + preprocessed 294 + permutation 512',
  }),
  /** Per round, MEASURED. */
  censusByRound: { main: 1768, quotient_chunk: 56, preprocessed: 294, permutation: 512 } as const,
  /** The committed matrix log-heights, DESCENDING. MEASURED. */
  heights: [22, 21, 16, 9, 6] as const,
  /** `log_global_max_height` — the tallest, and the input-phase path depth. */
  logGlobalMaxHeight: 22,
  /** Base columns committed per round, MEASURED. */
  baseColsByRound: { main: 940, quotient_chunk: 56, preprocessed: 175, permutation: 256 } as const,
  /** Of the census, how many are lanes of the AIR chain's own column
   *  commitment. MEASURED by `planOpenedValues`. */
  airCoveredPerQuery: 1236,
  /** Bridged to the AIR by `permBind` — paid ONCE, not per query. */
  permBindPerProof: 512,
} as const;

/**
 * ⚑ THE RETIRED MODEL, kept ONLY so the delta can be printed and so nothing
 * silently re-adopts it. Never price anything with these.
 */
export const RETIRED_FLAT_MODEL = {
  /** `940*2 + 175*2 + 7*2*4` — §3.14/§3.15's census. */
  censusPerQuery: 2286,
  /** Every matrix forced to the global max height. */
  flatLogHeight: 22,
  /** `DEPLOYED_COLS` — 940 main + 175 preprocessed. */
  cols: 940 + 175,
  /** What a naive "two points everywhere" census would give, for contrast. */
  twoPointsEverywhere: 2798,
} as const;

/** DERIVED: how far the census correction moves a per-query term count. */
export const CENSUS_CORRECTION =
  MEASURED_ROOT_GEOMETRY.censusPerQuery / RETIRED_FLAT_MODEL.censusPerQuery - 1;

/**
 * Re-derive the geometry from a real committed proof and refuse a mismatch.
 *
 * ⚑ THIS IS WHAT MAKES `MEASURED_ROOT_GEOMETRY` A MEASUREMENT RATHER THAN A
 * COPIED NUMBER. A constant transcribed from a document is a claim; a constant
 * checked against the artifact it was read off is a measurement with a ratchet.
 */
export function assertGeometryMatchesProof(real: {
  inputRounds: { kindName: string; matrices: { logHeight: number; width: number; points: unknown[] }[] }[];
}): void {
  let total = 0;
  const byRound: Record<string, number> = {};
  const heights = new Set<number>();
  for (const r of real.inputRounds) {
    let n = 0;
    for (const m of r.matrices) {
      n += m.width * m.points.length;
      heights.add(m.logHeight);
    }
    byRound[r.kindName] = n;
    total += n;
  }
  if (total !== MEASURED_ROOT_GEOMETRY.censusPerQuery)
    throw new Error(
      `the committed proof's DEEP census is ${total} and CostModel records ` +
        `${MEASURED_ROOT_GEOMETRY.censusPerQuery}. The geometry moved; every size figure that ` +
        'rides on it is stale until this is re-derived, not just this constant.',
    );
  const hs = [...heights].sort((a, b) => b - a);
  const want = [...MEASURED_ROOT_GEOMETRY.heights];
  if (hs.length !== want.length || hs.some((h, i) => h !== want[i]))
    throw new Error(
      `the committed proof sits at heights [${hs}] and CostModel records [${want}]. ` +
        'The mixed-height MMCS injection schedule is a function of exactly this list.',
    );
  for (const [k, v] of Object.entries(byRound)) {
    const w = (MEASURED_ROOT_GEOMETRY.censusByRound as Record<string, number>)[k];
    if (w !== v)
      throw new Error(`round \`${k}\` opens ${v} terms and CostModel records ${w}`);
  }
}

// ===========================================================================
// 4. THE CHUNK GROUPING — asserted, not assumed.
// ===========================================================================
//
// ⚑ THE SCHEDULER PRICED A COMMITMENT THE CIRCUIT DOES NOT BUILD.
// `PartitionSchedule`'s program grouped the root's lanes as `{misc, fold,
// open*}` (m = 2 + n) while `DreggProofSchedule.rootChunks` — the grouping the
// circuit ACTUALLY commits to — is `{input, fold, pub, open*, pow}` (m = 4 + n).
// Both feed `rootCommitDigest = Poseidon(d_0 .. d_{m-1})`, and the only
// consistency assertion in either file compared the LANE TOTAL. Two groupings
// with the same total are two different digests, so every step count quoted for
// the dregg-proof chain was priced against a commitment that does not exist.
//
// The grouping below is the CIRCUIT's. `assertGrouping` is what a model has to
// pass before its step counts mean anything.

/** The fixed (non-`open*`) chunk ids, in commitment order, as
 *  `DreggProofSchedule.rootChunks` builds them. */
export const FIXED_CHUNK_IDS_BEFORE_OPEN = ['input', 'fold', 'pub'] as const;
export const FIXED_CHUNK_IDS_AFTER_OPEN = ['pow'] as const;

/** How many chunk digests a step witnesses at `n` opened-evaluation chunks. */
export const chunkCountAt = (nOpenChunks: number): number =>
  FIXED_CHUNK_IDS_BEFORE_OPEN.length + nOpenChunks + FIXED_CHUNK_IDS_AFTER_OPEN.length;

/** The authoritative id list in commitment order. */
export const chunkIdsAt = (nOpenChunks: number): string[] => [
  ...FIXED_CHUNK_IDS_BEFORE_OPEN,
  ...Array.from({ length: nOpenChunks }, (_, i) => `open${i}`),
  ...FIXED_CHUNK_IDS_AFTER_OPEN,
];

/**
 * ⚑ ASSERT THE GROUPING, NOT THE TOTAL.
 *
 * A model's chunk list must be the circuit's chunk list — same ids, same order,
 * same count — or its carry is priced against a `rootCommitDigest` nothing
 * computes. Passing the lane total is NOT evidence: `{misc(183), fold(140),
 * open*}` and `{input(32), fold(140), pub(25), open*, pow(1)}` can cover the
 * same 9,103 lanes and hash to different roots.
 */
export function assertGrouping(modelIds: string[], nOpenChunks: number, who: string): void {
  const want = chunkIdsAt(nOpenChunks);
  const same = modelIds.length === want.length && modelIds.every((x, i) => x === want[i]);
  if (!same)
    throw new Error(
      `${who} groups the root's committed lanes as\n` +
        `    [${modelIds.join(', ')}]  (m = ${modelIds.length})\n` +
        'and `DreggProofSchedule.rootChunks` — the grouping the CIRCUIT commits to — is\n' +
        `    [${want.join(', ')}]  (m = ${want.length})\n` +
        'Both feed `rootCommitDigest = Poseidon(digests)`, so these are two different ' +
        'commitments. A step count priced against the first is priced against a digest ' +
        'that does not exist. Matching the LANE TOTAL is not enough and is what was ' +
        'being checked before.',
    );
}

// ===========================================================================
// 5. THE SEAL CONVENTIONS — one definition each, and names that cannot collide.
// ===========================================================================
//
// ⚑ WHAT WAS WRONG. `stepBoundary` had an IDENTICAL signature and an IDENTICAL
// body in `DreggProofPartition` and `RootAirChain`, so importing the wrong one
// compiled, type-checked, and was numerically right — until the day one of them
// changed. `terminalSeal` differed (4-field domain-tagged against 3-field
// untagged) and was caught ONLY by arity, which is not a mechanism either.
//
// The fix is not a lint. `chainStepBoundary` below is the ONE definition both
// families now call, so they CANNOT diverge; and the two seals keep their real
// difference under names that say which is which, so a wrong import is a
// compile error rather than a coincidence.

/** Eight 31-bit lanes pack losslessly into one 254-bit Pasta field. */
export const LANES_PER_FIELD = 8;
export const LANE_BITS = 31n;

/**
 * **THE STEP BOUNDARY — the one definition.**
 *
 * `boundary_k = Poseidon(commitment, carried, k)`, `KimchiPartition
 * .StepPublicInput`'s three slots. Both chain families call this: the AIR/FRI
 * walk passes `(dagDigest | friCommit, liveDigest, k)` and the proof partition
 * passes `(rootCommitDigest, challengeDigest, stepIndex)`. They are the same
 * algebra over different carried sets, which is exactly why they must be the
 * same function.
 */
export const chainStepBoundary = (commitment: Field, carried: Field, k: Field | number): Field =>
  Poseidon.hash([commitment, carried, typeof k === 'number' ? Field(k) : k]);

/**
 * **The UNTAGGED closing seal** — the proof-partition family's.
 *
 * The same three-slot shape as a step boundary, with the carried slot empty and
 * the index at `nSteps`: "the chain over THIS proof closed after exactly this
 * many steps". Both ends of the chain are computable from the dregg proof alone.
 *
 * ⚠ It is a `chainStepBoundary` at a reserved carried value, so it lives in the
 * SAME image as the step boundaries. That is safe only because the index slot
 * separates them; it is named `Untagged` so nobody reads it as domain-separated.
 */
export const untaggedTerminalSeal = (rootCommitDigest: Field, nSteps: number | Field): Field =>
  chainStepBoundary(rootCommitDigest, Field(0), nSteps);

/**
 * **The DOMAIN-TAGGED closing seal** — the AIR/FRI walk family's.
 *
 * Carries the ACCUMULATOR's digest rather than a live set, and a fourth field
 * `1` that separates it from every step boundary by construction rather than by
 * an index convention. The single external check is one field comparison a
 * verifier computes from the expected accumulator and the artifact alone.
 */
export const taggedTerminalSeal = (
  commitment: Field,
  accDigest: Field,
  nSteps: number | Field,
): Field =>
  Poseidon.hash([commitment, accDigest, typeof nSteps === 'number' ? Field(nSteps) : nSteps, Field(1)]);

// ===========================================================================
// 6. THE PICKLES CEILING — what a slice count is denominated in.
// ===========================================================================

export const PICKLES = {
  /** The Kimchi step domain (`kimchi_pasta_basic.ml:16-17`, `Step = Nat.N16`). */
  domainRows: 65_536,
  /**
   * ⚑ NARROWED, MEASURED (leg 16). The largest EMITTED body, in the widest
   * branch of the real three-slice chain, that `compile()` accepts. Budget
   * 54,289 gives 54,300 rows and compiles; 54,324 gives 54,376 and fails.
   *
   * ⚠ A ceiling is only honest for the SHAPE it was measured on: 57,769 rows of
   * extension arithmetic FAIL where 63,300 rows of single-row field multiplies
   * COMPILE, so this is not a function of the row count alone.
   */
  usableRowsMpv1: register({
    key: 'rows/usable@pickles-mpv1',
    value: 54_300,
    site: 'CostModel.PICKLES.usableRowsMpv1',
    provenance: 'MEASURED',
    source: 'leg 16 `npm run root-air-ceiling`, narrowed on the real three-slice chain body',
  }),
  /** The smallest widest-branch row count OBSERVED to fail, same shape. */
  failsAtMpv1: 54_376,
  /** ⚠ NOT NARROWED — a LOWER BOUND: leg 17 compiled, PROVED and VERIFIED a
   *  side-loaded slice branch of this width. */
  sideloadAtLeast: 51_136,
  /** The budget the committed FRI walk plans against. */
  friWalkBudget: 50_000,
} as const;

/** Slices at a budget, work-only (no carry). The currency §0 of
 *  `MINA-FACING-TERMINAL-OPTIONS.md` quotes. */
export const slicesAt = (rows: number, usable = PICKLES.usableRowsMpv1): number =>
  Math.ceil(rows / usable);
